import PQ.Interactive.QromBridgeEvalQ
import PQ.QROM.TwoPhaseAdv
import PQ.Interactive.QromBridgePrfStruct

/-!
# From non-closed `PUE` families to interactive adversaries (`IAdv`)

A `PUE` family `Mach : (X → Y) → QOC (WS X Y E) (unifSpec + (Req →ₒ Resp)) α` (game queries of
weight `0`) is compiled into ONE interactive adversary
`x : IAdv LocalSig.instruments (qromSpec X Y) Req Resp (fun _ ↦ α) n (progReg X Y E)` over the SAME
port oracle: instrument nodes are local operations, port calls are oracle calls, classical
evaluations are basis calls (`QComp.callBasis`), uniform-sampling nodes are uniform coins, and
every game query becomes an `IAdv` request.

* `PUE.exists_iadv`: `IAdv.IsQueryBound n x (fun _ ↦ q)`, and for every deterministic
  challenger `ch : Req → St → Resp × St`, start state `s`, port function `H` with at most `n`
  game queries on every path of `Mach H` (`CountBound isGameQ`), and every event:
  `leafW (oracleRt H) I (IAdv.flat ch IAdv.stop n s x) M Ev = qWeight Ev (PQ.Interactive.close (detImpl ch) (Mach H) s) M`.
* `PUE.exists_iadv_qprob`: the same for `PQ.QROM.qprob` and initial states `ρ ⊗ |()⟩⟨()|`.
* `WCount` transfer through interpretations (`WCount.simulateQ`, `WCount.simulateQ_run`), used to
  bound the number of game queries of wrapped machines.
-/

open OracleComp OracleSpec ENNReal Quantum MeasureTheory Matrix
open scoped Kronecker ComplexOrder

set_option linter.unusedSectionVars false

namespace PQ.Interactive

variable {X Y E : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
  [Fintype E] [DecidableEq E] {α β γ : Type} {Req Resp : Type}

/-- The closed implementation of a deterministic challenger: uniform bits forwarded, game query
`r` answered by `ch r`. -/
noncomputable def detImpl {St : Type} (ch : Req → St → Resp × St) :
    QueryImpl (unifSpec + (Req →ₒ Resp)) (StateT St ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St ProbComp) +
    fun r ↦ StateT.mk fun s ↦ (pure (ch r s) : ProbComp (Resp × St))

/-- Game queries of a machine over `unifSpec + (Req →ₒ Resp)`. -/
def isGameQ {W : Type} [Fintype W] :
    (instrSpec W + (unifSpec + (Req →ₒ Resp))).Domain → Prop
  | .inr (.inr _) => True
  | _ => False

instance {W : Type} [Fintype W] : DecidablePred (isGameQ (W := W) (Req := Req) (Resp := Resp)) :=
  fun t ↦ by rcases t with _ | _ | _ <;> unfold isGameQ <;> infer_instance

/-! ## Uniform constructors of interactive adversaries -/

section ctor

abbrev IA (X Y E : Type) [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Fintype E]
    [DecidableEq E] (Req Resp α : Type) (n : ℕ) (A : QReg) : Type 1 :=
  PQ.QROM.IAdv LocalSig.instruments.{0} (qromSpec X Y) Req Resp (fun _ ↦ α) n A

abbrev iflat {St : Type} (ch : Req → St → Resp × St) (n : ℕ) {A : QReg} (s : St)
    (x : IA X Y E Req Resp α n A) :
    QuantumComp LocalSig.instruments.{0} (qromSpec X Y) (fun _ ↦ α × St) A :=
  PQ.QROM.IAdv.flat ch (PQ.QROM.IAdv.stop (L := LocalSig.instruments.{0})
    (spec := qromSpec X Y)) n s x

def iPure : (n : ℕ) → {A : QReg} → α → IA X Y E Req Resp α n A
  | 0, _, a => QuantumComp.pure a
  | _ + 1, _, a => QuantumComp.pure (.inl a)

def iPrim : (n : ℕ) → {A : QReg} → (o : (LocalSig.instruments.{0}).Op A) →
    ((b : (LocalSig.instruments.{0}).Outcome o) →
      IA X Y E Req Resp α n ((LocalSig.instruments.{0}).next o b)) → IA X Y E Req Resp α n A
  | 0, _, o, k => QuantumComp.primBind o k
  | _ + 1, _, o, k => QuantumComp.primBind o k

def iQuery : (n : ℕ) → {A : QReg} → (E' : QReg) → (ℓ : A ≃ (qromSpec X Y).In () × E') →
    ((qromSpec X Y).Result () → IA X Y E Req Resp α n (QReg.of ((qromSpec X Y).Out () × E'))) →
      IA X Y E Req Resp α n A
  | 0, _, E', ℓ, k => QuantumComp.queryBind () E' ℓ k
  | _ + 1, _, E', ℓ, k => QuantumComp.queryBind () E' ℓ k

noncomputable def iEval : (n : ℕ) → (x₀ : X) →
    (Y → IA X Y E Req Resp α n (progReg X Y E)) → IA X Y E Req Resp α n (progReg X Y E)
  | 0, x₀, k => PQ.QROM.fidBind
      (QComp.callBasis (spec := qromSpec X Y) () (progReg X Y E) (x₀, (0 : Y)) (fun o _ ↦ o.2)) k
  | _ + 1, x₀, k => PQ.QROM.fidBind
      (QComp.callBasis (spec := qromSpec X Y) () (progReg X Y E) (x₀, (0 : Y)) (fun o _ ↦ o.2)) k

variable {St : Type} (ch : Req → St → Resp × St)

theorem iflat_iPure (n : ℕ) {A : QReg} (s : St) (a : α) :
    iflat (X := X) (Y := Y) (E := E) ch n s (iPure n (A := A) a) = QuantumComp.pure (a, s) := by
  cases n <;> rfl

theorem iflat_iPrim (n : ℕ) {A : QReg} (s : St) (o : (LocalSig.instruments.{0}).Op A) (k) :
    iflat (X := X) (Y := Y) (E := E) (α := α) ch n s (iPrim n o k) =
      QuantumComp.primBind o fun b ↦ iflat ch n s (k b) := by
  cases n <;> rfl

theorem iflat_iQuery (n : ℕ) {A : QReg} (s : St) (E' : QReg) (ℓ) (k) :
    iflat (X := X) (Y := Y) (E := E) (α := α) ch n s (iQuery n (A := A) E' ℓ k) =
      QuantumComp.queryBind () E' ℓ fun r ↦ iflat ch n s (k r) := by
  cases n <;> rfl

theorem iflat_iEval (n : ℕ) (s : St) (x₀ : X) (k : Y → IA X Y E Req Resp α n (progReg X Y E)) :
    iflat ch n s (iEval n x₀ k) =
      PQ.QROM.fidBind
        (QComp.callBasis (spec := qromSpec X Y) () (progReg X Y E) (x₀, (0 : Y)) (fun o _ ↦ o.2))
        fun y ↦ iflat ch n s (k y) := by
  cases n <;> exact PQ.QROM.fidBind_bind _ _ _

theorem iflat_req (n : ℕ) {A : QReg} (s : St) (t : Req) (k : Resp → IA X Y E Req Resp α n A) :
    iflat (X := X) (Y := Y) (E := E) ch (n + 1) s
        (QuantumComp.pure (.inr (t, k)) : IA X Y E Req Resp α (n + 1) A) =
      iflat (X := X) (Y := Y) (E := E) ch n (ch t s).2 (k (ch t s).1) := rfl

end ctor

/-! ## The compiler -/

lemma close_detImpl_game {W : Type} [Fintype W] {St : Type} (ch : Req → St → Resp × St) (t : Req)
    (k : Resp → QOC W (unifSpec + (Req →ₒ Resp)) α) (s : St) :
    PQ.Interactive.close (W := W) (detImpl ch) (liftM ((instrSpec W + (unifSpec + (Req →ₒ Resp))).query
      (Sum.inr (Sum.inr t))) >>= k) s =
      PQ.Interactive.close (W := W) (detImpl ch) (k (ch t s).1) (ch t s).2 := by
  rw [close_query_bind]
  change liftU (pure (ch t s)) >>= _ = _
  rw [liftU_pure, pure_bind]

/-- **Compiler of non-closed `PUE` families into interactive adversaries, matrix form.** -/
theorem PUE.exists_iadv [Nonempty α]
    {Mach : (X → Y) → QOC (WS X Y E) (unifSpec + (Req →ₒ Resp)) α} {q : ℕ}
    (h : PUE (fun _ ↦ 0) Mach q) (n : ℕ) :
    ∃ x : IA X Y E Req Resp α n (progReg X Y E),
      PQ.QROM.IAdv.IsQueryBound n x (fun _ ↦ q) ∧
      ∀ (St : Type) (ch : Req → St → Resp × St) (s : St) (Ev : α × St → Prop) [DecidablePred Ev]
        (H : X → Y) (M : Matrix (WS X Y E) (WS X Y E) ℂ), M.PosSemidef →
        CountBound (isGameQ (Req := Req) (Resp := Resp)) (Mach H) n →
        leafW (A := progReg X Y E) (oracleRt H) LocalSig.Interp.instruments (iflat ch n s x) M Ev =
          qWeight Ev (PQ.Interactive.close (detImpl ch) (Mach H) s) M := by
  suffices key : ∀ n, ∃ x : IA X Y E Req Resp α n (progReg X Y E),
      ∀ (St : Type) (ch : Req → St → Resp × St) (s : St),
        (iflat ch n s x).IsQueryBound (fun _ ↦ q) ∧
        ∀ (Ev : α × St → Prop) [DecidablePred Ev] (H : X → Y)
          (M : Matrix (WS X Y E) (WS X Y E) ℂ), M.PosSemidef →
          CountBound (isGameQ (Req := Req) (Resp := Resp)) (Mach H) n →
          leafW (A := progReg X Y E) (oracleRt H) LocalSig.Interp.instruments (iflat ch n s x) M Ev =
            qWeight Ev (PQ.Interactive.close (detImpl ch) (Mach H) s) M by
    obtain ⟨x, hx⟩ := key n
    exact ⟨x, fun St ch s ↦ (hx St ch s).1, fun St ch s Ev _ H M hM hc ↦ (hx St ch s).2 Ev H M hM hc⟩
  clear n
  induction h with
  | pure a q =>
    intro n
    refine ⟨iPure n a, fun St ch s ↦ ⟨?_, fun Ev _ H M _ _ ↦ ?_⟩⟩
    · rw [iflat_iPure]
      exact QuantumComp.isQueryBound_pure _ _
    · rw [iflat_iPure, close_pure, qWeight_pure]
      exact leafW_pure (oracleRt H) LocalSig.Interp.instruments (a, s) M Ev
  | instr j k q _ ih =>
    intro n
    choose x hx using fun i ↦ ih i n
    refine ⟨iPrim n (instrOp j) fun b ↦ x b, fun St ch s ↦ ⟨?_, fun Ev _ H M hM hc ↦ ?_⟩⟩
    · rw [iflat_iPrim]
      exact (QuantumComp.isQueryBound_primBind_iff _ _ _).2 fun b ↦ (hx b St ch s).1
    · rw [iflat_iPrim, close_instr_bind, qWeight_instr_bind]
      rw [countBound_query_bind] at hc
      have hc' : ∀ i, CountBound (isGameQ (Req := Req) (Resp := Resp)) (k i H) n := by simpa [isGameQ] using hc
      have h := leafW_bind_aux (A := progReg X Y E) (oracleRt H) LocalSig.Interp.instruments
        ((LocalSig.Interp.instruments (instrOp j)).frame (QReg.of Unit))
        (fun b ↦ iflat ch n s (x b)) M hM Ev
      refine Eq.trans h ?_
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      exact (hx i St ch s).2 Ev H _ (((framedIdx j).2.1.isCP_branch i).posSemidef hM) (hc' i)
  | port k q _ ih =>
    intro n
    obtain ⟨x, hx⟩ := ih n
    refine ⟨iQuery n (QReg.of E) (idSplit X Y E) fun _ ↦ x, fun St ch s ↦ ⟨?_, fun Ev _ H M hM hc ↦ ?_⟩⟩
    · rw [iflat_iQuery, QuantumComp.isQueryBound_queryBind_iff]
      refine ⟨Nat.succ_pos q, fun _ ↦ ?_⟩
      have e : Function.update (fun _ : (qromSpec X Y).Port ↦ q + 1) () (q + 1 - 1) =
          fun _ ↦ q := by
        funext u
        simp
      rw [e]
      exact (hx St ch s).1
    · rw [iflat_iQuery, close_instr_bind, qWeight_instr_bind]
      rw [countBound_query_bind] at hc
      have hc' : CountBound (isGameQ (Req := Req) (Resp := Resp)) (k H) n := by simpa [isGameQ] using hc ⟨0, Nat.zero_lt_one⟩
      have h := leafW_bind_aux (A := progReg X Y E) (oracleRt H) LocalSig.Interp.instruments
        (portStep (E := E) H) (fun _ ↦ iflat ch n s x) M hM Ev
      rw [Fintype.sum_unique] at h
      refine Eq.trans h ?_
      change _ = ∑ i : Fin (0 + 1), qWeight Ev (PQ.Interactive.close (detImpl ch) (k H) s) ((portInstr H).branch i M)
      rw [Fin.sum_univ_one]
      exact (hx St ch s).2 Ev H _ (((portStep (E := E) H).isCP_branch ()).posSemidef hM) hc'
  | query t k q _ ih =>
    intro n
    rcases t with m | t
    · choose x hx using fun i ↦ ih i n
      refine ⟨iPrim n (instrOp (coinIdx X Y E m)) fun b ↦ x b,
        fun St ch s ↦ ⟨?_, fun Ev _ H M hM hc ↦ ?_⟩⟩
      · rw [iflat_iPrim]
        exact (QuantumComp.isQueryBound_primBind_iff _ _ _).2 fun b ↦ (hx b St ch s).1
      · rw [iflat_iPrim]
        rw [countBound_query_bind] at hc
        have hc' : ∀ i, CountBound (isGameQ (Req := Req) (Resp := Resp)) (k i H) n := by simpa [isGameQ] using hc
        change _ = qWeight Ev (PQ.Interactive.close (detImpl ch)
          (liftM ((instrSpec (WS X Y E) + (unifSpec + (Req →ₒ Resp))).query
            (Sum.inr (Sum.inl m))) >>= fun r ↦ k r H) s) M
        rw [close_unif_bind (detImpl ch) (forwardsUnif_ofLift_add _), qWeight_unif_bind]
        have h := leafW_bind_aux (A := progReg X Y E) (oracleRt H) LocalSig.Interp.instruments
          ((LocalSig.Interp.instruments (instrOp (coinIdx X Y E m))).frame (QReg.of Unit))
          (fun b ↦ iflat ch n s (x b)) M hM Ev
        refine Eq.trans h ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        have hc0 : (0 : ℝ) ≤ ((m : ℝ) + 1)⁻¹ := by positivity
        have hpos : ((LocalSig.Interp.instruments (instrOp (coinIdx X Y E m))).frame
            (QReg.of Unit)).branch i M |>.PosSemidef :=
          ((framedIdx (coinIdx X Y E m)).2.1.isCP_branch i).posSemidef hM
        have hb := coin_frame_branch (X := X) (Y := Y) (E := E) m i M
        rw [(hx i St ch s).2 Ev H _ hpos (hc' i), hb, qWeight_smul _ _ _ hc0]
        congr 1
        rw [ENNReal.ofReal_inv_of_pos (by positivity),
          ENNReal.ofReal_add (by positivity) zero_le_one]
        simp
    · cases n with
      | zero =>
        refine ⟨iPure 0 (Classical.arbitrary α), fun St ch s ↦ ⟨?_, fun Ev _ H M _ hc ↦ ?_⟩⟩
        · rw [iflat_iPure]
          exact QuantumComp.isQueryBound_pure _ _
        · rw [countBound_query_bind] at hc
          simp [isGameQ] at hc
      | succ n =>
        choose x hx using fun r ↦ ih r n
        refine ⟨QuantumComp.pure (.inr (t, fun r ↦ x r)), fun St ch s ↦ ⟨?_, fun Ev _ H M hM hc ↦ ?_⟩⟩
        · rw [iflat_req]
          exact (hx _ St ch (ch t s).2).1
        · rw [iflat_req]
          change _ = qWeight Ev (PQ.Interactive.close (detImpl ch)
            (liftM ((instrSpec (WS X Y E) + (unifSpec + (Req →ₒ Resp))).query
              (Sum.inr (Sum.inr t))) >>= fun r ↦ k r H) s) M
          rw [close_detImpl_game]
          rw [countBound_query_bind] at hc
          have hc' : CountBound (isGameQ (Req := Req) (Resp := Resp)) (k (ch t s).1 H) n := by
            simpa [isGameQ] using hc.2 (ch t s).1
          exact (hx _ St ch (ch t s).2).2 Ev H M hM hc'
  | eval x₀ k q _ ih =>
    intro n
    choose x hx using fun y ↦ ih y n
    refine ⟨iEval n x₀ fun y ↦ x y, fun St ch s ↦ ⟨?_, fun Ev _ H M hM hc ↦ ?_⟩⟩
    · rw [iflat_iEval]
      have hb := PQ.QROM.fidBind_isQueryBound
        (QComp.isQueryBound_callBasis (spec := qromSpec X Y) (p := ()) (b := fun _ ↦ 1)
          Nat.one_pos (progReg X Y E) (x₀, (0 : Y)) (fun o _ ↦ o.2)) fun y ↦ (hx y St ch s).1
      have e : ((fun _ ↦ 1) + fun _ ↦ q : (qromSpec X Y).Port → ℕ) = fun _ ↦ q + 1 := by
        funext u
        simp [add_comm]
      rw [e] at hb
      exact hb
    · rw [← (hx (H x₀) St ch s).2 Ev H M hM hc, iflat_iEval]
      unfold leafW
      refine tsum_congr fun p ↦ ?_
      have key := PQ.QROM.fid_run_fidBind_det (oracleRt H) LocalSig.Interp.instruments
        (QComp.callBasis (spec := qromSpec X Y) () (progReg X Y E) (x₀, (0 : Y)) (fun o _ ↦ o.2))
        (fun y ↦ iflat ch n s (x y)) p M M (H x₀)
        (by rw [run₂_callBasis_branch]; simp)
        (fun y hy ↦ by rw [run₂_callBasis_branch]; simp [Ne.symm hy])
      exact congrArg (fun m ↦ if Ev p.2 then ENNReal.ofReal m.trace.re else 0) key

/-- **Compiler, `qprob` form**, initial states `ρ ⊗ |()⟩⟨()|`. -/
theorem PUE.exists_iadv_qprob [Nonempty α]
    {Mach : (X → Y) → QOC (WS X Y E) (unifSpec + (Req →ₒ Resp)) α} {q : ℕ}
    (h : PUE (fun _ ↦ 0) Mach q) (n : ℕ) :
    ∃ x : IA X Y E Req Resp α n (progReg X Y E),
      PQ.QROM.IAdv.IsQueryBound n x (fun _ ↦ q) ∧
      ∀ (St : Type) (ch : Req → St → Resp × St) (s : St) (Ev : α × St → Prop) [DecidablePred Ev]
        (H : X → Y) (ρ : SubState ((X × Y) × E)), CountBound (isGameQ (Req := Req) (Resp := Resp)) (Mach H) n →
        PQ.QROM.qprob LocalSig.Interp.instruments H (iflat ch n s x) ρ (fun p ↦ Ev p.2) =
          qWeight Ev (PQ.Interactive.close (detImpl ch) (Mach H) s) (ρ.matrix ⊗ₖ (SubState.basis ()).matrix) := by
  obtain ⟨x, hx, hxe⟩ := h.exists_iadv n
  refine ⟨x, hx, fun St ch s Ev _ H ρ hc ↦ ?_⟩
  have hM : (ρ.matrix ⊗ₖ (SubState.basis ()).matrix).PosSemidef :=
    (ρ.prod (SubState.basis ())).posSemidef
  rw [← hxe St ch s Ev H _ hM hc]
  unfold PQ.QROM.qprob
  rw [additiveOracleRuntime_eq, QuantumRuntime.evalDistMap_apply _ _ _ _ _
    (MeasurableSet.of_discrete)]
  unfold leafW
  refine tsum_congr fun p ↦ ?_
  rw [QuantumRuntime.matrix_jointPost]
  by_cases hp : Ev p.2 <;> simp [hp, Set.indicator]

/-! ## Weighted counts through interpretations -/

/-- A stateless interpretation in which each query `t` has weighted count `w t` maps a program of
weighted count `n` to one of weighted count `n`. -/
theorem WCount.simulateQ {κ κ' : Type} {sp : OracleSpec κ} {sp' : OracleSpec κ'}
    {w : sp.Domain → ℕ} {w' : sp'.Domain → ℕ} (impl : QueryImpl sp (OracleComp sp'))
    (hi : ∀ t, WCount w' (impl t) (w t)) {P : OracleComp sp α} {n : ℕ} (hP : WCount w P n) :
    WCount w' (_root_.simulateQ impl P) n := by
  induction P using OracleComp.inductionOn generalizing n with
  | pure a => exact trivial
  | query_bind t k ih =>
    rw [wCount_query_bind] at hP
    rw [simulateQ_bind, simulateQ_spec_query]
    have h := WCount.bind (hi t) fun r ↦ ih r (hP.2 r)
    exact h.mono (by omega)

/-- The stateful analogue. -/
theorem WCount.simulateQ_run {κ κ' : Type} {sp : OracleSpec κ} {sp' : OracleSpec κ'} {σ : Type}
    {w : sp.Domain → ℕ} {w' : sp'.Domain → ℕ} (impl : QueryImpl sp (StateT σ (OracleComp sp')))
    (hi : ∀ t s, WCount w' ((impl t).run s) (w t)) {P : OracleComp sp α} {n : ℕ}
    (hP : WCount w P n) (s : σ) : WCount w' ((_root_.simulateQ impl P).run s) n := by
  induction P using OracleComp.inductionOn generalizing n s with
  | pure a => exact trivial
  | query_bind t k ih =>
    rw [wCount_query_bind] at hP
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    have h := WCount.bind (hi t s) fun r ↦ ih r.1 (hP.2 r.1) r.2
    exact h.mono (by omega)

theorem countBound_iff_wCount {κ : Type} {sp : OracleSpec κ} (p : κ → Prop) [DecidablePred p]
    (P : OracleComp sp α) (n : ℕ) :
    CountBound p P n ↔ WCount (fun t ↦ if p t then 1 else 0) P n := by
  induction P using OracleComp.inductionOn generalizing n with
  | pure a => exact Iff.rfl
  | query_bind t k ih =>
    rw [countBound_query_bind, wCount_query_bind]
    by_cases hp : p t
    · simp only [hp, ite_true]
      constructor
      · rintro ⟨h0, h⟩
        exact ⟨h0, fun r ↦ (ih r _).1 (h r)⟩
      · rintro ⟨h0, h⟩
        exact ⟨h0, fun r ↦ (ih r _).2 (h r)⟩
    · simp only [hp, ite_false, Nat.sub_zero, zero_le, true_and]
      exact forall_congr' fun r ↦ ih r n

/-- Weighted counts are antitone in the weights. -/
theorem WCount.wmono {κ : Type} {sp : OracleSpec κ} {w w' : sp.Domain → ℕ}
    (hw : ∀ t, w t ≤ w' t) {P : OracleComp sp α} {n : ℕ} (h : WCount w' P n) : WCount w P n := by
  induction P using OracleComp.inductionOn generalizing n with
  | pure a => exact trivial
  | query_bind t k ih =>
    rw [wCount_query_bind] at h ⊢
    refine ⟨(hw t).trans h.1, fun r ↦ ((ih r (h.2 r)).mono ?_)⟩
    have := hw t
    omega

section qoc

variable {W : Type} [Fintype W] {ι ι' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'}
  {τ : Type}

/-- Instrument nodes weigh `0`, classical queries `w`. -/
abbrev qw (W : Type) [Fintype W] (w : ι → ℕ) : (instrSpec W + spec).Domain → ℕ :=
  Sum.elim (fun _ ↦ 0) w

theorem WCount.liftQ {w : spec.Domain → ℕ} {ob : OracleComp spec α} {n : ℕ} (h : WCount w ob n) :
    WCount (qw W (spec := spec) w) (PQ.Interactive.liftQ (W := W) ob) n :=
  WCount.simulateQ (w' := qw W (spec := spec) w)
    (fun t ↦ (liftM ((instrSpec W + spec).query (Sum.inr t)) : QOC W spec _))
    (fun _ ↦ wCount_liftM_query _ _ le_rfl) h

theorem WCount.wrap0 (h : QueryImpl spec (OracleComp (unifSpec + spec')))
    {w : spec.Domain → ℕ} {w' : (unifSpec + spec').Domain → ℕ} (hc : ∀ t, WCount w' (h t) (w t))
    {Q : QOC W spec α} {n : ℕ} (hQ : WCount (qw W w) Q n) :
    WCount (qw W w') (PQ.Interactive.wrap0 h Q) n := by
  refine WCount.simulateQ _ (fun t ↦ ?_) hQ
  rcases t with j | t
  · exact wCount_liftM_query _ _ le_rfl
  · exact WCount.liftQ (hc t)

theorem WCount.wrap (implB : QueryImpl spec (StateT τ (OracleComp (unifSpec + spec'))))
    {w : spec.Domain → ℕ} {w' : (unifSpec + spec').Domain → ℕ}
    (hc : ∀ t s, WCount w' ((implB t).run s) (w t))
    {Q : QOC W spec α} {n : ℕ} (hQ : WCount (qw W w) Q n) (s : τ) :
    WCount (qw W w') (PQ.Interactive.wrap implB Q s) n := by
  refine WCount.simulateQ_run _ (fun t s ↦ ?_) hQ s
  rcases t with j | t
  · exact WCount.map (wCount_liftM_query _ _ le_rfl) _
  · exact WCount.liftQ (hc t s)

theorem WCount.compileQ {X Y E : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    [AddCommGroup Y] [Fintype E] [DecidableEq E] (H : X → Y) {w : spec.Domain → ℕ}
    {P : QOC ((X × Y) × E) (portSpec + spec) α} {n : ℕ}
    (hP : WCount (qw ((X × Y) × E) (Sum.elim (fun _ ↦ 0) w)) P n) :
    WCount (qw (WS X Y E) w) (PQ.Interactive.compileQ H P) n := by
  refine WCount.simulateQ _ (fun t ↦ ?_) hP
  rcases t with j | ⟨⟨⟩⟩ | t
  · exact wCount_liftM_query _ _ le_rfl
  · exact WCount.map (wCount_liftM_query _ _ le_rfl) _
  · exact wCount_liftM_query _ _ le_rfl

end qoc

end PQ.Interactive

open PQ.Interactive in
#print axioms PUE.exists_iadv
open PQ.Interactive in
#print axioms PUE.exists_iadv_qprob
open PQ.Interactive in
#print axioms WCount.simulateQ_run
open PQ.Interactive in
#print axioms countBound_iff_wCount
