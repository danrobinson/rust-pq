import PQ.Interactive.QromBridgeEval

/-!
# Part-2 programs and hybrid models of closed `PUE` machines

* `PUE.exists_prog`: a closed `PUE` machine with budget `q` (`cnt0`: sampling free) has ONE VCVio
  quantum query program `x` (independent of the port function `H`) with at most `q` oracle calls,
  whose Part-2 leaf weight against `U_H` equals the Part-1 Born weight of `Mach H`.  Classical
  evaluation nodes become `QComp.callBasis` on the program register (`run₂_callBasis_branch`).
* `PUE.exists_prog_qprob`: the same for `PQ.QROM.qprob` and initial states `ρ ⊗ |()⟩⟨()|`.
* `PUE.exists_model`: hence a `PQ.QROM.HybridModel X Y α q`.
* `PUE.compileQ`: compiled port programs are `PUE`, for a weighted count of the program; and
  `wCount_of_countBound`: `CountBound isPort P q` and `CountBound isSign P qs` give that weighted
  count with total `q + qs * c` when every signing query weighs `c`.
-/

open OracleComp OracleSpec ENNReal Quantum MeasureTheory Matrix
open scoped Kronecker ComplexOrder

set_option linter.unusedSectionVars false

namespace PQ.Interactive

variable {X Y E : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
  [Fintype E] [DecidableEq E] {α β γ : Type} {ι : Type} {spec : OracleSpec ι}

/-- **Bridge for closed `PUE` machines, matrix form.** -/
theorem PUE.exists_prog {Mach : (X → Y) → Closed (WS X Y E) α} {q : ℕ}
    (h : PUE (spec := unifSpec) cnt0 Mach q) :
    ∃ x : QuantumComp LocalSig.instruments.{0} (qromSpec X Y) (fun _ ↦ α) (progReg X Y E),
      x.IsQueryBound (fun _ ↦ q) ∧
      ∀ (Ev : α → Prop) [DecidablePred Ev] (H : X → Y) (M : Matrix (WS X Y E) (WS X Y E) ℂ),
        M.PosSemidef →
        leafW (A := progReg X Y E) (oracleRt H) LocalSig.Interp.instruments x M Ev =
          qWeight Ev (Mach H) M := by
  induction h with
  | pure a q =>
    refine ⟨QuantumComp.pure a, QuantumComp.isQueryBound_pure _ _, fun Ev _ H M _ ↦ ?_⟩
    rw [qWeight_pure]
    exact leafW_pure (oracleRt H) LocalSig.Interp.instruments a M Ev
  | instr j k q _ ih =>
    choose x hx hxe using ih
    refine ⟨QuantumComp.primBind (instrOp j) fun b ↦ x b,
      (QuantumComp.isQueryBound_primBind_iff _ _ _).2 hx, fun Ev _ H M hM ↦ ?_⟩
    rw [qWeight_instr_bind]
    have h := leafW_bind_aux (A := progReg X Y E) (oracleRt H) LocalSig.Interp.instruments
      ((LocalSig.Interp.instruments (instrOp j)).frame (QReg.of Unit)) (fun b ↦ x b) M hM Ev
    refine Eq.trans h ?_
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    exact hxe i Ev H _ (((framedIdx j).2.1.isCP_branch i).posSemidef hM)
  | port k q _ ih =>
    obtain ⟨x, hx, hxe⟩ := ih
    refine ⟨QuantumComp.queryBind (spec := qromSpec X Y) () (QReg.of E) (idSplit X Y E)
      fun _ ↦ x, ?_, fun Ev _ H M hM ↦ ?_⟩
    · rw [QuantumComp.isQueryBound_queryBind_iff]
      refine ⟨Nat.succ_pos q, fun _ ↦ ?_⟩
      have e : Function.update (fun _ : (qromSpec X Y).Port ↦ q + 1) () (q + 1 - 1) =
          fun _ ↦ q := by
        funext u
        simp
      rw [e]
      exact hx
    · rw [qWeight_instr_bind]
      have h := leafW_bind_aux (A := progReg X Y E) (oracleRt H) LocalSig.Interp.instruments
        (portStep (E := E) H) (fun _ ↦ x) M hM Ev
      rw [Fintype.sum_unique] at h
      refine Eq.trans h ?_
      change _ = ∑ i : Fin (0 + 1), qWeight Ev (k H) ((portInstr H).branch i M)
      rw [Fin.sum_univ_one]
      exact hxe Ev H _ (((portStep (E := E) H).isCP_branch ()).posSemidef hM)
  | query n k q _ ih =>
    choose x hx hxe using ih
    refine ⟨QuantumComp.primBind (instrOp (coinIdx X Y E n)) fun b ↦ x b,
      (QuantumComp.isQueryBound_primBind_iff _ _ _).2 hx, fun Ev _ H M hM ↦ ?_⟩
    rw [qWeight_unif_bind]
    have h := leafW_bind_aux (A := progReg X Y E) (oracleRt H) LocalSig.Interp.instruments
      ((LocalSig.Interp.instruments (instrOp (coinIdx X Y E n))).frame (QReg.of Unit))
      (fun b ↦ x b) M hM Ev
    refine Eq.trans h ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have hc : (0 : ℝ) ≤ ((n : ℝ) + 1)⁻¹ := by positivity
    have hpos : ((LocalSig.Interp.instruments (instrOp (coinIdx X Y E n))).frame
        (QReg.of Unit)).branch i M |>.PosSemidef :=
      ((framedIdx (coinIdx X Y E n)).2.1.isCP_branch i).posSemidef hM
    have hb := coin_frame_branch (X := X) (Y := Y) (E := E) n i M
    rw [hxe i Ev H _ hpos, hb, qWeight_smul _ _ _ hc]
    congr 1
    rw [ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_add (by positivity) zero_le_one]
    simp
  | eval x₀ k q _ ih =>
    choose x hx hxe using ih
    refine ⟨PQ.QROM.fidBind
      (QComp.callBasis (spec := qromSpec X Y) () (progReg X Y E) (x₀, (0 : Y)) (fun o _ ↦ o.2))
      (fun y ↦ x y), ?_, fun Ev _ H M hM ↦ ?_⟩
    · have hb := PQ.QROM.fidBind_isQueryBound
        (QComp.isQueryBound_callBasis (spec := qromSpec X Y) (p := ()) (b := fun _ ↦ 1)
          Nat.one_pos (progReg X Y E) (x₀, (0 : Y)) (fun o _ ↦ o.2)) hx
      have e : ((fun _ ↦ 1) + fun _ ↦ q : (qromSpec X Y).Port → ℕ) = fun _ ↦ q + 1 := by
        funext u
        simp [add_comm]
      rw [e] at hb
      exact hb
    · rw [← hxe (H x₀) Ev H M hM]
      unfold leafW
      refine tsum_congr fun p ↦ ?_
      have key := PQ.QROM.fid_run_fidBind_det (oracleRt H) LocalSig.Interp.instruments
        (QComp.callBasis (spec := qromSpec X Y) () (progReg X Y E) (x₀, (0 : Y)) (fun o _ ↦ o.2))
        (fun y ↦ x y) p M M (H x₀)
        (by rw [run₂_callBasis_branch]; simp)
        (fun y hy ↦ by rw [run₂_callBasis_branch]; simp [Ne.symm hy])
      exact congrArg (fun m ↦ if Ev p.2 then ENNReal.ofReal m.trace.re else 0) key

/-- **Bridge for closed `PUE` machines.**  One VCVio program for all `H`: its Part-2 probability
(`PQ.QROM.qprob`) of any event equals the Part-1 Born weight of `Mach H` started in
`ρ ⊗ |()⟩⟨()|`. -/
theorem PUE.exists_prog_qprob {Mach : (X → Y) → Closed (WS X Y E) α} {q : ℕ}
    (h : PUE (spec := unifSpec) cnt0 Mach q) :
    ∃ x : QuantumComp LocalSig.instruments.{0} (qromSpec X Y) (fun _ ↦ α) (progReg X Y E),
      x.IsQueryBound (fun _ ↦ q) ∧
      ∀ (Ev : α → Prop) [DecidablePred Ev] (H : X → Y) (ρ : SubState ((X × Y) × E)),
        PQ.QROM.qprob LocalSig.Interp.instruments H x ρ (fun p ↦ Ev p.2) =
          qWeight Ev (Mach H) (ρ.matrix ⊗ₖ (SubState.basis ()).matrix) := by
  obtain ⟨x, hx, hxe⟩ := h.exists_prog
  refine ⟨x, hx, fun Ev _ H ρ ↦ ?_⟩
  have hM : (ρ.matrix ⊗ₖ (SubState.basis ()).matrix).PosSemidef :=
    (ρ.prod (SubState.basis ())).posSemidef
  rw [← hxe Ev H _ hM]
  unfold PQ.QROM.qprob
  rw [additiveOracleRuntime_eq, QuantumRuntime.evalDistMap_apply _ _ _ _ _
    (MeasurableSet.of_discrete)]
  unfold leafW
  refine tsum_congr fun p ↦ ?_
  rw [QuantumRuntime.matrix_jointPost]
  by_cases hp : Ev p.2 <;> simp [hp, Set.indicator]

/-- **Hybrid model of a closed `PUE` machine.**  For a fixed initial state `ρ ⊗ |()⟩⟨()|`, the
Born weights of the family `Mach` are the probabilities of one `HybridModel` with `q` queries. -/
theorem PUE.exists_model {Mach : (X → Y) → Closed (WS X Y E) α} {q : ℕ}
    (h : PUE (spec := unifSpec) cnt0 Mach q) (ρ : SubState ((X × Y) × E)) :
    ∃ Mo : PQ.QROM.HybridModel X Y α q, ∀ (H : X → Y) (Ev : α → Prop) [DecidablePred Ev],
      Mo.prob H Ev = qWeight Ev (Mach H) (ρ.matrix ⊗ₖ (SubState.basis ()).matrix) := by
  obtain ⟨x, hx, hxe⟩ := h.exists_prog_qprob
  refine ⟨PQ.QROM.HybridModel.ofProgram LocalSig.Interp.instruments x ρ q hx Sigma.snd,
    fun H Ev _ ↦ ?_⟩
  exact hxe Ev H ρ

/-! ## Compiled port programs -/

/-- The weight of a compiled port program's queries: instruments free, port calls `1`, a classical
query `t` of the interface `cnt t`. -/
def compileW (cnt : ι → ℕ) : (instrSpec ((X × Y) × E) + (portSpec + spec)).Domain → ℕ :=
  Sum.elim (fun _ ↦ 0) (Sum.elim (fun _ ↦ 1) cnt)

/-- **Compiled port programs are `PUE`**, for the weighted count of the program. -/
theorem PUE.compileQ (cnt : ι → ℕ) (P : QOC ((X × Y) × E) (portSpec + spec) α) (n : ℕ)
    (hP : WCount (compileW (X := X) (Y := Y) (E := E) cnt) P n) :
    PUE cnt (fun H ↦ PQ.Interactive.compileQ H P) n := by
  induction P using OracleComp.inductionOn generalizing n with
  | pure a =>
    simp only [compileQ_pure]
    exact PUE.pure a n
  | query_bind t k ih =>
    rw [wCount_query_bind] at hP
    rcases t with j | ⟨⟨⟩⟩ | t
    · simp only [compileQ_instr_bind]
      have hP' : ∀ r, WCount (compileW (X := X) (Y := Y) (E := E) cnt) (k r) n := by
        simpa [compileW] using hP.2
      exact PUE.instr j (fun i H ↦ PQ.Interactive.compileQ H (k i)) n fun i ↦ ih i n (hP' i)
    · simp only [compileQ_port_bind]
      have h1 : 1 ≤ n := by simpa [compileW] using hP.1
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      have hP' : WCount (compileW (X := X) (Y := Y) (E := E) cnt) (k ()) n' := by
        simpa [compileW] using hP.2 ()
      exact PUE.port (fun H ↦ PQ.Interactive.compileQ H (k ())) n' (ih () n' hP')
    · simp only [compileQ_query_bind]
      have h1 : cnt t ≤ n := by simpa [compileW] using hP.1
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + cnt t := ⟨n - cnt t, by omega⟩
      have hP' : ∀ r, WCount (compileW (X := X) (Y := Y) (E := E) cnt) (k r) n' := by
        intro r
        simpa [compileW] using hP.2 r
      exact PUE.query t (fun r H ↦ PQ.Interactive.compileQ H (k r)) n' fun r ↦ ih r n' (hP' r)

/-- Two count bounds give a weighted count: port calls weigh `1`, the queries `t` with
`counted t` weigh `c` (each such query is a `Sum.inr (Sum.inr t)` query), everything else `0`.
Stated for any classical program; `isPort`/`isSign` below. -/
theorem wCount_of_countBound {κ : Type} {sp : OracleSpec κ} (isP isS : κ → Prop)
    [DecidablePred isP] [DecidablePred isS] (w : κ → ℕ) (c : ℕ)
    (hw : ∀ t, w t ≤ (if isP t then 1 else 0) + (if isS t then c else 0))
    (P : OracleComp sp α) (q qs : ℕ) (hq : CountBound isP P q) (hs : CountBound isS P qs) :
    WCount w P (q + qs * c) := by
  induction P using OracleComp.inductionOn generalizing q qs with
  | pure a => exact trivial
  | query_bind t k ih =>
    rw [countBound_query_bind] at hq hs
    rw [wCount_query_bind]
    have hwt := hw t
    by_cases hp : isP t <;> by_cases hS : isS t <;> simp only [hp, hS, ite_true, ite_false] at hq hs hwt
    · obtain ⟨hq0, hq⟩ := hq
      obtain ⟨hs0, hs⟩ := hs
      refine ⟨?_, fun r ↦ ?_⟩
      · nlinarith
      · have := ih r (q - 1) (qs - 1) (hq r) (hs r)
        refine this.mono ?_
        obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
        obtain ⟨s', rfl⟩ : ∃ s', qs = s' + 1 := ⟨qs - 1, by omega⟩
        simp only [Nat.add_sub_cancel]
        have : w t ≤ 1 + c := hwt
        rw [Nat.add_mul, one_mul]
        omega
    · obtain ⟨hq0, hq⟩ := hq
      refine ⟨by omega, fun r ↦ ?_⟩
      refine (ih r (q - 1) qs (hq r) (hs r)).mono ?_
      omega
    · obtain ⟨hs0, hs⟩ := hs
      refine ⟨?_, fun r ↦ ?_⟩
      · obtain ⟨s', rfl⟩ : ∃ s', qs = s' + 1 := ⟨qs - 1, by omega⟩
        rw [Nat.add_mul, one_mul]
        omega
      · refine (ih r q (qs - 1) (hq r) (hs r)).mono ?_
        obtain ⟨s', rfl⟩ : ∃ s', qs = s' + 1 := ⟨qs - 1, by omega⟩
        simp only [Nat.add_sub_cancel]
        rw [Nat.add_mul, one_mul]
        omega
    · refine ⟨by omega, fun r ↦ ?_⟩
      refine (ih r q qs (hq r) (hs r)).mono ?_
      omega

/-! ## Small weighted-count facts -/

theorem WCount.map {κ : Type} {sp : OracleSpec κ} {w : sp.Domain → ℕ} {oa : OracleComp sp α}
    {n : ℕ} (h : WCount w oa n) (f : α → β) : WCount w (f <$> oa) n := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure a => exact trivial
  | query_bind t k ih =>
    rw [wCount_query_bind] at h
    rw [map_bind, wCount_query_bind]
    exact ⟨h.1, fun r ↦ ih r (h.2 r)⟩

theorem wCount_liftM_query {κ : Type} {sp : OracleSpec κ} (w : sp.Domain → ℕ) (t : sp.Domain)
    {n : ℕ} (h : w t ≤ n) : WCount w (liftM (sp.query t) : OracleComp sp _) n := by
  have e : (liftM (sp.query t) : OracleComp sp _) = liftM (sp.query t) >>= pure := (bind_pure _).symm
  rw [e, wCount_query_bind]
  exact ⟨h, fun _ ↦ trivial⟩

/-- A predicate-targeted query bound is a weighted count with indicator weights. -/
theorem wCount_of_isQueryBoundP {κ : Type} {sp : OracleSpec κ} (p : κ → Prop) [DecidablePred p]
    (P : OracleComp sp α) (n : ℕ) (h : IsQueryBoundP P p n) :
    WCount (fun t ↦ if p t then 1 else 0) P n := by
  induction P using OracleComp.inductionOn generalizing n with
  | pure a => exact trivial
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at h
    rw [wCount_query_bind]
    refine ⟨?_, fun r ↦ ?_⟩
    · by_cases hp : p t
      · simp only [hp, ite_true]
        rcases h.1 with h1 | h1
        · exact absurd hp h1
        · omega
      · simp [hp]
    · have := ih r _ (h.2 r)
      by_cases hp : p t <;> simpa [hp] using this

end PQ.Interactive

open PQ.Interactive in
#print axioms PUE.exists_prog
open PQ.Interactive in
#print axioms PUE.exists_prog_qprob
open PQ.Interactive in
#print axioms PUE.exists_model
open PQ.Interactive in
#print axioms PUE.compileQ
open PQ.Interactive in
#print axioms wCount_of_countBound
open PQ.Interactive in
#print axioms wCount_of_isQueryBoundP
