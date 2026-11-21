import PQ.Interactive.QromBridgeSpec
import PQ.Interactive.Wrap
import PQ.Interactive.Collapse
import PQ.Interactive.Games

/-!
# Bridge for machines with uniform-sampling nodes and classical wrappers: port-uniform machines

`PU Mach q` ("port-uniform"): `Mach : (X → Y) → QOC (WS X Y E) spec α` is a family of Part-1
machines, one per port function `H`, whose control tree does NOT depend on `H` except that its
oracle-call nodes are the instrument `U_H` (`portIdx H`); all other instrument nodes are framed
instruments on the program register, and at most `q` oracle calls are made on every path.

* `PU.compileQ`: the compiled machine of a port program with `CountBound isPort P q` is `PU`.
* closure: `PU.bind`, `PU.liftQ_bind`, `PU.map`, `PU.wrap`, `PU.wrap0`, and `PU.close` (closing
  with ANY stateful probabilistic classical implementation, so probabilistic and lazy challengers
  are covered: the closed machine has only instrument, port and uniform-sampling nodes).
* `PU.exists_prog`: for a closed port-uniform machine there is ONE VCVio quantum query program
  `x` (independent of `H`) with at most `q` oracle calls such that for every `H`, every positive
  semidefinite matrix and every event, the Part-2 leaf weight of `x` against `U_H` equals the
  Part-1 Born weight of `Mach H`.  Uniform-sampling nodes become the uniform-coin instrument
  (`SubInstrument.uniform`).
* `PU.exists_prog_qprob`: the same with `PQ.QROM.qprob` for initial states `ρ ⊗ |()⟩⟨()|`.

Also: `qWeight_smul` (homogeneity of the Born weight), `qWeight_liftU_bind_sum` and
`qWeight_liftU_uniform_bind` (classical sampling in front of a machine).
-/

open OracleComp OracleSpec ENNReal Quantum MeasureTheory Matrix
open scoped Kronecker ComplexOrder

set_option linter.unusedSectionVars false

namespace PQ.Interactive

section basic

variable {W : Type} [Fintype W] {α β γ : Type}

/-- Homogeneity of the Born weight in the (unnormalised) state. -/
lemma qWeight_smul (p : α → Prop) [DecidablePred p] (X : Closed W α) (c : ℝ) (hc : 0 ≤ c)
    (ρ : Matrix W W ℂ) : qWeight p X ((c : ℂ) • ρ) = ENNReal.ofReal c * qWeight p X ρ := by
  induction X using OracleComp.inductionOn generalizing ρ with
  | pure a =>
    simp only [qWeight_pure]
    split_ifs
    · rw [Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul, ENNReal.ofReal_mul hc]
    · simp
  | query_bind t k ih =>
    rcases t with j | n
    · rw [qWeight_instr_bind, qWeight_instr_bind, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [map_smul, ih]
    · rw [qWeight_unif_bind, qWeight_unif_bind]
      simp only [ih]
      rw [← Finset.mul_sum]
      ring

/-- Classical sampling in front of a machine: the Born weight is the average over the sample. -/
lemma qWeight_liftU_bind_sum [Fintype γ] [DecidableEq γ] (p : α → Prop) [DecidablePred p]
    (oa : ProbComp γ) (f : γ → Closed W α) (ρ : Matrix W W ℂ) :
    qWeight p (liftU oa >>= f) ρ = ∑ x, prob oa (· = x) * qWeight p (f x) ρ := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    rw [liftU_pure, pure_bind]
    simp only [prob_pure]
    rw [Finset.sum_eq_single a]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · simp
  | query_bind n k ih =>
    rw [liftU_query_bind, bind_assoc, qWeight_unif_bind]
    simp only [ih, prob_unif_query_bind]
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    rw [← Finset.sum_mul, mul_assoc]

/-- The canonical sampler hits every point with probability `1/|T|`. -/
lemma prob_uniformSample_eq {T : Type} [Fintype T] [SampleableType T] (x : T) :
    prob ($ᵗ T) (· = x) = (Fintype.card T : ℝ≥0∞)⁻¹ := by
  letI : MeasurableSpace T := ⊤
  haveI : MeasurableSingletonClass T := ⟨fun _ ↦ MeasurableSpace.measurableSet_top⟩
  unfold prob
  rw [prEvent_eq_evalDist_singleton, SampleableType.evalDist_uniformSample,
    ProbabilityTheory.uniformOn_univ]
  simp

/-- Uniform sampling of a finite type in front of a machine. -/
lemma qWeight_liftU_uniform_bind {T : Type} [Fintype T] [DecidableEq T] [SampleableType T]
    (p : α → Prop) [DecidablePred p] (f : T → Closed W α) (ρ : Matrix W W ℂ) :
    qWeight p (liftU ($ᵗ T) >>= f) ρ =
      (Fintype.card T : ℝ≥0∞)⁻¹ * ∑ x, qWeight p (f x) ρ := by
  rw [qWeight_liftU_bind_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ ↦ by rw [prob_uniformSample_eq]

lemma liftU_eq_liftQ (oa : ProbComp γ) : (liftU oa : Closed W γ) = liftQ oa := rfl

end basic

variable {X Y E : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
  [Fintype E] [DecidableEq E] {α β γ : Type} {ι : Type} {spec : OracleSpec ι}

/-! ## Port-uniform machines -/

/-- Port-uniform families of machines with at most `q` oracle calls on every path. -/
inductive PU {α : Type} : ((X → Y) → QOC (WS X Y E) spec α) → ℕ → Prop
  | pure (a : α) (q : ℕ) : PU (fun _ ↦ Pure.pure a) q
  | instr (j : InstrIdx ((X × Y) × E)) (k : Fin (j.1 + 1) → (X → Y) → QOC (WS X Y E) spec α)
      (q : ℕ) (h : ∀ i, PU (k i) q) :
      PU (fun H ↦ liftM ((instrSpec (WS X Y E) + spec).query (Sum.inl (framedIdx j))) >>=
        fun i ↦ k i H) q
  | port (k : (X → Y) → QOC (WS X Y E) spec α) (q : ℕ) (h : PU k q) :
      PU (fun H ↦ liftM ((instrSpec (WS X Y E) + spec).query (Sum.inl (portIdx H))) >>=
        fun _ ↦ k H) (q + 1)
  | query (t : spec.Domain) (k : spec.Range t → (X → Y) → QOC (WS X Y E) spec α) (q : ℕ)
      (h : ∀ r, PU (k r) q) :
      PU (fun H ↦ liftM ((instrSpec (WS X Y E) + spec).query (Sum.inr t)) >>= fun r ↦ k r H) q

namespace PU

theorem mono {A : (X → Y) → QOC (WS X Y E) spec α} {q : ℕ} (h : PU A q) :
    ∀ {q' : ℕ}, q ≤ q' → PU A q' := by
  induction h with
  | pure a q => exact fun _ ↦ PU.pure a _
  | instr j k q _ ih => exact fun hq ↦ PU.instr j k _ fun i ↦ ih i hq
  | port k q _ ih =>
    intro q' hq
    obtain ⟨q'', rfl⟩ : ∃ q'', q' = q'' + 1 := ⟨q' - 1, by omega⟩
    exact PU.port k q'' (ih (by omega))
  | query t k q _ ih => exact fun hq ↦ PU.query t k _ fun r ↦ ih r hq

theorem bind {A : (X → Y) → QOC (WS X Y E) spec α}
    {B : α → (X → Y) → QOC (WS X Y E) spec β} {q₁ q₂ : ℕ} (hA : PU A q₁)
    (hB : ∀ a, PU (B a) q₂) : PU (fun H ↦ A H >>= fun a ↦ B a H) (q₁ + q₂) := by
  induction hA with
  | pure a q =>
    simp only [pure_bind]
    exact (hB a).mono (by omega)
  | instr j k q _ ih =>
    simp only [bind_assoc]
    exact PU.instr j (fun i H ↦ k i H >>= fun a ↦ B a H) _ ih
  | port k q _ ih =>
    simp only [bind_assoc]
    rw [Nat.add_right_comm]
    exact PU.port (fun H ↦ k H >>= fun a ↦ B a H) _ ih
  | query t k q _ ih =>
    simp only [bind_assoc]
    exact PU.query t (fun r H ↦ k r H >>= fun a ↦ B a H) _ ih

theorem liftQ_bind (ob : OracleComp spec γ) {B : γ → (X → Y) → QOC (WS X Y E) spec β} {q : ℕ}
    (hB : ∀ c, PU (B c) q) : PU (fun H ↦ liftQ ob >>= fun c ↦ B c H) q := by
  induction ob using OracleComp.inductionOn with
  | pure a =>
    simp only [liftQ_pure, pure_bind]
    exact hB a
  | query_bind t k ih =>
    simp only [liftQ_query_bind, bind_assoc]
    exact PU.query t (fun r H ↦ liftQ (k r) >>= fun c ↦ B c H) _ ih

theorem liftQ (ob : OracleComp spec γ) (q : ℕ) :
    PU (X := X) (Y := Y) (E := E) (fun _ ↦ PQ.Interactive.liftQ ob) q := by
  have h := liftQ_bind (X := X) (Y := Y) (E := E) ob (B := fun c _ ↦ Pure.pure c) (q := q)
    fun c ↦ PU.pure c q
  simpa using h

theorem map (f : α → β) {A : (X → Y) → QOC (WS X Y E) spec α} {q : ℕ} (hA : PU A q) :
    PU (fun H ↦ f <$> A H) q := by
  have h := bind hA (B := fun a _ ↦ Pure.pure (f a)) (q₂ := 0) fun a ↦ PU.pure (f a) 0
  simpa [map_eq_bind_pure_comp] using h

variable {ι' : Type} {spec' : OracleSpec ι'} {σ τ : Type}

theorem wrap (implB : QueryImpl spec (StateT τ (OracleComp (unifSpec + spec'))))
    {A : (X → Y) → QOC (WS X Y E) spec α} {q : ℕ} (hA : PU A q) :
    ∀ t : τ, PU (fun H ↦ PQ.Interactive.wrap implB (A H) t) q := by
  induction hA with
  | pure a q =>
    intro t
    simp only [wrap_pure]
    exact PU.pure _ _
  | instr j k q _ ih =>
    intro t
    simp only [wrap_instr_bind]
    exact PU.instr j (fun i H ↦ PQ.Interactive.wrap implB (k i H) t) _ fun i ↦ ih i t
  | port k q _ ih =>
    intro t
    simp only [wrap_instr_bind]
    exact PU.port (fun H ↦ PQ.Interactive.wrap implB (k H) t) _ (ih t)
  | query u k q _ ih =>
    intro t
    simp only [wrap_query_bind]
    exact liftQ_bind _ fun x ↦ ih x.1 x.2

theorem wrap0 (h : QueryImpl spec (OracleComp (unifSpec + spec')))
    {A : (X → Y) → QOC (WS X Y E) spec α} {q : ℕ} (hA : PU A q) :
    PU (fun H ↦ PQ.Interactive.wrap0 h (A H)) q := by
  induction hA with
  | pure a q =>
    simp only [wrap0_pure]
    exact PU.pure _ _
  | instr j k q _ ih =>
    simp only [wrap0_instr_bind]
    exact PU.instr j (fun i H ↦ PQ.Interactive.wrap0 h (k i H)) _ ih
  | port k q _ ih =>
    simp only [wrap0_instr_bind]
    exact PU.port (fun H ↦ PQ.Interactive.wrap0 h (k H)) _ ih
  | query u k q _ ih =>
    simp only [wrap0_query_bind]
    exact liftQ_bind _ ih

/-- Closing a port-uniform machine with any stateful probabilistic implementation of its
classical interface gives a port-uniform closed machine. -/
theorem close (impl : QueryImpl spec (StateT σ ProbComp))
    {A : (X → Y) → QOC (WS X Y E) spec α} {q : ℕ} (hA : PU A q) :
    ∀ s : σ, PU (spec := unifSpec) (fun H ↦ PQ.Interactive.close impl (A H) s) q := by
  induction hA with
  | pure a q =>
    intro s
    simp only [close_pure]
    exact PU.pure _ _
  | instr j k q _ ih =>
    intro s
    simp only [close_instr_bind]
    exact PU.instr j (fun i H ↦ PQ.Interactive.close impl (k i H) s) _ fun i ↦ ih i s
  | port k q _ ih =>
    intro s
    simp only [close_instr_bind]
    exact PU.port (fun H ↦ PQ.Interactive.close impl (k H) s) _ (ih s)
  | query u k q _ ih =>
    intro s
    simp only [close_query_bind, liftU_eq_liftQ]
    exact liftQ_bind _ fun x ↦ ih x.1 x.2

/-- Classical sampling in front of a closed port-uniform family. -/
theorem liftU_bind (oa : ProbComp γ) {B : γ → (X → Y) → Closed (WS X Y E) β} {q : ℕ}
    (hB : ∀ c, PU (spec := unifSpec) (B c) q) :
    PU (spec := unifSpec) (fun H ↦ liftU oa >>= fun c ↦ B c H) q := by
  simp only [liftU_eq_liftQ]
  exact liftQ_bind oa hB

end PU

/-! ## Compiled port programs are port-uniform -/

lemma compileQ_pure (H : X → Y) (a : α) :
    compileQ H (pure a : QOC ((X × Y) × E) (portSpec + spec) α) = pure a := by
  simp [compileQ]

lemma compileQ_instr_bind (H : X → Y) (j : InstrIdx ((X × Y) × E))
    (k : Fin (j.1 + 1) → QOC ((X × Y) × E) (portSpec + spec) α) :
    compileQ H (liftM ((instrSpec ((X × Y) × E) + (portSpec + spec)).query (Sum.inl j)) >>= k) =
      liftM ((instrSpec (WS X Y E) + spec).query (Sum.inl (framedIdx j))) >>=
        fun i ↦ compileQ H (k i) := by
  unfold compileQ
  rw [simulateQ_bind, simulateQ_spec_query]
  rfl

lemma compileQ_port_bind (H : X → Y) (k : Unit → QOC ((X × Y) × E) (portSpec + spec) α) :
    compileQ H (liftM ((instrSpec ((X × Y) × E) + (portSpec + spec)).query
        (Sum.inr (Sum.inl ()))) >>= k) =
      liftM ((instrSpec (WS X Y E) + spec).query (Sum.inl (portIdx H))) >>=
        fun _ ↦ compileQ H (k ()) := by
  unfold compileQ
  rw [simulateQ_bind, simulateQ_spec_query]
  change ((fun _ ↦ ()) <$> _) >>= _ = _
  simp

lemma compileQ_query_bind (H : X → Y) (t : spec.Domain)
    (k : spec.Range t → QOC ((X × Y) × E) (portSpec + spec) α) :
    compileQ H (liftM ((instrSpec ((X × Y) × E) + (portSpec + spec)).query
        (Sum.inr (Sum.inr t))) >>= k) =
      liftM ((instrSpec (WS X Y E) + spec).query (Sum.inr t)) >>=
        fun r ↦ compileQ H (k r) := by
  unfold compileQ
  rw [simulateQ_bind, simulateQ_spec_query]
  rfl

lemma countBound_query_bind {κ : Type} {sp : OracleSpec κ} (counted : κ → Prop)
    [DecidablePred counted] (t : sp.Domain) (k : sp.Range t → OracleComp sp α) (q : ℕ) :
    CountBound counted (liftM (sp.query t) >>= k) q =
      if counted t then 0 < q ∧ ∀ r, CountBound counted (k r) (q - 1)
      else ∀ r, CountBound counted (k r) q := rfl

/-- The compiled machines of a port program with at most `q` port calls on every path form a
port-uniform family. -/
theorem PU.compileQ (P : QOC ((X × Y) × E) (portSpec + spec) α) (q : ℕ)
    (hP : CountBound isPort P q) : PU (fun H ↦ PQ.Interactive.compileQ H P) q := by
  induction P using OracleComp.inductionOn generalizing q with
  | pure a =>
    simp only [compileQ_pure]
    exact PU.pure a q
  | query_bind t k ih =>
    rw [countBound_query_bind] at hP
    rcases t with j | ⟨⟨⟩⟩ | t
    · simp only [compileQ_instr_bind]
      have hP' : ∀ r, CountBound isPort (k r) q := by simpa [isPort] using hP
      exact PU.instr j (fun i H ↦ PQ.Interactive.compileQ H (k i)) q fun i ↦ ih i q (hP' i)
    · simp only [compileQ_port_bind]
      have hP' : 0 < q ∧ ∀ r, CountBound isPort (k r) (q - 1) := by simpa [isPort] using hP
      obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
      exact PU.port (fun H ↦ PQ.Interactive.compileQ H (k ())) q' (ih () q' (hP'.2 ()))
    · simp only [compileQ_query_bind]
      have hP' : ∀ r, CountBound isPort (k r) q := by simpa [isPort] using hP
      exact PU.query t (fun r H ↦ PQ.Interactive.compileQ H (k r)) q fun r ↦ ih r q (hP' r)

/-! ## The Part-2 program of a closed port-uniform machine -/

/-- The uniform coin with `n + 1` outcomes as an instrument index on the program register. -/
noncomputable def coinIdx (X Y E : Type) [Fintype X] [Fintype Y] [Fintype E] (n : ℕ) :
    InstrIdx ((X × Y) × E) :=
  ⟨n, SubInstrument.uniform (Fin (n + 1)) ((X × Y) × E), SubInstrument.lossless_uniform _ _⟩

lemma coin_frame_branch (n : ℕ) (i : Fin (n + 1)) (M : Matrix (WS X Y E) (WS X Y E) ℂ) :
    ((LocalSig.Interp.instruments (instrOp (coinIdx X Y E n))).frame (QReg.of Unit)).branch i M =
      ((((n : ℝ) + 1)⁻¹ : ℝ) : ℂ) • M := by
  ext x y
  change ((SubInstrument.uniform (Fin (n + 1)) ((X × Y) × E)).branch i).amplify Unit M x y = _
  rw [MatrixMap.amplify_apply, SubInstrument.branch_uniform_apply]
  simp

/-- **Bridge for closed port-uniform machines, matrix form.** -/
theorem PU.exists_prog {Mach : (X → Y) → Closed (WS X Y E) α} {q : ℕ}
    (h : PU (spec := unifSpec) Mach q) :
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

/-- **Bridge for closed port-uniform machines.**  One VCVio program for all `H`: its Part-2
probability (`PQ.QROM.qprob`) of any event equals the Part-1 Born weight of `Mach H` started in
`ρ ⊗ |()⟩⟨()|`. -/
theorem PU.exists_prog_qprob {Mach : (X → Y) → Closed (WS X Y E) α} {q : ℕ}
    (h : PU (spec := unifSpec) Mach q) :
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

end PQ.Interactive

open PQ.Interactive in
#print axioms qWeight_smul
open PQ.Interactive in
#print axioms qWeight_liftU_uniform_bind
open PQ.Interactive in
#print axioms PU.bind
open PQ.Interactive in
#print axioms PU.wrap
open PQ.Interactive in
#print axioms PU.wrap0
open PQ.Interactive in
#print axioms PU.close
open PQ.Interactive in
#print axioms PU.compileQ
open PQ.Interactive in
#print axioms PU.exists_prog
open PQ.Interactive in
#print axioms PU.exists_prog_qprob
