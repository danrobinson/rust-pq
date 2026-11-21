import PQ.Interactive.Closed

/-!
# Classical strategies of a quantum machine relative to an arbitrary outcome sampler

`toProbComp` (`Collapse.lean`) samples the outcome of every instrument node with its exact Born
probabilities, which is implementable with one uniform query only when these are rational.

Here the recursion is abstracted over the *sampler* `samp : Sampler W`, the classical code used to
draw the outcome of the instrument `j` in the tracked state `ρ`:

* `toProbCompWith samp Q ρ` (open machines), `toProbCompCWith samp X ρ` (closed machines);
* `toProbComp = toProbCompWith exactSamp`, `toProbCompC = toProbCompCWith exactSamp`;
* every *syntactic* commutation lemma of `Wrap.lean` / `Closed.lean` (pre/post-processing,
  `wrap`, `wrap0`, output maps, the forger harness, `close`) holds verbatim for every sampler.

No rationality hypothesis appears anywhere in this file.
-/

open OracleComp OracleSpec ENNReal Quantum MeasureTheory
open scoped ComplexOrder

namespace PQ.Interactive

variable {W : Type} [Fintype W] {α β γ : Type}
variable {ι : Type} {spec : OracleSpec ι} {ι' : Type} {spec' : OracleSpec ι'} {σ τ : Type}

/-- A sampler: classical probabilistic code drawing the outcome of the instrument node `j` when
the tracked (unnormalised) workspace state is `ρ`. -/
abbrev Sampler (W : Type) [Fintype W] : Type :=
  (j : InstrIdx W) → Matrix W W ℂ → ProbComp (Fin (j.1 + 1))

/-- The exact Born sampler of `Collapse.lean` (meaningful only for rational Born
probabilities). -/
noncomputable def exactSamp : Sampler W := fun j ρ ↦ sampleOf (bornW j.2.1 ρ)

/-! ## Open machines -/

/-- The classical strategy of the quantum machine `Q` started in the (unnormalised) state `ρ`,
drawing the outcome of every instrument node with the sampler `samp` and continuing from the true
unnormalised post-measurement state. -/
noncomputable def toProbCompWith (samp : Sampler W) (Q : QOC W (unifSpec + spec') α) :
    Matrix W W ℂ → OracleComp (unifSpec + spec') α :=
  OracleComp.construct (C := fun _ ↦ Matrix W W ℂ → OracleComp (unifSpec + spec') α)
    (fun a _ ↦ pure a)
    (fun t _ ih ρ ↦
      match t, ih with
      | .inl j, ih => liftL (samp j ρ) >>= fun i ↦ ih i (j.2.1.branch i ρ)
      | .inr t, ih => liftM ((unifSpec + spec').query t) >>= fun u ↦ ih u ρ) Q

variable (samp : Sampler W)

@[simp] lemma toProbCompWith_pure (a : α) (ρ : Matrix W W ℂ) :
    toProbCompWith samp (pure a : QOC W (unifSpec + spec') α) ρ = pure a := rfl

lemma toProbCompWith_instr_bind (j : InstrIdx W) (k : Fin (j.1 + 1) → QOC W (unifSpec + spec') α)
    (ρ : Matrix W W ℂ) :
    toProbCompWith samp (liftM ((instrSpec W + (unifSpec + spec')).query (Sum.inl j)) >>= k) ρ =
      liftL (samp j ρ) >>= fun i ↦ toProbCompWith samp (k i) (j.2.1.branch i ρ) := rfl

lemma toProbCompWith_query_bind (t : (unifSpec + spec').Domain)
    (k : (unifSpec + spec').Range t → QOC W (unifSpec + spec') α) (ρ : Matrix W W ℂ) :
    toProbCompWith samp (liftM ((instrSpec W + (unifSpec + spec')).query (Sum.inr t)) >>= k) ρ =
      liftM ((unifSpec + spec').query t) >>= fun u ↦ toProbCompWith samp (k u) ρ := rfl

/-- `toProbComp` is the strategy of the exact Born sampler. -/
theorem toProbComp_eq_toProbCompWith (Q : QOC W (unifSpec + spec') α) (ρ : Matrix W W ℂ) :
    toProbComp Q ρ = toProbCompWith exactSamp Q ρ := by
  induction Q using OracleComp.inductionOn generalizing ρ with
  | pure a => rfl
  | query_bind t k ih =>
    rcases t with j | t
    · rw [toProbComp_instr_bind, toProbCompWith_instr_bind]
      simp only [ih]
      rfl
    · rw [toProbComp_query_bind, toProbCompWith_query_bind]
      simp only [ih]

/-- Classical pre-processing commutes with classicalisation. -/
lemma toProbCompWith_liftQ_bind (ob : OracleComp (unifSpec + spec') γ)
    (F : γ → QOC W (unifSpec + spec') α) (ρ : Matrix W W ℂ) :
    toProbCompWith samp (liftQ ob >>= F) ρ = ob >>= fun x ↦ toProbCompWith samp (F x) ρ := by
  induction ob using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    rw [liftQ_query_bind, bind_assoc, toProbCompWith_query_bind, bind_assoc]
    simp only [ih]

@[simp] lemma toProbCompWith_liftQ (ob : OracleComp (unifSpec + spec') α) (ρ : Matrix W W ℂ) :
    toProbCompWith samp (liftQ ob : QOC W (unifSpec + spec') α) ρ = ob := by
  simpa using toProbCompWith_liftQ_bind samp ob (pure : α → QOC W (unifSpec + spec') α) ρ

/-- Classical post-processing commutes with classicalisation. -/
lemma toProbCompWith_bind_liftQ (Q : QOC W (unifSpec + spec') α)
    (post : α → OracleComp (unifSpec + spec') β) (ρ : Matrix W W ℂ) :
    toProbCompWith samp (Q >>= fun a ↦ liftQ (post a)) ρ = toProbCompWith samp Q ρ >>= post := by
  induction Q using OracleComp.inductionOn generalizing ρ with
  | pure a => simp
  | query_bind t k ih =>
    rcases t with j | t
    · rw [bind_assoc, toProbCompWith_instr_bind, toProbCompWith_instr_bind, bind_assoc]
      simp only [ih]
    · rw [bind_assoc, toProbCompWith_query_bind, toProbCompWith_query_bind, bind_assoc]
      simp only [ih]

/-- **Wrapping commutes with classicalisation, for every sampler.** -/
theorem toProbCompWith_wrap
    (implB : QueryImpl (unifSpec + spec) (StateT τ (OracleComp (unifSpec + spec'))))
    (hB : ForwardsUnifB implB) (Q : QOC W (unifSpec + spec) α) (t : τ) (ρ : Matrix W W ℂ) :
    toProbCompWith samp (wrap implB Q t) ρ =
      (simulateQ implB (toProbCompWith samp Q ρ)).run t := by
  induction Q using OracleComp.inductionOn generalizing t ρ with
  | pure a => simp
  | query_bind q k ih =>
    rcases q with j | q
    · rw [wrap_instr_bind, toProbCompWith_instr_bind, toProbCompWith_instr_bind,
        hB.run_simulateQ_liftL_bind]
      simp only [ih]
    · rw [wrap_query_bind, toProbCompWith_liftQ_bind, toProbCompWith_query_bind, simulateQ_bind,
        StateT.run_bind, simulateQ_spec_query]
      simp only [ih]

/-- **The reduction commutes with classicalisation, for every sampler.** -/
theorem toProbCompWith_qReduction (pre : OracleComp (unifSpec + spec') γ)
    (implB : γ → QueryImpl (unifSpec + spec) (StateT τ (OracleComp (unifSpec + spec'))))
    (hB : ∀ a, ForwardsUnifB (implB a)) (t₀ : γ → τ)
    (post : γ → α × τ → OracleComp (unifSpec + spec') β)
    (Q : γ → QOC W (unifSpec + spec) α) (ρ : Matrix W W ℂ) :
    toProbCompWith samp (qReduction pre implB t₀ post Q) ρ =
      cReduction pre implB t₀ post fun a ↦ toProbCompWith samp (Q a) ρ := by
  unfold qReduction cReduction
  rw [toProbCompWith_liftQ_bind]
  refine bind_congr fun a ↦ ?_
  rw [toProbCompWith_bind_liftQ, toProbCompWith_wrap _ _ (hB a)]

/-- **Stateless wrappers commute with classicalisation, for every sampler.** -/
theorem toProbCompWith_wrap0 (h : QueryImpl (unifSpec + spec) (OracleComp (unifSpec + spec')))
    (hh : ForwardsUnif0 h) (Q : QOC W (unifSpec + spec) α) (ρ : Matrix W W ℂ) :
    toProbCompWith samp (wrap0 h Q) ρ = simulateQ h (toProbCompWith samp Q ρ) := by
  induction Q using OracleComp.inductionOn generalizing ρ with
  | pure a => simp
  | query_bind q k ih =>
    rcases q with j | q
    · rw [wrap0_instr_bind, toProbCompWith_instr_bind, toProbCompWith_instr_bind,
        hh.simulateQ_liftL_bind]
      simp only [ih]
    · rw [wrap0_query_bind, toProbCompWith_liftQ_bind, toProbCompWith_query_bind, simulateQ_bind,
        simulateQ_spec_query]
      simp only [ih]

/-- Classicalisation commutes with relabelling the output. -/
theorem toProbCompWith_map (f : α → β) (Q : QOC W (unifSpec + spec') α) (ρ : Matrix W W ℂ) :
    toProbCompWith samp (f <$> Q) ρ = f <$> toProbCompWith samp Q ρ := by
  have e : f <$> Q = Q >>= fun a ↦ liftQ (pure (f a) : OracleComp (unifSpec + spec') β) := by
    simp only [liftQ_pure]; exact map_eq_pure_bind f Q
  rw [e, toProbCompWith_bind_liftQ]
  exact (map_eq_pure_bind f _).symm

/-- The harness around the quantum forger classicalises to the harness around its classical
strategy, for every sampler. -/
theorem toProbCompWith_qRunForger {Msg Sig : Type} (Q : QOC W (unifSpec + (Msg →ₒ Sig)) α)
    (sign : Msg → OracleComp (unifSpec + spec') Sig) (ρ : Matrix W W ℂ) :
    toProbCompWith samp (qRunForger Q sign) ρ = runForgerG (toProbCompWith samp Q ρ) sign :=
  toProbCompWith_wrap samp _ (forwardsUnifB_harnessImpl sign) Q [] ρ

/-! ## Closed machines -/

/-- The classical strategy of a closed machine started in the state `ρ`, for the sampler
`samp`. -/
noncomputable def toProbCompCWith (samp : Sampler W) (X : Closed W α) :
    Matrix W W ℂ → ProbComp α :=
  OracleComp.construct (C := fun _ ↦ Matrix W W ℂ → ProbComp α)
    (fun a _ ↦ pure a)
    (fun t _ ih ρ ↦
      match t, ih with
      | .inl j, ih => samp j ρ >>= fun i ↦ ih i (j.2.1.branch i ρ)
      | .inr n, ih => liftM (unifSpec.query n) >>= fun u ↦ ih u ρ) X

@[simp] lemma toProbCompCWith_pure (a : α) (ρ : Matrix W W ℂ) :
    toProbCompCWith samp (pure a : Closed W α) ρ = pure a := rfl

lemma toProbCompCWith_instr_bind (j : InstrIdx W) (k : Fin (j.1 + 1) → Closed W α)
    (ρ : Matrix W W ℂ) :
    toProbCompCWith samp (liftM ((instrSpec W + unifSpec).query (Sum.inl j)) >>= k) ρ =
      samp j ρ >>= fun i ↦ toProbCompCWith samp (k i) (j.2.1.branch i ρ) := rfl

lemma toProbCompCWith_unif_bind (n : ℕ) (k : Fin (n + 1) → Closed W α) (ρ : Matrix W W ℂ) :
    toProbCompCWith samp (liftM ((instrSpec W + unifSpec).query (Sum.inr n)) >>= k) ρ =
      liftM (unifSpec.query n) >>= fun u ↦ toProbCompCWith samp (k u) ρ := rfl

/-- `toProbCompC` is the closed strategy of the exact Born sampler. -/
theorem toProbCompC_eq_toProbCompCWith (X : Closed W α) (ρ : Matrix W W ℂ) :
    toProbCompC X ρ = toProbCompCWith exactSamp X ρ := by
  induction X using OracleComp.inductionOn generalizing ρ with
  | pure a => rfl
  | query_bind t k ih =>
    rcases t with j | n
    · rw [toProbCompC_instr_bind, toProbCompCWith_instr_bind]
      simp only [ih]
      rfl
    · rw [toProbCompC_unif_bind, toProbCompCWith_unif_bind]
      simp only [ih]

/-- Classical pre-processing commutes with classicalisation. -/
lemma toProbCompCWith_liftU_bind (oa : ProbComp γ) (F : γ → Closed W α) (ρ : Matrix W W ℂ) :
    toProbCompCWith samp (liftU oa >>= F) ρ = oa >>= fun x ↦ toProbCompCWith samp (F x) ρ := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp
  | query_bind n k ih =>
    rw [liftU_query_bind, bind_assoc, toProbCompCWith_unif_bind, bind_assoc]
    simp only [ih]

@[simp] lemma toProbCompCWith_liftU (oa : ProbComp α) (ρ : Matrix W W ℂ) :
    toProbCompCWith samp (liftU oa : Closed W α) ρ = oa := by
  simpa using toProbCompCWith_liftU_bind samp oa (pure : α → Closed W α) ρ

/-- Classical post-processing commutes with classicalisation. -/
lemma toProbCompCWith_bind_liftU (X : Closed W α) (post : α → ProbComp β) (ρ : Matrix W W ℂ) :
    toProbCompCWith samp (X >>= fun a ↦ liftU (post a)) ρ = toProbCompCWith samp X ρ >>= post := by
  induction X using OracleComp.inductionOn generalizing ρ with
  | pure a => simp
  | query_bind t k ih =>
    rcases t with j | n
    · rw [bind_assoc, toProbCompCWith_instr_bind, toProbCompCWith_instr_bind, bind_assoc]
      simp only [ih]
    · rw [bind_assoc, toProbCompCWith_unif_bind, toProbCompCWith_unif_bind, bind_assoc]
      simp only [ih]

/-- **Closing commutes with classicalisation, for every sampler.** -/
theorem toProbCompCWith_close (impl : QueryImpl (unifSpec + spec') (StateT σ ProbComp))
    (himpl : ForwardsUnif impl) (Q : QOC W (unifSpec + spec') α) (s : σ) (ρ : Matrix W W ℂ) :
    toProbCompCWith samp (close impl Q s) ρ =
      (simulateQ impl (toProbCompWith samp Q ρ)).run s := by
  induction Q using OracleComp.inductionOn generalizing s ρ with
  | pure a => simp
  | query_bind t k ih =>
    rcases t with j | t
    · rw [close_instr_bind, toProbCompCWith_instr_bind, toProbCompWith_instr_bind,
        himpl.run_simulateQ_liftL_bind]
      simp only [ih]
    · rw [close_query_bind, toProbCompCWith_liftU_bind, toProbCompWith_query_bind, simulateQ_bind,
        StateT.run_bind, simulateQ_spec_query]
      simp only [ih]

end PQ.Interactive

open PQ.Interactive in
#print axioms toProbComp_eq_toProbCompWith
open PQ.Interactive in
#print axioms toProbCompWith_wrap
open PQ.Interactive in
#print axioms toProbCompWith_wrap0
open PQ.Interactive in
#print axioms toProbCompCWith_close
