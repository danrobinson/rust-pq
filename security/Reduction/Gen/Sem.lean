import Reduction.Gen.Run
import Reduction.Tables
import VCVio.EvalDist.FiniteSupport

/-!
# Semantics over the general sampling interface and the bridge to `IsLin`

`prG ds g = 𝒟[g] {true}` for `g : OracleComp (ds + unifSpec) Bool` (VCVio's measure semantics for
a spec with an `AnswerMeasure`).  Facts:

* `prG_liftR` — classical code keeps its law over the general interface;
* `val_modelOf` — the probability that a classical context (stateful handler `impl`, final test
  `post`) around a general-spec program outputs `true` is a `Model.val`;
* `isLin_run`, `isLin_liftR_bind` — hence every "classical prefix; one run of the forger against a
  classical handler; classical suffix" experiment is an `IsLin` functional of the forger;
* `derandG` — `IsLin.derand` for the answer-measure weights.
-/

open OracleComp OracleSpec ENNReal MeasureTheory

namespace Reduction.Gen

set_option linter.unusedSectionVars false

variable {κ : Type} (ds : OracleSpec κ) [OracleSpec.AnswerMeasure ds] [∀ d, Fintype (ds.Range d)]
variable {ιx : Type} {X : OracleSpec ιx} {σ α β PK : Type}

instance instFintypeGSpecRange (t : (gSpec ds).Domain) : Fintype ((gSpec ds).Range t) :=
  match t with
  | .inl d => inferInstanceAs (Fintype (ds.Range d))
  | .inr n => inferInstanceAs (Fintype (Fin (n + 1)))

/-- Probability that a Boolean program over the general sampling interface outputs `true`. -/
noncomputable def prG (g : OracleComp (gSpec ds) Bool) : ℝ≥0∞ := 𝒟[g] {true}

/-- The weights of the `ds`-answers. -/
noncomputable def wOf (d : ds.Domain) (u : ds.Range d) : ℝ≥0∞ :=
  OracleSpec.AnswerMeasure.toMeasure d {u}

lemma wOf_sum (d : ds.Domain) : ∑ u, wOf ds d u = 1 := by
  let _ : MeasurableSpace (ds.Range d) := ⊤
  unfold wOf
  rw [sum_measure_singleton]
  simp

/-! ## Probability rules -/

/-- An event after a bind is the weighted sum, over the prefix's outputs, of the continuation's
event (specs with finite answer types). -/
theorem prEvent_bind_tsum {κ' : Type} {cs : OracleSpec κ'} [OracleSpec.AnswerMeasure cs]
    [∀ t, Finite (cs.Range t)] {γ : Type} (oa : OracleComp cs γ) (g : γ → OracleComp cs β)
    (p : β → Prop) :
    Pr{let y ← oa >>= g}[p y] = ∑' x, Pr{let z ← oa}[z = x] * Pr{let y ← g x}[p y] := by
  let _ : MeasurableSpace γ := ⊤
  rw [prEvent_bind_eq_lintegral_of_discrete,
    lintegral_evalDist_eq_tsum_of_support_finite oa (OracleComp.support_finite oa)]

/-- The singleton masses sum to at most one. -/
theorem tsum_prEvent_le_one' {κ' : Type} {cs : OracleSpec κ'} [OracleSpec.AnswerMeasure cs]
    [∀ t, Finite (cs.Range t)] {γ : Type} (oa : OracleComp cs γ) :
    ∑' x, Pr{let y ← oa}[y = x] ≤ 1 := by
  let _ : MeasurableSpace γ := ⊤
  have h := lintegral_evalDist_eq_tsum_of_support_finite oa (OracleComp.support_finite oa)
    fun _ ↦ 1
  simp only [mul_one, lintegral_const, one_mul] at h
  rw [← h]
  exact prob_le_one

/-- Probability of an event after one query of a spec with finite answer types. -/
lemma prEvent_query_bind {κ' : Type} {cs : OracleSpec κ'} [OracleSpec.AnswerMeasure cs]
    (t : cs.Domain) [Fintype (cs.Range t)] (k : cs.Range t → OracleComp cs β) (q : β → Prop) :
    Pr{let y ← liftM (cs.query t) >>= k}[q y] =
      ∑ u, OracleSpec.AnswerMeasure.toMeasure t {u} * Pr{let y ← k u}[q y] := by
  let _ : MeasurableSpace (cs.Range t) := ⊤
  rw [prEvent_bind_eq_lintegral_of_discrete, lintegral_fintype]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [mul_comm, evalDist_liftM_query_apply (spec := cs) t (MeasurableSet.of_discrete)]

/-- Classical code keeps its law over the general sampling interface. -/
theorem prEvent_liftR (oa : ProbComp β) (q : β → Prop) :
    Pr{let y ← liftR ds oa}[q y] = Pr{let y ← oa}[q y] := by
  induction oa using OracleComp.inductionOn with
  | pure a => classical rw [liftR_pure, prEvent_pure, prEvent_pure]
  | query_bind n k ih =>
    rw [liftR_bind, liftR_query, prEvent_query_bind (cs := gSpec ds) (Sum.inr n),
      prEvent_query_bind (cs := unifSpec) n]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [ih]
    rfl

lemma prG_eq (g : OracleComp (gSpec ds) Bool) : prG ds g = Pr{let y ← g}[y = true] :=
  (prEvent_eq_evalDist_singleton g true).symm

lemma prTrue_eq (g : ProbComp Bool) : prTrue g = Pr{let y ← g}[y = true] :=
  (prEvent_eq_evalDist_singleton g true).symm

/-- Classical Boolean code keeps its success probability. -/
theorem prG_liftR (g : ProbComp Bool) : prG ds (liftR ds g) = prTrue g := by
  rw [prG_eq, prTrue_eq, prEvent_liftR]

theorem prG_le_one (g : OracleComp (gSpec ds) Bool) : prG ds g ≤ 1 := prob_le_one

/-- `prG` of a bind with a classical prefix. -/
theorem prG_liftR_bind (p : ProbComp β) (f : β → OracleComp (gSpec ds) Bool) :
    prG ds (liftR ds p >>= f) = ∑' x, Pr{let y ← p}[y = x] * prG ds (f x) := by
  rw [prG_eq, prEvent_bind_tsum]
  refine tsum_congr fun x ↦ ?_
  rw [prEvent_liftR, prG_eq]

/-! ## The model of a classical context -/

/-- The model of a classical stateful handler `impl` and final Boolean test `post`. -/
noncomputable def modelOf (impl : QueryImpl (unifSpec + X) (StateT σ ProbComp))
    (post : α × σ → ProbComp Bool) : Model unifSpec X α where
  σ := σ
  step t s x := Pr{let y ← (impl t).run s}[y = x]
  fin a s := prTrue (post (a, s))
  step_le _ _ := tsum_prEvent_le_one' _
  fin_le _ _ := prob_le_one

lemma runG_ds_bind (impl : QueryImpl (unifSpec + X) (StateT σ ProbComp)) (d : ds.Domain)
    (k : ds.Range d → OracleComp ((ds + unifSpec) + X) α) (s : σ) :
    runG ds impl (liftM (((ds + unifSpec) + X).query (Sum.inl (Sum.inl d))) >>= k) s =
      liftM ((gSpec ds).query (Sum.inl d)) >>= fun u ↦ runG ds impl (k u) s := by
  unfold runG
  rw [simulateQ_bind, StateT.run_bind, simulateQ_spec_query]
  exact bind_map_left (m := OracleComp (gSpec ds)) (fun u ↦ (u, s))
    (liftM ((gSpec ds).query (Sum.inl d))) _

lemma runG_us_bind (impl : QueryImpl (unifSpec + X) (StateT σ ProbComp)) (n : ℕ)
    (k : Fin (n + 1) → OracleComp ((ds + unifSpec) + X) α) (s : σ) :
    runG ds impl (liftM (((ds + unifSpec) + X).query (Sum.inl (Sum.inr n))) >>= k) s =
      liftR ds ((impl (Sum.inl n)).run s) >>= fun p ↦ runG ds impl (k p.1) p.2 := by
  unfold runG
  rw [simulateQ_bind, StateT.run_bind, simulateQ_spec_query]
  rfl

lemma runG_X_bind (impl : QueryImpl (unifSpec + X) (StateT σ ProbComp)) (x : X.Domain)
    (k : X.Range x → OracleComp ((ds + unifSpec) + X) α) (s : σ) :
    runG ds impl (liftM (((ds + unifSpec) + X).query (Sum.inr x)) >>= k) s =
      liftR ds ((impl (Sum.inr x)).run s) >>= fun p ↦ runG ds impl (k p.1) p.2 := by
  unfold runG
  rw [simulateQ_bind, StateT.run_bind, simulateQ_spec_query]
  rfl

/-- **Bridge.** The success probability of a classical context around a general-spec program is
the value of the program in the model of the context. -/
theorem val_modelOf (impl : QueryImpl (unifSpec + X) (StateT σ ProbComp))
    (post : α × σ → ProbComp Bool) (oa : OracleComp ((ds + unifSpec) + X) α) (s : σ) :
    (modelOf impl post).val ds (wOf ds) oa s =
      prG ds (runG ds impl oa s >>= fun r ↦ liftR ds (post r)) := by
  induction oa using ind3 generalizing s with
  | pure a =>
    change prTrue (post (a, s)) = _
    rw [runG_pure, pure_bind, prG_liftR]
  | hds d k ih =>
    change ∑ u, wOf ds d u * (modelOf impl post).val ds (wOf ds) (k u) s = _
    rw [runG_ds_bind, bind_assoc, prG_eq,
      prEvent_query_bind (cs := gSpec ds) (Sum.inl d)]
    refine Finset.sum_congr rfl fun u _ ↦ ?_
    rw [ih, prG_eq]
    rfl
  | hus n k ih =>
    change ∑' x : Fin (n + 1) × σ, (modelOf impl post).step (.inl n) s x *
      (modelOf impl post).val ds (wOf ds) (k x.1) x.2 = _
    rw [runG_us_bind, bind_assoc, prG_liftR_bind]
    exact tsum_congr fun x ↦ by rw [ih]; rfl
  | hX x k ih =>
    change ∑' y : X.Range x × σ, (modelOf impl post).step (.inr x) s y *
      (modelOf impl post).val ds (wOf ds) (k y.1) y.2 = _
    rw [runG_X_bind, bind_assoc, prG_liftR_bind]
    exact tsum_congr fun y ↦ by rw [ih]; rfl

/-! ## `IsLin` for experiments -/

/-- One run of the forger against a classical handler, followed by a classical test. -/
theorem isLin_run (impl : QueryImpl (unifSpec + X) (StateT σ ProbComp)) (pk : PK) (s : σ)
    (post : α × σ → ProbComp Bool) :
    IsLin ds (wOf ds) 1 (fun F : PK → OracleComp ((ds + unifSpec) + X) α ↦
      prG ds (runG ds impl (F pk) s >>= fun r ↦ liftR ds (post r))) :=
  ⟨modelOf impl post, Unit, fun _ ↦ 1, fun _ ↦ pk, fun _ ↦ s, by simp, fun F ↦ by
    rw [tsum_fintype]; simp [val_modelOf]⟩

/-- The same with a pure final test. -/
theorem isLin_run_pure (impl : QueryImpl (unifSpec + X) (StateT σ ProbComp)) (pk : PK) (s : σ)
    (f : α × σ → Bool) :
    IsLin ds (wOf ds) 1 (fun F : PK → OracleComp ((ds + unifSpec) + X) α ↦
      prG ds (runG ds impl (F pk) s >>= fun r ↦ pure (f r))) := by
  have h := isLin_run ds impl pk s (fun r ↦ (pure (f r) : ProbComp Bool))
  simpa using h

/-- A classical prefix. -/
theorem isLin_liftR_bind {Y : Type} (p : ProbComp Y)
    (K : Y → (PK → OracleComp ((ds + unifSpec) + X) α) → OracleComp (gSpec ds) Bool)
    (h : ∀ y, IsLin ds (wOf ds) 1 (fun F ↦ prG ds (K y F))) :
    IsLin ds (wOf ds) 1 (fun F ↦ prG ds (liftR ds p >>= fun y ↦ K y F)) := by
  have h1 := IsLin.tsum ds (fun y ↦ Pr{let z ← p}[z = y]) (fun y F ↦ prG ds (K y F)) h
  have h2 : IsLin ds (wOf ds) ((∑' y, Pr{let z ← p}[z = y]) * 1)
      (fun F ↦ prG ds (liftR ds p >>= fun y ↦ K y F)) := by
    simpa only [prG_liftR_bind] using h1
  exact IsLin.mono ds h2 (by rw [mul_one]; exact tsum_prEvent_le_one' p)

/-- **Derandomisation of the `ds`-coins.** A linear inequality between `IsLin` functionals that
holds for all `ds`-free forger families holds for all families over `(ds + unifSpec) + X`. -/
theorem derandG {N P : (PK → OracleComp ((ds + unifSpec) + X) α) → ℝ≥0∞} {bN bP : ℝ≥0∞}
    (hbN : bN ≠ ⊤) (hbP : bP ≠ ⊤) (hN : IsLin ds (wOf ds) bN N) (hP : IsLin ds (wOf ds) bP P)
    (h : ∀ F₀ : PK → OracleComp (unifSpec + X) α,
      N (fun pk ↦ embed ds (F₀ pk)) ≤ P (fun pk ↦ embed ds (F₀ pk))) :
    ∀ F, N F ≤ P F :=
  IsLin.derand ds (wOf_sum ds) hbN hbP hN hP h

end Reduction.Gen

section Axioms
open Reduction.Gen
#print axioms prG_liftR
#print axioms val_modelOf
#print axioms isLin_run
#print axioms isLin_liftR_bind
#print axioms derandG
end Axioms
