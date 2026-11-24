import Integration.SlhDsaCompressionHiddenWeight
import Ideal.Games.TcrMultiIdeal

namespace Reduction.Compression.Posterior
open PQ.Interactive PQ.QROM Ideal Ideal.HP OracleComp OracleSpec ENNReal HiddenWeight
open scoped Classical
variable {D : Type} {sp : OracleSpec D} [DecidableEq D]
abbrev Answers {I : Type} (spec : OracleSpec I) := (t : I) → spec.Range t
private def read (ds : List D) (g : (Answers sp)) : OracleComp (unifSpec + sp) (Answers sp) :=
  match ds with
  | [] => pure g
  | d::rest => (liftM ((unifSpec + sp).query (.inr d)) : OracleComp (unifSpec + sp) _) >>=
      fun v => read rest (Function.update g d v)

private def fill (ds : List D) (g f : (Answers sp)) : (Answers sp) :=
  match ds with
  | [] => g
  | d::rest => fill rest (Function.update g d (f d)) f

private theorem reads (ds : List D) (g f : (Answers sp)) :
    simulateQ (ansImpl f) (read ds g) = pure (fill ds g f) := by
  induction ds generalizing g with
  | nil => simp [read,fill]
  | cons d rest ih =>
    rw [read,simulateQ_ansImpl_inr_bind,fill,ih]

private theorem fill_at (ds : List D) (g f : (Answers sp)) (i : D) :
    fill ds g f i = if i ∈ ds then f i else g i := by
  induction ds generalizing g with
  | nil => simp [fill]
  | cons d rest ih =>
    rw [fill,ih]
    by_cases h : i = d
    · subst i; simp
    · simp [List.mem_cons,h,Function.update_of_ne]

variable [Fintype D] [∀ i, SampleableType (sp.Range i)]
/-- Read the entire finite table to identify its joint law with a classical transcript. -/
private noncomputable def allCells : OracleComp (unifSpec + sp) (Answers sp) :=
  read Finset.univ.toList (fun i => Classical.arbitrary (sp.Range i))

private theorem readsAll (g : (Answers sp)) : simulateQ (ansImpl g) (allCells (sp := sp)) = pure g := by
  rw [allCells,reads]
  congr 1
  funext i
  simp [fill_at]

private theorem mean_congr_eval {α : Type} [MeasurableSpace α] [DiscreteMeasurableSpace α]
    (p q : ProbComp α) (e : 𝒟[p] = 𝒟[q])
    (w : α → ℝ≥0∞) : mean p w = mean q w := by
  apply tsum_congr
  intro x
  apply congrArg (· * w x)
  unfold prob
  rw [prEvent_eq_evalDist_of_discrete,prEvent_eq_evalDist_of_discrete,e]

variable [SampleableType (Answers sp)]
private theorem lazy_all (c : sp.QueryCache) (w : (Answers sp) → ℝ≥0∞) :
    mean ((simulateQ sp.romImpl (allCells (sp := sp))).run' c) w =
      mean ($ᵗ (Answers sp)) (fun f => w (completeTable c f)) := by
  classical
  let : MeasurableSpace (Answers sp) := ⊤
  let : DiscreteMeasurableSpace (Answers sp) := ⟨fun _ => trivial⟩
  have e := evalDist_simulateQ_romImpl_run'_eq_completeTable (allCells (sp := sp)) c
  have h := mean_congr_eval _ _ e w
  simpa only [mean_bind,readsAll,mean_pure] using h

variable {α : Type}
/-- After an adaptive classical transcript the untouched table entries can be sampled fresh, even when the continuation reads the completed table. -/
theorem posterior (P : OracleComp (unifSpec + sp) α) (w : (Answers sp) → α → ℝ≥0∞) (c : sp.QueryCache) :
    mean ($ᵗ (Answers sp)) (fun g => mean (simulateQ (ansImpl (completeTable c g)) P) (w (completeTable c g))) =
      mean ((simulateQ sp.romImpl P).run c) (fun z => mean ($ᵗ (Answers sp)) (fun g => w (completeTable z.2 g) z.1)) := by
  classical
  let : MeasurableSpace (α × (Answers sp)) := ⊤
  let : DiscreteMeasurableSpace (α × (Answers sp)) := ⟨fun _ => trivial⟩
  let post := fun x : α => allCells (sp := sp) >>= fun f => pure (x,f)
  have e := evalDist_simulateQ_romImpl_run'_eq_completeTable (P >>= post) c
  have h := mean_congr_eval _ _ e (fun z => w z.2 z.1)
  unfold post at h
  simp only [simulateQ_bind,simulateQ_pure,StateT.run'_eq,StateT.run_bind,map_bind,StateT.run_pure,
    map_pure,mean_bind,mean_pure,readsAll,pure_bind] at h
  rw [← h]
  apply congrArg (mean _)
  funext z
  have hh := lazy_all z.2 (fun f => w f z.1)
  simpa only [StateT.run'_eq,map_eq_bind_pure_comp,Function.comp_def,mean_bind,mean_pure] using hh
end Reduction.Compression.Posterior
#print axioms Reduction.Compression.Posterior.posterior
