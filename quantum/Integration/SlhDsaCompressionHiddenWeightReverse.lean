import Integration.SlhDsaCompressionHiddenWeight

namespace Reduction.Compression.HiddenWeight
open Ideal Ideal.HP OracleComp OracleSpec PQ.Interactive ENNReal

private theorem mean_const_one {α : Type} (p : ProbComp α) : mean p (fun _ => 1) = 1 := by
  have h := flag p (fun _ => true)
  simp only [ite_true] at h
  rw [← h]
  apply prT_eq_one_of_support
  intro b hb
  rw [mem_support_bind_iff] at hb
  obtain ⟨_,_,hp⟩ := hb
  exact hp

private theorem complement {α : Type} (p : ProbComp α) (w : α → ℝ≥0∞) (hw : ∀ x, w x ≤ 1) :
    mean p w + mean p (fun x => 1 - w x) = 1 := by
  rw [← mean_add]
  simpa only [add_tsub_cancel_of_le (hw _)] using mean_const_one p

variable {St Blk PkSeed σ : Type} [DecidableEq St] [DecidableEq Blk]
variable (IV : St) (sb : PkSeed → Blk)
variable (P : OracleComp (unifSpec + (hS St Blk + chainS St Blk)) σ)
variable [Fintype St] [SampleableType St] [Fintype Blk] [SampleableType (CF St Blk)]

/-- The same transcript coupling bounds the opposite direction, including
when the measured continuation depends on the entire compression table. -/
theorem hiddenPrefix_reverse (seeds : ProbComp PkSeed) (hsb : Function.Injective sb)
    (γ : ℝ≥0∞) (hγ : ∀ s, Pr{let s' ← seeds}[s' = s] ≤ γ)
    (q C L : ℕ) (hq : IsQueryBoundP P (fun i => isPub i = true) q)
    (hC : IsQueryBoundP P (fun i => isChain i = true) C) (hL : AllQueriesSatisfy P (chainLenLe L))
    (w : PkSeed → CF St Blk → σ → ℝ≥0∞) (hw : ∀ s g x, w s g x ≤ 1) :
    mean seeds (fun s => mean ($ᵗ St) fun cv => mean ($ᵗ (CF St Blk)) fun g => mean ($ᵗ (Blk → St)) fun T =>
      mean (simulateQ (ans₁ g (chainI g T)) P) (w s (gstar IV (sb s) cv g T))) ≤
    mean seeds (fun s => mean ($ᵗ (CF St Blk)) fun g =>
      mean (simulateQ (ans₁ g (keyedChain IV sb g s)) P) (w s g)) +
        (q*γ + (2*q+C*(1+2*L)+1:ℕ)*(Fintype.card St:ℝ≥0∞)⁻¹) := by
  let actual : ProbComp (PkSeed × CF St Blk × σ) := do
    let s ← seeds
    let g ← $ᵗ (CF St Blk)
    let x ← simulateQ (ans₁ g (keyedChain IV sb g s)) P
    pure (s,g,x)
  let ideal : ProbComp (PkSeed × CF St Blk × σ) := do
    let s ← seeds
    let cv ← $ᵗ St
    let g ← $ᵗ (CF St Blk)
    let T ← $ᵗ (Blk → St)
    let x ← simulateQ (ans₁ g (chainI g T)) P
    pure (s,gstar IV (sb s) cv g T,x)
  let f := fun z : PkSeed × CF St Blk × σ => w z.1 z.2.1 z.2.2
  let e := q*γ + (2*q+C*(1+2*L)+1:ℕ)*(Fintype.card St:ℝ≥0∞)⁻¹
  have hc : mean actual (fun x => 1 - f x) ≤ mean ideal (fun x => 1 - f x) + e := by
    simpa only [actual,ideal,f,e,mean_bind,mean_pure] using
      hiddenPrefix IV sb P seeds hsb γ hγ q C L hq hC hL (fun s g x => 1 - w s g x) (fun _ _ _ => tsub_le_self)
  have fc : ∀ z, f z ≤ 1 := fun z => hw _ _ _
  have finite : mean ideal (fun x => 1 - f x) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (mean_one _ (fun _ => tsub_le_self))
  have h : mean ideal f ≤ mean actual f + e := by
    apply (ENNReal.add_le_add_iff_right finite).mp
    calc mean ideal f + mean ideal (fun x => 1 - f x) = 1 := complement ideal f fc
         _ = mean actual f + mean actual (fun x => 1 - f x) := (complement actual f fc).symm
         _ ≤ mean actual f + (mean ideal (fun x => 1 - f x) + e) := add_le_add_right hc _
         _ = (mean actual f + e) + mean ideal (fun x => 1 - f x) := by ac_rfl
  simpa only [actual,ideal,e,f,mean_bind,mean_pure] using h

end Reduction.Compression.HiddenWeight
#print axioms Reduction.Compression.HiddenWeight.hiddenPrefix_reverse
