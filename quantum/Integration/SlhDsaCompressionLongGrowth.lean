import Integration.SlhDsaCompressionDatabaseGrowth
import Ideal.Games.TcrMultiPhase2

namespace Reduction.Compression.LongClass
set_option linter.unusedSectionVars false
open Ideal Ideal.MP2 Recording.Database TweakableHash OracleComp OracleSpec ENNReal Classical
variable {St Blk K T M Y I : Type}
variable (F : THFam St Blk K T M Y I) (btw : Blk → T) (L : ℕ) (qs : List (T × M)) (cv : St)
abbrev Partial (St Blk : Type) := Cell St Blk → Option St

/-- Overlay the fixed honest transcript on a sparse database of fresh cells. -/
def extend (c d : Partial St Blk) (x : Cell St Blk) : Option St := (c x).or (d x)
theorem base_le (c d : Partial St Blk) : CLe c (extend c d) := by
  intro x v h
  simp [extend,h]

private theorem restrict_good {c mid big : Partial St Blk}
    (hc : Good F btw L qs cv c) (hb : Good F btw L qs cv big)
    (h₁ : CLe c mid) (h₂ : CLe mid big) : Good F btw L qs cv mid := by
  refine ⟨fun x y v hx hy => hb.inj x y v (h₂ x v hx) (h₂ y v hy),?_,?_⟩
  · intro x
    exact ⟨fun hx => (hb.nov x).1 (h₂ _ _ hx),fun hx => (hb.nov x).2 (h₂ _ _ hx)⟩
  · intro t m hm
    obtain ⟨v,hv,_⟩ := hc.tgt t m hm
    obtain ⟨w,hw,uniq⟩ := hb.tgt t m hm
    have hmid := chainVal_mono h₁ hv
    have eq := Option.some.inj (hw.symm.trans (chainVal_mono h₂ hmid))
    subst w
    exact ⟨v,hmid,fun X w len htw ne full => uniq X w len htw ne (chainVal_mono h₂ full)⟩

variable [Fintype St] [Fintype Blk] [DecidableEq St] [DecidableEq Blk] [Nonempty St]
private theorem extend_finite {c : Partial St Blk} {n : ℕ} (hc : CFin c n) (d : Partial St Blk) :
    CFin (extend c d) (n+(occupied d).card) := by
  obtain ⟨l,hl,mem⟩ := hc
  refine ⟨l ++ (occupied d).toList,by simpa using hl,?_⟩
  intro x hx
  apply List.mem_append.mpr
  cases he : c x with
  | some v => exact Or.inl (mem x (by simp [he]))
  | none =>
    right
    simpa only [Finset.mem_toList,occupied,Finset.mem_filter,Finset.mem_univ,true_and,
      extend,he,Option.none_or] using hx

private theorem blank_le (c : Partial St Blk) (x : Cell St Blk) (r : Rest x St) (v : Option St) :
    CLe (extend c (assemble x r none)) (extend c (assemble x r v)) := by
  intro z w hz
  by_cases eq : z = x
  · subst z
    have e : c x = some w := by simpa [extend,assemble_at] using hz
    simp [extend,e]
  · simpa [extend,assemble_other _ _ _ eq] using hz

private theorem same (c : Partial St Blk) (x : Cell St Blk) (r : Rest x St) (v : St) :
    extend c (assemble x r (some v)) = if (c x).isSome then extend c (assemble x r none)
      else Function.update (extend c (assemble x r none)) x (some v) := by
  funext z
  by_cases h : z = x
  · subst z
    cases e : c x <;> simp [extend,e]
  · cases e : c x <;> simp [extend,assemble_other _ _ _ h,Function.update_of_ne h]

/-- The classical single-cell bad-extension estimate is exactly the marked
fraction needed by a coherent recording query. It keeps the 128-bit output
test separate from the cost of colliding with a full chaining state. -/
theorem good_growth [SampleableType St] (c : Partial St Blk) (n q : ℕ) (hc : CFin c n)
    (hg : Good F btw L qs cv c)
    (tw : ∀ t m m', (t,m) ∈ qs → (t,m') ∈ qs → m=m')
    (δ : ℝ≥0∞) (hf : δ ≠ ⊤) (hδ : ∀ y, Pr{let u ← $ᵗ St}[F.out u = y] ≤ δ) :
    Growth (fun d => ¬Good F btw L qs cv (extend c d)) q
      (δ.toReal + (2*(n+(q+1))+3 : ℕ)/ (Fintype.card St : ℝ)) := by
  classical
  constructor
  · intro x r v fail full
    exact fail (restrict_good F btw L qs cv hg full (base_le c _) (blank_le c x r v))
  · intro x r cnt live
    have healthy := not_not.mp live
    by_cases hit : (c x).isSome
    · have z (y : St) : Good F btw L qs cv (extend c (assemble x r (some y))) := by rwa [same,ite_eq_left hit]
      simp only [z,not_true_eq_false,Finset.filter_false,Finset.card_empty,Nat.cast_zero,zero_div]
      positivity
    · have nc : c x = none := by cases e : c x <;> simp_all
      let d := assemble x r none
      have size : (occupied d).card ≤ q+1 := (occupied_assemble_le ..).trans (Nat.succ_le_succ cnt)
      have atx : extend c d x = none := by simp [extend,d,nc]
      have prob := prEvent_not_good_update_le δ hδ tw healthy (CFin.mono (extend_finite hc d) (Nat.add_le_add_left size n)) atx
      simp only [SampleableType.prEvent_uniformSample] at prob
      have e := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hf,by finiteness⟩) prob
      rw [ENNReal.toReal_add hf (by finiteness)] at e
      simpa only [same,ite_eq_right hit,ENNReal.toReal_div,ENNReal.toReal_natCast,
        ENNReal.toReal_mul,ENNReal.toReal_inv,div_eq_mul_inv] using e

end Reduction.Compression.LongClass
#print axioms Reduction.Compression.LongClass.good_growth
