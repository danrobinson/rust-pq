import Integration.SlhDsaShakePermutationManifest

/-! Exact finite counting for a predetermined prefix tree. Every non-root
node fixes one edge of the permutation. Assigning distinct nonzero capacity
labels on the tree makes those inputs and outputs injective. -/
namespace Reduction.ShakePermutation.Manifest
open Classical Fix
set_option maxRecDepth 16000
noncomputable section

structure Tree (I : Type) where
  paths : I → List Rate
  parent : I → Option I
  block : I → Rate
  step : ∀ i, paths i = ((parent i).elim [] paths) ++ [block i]
  siblings : Function.Injective (fun i => (parent i, block i))

variable {I : Type}
abbrev Caps (I : Type) := I ↪ {z : Capacity // z ≠ 0}
def branch (c : Caps I) : Option I → Capacity
  | none => 0
  | some i => (c i).val

theorem branch_injective (c : Caps I) : Function.Injective (branch c) := by
  rintro (_ | i) (_ | j) h
  · rfl
  · exact False.elim ((c j).property h.symm)
  · exact False.elim ((c i).property h)
  · exact congrArg some (c.injective (Subtype.ext h))

def inputs (t : Tree I) (c : Caps I) : I ↪ Words :=
  ⟨fun i => join (t.block i) (branch c (t.parent i)),by
    intro i j e
    apply t.siblings
    exact Prod.ext (branch_injective c (by simpa only [cap_join] using congrArg capOf e))
      (by simpa only [rate_join] using congrArg rateOf e)⟩

def outputs (c : Caps I) (r : I → Rate) : I ↪ Words :=
  ⟨fun i => join (r i) (c i).val,by
    intro i j e
    exact c.injective (Subtype.ext (by simpa only [cap_join] using congrArg capOf e))⟩

theorem states (t : Tree I) (c : Caps I) (r : I → Rate) (π : Permutation)
    (e : imageTuple (inputs t c) π = outputs c r) (i : I) :
    overwrite π (t.paths i) = outputs c r i := by
  have sub (n : ℕ) (i : I) (hn : (t.paths i).length = n) :
      overwrite π (t.paths i) = outputs c r i := by
    induction n using Nat.strong_induction_on generalizing i with
    | ind n ih =>
      rw [t.step i] at hn ⊢
      simp only [overwrite,List.foldl_append,List.foldl_cons,List.foldl_nil]
      change π (join (t.block i) (capOf (overwrite π ((t.parent i).elim [] t.paths)))) = _
      have h := DFunLike.congr_fun e i
      change π (join (t.block i) (branch c (t.parent i))) = outputs c r i at h
      cases hp : t.parent i with
      | none => rw [hp] at h; exact h
      | some j =>
        simp only [hp,Option.elim_some,List.length_append,List.length_singleton] at hn
        rw [Option.elim_some,ih (t.paths j).length (by omega) j rfl]
        change π (join (t.block i) (capOf (join (r j) (c j).val))) = _
        rw [cap_join]
        rw [hp] at h
        exact h
  exact sub _ i rfl

def good (t : Tree I) (π : Permutation) :=
  Function.Injective (fun i => capOf (overwrite π (t.paths i))) ∧
  ∀ i, capOf (overwrite π (t.paths i)) ≠ 0

/-- Lower bound on the number of permutations with collision-free
prefix states. The index type counts all non-root prefixes once. -/
theorem good_count [Fintype I] (t : Tree I) :
    Nat.card (Caps I × (I → Rate)) * Nat.card Permutation ≤
      Nat.card (I ↪ Words) * Nat.card {π : Permutation // good t π} := by
  classical
  simp only [Nat.card_eq_fintype_card]
  let W := Caps I × (I → Rate)
  let B (w : W) := {π : Permutation // imageTuple (inputs t w.1) π = outputs w.1 w.2}
  have st (z : Σ w : W, B w) := states t z.1.1 z.1.2 z.2.val z.2.property
  have cap (z : Σ w : W, B w) (i : I) : capOf (overwrite z.2.val (t.paths i)) = (z.1.1 i).val := by
    rw [st z i]; apply cap_join
  have rate (z : Σ w : W, B w) (i : I) : rateOf (overwrite z.2.val (t.paths i)) = z.1.2 i := by
    rw [st z i]; apply rate_join
  let f (z : Σ w : W, B w) : {π : Permutation // good t π} := ⟨z.2.val,by
    constructor
    · intro i j e
      exact z.1.1.injective (Subtype.ext ((cap z i).symm.trans (e.trans (cap z j))))
    · intro i; rw [cap z i]; exact (z.1.1 i).property⟩
  have inj : Function.Injective f := by
    rintro ⟨w,p⟩ ⟨v,q⟩ e
    have h : p.val = q.val := congrArg Subtype.val e
    have he : w = v := by
      apply Prod.ext
      · apply DFunLike.ext
        intro i
        apply Subtype.ext
        exact (cap ⟨w,p⟩ i).symm.trans (by simpa only [h] using cap ⟨v,q⟩ i)
      · funext i
        exact (rate ⟨w,p⟩ i).symm.trans (by simpa only [h] using rate ⟨v,q⟩ i)
    subst v
    exact congrArg (Sigma.mk w) (Subtype.ext h)
  have h := Nat.mul_le_mul_left (Fintype.card (I ↪ Words)) (Fintype.card_le_of_injective _ inj)
  rw [Fintype.card_sigma,Finset.mul_sum] at h
  have hf (w : W) : Fintype.card (I ↪ Words) * Fintype.card (B w) = Fintype.card Permutation := by
    rw [← Nat.card_eq_fintype_card,← Nat.card_eq_fintype_card,← Nat.card_eq_fintype_card]
    exact nat_embedding_fiber (inputs t w.1) (outputs w.1 w.2)
  simpa only [hf,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.cast_id,W] using h

end
end Reduction.ShakePermutation.Manifest
#print axioms Reduction.ShakePermutation.Manifest.good_count
