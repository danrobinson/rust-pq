import Integration.SlhDsaShakePermutationMask
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Logic.Equiv.Fintype

/-! Explicit exceptional-permutation probability for the 1088/512 split.
A slice of a permutation fixes both rate coordinates and counts admissible
capacity pairs. The bound holds simultaneously for every pair of rates. -/
namespace Reduction.ShakePermutation
open Classical

private def imageTuple {I A : Type} (x : I ↪ A) (π : Equiv.Perm A) : I ↪ A :=
  x.trans π.toEmbedding

private theorem embedding_fiber {I A : Type} [Fintype I] [Fintype A] (x y : I ↪ A) :
    Fintype.card (I ↪ A) * Fintype.card {π : Equiv.Perm A // imageTuple x π = y} =
      Fintype.card (Equiv.Perm A) := by
  classical
  have h (z : I ↪ A) : Fintype.card {π : Equiv.Perm A // imageTuple x π = z} =
      Fintype.card {π : Equiv.Perm A // imageTuple x π = y} := by
    obtain ⟨σ,hσ⟩ := Equiv.Perm.exists_extending_pair z y z.injective y.injective
    let f : {π : Equiv.Perm A // imageTuple x π = z} ≃
        {π : Equiv.Perm A // imageTuple x π = y} := {
      toFun := fun ⟨π,hπ⟩ => ⟨π.trans σ,by
        ext i
        change σ ((imageTuple x π) i) = y i
        rw [hπ,hσ]⟩
      invFun := fun ⟨π,hπ⟩ => ⟨π.trans σ.symm,by
        ext i
        change σ.symm ((imageTuple x π) i) = z i
        rw [hπ,← hσ,σ.symm_apply_apply]⟩
      left_inv := fun π => by ext i; exact σ.symm_apply_apply _
      right_inv := fun π => by ext i; exact σ.apply_symm_apply _ }
    exact Fintype.card_congr f
  have hcard := Fintype.card_congr (Equiv.sigmaFiberEquiv (imageTuple x))
  simpa only [Fintype.card_sigma,h,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.cast_id] using hcard

def capOf (w : Words) : Capacity := fun i => w ⟨i.val+17,by omega⟩
def join (r : Rate) (c : Capacity) : Words := fun i =>
  if h : i.val < 17 then r ⟨i.val,h⟩ else c ⟨i.val-17,by omega⟩

@[simp] theorem cap_join (r : Rate) (c : Capacity) : capOf (join r c) = c := by
  funext i
  simp [capOf,join]

@[simp] theorem rate_join (r : Rate) (c : Capacity) : rateOf (join r c) = r := by
  funext i
  simp [rateOf,join,i.isLt]

@[simp] theorem join_split (w : Words) : join (rateOf w) (capOf w) = w := by
  funext i
  by_cases hi : i.val < 17
  · simp [join,hi,rateOf]
  · simp [join,hi,capOf,Nat.sub_add_cancel (by omega : 17 ≤ i.val)]

def sliceTuple {k : Nat} (r : Rate) (c : Fin k ↪ Capacity) : Fin k ↪ Words :=
  c.trans ⟨join r,fun x y h => by simpa only [cap_join] using congrArg capOf h⟩

def irregular (π : Permutation) : Prop :=
  ∃ (r s : Rate) (a b : Fin 5 ↪ Capacity), ∀ i, π (join r (a i)) = join s (b i)

private abbrev Witness := Rate × Rate × (Fin 5 ↪ Capacity) × (Fin 5 ↪ Capacity)

private theorem graph_union_bound {I A W : Type} [Fintype I] [Fintype A] [Fintype W]
    (left right : W → I ↪ A) (bad : Equiv.Perm A → Prop)
    (cert : ∀ π, bad π → ∃ w, imageTuple (left w) π = right w) :
    Nat.card (I ↪ A) * Nat.card {π : Equiv.Perm A // bad π} ≤ Nat.card W * Nat.card (Equiv.Perm A) := by
  classical
  simp only [Nat.card_eq_fintype_card]
  let B (w : W) := {π : Equiv.Perm A // imageTuple (left w) π = right w}
  let f (π : {π : Equiv.Perm A // bad π}) : Σ w : W, B w :=
    ⟨(cert π π.property).choose,π.val,(cert π π.property).choose_spec⟩
  have hi : Function.Injective f := by
    intro π ρ he
    exact Subtype.ext (congrArg (fun t : Σ w : W, B w => t.2.val) he)
  have h := Nat.mul_le_mul_left (Fintype.card (I ↪ A)) (Fintype.card_le_of_injective _ hi)
  rw [Fintype.card_sigma,Finset.mul_sum] at h
  have hf (w : W) : Fintype.card (I ↪ A) * Fintype.card (B w) = Fintype.card (Equiv.Perm A) :=
    embedding_fiber (left w) (right w)
  simpa only [hf,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.cast_id] using h

private theorem witness_count :
    Nat.card (Fin 5 ↪ Words) * Nat.card {π : Permutation // irregular π} ≤
      Nat.card Witness * Nat.card Permutation := by
  exact graph_union_bound (fun w : Witness => sliceTuple w.1 w.2.2.1)
    (fun w => sliceTuple w.2.1 w.2.2.2) irregular (by
      rintro π ⟨r,s,a,b,h⟩
      exact ⟨(r,s,a,b),DFunLike.ext _ _ h⟩)

private theorem card_lanes (n : Nat) : Fintype.card (Fin n → UInt64) = (2^64)^n := by
  rw [Fintype.card_fun,Fintype.card_fin,← FinEnum.card_eq_fintypeCard,FinEnum.card_UInt64]

/-- At most one permutation in 2^699 admits a slice of size five.
The result concerns the actual uniform distribution over bijections. -/
theorem irregular_probability :
    2^699 * Nat.card {π : Permutation // irregular π} ≤ Nat.card Permutation := by
  classical
  have hnum : Nat.card Witness * 2^699 ≤ Nat.card (Fin 5 ↪ Words) := by
    simp only [Nat.card_eq_fintype_card,Witness,Fintype.card_prod,Fintype.card_embedding_eq,Fintype.card_fin,
      Rate,Capacity,Words,card_lanes]
    decide +kernel
  have h := (Nat.mul_le_mul_right (Nat.card {π : Permutation // irregular π}) hnum).trans
    witness_count
  rw [Nat.mul_assoc] at h
  have hp : 0 < Nat.card Witness := by
    simp only [Nat.card_eq_fintype_card,Witness,Fintype.card_prod,Fintype.card_embedding_eq,Fintype.card_fin,Rate,Capacity,card_lanes]
    decide +kernel
  exact Nat.le_of_mul_le_mul_left h hp

abbrev slice (π : Permutation) (r s : Rate) := {c : Capacity // rateOf (π (join r c)) = s}

theorem slice_card (π : Permutation) (hπ : ¬irregular π) (r s : Rate) :
    Fintype.card (slice π r s) ≤ 4 := by
  classical
  by_contra! h
  let e : Fin 5 ↪ slice π r s :=
    (Fin.castLEEmb (by omega)).trans (Fintype.equivFin _).symm.toEmbedding
  let a : Fin 5 ↪ Capacity := e.trans (Function.Embedding.subtype _)
  have hrate (i : Fin 5) : rateOf (π (join r (a i))) = s := (e i).property
  have hjoin (i : Fin 5) : join s (capOf (π (join r (a i)))) = π (join r (a i)) := by
    rw [← hrate i,join_split]
  let b : Fin 5 ↪ Capacity := ⟨fun i => capOf (π (join r (a i))),by
    intro i j he
    have he' := congrArg (join s) he
    rw [hjoin,hjoin] at he'
    exact (sliceTuple r a).injective (π.injective he')⟩
  exact hπ ⟨r,s,a,b,fun i => (hjoin i).symm⟩

theorem irregular_symm (π : Permutation) : irregular π.symm ↔ irregular π := by
  constructor
  · rintro ⟨r,s,a,b,h⟩
    exact ⟨s,r,b,a,fun i => (π.symm_apply_eq.mp (h i)).symm⟩
  · rintro ⟨r,s,a,b,h⟩
    exact ⟨s,r,b,a,fun i => π.symm_apply_eq.mpr (h i).symm⟩

end Reduction.ShakePermutation
#print axioms Reduction.ShakePermutation.irregular_probability
