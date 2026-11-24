import Integration.SlhDsaShakePermutationRelabel
import VCVio.Quantum.Oracle.Compressed.Action

namespace Reduction.ShakePermutation.Relabel
open Quantum Classical Tails
set_option maxRecDepth 8192
variable (π : Permutation) (k k' : Db) (L : ℕ)
abbrev Address (L : ℕ) := Capacity ⊕ Path L

/-- A reached capacity and its selected path exchange recording cells. -/
noncomputable def route : Address L → Address L × Option Rate
  | .inl z => match chosen π k k' L z with
    | none => (.inl z,none)
    | some (x,h) => (.inr x,some h)
  | .inr x => match mate π k k' x with
    | none => (.inr x,none)
    | some (z,h) => (.inl z,some h)

theorem route_back (i : Address L) :
    route π k k' L (route π k k' L i).1 = (i,(route π k k' L i).2) := by
  cases i with
  | inl z =>
    cases e : chosen π k k' L z with
    | none => simp [route,e]
    | some a => rcases a with ⟨x,h⟩; simp [route,e,(mates π k k').mp e]
  | inr x =>
    cases e : mate π k k' x with
    | none => simp [route,e]
    | some a => rcases a with ⟨z,h⟩; simp [route,e,(mates π k k').mpr e]

noncomputable def dest : Equiv.Perm (Address L) :=
  Function.Involutive.toPerm (fun i => (route π k k' L i).1) fun i => congrArg Prod.fst (route_back π k k' L i)

def cellMap : Option Rate → Equiv.Perm (Option Rate)
  | none => Equiv.refl _
  | some h => Function.Involutive.toPerm (twist h) (twist_twice h)

theorem read_swap (d : Cells L) (i : Address L) : swap π k k' L d i =
    cellMap (route π k k' L i).2 (d (dest π k k' L i)) := by
  cases i with
  | inl z => cases e : chosen π k k' L z <;> simp [swap,dest,route,e,cellMap] <;> rfl
  | inr x => cases e : mate π k k' x <;> simp [swap,dest,route,e,cellMap] <;> rfl

theorem compress_cell (head a b : Option Rate) :
    cellCompress Rate (cellMap head a) (cellMap head b) = cellCompress Rate a b := by
  cases head with
  | none => rfl
  | some h =>
    have inj : Function.Injective (fun v : Rate => rateXor v h) :=
      Function.Involutive.injective (fun v => rateXor_cancel v h)
    change cellCompress Rate (twist h a) (twist h b) = _
    cases a <;> cases b <;> simp only [twist,Option.map_none,Option.map_some,cellCompress_none_none,
      cellCompress_none_some,cellCompress_some_none,cellCompress_some_some,inj.eq_iff]

/-- VCVio's exact local compression matrix on h is carried to local compression
on the simulator's chosen cell, for every basis index and every amplitude. -/
theorem compressAt_swap (d e : Cells L) (i : Address L) :
    compressAt Rate i (swap π k k' L d) (swap π k k' L e) = compressAt Rate (dest π k k' L i) d e := by
  classical
  let f := dest π k k' L
  have outside :
      (∀ j ≠ i, swap π k k' L d j = swap π k k' L e j) ↔ ∀ j ≠ f i, d j = e j := by
    simp only [read_swap,Equiv.apply_eq_iff_eq]
    constructor
    · intro same j hj
      obtain ⟨x,rfl⟩ := f.surjective j
      exact same x fun he => hj (he ▸ rfl)
    · exact fun same j hj => same _ (fun eq => hj (f.injective eq))
  rw [compressAt_apply,compressAt_apply]
  by_cases same : ∀ j ≠ i, swap π k k' L d j = swap π k k' L e j
  · rw [ite_eq_left same,ite_eq_left (outside.mp same),read_swap,read_swap,compress_cell]
  · rw [ite_eq_right same,ite_eq_right (fun h => same (outside.mpr h))]

end Reduction.ShakePermutation.Relabel
#print axioms Reduction.ShakePermutation.Relabel.compressAt_swap
