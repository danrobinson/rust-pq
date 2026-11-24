import Integration.SlhDsaShakePermutationInjectionSwap
import Integration.SlhDsaShakePermutationColumnGame

namespace Reduction.ShakePermutation.Program
open Classical Quantum PQ.Interactive PQ.QROM ENNReal
open scoped Kronecker ComplexOrder
noncomputable section
variable {I J A : Type} [Fintype I] [Fintype J] [DecidableEq I]

def slice (f : (I × J) ↪ A) (i : I) : J ↪ A :=
  ⟨fun j => f (i,j),fun _ _ h => congrArg Prod.snd (f.injective h)⟩

def occupants (f : (I × J) ↪ A) (a : A) : Finset I := by
  classical exact Finset.univ.filter fun i => a ∈ Set.range (slice f i)

omit [DecidableEq I] in
theorem occupant_spec (f : (I × J) ↪ A) (a : A) (i : I) :
    i ∈ occupants f a ↔ a ∈ Set.range (slice f i) := by classical simp [occupants]

omit [DecidableEq I] in
theorem occupants_card (f : (I × J) ↪ A) (a : A) : (occupants f a).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro i hi k hk
  obtain ⟨j,hj⟩ := (occupant_spec _ _ _).mp hi
  obtain ⟨l,hl⟩ := (occupant_spec _ _ _).mp hk
  exact congrArg Prod.fst (f.injective (hj.trans hl.symm))

variable [Nonempty I] {E : Type} [Fintype E] [DecidableEq E]
set_option allowUnsafeReducibility true in
attribute [local irreducible] reassign occupants

def keyOwners (π : Permutation) (u t : (I × J) ↪ Words) (p : Port) : Finset I :=
  let a := if p.1 then p.2 else π p.2
  occupants (imageTuple u π) a ∪ occupants t a

omit [Nonempty I] in
theorem keyOwners_card (π : Permutation) (u t : (I × J) ↪ Words) (p : Port) :
    (keyOwners π u t p).card ≤ 2 :=
  (Finset.card_union_le _ _).trans (Nat.add_le_add (occupants_card _ _) (occupants_card _ _))

omit [Nonempty I] in
theorem outside_column (π : Permutation) (u t : (I × J) ↪ Words) (i : I) (p : Port)
    (out : i ∉ keyOwners π u t p) :
    oracle (swapInjections (slice u i) (π,slice t i)).1 p = oracle π p := by
  let key (p : Port) := if p.1 then p.2 else π p.2
  have left (j : J) : imageTuple (slice u i) π j ≠ key p := by
    intro h; exact out (Finset.mem_union_left _ ((occupant_spec _ _ _).mpr ⟨j,h⟩))
  have right (j : J) : slice t i j ≠ key p := by
    intro h; exact out (Finset.mem_union_right _ ((occupant_spec _ _ _).mpr ⟨j,h⟩))
  have fixed := reassign_miss (imageTuple (slice u i) π) (slice t i) (key p)
    (fun ⟨j,h⟩ => left j h) (fun ⟨j,h⟩ => right j h)
  rcases p with ⟨d,v⟩
  cases d with
  | false => exact fixed
  | true =>
    change π.symm ((reassign _ _).symm v) = π.symm v
    exact congrArg π.symm ((Equiv.symm_apply_eq (e:=reassign _ _)).mpr fixed.symm)

/-- A column can be replaced by a second injection even if its image
intersects the old image. Each coherent address has at most two owners.
The public test is common to all hidden choices of the column. -/
theorem overlapping_column_game (π : Permutation) (u t : (I × J) ↪ Words)
    (M : (Port → Words) → Closed (WS Port Words E) Bool) (q : ℕ)
    (hq : PUE (spec:=unifSpec) cnt0 M q) (ρ : SubState ((Port × Words) × E)) :
    let w := fun p => qWeight (· = true) (M (oracle p)) (ρ.matrix ⊗ₖ (SubState.basis ()).matrix)
    SetOracle.uniformMean (fun i => w (swapInjections (slice u i) (π,slice t i)).1) ≤
      w π + ENNReal.ofReal (8*(q:ℝ)^2*(2/Fintype.card I)) := by
  dsimp only
  exact bounded_overlap_game _ _ (keyOwners π u t) 2 (keyOwners_card π u t)
    (outside_column π u t) M q hq ρ

/-- The pre-challenge state estimate also allows a later measurement to
depend on the chosen key. Probability bounds for a common test alone do
not imply this squared-norm estimate. -/
theorem overlapping_column_states (π : Permutation) (u t : (I × J) ↪ Words)
    (op : ℕ → Hidden.Vec E ≃ₗᵢ[ℂ] Hidden.Vec E) (x : Hidden.Vec E) (q : ℕ) :
    ∑ i, ‖Hidden.interact (swapInjections (slice u i) (π,slice t i)).1 op x q -
      Hidden.interact π op x q‖^2 ≤ 8*(q:ℝ)^2*‖x‖^2 := by
  classical
  let rows (i : I) := Finset.univ.filter fun p => i ∈ keyOwners π u t p
  have multiplicity (p : Port) : (Finset.univ.filter fun i => p ∈ rows i).card ≤ 2 := by
    have e : Finset.univ.filter (fun i => p ∈ rows i) = keyOwners π u t p := by ext i; simp [rows]
    rw [e]; exact keyOwners_card _ _ _ _
  have h := Hidden.changed_call_sum (E:=E) π (fun i => (swapInjections (slice u i) (π,slice t i)).1)
    id rows 2 (fun i p out => outside_column π u t i p (fun mem => out (by simpa [rows] using mem)))
    multiplicity
  exact Hidden.query_hybrid _ _ 8 (by intro y; convert! h y using 1 <;> norm_num) op x q

end
end Reduction.ShakePermutation.Program
#print axioms Reduction.ShakePermutation.Program.overlapping_column_game
