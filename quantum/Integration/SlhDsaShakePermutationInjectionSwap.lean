import Integration.SlhDsaShakePermutationResample

/-! Resample a public permutation on an injectively labelled column,
including when its original and replacement image sets overlap. -/
namespace Reduction.ShakePermutation.Program
open Classical ENNReal
noncomputable section
variable {J A : Type} [Fintype J] [Fintype A]

private abbrev Outside (x y : J ↪ A) := {a : A // a ∉ Set.range x ∧ a ∉ Set.range y}

private theorem supported (x y : J ↪ A) : ∃ e : Equiv.Perm A,
    (∀ j, e (x j) = y j) ∧ ∀ a, a ∉ Set.range x → a ∉ Set.range y → e a = a := by
  classical
  let f : J ⊕ Outside x y → A := Sum.elim x Subtype.val
  let g : J ⊕ Outside x y → A := Sum.elim y Subtype.val
  have inj (k : J ↪ A) (out : ∀ a : Outside x y, a.val ∉ Set.range k) :
      Function.Injective (Sum.elim k (Subtype.val : Outside x y → A)) := by
    rintro (i|a) (j|b) h
    · exact congrArg Sum.inl (k.injective h)
    · exact (out b ⟨i,h⟩).elim
    · exact (out a ⟨j,h.symm⟩).elim
    · exact congrArg Sum.inr (Subtype.ext h)
  obtain ⟨e,he⟩ := Equiv.Perm.exists_extending_pair f g (inj x (fun a => a.property.1))
    (inj y (fun a => a.property.2))
  exact ⟨e,fun j => he (.inl j),fun a hx hy => he (.inr ⟨a,hx,hy⟩)⟩

private def rank (x : J ↪ A) : ℕ := (Fintype.equivFin (J ↪ A) x).val

private theorem rank_inj : Function.Injective (@rank J A _ _) :=
  fun _ _ h => (Fintype.equivFin _).injective (Fin.ext h)

def reassign (x y : J ↪ A) : Equiv.Perm A :=
  if rank x < rank y then (supported x y).choose
  else if rank y < rank x then (supported y x).choose.symm else Equiv.refl A

theorem reassign_hit (x y : J ↪ A) (j : J) : reassign x y (x j) = y j := by
  unfold reassign
  split
  · exact (supported x y).choose_spec.1 j
  · split
    · exact ((supported y x).choose.symm_apply_eq).mpr ((supported y x).choose_spec.1 j).symm
    · have : x = y := rank_inj (by omega)
      subst y; rfl

theorem reassign_miss (x y : J ↪ A) (a : A) (hx : a ∉ Set.range x) (hy : a ∉ Set.range y) :
    reassign x y a = a := by
  unfold reassign
  split
  · exact (supported x y).choose_spec.2 a hx hy
  · split
    · exact ((supported y x).choose.symm_apply_eq).mpr ((supported y x).choose_spec.2 a hy hx).symm
    · rfl

theorem reassign_symm (x y : J ↪ A) : reassign y x = (reassign x y).symm := by
  rcases lt_trichotomy (rank x) (rank y) with h|h|h
  · simp [reassign,h,not_lt_of_gt h]
  · simp [reassign,h]
  · simp [reassign,h,not_lt_of_gt h]

def swapInjections (u : J ↪ A) (p : Equiv.Perm A × (J ↪ A)) :=
  (p.1.trans (reassign (imageTuple u p.1) p.2),imageTuple u p.1)

theorem swapInjections_involutive (u : J ↪ A) : Function.Involutive (swapInjections u) := by
  rintro ⟨π,t⟩
  let x := imageTuple u π
  have now : imageTuple u (π.trans (reassign x t)) = t := by
    ext j; exact reassign_hit x t j
  change ((π.trans (reassign x t)).trans (reassign (imageTuple u (π.trans (reassign x t))) x),
    imageTuple u (π.trans (reassign x t))) = _
  rw [now,reassign_symm x t]
  exact Prod.ext (Equiv.ext fun a => (reassign x t).symm_apply_apply (π a)) rfl

/-- The joint uniform law is preserved exactly even for large columns.
No exceptional collision probability between the two image sets is charged. -/
theorem swapInjections_law (u : J ↪ A) (W : Equiv.Perm A → (J ↪ A) → ℝ≥0∞) :
    SetOracle.uniformMean (fun π => SetOracle.uniformMean (W π)) =
      SetOracle.uniformMean (fun π => SetOracle.uniformMean (fun t =>
        W (swapInjections u (π,t)).1 (swapInjections u (π,t)).2)) := by
  classical
  let e := Function.Involutive.toPerm _ (swapInjections_involutive u)
  have h := Equiv.sum_comp e (fun s => unifW _ s.1 * (unifW _ s.2 * W s.1 s.2))
  have he (s) : e s = swapInjections u s := rfl
  simp only [he] at h
  simpa only [SetOracle.uniformMean,Finset.mul_sum,Fintype.sum_prod_type,unifW] using h.symm

end
end Reduction.ShakePermutation.Program
#print axioms Reduction.ShakePermutation.Program.swapInjections_law
