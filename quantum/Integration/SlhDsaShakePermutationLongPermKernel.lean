import Integration.SlhDsaShakePermutationLongKernel

/-! On a row of the same degree, every injective tuple into its old
alphabet is an ordering of that alphabet. -/
namespace Reduction.ShakePermutation.Long.Gram
open Classical Harmonic Finset OracleComp PermutationConditioning
noncomputable section
set_option linter.unusedSectionVars false
variable {A : Type} [Fintype A] [DecidableEq A] [Inhabited A] {r : ℕ}

def Symmetric (f : Coeff A r) := ∀ (u : Equiv.Perm (Fin r)) (x y : Fin r → A),
  f (x ∘ u) (y ∘ u) = f x y

private theorem onlyPerms {D : Type} [Fintype D] [DecidableEq D] (e : Fin r ≃ D) (g : (Fin r → D) → ℂ)
    (supp : ∀ a, ¬Function.Injective a → g a = 0) :
    ∑ a, g a = ∑ u : Equiv.Perm (Fin r), g (e ∘ u) := by
  symm; apply Fintype.sum_of_injective (fun (u : Equiv.Perm (Fin r)) => e ∘ u)
    (fun _ _ eq => Equiv.ext (fun i => e.injective (congrFun eq i))) _ _ _ (fun _ => rfl)
  intro a out; apply supp a; intro inj
  let z := e.symm ∘ a
  have zi := e.symm.injective.comp inj
  let u := Equiv.ofBijective z ⟨zi,Finite.surjective_of_injective zi⟩
  exact out ⟨u,funext (fun i => e.apply_symm_apply _)⟩

theorem kernel_perms {D : Finset A} (e : Fin r ≃ D) (p : Equiv.Perm A) (f : Coeff A r) (H : Finset (Fin r))
    (sx : ∀ x y, ¬Function.Injective x → f x y = 0)
    (sy : ∀ x y, ¬Function.Injective y → f x y = 0) :
    kernel (D:=D) p f H = ∑ u : Equiv.Perm (Fin r), ∑ w : Equiv.Perm (Fin r),
      if ∀ i ∉ H, w i = u i then f (fun i => (e (u i)).val) (fun i => p (e (w i)).val) else 0 := by
  unfold kernel
  rw [Finset.sum_comm]
  rw [onlyPerms e _ (fun x hx => Finset.sum_eq_zero (fun y _ => by
    split
    · apply sx; exact fun hi => hx (fun _ _ h => hi (congrArg Subtype.val h))
    · rfl))]
  apply Finset.sum_congr rfl; intro u _
  rw [onlyPerms e _ (fun y hy => by
    split
    · apply sy; exact fun hi => hy (fun _ _ h => hi (congrArg p (congrArg Subtype.val h)))
    · rfl)]
  simp only [Function.comp_apply,e.apply_eq_iff_eq]

def permutes (H : Finset (Fin r)) (w : Equiv.Perm (Fin r)) : Prop := ∀ i ∉ H, w i = i

theorem shifted (u : Equiv.Perm (Fin r))
    (H : Finset (Fin r)) (w : Equiv.Perm (Fin r)) :
    (∀ i ∉ H, w i = u i) ↔ permutes (H.map u.toEmbedding) (u.symm.trans w) := by
  constructor
  · intro h j hj
    have hh : u.symm j ∉ H := by simpa using hj
    exact (h _ hh).trans (u.apply_symm_apply _)
  · intro h i hi
    have hh : u i ∉ H.map u.toEmbedding := by simpa using hi
    simpa using h _ hh

def rotate (u : Equiv.Perm (Fin r)) : Equiv.Perm (Equiv.Perm (Fin r)) where
  toFun w := u.symm.trans w
  invFun w := u.trans w
  left_inv w := by ext i; simp
  right_inv w := by ext i; simp

def internal (c : ℕ → ℂ) (f : Coeff A r) (x y : Fin r → A) (H : Finset (Fin r)) (w : Equiv.Perm (Fin r)) :=
  c H.card * (if permutes H w then f x (y ∘ w) else 0)

theorem aggregate {D : Finset A} (e : Fin r ≃ D) (p : Equiv.Perm A) (f : Coeff A r) (c : ℕ → ℂ)
    (sx : ∀ x y, ¬Function.Injective x → f x y = 0) (sy : ∀ x y, ¬Function.Injective y → f x y = 0)
    (symm : Symmetric f) :
    (∑ H : Finset (Fin r), c H.card * kernel (D:=D) p f H) =
      (r.factorial : ℂ) * ∑ H : Finset (Fin r), ∑ w : Equiv.Perm (Fin r),
        internal c f (fun i => (e i).val) (fun i => p (e i).val) H w := by
  let x (i : Fin r) := (e i).val
  let y (i : Fin r) := p (e i).val
  let v := internal c f x y
  have rotate_eq (H : Finset (Fin r)) (u w : Equiv.Perm (Fin r)) :
      c H.card * (if ∀ i ∉ H, w i = u i then f (x ∘ u) (y ∘ w) else 0) = v (u.finsetCongr H) (rotate u w) := by
    have h : f (x ∘ u) (y ∘ w) = f x (y ∘ (rotate u w)) := by
      have hu := symm u x (y ∘ (rotate u w))
      simpa [rotate,Function.comp_def] using hu
    simp only [v,internal,Equiv.finsetCongr_apply,Finset.card_map,shifted u H w,h,rotate,Equiv.coe_fn_mk]
  have batch (u : Equiv.Perm (Fin r)) :
      (∑ H : Finset (Fin r), ∑ w : Equiv.Perm (Fin r), v (u.finsetCongr H) (rotate u w)) =
        ∑ H : Finset (Fin r), ∑ w : Equiv.Perm (Fin r), v H w := by
    simp_rw [Equiv.sum_comp (rotate u)]
    exact Equiv.sum_comp u.finsetCongr (fun H => ∑ w, v H w)
  conv_lhs => simp only [kernel_perms e p f _ sx sy,Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  change (∑ u : Equiv.Perm (Fin r), ∑ H : Finset (Fin r), ∑ w : Equiv.Perm (Fin r),
      c H.card * (if ∀ i ∉ H, w i = u i then f (x ∘ u) (y ∘ w) else 0)) =
    (r.factorial : ℂ) * ∑ H : Finset (Fin r), ∑ w : Equiv.Perm (Fin r), v H w
  simp_rw [rotate_eq,batch]
  rw [Finset.sum_const,Finset.card_univ,Fintype.card_perm,Fintype.card_fin,nsmul_eq_mul]

end
end Reduction.ShakePermutation.Long.Gram
#print axioms Reduction.ShakePermutation.Long.Gram.aggregate
