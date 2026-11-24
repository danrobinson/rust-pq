import Integration.SlhDsaShakePermutationLongNorm

/-! Near-isometry of the normalized permutation completion Gram on the
two-sided harmonic subspace. This version uses ordered tuples and divides
by the number of simultaneous orderings. -/
namespace Reduction.ShakePermutation.Long.Gram
open Classical Harmonic Finset OracleComp PermutationConditioning
noncomputable section
set_option linter.unusedSectionVars false
variable {A : Type} [Fintype A] [DecidableEq A] [Inhabited A] {r : ℕ}

def coeff (v : Space A r) : Coeff A r := fun x y => v (x,y)

structure HarmonicVector (v : Space A r) : Prop where
  sx : ∀ x y, ¬Function.Injective x → coeff v x y = 0
  sy : ∀ x y, ¬Function.Injective y → coeff v x y = 0
  left : ∀ i y, zeroMarginal (fun x => coeff v x y) i
  right : ∀ i x, zeroMarginal (coeff v x) i
  symm : Symmetric (coeff v)

def gram (v : Space A r) : Space A r := WithLp.toLp 2 (fun j =>
  if Function.Injective j.1 ∧ Function.Injective j.2 then
    (∑ y, ∑ x, (count (pairs j.1 j.2++pairs x y) : ℂ) * coeff v x y) /
      (r.factorial * (Fintype.card A-r).factorial) else 0)

private theorem order (x y : Fin r → A) (hx : Function.Injective x) :
    ∃ e : Fin r ≃ inputs (pairs x y), ∀ i, (e i).val = x i := by
  let g (i : Fin r) : inputs (pairs x y) := ⟨x i,(inputs_mem _ _).mpr ⟨y i,List.mem_ofFn.mpr ⟨i,rfl⟩⟩⟩
  have hg : Function.Injective g := fun i j h => hx (congrArg Subtype.val h)
  have onto : Function.Surjective g := by
    rintro ⟨a,ha⟩
    obtain ⟨b,hab⟩ := (inputs_mem _ _).mp ha
    obtain ⟨i,hi⟩ := List.mem_ofFn.mp hab
    exact ⟨i,Subtype.ext (congrArg Prod.fst hi)⟩
  exact ⟨Equiv.ofBijective g ⟨hg,onto⟩,fun _ => rfl⟩

private theorem proj_sum {K : Type} (s : Finset K) (f : K → Space A r) (i : Index A r) :
    (∑ j ∈ s, f j) i = ∑ j ∈ s, f j i :=
  congrFun (WithLp.ofLp_sum 2 _ s f) i |>.trans (Finset.sum_apply ..)

private theorem block_coordinates (N : ℕ) (H : Finset (Fin r)) (v : Space A r) (x y : Fin r → A) :
    block N H v (x,y) = ∑ w : Equiv.Perm (Fin r), internal (fun j => (weight N r j : ℂ)) (coeff v) x y H w := by
  simp only [block,proj_sum,PiLp.smul_apply,move_apply,smul_eq_mul,internal,mul_ite,mul_zero]
  rw [← Finset.sum_filter]
  symm; apply Finset.sum_subtype (Finset.univ.filter (permutes H)) (fun w => by simp) (fun w => (weight N r H.card : ℂ) * coeff v x (y ∘ w))

theorem gram_eq (v : Space A r) (h : HarmonicVector v) : gram v = ∑ H : Finset (Fin r), block (Fintype.card A) H v := by
  apply PiLp.ext; rintro ⟨x,y⟩
  rw [proj_sum]
  let N := Fintype.card A
  change (if Function.Injective x ∧ Function.Injective y then _ else 0) = _
  by_cases good : Function.Injective x ∧ Function.Injective y
  · rw [ite_eq_left good]
    let t := pairs x y
    obtain ⟨p,hp⟩ := Equiv.Perm.exists_extending_pair x y good.1 good.2
    let q : Extensions t := ⟨p,fun z hz => by obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hz; exact hp i⟩
    obtain ⟨e,enum⟩ := order x y good.1
    have rk : rank t = r := by
      change (inputs t).card = r
      rw [← Fintype.card_coe,← Fintype.card_congr e,Fintype.card_fin]
    let c (j : ℕ) : ℂ := (N-(r+j)).factorial
    have roweq := row_kernel t q (coeff v) h.sx h.sy h.left h.right
    rw [rk] at roweq
    have aa := aggregate e p (coeff v) c h.sx h.sy h.symm
    change (∑ H : Finset (Fin r), c H.card * kernel (D:=inputs t) p (coeff v) H) = _ at aa
    rw [roweq,aa]
    simp only [enum,hp]
    have den : (r.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero r
    rw [mul_div_mul_left _ _ den]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl; intro H _
    rw [block_coordinates,Finset.sum_div]
    apply Finset.sum_congr rfl; intro w _
    simp only [internal,weight,c,N,Complex.ofReal_div,Complex.ofReal_natCast,Nat.sub_add_eq]
    ring
  · rw [ite_eq_right good]
    symm; apply Finset.sum_eq_zero; intro H _
    rw [block_coordinates]
    apply Finset.sum_eq_zero; intro w _
    rcases not_and_or.mp good with hx|hy
    · simp [internal,h.sx _ _ hx]
    · have new : ¬Function.Injective (y ∘ w) := fun hh => hy (fun i j he =>
        w.symm.injective (hh (a₁:=w.symm i) (a₂:=w.symm j) (by simpa [Function.comp_def] using he)))
      simp [internal,h.sy _ _ new]

theorem gram_near (v : Space A r) (h : HarmonicVector v) (size : 3*r+1 ≤ Fintype.card A) :
    ‖gram v-v‖ ≤ ((r : ℝ) * ((r : ℝ)/(Fintype.card A-2*r : ℕ))) * ‖v‖ :=
  (gram_eq v h) ▸ near_identity _ size v

end
end Reduction.ShakePermutation.Long.Gram
#print axioms Reduction.ShakePermutation.Long.Gram.gram_near
