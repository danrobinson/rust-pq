import Integration.SlhDsaShakePermutationLongRows

/-! After harmonic cancellation the row only contains permutations of its
already occupied source and image labels. The free-coordinate subset
exactly identifies the original cell once the input tuple is fixed. -/
namespace Reduction.ShakePermutation.Long.Gram
open Classical Harmonic Finset OracleComp PermutationConditioning
noncomputable section
set_option linter.unusedSectionVars false
variable {A : Type} [Fintype A] [DecidableEq A] [Inhabited A] {r : ℕ}

def closedFit {D : Finset A} (p : Equiv.Perm A) (b : Tag D r) (x y : Fin r → A) :=
  ∀ i, match b i with
    | none => x i ∈ D ∧ p.symm (y i) ∈ D
    | some a => x i = a.val ∧ y i = p a.val

private theorem fits {D : Finset A} (p : Equiv.Perm A) (b : Tag D r) (x y : Fin r → A) :
    closedFit p b x y ↔ inside (fun _ => D) (holes b).toList (frozen b) x ∧
      inside (fun _ => D.map p.toEmbedding) (holes b).toList (fun i => p (frozen b i)) y := by
  have image (v : A) : v ∈ D.map p.toEmbedding ↔ p.symm v ∈ D := by simp
  simp only [inside,Finset.mem_toList,holes,mem_filter,mem_univ,true_and,image]
  constructor
  · intro h
    refine ⟨⟨fun i hi => ?_,fun i hi => ?_⟩,fun i hi => ?_,fun i hi => ?_⟩
    · exact ((by simpa [hi] using h i) : _ ∧ _).1
    · obtain ⟨a,ha⟩ := Option.ne_none_iff_exists'.mp hi
      simpa [frozen,ha] using (show x i = a.val from ((by simpa [ha] using h i) : _ ∧ _).1)
    · exact ((by simpa [hi] using h i) : _ ∧ _).2
    · obtain ⟨a,ha⟩ := Option.ne_none_iff_exists'.mp hi
      simpa [frozen,ha] using (show y i = p a.val from ((by simpa [ha] using h i) : _ ∧ _).2)
  · rintro ⟨⟨xin,xout⟩,yin,yout⟩ i
    cases eq : b i with
    | none => exact ⟨xin i eq,yin i eq⟩
    | some a =>
      have ne : b i ≠ none := by simp [eq]
      exact ⟨by simpa [frozen,eq] using xout i ne,by simpa [frozen,eq] using yout i ne⟩

theorem inside_cell {D : Finset A} (p : Equiv.Perm A) (b : Tag D r) (f : Coeff A r)
    (left : ∀ i y, zeroMarginal (fun x => f x y) i) (right : ∀ i x, zeroMarginal (f x) i) :
    cell p b f = ∑ y, ∑ x, if closedFit p b x y then f x y else 0 := by
  rw [cell_box,two_ends _ _ f _ (holes b).nodup_toList (fun i _ => left i) (fun i _ => right i)]
  simp only [compl_compl]
  rw [expand _ _ _ (holes b).nodup_toList]
  apply Finset.sum_congr rfl; intro y _
  split <;> rename_i hy
  · rw [expand _ _ _ (holes b).nodup_toList]
    simp only [fits,hy,and_true]
  · simp only [fits,hy,and_false,ite_false,Finset.sum_const_zero]

def mask {D : Finset A} (H : Finset (Fin r)) (x : Fin r → D) : Tag D r := fun i =>
  if i ∈ H then none else some (x i)

theorem holes_mask {D : Finset A} (H : Finset (Fin r)) (x : Fin r → D) : holes (mask H x) = H := by
  ext i; by_cases h : i ∈ H <;> simp [mask,holes,h]

theorem occupied {D : Finset A} {p : Equiv.Perm A} {b : Tag D r} {x y : Fin r → A}
    (h : closedFit p b x y) : (∀ i, x i ∈ D) ∧ ∀ i, p.symm (y i) ∈ D := by
  have both (i) : x i ∈ D ∧ p.symm (y i) ∈ D := by
    have hi := h i
    cases eq : b i with
    | none => simpa [eq] using hi
    | some a => simp [eq] at hi; simp [hi.1,hi.2]
  exact ⟨fun i => (both i).1,fun i => (both i).2⟩

theorem mask_unique {D : Finset A} (p : Equiv.Perm A) (b : Tag D r) (x y : Fin r → D) (H : Finset (Fin r)) :
    holes b = H ∧ closedFit p b (fun i => (x i).val) (fun i => p (y i).val) ↔
      b = mask H x ∧ ∀ i ∉ H, y i = x i := by
  constructor
  · rintro ⟨rfl,h⟩
    have frozen_eq (i : Fin r) (ne : i ∉ holes b) : b i = some (x i) ∧ y i = x i := by
      have hn : b i ≠ none := by simpa [holes] using ne
      obtain ⟨a,ha⟩ := Option.ne_none_iff_exists'.mp hn
      have hc := h i; simp only [ha,p.apply_eq_iff_eq] at hc
      have e1 := Subtype.ext hc.1
      have e2 := Subtype.ext hc.2
      exact ⟨ha.trans (congrArg some e1.symm),e2.trans e1.symm⟩
    refine ⟨funext (fun i => ?_),fun i hi => (frozen_eq i hi).2⟩
    by_cases hi : i ∈ holes b
    · simpa [mask,hi] using (show b i = none from (Finset.mem_filter.mp hi).2)
    · simpa [mask,hi] using (frozen_eq i hi).1
  · rintro ⟨rfl,h⟩
    refine ⟨holes_mask _ _,fun i => ?_⟩
    by_cases hi : i ∈ H
    · simp [mask,hi]
    · simp [mask,hi,h i hi]

end
end Reduction.ShakePermutation.Long.Gram
#print axioms Reduction.ShakePermutation.Long.Gram.mask_unique
