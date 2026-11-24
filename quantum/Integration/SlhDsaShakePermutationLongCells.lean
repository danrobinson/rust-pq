import Integration.SlhDsaShakePermutationLongFrames
import Integration.SlhDsaShakePermutationLongBox

/-! Partition an ordered completion row by its frozen coordinates.
Inside a cell both unoccupied coordinate alphabets are independent. -/
namespace Reduction.ShakePermutation.Long.Gram
open Classical Harmonic Finset
noncomputable section
set_option linter.unusedSectionVars false
variable {A : Type} [Fintype A] [DecidableEq A] [Inhabited A] {r : ℕ}

abbrev Tag (D : Finset A) (r : ℕ) := Fin r → Option D

def tag (D : Finset A) (x : Fin r → A) : Tag D r := fun i =>
  if h : x i ∈ D then some ⟨x i,h⟩ else none

def holes {D : Finset A} (b : Tag D r) := Finset.univ.filter (fun i => b i = none)

def frozen {D : Finset A} (b : Tag D r) (i : Fin r) : A :=
  ((b i).map Subtype.val).getD default

def fit {D : Finset A} (p : Equiv.Perm A) (b : Tag D r) (x y : Fin r → A) :=
  ∀ i, match b i with
    | none => x i ∉ D ∧ p.symm (y i) ∉ D
    | some a => x i = a.val ∧ y i = p a.val

theorem fit_unique {D : Finset A} (p : Equiv.Perm A) (b : Tag D r) (x y : Fin r → A) :
    fit p b x y ↔ b = tag D x ∧ admissible D p x y := by
  constructor
  · intro h
    refine ⟨funext (fun i => ?_),fun i => ?_⟩
    · have hi := h i
      cases eq : b i with
      | none => simp [eq] at hi; simp [tag,hi.1]
      | some a =>
        simp [eq] at hi
        simp [tag,hi.1]
    · have hi := h i
      cases eq : b i with
      | none => simp [eq] at hi; exact ⟨fun hd => (hi.1 hd).elim,fun _ => hi.2⟩
      | some a =>
        simp [eq] at hi
        exact ⟨fun _ => hi.2.trans (congrArg p hi.1.symm),fun hf => (hf (hi.1 ▸ a.property)).elim⟩
  · rintro ⟨rfl,h⟩ i
    by_cases mem : x i ∈ D
    · simp [tag,mem,(h i).1 mem]
    · simp [tag,mem,(h i).2 mem]

theorem holes_tag (D : Finset A) (x : Fin r → A) : holes (tag D x) = freshSet D x := by
  ext i; by_cases mem : x i ∈ D <;> simp [holes,tag,freshSet,mem]

theorem fit_box {D : Finset A} (p : Equiv.Perm A) (b : Tag D r) (x y : Fin r → A) :
    fit p b x y ↔ inside (fun _ => Dᶜ) (holes b).toList (frozen b) x ∧
      inside (fun _ => (D.map p.toEmbedding)ᶜ) (holes b).toList (fun i => p (frozen b i)) y := by
  have image (v : A) : v ∈ D.map p.toEmbedding ↔ p.symm v ∈ D := by
    simp
  simp only [inside,Finset.mem_toList,holes,mem_filter,mem_univ,true_and,Finset.mem_compl,image]
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

end
end Reduction.ShakePermutation.Long.Gram
#print axioms Reduction.ShakePermutation.Long.Gram.fit_box
