import Integration.SlhDsaCompressionConstraintReadout
import Integration.SlhDsaCompressionCompileFailure
import Integration.SlhDsaCompressionLeftTables

namespace Reduction.Compression.LongClass
open Recording Recording.Database Recording.Compile MLink Ideal PQ.QROM Quantum Classical

private noncomputable def fibre {B C : Type} [Fintype B] [DecidableEq C]
    (e : B ≃ C × C) (u : C) : Finset B :=
  Finset.univ.filter fun y => (e y).1 = u

private theorem mem_fibre {B C : Type} [Fintype B] [DecidableEq C]
    (e : B ≃ C × C) (u : C) (y : B) : y ∈ fibre e u ↔ (e y).1 = u := by simp [fibre]

private theorem general_density {B C : Type} [Fintype B] [Fintype C] [Nonempty C] [DecidableEq C]
    (e : B ≃ C × C) (u : C) :
    ((fibre e u).card : ℝ) / Fintype.card B = (Fintype.card C : ℝ)⁻¹ := by
  have eq : (fibre e u).card = (({u} : Finset C) ×ˢ (Finset.univ : Finset C)).card := by
    apply Finset.card_equiv e
    intro i
    simp only [fibre,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_product,Finset.mem_singleton,and_true]
  rw [eq,Finset.card_product,Finset.card_singleton,one_mul,Finset.card_univ,
    Fintype.card_congr e,Fintype.card_prod,Nat.cast_mul]
  rw [div_eq_mul_inv,mul_inv_rev,← mul_assoc,
      mul_inv_cancel₀ (by positivity : (Fintype.card C : ℝ) ≠ 0),one_mul]

private theorem read_log {X Y C L V α : Type} [Fintype X] [DecidableEq X]
    [Fintype Y] [Nonempty Y] [DecidableEq Y] [Fintype C] [DecidableEq C] [Nonempty C]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (e : Y ≃ C × C) (tag : L → X) (logs : α → List (L × C)) (ok : α → Prop)
    (goal : DB X Y → Prop) (m : ℕ)
    (rec : ∀ z d, ok z → (∀ p ∈ logs z, ∃ y, d (tag p.1) = some y ∧ (e y).1 = p.2) → goal d)
    (len : ∀ z, (logs z).length ≤ m) (z : α) (v : DB X Y → V) :
    sumWeight (fun h : X → Y => ok z ∧ ∀ p ∈ logs z, (e (h (tag p.1))).1 = p.2)
      (fun h => tensor v (fun j => some (h j))) ≤
      (Real.sqrt (sumWeight goal v) + (2*(m:ℝ)*Real.sqrt (Fintype.card C : ℝ)⁻¹)*
        Real.sqrt (∑ d, ‖v d‖^2))^2 := by
  classical
  by_cases valid : ok z
  · let cell := fun (p : L × C) => (tag p.1,fibre e p.2)
    let cs := (logs z).map cell
    apply readout_failure cs m (by simpa [cs] using len z) _ (by positivity) _ _ _ _ _ v
    · intro c hc
      obtain ⟨p,_,rfl⟩ := List.mem_map.mp hc
      exact (general_density e p.2).le
    · intro h hh c hc
      obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hc
      exact (mem_fibre e p.2 (h (tag p.1))).mpr (hh.2 p hp)
    · intro d hd
      apply rec z d valid
      intro p hp
      obtain ⟨y,hy,eq⟩ := hd (cell p) (List.mem_map.mpr ⟨p,hp,rfl⟩)
      exact ⟨y,eq,(mem_fibre e p.2 y).mp hy⟩
  · simp only [valid,false_and,sumWeight,ite_false,Finset.sum_const_zero]
    exact sq_nonneg _

/-- A measured valid transcript certifies a recorded failure whenever all of its
SHA-256 observations are already recorded. The remaining readout cost depends on
its maximum length even when the list repeats a compression input. -/
theorem log_leaf {α : Type} (logs : α → List (Left × St)) (ok : α → Prop) (goal : Cells → Prop)
    (m : ℕ) (rec : ∀ z d, ok z → (∀ p ∈ logs z, ∃ y, d (.inl p.1) = some y ∧
      (LeftPort.halves y).1 = p.2) → goal d) (len : ∀ z, (logs z).length ≤ m)
    (A : QReg) (z : α) (v : State A) :
    sumWeight (fun h : Full => ok z ∧ ∀ p ∈ logs z, LeftPort.projectTable h p.1 = p.2)
      (fun h => tensor v (fun j => some (h j))) ≤
      Failure.potential goal (2*(m:ℝ)*Real.sqrt (((2:ℝ)^256)⁻¹)) v := by
  have h := read_log LeftPort.halves (Sum.inl : Left → Input) logs ok goal m rec len z v
  rw [card_St,Nat.cast_pow,Nat.cast_ofNat] at h
  exact h

end Reduction.Compression.LongClass
#print axioms Reduction.Compression.LongClass.log_leaf
