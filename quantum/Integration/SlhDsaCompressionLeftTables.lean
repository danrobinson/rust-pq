import Integration.SlhDsaCompressionCompileResponse
import Integration.SlhDsaCompressionClassPort

namespace Reduction.Compression.Recording.Compile.LeftPort
open MLink Ideal MIdeal.Sha512 PQ.QROM Quantum ENNReal
open scoped ComplexOrder
noncomputable def halves : Chain512 ≃ St × St := Fintype.equivOfCardEq (by
  rw [Fintype.card_prod,card_St,card_chain512,← pow_add])

noncomputable def projectTable (h : Full) : CF St Blk := fun x => (halves (h (.inl x))).1

noncomputable def mapping (b : CF Chain512 Block512) : Response.Mapping
  | .inl _, y => ((halves y).1,0)
  | .inr j, _ => (0,arrayVectorEquivFin UInt64 8 (b j))

theorem port (b : CF Chain512 Block512) (h : Full) :
    Response.project (mapping b) h = oracle (projectTable h,b) := by
  funext x
  cases x <;> rfl

private noncomputable def shuffle : Full ≃ (Left → St) × ((Left → St) × (Right → Chain512)) :=
  split.trans (((Equiv.arrowCongr (Equiv.refl Left) halves).trans
    (Equiv.arrowProdEquivProdArrow Left (fun _ => St) (fun _ => St))).prodCongr
    (Equiv.refl (Right → Chain512))) |>.trans (Equiv.prodAssoc _ _ _)

private theorem mean_space {A B C : Type} [Fintype A] [Fintype B] [Fintype C] [Nonempty C]
    (e : A ≃ B × C) (f : B → ℝ≥0∞) :
    (∑ x, unifW _ x * f (e x).1) = ∑ b, unifW _ b * f b := by
  rw [show (∑ x, unifW _ x * f (e x).1) = ∑ t : B × C, unifW A (e.symm t) * f t.1 from
    (Equiv.sum_comp e (fun t => unifW A (e.symm t) * f t.1))]
  have hc : (Fintype.card C : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  unfold unifW
  rw [Fintype.card_congr e, Fintype.card_prod, Nat.cast_mul,
    ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl (ENNReal.natCast_ne_top _)),Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro b _
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  calc _ = ((Fintype.card C : ℝ≥0∞) * (Fintype.card C : ℝ≥0∞)⁻¹) * ((Fintype.card B : ℝ≥0∞)⁻¹ * f b) := by ring
       _ = _ := by rw [ENNReal.mul_inv_cancel hc (ENNReal.natCast_ne_top _),one_mul]

theorem mean (f : CF St Blk → ℝ≥0∞) :
    (∑ h : Full, unifW _ h * f (projectTable h)) = ∑ a, unifW _ a * f a := by
  exact mean_space shuffle f

end Reduction.Compression.Recording.Compile.LeftPort
#print axioms Reduction.Compression.Recording.Compile.LeftPort.mean
