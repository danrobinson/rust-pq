import Integration.SlhDsaCompressionCompilePort
import Integration.SlhDsaCompressionReadout

namespace Reduction.Compression.Recording.Compile
open PQ.QROM Quantum Database Classical

private noncomputable def realIso {V W : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [NormedSpace ℝ V] [NormedSpace ℝ W]
    [IsScalarTower ℝ ℂ V] [IsScalarTower ℝ ℂ W] (e : V ≃ₗᵢ[ℂ] W) : V ≃ₗᵢ[ℝ] W :=
  { toLinearEquiv := e.toLinearEquiv.restrictScalars ℝ, norm_map' := e.norm_map }

/-- Group the coordinates of the native port register by their input address. -/
noncomputable def fibers (X Y U : Type) [Fintype X] [Fintype Y] [Fintype U] :
    EuclideanSpace ℂ (Tight.Reg X Y U) ≃ₗᵢ[ℝ] Work X (Fiber U Y) where
  toFun v := WithLp.toLp 2 (slice U v)
  invFun w := WithLp.toLp 2 fun p => w p.1.1 (p.1.2,p.2)
  left_inv v := by ext ⟨⟨x,y⟩,u⟩; rfl
  right_inv w := by ext x ⟨y,u⟩; rfl
  map_add' u v := by ext x ⟨y,e⟩; rfl
  map_smul' a v := by ext x ⟨y,e⟩; rfl
  norm_map' v := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp only [PiLp.norm_sq_eq_of_L2,Fintype.sum_prod_type]
    rfl

abbrev Vec (A : QReg) := EuclideanSpace ℂ (A × Unit)

/-- Input and output register changes for exactly the VCVio query instruction. -/
noncomputable def expose {A U : QReg} (l : A ≃ (Input × Output) × U) :
    Vec A ≃ₗᵢ[ℝ] Work Input (Fiber (U × Unit) Output) :=
  (realIso (Purify.splitIso l)).trans (fibers Input Output (U × Unit))

noncomputable def restore (U : QReg) :
    Work Input (Fiber (U × Unit) Output) ≃ₗᵢ[ℝ] Vec (QReg.of ((Input × Output) × U)) :=
  (fibers Input Output (U × Unit)).symm.trans (realIso (Purify.joinIso Input Output U))

set_option maxRecDepth 40000 in
theorem query_vector {A U : QReg} (l : A ≃ (Input × Output) × U) (a : Ideal.CF Ideal.St Ideal.Blk)
    (h : Full) (v : Vec A) :
    Purify.qvec l (project a h) v = restore U (WithLp.toLp 2 fun x =>
      control (U × Unit) a x (some (h x)) ((expose l v) x)) := by
  let u := (Tight.stdOracle Input Output (U × Unit)).O (project a h) (Purify.splitIso l v)
  have eq : fibers Input Output (U × Unit) u = WithLp.toLp 2 (fun x =>
      control (U × Unit) a x (some (h x)) ((expose l v) x)) := by
    ext1 x
    exact ordinary_port _ a h _ x
  rw [← eq]
  change _ = Purify.joinIso _ _ _ ((fibers Input Output (U × Unit)).symm ((fibers Input Output (U × Unit)) u))
  rw [LinearIsometryEquiv.symm_apply_apply]
  rfl

end Reduction.Compression.Recording.Compile
#print axioms Reduction.Compression.Recording.Compile.query_vector
