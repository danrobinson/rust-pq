import Integration.SlhDsaShakePermutationRelabelOracle
import Mathlib.LinearAlgebra.Matrix.Reindex

/-! Exact conjugation for h queries in the fixed-mask branch of the simulator.
The central unitary may include the caller's response and ancillary registers. -/
namespace Reduction.ShakePermutation.Relabel
open Quantum Classical Tails Matrix
set_option maxRecDepth 8192
set_option maxHeartbeats 800000
variable (π : Permutation) (k k' : Db) (L : ℕ)
variable {U : Type} [Fintype U] [DecidableEq U]
noncomputable local instance (L : ℕ) : Fintype (Cells L) := by
  classical
  letI : Fintype (Address L) := inferInstance
  unfold Cells
  infer_instance

noncomputable def changeBasis : Equiv.Perm (U × Cells L) :=
  (Equiv.refl U).prodCongr (Function.Involutive.toPerm (swap π k k' L) (swap_twice π k k' L))

noncomputable def cmat (i : Address L) : Matrix (U × Cells L) (U × Cells L) ℂ :=
  fun a b => if a.1 = b.1 then compressAt Rate i a.2 b.2 else 0

noncomputable def controlledRead (i : Address L) (O : Option Rate → Matrix U U ℂ) :
    Matrix (U × Cells L) (U × Cells L) ℂ := by
  exact fun a b => @ite ℂ (a.2 = b.2) (Classical.propDecidable _) (O (a.2 i) a.1 b.1) 0

noncomputable def localCall (i : Address L) (O : Option Rate → Matrix U U ℂ) :=
  cmat L i * controlledRead L i O * cmat L i

private theorem compress_conj (i : Address L) :
    Matrix.reindexAlgEquiv ℂ ℂ (changeBasis π k k' L) (cmat (U:=U) L i) =
      cmat L (dest π k k' L i) := by
  ext a b
  change (if a.1 = b.1 then compressAt Rate i (swap π k k' L a.2) (swap π k k' L b.2) else 0) = _
  rw [compressAt_swap]
  rfl

private theorem read_conj (i : Address L) (O : Option Rate → Matrix U U ℂ) :
    Matrix.reindexAlgEquiv ℂ ℂ (changeBasis π k k' L) (controlledRead L i O) =
    controlledRead L (dest π k k' L i) (fun v => O (cellMap (route π k k' L i).2 v)) := by
  classical
  ext a b
  simp only [Matrix.coe_reindexAlgEquiv,Matrix.reindex_apply,Matrix.submatrix_apply,controlledRead]
  have atBasis (v : U × Cells L) : (changeBasis π k k' L).symm v = (v.1,swap π k k' L v.2) := rfl
  simp only [atBasis,(swap_twice π k k' L).injective.eq_iff,read_swap]

theorem h_query (z : Capacity) (O : Option Rate → Matrix U U ℂ) :
    Matrix.reindexAlgEquiv ℂ ℂ (changeBasis π k k' L) (localCall L (.inl z) O) =
    localCall L (dest π k k' L (.inl z)) (fun v => O (cellMap (route π k k' L (.inl z)).2 v)) := by
  unfold localCall
  rw [map_mul,map_mul,compress_conj,read_conj]

end Reduction.ShakePermutation.Relabel
#print axioms Reduction.ShakePermutation.Relabel.h_query
