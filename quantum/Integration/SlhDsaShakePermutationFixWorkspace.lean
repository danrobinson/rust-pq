import Integration.SlhDsaShakePermutationFixAccess
import QuantumFoundations.SubInstrument.Relabel

namespace Reduction.ShakePermutation.Fix.Workspace
open Matrix Quantum PQ.Interactive Classical
open scoped Kronecker ComplexOrder
variable {X Y U : Type} {T : ℕ} [Fintype X] [Fintype Y] [Fintype U]
  [DecidableEq X] [DecidableEq Y] [DecidableEq U] [AddCommGroup Y]
abbrev Aux (X Y : Type) (T : ℕ) := (X × Y) × Access.Data T
abbrev W (X Y : Type) (T : ℕ) (U : Type) := Register X Y (Access.Scratch T U)

def pack : U × Aux X Y T ≃ W X Y T U where
  toFun p := (p.2.1,(p.2.2,p.1))
  invFun w := (w.2.2,(w.1,w.2.1))
  left_inv _ := rfl
  right_inv _ := rfl

def blank (base : X) : Aux X Y T := ((base,0),(Access.zeroPath,0))

noncomputable def liftIdx (j : InstrIdx U) : InstrIdx (W X Y T U) :=
  ⟨j.1,(j.2.1.frame (Aux X Y T)).reindex pack pack,
    (j.2.2.frame (Aux X Y T)).reindex pack pack⟩

private theorem append_matrix {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (b : B) (M : Matrix A A ℂ) :
    MatrixMap.conj (basisMatrix (fun a : A => (a,b))) M = M ⊗ₖ Matrix.single b b 1 := by
  ext ⟨i,j⟩ ⟨k,l⟩
  by_cases hj : j = b <;> by_cases hl : l = b <;>
    simp [MatrixMap.conj_apply,Matrix.mul_apply,basisMatrix_apply,Prod.mk.injEq,
      Matrix.single_apply,kroneckerMap_apply,hj,hl,eq_comm] <;> grind

def embed (base : X) (u : U) : WS X Y (Access.Scratch T U) := (((base,0),Access.scratch u),())

noncomputable def state (base : X) (M : Matrix U U ℂ) : Matrix (WS X Y (Access.Scratch T U)) (WS X Y (Access.Scratch T U)) ℂ :=
  MatrixMap.conj (basisMatrix (embed base)) M

theorem state_form (base : X) (M : Matrix U U ℂ) :
    state (T := T) (Y := Y) base M =
      ((M ⊗ₖ Matrix.single (blank (T := T) (Y := Y) base) (blank base) 1).submatrix
        (pack (U := U)).symm pack.symm) ⊗ₖ Matrix.single () () 1 := by
  let ins := fun u : U => (u,blank (T := T) (Y := Y) base)
  let unit := fun w : W X Y T U => (w,())
  change MatrixMap.conj (basisMatrix (unit ∘ pack ∘ ins)) M = _
  rw [basisMatrix_comp,MatrixMap.conj_mul,LinearMap.comp_apply,append_matrix,
    basisMatrix_comp,MatrixMap.conj_mul,LinearMap.comp_apply,conj_basisMatrix_equiv,append_matrix]

theorem lift_branch (base : X) (j : InstrIdx U) (i : Fin (j.1+1)) (M : Matrix U U ℂ) :
    (framedIdx (liftIdx (X := X) (Y := Y) (T := T) j)).2.1.branch i (state base M) =
      state base (j.2.1.branch i M) := by
  rw [state_form,state_form]
  change (((j.2.1.frame _).reindex pack pack).frame Unit).branch i _ = _
  rw [DSubInstrument.branch_frame_apply,MatrixMap.amplify_kronecker,SubInstrument.branch_reindex_apply]
  simp only [Matrix.submatrix_submatrix,Equiv.symm_comp_self,Matrix.submatrix_id_id,
    DSubInstrument.branch_frame_apply,MatrixMap.amplify_kronecker]

omit [DecidableEq U] in
theorem embed_injective (base : X) : Function.Injective (embed (Y := Y) (T := T) (U := U) base) :=
  fun _ _ h => congrArg (fun w => w.1.2.2) h

theorem state_trace (base : X) (M : Matrix U U ℂ) : (state (Y := Y) (T := T) base M).trace = M.trace := by
  unfold state
  rw [MatrixMap.conj_apply,Matrix.trace_mul_cycle,conjTranspose_basisMatrix_mul_self (embed_injective _),
    Matrix.one_mul]

theorem state_pos (base : X) (M : Matrix U U ℂ) (hm : M.PosSemidef) :
    (state (Y := Y) (T := T) base M).PosSemidef :=
  (MatrixMap.isCP_conj _).posSemidef hm

end Reduction.ShakePermutation.Fix.Workspace
#print axioms Reduction.ShakePermutation.Fix.Workspace.lift_branch
