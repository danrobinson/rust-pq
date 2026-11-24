import Kdiag.Funs
import Keccakasm.Proof
open Aeneas Aeneas.Std Result
namespace slhdsa.Kdiag
open KdiagRust.shake256.stream_x86
abbrev Reg := KdiagRust.core.core_arch.x86.__m512i
abbrev Grid := Array Reg 5#usize
def col (base stride i : Nat) : Fin 8 := ⟨(base+i*stride)%5,by omega⟩

theorem index_spec (base stride : Usize) (hb : base.val < 5) (hs : stride.val < 5) :
    indices base stride ⦃ v => ∀ i : Fin 8, (v i).toNat = (col base.val stride.val i.val).val ⦄ := by
  unfold indices
  have build := core.array.from_fn.spec_stateless_getElem! 8#usize
    (indices.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64 base stride) ()
    (fun n (w : U64) => w.val=(col base.val stride.val n).val) (by
      intro n hn
      unfold indices.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64
      simp only [indices.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut, bind_tc_eq]
      step as ⟨off,ho⟩
      all_goals try scalar_tac
      step as ⟨ix,hi⟩
      all_goals try scalar_tac
      step as ⟨ix',hr⟩
      simp [lift,col,UScalar.cast_val_eq,hr,hi,ho] <;> omega)
  apply WP.spec_bind build
  intro a h
  simp only [KdiagRust.core.intrinsics.transmute,step_simps]
  intro i
  simpa [Array.getElem!_Nat_eq] using h i.val i.isLt

theorem move_spec (b s : Usize) (hb : b.val<5) (hs : s.val<5) (x : Reg) :
    move_lanes b s x ⦃ r => ∀ j, r j = x (col b.val s.val j.val) ⦄ := by
  unfold move_lanes
  apply WP.spec_bind (index_spec b s hb hs)
  intro idx h
  simp only [KdiagRust.core.core_arch.x86.avx512f._mm512_permutexvar_epi64,step_simps]
  intro j
  congr 1
  apply Fin.ext
  change (idx j).toNat%8 = _
  rw [h,Nat.mod_eq_of_lt (col _ _ _).isLt]
end slhdsa.Kdiag
