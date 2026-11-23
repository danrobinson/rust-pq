import Rcsoft256.Funs
import Streamround.Read
import Slhdsa.Proofs.Sha256Core
open Aeneas Aeneas.Std Result
namespace slhdsa.RcSoft256Proof
open Spec.SHA256 RcSoft256

theorem constants_eq : RcSoft256.consts.K32 = slhdsa.sha256.K := by
  unfold RcSoft256.consts.K32 slhdsa.sha256.K
  rfl

theorem volatile_read (i : Usize) :
    RcSoft256.sha256.soft.unroll.rk i = Array.index_usize RcSoft256.consts.K32 i := by
  rw [constants_eq]
  rfl

theorem constant_spec (i : Usize) (hi : i.val < 64) :
    RcSoft256.sha256.soft.unroll.rk i ⦃ w => w.bv = K[i.val]! ⦄ := by
  rw [volatile_read, constants_eq]
  step
  rw [← slhdsa.K_eq, slhdsa.wv_getElem!]
  all_goals first | scalar_tac | simp_all

theorem read_word (block : Array U8 64#usize) (j : Usize) (hi : j.val < 16) :
    RcSoft256.sha256.soft.to_u32s.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut block j
      ⦃ w c => w.bv = (schedule (bytes block.val))[j.val]! ∧ c = block ⦄ := by
  unfold RcSoft256.sha256.soft.to_u32s.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut
  step*
  · change 4 ≤ s.length
    have : block.to_slice.length = 64 := by simp
    omega
  · cases r with
    | Ok a => exact ⟨a,rfl⟩
    | Err e => cases e; simp only at r_post; omega
  · have converted : i1.bv = (core.num.U32.from_be_bytes chunk).bv := i1_post
    rw [converted]
    apply X86.Stream.load256 block j.val hi chunk
    subst r
    simp_all [Array.val_to_slice, List.slice]

theorem words_spec (block : Array U8 64#usize) :
    RcSoft256.sha256.soft.to_u32s block ⦃ r =>
      ∀ j < 16, (r.val[j]!).bv = (schedule (bytes block.val))[j]! ⦄ := by
  unfold RcSoft256.sha256.soft.to_u32s
  simpa only [Array.getElem!_Nat_eq, show (16#usize).val = 16 by rfl] using
    (core.array.from_fn.spec_stateless_getElem! 16#usize
      RcSoft256.sha256.soft.to_u32s.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32 block
      (fun j (v : U32) => v.bv = (schedule (bytes block.val))[j]!)
      (fun i hi => read_word block i hi))
end slhdsa.RcSoft256Proof
