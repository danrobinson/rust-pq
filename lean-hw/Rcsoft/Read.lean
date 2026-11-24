import Rcsoft.Funs
import Streamround.Read
import Slhdsa.Proofs.Sha512Core
open Aeneas Aeneas.Std Result
namespace slhdsa.RcSoftProof
open Spec.SHA512 RcSoft

theorem constants_eq : RcSoft.consts.K64 = slhdsa.sha512.K := by
  unfold RcSoft.consts.K64 slhdsa.sha512.K
  rfl

theorem volatile_read (i : Usize) :
    RcSoft.sha512.soft.unroll.rk i = Array.index_usize RcSoft.consts.K64 i := by
  rw [constants_eq]
  rfl

theorem constant_spec (i : Usize) (hi : i.val < 80) :
    RcSoft.sha512.soft.unroll.rk i ⦃ w => w.bv = K[i.val]! ⦄ := by
  rw [volatile_read, constants_eq]
  step
  rw [← S512.K_eq, S512.wv_getElem!]
  all_goals first | scalar_tac | simp_all

theorem read_word (block : Array U8 128#usize) (j : Usize) (hi : j.val < 16) :
    RcSoft.sha512.soft.to_u64s.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut block j
      ⦃ w c => w.bv = (schedule (bytes block.val))[j.val]! ∧ c = block ⦄ := by
  unfold RcSoft.sha512.soft.to_u64s.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
  step*
  · change 8 ≤ s.length
    have : block.to_slice.length = 128 := by simp
    omega
  · cases r with
    | Ok a => exact ⟨a,rfl⟩
    | Err e => cases e; simp only at r_post; omega
  · have converted : i1.bv = (core.num.U64.from_be_bytes chunk).bv := i1_post
    rw [converted]
    apply X86.Stream.load512 block j.val hi chunk
    subst r
    simp_all [Array.val_to_slice, List.slice]

theorem words_spec (block : Array U8 128#usize) :
    RcSoft.sha512.soft.to_u64s block ⦃ r =>
      ∀ j < 16, (r.val[j]!).bv = (schedule (bytes block.val))[j]! ⦄ := by
  unfold RcSoft.sha512.soft.to_u64s
  simpa only [Array.getElem!_Nat_eq, show (16#usize).val = 16 by rfl] using
    (core.array.from_fn.spec_stateless_getElem! 16#usize
      RcSoft.sha512.soft.to_u64s.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64 block
      (fun j (v : U64) => v.bv = (schedule (bytes block.val))[j]!)
      (fun i hi => read_word block i hi))
end slhdsa.RcSoftProof
