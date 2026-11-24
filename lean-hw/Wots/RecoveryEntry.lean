import Wots.Termination
import Wots.Input
import Chainwide.Prefix
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.Wots
open WotsRust.sha256.x86.avx512
open Spec.SHA256

private theorem recovery_broadcast (N : Usize) (state : Array U32 8#usize) :
    core.array.Array.map (recover.closure_1.Insts.CoreOpsFunctionFnMutTupleU32__m512i N) state ()
      ⦃ iv => ∀ i < 8, ∀ j : Fin 16, iv.val[i]! j = state.val[i]!.bv ⦄ :=
  Leaf.initial_spec N state

private theorem recovery_first_four (iv : Hash) (base : Words) :
    recover_loop4 ⟨0#usize,4#usize⟩ base iv ⦃ pre =>
      Trace pre (fun j => schedule (Leaf.blockOf (chainWords base j))) (laneState iv) 4 ⦄ := by
  have eq : recover_loop4.body base = ChainWideRust.sha256.x86.avx512.chains_loop0_loop0.body base := by
    funext it s
    simp only [recover_loop4.body,ChainWideRust.sha256.x86.avx512.chains_loop0_loop0.body,
      show WotsRust.sha256.K = ChainWideRust.sha256.K from by unfold WotsRust.sha256.K ChainWideRust.sha256.K; rfl]
    rfl
  unfold recover_loop4
  simp_rw [eq]
  exact Chain.prefix_spec iv base _ (fun k hk j => (Leaf.word_blockOf (chainWords base j) k (by omega)).symm)

/-- Initial conditions provided by the public recovery kernel itself. These include
the actual address template, broadcast SHA state and four cached rounds. -/
theorem run_recovery_entry (N : Usize) (state : Array U32 8#usize) (a : WotsRust.address.Adrs)
    (sig : Slice U8) (digits : Slice U32) (order : Order) (work : Usize) (out : Buffers)
    (size : N.val ≤ 32) (post : Buffers → Prop)
    (run : ∀ (base : Words) (iv pre : Hash),
      (∀ j, stateWords (laneState iv j) = state.val.map (·.bv)) →
      (∀ j k, k < 16 → base.val[k]! j = word (template
        { adrsS (WotsRust.addressOf a) with word2 := 0 } (List.replicate N.val 0)) (4*k)) →
      Trace pre (fun j => schedule (Leaf.blockOf (chainWords base j))) (laneState iv) 4 →
      let empty := Array.repeat 16#usize 0#i32
      let zero : Reg := fun _ => 0
      recover_loop5 N zero sig digits out order work base iv pre (fun _ => 0xffff) Store.control
        empty empty zero zero 0#u16 0#usize (Array.repeat 8#usize zero) ⦃ post ⦄) :
    runRecovery N state a sig digits order work out ⦃ post ⦄ := by
  unfold runRecovery
  simp only [WotsRust.address.Adrs.with_word2,WotsRust.address.Adrs.with_word3,lift,bind_ok]
  step with short_block_spec _ (Array.to_slice (Array.repeat N 0#u8)) (by simp; omega) as ⟨b,hb⟩
  step with recovery_words N b as ⟨base,words⟩
  step with recovery_broadcast N state as ⟨iv,broadcast⟩
  step with recovery_first_four iv base as ⟨pre,trace⟩
  simp only [_root_.core.core_arch.x86.avx512f._mm512_set1_epi32,
    _root_.core.core_arch.x86.sse2._mm_set_epi32,WotsRust.core.core_arch.x86.avx512f._mm512_broadcast_i32x4,
    GatherRust.core.core_arch.x86.avx512f._mm512_broadcast_i32x4,
    WotsRust.core.core_arch.x86.avx512f._mm512_setzero_si512,GatherRust.core.core_arch.x86.avx512f._mm512_setzero_si512,bind_tc_eq,bind_ok]
  apply run base iv pre (fun j => Leaf.initial_words _ _ broadcast j) _ trace
  intro j k hk
  rw [words k hk j,hb]
  simp [template,WotsRust.addressOf,adrsS,bytes,Array.val_to_slice,Array.repeat]

theorem recover_total (N : Usize) (state : Array U32 8#usize) (a : WotsRust.address.Adrs)
    (sig : Slice U8) (digits : Slice U32) (out : Buffers)
    (shape : N.val=16 ∨ N.val=24 ∨ N.val=32) (small : digits.length ≤ 67)
    (valid : ∀ i < digits.length, digits.val[i]!.val < 16)
    (rows : digits.length ≤ out.length) (available : N.val*digits.length ≤ sig.length) :
    recover N state a sig digits out ⦃ buf => buf.length = out.length ⦄ := by
  rw [recover_eq]
  step with preparation_spec N sig digits out (by omega) small valid rows available
    as ⟨order,work,buf,ordered,split,prepared⟩
  apply run_recovery_entry N state a sig digits order work buf (by omega)
  intro base iv pre _ _ trace
  apply WP.spec_mono (recovery_terminates N _ sig digits order work base iv pre _ buf _ _ _ _
    shape small available (prepared.1 ▸ rows) ordered valid (split.trans (workload_eq digits valid).symm) trace)
  intro final len
  exact len.trans prepared.1

end slhdsa.X86.Wots
