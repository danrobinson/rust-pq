import Wots.Retire
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.Wots
open WotsRust.sha256.x86.avx512
open WotsRust.core.core_arch.x86.avx512f
open _root_.core.core_arch.x86.avx512f

def stageAll (N : Usize) (h : Hash) := do
  let initial := Array.repeat 16#usize (Array.repeat N 0#u8)
  let (dst,back) ← lift (Array.to_slice_mut initial)
  let written ← WotsRust.sha256.x86.avx512.write_words h dst
  ok (back written)

theorem stage_all_spec (N : Usize) (h : Hash) (shape : N.val=16 ∨ N.val=24 ∨ N.val=32) :
    stageAll N h ⦃ a => ∀ j : Fin 16, ∀ k < N.val, (a.val[j.val]!.val[k]!).bv = Store.digestByte h j k ⦄ := by
  unfold stageAll
  simp only [lift,Array.to_slice_mut,bind_tc_eq,bind_ok]
  step with Store.write_words_spec h (Array.to_slice (Array.repeat 16#usize (Array.repeat N 0#u8))) shape (by simp) as ⟨w,len,words⟩
  have size : w.val.length = (16#usize).val := by simpa [Slice.length,Array.val_to_slice] using len
  simp only [Array.from_slice_val _ _ size]
  intro j k hk
  exact words j (by simp) k hk

def finishRound {N : Usize} (counter : Reg) (active : U16) (hash : Hash) (out : Buffers) (indices : LaneArray) := do
  let one ← _mm512_set1_epi32 1#i32
  let next ← _mm512_add_epi32 counter one
  let endAt ← _mm512_set1_epi32 15#i32
  let eq ← _mm512_cmpeq_epi32_mask next endAt
  let finished := active &&& eq
  if finished != 0#u16 then
    let staged ← stageAll N hash
    let buf ← recover_loop5_loop3 out indices staged finished
    ok (next,active &&& (~~~finished),buf)
  else ok (next,active,out)

def finishes (active : U16) (counter : Reg) (j : Fin 16) :=
  enabled active j = true ∧ counter j + 1 = 15

theorem finish_spec {N : Usize} (counter : Reg) (active : U16) (hash : Hash) (out : Buffers) (indices : LaneArray)
    (shape : N.val=16 ∨ N.val=24 ∨ N.val=32)
    (valid : ∀ j, finishes active counter j → outputKey indices j < out.length)
    (unique : ∀ i j, finishes active counter i → finishes active counter j →
      outputKey indices i = outputKey indices j → i=j) :
    finishRound (N := N) counter active hash out indices ⦃ next mask buf =>
      (∀ j, next j = counter j+1) ∧
      (∀ j, enabled mask j = true ↔ enabled active j = true ∧ next j ≠ 15) ∧
      ∃ staged : Staged N, retired indices staged out buf (finishes active counter) ∧
        ∀ j, finishes active counter j → ∀ k < N.val, (staged.val[j.val]!.val[k]!).bv = Store.digestByte hash j k ⦄ := by
  let eq := ChainWideRust.core.core_arch.x86.avx512f.laneMask (fun j => counter j+1 == 15)
  let finished := active &&& eq
  have matchBit (j) : enabled finished j = true ↔ finishes active counter j := by
    change (active.bv &&& eq.bv).getLsbD j.val = true ↔ _
    simp only [BitVec.getLsbD_and,eq,Chain.lane_mask,Bool.and_eq_true,beq_iff_eq,finishes,enabled]
  have remain (j : Fin 16) : enabled (active &&& ~~~finished) j = true ↔
      enabled active j = true ∧ counter j+1 ≠ 15 := by
    change (active.bv &&& (show BitVec 16 from ~~~finished.bv)).getLsbD j.val = true ↔ _
    simp only [BitVec.getLsbD_and,BitVec.getLsbD_not,j.isLt,decide_true,Bool.true_and,Bool.and_eq_true,Bool.not_eq_true']
    change (enabled active j = true ∧ enabled finished j = false) ↔ _
    rw [Bool.eq_false_iff]; have h := matchBit j; unfold finishes at h; tauto
  unfold finishRound
  simp only [_mm512_set1_epi32,_mm512_add_epi32,_mm512_cmpeq_epi32_mask,
    ChainWideRust.core.core_arch.x86.avx512f._mm512_cmpeq_epi32_mask,bind_tc_eq,bind_ok]
  simp only [show (1#i32).bv = (1 : BitVec 32) by rfl,show (15#i32).bv = (15 : BitVec 32) by rfl]
  change (if finished != 0#u16 then _ else _) ⦃ _ ⦄
  by_cases nz : finished ≠ 0#u16
  · rw [if_pos (bne_iff_ne.mpr nz)]
    step with stage_all_spec N hash shape as ⟨staged,bytes⟩
    step with retire_spec out indices staged finished (by omega) (fun j h => valid _ ((matchBit j).mp h))
      (fun i j a b => unique i j ((matchBit i).mp a) ((matchBit j).mp b)) as ⟨buf,wrote⟩
    refine ⟨fun _ => True.intro,remain,staged,?_,fun j _ => bytes j⟩
    have eqPred : (fun j => enabled finished j=true) = finishes active counter := funext fun j => propext (matchBit j)
    rwa [eqPred] at wrote
  · have zero : finished = 0#u16 := Classical.not_not.mp nz
    have none (j) : ¬ finishes active counter j := by rw [← matchBit,zero]; simp [enabled]
    rw [if_neg (fun h => nz (bne_iff_ne.mp h))]
    simp only [step_simps]
    refine ⟨fun _ => True.intro,fun j => ?_,Array.repeat 16#usize (Array.repeat N 0#u8),?_,fun j h => (none j h).elim⟩
    · have := none j; unfold finishes at this; change _ ↔ enabled active j = true ∧ counter j+1 ≠ 15; tauto
    · simp [retired,none]

end slhdsa.X86.Wots
