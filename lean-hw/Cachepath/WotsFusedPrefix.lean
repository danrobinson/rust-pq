import Cachepath.WotsFusedStream
import Shakebatch.Short

open Aeneas Aeneas.Std Result slhdsa.ShakeBatch
namespace slhdsa.cache.builder.nativeShake.Vector.Fused
open Spec.Keccak
set_option linter.concreteInstances false
set_option maxHeartbeats 1500000
variable [machine : Machine]

private theorem zero_row (s : Matrix machine.width) (index : Usize) (k j : Nat)
    (inside : index.val < 25) (valid : j<machine.width.val) :
    cell (s.set index (Array.repeat machine.width 0#u64)) k j =
      if k=index.val then 0 else cell s k j := by
  by_cases same : k=index.val
  · subst k; rw [cell,Array.set_val_eq,setSame _ _ _ (by simpa using inside),Array.repeat_val]
    simp [valid]
  · simp only [cell,Array.set_val_eq,setOther _ _ _ _ (Ne.symm same),same,ite_false]

/-- For a streamed public key hash the two zero stores remove both single-block padding words. -/
theorem init_pk (seed : Array U8 N) (addresses : Array address.Adrs machine.width)
    (size offset : Usize) (sizeEq : size.val=N.val+32) (off : offset.val=N.val/8+4)
    (small : N.val ≤ 32) (aligned : N.val%8=0) :
    (do let pk ← ShakeBatch.shake.batch.header seed addresses size
        let pk ← Array.update pk offset (Array.repeat machine.width 0#u64)
        Array.update pk 16#usize (Array.repeat machine.width 0#u64)) ⦃ out =>
      ∀ l < machine.width.val, (ShakeBatch.lane out l,8*offset.val) =
        (bytes seed.val ++ (adrsS addresses.val[l]!).bytes).foldl feed initial ⦄ := by
  step with header_spec seed addresses size small (by omega) as ⟨header,hs⟩
  step as ⟨first,save⟩
  step as ⟨out,final⟩
  rename_i l hl
  let msg := bytes seed.val ++ (adrsS addresses.val[l]!).bytes
  have len : msg.length = 8*offset.val := by simp [msg,address_length]; omega
  have exactPrefix := aligned_prefix msg offset.val (by omega) (by omega)
  rw [← len,List.take_length] at exactPrefix
  refine Eq.trans ?_ exactPrefix.symm
  apply Prod.ext _ len.symm
  change ShakeBatch.lane out l = prefixState msg offset.val
  apply ext25 _ _ (by simp [ShakeBatch.lane]) (by simp [prefixState])
  intro k hk
  rw [show (ShakeBatch.lane out l)[k]! = _ from ofFnAt _ k hk,final,zero_row _ _ _ _ (by decide) hl,
    save,zero_row _ _ _ _ (by omega) hl,hs k hk l hl]
  have size8 : (bytes seed.val).length = 8*(N.val/8) := by simp; omega
  simp only [prefixState,ofFnAt _ k hk,msg,messageWord_append _ _ _ _ size8,initialWord,
    inputWord_eq,addressWord_eq,show (16#usize).val=16 by rfl]
  have index : size.val/8=offset.val := by omega
  rw [index,off]
  split_ifs <;> first | rfl | omega

end slhdsa.cache.builder.nativeShake.Vector.Fused
