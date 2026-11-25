import Buffered.SmallWotsInit
import Buffered.SmallWotsFinish
import Buffered.SmallForest
open Aeneas Aeneas.Std Result
namespace slhdsa.Buffered.SmallWots
open ShakeBatch NativeVerify
set_option maxHeartbeats 1500000
set_option linter.concreteInstances false
variable [kernel : Fused.Kernel]
local instance entryMachine : Machine := Fused.machine kernel

private def grouped {N : Usize} (K : Usize) (sk seed : Array U8 N) (first : U32) (a : address.Adrs) := do
  let twice ← 2#usize * N
  let len ← twice + params.LEN2
  let total ← K * len
  let n ← N / 8#usize
  let off ← n + 4#usize
  let sw ← seed_words seed
  let skw ← seed_words sk
  let aw ← adrs_words a
  let w0 ← Array.index_usize aw 0#usize
  let w1 ← Array.index_usize aw 1#usize
  let pk ← init K first n sw w0 w1
  let (acc,pos) ← leaves_loop2 N K first total n sw skw w0 w1 pk off
    (Array.repeat 25#usize (Array.repeat 8#usize 0#u64)) 0#usize
  finish N K acc pos

theorem raw_eq {N : Usize} (K : Usize) (sk seed : Array U8 N) (first : U32) (a : address.Adrs) :
    leaves K sk seed first a=grouped K sk seed first a := by
  simp only [leaves,grouped,init,front,finish,bind_tc_eq,Std.bind_assoc,bind_ok]
  rfl

theorem leaves_spec {N : Usize} (p : params.Params) (hp : PN p N) (sk seed : Array U8 N)
    (a : address.Adrs) (K : Usize) (first : U32) (width : K.val=2 ∨ K.val=4)
    (room : first.val+K.val≤512) (active : ActiveCorrect (Fused.machine kernel) kernel.active) :
    leaves K sk seed first a ⦃ rows => LeafRows p sk seed a first.val rows ⦄ := by
  rw [raw_eq]
  unfold grouped
  have small := hp.le32
  step as ⟨twice,tw⟩
  simp only [LEN2_eq]
  step as ⟨len,lenEq⟩
  have length : len.val=(Shake.params p).len := by change len.val=(paramsS p).len; rw [hp.len]; omega
  have cap : K.val*len.val≤512 := by rcases width with h|h <;> rw [h] <;> omega
  step as ⟨total,slots⟩
  step as ⟨n,nval⟩
  step as ⟨off,pos⟩
  step with seed_spec seed small as ⟨sw,words⟩
  step with seed_spec sk small as ⟨skw,secret⟩
  step with address_spec a as ⟨aw,addr⟩
  step as ⟨w0,rd0⟩
  step as ⟨w1,rd1⟩
  have lo : w0.bv=addressWord a 0 := by rw [rd0,←getElem!_pos]; exact addr 0 (by decide)
  have hi : w1.bv=addressWord a 1 := by rw [rd1,←getElem!_pos]; exact addr 1 (by decide)
  have seedWords (k : Nat) (hk : k<N.val/8) : sw.val[k]!.bv=inputWord seed.val k := by
    simpa only [hk,ite_true] using words k (by omega)
  have secretWords (k : Nat) (hk : k<N.val/8) : skw.val[k]!.bv=inputWord sk.val k := by
    simpa only [hk,ite_true] using secret k (by omega)
  step with init_keys p hp seed a first K n off sw w0 w1 (by omega) room nval pos
    (fun k hk => seedWords k (by omega)) lo hi as ⟨pk,initial⟩
  obtain ⟨⟨acc,cursor⟩,ran,rate,streams⟩ := spec_imp_exists (forest p hp sk seed a first K total n sw skw w0 w1 pk off _ width (by rw [slots,length])
    (by omega) room nval (by omega) seedWords secretWords lo hi active (fun l hl => by
      simpa only [Fused.streamPrefix,List.range_zero,List.flatMap_nil,List.append_nil] using initial l hl))
  rw [ran]
  simp only [bind_tc_eq,bind_ok]
  exact finish_keys p hp sk seed a first K acc cursor (by omega) room rate active streams

end slhdsa.Buffered.SmallWots
