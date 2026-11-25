import Buffered.SmallChains
import Buffered.SmallWotsGroups
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.Buffered.SmallWots
open ShakeBatch NativeVerify NativeVerify.Wots NativeShakeWots cache.builder.nativeShake.Vector.Fused
set_option linter.concreteInstances false
set_option maxHeartbeats 1800000
variable [kernel : Fused.Kernel]
local instance shortForestMachine : Machine := Fused.machine kernel

private theorem batchBind {α} (N K idx active : Usize) (first : U32)
    (sw skw : Array U64 4#usize) (w0 w1 : U64) (state : Matrix 8#usize)
    (tag : Array U64 8#usize) (f : Matrix 8#usize → Result α) :
    (batch (N:=N) K idx active first sw skw w0 w1 state tag tag tag >>= f) = (do
      let (prf,hash,ids) ← leaves_loop2_loop0 K ⟨0#usize,active⟩ first idx tag tag tag
      let packed ← fill_prf N state sw skw w0 w1 prf ids
      let start ← kernel.active packed active
      let steps ← params.W - 1#u32
      let out ← leaves_loop2_loop1 N K ⟨0#u32,steps⟩ sw w0 w1 start active hash ids
      f out) := by
  simp only [batch,bind_tc_eq,Std.bind_assoc]
  rfl

private theorem geometry (K idx count active : Nat) (width : K=2 ∨ K=4) (aligned : idx%K=0)
    (remaining : idx<K*count) (selected : active=min (K*count-idx) 8) :
    0<active ∧ active≤8 ∧ idx+active≤K*count ∧ (idx+active)%K=0 ∧ active=K*(active/K) ∧
    (idx+active)/K=idx/K+active/K ∧
    (∀ t<active/K, ∀ l<K, K*t+l<active ∧ (idx+(K*t+l))%K=l ∧ (idx+(K*t+l))/K=idx/K+t) := by
  rcases width with rfl|rfl <;> simp only [Nat.mul_comm 2, Nat.mul_comm 4] at * <;>
    refine ⟨by omega,by omega,by omega,by omega,by omega,by omega,?_⟩ <;> intro t ht l hl <;> omega

theorem forest {N : Usize} (p : params.Params) (hp : PN p N) (sk seed : Array U8 N) (a : address.Adrs)
    (first : U32) (K total n : Usize) (sw skw : Array U64 4#usize) (w0 w1 : U64)
    (pk : Matrix 8#usize) (pos : Usize) (state : Matrix 8#usize)
    (width : K.val=2 ∨ K.val=4) (slots : total.val=K.val*(Shake.params p).len)
    (cap : total.val≤512) (fit : first.val+K.val≤512) (size : n.val=N.val/8) (rate : pos.val<17)
    (seedOk : ∀ k<N.val/8, sw.val[k]!.bv=inputWord seed.val k)
    (keyOk : ∀ k<N.val/8, skw.val[k]!.bv=inputWord sk.val k)
    (lo : w0.bv=addressWord a 0) (hi : w1.bv=addressWord a 1)
    (perm : ActiveCorrect (Fused.machine kernel) kernel.active)
    (prior : ∀ l<K.val, (ShakeBatch.lane pk l,8*pos.val)=Fused.streamPrefix p sk seed a first.val l 0) :
    leaves_loop2 N K first total n sw skw w0 w1 pk pos state 0#usize ⦃ out =>
      out.2.val<17 ∧ ∀ l<K.val, (ShakeBatch.lane out.1 l,8*out.2.val)=Fused.streamPrefix p sk seed a first.val l (Shake.params p).len ⦄ := by
  have positive : 0<K.val := by omega
  unfold leaves_loop2
  apply loop.spec_decr_nat (measure := fun q : Matrix 8#usize × Usize × Matrix 8#usize × Usize => total.val-q.2.2.2.val)
    (inv := fun q => q.2.2.2.val≤total.val ∧ q.2.2.2.val%K.val=0 ∧ q.2.1.val<17 ∧
      ∀ l<K.val, (ShakeBatch.lane q.1 l,8*q.2.1.val)=Fused.streamPrefix p sk seed a first.val l (q.2.2.2.val/K.val))
  · rintro ⟨acc,ptr,st,idx⟩ ⟨bounded,aligned,rated,streams⟩
    simp only at bounded aligned rated streams ⊢
    unfold leaves_loop2.body
    split
    · rename_i more
      have moreN : idx.val<total.val := more
      step as ⟨left,remaining⟩
      simp only [lift,bind_ok]
      let active := core.cmp.impls.OrdUsize.min left 8#usize
      have count : active.val=min (total.val-idx.val) 8 := by
        change (if 8#usize < left then 8#usize else left).val=_
        rw [←remaining]
        split <;> rename_i test
        · exact (min_eq_right (Nat.le_of_lt test)).symm
        · exact (min_eq_left (Nat.le_of_not_gt test)).symm
      obtain ⟨nonzero,lanes,room,mod0,div,advance,coordinates⟩ := geometry K.val idx.val (Shake.params p).len active.val width aligned (slots ▸ moreN) (slots ▸ count)
      erw [←batchBind N K idx active first sw skw w0 w1 st (Array.repeat 8#usize 0#u64)]
      step with batch_tips p hp sk seed a first K idx active sw skw w0 w1 st _ _ _ positive (by omega)
        (by omega) (by omega) lanes seedOk keyOk lo hi perm as ⟨out,computed⟩
      step as ⟨it,iter,stepSize⟩
      have same : it=⟨⟨0#usize,active⟩,K⟩ := by
        cases it with | mk rng stride => exact congrArg₂ _ iter stepSize
      rw [same]
      step with groups p hp sk seed a first K n active acc ptr out (idx.val/K.val) (active.val/K.val) positive
        (by omega) div lanes size rated perm streams (by
          intro t ht l hl
          obtain ⟨inside,key,id⟩ := coordinates t ht l hl
          rw [computed _ inside,key,id]) as ⟨acc',ptr',rate',updated⟩
      step as ⟨next,inc⟩
      change next.val=idx.val+active.val at inc
      rw [←slots] at room
      have idxDone : next.val/K.val=idx.val/K.val+active.val/K.val := by rw [inc,advance]
      exact ⟨by omega,inc ▸ mod0,rate',idxDone ▸ updated,by omega⟩
    · rename_i stop
      simp only [step_simps]
      have equal : idx.val=total.val := by change ¬ idx.val<total.val at stop;omega
      have done : idx.val/K.val=(Shake.params p).len := by rw [equal,slots,Nat.mul_div_cancel_left _ positive]
      exact ⟨rated,done ▸ streams⟩
  · exact ⟨Nat.zero_le _,Nat.zero_mod _,rate,by simpa only [show (0#usize).val=0 from rfl,Nat.zero_div] using prior⟩
end slhdsa.Buffered.SmallWots
