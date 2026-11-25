import Buffered.FullProgram
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.Buffered.Full
open Fused ShakeBatch NativeVerify NativeVerify.Wots cache.builder.nativeShake.Vector.Fused NativeShakeWots
set_option linter.concreteInstances false
set_option maxHeartbeats 2000000
variable [kernel : Fused.Kernel]
local instance : Machine := Fused.machine kernel

theorem rounds_spec {N : Usize} (p : params.Params) (hp : PN p N) (seed : Array U8 N)
    (addr : Nat → address.Adrs) (id : U32) (initial : Nat → Spec.Bytes) (sw : Array U64 4#usize)
    (w0 w1 : U64) (w2 : Array U64 8#usize) (state : Matrix 8#usize) (tag : U64)
    (header : Header seed addr sw w0 w1 w2) (tagged : tag.bv=addressLow id)
    (started : ∀ l<8, digest N state l=chainValue p seed addr id initial 0 l) (perms : Permutes kernel) :
    leaves_loop1_loop0 N ⟨0#u32,15#u32⟩ sw w0 w1 w2 state tag ⦃ out =>
      ∀ l<8, digest N out l=chainValue p seed addr id initial 15 l ⦄ := by
  unfold leaves_loop1_loop0
  apply loop.spec_decr_nat (measure := fun s : (core.ops.range.Range U32) × Matrix 8#usize => 15-s.1.start.val)
    (inv := fun s => s.1.«end».val=15 ∧ s.1.start.val≤15 ∧
      ∀ l<8, digest N s.2 l=chainValue p seed addr id initial s.1.start.val l)
  · rintro ⟨it,st⟩ ⟨last,le,prior⟩
    simp only at last le prior ⊢
    unfold leaves_loop1_loop0.body
    by_cases more : it.start.val<15
    · step with core.iter.range.IteratorRange.next_U32_some_spec it (by rw [last];exact more) as ⟨_,next,tagEq,idx,ends⟩
      simp only [tagEq,ShakeBatch.core.num.U32.swap_bytes,lift,bind_ok]
      step as ⟨hi,_,bits⟩
      try simp only [lift,bind_ok]
      let t := tag ||| hi
      have tg : t.bv=addressLow id ||| wordTag it.start := by
        change tag.bv ||| hi.bv=_
        rw [tagged]
        exact congrArg (fun x => addressLow id ||| x) bits
      obtain ⟨matrix,filled,_⟩ := spec_imp_exists (refill_layout N st sw w0 w1 w2 (Array.repeat 8#usize t) hp.le32)
      obtain ⟨newState,permuted,_⟩ := spec_imp_exists (perms matrix)
      have nextValues := next_permutation p hp seed addr id it.start initial sw w0 w1 w2 t st header tg prior perms
      change kernel.permute matrix=ok newState at permuted
      simp only [filled,bind_ok,permuted,WP.spec_ok] at nextValues
      dsimp only [t] at filled
      rw [filled]
      simp only [bind_ok,permuted,step_simps]
      exact ⟨ends ▸ last,by omega,fun l hl => idx ▸ nextValues l hl,by omega⟩
    · obtain ⟨⟨_,_⟩,no,tag,_⟩ := spec_imp_exists (core.iter.range.IteratorRange.next_U32_none_spec it (by rw [last];omega))
      simpa [no,tag,show it.start.val=15 by omega] using prior
  · exact ⟨rfl,by change 0≤15; decide,started⟩

theorem forest_spec {N : Usize} (p : params.Params) (hp : PN p N) (sk seed : Array U8 N) (a : address.Adrs)
    (base : Nat) (len n : Usize) (sw skw : Array U64 4#usize) (w0 w1 : U64) (prf hash : Array U64 8#usize)
    (pk0 : Matrix 8#usize) (pos0 : Usize) (state0 : Matrix 8#usize) (cap : len.val≤67) (width : n.val=N.val/8)
    (prfHeader : Header seed (laneAddress a address.WOTS_PRF base) sw w0 w1 prf)
    (hashHeader : Header seed (laneAddress a address.WOTS_HASH base) sw w0 w1 hash)
    (key : ∀ k<N.val/8, skw.val[k]!.bv=inputWord sk.val k) (rate : pos0.val<17)
    (ready : ∀ l<8, (ShakeBatch.lane pk0 l,8*pos0.val)=streamPrefix p sk seed a base l 0) (perms : Permutes kernel) :
    leaves_loop1 N ⟨0#usize,len⟩ n sw skw w0 w1 prf hash pk0 pos0 state0 ⦃ out =>
      out.2.val<17 ∧ ∀ l<8, (ShakeBatch.lane out.1 l,8*out.2.val)=streamPrefix p sk seed a base l len.val ⦄ := by
  unfold leaves_loop1
  apply loop.spec_decr_nat (measure := fun s : (core.ops.range.Range Usize) × Matrix 8#usize × Usize × Matrix 8#usize => len.val-s.1.start.val)
    (inv := fun s => s.1.«end»=len ∧ s.1.start.val≤len.val ∧ s.2.2.1.val<17 ∧
      ∀ l<8, (ShakeBatch.lane s.2.1 l,8*s.2.2.1.val)=streamPrefix p sk seed a base l s.1.start.val)
  · rintro ⟨it,pk,pos,state⟩ ⟨last,le,rated,streamed⟩
    simp only at last le rated streamed ⊢
    unfold leaves_loop1.body
    by_cases more : it.start.val<len.val
    · step with core.iter.range.IteratorRange.next_Usize_some_spec it (by simpa only [last] using more) as ⟨_,next,tagEq,idx,ends⟩
      let id := UScalar.cast .U32 it.start
      have iv : id.val=it.start.val := by dsimp only [id]; scalar_tac
      let prfVal := seedValue p sk seed a base id
      simp only [tagEq,ShakeBatch.core.num.U32.swap_bytes,lift,bind_ok]
      let swapped : U32 := ⟨id.bv.extractLsb' 0 8 ++ id.bv.extractLsb' 8 8 ++ id.bv.extractLsb' 16 8 ++ id.bv.extractLsb' 24 8⟩
      let word := core.convert.num.FromU64U32.from swapped
      have wtag : word.bv=addressLow id := rfl
      obtain ⟨prepared,filled,_⟩ := spec_imp_exists (fill_layout N state sw skw w0 w1 prf (Array.repeat 8#usize word) hp.le32)
      obtain ⟨start,permuted,_⟩ := spec_imp_exists (perms prepared)
      change kernel.permute prepared=ok start at permuted
      have p0 := initial_permutation p hp sk seed (laneAddress a address.WOTS_PRF base) id sw skw w0 w1 prf word state prfHeader key wtag perms
      simp only [filled,bind_ok,permuted,WP.spec_ok] at p0
      dsimp only [word,swapped,id] at filled
      rw [filled]
      have init (l : Nat) (hl : l<8) : digest N start l=chainValue p seed (laneAddress a address.WOTS_HASH base) id prfVal 0 l := p0 l hl
      have maximum : params.W - 1#u32=ok 15#u32 := by rw [W_eq];rfl
      simp only [bind_ok,permuted,maximum]
      step with rounds_spec p hp seed (laneAddress a address.WOTS_HASH base) id prfVal sw w0 w1 hash start
        word hashHeader wtag init perms as ⟨final,done⟩
      have row (l : Nat) (hl : l<8) : digest N final l=tip p sk seed a base l it.start.val := by
        rw [done l hl,←iv]
        exact tip_value p sk seed a base l id
      have absorber := Fused.Stream.absorb_digest N n pk pos final rated width (by have := hp.le32;omega) (aligned_hash hp) perms
        (fun l => tip p sk seed a base l it.start.val) row
      have same : leaves_loop1_loop1 ⟨0#usize,n⟩ pk pos final = xmss_sign_batch_loop2_loop1 8#usize ⟨0#usize,n⟩ pk pos final := by
        unfold leaves_loop1_loop1 xmss_sign_batch_loop2_loop1
        congr 1
        funext q
        rcases q with ⟨it,s,i⟩
        simp only [leaves_loop1_loop1.body,xmss_sign_batch_loop2_loop1.body,bind_ok]
        rfl
      rw [same]
      step with absorber as ⟨newPk,newPos,newRate,feed⟩
      refine ⟨ends.trans last,by omega,newRate,?_,by omega⟩
      intro l hl
      rw [feed l hl,streamed l hl,idx]
      simp [streamPrefix,List.range_succ,List.foldl_append,List.append_assoc]
    · obtain ⟨⟨_,_⟩,no,tag,_⟩ := spec_imp_exists (core.iter.range.IteratorRange.next_Usize_none_spec it (by rw [last];omega))
      simp [no,tag,show it.start.val=len.val by omega] at streamed ⊢
      exact ⟨rated,streamed⟩
  · exact ⟨rfl,by simp,rate,ready⟩

end slhdsa.Buffered.Full
