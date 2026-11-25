import Fused.Written
import Fused.StreamPrefix
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.Fused
open ShakeBatch NativeVerify NativeVerify.Wots NativeShakeWots NativeShakeWots.Signer cache.builder.nativeShake.Vector.Fused
set_option linter.concreteInstances false
set_option maxHeartbeats 1500000
variable [kernel : Kernel]
local instance forestMachine : Machine := machine kernel

def seedValue {N : Usize} (p : params.Params) (sk seed : Array U8 N) (a : address.Adrs) (base : Nat) (id : U32) (l : Nat) :=
  Spec.PRF (Shake.params p) (bytes seed.val) (bytes sk.val) {adrsS (laneAddress a address.WOTS_PRF base l) with word2:=id.val,word3:=0}

def tip {N : Usize} (p : params.Params) (sk seed : Array U8 N) (a : address.Adrs) (base l : Nat) :=
  pkGenStep (Shake.params p) (bytes sk.val) (bytes seed.val) (adrsS (laneAddress a address.WOTS_HASH base l))

def streamPrefix {N : Usize} (p : params.Params) (sk seed : Array U8 N) (a : address.Adrs) (base l n : Nat) :=
  ((bytes seed.val ++ (Spec.wotsPkAdrs (adrsS (laneAddress a address.WOTS_HASH base l))).bytes) ++
    (List.range n).flatMap (tip p sk seed a base l)).foldl Spec.Keccak.feed Spec.Keccak.initial

theorem tip_value {N : Usize} (p : params.Params) (sk seed : Array U8 N) (a : address.Adrs) (base l : Nat) (id : U32) :
    chainValue p seed (laneAddress a address.WOTS_HASH base) id (seedValue p sk seed a base id) 15 l =
    tip p sk seed a base l id.val := by
  simp only [chainValue,seedValue,tip,pkGenStep,signedChain,adrsS,laneAddress,Spec.wotsSkAdrs,Spec.Adrs.setTypeAndClear,
    address.WOTS_PRF,Spec.WOTS_PRF,show (5#u32).val=5 from rfl,show (0#u32).val=0 from rfl,show (Shake.params p).w - 1 = 15 from rfl]

theorem signed_value {N : Usize} (p : params.Params) (sk seed : Array U8 N) (a : address.Adrs) (base l : Nat)
    (id : U32) (digits : List U32) :
    chainValue p seed (laneAddress a address.WOTS_HASH base) id (seedValue p sk seed a base id) digits[id.val]!.val l =
    signedChain p sk seed (laneAddress a address.WOTS_HASH base l) digits id.val := by
  simp only [chainValue,seedValue,tip,pkGenStep,signedChain,adrsS,laneAddress,Spec.wotsSkAdrs,Spec.Adrs.setTypeAndClear,
    address.WOTS_PRF,Spec.WOTS_PRF,show (5#u32).val=5 from rfl,show (0#u32).val=0 from rfl,show (Shake.params p).w - 1 = 15 from rfl]

def captureZero (N : Usize) (d chain : Usize) (digit : U32) (sig : Signature) (state : Matrix 8#usize) := do
  if digit=0#u32 then
    let start ← chain * N
    let next ← chain + 1#usize
    let stop ← next * N
    let (part,back) ← alloc.vec.Vec.index_mut (core.slice.index.SliceIndexRangeUsizeSlice U8) sig {start:=start,«end»:=stop}
    let value ← NativeVerify.Wots.extract_lane N state 0#usize d
    let bytes ← lift (Array.to_slice value)
    let copied ← core.slice.Slice.copy_from_slice core.marker.CopyU8 part bytes
    ok (back copied)
  else ok sig

theorem captureZero_spec {N : Usize} (p : params.Params) (hp : PN p N) (lane chain : Usize) (d : U32)
    (sig : Signature) (state : Matrix 8#usize) (slots : Nat) (size : sig.length=slots*N.val) (live : chain.val<slots)
    (cap : slots≤128) (fit : lane.val<8) :
    captureZero N lane chain d sig state ⦃ out => out.length=slots*N.val ∧ ∀ i<slots, ∀ b<N.val,
      Block out N.val i b=if i=chain.val ∧ d.val=0 then (digest N state lane.val)[b]! else Block sig N.val i b ⦄ := by
  unfold captureZero
  split
  · rename_i hit
    subst d
    change writeLane N sig chain lane state ⦃ _ ⦄
    apply WP.spec_mono (writeLane_spec p hp sig chain lane state slots size live cap fit)
    intro out wrote
    simpa [Stored] using wrote
  · rename_i miss
    have ne : d.val ≠ 0 := by intro h;apply miss;apply UScalar.eq_of_val_eq;exact h
    simp [ne,size]

theorem forest {N : Usize} (p : params.Params) (hp : PN p N) (sk seed : Array U8 N) (a : address.Adrs) (base : Nat)
    (digits : alloc.vec.Vec U32) (len n : Usize) (sw skw : Array U64 4#usize) (lane : Usize) (w0 w1 : U64)
    (prf hash : Array U64 8#usize) (buffer : Signature) (pk0 : Matrix 8#usize) (pos0 : Usize) (state0 : Matrix 8#usize)
    (counts : len.val=digits.length) (width : n.val=N.val/8) (fit : lane.val<8) (slots : Nat)
    (enough : len.val≤slots) (cap : slots≤128) (size : buffer.length=slots*N.val)
    (valid : ∀ i<digits.length, digits.val[i]!.val≤15)
    (prfHeader : Header seed (laneAddress a address.WOTS_PRF base) sw w0 w1 prf)
    (hashHeader : Header seed (laneAddress a address.WOTS_HASH base) sw w0 w1 hash)
    (key : ∀ k<N.val/8, skw.val[k]!.bv=inputWord sk.val k) (rate : pos0.val<17)
    (ready : ∀ l<8, (ShakeBatch.lane pk0 l,8*pos0.val)=streamPrefix p sk seed a base l 0) (perms : Permutes kernel) :
    xmss_sign_batch_loop2 N 8#usize ⟨0#usize,len⟩ digits n sw skw lane w0 w1 prf hash buffer pk0 pos0 state0 ⦃ out =>
      WrittenPrefix p sk seed (laneAddress a address.WOTS_HASH base lane.val) digits.val slots len.val buffer out.1 ∧
      out.2.2.val<17 ∧ ∀ l<8, (ShakeBatch.lane out.2.1 l,8*out.2.2.val)=streamPrefix p sk seed a base l len.val ⦄ := by
  unfold xmss_sign_batch_loop2
  apply loop.spec_decr_nat (measure := fun s : (core.ops.range.Range Usize) × Signature × Matrix 8#usize × Usize × Matrix 8#usize => len.val-s.1.start.val)
    (inv := fun s => s.1.«end»=len ∧ s.1.start.val≤len.val ∧
      WrittenPrefix p sk seed (laneAddress a address.WOTS_HASH base lane.val) digits.val slots s.1.start.val buffer s.2.1 ∧
      s.2.2.2.1.val<17 ∧ ∀ l<8, (ShakeBatch.lane s.2.2.1 l,8*s.2.2.2.1.val)=streamPrefix p sk seed a base l s.1.start.val)
  · rintro ⟨it,sig,pk,pos,state⟩ ⟨last,le,written,rated,streamed⟩
    simp only at last le written rated streamed ⊢
    unfold xmss_sign_batch_loop2.body
    by_cases more : it.start.val<len.val
    · step with core.iter.range.IteratorRange.next_Usize_some_spec it (by simpa only [last] using more) as ⟨_,next,tagEq,idx,ends⟩
      simp only [tagEq]
      step as ⟨d,read⟩
      rw [←getElem!_pos] at read
      let id := UScalar.cast .U32 it.start
      have iv : id.val=it.start.val := by
        dsimp only [id];scalar_tac
      let prfVal := seedValue p sk seed a base id
      simp only [ShakeBatch.core.num.U32.swap_bytes,lift,bind_ok]
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
      simp only [bind_ok,permuted]
      apply WP.spec_bind (Pₘ := fun out : Signature => out.length=slots*N.val ∧ ∀ i<slots, ∀ b<N.val,
        Block out N.val i b=if i=it.start.val ∧ d.val=0 then (digest N start lane.val)[b]! else Block sig N.val i b)
      · split
        · rename_i hit
          apply write_then p hp sig it.start lane start slots written.1 (by omega) cap fit (fun out => ok out) _
          intro out wrote
          exact (WP.spec_ok _).mpr (by simpa only [hit,show (0#u32).val=0 from rfl,and_true,Stored] using wrote)
        · rename_i miss
          have ne : d.val≠0 := by intro h;apply miss;apply UScalar.eq_of_val_eq;exact h
          exact (WP.spec_ok _).mpr ⟨written.1,by simp [ne]⟩
      intro sig0 zeroStage
      obtain ⟨zsize,zeros⟩ := zeroStage
      have init (l : Nat) (hl : l<8) : digest N start l=chainValue p seed (laneAddress a address.WOTS_HASH base) id prfVal 0 l := p0 l hl
      have maximum : params.W - 1#u32=ok 15#u32 := by rw [W_eq];rfl
      simp only [maximum,bind_ok]
      step with rounds p hp seed (laneAddress a address.WOTS_HASH base) id prfVal sw lane w0 w1 hash sig0 start
        it.start d word slots hashHeader wtag fit (by omega) cap zsize init perms as ⟨signed,final,captured,done⟩
      have row (l : Nat) (hl : l<8) : digest N final l=tip p sk seed a base l it.start.val := by
        rw [done l hl,←iv]
        exact tip_value p sk seed a base l id
      step with Stream.absorb_digest N n pk pos final rated width (by have := hp.le32;omega) (aligned_hash hp) perms
        (fun l => tip p sk seed a base l it.start.val) row as ⟨newPk,newPos,newRate,feed⟩
      refine ⟨ends.trans last,by omega,⟨captured.1,?_⟩,newRate,?_,by omega⟩
      · intro i hi b hb
        have dv : d.val=digits.val[it.start.val]!.val := by rw [read]
        have hv := valid it.start.val (by omega)
        have positive : 0<d.val → d.val≤15 := by omega
        rw [captured.2 i hi b hb,zeros i hi b hb,written.2 i hi b hb,idx]
        by_cases selected : i=it.start.val
        · subst i
          simp only [true_and,le_refl,lt_self_iff_false,ite_false,lt_add_iff_pos_right,Nat.zero_lt_one,ite_true]
          rw [←iv,←signed_value p sk seed a base lane.val id digits.val]
          rw [←iv] at dv
          rw [←dv]
          by_cases zero : d.val=0
          · rw [if_neg (by omega),if_pos zero,zero]
            exact congrArg (fun v : Spec.Bytes => v[b]!) (init lane.val fit)
          · rw [if_pos ⟨by omega,positive (by omega)⟩]
        · have no1 : ¬ (i=it.start.val ∧ 0<d.val ∧ d.val≤15) := fun h => selected h.1
          have no0 : ¬ (i=it.start.val ∧ d.val=0) := fun h => selected h.1
          have eq : (i < it.start.val+1) ↔ (i < it.start.val) := by omega
          rw [if_neg no1,if_neg no0]
          by_cases old : i < it.start.val
          · rw [if_pos old,if_pos (eq.mpr old)]
          · rw [if_neg old,if_neg (fun hh => old (eq.mp hh))]
      · intro l hl
        rw [feed l hl,streamed l hl,idx]
        simp [streamPrefix,List.range_succ,List.foldl_append,List.append_assoc]
    · obtain ⟨⟨_,_⟩,no,tag,_⟩ := spec_imp_exists (core.iter.range.IteratorRange.next_Usize_none_spec it (by rw [last];omega))
      simp [no,tag,show it.start.val=len.val by omega] at written streamed ⊢
      exact ⟨written,rated,streamed⟩
  · refine ⟨rfl,by simp,⟨size,?_⟩,rate,ready⟩
    intro i hi b hb
    simp

end slhdsa.Fused
