import Fused.ChainValues
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.Fused
open ShakeBatch NativeVerify NativeVerify.Wots NativeShakeWots NativeShakeWots.Signer cache.builder.nativeShake.Vector.Fused
set_option linter.concreteInstances false
set_option maxHeartbeats 1000000
variable [kernel : Kernel]
local instance captureMachine : Machine := machine kernel

def writeLane (N : Usize) (sig : Signature) (chain lane : Usize) (state : Matrix 8#usize) := do
  let lo ← chain * N
  let next ← chain + 1#usize
  let hi ← next * N
  let (slice,back) ← alloc.vec.Vec.index_mut (core.slice.index.SliceIndexRangeUsizeSlice U8) sig {start:=lo,«end»:=hi}
  let raw ← NativeVerify.Wots.extract_lane N state 0#usize lane
  let s ← lift (Array.to_slice raw)
  let copy ← core.slice.Slice.copy_from_slice core.marker.CopyU8 slice s
  ok (back copy)

def Stored (N : Usize) (slots id : Nat) (before after : Signature) (v : Spec.Bytes) : Prop :=
  after.length=slots*N.val ∧ ∀ i<slots, ∀ b<N.val, Block after N.val i b=
    if i=id then v[b]! else Block before N.val i b

theorem writeLane_spec {N : Usize} (p : params.Params) (hp : PN p N) (sig : Signature) (chain lane : Usize)
    (state : Matrix 8#usize) (slots : Nat) (size : sig.length=slots*N.val) (live : chain.val<slots)
    (cap : slots≤128) (fits : lane.val<8) :
    writeLane N sig chain lane state ⦃ out => Stored N slots chain.val sig out (digest N state lane.val) ⦄ := by
  have bound := hp.le32
  have limit := Nat.mul_le_mul cap bound
  have endRoom := Nat.mul_le_mul_right N.val live
  unfold writeLane
  step as ⟨lo,beginAt⟩ <;> try scalar_tac
  step as ⟨next,nextAt⟩
  step as ⟨hi,endAt⟩ <;> try scalar_tac
  step as ⟨piece,_,plen,backEq⟩
  step with extract_digest N state lane bound (aligned_hash hp) fits as ⟨raw,rawBytes⟩
  simp only [lift,bind_ok]
  step as ⟨copy,cp⟩
  all_goals try (simp [beginAt,endAt,nextAt,Nat.add_mul] at *;omega)
  have update : (piece.2 copy).val=sig.val.setSlice! (chain.val*N.val) raw.val := by
    rw [backEq,cp]
    simp [alloc.vec.Vec.setSlice!,alloc.vec.Vec.val,Slice.setSlice!_val,beginAt]
  exact rawBytes ▸ block_store raw sig (piece.2 copy) _ _ size live update

theorem write_then {α : Type} {N : Usize} (p : params.Params) (hp : PN p N)
    (sig : Signature) (chain lane : Usize) (state : Matrix 8#usize) (slots : Nat)
    (size : sig.length=slots*N.val) (live : chain.val<slots) (cap : slots≤128) (fits : lane.val<8)
    (k : Signature → Result α) (post : α → Prop)
    (cont : ∀ out, Stored N slots chain.val sig out (digest N state lane.val) → k out ⦃post⦄) :
    (do let lo ← chain * N
        let next ← chain + 1#usize
        let hi ← next * N
        let (slice,back) ← alloc.vec.Vec.index_mut (core.slice.index.SliceIndexRangeUsizeSlice U8) sig {start:=lo,«end»:=hi}
        let raw ← NativeVerify.Wots.extract_lane N state 0#usize lane
        let copy ← core.slice.Slice.copy_from_slice core.marker.CopyU8 slice raw.to_slice
        k (back copy)) ⦃post⦄ := by
  have bound := hp.le32
  have limit := Nat.mul_le_mul cap bound
  have endRoom := Nat.mul_le_mul_right N.val live
  step as ⟨lo,beginAt⟩ <;> try scalar_tac
  step as ⟨next,nextAt⟩
  step as ⟨hi,endAt⟩ <;> try scalar_tac
  step as ⟨piece,back,_,plen,backEq⟩
  step with extract_digest N state lane bound (aligned_hash hp) fits as ⟨raw,rawBytes⟩
  step as ⟨copy,cp⟩
  all_goals try (simp [beginAt,endAt,nextAt,Nat.add_mul] at *;omega)
  have update : (back copy).val=sig.val.setSlice! (chain.val*N.val) raw.val := by
    rw [backEq,cp]
    simp [alloc.vec.Vec.setSlice!,alloc.vec.Vec.val,Slice.setSlice!_val,beginAt]
  apply cont
  exact rawBytes ▸ block_store raw sig (back copy) _ _ size live update

/-- The register image and all untouched signature bytes after the actual
fifteen-round signer loop. A zero digit is handled by its caller's PRF write. -/
def Seen (N : Usize) (slots id digit steps : Nat) (before after : Signature) (v : Spec.Bytes) : Prop :=
  after.length=slots*N.val ∧ ∀ i<slots, ∀ b<N.val, Block after N.val i b=
    if i=id ∧ 0<digit ∧ digit≤steps then v[b]! else Block before N.val i b

theorem rounds {N : Usize} (p : params.Params) (hp : PN p N) (seed : Array U8 N)
    (addr : Nat → address.Adrs) (id : U32) (initial : Nat → Spec.Bytes) (sw : Array U64 4#usize)
    (lane : Usize) (w0 w1 : U64) (w2 : Array U64 8#usize) (sig : Signature) (state : Matrix 8#usize)
    (chain : Usize) (d : U32) (tag : U64) (slots : Nat)
    (header : Header seed addr sw w0 w1 w2) (tagged : tag.bv=addressLow id)
    (fit : lane.val<8) (live : chain.val<slots) (cap : slots≤128) (size : sig.length=slots*N.val)
    (started : ∀ l<8, digest N state l=chainValue p seed addr id initial 0 l) (perms : Permutes kernel) :
    xmss_sign_batch_loop2_loop0 N ⟨0#u32,15#u32⟩ sw lane w0 w1 w2 sig state chain d tag ⦃ out =>
      Seen N slots chain.val d.val 15 sig out.1 (chainValue p seed addr id initial d.val lane.val) ∧
      ∀ l<8, digest N out.2 l=chainValue p seed addr id initial 15 l ⦄ := by
  unfold xmss_sign_batch_loop2_loop0
  apply loop.spec_decr_nat (measure := fun s : (core.ops.range.Range U32) × Signature × Matrix 8#usize => 15-s.1.start.val)
    (inv := fun s => s.1.«end».val=15 ∧ s.1.start.val≤15 ∧
      Seen N slots chain.val d.val s.1.start.val sig s.2.1 (chainValue p seed addr id initial d.val lane.val) ∧
      ∀ l<8, digest N s.2.2 l=chainValue p seed addr id initial s.1.start.val l)
  · rintro ⟨it,current,st⟩ ⟨last,le,seen,prior⟩
    simp only at last le seen prior ⊢
    unfold xmss_sign_batch_loop2_loop0.body
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
      simp only [bind_ok,permuted]
      step as ⟨count,cv⟩
      split
      · rename_i hit
        apply write_then p hp current chain lane newState slots seen.1 live cap fit (fun out => ok (cont (next,out,newState))) _
        intro newSig stored
        simp only [step_simps]
        refine ⟨by simpa only [ends] using last,by omega,⟨stored.1,?_⟩,by simpa [idx] using nextValues,by omega⟩
        intro i hi' b hb
        have equal : d.val=it.start.val+1 := by subst d;exact cv
        rw [stored.2 i hi' b hb,nextValues lane.val fit,seen.2 i hi' b hb,equal,idx]
        split_ifs <;> first | rfl | omega
      · rename_i missed
        simp only [step_simps]
        have ne : d.val ≠ it.start.val+1 := by intro h;apply missed;apply UScalar.eq_of_val_eq;omega
        refine ⟨by simpa only [ends] using last,by omega,⟨seen.1,?_⟩,by simpa [idx] using nextValues,by omega⟩
        intro i hi' b hb
        rw [seen.2 i hi' b hb,idx]
        split_ifs <;> first | rfl | omega
    · obtain ⟨⟨_,_⟩,no,tag,_⟩ := spec_imp_exists (core.iter.range.IteratorRange.next_U32_none_spec it
        (by rw [last]; change 15 ≤ it.start.val; omega))
      simp [no,tag,show it.start.val=15 by omega] at seen prior ⊢
      exact ⟨seen,prior⟩
  · refine ⟨rfl,by simp,⟨size,?_⟩,started⟩
    intro i hi b hb
    change Block sig N.val i b=(if i=chain.val ∧ 0<d.val ∧ d.val≤0 then _ else _)
    rw [ite_eq_right (by omega)]

end slhdsa.Fused
