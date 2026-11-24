import Kappleouter.Parts
open Aeneas Aeneas.Std Result
namespace slhdsa.PlatformShake.Apple
open Keccak (words)
set_option maxHeartbeats 2000000

def portable (s : KappleouterRust.shake256.Sponge) : ShakeAbsRust.shake256.Sponge := ⟨s.lanes,s.pos⟩

private theorem partialEq : @KappleouterRust.shake256.Sponge.absorb_loop1 = @KspongeLRust.shake256.Sponge.absorb_loop1 := by
  unfold KappleouterRust.shake256.Sponge.absorb_loop1 KspongeLRust.shake256.Sponge.absorb_loop1
    KappleouterRust.shake256.Sponge.absorb_loop1.body KspongeLRust.shake256.Sponge.absorb_loop1.body
  simp only [permuteEq,Linux.permuteEq,KappleouterRust.shake256.RATE,KspongeLRust.shake256.RATE]

theorem absorb (s : KappleouterRust.shake256.Sponge) (data : Slice U8) (rate : s.pos.val<136) :
    KappleouterRust.shake256.Sponge.absorb s data ⦃ out => out.pos.val<136 ∧
      (words out.lanes,out.pos.val) = (bytes data.val).foldl Spec.Keccak.feed (words s.lanes,s.pos.val) ⦄ := by
  unfold KappleouterRust.shake256.Sponge.absorb
  step with initialBytes data s 0#usize (by simp) rate as ⟨st,p,k,ki,pr,pa,first⟩
  have rateVal : KappleouterRust.shake256.RATE.val=136 := by unfold KappleouterRust.shake256.RATE; rfl
  step as ⟨left,lval⟩
  step as ⟨two,tv⟩
  spec_split
  · rename_i enough
    have avail : k.val+272 ≤ data.length := by scalar_tac
    have pal : p.val%8=0 := by omega
    rw [partialEq]
    step with Linux.partialBlock data st p k (by omega) ki pr pal as ⟨st1,p1,k1,k1le,pzero,pref⟩
    step as ⟨rem,rv⟩
    step as ⟨n,nv⟩
    step as ⟨used,uv⟩
    simp only [KappleouterRust.sha512.hw.arm.available,bind_ok,ite_true,Std.bind_assoc]
    step as ⟨stop,sv⟩
    step as ⟨chunk,cv,cl⟩
    have whole : chunk.length%136=0 := by scalar_tac
    step with Kapplebulk.blocks_fips st1 chunk whole as ⟨st2,blk⟩
    have splitData : (bytes data.val).drop k1.val = bytes chunk.val ++ (bytes data.val).drop stop.val := by
      rw [cv,List.slice,bytes_take,bytes_drop,sv,Nat.add_sub_cancel_left,← List.drop_drop]
      exact (List.take_append_drop _ _).symm
    have bulk : remaining data st2 p1 stop = remaining data st1 p1 k1 := by
      unfold remaining
      rw [splitData,List.foldl_append,pzero,←blk]
    rw [alignedLong,tailLong]
    step with aligned data st2 p1 stop (by scalar_tac) (by omega) (Or.inl (by omega)) as ⟨st3,p3,k3,k3le,p3r,middle⟩
    step with tail data st3 p3 k3 k3le p3r as ⟨out,pos,last,done⟩
    exact ⟨last,by simpa [remaining] using done.trans (middle.trans (bulk.trans (pref.trans first)))⟩
  · rw [alignedShort,tailShort]
    step with aligned data st p k ki pr pa as ⟨st',p',k',ki',pr',middle⟩
    step with tail data st' p' k' ki' pr' as ⟨out,pos,last,done⟩
    exact ⟨last,by simpa [remaining] using done.trans (middle.trans first)⟩

theorem finishEq (s : KappleouterRust.shake256.Sponge) (out : Slice U8) :
    KappleouterRust.shake256.Sponge.finish s out = ShakeAbsRust.shake256.Sponge.finish (portable s) out := by
  unfold KappleouterRust.shake256.Sponge.finish ShakeAbsRust.shake256.Sponge.finish
    KappleouterRust.shake256.Sponge.finish_loop ShakeAbsRust.shake256.Sponge.finish_loop
    KappleouterRust.shake256.Sponge.finish_loop.body ShakeAbsRust.shake256.Sponge.finish_loop.body
  simp only [portable,permuteEq,KappleouterRust.shake256.RATE,ShakeAbsRust.shake256.RATE]

theorem shake256_fips (input out : Slice U8) :
    KappleouterRust.shake256.shake256 input out ⦃ result => bytes result.val=Spec.shake256 (bytes input.val) out.length ⦄ := by
  unfold KappleouterRust.shake256.shake256
  simp only [KappleouterRust.shake256.Sponge.new,bind_ok]
  step with absorb ⟨Array.repeat 25#usize 0#u64,0#usize⟩ input (by decide) as ⟨s,rate,feed⟩
  rw [finishEq,finish_eq]
  apply WP.spec_mono (Keccak.finish_spec _ _ rate)
  intro r eq
  rw [eq]
  change Spec.Keccak.squeeze (Spec.Keccak.finalize (words s.lanes,s.pos.val)) 0 _ = _
  rw [feed]
  rfl
end slhdsa.PlatformShake.Apple
