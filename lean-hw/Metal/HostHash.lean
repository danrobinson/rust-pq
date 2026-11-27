import Metal.HostHashProgram
import Slhdsa.Proofs.ShakeHash

open Aeneas Aeneas.Std Result slhdsa
namespace MetalHostHash

theorem tree_fips (p : params.Params) (digest : Slice U8) (hv : (paramsS p).Valid)
    (h : digest.length=p.m.val) :
    digest_tree p digest ⦃ r => r.val=Spec.digestTree (paramsS p) (bytes digest.val) ∧ r.val<2^(p.h.val-p.hp.val) ⦄ :=
  slhdsa.digest_tree_spec p digest hv h

theorem leaf_fips (p : params.Params) (digest : Slice U8) (hv : (paramsS p).Valid)
    (h : digest.length=p.m.val) :
    digest_leaf p digest ⦃ r => r.val=Spec.digestLeaf (paramsS p) (bytes digest.val) ∧ r.val<2^p.hp.val ⦄ :=
  slhdsa.digest_leaf_spec p digest hv h

theorem frame_fips (m ctx : Slice U8) (hc : ctx.length≤255) (room : m.length+257≤Usize.max) :
    with_context m ctx ⦃ out => bytes out.val=Spec.withContext (bytes m.val) (bytes ctx.val) ∧
      out.length=2+ctx.length+m.length ⦄ := by
  unfold with_context
  step as ⟨i,hi⟩
  step as ⟨j,hj⟩
  apply slhdsa.with_context_spec m ctx hc room

theorem shake_randomizer {N : Usize} (k rnd : Array U8 N) (m : Slice U8)
    (room : m.length+2*N.val≤Usize.max) :
    shake_prf_msg k rnd m ⦃ out => bytes out.val=Spec.shake256 (bytes k.val++bytes rnd.val++bytes m.val) N.val ⦄ := by
  unfold shake_prf_msg
  step as ⟨i,hi⟩
  step as ⟨j,hj⟩
  simp only [lift,bind_ok,Array.to_slice_mut]
  step with fors_extend_from_slice_spec as ⟨x,hx,lx⟩
  · simp [alloc.vec.Vec.with_capacity,alloc.vec.Vec.new,alloc.vec.Vec.length,Slice.length] at * <;> omega
  step with fors_extend_from_slice_spec as ⟨y,hy,ly⟩
  · simp [alloc.vec.Vec.with_capacity,alloc.vec.Vec.new,alloc.vec.Vec.length,Slice.length,lx] at * <;> omega
  step with fors_extend_from_slice_spec as ⟨z,hz,lz⟩
  · simp [alloc.vec.Vec.with_capacity,alloc.vec.Vec.new,alloc.vec.Vec.length,Slice.length,ly,lx] at * <;> omega
  step with PlatformShake.Apple.shake256_fips as ⟨out,value⟩
  have size : out.val.length=N.val := by simpa using congrArg List.length value
  simp [Array.from_slice_val _ _ size,value,vec_deref_val,hz,hy,hx,bytes_append,alloc.vec.Vec.with_capacity]

theorem shake_digest {N : Usize} (p : params.Params) (r pk root : Array U8 N) (m : Slice U8)
    (room : m.length+3*N.val≤Usize.max) :
    shake_h_msg p r pk root m ⦃ out => bytes out.val=Spec.shake256 (bytes r.val++bytes pk.val++bytes root.val++bytes m.val) p.m.val ⦄ := by
  unfold shake_h_msg
  step as ⟨i,hi⟩
  step as ⟨j,hj⟩
  simp only [lift,bind_ok]
  step with fors_extend_from_slice_spec as ⟨a,ha,la⟩
  · simp [alloc.vec.Vec.with_capacity,alloc.vec.Vec.new,alloc.vec.Vec.length,Slice.length] at * <;> omega
  step with fors_extend_from_slice_spec as ⟨b,hb,lb⟩
  · simp [alloc.vec.Vec.with_capacity,alloc.vec.Vec.new,alloc.vec.Vec.length,Slice.length,la] at * <;> omega
  step with fors_extend_from_slice_spec as ⟨c,hc,lc⟩
  · simp [alloc.vec.Vec.with_capacity,alloc.vec.Vec.new,alloc.vec.Vec.length,Slice.length,lb,la] at * <;> omega
  step with fors_extend_from_slice_spec as ⟨d,hd,ld⟩
  · simp [alloc.vec.Vec.with_capacity,alloc.vec.Vec.new,alloc.vec.Vec.length,Slice.length,lc,lb,la] at * <;> omega
  step as ⟨v,contents,len⟩
  simp only [alloc.vec.Vec.deref_mut,bind_ok,lift]
  step with PlatformShake.Apple.shake256_fips as ⟨o,value⟩
  change v.slice.length=p.m.val at len
  change bytes o.val=_
  simpa [vec_deref_val,hd,hc,hb,ha,bytes_append,alloc.vec.Vec.with_capacity,len] using value

end MetalHostHash
