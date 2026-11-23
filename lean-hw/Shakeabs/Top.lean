import Shakeabs.Prefix
open Aeneas Aeneas.Std Result
namespace slhdsa.PlatformShake
open Keccak (words)
def asScalar (s : ShakeAbsRust.shake256.Sponge) : shake256.Sponge := ⟨s.lanes,s.pos⟩

theorem absorb (s : ShakeAbsRust.shake256.Sponge) (data : Slice U8) (rate : s.pos.val<136) :
    ShakeAbsRust.shake256.Sponge.absorb s data ⦃ out => out.pos.val<136 ∧
      Keccak.view (asScalar out) = (bytes data.val).foldl Spec.Keccak.feed (Keccak.view (asScalar s)) ⦄ := by
  unfold ShakeAbsRust.shake256.Sponge.absorb
  step with initialBytes data s 0#usize (by simp) rate as ⟨st,p,k,ki,pr,alignedPos,first⟩
  step with aligned data st p k ki pr alignedPos as ⟨st',p',k',ki',pr',middle⟩
  step with tail data st' p' k' ki' pr' as ⟨out,pos,last,done⟩
  exact ⟨last,by simpa [remaining,Keccak.view,asScalar] using done.trans (middle.trans first)⟩

theorem finish_eq (s : ShakeAbsRust.shake256.Sponge) (out : Slice U8) :
    ShakeAbsRust.shake256.Sponge.finish s out=shake256.Sponge.finish (asScalar s) out := by
  unfold ShakeAbsRust.shake256.Sponge.finish shake256.Sponge.finish
    ShakeAbsRust.shake256.Sponge.finish_loop shake256.Sponge.finish_loop
    ShakeAbsRust.shake256.Sponge.finish_loop.body shake256.Sponge.finish_loop.body
  simp only [ShakeAbsRust.shake256.RATE,shake256.RATE,ShakeAbsRust.shake256.permute,scalar_eq,asScalar]

/-- The aligned x86 SHAKE sponge consumes and emits the FIPS 202 bytes for
arbitrary input and output lengths, including complete rate blocks. -/
theorem shake256_fips (input out : Slice U8) :
    ShakeAbsRust.shake256.shake256 input out ⦃ result => bytes result.val=Spec.shake256 (bytes input.val) out.length ⦄ := by
  unfold ShakeAbsRust.shake256.shake256
  simp only [ShakeAbsRust.shake256.Sponge.new,bind_ok]
  step with absorb ⟨Array.repeat 25#usize 0#u64,0#usize⟩ input (by decide) as ⟨s,rate,feed⟩
  rw [finish_eq]
  apply WP.spec_mono (Keccak.finish_spec _ _ rate)
  intro r eq
  rw [eq,feed]
  rfl
end slhdsa.PlatformShake
