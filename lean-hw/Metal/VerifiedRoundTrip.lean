import Metal.PublicSignatures
import Armwide.PublicSignature
import Cachepath.NativeVerify.Hosted
open Aeneas Aeneas.Std Result slhdsa
open MetalPublicSignatures

namespace MetalVerifiedRoundTrip
noncomputable section
open slhdsa.Armwide.Public.Dispatcher (Cpu)
open slhdsa.Armwide.Keygen (Features)
variable [Cpu] [Features]

/-- Apple's hosted CPU verifier for each backend, including its SIMD recoveries. -/
def cpu (family : Spec.HashFamily) (sha3 : Bool) (N : Usize) (p : params.Params) :=
  match family with
  | .sha2 => ArmSdk.AppleContext.SegmentedSdk.slhdsa.api.verify N p
  | .shake => AppleVerifier.VerifierWithRecovery.SegmentedPublic.slhdsa.shake.api.verify
      (AppleNativeRecovery.slhdsa.NativeVerify.appleRecovery sha3) N p

def view (family : Spec.HashFamily) (p : params.Params) :=
  match family with | .sha2 => paramsS p | .shake => Shake.params p

theorem cpu_spec {N : Usize} (family : Spec.HashFamily) (sha3 : Bool) (p : params.Params)
    (hp : PN p N) (m sig ctx pk : Slice U8) (hs : pk.length=2*N.val) (room : Room m.length (msgSlack N.val+257)) :
    cpu family sha3 N p m sig ctx pk ⦃ v => v=Spec.slhVerify (view family p)
        (bytes m.val) (bytes sig.val) (bytes ctx.val) (bytes pk.val) ⦄ := by
  cases family
  · exact ArmSdk.AppleContext.SegmentedSdk.slhdsa.api_verify_spec p hp _ _ _ _ hs room
  · exact CacheopsRust.NativeVerifier.appleVerify sha3 p hp _ _ _ _ hs room

private def buf (b : Spec.Bytes) (size : b.length≤Usize.max) : Slice U8 :=
  Slice.from (b.map fun x => (⟨x⟩ : U8)) (by simpa using size)
private theorem buf_bytes (b : Spec.Bytes) (size : b.length≤Usize.max) :
    bytes (buf b size).val=b := by simp [buf,Slice.from_val,bytes]

/-- This property starts with the Metal key readback, passes its secret key into
the Metal signer, and passes its public key and returned signature to the CPU. -/
def Session (P : Spec.Params) (verify : Slice U8 → Slice U8 → Slice U8 → Slice U8 → Result Bool)
    (keyOutput : Except MetalCompletion.Error (List (Spec.Bytes × Spec.Bytes))) (raw : Raw)
    (secret prf pub rnd : Spec.Bytes) (m ctx : Slice U8) : Prop :=
  ∃ sk pk sig pkBuf sigBuf,
    keyOutput=.ok [(sk,pk)] ∧ single raw (bytes m.val) (bytes ctx.val) sk rnd=.ok (some sig) ∧
    (sk,pk)=Spec.slhKeygenInternal P secret prf pub ∧
    some sig=Spec.slhSign P (bytes m.val) (bytes ctx.val) sk rnd ∧
    bytes pkBuf.val=pk ∧ bytes sigBuf.val=sig ∧ verify m sigBuf ctx pkBuf=ok true

theorem roundTrip {N : Usize} (family : Spec.HashFamily) (sha3 : Bool) (p : params.Params)
    (hp : PN p N) (P : Spec.Params) (matching : view family p=P) (valid : P.Valid)
    (maxSig : P.sigBytes≤Usize.max) (width : P.n=N.val)
    (secret prf pub rnd : Spec.Bytes) (ss : secret.length=P.n) (ps : prf.length=P.n) (ks : pub.length=P.n)
    (m ctx : Slice U8) (context : ctx.length≤255) (room : Room m.length (msgSlack N.val+257))
    (kg : Except MetalCompletion.Error (List (Spec.Bytes × Spec.Bytes))) (raw : Raw)
    (generated : kg=.ok [Spec.slhKeygenInternal P secret prf pub])
    (signed : ∀ msg sk r, rawSingle raw msg sk r=.ok (Spec.slhSignInternal P msg sk r)) :
    Session P (cpu family sha3 N p) kg raw secret prf pub rnd m ctx := by
  let keys := Spec.slhKeygenInternal P secret prf pub
  let sig := Spec.slhSignInternal P (Spec.withContext (bytes m.val) (bytes ctx.val)) keys.1 rnd
  have size : keys.2.length=2*N.val := by simp [keys,Spec.slhKeygenInternal,Spec.xmssNode_length _ valid,ks,width];omega
  have pkFits : keys.2.length≤Usize.max := by
    rw [size];have := hp.le32;have cap : 64≤Usize.max := by scalar_tac
    omega
  have sigFits : sig.length≤Usize.max := by rw [Spec.slhSignInternal_length P valid]; exact maxSig
  let pkBuf := buf keys.2 pkFits
  let sigBuf := buf sig sigFits
  have pkLen : pkBuf.length=2*N.val := by simpa [pkBuf,buf,Slice.length,Slice.from_val] using size
  have live : ¬ (bytes ctx.val).length>255 := by simpa [Slice.length] using Nat.not_lt.mpr context
  have legal := Spec.keygen_keyOk P valid secret prf pub ss ps ks
  have correct := Spec.slh_complete_internal P valid (Spec.withContext (bytes m.val) (bytes ctx.val)) keys.1 rnd legal.1
  obtain ⟨v,run,verdict⟩ := spec_imp_exists (cpu_spec family sha3 p hp m sigBuf ctx pkBuf pkLen room)
  have accepted : v=true := by
    rw [verdict,matching,buf_bytes,buf_bytes,Spec.slhVerify,if_neg live]
    exact legal.2.symm ▸ correct
  refine ⟨keys.1,keys.2,sig,pkBuf,sigBuf,generated,?_,rfl,?_,buf_bytes ..,buf_bytes ..,accepted ▸ run⟩
  · simp [single,live,context,Slice.length] at context ⊢
    simp_all [signed,Except.map,sig]
  · simp [Spec.slhSign,live,sig,show ctx.val.length≤255 from context]

end
end MetalVerifiedRoundTrip
