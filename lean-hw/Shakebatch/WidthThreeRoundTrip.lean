import Shakebatch.WidthThreeParallel
import Shakebatch.WidthThreeLengths
import Shakebatch.WidthThreeKeygen
open Aeneas Aeneas.Std Result
namespace slhdsa.WidthThree
noncomputable section

/-- Generate a key from three N-byte seeds, sign with the selected Rust entry,
and pass the returned signature and public key to the native verifier. -/
def generateSignVerify {N : Usize}
    (sign : Slice U8 → Slice U8 → Slice U8 → Array U8 N → Result (Option (alloc.vec.Vec U8)))
    (p : slhdsa.params.Params) (secret prf publicSeed : Array U8 N)
    (sk pk msg ctx : Slice U8) (rnd : Array U8 N) : Result Bool := do
  let (secretKey,publicKey) ← WidthThreeKeygenSDK.slhdsa.shake.slh.slh_keygen_internal p
    secret prf publicSeed sk pk
  let signature ← sign msg ctx secretKey rnd
  match signature with
  | none => ok false
  | some sig => WidthThreeVerifySDK.ShakeoptSeg.shake.slh.slh_verify N p msg sig.deref ctx publicKey

private theorem generated_accepts {N : Usize} (p : slhdsa.params.Params) (hp : PN p N)
    (sign : Slice U8 → Slice U8 → Slice U8 → Array U8 N → Result (Option (alloc.vec.Vec U8)))
    (secret prf publicSeed : Array U8 N) (sk pk msg ctx : Slice U8) (rnd : Array U8 N)
    (ks : sk.length=4*N.val) (ps : pk.length=2*N.val) (hc : ctx.length≤255)
    (correct : ∀ key : Slice U8, key.length=4*N.val → sign msg ctx key rnd ⦃ r =>
      r.map (fun x => bytes x.val) = Spec.slhSign (Shake.params p) (bytes msg.val) (bytes ctx.val)
        (bytes key.val) (bytes rnd.val) ⦄) :
    generateSignVerify sign p secret prf publicSeed sk pk msg ctx rnd = ok true := by
  have hv : (Shake.params p).Valid := by
    obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_⟩ := hp.valid
    constructor <;> assumption
  obtain ⟨⟨sk',pk'⟩,gen,keys,ks',ps'⟩ := spec_imp_exists
    (WidthThreeKeygenSDK.slhdsa.Shake.slh_keygen_internal_spec p hp secret prf publicSeed sk pk ks ps)
  have length (a : Array U8 N) : (bytes a.val).length = (Shake.params p).n := by simp only [bytes_length,Array.property]; exact hp.n.symm
  have good := Spec.keygen_keyOk (Shake.params p) hv _ _ _ (length secret) (length prf) (length publicSeed)
  rw [← keys] at good
  obtain ⟨signature,sg,bytesEq⟩ := spec_imp_exists (correct sk' ks')
  obtain ⟨expected,some_bytes,verified⟩ := Spec.slh_complete (Shake.params p) hv (bytes msg.val) (bytes ctx.val)
    (bytes sk'.val) (bytes rnd.val) (by simpa [bytes] using hc) good.1
  rw [some_bytes] at bytesEq
  cases signature with
  | none => contradiction
  | some sig =>
    obtain ⟨verdict,run,answer⟩ := spec_imp_exists
      (WidthThreeVerifySDK.Shakeopt.Segmented.slh_verify_spec p hp msg sig.deref ctx pk' ps')
    have byteEq : bytes sig.val = expected := Option.some.inj bytesEq
    have pkEq : bytes pk'.val = Spec.skPk (Shake.params p) (bytes sk'.val) := good.2
    rw [vec_deref_val,byteEq,pkEq,verified] at answer
    simp only [generateSignVerify,gen,bind_ok,uncurry,sg,run,answer]

theorem serial_roundtrip {N : Usize} (c : SigningPrimitives) (p : slhdsa.params.Params) (hp : PN p N)
    (secret prf publicSeed : Array U8 N) (sk pk msg ctx : Slice U8) (rnd : Array U8 N)
    (ks : sk.length=4*N.val) (ps : pk.length=2*N.val) (hc : ctx.length≤255) :
    generateSignVerify (WidthThreeLinuxSDK.WidthThreeSDK.ShakeoptSeg.shake.slh.slh_sign c p) p
      secret prf publicSeed sk pk msg ctx rnd = ok true :=
  generated_accepts p hp _ secret prf publicSeed sk pk msg ctx rnd ks ps hc
    (fun key size => WidthThreeLinuxSDK.WidthThreeSDK.Shakeopt.Segmented.slh_sign_spec c p hp msg ctx key rnd size)

theorem serial_keygen_parallel_sign_roundtrip {N : Usize} (ops : ParallelPrimitives) (p : slhdsa.params.Params) (hp : PN p N)
    (secret prf publicSeed : Array U8 N) (sk pk msg ctx : Slice U8) (rnd : Array U8 N)
    (ks : sk.length=4*N.val) (ps : pk.length=2*N.val) (hc : ctx.length≤255) :
    generateSignVerify (WidthThreeParallel.ShakeoptSeg.shake.slh.slh_sign ops p) p
      secret prf publicSeed sk pk msg ctx rnd = ok true :=
  generated_accepts p hp _ secret prf publicSeed sk pk msg ctx rnd ks ps hc
    (fun key size => WidthThreeParallel.Shakeopt.Segmented.slh_sign_spec ops p hp msg ctx key rnd size)

end
end slhdsa.WidthThree
