import Shakebatch.WidthEightHosted
import Shakebatch.WidthEightHostedKeys
open Aeneas Aeneas.Std Result
namespace slhdsa.WidthEight
open ParallelKeygenHost
noncomputable section

def Platform.isX86 : Platform → Bool
  | .apple _ => false
  | .x86 => true

@[instance_reducible] noncomputable def keyEngine (host : Platform) (p : params.Params) : Engine ShakeSeed :=
  match host with
  | .apple sha3 => WidthEightAppleKeys.slhdsa.WidthEight.sourceEngine (.apple sha3) p
  | .x86 => WidthEightX86Keys.slhdsa.WidthEight.sourceEngine .x86 p

theorem keys (host : Platform) {N : Usize} (p : params.Params) (hp : PN p N)
    (threads : Nat) (pool : PoolOutcome) : ShNode.KeyPair (keyEngine host p) host.isX86 threads pool (N:=N) p := by
  cases host with
  | apple sha3 => exact WidthEightAppleKeys.slhdsa.WidthEight.apple_keys sha3 p hp threads pool
  | x86 => exact WidthEightX86Keys.slhdsa.WidthEight.x86_keys p hp threads pool

theorem keygen_public {N : Usize} (p : params.Params) (hp : PN p N) (host : Platform) (threads : Nat)
    (pool : PoolOutcome) (seeds sk pk : Slice U8) (ss : seeds.length=3*N.val)
    (ks : sk.length=4*N.val) (ps : pk.length=2*N.val) :
    @Sh.shake.api.keygen (keyEngine host p) ⟨host.isX86,threads,pool⟩ N p seeds sk pk ⦃ out =>
      (bytes out.1.val,bytes out.2.val)=Spec.slhKeygenInternal (Shake.params p)
        (Spec.block (paramsS p) (bytes seeds.val) 0) (Spec.block (paramsS p) (bytes seeds.val) 1)
        (Spec.block (paramsS p) (bytes seeds.val) 2) ∧ out.1.length=4*N.val ∧ out.2.length=2*N.val ⦄ :=
  @Sh.public_keygen (keyEngine host p) ⟨host.isX86,threads,pool⟩ N p hp seeds sk pk ss ks ps
    (keys host p hp threads pool)

def sign (host : Platform) {N : Usize} (p : params.Params) (m ctx sk : Slice U8) (rnd : Array U8 N) :=
  match host with
  | .apple sha3 => WidthEightApple.WidthEightSDK.ShakeoptSeg.shake.slh.slh_sign (.apple sha3) p m ctx sk rnd
  | .x86 => WidthEightX86.WidthEightSDK.ShakeoptSeg.shake.slh.slh_sign .x86 p m ctx sk rnd

theorem sign_spec (host : Platform) {N : Usize} (p : params.Params) (hp : PN p N)
    (m ctx sk : Slice U8) (rnd : Array U8 N) (ks : sk.length=4*N.val) :
    sign host p m ctx sk rnd ⦃ r => r.map (fun x => bytes x.val) =
      Spec.slhSign (Shake.params p) (bytes m.val) (bytes ctx.val) (bytes sk.val) (bytes rnd.val) ⦄ := by
  cases host with
  | apple sha3 => exact WidthEightApple.WidthEightSDK.Shakeopt.Segmented.slh_sign_spec (.apple sha3) p hp m ctx sk rnd ks
  | x86 => exact WidthEightX86.WidthEightSDK.Shakeopt.Segmented.slh_sign_spec .x86 p hp m ctx sk rnd ks

def verify (host : Platform) (N : Usize) (p : params.Params) (m sig ctx pk : Slice U8) :=
  match host with
  | .apple sha3 => WidthEightApple.WidthEightSDK.ShakeoptSeg.shake.slh.slh_verify (.apple sha3) N p m sig ctx pk
  | .x86 => WidthEightX86.WidthEightSDK.ShakeoptSeg.shake.slh.slh_verify .x86 N p m sig ctx pk

theorem verify_spec (host : Platform) {N : Usize} (p : params.Params) (hp : PN p N)
    (m sig ctx pk : Slice U8) (ps : pk.length=2*N.val) :
    verify host N p m sig ctx pk ⦃ r => r=Spec.slhVerify (Shake.params p) (bytes m.val) (bytes sig.val)
      (bytes ctx.val) (bytes pk.val) ⦄ := by
  cases host with
  | apple sha3 => exact WidthEightApple.WidthEightSDK.Shakeopt.Segmented.slh_verify_spec (.apple sha3) p hp m sig ctx pk ps
  | x86 => exact WidthEightX86.WidthEightSDK.Shakeopt.Segmented.slh_verify_spec .x86 p hp m sig ctx pk ps

/-- Generate a key from three N-byte seeds, sign with the selected Rust entry,
and pass the returned signature and public key to the native verifier. -/
def generateSignVerify {N : Usize}
    (host : Platform) (threads : Nat) (pool : slhdsa.ParallelKeygenHost.PoolOutcome)
    (p : slhdsa.params.Params) (secret prf publicSeed : Array U8 N)
    (sk pk msg ctx : Slice U8) (rnd : Array U8 N) : Result Bool := do
  let (secretKey,publicKey) ← @Sh.shake.slh.slh_keygen_internal (keyEngine host p) ⟨host.isX86,threads,pool⟩ N p
    secret prf publicSeed sk pk
  let signature ← sign host p msg ctx secretKey rnd
  match signature with
  | none => ok false
  | some sig => verify host N p msg sig.deref ctx publicKey

theorem generated_accepts {N : Usize} (p : slhdsa.params.Params) (hp : PN p N)
    (host : Platform) (threads : Nat) (pool : slhdsa.ParallelKeygenHost.PoolOutcome)
    (secret prf publicSeed : Array U8 N) (sk pk msg ctx : Slice U8) (rnd : Array U8 N)
    (ks : sk.length=4*N.val) (ps : pk.length=2*N.val) (hc : ctx.length≤255) :
    generateSignVerify host threads pool p secret prf publicSeed sk pk msg ctx rnd = ok true := by
  have hv : (Shake.params p).Valid := by
    obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_⟩ := hp.valid
    constructor <;> assumption
  obtain ⟨⟨sk',pk'⟩,gen,keys,ks',ps'⟩ := spec_imp_exists
    (keys host p hp threads pool secret prf publicSeed sk pk ks ps)
  have length (a : Array U8 N) : (bytes a.val).length = (Shake.params p).n := by simp only [bytes_length,Array.property]; exact hp.n.symm
  have good := Spec.keygen_keyOk (Shake.params p) hv _ _ _ (length secret) (length prf) (length publicSeed)
  rw [← keys] at good
  obtain ⟨signature,sg,bytesEq⟩ := spec_imp_exists (sign_spec host p hp msg ctx sk' rnd ks')
  obtain ⟨expected,some_bytes,verified⟩ := Spec.slh_complete (Shake.params p) hv (bytes msg.val) (bytes ctx.val)
    (bytes sk'.val) (bytes rnd.val) (by simpa [bytes] using hc) good.1
  rw [some_bytes] at bytesEq
  cases signature with
  | none => contradiction
  | some sig =>
    obtain ⟨verdict,run,answer⟩ := spec_imp_exists
      (verify_spec host p hp msg sig.deref ctx pk' ps')
    have byteEq : bytes sig.val = expected := Option.some.inj bytesEq
    have pkEq : bytes pk'.val = Spec.skPk (Shake.params p) (bytes sk'.val) := good.2
    rw [vec_deref_val,byteEq,pkEq,verified] at answer
    simp only [generateSignVerify,gen,bind_ok,uncurry,sg,run,answer]

/-- The public three-seed buffer is decoded by the same three block reads as
the ordinary key-generation API. -/
def seededSession (host : Platform) (threads : Nat) (pool : PoolOutcome) {N : Usize}
    (p : params.Params) (seeds sk pk msg ctx : Slice U8) (rnd : Array U8 N) : Result Bool := do
  let secret ← util.block N seeds 0#usize
  let prf ← util.block N seeds 1#usize
  let publicSeed ← util.block N seeds 2#usize
  generateSignVerify host threads pool p secret prf publicSeed sk pk msg ctx rnd

theorem seeded_accepts (host : Platform) (threads : Nat) (pool : PoolOutcome) {N : Usize}
    (p : params.Params) (hp : PN p N) (seeds sk pk msg ctx : Slice U8) (rnd : Array U8 N)
    (ss : seeds.length=3*N.val) (ks : sk.length=4*N.val) (ps : pk.length=2*N.val) (hc : ctx.length≤255) :
    seededSession host threads pool p seeds sk pk msg ctx rnd = ok true := by
  unfold seededSession
  suffices result : _ ⦃ r => r=true ⦄ by
    obtain ⟨_,run,rfl⟩ := spec_imp_exists result
    exact run
  let* ⟨secret,_⟩ ← block_spec
  let* ⟨prf,_⟩ ← block_spec
  let* ⟨publicSeed,_⟩ ← block_spec
  rw [generated_accepts p hp host threads pool secret prf publicSeed sk pk msg ctx rnd ks ps hc]
  exact (WP.spec_ok _).mpr rfl

end
end slhdsa.WidthEight
