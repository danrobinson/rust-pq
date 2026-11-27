import Parallel.KeygenWidthThree
import Shakebatch.WidthThreeNative
open Aeneas Aeneas.Std Result
namespace slhdsa.ParallelKeygenHost
noncomputable section

private theorem keygen_eq {N : Usize} (p : params.Params) (hp : PN p N) (threads : Nat)
    (pool : PoolOutcome) (secret prf publicSeed : Array U8 N) (sk pk : Slice U8)
    (ks : sk.length=4*N.val) (ps : pk.length=2*N.val) :
    @Sh.shake.slh.slh_keygen_internal linuxNarrow ⟨false,threads,pool⟩ N p secret prf publicSeed sk pk =
      WidthThreeKeygenSDK.slhdsa.shake.slh.slh_keygen_internal p secret prf publicSeed sk pk := by
  obtain ⟨⟨s1,p1⟩,parallel,values,_,_⟩ := spec_imp_exists
    (linux_narrow_keys p hp threads pool secret prf publicSeed sk pk ks ps)
  obtain ⟨⟨s2,p2⟩,serial,expected,_,_⟩ := spec_imp_exists
    (WidthThreeKeygenSDK.slhdsa.Shake.slh_keygen_internal_spec p hp secret prf publicSeed sk pk ks ps)
  have eq := values.trans expected.symm
  rw [parallel,serial]
  have hs : s1=s2 := by apply Slice.ext; exact (bytes_inj _ _).mp (congrArg Prod.fst eq)
  have hp' : p1=p2 := by apply Slice.ext; exact (bytes_inj _ _).mp (congrArg Prod.snd eq)
  rw [hs,hp']

def linuxGenerateSignVerify {N : Usize} (threads : Nat) (pool : PoolOutcome)
    (sign : Slice U8 → Slice U8 → Slice U8 → Array U8 N → Result (Option (alloc.vec.Vec U8)))
    (p : params.Params) (secret prf publicSeed : Array U8 N) (sk pk msg ctx : Slice U8)
    (rnd : Array U8 N) : Result Bool := do
  let (secretKey, publicKey) ← @Sh.shake.slh.slh_keygen_internal linuxNarrow ⟨false,threads,pool⟩
    N p secret prf publicSeed sk pk
  let signature ← sign msg ctx secretKey rnd
  match signature with
  | none => ok false
  | some sig => WidthThreeVerifySDK.ShakeoptSeg.shake.slh.slh_verify N p msg sig.deref ctx publicKey

theorem linux_narrow_serial_sign_roundtrip {N : Usize} (p : params.Params) (hp : PN p N) (threads : Nat)
    (pool : PoolOutcome) (secret prf publicSeed : Array U8 N) (sk pk msg ctx : Slice U8) (rnd : Array U8 N)
    (ks : sk.length=4*N.val) (ps : pk.length=2*N.val) (hc : ctx.length≤255) :
    linuxGenerateSignVerify threads pool (WidthThreeLinuxSDK.WidthThreeSDK.ShakeoptSeg.shake.slh.slh_sign
      WidthThree.linuxSigning p) p secret prf publicSeed sk pk msg ctx rnd = ok true := by
  unfold linuxGenerateSignVerify
  rw [keygen_eq p hp threads pool secret prf publicSeed sk pk ks ps]
  exact WidthThree.linux_serial_roundtrip p hp secret prf publicSeed sk pk msg ctx rnd ks ps hc

theorem linux_narrow_parallel_sign_roundtrip (w : WidthThree.PublishedWorker) {N : Usize}
    (p : params.Params) (hp : PN p N) (threads : Nat) (pool : PoolOutcome)
    (secret prf publicSeed : Array U8 N) (sk pk msg ctx : Slice U8) (rnd : Array U8 N)
    (ks : sk.length=4*N.val) (ps : pk.length=2*N.val) (hc : ctx.length≤255) :
    linuxGenerateSignVerify threads pool (WidthThreeParallel.ShakeoptSeg.shake.slh.slh_sign
      (WidthThree.linuxParallel w) p) p secret prf publicSeed sk pk msg ctx rnd = ok true := by
  unfold linuxGenerateSignVerify
  rw [keygen_eq p hp threads pool secret prf publicSeed sk pk ks ps]
  exact WidthThree.linux_worker_roundtrip w p hp secret prf publicSeed sk pk msg ctx rnd ks ps hc

end
end slhdsa.ParallelKeygenHost
