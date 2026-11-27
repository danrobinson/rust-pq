import Shakebatch.WidthThree
import Cachepath.NativeVerify.Hosted
import Parallel.SegmentedCaller
open Aeneas Aeneas.Std Result
namespace slhdsa.WidthThree
set_option linter.concreteInstances false
noncomputable section

/-- The two remaining WOTS certificates, restricted to normalized FIPS leaf addresses. -/
structure Certified where
  ops : Wots
  laws : WotsCorrect ops

abbrev signXmss (c : Certified) := @shake.xmss.xmss_sign c.ops
abbrev signXmssSpec (c : Certified) := @xmss_sign_spec c.ops c.laws
abbrev recoverXmss (_ : Certified) := @CacheopsRust.NativeVerifier.xmssPk NativeVerify.linuxRecovery
abbrev recoverXmssSpec (_ : Certified) := @CacheopsRust.NativeVerifier.xmssSpec NativeVerify.linuxRecovery

open Lean Meta Elab Command in
set_option Elab.async false in
set_option maxHeartbeats 0 in
run_cmd liftTermElabM do
  let names ← IO.mkRef (Std.HashMap.ofList [
    (`slhdsa.shake.xmss.xmss_sign,`slhdsa.WidthThree.signXmss),
    (`slhdsa.Shake.xmss_sign_spec,`slhdsa.WidthThree.signXmssSpec),
    (`slhdsa.shake.xmss.xmss_pk_from_sig,`slhdsa.WidthThree.recoverXmss),
    (`slhdsa.Shake.xmss_pk_from_sig_spec,`slhdsa.WidthThree.recoverXmssSpec)])
  let root := `slhdsa.Shake.ht_sign_spec
  let actual ← CacheopsRust.NativeVerifier.abstractCalls `WidthThreeTree [`Slhdsa] root names `slhdsa.WidthThree.Certified
  unless actual == `WidthThreeTree ++ root do throwError "width-three hypertree substitution missed its root"

/-- The live uncached FORS signer has its own active-lane scheduler. -/
structure ForsSigner where
  run {N : Usize} : slhdsa.params.Params → Slice U8 → Array U8 N → Array U8 N → address.Adrs → Result (alloc.vec.Vec U8)
  correct {N : Usize} (p : slhdsa.params.Params) (hp : PN p N) (md : Slice U8)
    (sk seed : Array U8 N) (a : address.Adrs) (size : md.length=(p.k.val*p.a.val+7)/8)
    (domain : a.typ=address.FORS_TREE ∧ a.word2=0#u32 ∧ a.word3=0#u32) :
    run p md sk seed a ⦃ r => bytes r.val=Spec.forsSign (Shake.params p) (bytes md.val)
      (bytes sk.val) (bytes seed.val) (adrsS a) ∧ r.length=p.k.val*(1+p.a.val)*N.val ⦄

@[instance_reducible] def fallback (c : Certified) (f : ForsSigner) : ParallelCaller.Sh.Fallback where
  forsSign := f.run
  forsRecover := NativeVerify.linuxRecovery.fors
  htSign := WidthThreeTree.slhdsa.shake.ht.ht_sign c

theorem fallback_spec (c : Certified) (f : ForsSigner) {N : Usize} (p : slhdsa.params.Params) (hp : PN p N) :
    ParallelCaller.Sh.FallbackCorrect (fallback c f) (N:=N) p :=
  ⟨f.correct p hp, NativeVerify.linuxRecovery.fors_spec p hp, WidthThreeTree.slhdsa.Shake.ht_sign_spec c p hp⟩

theorem parallel_sign_spec (c : Certified) (f : ForsSigner) [worker : ParallelCaller.Worker ParallelCaller.ShakeSeed]
    {N : Usize} (p : slhdsa.params.Params) (hp : PN p N) (m sk : Slice U8) (rnd : Array U8 N)
    (hsk : sk.length=4*N.val) (slots : ParallelCaller.WorkerCorrect worker (N:=N) p (Shake.params p)
      (fun s => bytes s.val) (fun _ => True)) :
    @ParallelCaller.Sh.shake.slh.slh_sign_internal (fallback c f) worker N p m sk rnd ⦃ out =>
      bytes out.val=Spec.slhSignInternal (Shake.params p) (bytes m.val) (bytes sk.val) (bytes rnd.val) ∧
      out.length=(Shake.params p).sigBytes ⦄ :=
  @ParallelCaller.Sh.sign_spec (fallback c f) worker N p hp m sk rnd hsk (fallback_spec c f p hp) slots

theorem parallel_context_spec (c : Certified) (f : ForsSigner) [worker : ParallelCaller.Worker ParallelCaller.ShakeSeed]
    {N : Usize} (p : slhdsa.params.Params) (hp : PN p N) (m ctx sk : Slice U8) (rnd : Array U8 N)
    (hsk : sk.length=4*N.val) (hc : ctx.length≤255)
    (slots : ParallelCaller.WorkerCorrect worker (N:=N) p (Shake.params p) (fun s => bytes s.val) (fun _ => True)) :
    @ParallelCaller.Sh.shake.slh.shake_sign_ctx (fallback c f) worker N p m ctx sk rnd ⦃ out =>
      bytes out.val=Spec.slhSignInternal (Shake.params p) (Spec.withContext (bytes m.val) (bytes ctx.val))
        (bytes sk.val) (bytes rnd.val) ∧ out.length=(paramsS p).sigBytes ⦄ :=
  @ParallelCaller.Sh.sign_ctx_spec (fallback c f) worker N p hp m ctx sk rnd hsk hc (fallback_spec c f p hp) slots

end
end slhdsa.WidthThree
