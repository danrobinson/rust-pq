import X86platform.Hypertree
import Armplatform.ForsLoops
import Xfors.Top
open Lean Elab Command

set_option maxHeartbeats 0 in
run_cmd liftCoreM do
  PlatformProof.replay `X86NativeLoops X86Platform.primitives
    #[`slhdsa.PlatformFors.x86TreeLoopSpec, `slhdsa.PlatformFors.x86PathLoopSpec]

def X86Platform.forsLoops : List (Name × Name) :=
  [(`slhdsa.fors.fors_batch_loop3, `X86NativeLoops.slhdsa.PlatformFors.x86TreeLoop),
   (`slhdsa.fors_batch_loop3_spec, `X86NativeLoops.slhdsa.PlatformFors.x86TreeLoopSpec),
   (`slhdsa.fors.fors_pk_from_sig_loop2, `X86NativeLoops.slhdsa.PlatformFors.x86PathLoop),
   (`slhdsa.fors_pk_from_sig_loop2_spec, `X86NativeLoops.slhdsa.PlatformFors.x86PathLoopSpec)]

set_option maxHeartbeats 0 in
run_cmd liftCoreM do
  PlatformProof.replay `X86Fallback (X86Platform.primitives ++ X86Platform.forsLoops)
    #[`slhdsa.fors_batch_spec]

open Aeneas Aeneas.Std Result
namespace slhdsa.X86.Platform

def subtree {N : Usize} (sk : Array U8 N) (i z : U32) (s : hash.Seed N) (a : address.Adrs) :=
  XForsRust.fors.wide.subtree sk i z ⟨s.pk_seed,s.state,s.state512⟩
    ⟨a.layer,a.tree,a.typ,a.keypair,a.word2,a.word3⟩

-- Charon duplicates the fallback below all three guards. The independent
-- extraction gate checks this factorization by definitional equality.
noncomputable def batch {N : Usize} (sk : Array U8 N) (i z : U32) (s : hash.Seed N) (a : address.Adrs) :
    Result (Array U8 N) := do
  let fallback := X86Fallback.slhdsa.fors.fors_batch sk i z s a
  if z >= 3#u32 then
    let supported ← match N.val with
      | 16 => ok true
      | 24 => ok true
      | 32 => ok true
      | _ => ok false
    if supported then
      let available ← WotsApiRust.sha256.x86.avx512_available
      if available then subtree sk i z s a else fallback
    else fallback
  else fallback

theorem batch_spec {N : Usize} (p : params.Params) (hp : PN p N) (sk : Array U8 N) (i z : U32)
    (seed : hash.Seed N) (hs : SeedOk seed) (a : address.Adrs) (hz : z.val ≤ 7)
    (h : (i.val+1)*2^z.val < 2^32) :
    batch sk i z seed a ⦃ out => bytes out.val = Spec.forsNode (paramsS p) (bytes sk.val)
      i.val z.val (bytes seed.pk_seed.val) (adrsS a) ⦄ := by
  have fallback := X86Fallback.slhdsa.fors_batch_spec p hp sk i z seed hs a hz h
  unfold batch
  split
  · rename_i height
    cases cpu : GatherRust.avx512Available with
    | false =>
      rcases hp.nok with w|w|w <;> simpa only [w,bind_ok,WotsApiRust.sha256.x86.avx512_available,
        WotsX86Rust.sha256.x86.avx512_available,WotsX86Rust.sha256.x86.has_avx512.get,
        GatherRust.sha256.x86.avx512_available,cpu,Bool.false_eq_true,ite_false,ite_true] using fallback
    | true =>
      have wide := Fors.subtree_fips p hp ⟨seed.pk_seed,seed.state,seed.state512⟩ hs sk
        ⟨a.layer,a.tree,a.typ,a.keypair,a.word2,a.word3⟩ i z (by scalar_tac) hz cpu (Nat.le_of_lt h)
      rcases hp.nok with w|w|w <;> simpa only [w,bind_ok,WotsApiRust.sha256.x86.avx512_available,
        WotsX86Rust.sha256.x86.avx512_available,WotsX86Rust.sha256.x86.has_avx512.get,
        GatherRust.sha256.x86.avx512_available,cpu,ite_true,subtree,Fors.addressOf,TreeHash.addr,XForsRust.scalarAddr,adrsS] using wide
  · exact fallback

end slhdsa.X86.Platform

def X86Platform.calls : List (Name × Name) :=
  X86Platform.primitives ++ X86Platform.forsLoops ++
    [(`slhdsa.fors.fors_batch, `slhdsa.X86.Platform.batch),
     (`slhdsa.fors_batch_spec, `slhdsa.X86.Platform.batch_spec)]

set_option maxHeartbeats 0 in
run_cmd liftCoreM do
  PlatformProof.replay `X86Core X86Platform.calls #[`slhdsa.fors_sign_spec, `slhdsa.fors_pk_from_sig_spec]
