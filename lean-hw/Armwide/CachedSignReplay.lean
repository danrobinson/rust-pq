import Lean

open Lean Elab Command
namespace slhdsa.CachedArm.Replay

/-- Re-elaborate the cache invariant and loop proof against the source-linked
Arm primitives. The additional address premises are constructed at the exact
two cache-hit sites and at the FORS address constructor. -/
def specialize (proof : String) : String := Id.run do
  let mut code := proof
  for call in ["cache.sha2_ops.sign_from_digest","hash.seed_ctx","wots.wots_sign",
      "fors.fors_sign","fors.fors_pk_from_sig","xmss.xmss_sign","xmss.xmss_pk_from_sig"] do
    code := code.replace ("CacheopsRust."++call) ("ArmCached.CacheopsRust."++call)
  for name in ["sign_from_digest_loop_spec","sign_from_digest_spec","sign_from_digest_with_cache_spec"] do
    code := code.replace ("theorem "++name++" {") ("theorem "++name++
      " [cpu : Armwide.Public.Dispatcher.Cpu] [features : Armwide.Keygen.Features] {")
  code := code.replace "slhdsa.xmss_sign_spec" "Armwide.XmssLeaves.Signer.xmss_sign_spec"
  code := code.replace "slhdsa.xmss_pk_from_sig_spec" "Armwide.Hypertree.xmss_pk_from_sig_spec"
  code := code.replace "slhdsa.fors_pk_from_sig_spec" "WideFors.dispatch_fips cpu.wide features.sha512 features.sha512"
  code := code.replace "slhdsa.fors_sign_spec" "ArmForsTree.Entry.fors_sign_spec"
  code := code.replace "hseed_ok _ (by rw [hmd_len, hi_eq]; rfl) as ⟨sig_fors"
    "hseed_ok (toSlhAdrs ⟨0#u32,idx_tree,CacheopsRust.address.FORS_TREE,idx_leaf,0#u32,0#u32⟩) (by with_unfolding_all rfl) (by rw [hmd_len, hi_eq]; rfl) as ⟨sig_fors"
  code := code.replace "slhdsa.wots_sign_spec (toSlhParams p) hp curRoot sk_seed (toSlhSeed seed) hs"
    "normalized_wots (toSlhParams p) hp curRoot sk_seed (toSlhSeed seed) hs"
  return code

private def scalarProof := include_str "../Cachepath/EndToEnd.lean"

def emit (start stop : String) : CommandElabM Unit := do
  let [_,tail] := scalarProof.splitOn start | throwError "expected one cache theorem start, {start}"
  let [body,_] := tail.splitOn stop | throwError "expected one cache theorem end, {stop}"
  let src := specialize (start++body)
  let .ok stx := Parser.runParserCategory (← getEnv) `command src
    | throwError "failed to parse Arm cache replay for {start}"
  elabCommand stx

end slhdsa.CachedArm.Replay
