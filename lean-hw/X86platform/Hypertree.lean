import Armplatform.Replay
import X86key.Node
import X86stream.Top
import Slhdsa.Proofs.Ht

open Aeneas Aeneas.Std Result
namespace slhdsa.X86.Platform

def node {N : Usize} (sk : Array U8 N) (i z : U32) (s : hash.Seed N) (a : address.Adrs) :=
  X86KeyRust.xmss.xmss_node sk i z ⟨s.pk_seed,s.state,s.state512⟩
    ⟨a.layer,a.tree,a.typ,a.keypair,a.word2,a.word3⟩

theorem node_spec {N : Usize} (p : params.Params) (hp : PN p N) (sk : Array U8 N)
    (i z : U32) (s : hash.Seed N) (hs : SeedOk s) (a : address.Adrs)
    (within : (i.val+1)*2^z.val ≤ 2^p.hp.val) :
    node sk i z s a ⦃ out => bytes out.val = Spec.xmssNode (paramsS p) (bytes sk.val)
      i.val z.val (bytes s.pk_seed.val) (adrsS a) ⦄ :=
  Key.node_fips p hp sk ⟨s.pk_seed,s.state,s.state512⟩ hs
    ⟨a.layer,a.tree,a.typ,a.keypair,a.word2,a.word3⟩ z.val i z rfl within

def recover {N : Usize} (sig : Slice U8) (m : Array U8 N) (s : hash.Seed N) (a : address.Adrs) :=
  WotsApiRust.wots.wots_pk_from_sig sig m ⟨s.pk_seed,s.state,s.state512⟩
    ⟨a.layer,a.tree,a.typ,a.keypair,a.word2,a.word3⟩

theorem recover_spec {N : Usize} (p : params.Params) (hp : PN p N) (sig : Slice U8)
    (m : Array U8 N) (s : hash.Seed N) (hs : SeedOk s) (a : address.Adrs)
    (room : N.val*(2*N.val+3) ≤ sig.length) :
    recover sig m s a ⦃ out => bytes out.val = Spec.wotsPkFromSig (paramsS p)
      (bytes sig.val) (bytes m.val) (bytes s.pk_seed.val) (adrsS a) ⦄ :=
  Wots.Api.recover_fips p hp sig m _ _ hs room

theorem chains_spec (N : Usize) (hN : N.val ≤ 32) (state : Array U32 8#usize)
    (blocks : Slice (Array U8 64#usize)) (start «end» : Slice U32)
    (hs : blocks.length ≤ start.length) (he : blocks.length ≤ «end».length) :
    WotsApiRust.sha256.x86.chain_blocks N state blocks start «end» ⦃ r =>
      r.length = blocks.length ∧ ∀ i, i < blocks.length → bytes (r.val[i]!).val =
        runBlock N.val (wv state.val) (bytes (blocks.val[i]!).val) (start.val[i]!).val
          («end».val[i]!).val ⦄ := by
  rw [Wots.Api.chain_eq]
  exact chain_blocks_spec N hN state blocks start «end» hs he

end slhdsa.X86.Platform

open Lean Elab Command
def X86Platform.primitives : List (Name × Name) :=
    [(`slhdsa.xmss.xmss_node, `slhdsa.X86.Platform.node),
     (`slhdsa.xmss_tree_node_spec, `slhdsa.X86.Platform.node_spec),
     (`slhdsa.wots.wots_pk_from_sig, `slhdsa.X86.Platform.recover),
     (`slhdsa.wots_pk_from_sig_spec, `slhdsa.X86.Platform.recover_spec),
     (`slhdsa.hash.chain_blocks, `WotsApiRust.sha256.x86.chain_blocks),
     (`slhdsa.chain_blocks_spec, `slhdsa.X86.Platform.chains_spec),
     (`slhdsa.sha256.compress, `X86RemainderRust.sha256.compress),
     (`slhdsa.compress_spec, `slhdsa.X86.Stream.single256),
     (`slhdsa.sha512.compress, `X86RemainderRust.sha512.compress),
     (`slhdsa.S512.compress_spec, `slhdsa.X86.Stream.single512),
     (`slhdsa.sha256.sha256_from, `X86StreamRust.sha256.sha256_from),
     (`slhdsa.sha256_from_spec, `slhdsa.X86.Stream.stream256),
     (`slhdsa.sha512.sha512_from, `X86StreamRust.sha512.sha512_from),
     (`slhdsa.S512.sha512_from_spec, `slhdsa.X86.Stream.stream512)]

set_option maxHeartbeats 0 in
run_cmd liftCoreM do
  PlatformProof.replay `X86Platform X86Platform.primitives #[`slhdsa.ht_sign_spec, `slhdsa.ht_verify_spec]

#print axioms X86Platform.slhdsa.ht_sign_spec
#print axioms X86Platform.slhdsa.ht_verify_spec
