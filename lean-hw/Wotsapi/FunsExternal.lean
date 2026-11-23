module
public import Wotsapi.Types
public import Wotswide.Funs
public import Chainx86.Funs
@[expose] public section
open Aeneas Aeneas.Std Result
namespace WotsApiRust
def wideAddress (a : address.Adrs) : WotsWideRust.address.Adrs :=
  ⟨a.layer,a.tree,a.typ,a.keypair,a.word2,a.word3⟩
def wideSeed {N} (s : hash.Seed N) : WotsWideRust.hash.Seed N := ⟨s.pk_seed,s.state,s.state512⟩
abbrev sha256.x86.avx512_available := WotsX86Rust.sha256.x86.avx512_available
abbrev sha256.x86.chain_blocks := ChainX86Rust.sha256.x86.chain_blocks
def hash.thash_values {N} (seed : hash.Seed N) (a : address.Adrs) :=
  WotsWideRust.hash.thash_values (wideSeed seed) (wideAddress a)
def wots.wide.recover {N} (seed : hash.Seed N) (a : address.Adrs) :=
  WotsWideRust.wots.wide.recover (wideSeed seed) (wideAddress a)
end WotsApiRust
