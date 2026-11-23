module
public import X86key.Types
public import Wotsapi.FunsExternal
public import Xmssroot.Funs
@[expose] public section
open Aeneas Aeneas.Std Result
namespace X86KeyRust

def rootSeed {N} (s : hash.Seed N) : XmssRootRust.hash.Seed N := ⟨s.pk_seed,s.state,s.state512⟩
def rootAddr (a : address.Adrs) : XmssRootRust.address.Adrs := ⟨a.layer,a.tree,a.typ,a.keypair,a.word2,a.word3⟩
def wideSeed {N} (s : hash.Seed N) : WotsWideRust.hash.Seed N := ⟨s.pk_seed,s.state,s.state512⟩
def wideAddr (a : address.Adrs) : WotsWideRust.address.Adrs := ⟨a.layer,a.tree,a.typ,a.keypair,a.word2,a.word3⟩

def xmss.hash2 {N} (s : hash.Seed N) (a : address.Adrs) := XmssRootRust.xmss.hash2 (rootSeed s) (rootAddr a)
def xmss.wide.batch_root {N} (sk : Array U8 N) (i z : U32) (s : hash.Seed N) (a : address.Adrs) :=
  XmssRootRust.xmss.wide.batch_root sk i z (rootSeed s) (rootAddr a)
def hash.thash_values {N} (s : hash.Seed N) (a : address.Adrs) := WotsWideRust.hash.thash_values (wideSeed s) (wideAddr a)
abbrev sha256.x86.chain_blocks := WotsApiRust.sha256.x86.chain_blocks
abbrev sha256.x86.avx512_available := WotsApiRust.sha256.x86.avx512_available
abbrev sha256.compress := X86RemainderRust.sha256.compress
abbrev sha512.compress := X86RemainderRust.sha512.compress

def core.ops.range.RangeInclusive.contains {I U : Type _} (_ : core.cmp.PartialOrd I I)
    (lower : core.cmp.PartialOrd I U) (upper : core.cmp.PartialOrd U I)
    (r : core.ops.range.RangeInclusive I) (x : U) : Result Bool :=
  if r.exhausted then ok false else do
    let allowed ← lower.le r.start x
    if allowed then upper.le x r.end else ok false

end X86KeyRust
