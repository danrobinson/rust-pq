module
public import Chainx86.Types
public import Chainwide.Funs
public import Chainavx2.Funs
@[expose] public section
open Aeneas Aeneas.Std Result
namespace ChainX86Rust
abbrev hash.chain_blocks_portable := slhdsa.hash.chain_blocks_portable
abbrev sha256.x86.avx2.chains := ChainAvx2Rust.sha256.x86.avx2.chains
abbrev sha256.x86.avx512.chains := ChainWideRust.sha256.x86.avx512.chains
abbrev sha256.x86.chains := ChainNiRust.sha256.x86.chains
abbrev sha256.x86.sha_ni.get := ChainWideRust.sha256.x86.sha_ni.get
def sha256.x86.has_avx512.get : Result Bool := ok GatherRust.avx512Available
/-- Runtime detection is a fixed CPU/OS input. Both results are covered. -/
opaque avx2Available : Bool
def sha256.x86.has_avx2.get : Result Bool := ok avx2Available
end ChainX86Rust
