module
public import Armstream.Types
public import Chainavx2.Chunks
public import Slhdsa.Funs
@[expose] public section
open Aeneas Aeneas.Std Result
namespace ArmStreamRust

def core.slice.raw.from_ref {T : Type u} (x : T) : Result (Slice T) := ok (Slice.from [x] (by simp; scalar_tac))

def core.slice.Slice.as_chunks {T : Type u} (n : Usize) (b : Slice T) :=
  if n.val=0 then fail .panic else ok (ChainAvx2Rust.fullChunks n b,ChainAvx2Rust.remainder n b)

/-- RustCrypto's external block API is modeled by sequential verified portable
compressions. The driver proof assumes the linked backend implements this contract. -/
def sha2.sha256.compress256 (st : Array U32 8#usize) (blocks : Slice (Array U8 64#usize)) :=
  blocks.val.foldlM (fun s b => slhdsa.sha256.compress_portable s b.to_slice 0#usize) st

def sha2.sha512.compress512 (st : Array U64 8#usize) (blocks : Slice (Array U8 128#usize)) :=
  blocks.val.foldlM (fun s b => slhdsa.sha512.compress_portable s b.to_slice 0#usize) st

end ArmStreamRust
