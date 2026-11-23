module
public import Parentx86.Types
public import Parentdriver.Model
public import Gather512.Funs
public import Parent512.Funs
@[expose] public section
open Aeneas Aeneas.Std Result
namespace Parentx86Rust
abbrev address.Adrs.with_word3 := slhdsa.address.Adrs.with_word3
abbrev sha512.parents.parent_block := slhdsa.PlatformParent.Driver.makeBlock
abbrev sha256.x86.avx512_available := GatherRust.sha256.x86.avx512_available
abbrev sha512.x86.compress_parents {N : Usize} := @ParentsRust.sha512.x86.compress_parents N
end Parentx86Rust
