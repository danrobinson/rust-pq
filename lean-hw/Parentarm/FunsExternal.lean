module
public import Parentarm.Types
public import Parentdriver.Model
public import Paired.Funs
@[expose] public section
open Aeneas Aeneas.Std Result
namespace ParentarmRust
abbrev address.Adrs.with_word3 := slhdsa.address.Adrs.with_word3
abbrev sha512.parents.parent_block := slhdsa.PlatformParent.Driver.makeBlock
abbrev sha512.hw.arm.available := ok Arm.haveSha512
abbrev sha512.paired.compress_parents {N : Usize} := @PairedRust.sha512.paired.compress_parents N
end ParentarmRust
