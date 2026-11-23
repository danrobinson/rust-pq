module
public import Kspongel.Types
public import Koriented.Funs
public import Kbulk.Funs
@[expose] public section
namespace KspongeLRust
abbrev shake256.oriented.blocks := KbulkRust.shake256.oriented.blocks
abbrev shake256.oriented.permute := KorientedRust.shake256.oriented.permute
end KspongeLRust
