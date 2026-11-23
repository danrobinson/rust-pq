module
public import Kappleouter.Types
public import Kappleone.Funs
public import Kapplebulk.Funs
@[expose] public section
namespace KappleouterRust
abbrev shake256.parallel.blocks := KapplebulkRust.shake256.parallel.blocks
abbrev shake256.parallel.single := KappleoneRust.shake256.parallel.single
end KappleouterRust
