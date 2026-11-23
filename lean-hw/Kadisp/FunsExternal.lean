module
public import Kadisp.Types
public import Kappleperm.Funs
public import Kneonperm.Funs
@[expose] public section
namespace KadispRust
abbrev shake256.parallel.sha3.permute := KapplepermRust.shake256.parallel.sha3.permute
abbrev shake256.parallel.neon.permute := KneonpermRust.shake256.parallel.neon.permute
end KadispRust
