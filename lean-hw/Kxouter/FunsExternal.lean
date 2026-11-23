module
public import Kxouter.Types
public import Kgridbulk.Funs
public import Keccakscalar.Funs
@[expose] public section
namespace KxouterRust
abbrev sha256.x86.avx512_available := GatherRust.sha256.x86.avx512_available
abbrev shake256.stream_x86.blocks := KgridbulkRust.shake256.stream_x86.blocks
abbrev shake256.round := KeccakScalarRust.shake256.round
end KxouterRust
