module
public import Kavx.Types
public import Platform.FunsExternal
@[expose] public section
open Aeneas Aeneas.Std Result
namespace KavxRust
def core.core_arch.x86.avx512f._mm512_ternarylogic_epi64 (imm : I32) (a : core.core_arch.x86.__m512i) (b : core.core_arch.x86.__m512i) (c : core.core_arch.x86.__m512i) : Result core.core_arch.x86.__m512i := ok (fun j => slhdsa.X86.ternary (imm.bv.toNat%256) (a j) (b j) (c j))
def core.core_arch.x86.avx512f._mm512_rol_epi64 (imm : I32) (a : core.core_arch.x86.__m512i) : Result core.core_arch.x86.__m512i := ok (fun j => (a j).rotateLeft (imm.bv.toNat%64))
def core.core_arch.x86.avx512f._mm512_xor_si512 (a : core.core_arch.x86.__m512i) (b : core.core_arch.x86.__m512i) : Result core.core_arch.x86.__m512i := ok (fun j => a j ^^^ b j)
def core.core_arch.x86.avx512f._mm512_set1_epi64 (signed : I64) : Result core.core_arch.x86.__m512i := ok (fun _ => signed.bv)
end KavxRust
