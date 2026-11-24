module
public import Chainni.Types
@[expose] public section
open Aeneas Aeneas.Std Result
namespace ChainNiRust
abbrev hash.chain_blocks_portable := slhdsa.hash.chain_blocks_portable
abbrev sha256.x86.compress_pair := ShaNiRust.sha256.x86.compress_pair
namespace core.core_arch.x86.sse41
/-- Each immediate bit selects one 16-bit element from the second operand. -/
def _mm_blend_epi16 (imm : I32) (a b : slhdsa.Intel.Reg) : Result slhdsa.Intel.Reg :=
  let atWord := fun i =>
    let mask : BitVec 32 := (if imm.bv.getLsbD (2*i+1) then 0xffff0000 else 0) |||
      (if imm.bv.getLsbD (2*i) then 0xffff else 0)
    (slhdsa.Intel.get a i &&& ~~~mask) ||| (slhdsa.Intel.get b i &&& mask)
  ok ⟨atWord 0,atWord 1,atWord 2,atWord 3⟩
end core.core_arch.x86.sse41
end ChainNiRust
