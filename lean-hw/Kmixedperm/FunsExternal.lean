module
public import Kmixedperm.Types
public import Kmixed.Funs
@[expose] public section
open Aeneas Aeneas.Std Result
namespace KmixedpermRust
open core.core_arch.arm_shared.neon
namespace core.core_arch.arm_shared.neon.generated
def vcreate_u64 (w : U64) : Result uint64x1_t := ok w.bv
def vcombine_u64 (lo hi : uint64x1_t) : Result uint64x2_t := ok fun j => if j.val=0 then lo else hi
def vgetq_lane_u64 (i : I32) (v : uint64x2_t) : Result U64 :=
  if h : i.bv.toNat<2 then ok ⟨v ⟨i.bv.toNat,h⟩⟩ else fail .undef
end core.core_arch.arm_shared.neon.generated
-- Both extraction units contain the same Rust struct. Convert its two fields directly.
def native (a : Array shake256.parallel.mixed.V 25#usize) : Array KmixedRust.shake256.parallel.mixed.V 25#usize :=
  Array.from (a.val.map fun x => ⟨x.pair,x.scalar⟩) (by simp)
def localRows (a : Array KmixedRust.shake256.parallel.mixed.V 25#usize) : Array shake256.parallel.mixed.V 25#usize :=
  Array.from (a.val.map fun x => ⟨x.pair,x.scalar⟩) (by simp)
def shake256.parallel.mixed.round (a : Array shake256.parallel.mixed.V 25#usize) (rc : U64) := do
  let r ← KmixedRust.shake256.parallel.mixed.round (native a) rc
  ok (localRows r)
end KmixedpermRust
