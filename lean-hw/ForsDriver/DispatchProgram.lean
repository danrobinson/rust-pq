import ForsDriver.Program
import Cachepath.NativeVerify.ForsSignNodeProgram
open Aeneas Aeneas.Std Result
namespace slhdsa.ForsDriver
open NativeVerify
set_option linter.concreteInstances false

@[instance_reducible] def branches (k : Fused.Kernel)
    (node : {N : Usize} → Array U8 N → Array U8 N → address.Adrs → U32 → U32 → Result (Array U8 N)) : Trees where
  node := @node
  fallback := @ForsSign.descend (Fused.machine k) (@ForsFused.fused (Fused.machine k) k.active)
    (@ActiveHash.pair_active (Fused.machine k) k.active)

section
variable [kernel : Fused.Kernel] [trees : Trees]

def dispatched (available : Usize → Result Bool)
  {N : Std.Usize} (p : params.Params) (md : Slice Std.U8)
  (sk_seed : Array Std.U8 N) (seed : Array Std.U8 N) (adrs : address.Adrs) :
  Result (alloc.vec.Vec Std.U8)
  := do
  let i ← lift (UScalar.cast .Usize p.k)
  let indices ← util.base_2b md p.a i
  let b ← available N
  if b
  then
    let s := alloc.vec.Vec.deref indices
    sign p s sk_seed seed adrs
  else
    shake.fors.fors_sign_loop0 p.k sk_seed seed adrs p.a indices
      (alloc.vec.Vec.new Std.U8) 0#u32

theorem off_eq (available : Usize → Result Bool) {N : Usize} (p : params.Params)
    (md : Slice U8) (sk seed : Array U8 N) (a : address.Adrs) (off : available N=ok false) :
    dispatched available p md sk seed a=shake.fors.fors_sign p md sk seed a := by
  simp [dispatched,shake.fors.fors_sign,off,bind_ok]

end
end slhdsa.ForsDriver
