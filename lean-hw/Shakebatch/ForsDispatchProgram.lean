import Shakebatch.Recover
import Shakebatch.Sign
open Aeneas Aeneas.Std Result ControlFlow Error
open slhdsa
namespace slhdsa.ShakeBatch
set_option linter.concreteInstances false
noncomputable section
variable [machine : Machine] [stream : Stream] (available : Usize → Result Bool)

def shake.fors.fors_sign
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
    shake.fors_batch.sign p s sk_seed seed adrs
  else
    shake.fors.fors_sign_loop0 p.k sk_seed seed adrs p.a indices
      (alloc.vec.Vec.new Std.U8) 0#u32

def shake.fors.fors_pk_from_sig
  {N : Std.Usize} (p : params.Params) (sig : Slice Std.U8) (md : Slice Std.U8)
  (seed : Array Std.U8 N) (adrs : address.Adrs) :
  Result (Array Std.U8 N)
  := do
  let i ← lift (UScalar.cast .Usize p.k)
  let indices ← util.base_2b md p.a i
  let b ← available N
  if b
  then
    let s := alloc.vec.Vec.deref indices
    shake.fors_batch.recover p s sig seed adrs
  else
    let a ← address.Adrs.with_type adrs address.FORS_ROOTS
    let a1 ← address.Adrs.with_keypair a adrs.keypair
    let roots ← shake.hash.start seed a1
    let roots1 ←
      shake.fors.fors_pk_from_sig_loop p.a sig seed adrs.layer adrs.tree
        adrs.typ adrs.keypair adrs.word2 adrs.word3 indices roots 0#usize
    shake.hash.digest N roots1
end
end slhdsa.ShakeBatch
