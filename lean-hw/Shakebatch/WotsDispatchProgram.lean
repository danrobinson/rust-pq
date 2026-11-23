import Shakebatch.WotsSignProgram
import Shakebatch.WotsKeyProgram
import Slhdsa.Proofs.ShakeWots
open Aeneas Aeneas.Std Result
namespace slhdsa.ShakeBatch
variable [machine : Machine] [stream : Stream]

def shake.wots.wots_pk_gen
  (available : Std.Usize → Result Bool) {N : Std.Usize} (sk : Array Std.U8 N) (seed : Array Std.U8 N)
  (adrs : address.Adrs) :
  Result (Array Std.U8 N)
  := do
  let b ← available N
  if b
  then shake.batch.keygen sk seed adrs
  else
    let a ← address.Adrs.with_type adrs address.WOTS_PK
    let a1 ← address.Adrs.with_keypair a adrs.keypair
    let pk ← shake.hash.start seed a1
    let pk1 ←
      shake.wots.wots_pk_gen_loop sk seed adrs.layer adrs.tree adrs.typ
        adrs.keypair adrs.word2 adrs.word3 pk 0#usize
    shake.hash.digest N pk1

def shake.wots.wots_sign
  (available : Std.Usize → Result Bool) {N : Std.Usize} (msg : Array Std.U8 N) (sk : Array Std.U8 N)
  (seed : Array Std.U8 N) (adrs : address.Adrs) :
  Result (alloc.vec.Vec Std.U8)
  := do
  let digits ← wots.wots_digits msg
  let b ← available N
  if b
  then let s := alloc.vec.Vec.deref digits
       shake.batch.sign sk seed adrs s
  else
    shake.wots.wots_sign_loop sk seed adrs digits (alloc.vec.Vec.new Std.U8)
      0#usize

def shake.wots.wots_pk_from_sig
  (available : Std.Usize → Result Bool) {N : Std.Usize} (sig : Slice Std.U8) (msg : Array Std.U8 N)
  (seed : Array Std.U8 N) (adrs : address.Adrs) :
  Result (Array Std.U8 N)
  := do
  let digits ← wots.wots_digits msg
  let b ← available N
  if b
  then let s := alloc.vec.Vec.deref digits
       shake.batch.recover sig seed adrs s
  else
    let a ← address.Adrs.with_type adrs address.WOTS_PK
    let a1 ← address.Adrs.with_keypair a adrs.keypair
    let pk ← shake.hash.start seed a1
    let pk1 ←
      shake.wots.wots_pk_from_sig_loop sig seed adrs.layer adrs.tree
        adrs.typ adrs.keypair adrs.word2 adrs.word3 digits pk 0#usize
    shake.hash.digest N pk1

end slhdsa.ShakeBatch
