import Cachepath.NativeVerify.WotsRecover
import Shakebatch.WotsDispatch
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.NativeVerify.Wots
open ShakeBatch
set_option linter.concreteInstances false
variable [machine : Machine] [accelerator : Dispatch machine] [stream : Stream]

def dispatch
  (available : Std.Usize → Result Bool) {N : Std.Usize} (sig : Slice Std.U8) (msg : Array Std.U8 N)
  (seed : Array Std.U8 N) (adrs : address.Adrs) :
  Result (Array Std.U8 N)
  := do
  let digits ← wots.wots_digits msg
  let b ← available N
  if b
  then let s := alloc.vec.Vec.deref digits
       recover sig seed adrs s
  else
    let a ← address.Adrs.with_type adrs address.WOTS_PK
    let a1 ← address.Adrs.with_keypair a adrs.keypair
    let pk ← shake.hash.start seed a1
    let pk1 ←
      shake.wots.wots_pk_from_sig_loop sig seed adrs.layer adrs.tree
        adrs.typ adrs.keypair adrs.word2 adrs.word3 digits pk 0#usize
    shake.hash.digest N pk1


variable [StreamCorrect] (available : Usize → Result Bool)

theorem dispatch_spec {N : Usize} (p : slhdsa.params.Params) (hp : PN p N)
    (sig : Slice U8) (m seed : Array U8 N) (a : address.Adrs) (size : N.val*(2*N.val+3)≤sig.length)
    (domain : a.typ=address.WOTS_HASH ∧ a.word2=0#u32 ∧ a.word3=0#u32)
    (on : Bool) (select : available N=.ok on) (perms : on=true → ActiveCorrect machine accelerator.permute)
    (positive : on=true → 0<machine.width.val) :
    dispatch available sig m seed a ⦃ out => bytes out.val =
      Spec.wotsPkFromSig (Shake.params p) (bytes sig.val) (bytes m.val) (bytes seed.val) (adrsS a) ⦄ := by
  cases on with
  | false =>
    convert Shake.wots_pk_from_sig_spec p hp sig m seed a size using 1
    unfold dispatch slhdsa.shake.wots.wots_pk_from_sig
    simp only [select,bind_ok,Bool.false_eq_true,ite_false]
  | true =>
    unfold dispatch
    let* ⟨ds,hd,len,small⟩ ← wots_digits_spec p hp m
    have view : ds.deref=ds.slice := by apply Slice.ext;simp [alloc.vec.Vec.deref,Slice.from_val];rfl
    have hn := hp.le32
    have actual : ds.slice.length=2*N.val+3 := len
    simp only [select,bind_ok,ite_true,view]
    let* ⟨out,hash⟩ ← recover_spec p hp sig seed a ds.slice (positive rfl) (perms rfl) (by omega)
      (fun i hi=>by have := digits_bound ds small i hi;omega) (by simpa only [actual,Nat.mul_comm (2*N.val+3)] using size) domain
    change nats ds.val = Spec.wotsDigits (Shake.params p) (bytes m.val) at hd
    change bytes out.val = Spec.shake256 ((bytes seed.val ++ (Spec.wotsPkAdrs (adrsS a)).bytes) ++
      (List.range (Shake.params p).len).flatMap (fromSigStep _ _ _ _ (Spec.wotsDigits _ _))) (Shake.params p).n
    rw [hash,show (Shake.params p).len=ds.slice.length from hp.len.trans actual.symm,show (Shake.params p).n=N.val from hp.n,← hd]
    apply congrArg (fun xs => Spec.shake256 ((bytes seed.val ++ (Spec.wotsPkAdrs (adrsS a)).bytes) ++ xs) N.val)
    apply List.flatMap_congr
    intro i hi
    have bound : i<ds.val.length := List.mem_range.mp hi
    simp only [recoveredChain,fromSigStep,Spec.block,nats_getElem! _ _ bound,
      show (Shake.params p).n=N.val from hp.n,show (Shake.params p).w=16 from w_eq p,bytes_take,bytes_drop]
    rfl

end slhdsa.NativeVerify.Wots
