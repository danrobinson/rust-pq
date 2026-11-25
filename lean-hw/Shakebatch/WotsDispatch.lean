import Shakebatch.WotsDispatchProgram
import Shakebatch.WotsRecover
open Aeneas Aeneas.Std Result
namespace slhdsa.ShakeBatch
set_option linter.concreteInstances false
set_option maxHeartbeats 1100000
variable [machine : Machine] [stream : Stream] [correct : StreamCorrect]
variable (available : Usize → Result Bool)

theorem wots_pk_gen_spec {N : Usize} (p : slhdsa.params.Params) (hp : PN p N)
    (sk seed : Array U8 N) (a : address.Adrs) (on : Bool) (select : available N=.ok on)
    (perms : on=true → PermutationCorrect) (positive : on=true → 0<machine.width.val)
    (width : on=true → machine.width.val≤8) :
    shake.wots.wots_pk_gen available sk seed a ⦃ out => bytes out.val =
      Spec.wotsPkGen (Shake.params p) (bytes sk.val) (bytes seed.val) (adrsS a) ⦄ := by
  cases on with
  | false =>
    convert Shake.wots_pk_gen_spec p hp sk seed a using 1
    unfold shake.wots.wots_pk_gen slhdsa.shake.wots.wots_pk_gen
    simp only [select,bind_ok,Bool.false_eq_true,ite_false]
  | true =>
    simpa only [shake.wots.wots_pk_gen,select,bind_ok,ite_true] using keygen_spec p hp sk seed a (positive rfl) (width rfl) (perms rfl)

theorem digits_bound (digits : alloc.vec.Vec U32) (small : ∀ d ∈ digits.val, d.val<16) :
    ∀ i < digits.slice.length, digits.slice.val[i]!.val<16 := by
  intro i hi
  apply small
  change digits.val[i]! ∈ digits.val
  rw [getElem!_pos digits.val i hi]
  exact List.getElem_mem _

theorem wots_sign_spec {N : Usize} (p : slhdsa.params.Params) (hp : PN p N)
    (m sk seed : Array U8 N) (a : address.Adrs) (on : Bool) (select : available N=.ok on)
    (perms : on=true → PermutationCorrect) (positive : on=true → 0<machine.width.val) :
    shake.wots.wots_sign available m sk seed a ⦃ out => bytes out.val =
      Spec.wotsSign (Shake.params p) (bytes m.val) (bytes sk.val) (bytes seed.val) (adrsS a) ∧
      out.length=N.val*(2*N.val+3) ⦄ := by
  cases on with
  | false =>
    convert Shake.wots_sign_spec p hp m sk seed a using 1
    unfold shake.wots.wots_sign slhdsa.shake.wots.wots_sign
    simp only [select,bind_ok,Bool.false_eq_true,ite_false]
  | true =>
    unfold shake.wots.wots_sign
    let* ⟨ds,hd,len,small⟩ ← wots_digits_spec p hp m
    have view : ds.deref=ds.slice := by apply Slice.ext;simp [alloc.vec.Vec.deref,Slice.from_val];rfl
    have hn := hp.le32
    have actual : ds.slice.length=2*N.val+3 := len
    simp only [select,bind_ok,ite_true,view]
    let* ⟨out,rows,size⟩ ← sign_spec p hp sk seed a ds.slice (positive rfl) (perms rfl) (by omega) (digits_bound ds small)
    refine ⟨?_,by rw [size,actual,Nat.mul_comm]⟩
    change nats ds.val = Spec.wotsDigits (Shake.params p) (bytes m.val) at hd
    change bytes out.val = (List.range (Shake.params p).len).flatMap (signStep _ _ _ _ (Spec.wotsDigits _ _))
    rw [rows,show (Shake.params p).len=ds.slice.length from hp.len.trans actual.symm,← hd]
    apply List.flatMap_congr
    intro i hi
    have bound : i<ds.val.length := List.mem_range.mp hi
    simp only [signedChain,signStep,nats_getElem! _ _ bound];rfl

theorem wots_pk_from_sig_spec {N : Usize} (p : slhdsa.params.Params) (hp : PN p N)
    (sig : Slice U8) (m seed : Array U8 N) (a : address.Adrs) (size : N.val*(2*N.val+3)≤sig.length)
    (on : Bool) (select : available N=.ok on) (perms : on=true → PermutationCorrect)
    (positive : on=true → 0<machine.width.val) :
    shake.wots.wots_pk_from_sig available sig m seed a ⦃ out => bytes out.val =
      Spec.wotsPkFromSig (Shake.params p) (bytes sig.val) (bytes m.val) (bytes seed.val) (adrsS a) ⦄ := by
  cases on with
  | false =>
    convert Shake.wots_pk_from_sig_spec p hp sig m seed a size using 1
    unfold shake.wots.wots_pk_from_sig slhdsa.shake.wots.wots_pk_from_sig
    simp only [select,bind_ok,Bool.false_eq_true,ite_false]
  | true =>
    unfold shake.wots.wots_pk_from_sig
    let* ⟨ds,hd,len,small⟩ ← wots_digits_spec p hp m
    have view : ds.deref=ds.slice := by apply Slice.ext;simp [alloc.vec.Vec.deref,Slice.from_val];rfl
    have hn := hp.le32
    have actual : ds.slice.length=2*N.val+3 := len
    simp only [select,bind_ok,ite_true,view]
    let* ⟨out,hash⟩ ← recover_spec p hp sig seed a ds.slice (positive rfl) (perms rfl) (by omega)
      (digits_bound ds small) (by simpa only [actual,Nat.mul_comm (2*N.val+3)] using size)
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

#print axioms wots_pk_gen_spec
#print axioms wots_sign_spec
#print axioms wots_pk_from_sig_spec
end slhdsa.ShakeBatch
