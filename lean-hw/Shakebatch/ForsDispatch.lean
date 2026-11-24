import Shakebatch.ForsDispatchProgram
import Slhdsa.Proofs.ShakeFors
open Aeneas Aeneas.Std Result
namespace slhdsa.ShakeBatch
set_option linter.concreteInstances false
variable [machine : Machine] [stream : Stream] [correct : StreamCorrect]
variable (available : Usize → Result Bool)

theorem sign_dispatched {N : Usize} (p : slhdsa.params.Params) (hp : PN p N) (md : Slice U8)
    (sk seed : Array U8 N) (a : address.Adrs) (hmd : md.length=(p.k.val*p.a.val+7)/8)
    (on : Bool) (select : available N=.ok on)
    (perms : on=true → PermutationCorrect) (width : on=true → 0 < machine.width.val) :
    shake.fors.fors_sign available p md sk seed a ⦃ out =>
      bytes out.val=Spec.forsSign (Shake.params p) (bytes md.val) (bytes sk.val) (bytes seed.val) (adrsS a) ∧
      out.length=p.k.val*(1+p.a.val)*N.val ⦄ := by
  cases on with
  | false =>
    convert Shake.fors_sign_spec p hp md sk seed a hmd using 1
    unfold shake.fors.fors_sign slhdsa.shake.fors.fors_sign
    simp only [select,bind_ok,Bool.false_eq_true,ite_false]
  | true =>
    have ha : p.a.val ≤ 14 := hp.valid.a_le
    have pos : 1 ≤ p.a.val := hp.valid.a_pos
    unfold shake.fors.fors_sign
    step as ⟨k,hk⟩
    have kval : k.val=p.k.val := by simp [hk]
    let* ⟨digits,ind,len,valid⟩ ← base_2b_spec md p.a k (by omega) (by rw [kval,hmd];omega)
    rw [kval] at ind len
    have view : digits.deref=digits.slice := by apply Slice.ext; simp [alloc.vec.Vec.deref,Slice.from_val];rfl
    simp only [select,bind_ok,ite_true,view]
    let* ⟨out,bytesEq,size⟩ ← sign_fors_trees p hp sk seed a digits.slice (perms rfl) (width rfl)
      len (fun t ht => valid _ (by change digits.val[t]! ∈ digits.val; rw [getElem!_pos digits.val t ht]; exact List.getElem_mem _))
    refine ⟨?_,size⟩
    rw [forsSign_eq,bytesEq]
    change (List.range p.k.val).flatMap (forsSignTree _ _ _ _ (nats digits.val)) =
      (List.range p.k.val).flatMap (forsSignTree _ _ _ _ (Spec.base2b _ p.a.val p.k.val))
    rw [ind]

theorem recover_dispatched {N : Usize} (p : slhdsa.params.Params) (hp : PN p N) (sig md : Slice U8)
    (seed : Array U8 N) (a : address.Adrs) (len : sig.length=p.k.val*(1+p.a.val)*N.val)
    (hmd : md.length=(p.k.val*p.a.val+7)/8) (on : Bool) (select : available N=.ok on)
    (perms : on=true → PermutationCorrect) (width : on=true → 0 < machine.width.val) :
    shake.fors.fors_pk_from_sig available p sig md seed a ⦃ out => bytes out.val =
      Spec.forsPkFromSig (Shake.params p) (bytes sig.val) (bytes md.val) (bytes seed.val) (adrsS a) ⦄ := by
  cases on with
  | false =>
    convert Shake.fors_pk_from_sig_spec p hp sig md seed a len hmd using 1
    unfold shake.fors.fors_pk_from_sig slhdsa.shake.fors.fors_pk_from_sig
    simp only [select,bind_ok,Bool.false_eq_true,ite_false]
  | true =>
    have ha : p.a.val ≤ 14 := hp.valid.a_le
    have pos : 1 ≤ p.a.val := hp.valid.a_pos
    unfold shake.fors.fors_pk_from_sig
    step as ⟨k,hk⟩
    have kval : k.val=p.k.val := by simp [hk]
    let* ⟨digits,ind,count,valid⟩ ← base_2b_spec md p.a k (by omega) (by rw [kval,hmd];omega)
    rw [kval] at ind count
    have view : digits.deref=digits.slice := by apply Slice.ext; simp [alloc.vec.Vec.deref,Slice.from_val];rfl
    simp only [select,bind_ok,ite_true,view]
    let* ⟨out,bytesEq⟩ ← recover_fors_trees p hp sig len seed a (perms rfl) (width rfl) digits.slice
      count (fun t ht => valid _ (by change digits.val[t]! ∈ digits.val; rw [getElem!_pos digits.val t ht];exact List.getElem_mem _))
    rw [forsPkFromSig_eq,bytesEq]
    change _ = Spec.T _ _ _ ((List.range p.k.val).flatMap (forsRoot _ _ _ _ (Spec.base2b _ p.a.val p.k.val)))
    rw [← ind]
    rfl

end slhdsa.ShakeBatch
