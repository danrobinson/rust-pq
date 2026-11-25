import ForsDriver.DispatchProgram
import ForsDriver.Entry
import ForsDriver.Small
open Aeneas Aeneas.Std Result
namespace slhdsa.ForsDriver
open ShakeBatch NativeVerify
set_option linter.concreteInstances false
variable [kernel : Fused.Kernel] [trees : Trees]

theorem on_spec (available : Usize → Result Bool) {N : Usize} (p : params.Params) (hp : PN p N)
    (md : Slice U8) (sk seed : Array U8 N) (a : address.Adrs) (size : md.length=(p.k.val*p.a.val+7)/8)
    (domain : a.typ=address.FORS_TREE ∧ a.word2=0#u32 ∧ a.word3=0#u32)
    (on : available N=ok true) (perm : ActiveCorrect (Fused.machine kernel) kernel.active)
    (nodes : UpperNodes p sk seed a) :
    dispatched available p md sk seed a ⦃ out => bytes out.val=Spec.forsSign (Shake.params p)
      (bytes md.val) (bytes sk.val) (bytes seed.val) (adrsS a) ∧ out.length=p.k.val*(1+p.a.val)*N.val ⦄ := by
  have ha : p.a.val≤14 := hp.valid.a_le
  have positive : 1≤p.a.val := hp.valid.a_pos
  unfold dispatched
  step as ⟨k,hk⟩
  have kval : k.val=p.k.val := by simp [hk]
  let* ⟨digits,ind,len,valid⟩ ← base_2b_spec md p.a k (by omega) (by rw [kval,size];omega)
  rw [kval] at ind len
  have view : digits.deref=digits.slice := by apply Slice.ext; simp [alloc.vec.Vec.deref,Slice.from_val];rfl
  simp only [on,bind_ok,ite_true,view]
  have legal (t : Nat) (ht : t<digits.slice.length) : digits.val[t]!.val<2^p.a.val := by
    apply valid
    rw [getElem!_pos digits.val t ht]
    exact List.getElem_mem _
  have raw : sign p digits.slice sk seed a ⦃ out =>
      bytes out.val=(List.range p.k.val).flatMap (forsSignTree (Shake.params p)
        (bytes sk.val) (bytes seed.val) (adrsS a) (nats digits.val)) ∧
      out.length=p.k.val*(1+p.a.val)*N.val ⦄ := by
    by_cases height : 3≤p.a.val
    · exact sign_spec p hp digits.slice sk seed a domain len legal perm height nodes
    · exact sign_small_spec p hp digits.slice sk seed a domain len legal perm (by omega)
  apply WP.spec_mono raw
  rintro out ⟨data,length⟩
  refine ⟨?_,length⟩
  rw [forsSign_eq,data]
  change (List.range p.k.val).flatMap (forsSignTree _ _ _ _ (nats digits.val)) =
    (List.range p.k.val).flatMap (forsSignTree _ _ _ _ (Spec.base2b _ p.a.val p.k.val))
  rw [ind]

end slhdsa.ForsDriver
