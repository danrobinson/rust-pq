import Shakebatch.ForsDispatch
import Shakebatch.ScalarStream

open Aeneas Aeneas.Std Result slhdsa
namespace CacheopsRust.ForsCallbacks
open slhdsa.ShakeBatch
set_option linter.concreteInstances false
variable [machine : Machine] [stream : Stream] [StreamCorrect]

theorem sign_eq {N : Usize} (p : slhdsa.params.Params) (hp : PN p N)
    (positive : 0 < machine.width.val) (permutes : PermutationCorrect)
    (md : Slice U8) (sk seed : Array U8 N) (a : slhdsa.address.Adrs)
    (hmd : md.length = (p.k.val*p.a.val+7)/8) :
    (do let ds ← slhdsa.util.base_2b md p.a (UScalar.cast .Usize p.k)
        ShakeBatch.shake.fors_batch.sign p ds.deref sk seed a) = slhdsa.shake.fors.fors_sign p md sk seed a := by
  obtain ⟨x,hx,ex,_⟩ := spec_imp_exists (sign_dispatched (fun _ => ok true) p hp md sk seed a hmd
    true rfl (fun _ => permutes) (fun _ => positive))
  obtain ⟨y,hy,ey,_⟩ := spec_imp_exists (Shake.fors_sign_spec p hp md sk seed a hmd)
  simp only [ShakeBatch.shake.fors.fors_sign,lift,bind_ok,ite_true] at hx
  rw [hx,hy,ok.injEq]
  exact alloc.vec.Vec.ext _ _ ((bytes_inj _ _).mp (ex.trans ey.symm))

theorem recover_eq {N : Usize} (p : slhdsa.params.Params) (hp : PN p N)
    (positive : 0 < machine.width.val) (permutes : PermutationCorrect)
    (sig md : Slice U8) (seed : Array U8 N) (a : slhdsa.address.Adrs)
    (len : sig.length = p.k.val*(1+p.a.val)*N.val) (hmd : md.length = (p.k.val*p.a.val+7)/8) :
    (do let ds ← slhdsa.util.base_2b md p.a (UScalar.cast .Usize p.k)
        ShakeBatch.shake.fors_batch.recover p ds.deref sig seed a) = slhdsa.shake.fors.fors_pk_from_sig p sig md seed a := by
  obtain ⟨x,hx,ex⟩ := spec_imp_exists (recover_dispatched (fun _ => ok true) p hp sig md seed a len hmd
    true rfl (fun _ => permutes) (fun _ => positive))
  obtain ⟨y,hy,ey⟩ := spec_imp_exists (Shake.fors_pk_from_sig_spec p hp sig md seed a len hmd)
  simp only [ShakeBatch.shake.fors.fors_pk_from_sig,lift,bind_ok,ite_true] at hx
  rw [hx,hy,ok.injEq]
  exact Aeneas.Std.Array.ext _ _ ((bytes_inj _ _).mp (ex.trans ey.symm))

end CacheopsRust.ForsCallbacks
