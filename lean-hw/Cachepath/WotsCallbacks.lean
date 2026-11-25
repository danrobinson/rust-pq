import Shakebatch.WotsDispatch
import Shakebatch.ScalarStream
import Cachepath.WotsShortCaller

open Aeneas Aeneas.Std Result slhdsa
namespace CacheopsRust.WotsCallbacks
open slhdsa.ShakeBatch
set_option linter.concreteInstances false
variable [machine : Machine] [stream : Stream] [StreamCorrect]

/-- The cache's single-leaf generator batches chains within one WOTS key. -/
theorem single_eq {N : Usize} (p : slhdsa.params.Params) (hp : PN p N)
    (positive : 0 < machine.width.val) (width : machine.width.val ≤ 8) (permutes : PermutationCorrect)
    (sk seed : Array U8 N) (a : slhdsa.address.Adrs) :
    ShakeBatch.shake.batch.keygen sk seed a = slhdsa.shake.wots.wots_pk_gen sk seed a := by
  obtain ⟨x,hx,ex⟩ := spec_imp_exists (ShakeBatch.keygen_spec p hp sk seed a positive width permutes)
  obtain ⟨y,hy,ey⟩ := spec_imp_exists (Shake.wots_pk_gen_spec p hp sk seed a)
  rw [hx,hy,ok.injEq]
  exact Aeneas.Std.Array.ext _ _ ((bytes_inj _ _).mp (ex.trans ey.symm))

/-- The dispatcher's WOTS signing equality, instantiated with the source-replayed packed caller. -/
theorem sign_eq {N : Usize} (p : slhdsa.params.Params) (hp : PN p N)
    (positive : 0 < machine.width.val) (permutes : PermutationCorrect)
    (m sk seed : Array U8 N) (a : slhdsa.address.Adrs) :
    (do let ds ← slhdsa.wots.wots_digits m
        ShakeBatch.shake.batch.sign sk seed a ds.deref) = slhdsa.shake.wots.wots_sign m sk seed a := by
  obtain ⟨x,hx,ex,_⟩ := spec_imp_exists (ShakeBatch.wots_sign_spec (fun _ => ok true) p hp m sk seed a true rfl
    (fun _ => permutes) (fun _ => positive))
  obtain ⟨y,hy,ey,_⟩ := spec_imp_exists (Shake.wots_sign_spec p hp m sk seed a)
  simp only [ShakeBatch.shake.wots.wots_sign,bind_ok,ite_true] at hx
  rw [hx,hy,ok.injEq]
  exact alloc.vec.Vec.ext _ _ ((bytes_inj _ _).mp (ex.trans ey.symm))

theorem recover_eq_valid {N : Usize} (p : slhdsa.params.Params) (hp : PN p N)
    (positive : 0 < machine.width.val) (permutes : PermutationCorrect)
    (sig : Slice U8) (m seed : Array U8 N) (a : slhdsa.address.Adrs) (size : N.val*(2*N.val+3) ≤ sig.length) :
    (do let ds ← slhdsa.wots.wots_digits m
        ShakeBatch.shake.batch.recover sig seed a ds.deref) = slhdsa.shake.wots.wots_pk_from_sig sig m seed a := by
  obtain ⟨x,hx,ex⟩ := spec_imp_exists (ShakeBatch.wots_pk_from_sig_spec (fun _ => ok true) p hp sig m seed a size true rfl
    (fun _ => permutes) (fun _ => positive))
  obtain ⟨y,hy,ey⟩ := spec_imp_exists (Shake.wots_pk_from_sig_spec p hp sig m seed a size)
  simp only [ShakeBatch.shake.wots.wots_pk_from_sig,bind_ok,ite_true] at hx
  rw [hx,hy,ok.injEq]
  exact Aeneas.Std.Array.ext _ _ ((bytes_inj _ _).mp (ex.trans ey.symm))

/-- Full Rust-result equality, including signatures that fail a sorted block read. -/
theorem recover_eq {N : Usize} (p : slhdsa.params.Params) (hp : PN p N)
    (positive : 0 < machine.width.val) (permutes : PermutationCorrect)
    (sig : Slice U8) (m seed : Array U8 N) (a : slhdsa.address.Adrs) :
    (do let ds ← slhdsa.wots.wots_digits m
        ShakeBatch.shake.batch.recover sig seed a ds.deref) = slhdsa.shake.wots.wots_pk_from_sig sig m seed a := by
  by_cases size : N.val*(2*N.val+3) ≤ sig.length
  · exact recover_eq_valid p hp positive permutes sig m seed a size
  obtain ⟨ds,decode,_,len,valid⟩ := spec_imp_exists (wots_digits_spec p hp m)
  have hn := hp.le32
  have count : ds.deref.length ≤ 67 := by rw [vec_deref_length,len]; omega
  have small (j : Nat) (hj : j < ds.deref.length) : ds.deref.val[j]!.val < 16 := by
    rw [vec_deref_length] at hj
    rw [vec_deref_val,getElem!_pos ds.val j hj]
    exact valid _ (List.getElem_mem hj)
  have short := Nat.lt_of_not_ge size
  have bad := packed_reject p hp sig seed a ds.deref count small positive permutes (by
    rwa [vec_deref_length,len,Nat.mul_comm])
  simp only [decode,bind_ok,bad,WotsLanes.scalar_reject p hp sig m seed a short]

/-- The two WOTS fields of the cache fast-path contract on any machine implementing
lane-wise Keccak-f[1600]. The recovery field quantifies over every signature slice. -/
def Fields (N : Usize) : Prop :=
  (∀ (m sk seed : Array U8 N) a,
    (do let ds ← slhdsa.wots.wots_digits m
        ShakeBatch.shake.batch.sign sk seed a ds.deref) = slhdsa.shake.wots.wots_sign m sk seed a) ∧
  (∀ (sig : Slice U8) (m seed : Array U8 N) a,
    (do let ds ← slhdsa.wots.wots_digits m
        ShakeBatch.shake.batch.recover sig seed a ds.deref) = slhdsa.shake.wots.wots_pk_from_sig sig m seed a)

theorem fields {N : Usize} (p : slhdsa.params.Params) (hp : PN p N)
    (positive : 0 < machine.width.val) (permutes : PermutationCorrect) : Fields N :=
  ⟨sign_eq p hp positive permutes,recover_eq p hp positive permutes⟩

end CacheopsRust.WotsCallbacks
