import Shakebatch.RecoverMaps
open Aeneas Aeneas.Std Result
namespace slhdsa.ShakeBatch
set_option linter.concreteInstances false
variable [machine : Machine]
open shake.fors_batch.recover

private theorem row_fits (a k t n : Nat) (ht : t < k) :
    (t*(a+1)+1)*n ≤ k*(1+a)*n := by
  apply Nat.mul_le_mul_right
  have bound := Nat.mul_le_mul_right (a+1) (show t+1 ≤ k by omega)
  rw [Nat.add_mul,Nat.one_mul] at bound
  rw [Nat.add_comm 1 a]
  omega

theorem recover_secrets {N : Usize} (p : slhdsa.params.Params) (hp : PN p N)
    (sig : Slice U8) (len : sig.length=p.k.val*(1+p.a.val)*N.val)
    (stride : Usize) (hs : stride.val=p.a.val+1) (trees : Array Usize machine.width)
    (valid : ∀ j < machine.width.val, trees.val[j]!.val < p.k.val) :
    core.array.Array.map (closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU8N N) trees (sig,stride) ⦃ out =>
      ∀ j < machine.width.val, bytes out.val[j]!.val=Spec.block (Shake.params p) (bytes sig.val)
        (trees.val[j]!.val*(p.a.val+1)) ⦄ := by
  apply map_spec (closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU8N N) trees (sig,stride)
    (fun j v => bytes v.val=Spec.block (Shake.params p) (bytes sig.val) (trees.val[j]!.val*(p.a.val+1)))
  intro j hj
  have bound := row_fits p.a.val p.k.val trees.val[j]!.val N.val (valid j hj)
  have pos : 0 < N.val := by have := hp.nok.ge16; omega
  rw [← len] at bound
  have off : trees.val[j]!.val*stride.val ≤ Usize.max := by
    have := Nat.le_mul_of_pos_right (trees.val[j]!.val*(p.a.val+1)+1) pos
    rw [hs]; scalar_tac
  simp only [closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU8N.call_mut]
  step as ⟨i,hi⟩
  let* ⟨v,hv⟩ ← block_spec N sig i (by rw [hi,hs]; exact bound)
  refine ⟨bytes_block _ _ _ _ ?_, rfl⟩
  simpa only [Shake.params,paramsS_n,hp.n_eq,hi,hs] using hv

theorem recover_siblings {N : Usize} (p : slhdsa.params.Params) (hp : PN p N)
    (sig : Slice U8) (len : sig.length=p.k.val*(1+p.a.val)*N.val)
    (stride : Usize) (hs : stride.val=p.a.val+1) (h : U32) (level : h.val < p.a.val)
    (trees : Array Usize machine.width) (valid : ∀ j < machine.width.val, trees.val[j]!.val < p.k.val) :
    core.array.Array.map (closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU8N N) trees (sig,stride,h) ⦃ out =>
      ∀ j < machine.width.val, bytes out.val[j]!.val=Spec.block (Shake.params p) (bytes sig.val)
        (trees.val[j]!.val*(p.a.val+1)+1+h.val) ⦄ := by
  apply map_spec (closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU8N N) trees (sig,stride,h)
    (fun j v => bytes v.val=Spec.block (Shake.params p) (bytes sig.val) (trees.val[j]!.val*(p.a.val+1)+1+h.val))
  intro j hj
  have bound := fors_sib_bound _ _ _ _ _ _ (valid j hj) level len
  have lim : trees.val[j]!.val*stride.val+1+h.val+1 ≤ Usize.max := by
    rw [hs]
    have := Nat.le_mul_of_pos_right (trees.val[j]!.val*(p.a.val+1)+1+h.val+1) (show 0 < N.val by have := hp.nok.ge16; omega)
    scalar_tac
  simp only [closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU8N.call_mut]
  step as ⟨i,hi⟩
  simp only [lift,bind_ok]
  have cast : (UScalar.cast .Usize h).val=h.val := by simp
  step as ⟨i1,h1⟩
  step as ⟨i2,h2⟩
  have result : i2.val=trees.val[j]!.val*(p.a.val+1)+1+h.val := by rw [h2,h1,hi,hs,cast]; omega
  let* ⟨v,hv⟩ ← block_spec N sig i2 (by rw [result]; exact bound)
  refine ⟨bytes_block _ _ _ _ ?_, rfl⟩
  simpa only [Shake.params,paramsS_n,hp.n_eq,result] using hv

end slhdsa.ShakeBatch
