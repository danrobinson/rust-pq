import Cachepath.WotsRecovery
import Shakebatch.WotsBatchIds

open Aeneas Aeneas.Std Result slhdsa
namespace CacheopsRust.WotsCallbacks
open slhdsa.ShakeBatch
set_option linter.concreteInstances false

/-- A stateless array constructor returns the first panic even if other lanes are valid. -/
private theorem ofFnM_panic {n : Nat} {T S : Type} (f : Fin n → StateT S Result T) (s : S)
    (total : ∀ i, (∃ v, (f i).run s = ok (v,s)) ∨ (f i).run s = fail .panic) :
    ((∃ v, (Vector.ofFnM f).run s = ok (v,s)) ∧ ∀ i, ∃ v, (f i).run s = ok (v,s)) ∨
    ((Vector.ofFnM f).run s = fail .panic ∧ ∃ i, (f i).run s = fail .panic) := by
  induction n with
  | zero => exact Or.inl ⟨⟨_,by rw [Vector.ofFnM_zero]; rfl⟩,fun i => i.elim0⟩
  | succ n ih =>
    simp only [Vector.ofFnM_succ,StateT.run_bind,bind_tc_eq]
    rcases ih (fun i => f i.castSucc) (fun i => total i.castSucc) with ⟨⟨vs,hvs⟩,hs⟩ | ⟨bad,i,hi⟩
    · rw [hvs,bind_ok]
      rcases total (Fin.last n) with ⟨v,hv⟩ | bad
      · rw [hv,bind_ok]
        exact Or.inl ⟨⟨_,rfl⟩,Fin.lastCases ⟨v,hv⟩ hs⟩
      · rw [bad,bind_fail]
        exact Or.inr ⟨rfl,_,bad⟩
    · rw [bad,bind_fail]
      exact Or.inr ⟨rfl,i.castSucc,hi⟩

theorem map_blocks_panic [machine : Machine] {N : Usize} (sig : Slice U8)
    (ids : Array Usize machine.width) (room : ∀ j < machine.width.val, (ids.val[j]!.val+1)*N.val ≤ Usize.max)
    (short : ∃ j < machine.width.val, sig.length < (ids.val[j]!.val+1)*N.val) :
    core.array.Array.map (ShakeBatch.shake.batch.recover.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU8N N)
      ids sig = fail .panic := by
  unfold core.array.Array.map core.array.from_fn
  let step (i : Fin machine.width.val) (s : Slice U8) : Result (Array U8 N × Slice U8) := do
    let id ← ids.index_usize (Usize.ofNatCore i.val (by scalar_tac))
    let row ← slhdsa.util.block N s id
    ok (row,s)
  have get (i : Fin machine.width.val) : ids.index_usize (Usize.ofNatCore i.val (by scalar_tac)) = ok ids.val[i.val]! := by
    obtain ⟨v,e,h⟩ := spec_imp_exists (Array.index_usize_spec ids (Usize.ofNatCore i.val (by scalar_tac)) (by scalar_tac))
    rw [e,ok.injEq,h,getElem!_pos _ _ (by simpa using i.isLt)]
    rfl
  have total (i : Fin machine.width.val) : (∃ v, step i sig = ok (v,sig)) ∨ step i sig = fail .panic := by
    simp only [step,get,bind_ok]
    by_cases readable : (ids.val[i.val]!.val+1)*N.val ≤ sig.length
    · obtain ⟨b,h,_⟩ := spec_imp_exists (block_spec N sig ids.val[i.val]! readable)
      exact Or.inl ⟨b,by rw [h,bind_ok]⟩
    · rw [WotsLanes.block_reject sig _ (room _ i.isLt) (Nat.lt_of_not_ge readable),bind_fail]
      exact Or.inr rfl
  obtain ⟨j,hj,missing⟩ := short
  have bad : step ⟨j,hj⟩ sig = fail .panic := by
    simp only [step,get,bind_ok,WotsLanes.block_reject sig _ (room j hj) missing,bind_fail]
  rcases ofFnM_panic (fun i => step i) sig total with ⟨_,all⟩ | ⟨failed,_⟩
  · obtain ⟨v,hv⟩ := all ⟨j,hj⟩
    change step ⟨j,hj⟩ sig = ok (v,sig) at hv
    rw [bad] at hv
    simp at hv
  · change (do let (v,_) ← (Vector.ofFnM (m:=StateT (Slice U8) Result) step).run sig
               ok (Array.from (n:=machine.width) v.toList (by simp))) = _
    simp only [failed,bind_tc_eq,bind_fail]

end CacheopsRust.WotsCallbacks
