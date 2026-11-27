import Parallel.WorkerIterators
import Slhdsa.Proofs.Basic

namespace ParallelWorkerIterators
open Aeneas Aeneas.Std Result

private theorem normalBind {A B} (m : Result A) (k : A → Result B) {b : B}
    (ran : (m >>= k)=ok b) : ∃ a, m=ok a ∧ k a=ok b := by
  cases m with
  | ret a => exact ⟨a,rfl,by simpa using ran⟩
  | div => simp_all
  | vis e k => cases e with | fail e => simp_all

/-- Each successfully collected element comes from the iterator step at its
index. The statement also covers a partial traversal with a reversed prefix. -/
private theorem collected {I T : Type} (it : core.iter.traits.iterator.Iterator I T)
    (offset : I → Nat) (len : Nat) (origin : Nat → T → Prop) (legal : I → Prop)
    (one : ∀ s o tail, legal s → it.next s=ok (o,tail) → match o with
      | none => len≤offset s
      | some v => legal tail ∧ offset s<len ∧ offset tail=offset s+1 ∧ origin (offset s) v)
    (s : I) (valid : legal s) (acc out : List T) (ran : alloc.vec.FromIteratorVec.iterToList it s acc=ok out) :
    ∃ suffix, out=acc.reverse++suffix ∧ suffix.length=len-offset s ∧
      ∀ i (hi : i<suffix.length), origin (offset s+i) suffix[i] := by
  rw [alloc.vec.FromIteratorVec.iterToList] at ran
  obtain ⟨⟨o,tail⟩,step,ran⟩ := normalBind _ _ ran
  have status := one s o tail valid step
  cases o with
  | none =>
    cases Result.ok_injective ran
    exact ⟨[],by simp,by simpa using (Nat.sub_eq_zero_of_le status).symm,by simp⟩
  | some v =>
    obtain ⟨validTail,live,inc,entry⟩ := status
    obtain ⟨suffix,eq,size,rows⟩ := collected it offset len origin legal one tail validTail (v::acc) out ran
    refine ⟨v::suffix,by simpa [List.reverse_cons,List.append_assoc] using eq,by simp;omega,?_⟩
    intro i hi
    cases i with
    | zero => simpa using entry
    | succ i =>
      have row := rows i (by simpa using hi)
      simpa [inc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using row
termination_by len-offset s
decreasing_by omega

/-- The actual standard-library collect checks its vector bound after consuming
the mapped range. A successful call retains its length and every source index. -/
theorem collectedRange {T I : Type} (it : core.iter.traits.iterator.Iterator I T)
    (s : I) (offset : I → Nat) (len : Nat) (initial : offset s=0) (origin : Nat → T → Prop) (legal : I → Prop)
    (one : ∀ s o tail, legal s → it.next s=ok (o,tail) → match o with
      | none => len≤offset s
      | some v => legal tail ∧ offset s<len ∧ offset tail=offset s+1 ∧ origin (offset s) v)
    (valid : legal s) (out : alloc.vec.Vec T)
    (ran : core.iter.traits.iterator.Iterator.collect.default it (core.iter.traits.collect.FromIteratorVec T) s=ok out) :
    out.length=len ∧ ∀ i (hi : i<out.length),origin i out.val[i] := by
  simp only [core.iter.traits.iterator.Iterator.collect.default, core.iter.traits.collect.FromIteratorVec,
    alloc.vec.FromIteratorVec.from_iter,core.iter.traits.collect.IntoIterator.Blanket,
    core.iter.traits.collect.IntoIterator.Blanket.into_iter,bind_ok] at ran
  obtain ⟨xs,traversed,ret⟩ := normalBind (alloc.vec.FromIteratorVec.iterToList it s []) _ ran
  split at ret
  · cases Result.ok_injective ret
    obtain ⟨ys,eq,size,rows⟩ := collected it offset len origin legal one s valid [] xs traversed
    simp at eq
    subst xs
    simpa [alloc.vec.Vec.length,initial] using And.intro size rows
  · simp at ret


abbrev CellRange := core.iter.adapters.map.Map (core.ops.range.Range Usize) Unit

/-- The allocation loops map a zero-capture constructor over 0..len. Every
cell in the collected vector is returned by that constructor at its own index. -/
theorem allocationRows {T : Type} (it : core.iter.traits.iterator.Iterator CellRange T)
    (f : core.ops.function.FnMut Unit Usize T)
    (same : it.next = next (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize) f)
    (len : Usize) (out : alloc.vec.Vec T)
    (ran : core.iter.traits.iterator.Iterator.collect.default it (core.iter.traits.collect.FromIteratorVec T)
      ⟨⟨0#usize,len⟩,()⟩ = ok out) :
    out.length=len.val ∧ ∀ i (hi : i<out.length), ∃ index : Usize, index.val=i ∧ f.call_mut () index=ok (out.val[i],()) := by
  apply collectedRange it _ (fun s => s.iter.start.val) len.val rfl
    (fun i v => ∃ index : Usize,index.val=i ∧ f.call_mut () index=ok (v,()))
    (fun s => s.iter.end=len) _ rfl out ran
  rintro ⟨r,⟨⟩⟩ o tail valid get
  change r.end=len at valid
  rw [same] at get
  unfold next at get
  by_cases live : r.start.val < r.end.val
  · obtain ⟨⟨_,r'⟩,read,tag,inc,last⟩ := slhdsa.spec_imp_exists
      (core.iter.range.IteratorRange.next_Usize_some_spec r live)
    simp only [core.iter.traits.iterator.IteratorRange,read,tag,bind_ok] at get
    obtain ⟨⟨v,u⟩,created,ret⟩ := normalBind (f.call_mut () r.start) _ get
    cases u
    cases Result.ok_injective ret
    exact ⟨last.trans valid,valid ▸ live,inc,r.start,rfl,created⟩
  · obtain ⟨⟨_,r'⟩,read,tag,_⟩ := slhdsa.spec_imp_exists
      (core.iter.range.IteratorRange.next_Usize_none_spec r (by omega))
    simp only [core.iter.traits.iterator.IteratorRange,read,tag,bind_ok] at get
    cases Result.ok_injective get
    exact valid ▸ Nat.le_of_not_gt live

end ParallelWorkerIterators
