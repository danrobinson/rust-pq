import Cachepath.NativeVerify.ForsProgram
import Shakebatch.Range
import Shakebatch.Read

open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.NativeVerify.Fors
open ShakeBatch
set_option linter.concreteInstances false
variable [machine : Machine]

private abbrev State := Matrix machine.width

private def pairBody (n offset lane : Usize) (left right : Usize → Result U64) (it : Range) (state : State) :
    Result (ControlFlow (Range × State) State) := do
  let (o,next) ← core.iter.range.IteratorRange.next core.iter.range.StepUsize it
  match o with
  | none => ok (done state)
  | some i =>
    let x ← left i
    let r ← offset+i
    let (row,restore) ← Array.index_mut_usize state r
    let changed ← Array.update row lane x
    let y ← right i
    let second ← offset+n
    let r' ← second+i
    let state' := restore changed
    let (row',restore') ← Array.index_mut_usize state' r'
    let changed' ← Array.update row' lane y
    ok (cont (next,restore' changed'))

private def savedWord (cur : Array (Array U64 machine.width) 4#usize) (lane i : Usize) : Result U64 := do
  let row ← Array.index_usize cur i
  Array.index_usize row lane

private theorem saved_spec (cur : Array (Array U64 machine.width) 4#usize) (lane i : Usize)
    (inRow : i.val<4) (inLane : lane.val<machine.width.val) :
    savedWord cur lane i ⦃ x => x.bv=cur.val[i.val]!.val[lane.val]!.bv ⦄ := by
  unfold savedWord
  step as ⟨row,read⟩
  step as ⟨x,read'⟩
  rw [read',read,← getElem!_pos,← getElem!_pos]

def payload (s : State) (offset n lane : Nat) (left right : Nat → BitVec 64) (i k j : Nat) :=
  if j=lane ∧ offset+n ≤ k ∧ k < offset+n+i then right (k-(offset+n)) else
  if j=lane ∧ offset ≤ k ∧ k < offset+i then left (k-offset) else cell s k j

private theorem pairWords (s : State) (n offset lane : Usize) (left right : Usize → Result U64)
    (x y : Nat → BitVec 64) (bounds : offset.val+2*n.val≤25) (inside : lane.val<machine.width.val)
    (lhs : ∀ i : Usize, i.val<n.val → left i ⦃ w => w.bv=x i.val ⦄)
    (rhs : ∀ i : Usize, i.val<n.val → right i ⦃ w => w.bv=y i.val ⦄) :
    loop (fun (it,state) => pairBody n offset lane left right it state) (⟨0#usize,n⟩,s)
      ⦃ out => ∀ k<25, ∀ j<machine.width.val, cell out k j = payload s offset.val n.val lane.val x y n.val k j ⦄ := by
  apply range_fold (pairBody n offset lane left right) n s (fun i out => ∀ k < 25, ∀ j < machine.width.val,
    cell out k j = payload s offset.val n.val lane.val x y i k j)
  · intro k hk j hj
    simp [payload] <;> split_ifs <;> first | rfl | omega
  · intro it state stop live prev
    unfold pairBody
    step with core.iter.range.IteratorRange.next_Usize_some_spec it (by simpa [stop] using live) as ⟨_,next,tag,inc,ends⟩
    simp only [tag]
    step with lhs it.start live as ⟨a,av⟩
    step as ⟨r,rv⟩
    step as ⟨row,restore,read,back⟩
    step as ⟨row',upd⟩
    step with rhs it.start live as ⟨b,bv⟩
    step as ⟨base,basev⟩
    step as ⟨r2,r2v⟩
    step as ⟨other,restore2,read2,back2⟩
    step as ⟨other',upd2⟩
    refine ⟨next,_,rfl,ends.trans stop,inc,?_⟩
    intro k hk j hj
    rw [back2,upd2,read2,← getElem!_pos,cell_write _ _ _ _ (by omega) inside,
      back,upd,read,← getElem!_pos,cell_write _ _ _ _ (by omega) inside,prev k hk j hj]
    simp only [payload,inc,rv,r2v,basev,av,bv]
    split_ifs <;> first | rfl | omega | (congr 1 <;> omega)
  · intro it state atEnd stop
    unfold pairBody
    obtain ⟨⟨_,_⟩,no,tag,_⟩ := spec_imp_exists (core.iter.range.IteratorRange.next_Usize_none_spec it (by rw [stop,atEnd]))
    simp [no,tag]

private theorem left_eq (n offset lane : Usize) (cur : Array (Array U64 machine.width) 4#usize) (sib : Slice U8) :
    recover_loop0_loop4_loop1_loop0.body n offset cur lane sib =
      pairBody n offset lane (savedWord cur lane) (ShakeBatch.shake.batch.word sib) := by
  funext it state
  unfold recover_loop0_loop4_loop1_loop0.body pairBody
  congr 1
  funext ⟨o,next⟩
  cases o <;> simp [savedWord,Std.bind_assoc]

private theorem right_eq (n offset lane : Usize) (cur : Array (Array U64 machine.width) 4#usize) (sib : Slice U8) :
    recover_loop0_loop4_loop1_loop1.body n offset cur lane sib =
      pairBody n offset lane (ShakeBatch.shake.batch.word sib) (savedWord cur lane) := by
  funext it state
  unfold recover_loop0_loop4_loop1_loop1.body pairBody
  congr 1
  funext ⟨o,next⟩
  cases o <;> simp [savedWord,Std.bind_assoc]

theorem pair_payloads (s : State) (n offset lane : Usize) (cur : Array (Array U64 machine.width) 4#usize)
    (sib : Slice U8) (odd : Bool) (small : n.val≤4) (bounds : offset.val+2*n.val≤25)
    (inside : lane.val<machine.width.val) (fit : n.val*8≤sib.length) :
    (if odd then recover_loop0_loop4_loop1_loop1 ⟨0#usize,n⟩ n offset s cur lane sib
     else recover_loop0_loop4_loop1_loop0 ⟨0#usize,n⟩ n offset s cur lane sib) ⦃ out =>
      ∀ k<25, ∀ j<machine.width.val, let prior := fun i : Nat => cur.val[i]!.val[lane.val]!.bv
        let sibling := inputWord sib.val
        cell out k j = payload s offset.val n.val lane.val (if odd then sibling else prior)
          (if odd then prior else sibling) n.val k j ⦄ := by
  have a := fun (i : Usize) (h : i.val < n.val) => saved_spec cur lane i (by omega) inside
  have b := fun (i : Usize) (h : i.val < n.val) => ShakeBatch.word_spec sib i (by omega)
  cases odd
  · simp only [Bool.false_eq_true,ite_false,recover_loop0_loop4_loop1_loop0,left_eq]
    exact pairWords s n offset lane _ _ _ _ bounds inside a b
  · simp only [ite_true,recover_loop0_loop4_loop1_loop1,right_eq]
    exact pairWords s n offset lane _ _ _ _ bounds inside b a

end slhdsa.NativeVerify.Fors
