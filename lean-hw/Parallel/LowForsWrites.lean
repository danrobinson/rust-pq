import Parallel.LowForsIndices
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.ParallelLowFors
open ShakeBatch
variable [machine : Machine]
abbrev Journal (N : Usize) := alloc.vec.Vec (Usize × Array U8 N)
def Written {N} (initial : Journal N) (count : Nat) (slot : Nat→Nat) (rows : Array (Array U8 N) machine.width)
    (out : Journal N) :=
  out.length=initial.length+count ∧ (∀ i < initial.length, out.val[i]! = initial.val[i]!) ∧
  ∀ i<count, out.val[initial.length+i]!.1.val=slot i ∧ out.val[initial.length+i]!.2=rows.val[i]!

private theorem advance {N} {init cur out : Journal N} {i : Nat} {slot : Nat→Nat} {rows : Array (Array U8 N) machine.width}
    (prev : Written init i slot rows cur) (dest : Usize) (v : Array U8 N)
    (d : dest.val=slot i) (value : v=rows.val[i]!) (eq : out.val=cur.val++[(dest,v)]) :
    Written init (i+1) slot rows out := by
  obtain ⟨length,prior,old⟩ := prev
  refine ⟨?_,?_,?_⟩
  · change out.val.length=_
    rw [eq,List.length_append];change cur.length+1=_;omega
  · intro k hk
    rw [eq,List.getElem!_append_left _ _ _ (by change k<cur.length;omega),prior k hk]
  · intro k hk
    rw [eq]
    by_cases same : k=i
    · subst k
      rw [←length,List.getElem!_append_right _ _ _ (by rfl)]
      simpa [alloc.vec.Vec.length] using And.intro d value
    · rw [List.getElem!_append_left _ _ _ (by change _<cur.length;omega)]
      exact old k (by omega)

theorem secret_writes {N} (active first stride : Usize) (init : Journal N)
    (rows : Array (Array U8 N) machine.width)
    (width : active.val≤machine.width.val) (range : first.val+active.val≤35)
    (space : init.length+active.val≤Usize.max)
    (fit : ∀ l<active.val, (first.val+l)*stride.val≤Usize.max) :
    ticket_loop0 ⟨0#usize,active⟩ stride init first rows ⦃ out =>
      Written init active.val (fun l => (first.val+l)*stride.val) rows out ⦄ := by
  unfold ticket_loop0
  apply range_fold (ticket_loop0.body stride first rows) active init
    (fun k out => Written init k (fun l => (first.val+l)*stride.val) rows out) (by simp [Written])
  · intro it cur stop live prev
    have length := prev.1
    have fits := fit _ live
    have mx : 2^32-1≤Usize.max := by agrind
    unfold ticket_loop0.body
    step with core.iter.range.IteratorRange.next_Usize_some_spec it (by simpa [stop] using live) as ⟨_,next,tag,inc,last⟩
    simp only [tag,lift,bind_ok]
    step as ⟨pos,pv⟩
    step as ⟨base,bv⟩
    step as ⟨v,read⟩
    step with alloc.vec.Vec.push_spec cur (base,v) (by change cur.length<Usize.max;omega) as ⟨out,push⟩
    refine ⟨next,out,rfl,last.trans stop,inc,?_⟩
    rw [inc]
    exact advance prev base v (by rw [bv,pv]) (by rw [read,←getElem!_pos]) push
  · intro it cur last stop
    obtain ⟨_,no⟩ := ForsDriver.range_done it _ stop last
    simp [ticket_loop0.body,no]

theorem sibling_writes {N} (active first stride : Usize) (j : U32) (init : Journal N)
    (rows : Array (Array U8 N) machine.width)
    (width : active.val≤machine.width.val) (range : first.val+active.val≤35)
    (space : init.length+active.val≤Usize.max)
    (fit : ∀ l<active.val, (first.val+l)*stride.val+1+j.val≤Usize.max) :
    ticket_loop1_loop0 ⟨0#usize,active⟩ stride init first j rows ⦃ out =>
      Written init active.val (fun l => (first.val+l)*stride.val+1+j.val) rows out ⦄ := by
  unfold ticket_loop1_loop0
  apply range_fold (ticket_loop1_loop0.body stride first j rows) active init
    (fun k out => Written init k (fun l => (first.val+l)*stride.val+1+j.val) rows out) (by simp [Written])
  · intro it cur stop live prev
    have length := prev.1
    have fits := fit _ live
    have mx : 2^32-1≤Usize.max := by agrind
    unfold ticket_loop1_loop0.body
    step with core.iter.range.IteratorRange.next_Usize_some_spec it (by simpa [stop] using live) as ⟨_,next,tag,inc,last⟩
    simp only [tag,lift,bind_ok]
    step as ⟨pos,pv⟩
    step as ⟨base,bv⟩
    step as ⟨off,ov⟩
    step as ⟨dest,dv⟩
    step as ⟨v,read⟩
    step with alloc.vec.Vec.push_spec cur (dest,v) (by change cur.length<Usize.max;omega) as ⟨out,push⟩
    refine ⟨next,out,rfl,last.trans stop,inc,?_⟩
    rw [inc]
    exact advance prev dest v (by rw [dv,ov,bv,pv,U32.cast_Usize_val_eq]) (by rw [read,←getElem!_pos]) push
  · intro it cur last stop
    obtain ⟨_,no⟩ := ForsDriver.range_done it _ stop last
    simp [ticket_loop1_loop0.body,no]
end slhdsa.ParallelLowFors
