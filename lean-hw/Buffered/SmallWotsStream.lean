import Buffered.SmallWotsProgram
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.Buffered.SmallWots
open ShakeBatch Spec.Keccak cache.builder.nativeShake.Vector.Fused
set_option maxHeartbeats 1500000
set_option linter.concreteInstances false
variable [kernel : Fused.Kernel]
local instance streamMachine : Machine := Fused.machine kernel

theorem absorb_word (K group : Usize) (pk : Matrix 8#usize) (pos : Usize) (state : Matrix 8#usize) (j : Usize)
    (rate : pos.val<17) (bound : j.val<25) (groups : group.val+K.val≤8) :
    leaves_loop2_loop2_loop0_loop0 ⟨0#usize,K⟩ pk pos state group j ⦃ out =>
    ∀ l<K.val, ShakeBatch.lane out l = (ShakeBatch.lane pk l).setIfInBounds pos.val
      ((ShakeBatch.lane pk l)[pos.val]! ^^^ cell state j.val (group.val+l)) ⦄ := by
  unfold leaves_loop2_loop2_loop0_loop0
  apply sweep K (leaves_loop2_loop2_loop0_loop0.body pos state group j) pk
    (fun l a => a.setIfInBounds pos.val (a[pos.val]! ^^^ cell state j.val (group.val+l)))
  · intro it acc stop live
    unfold leaves_loop2_loop2_loop0_loop0.body
    step with core.iter.range.IteratorRange.next_Usize_some_spec it (by simpa [stop] using live) as ⟨_,next,tag,inc,he⟩
    have guard : j<25#usize := bound
    simp only [tag,massert,guard,ite_true,bind_ok]
    step as ⟨laneIdx,laneEq⟩
    step as ⟨row,read⟩
    step as ⟨w,word⟩
    erw [← xorCell_bind acc pos it.start w (fun u => ok (cont (next,u)))]
    step with xorCell_spec acc pos it.start w (by omega) (by change it.start.val<8;omega) as ⟨out,changed⟩
    refine ⟨next,out,rfl,he.trans stop,inc,?_⟩
    intro l hl
    rw [changed l (by change l<8;omega),word,read,←getElem!_pos,←getElem!_pos]
    by_cases eq : l=it.start.val <;> simp only [eq,ite_true,ite_false,laneEq,cell]
  · intro it acc last stop
    unfold leaves_loop2_loop2_loop0_loop0.body
    obtain ⟨⟨_,_⟩,next,tag,_⟩ := spec_imp_exists (core.iter.range.IteratorRange.next_Usize_none_spec it (by rw [stop,last]))
    simp [next,tag]

theorem absorb_tip (K group n : Usize) (pk : Matrix 8#usize) (pos : Usize) (state : Matrix 8#usize)
    (rate : pos.val<17) (small : n.val≤25) (groups : group.val+K.val≤8) (permutes : NativeVerify.ActiveCorrect (Fused.machine kernel) kernel.active)
    (tip : Nat → Spec.Bytes) (lengths : ∀ l<K.val, (tip l).length=8*n.val)
    (words : ∀ l<K.val, ∀ j<n.val, cell state j (group.val+l)=messageWord (tip l) j) :
    leaves_loop2_loop2_loop0 K ⟨0#usize,n⟩ pk pos state group ⦃ out =>
      out.2.val<17 ∧ ∀ l<K.val, (ShakeBatch.lane out.1 l,8*out.2.val) = (tip l).foldl feed (ShakeBatch.lane pk l,8*pos.val) ⦄ := by
  let inv (j : Nat) (q : Matrix 8#usize × Usize) := q.2.val<17 ∧ ∀ l<K.val,
    (ShakeBatch.lane q.1 l,q.2.val) = (List.range j).foldl
      (fun a w => FusedStream.absorb a (messageWord (tip l) w)) (ShakeBatch.lane pk l,pos.val)
  unfold leaves_loop2_loop2_loop0
  apply WP.spec_mono (range_fold (fun it q => leaves_loop2_loop2_loop0.body K state group it q.1 q.2)
    n (pk,pos) inv (by simpa [inv] using rate) ?_ ?_)
  · rintro ⟨acc,cursor⟩ ⟨hr,h⟩
    refine ⟨hr,?_⟩
    intro l hl
    have ref := FusedStream.absorb_tip (tip l) n.val (lengths l hl) (ShakeBatch.lane pk l)
      (by simp [ShakeBatch.lane]) pos.val rate
    rw [← h l hl] at ref
    exact ref
  · rintro it ⟨acc,cursor⟩ stop live ⟨hr,old⟩
    unfold leaves_loop2_loop2_loop0.body
    step with core.iter.range.IteratorRange.next_Usize_some_spec it (by simpa [stop] using live)
      as ⟨_,next,ho,inc,he⟩
    simp only [ho]
    step with absorb_word K group acc cursor state it.start hr (by omega) groups as ⟨updated,absorbed⟩
    step as ⟨p,advance⟩
    have folded (l : Nat) (hl : l<K.val) :
        (List.range next.start.val).foldl (fun a w => FusedStream.absorb a (messageWord (tip l) w))
          (ShakeBatch.lane pk l,pos.val) = FusedStream.absorb (ShakeBatch.lane acc l,cursor.val) (cell state it.start.val (group.val+l)) := by
      rw [inc,List.range_succ,List.foldl_append,← old l hl,words l hl _ live]
      rfl
    by_cases boundary : p=17#usize
    · simp only [boundary,ite_true]
      step with permutes updated K (by change K.val≤8;omega) as ⟨mixed,permuted⟩
      refine ⟨next,(mixed,0#usize),rfl,he.trans stop,inc,by dsimp; decide,?_⟩
      intro l hl
      have last : cursor.val=16 := by rw [boundary] at advance; scalar_tac
      rw [folded l hl,permuted l hl,absorbed l hl]
      simp [FusedStream.absorb,last]
    · simp only [boundary,ite_false,step_simps]
      have last : cursor.val≠16 := by intro e; apply boundary; apply UScalar.eq_of_val_eq; scalar_tac
      refine ⟨next,(updated,p),rfl,he.trans stop,inc,by dsimp at hr ⊢; omega,?_⟩
      intro l hl
      rw [folded l hl,absorbed l hl]
      simp [FusedStream.absorb,last,advance]
  · rintro it ⟨s,p⟩ last stop
    unfold leaves_loop2_loop2_loop0.body
    obtain ⟨⟨_,_⟩,next,ho,_⟩ := spec_imp_exists (core.iter.range.IteratorRange.next_Usize_none_spec it (by rw [stop,last]))
    simp [next,ho]

end slhdsa.Buffered.SmallWots
