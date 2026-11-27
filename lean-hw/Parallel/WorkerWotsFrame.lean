import Parallel.WorkerWotsHistory

namespace ParallelWorkerRuntime.Wots
open Aeneas Aeneas.Std Result ParallelWorkerHeap ParallelWorkerInterleave Aeneas.Data.Coinductive

private theorem local_frame {N len values w w'} {h h' : Shared N} (key : Key)
    (disjoint : ∀ j, .wotsSigs j≠key)
    (owner : Residual N len values w) (event : Step h [w] h' [w']) :
    h'.cells key=h.cells key := by
  cases owner with
  | next =>
    rw [unfold_worker] at event
    obtain ⟨rfl,_⟩ := event.unique_worker (Step.atomic h [] [] _ _)
    rfl
  | save j live =>
    unfold saving at event
    obtain ⟨rfl,_⟩ := event.unique_worker (Step.atomic h [] [] _ _)
    split
    · exact frame _ _ _ (disjoint j.val) _
    · rfl
  | retired =>
    obtain ⟨_,_,impossible,_,_⟩ := event.single_view
    change ITree.ret () = ITree.vis _ _ at impossible
    grind
  | failed =>
    obtain ⟨_,_,impossible,_,_⟩ := event.single_view
    cases vis_inj_effect impossible

/-- For every possible prefix, WOTS workers leave all foreign cells untouched. -/
theorem untouched {N len} (values : Usize → Bytes) (h h' : Shared N) (workers : Nat)
    (threads : List (Program (Shared N) Unit))
    (run : Steps h (List.replicate workers (worker N len values)) h' threads)
    (init : Correct len values h) (key : Key) (disjoint : ∀ j, .wotsSigs j ≠ key) :
    h'.cells key=h.cells key := by
  let inv := fun (s : Shared N × List (Program (Shared N) Unit)) =>
    s.1.cells key=h.cells key ∧ Correct len values s.1 ∧ ∀ w∈s.2, Residual N len values w
  have start : inv (h,List.replicate workers (worker N len values)) := by
    refine ⟨rfl,init,?_⟩
    intro w member
    obtain ⟨_,rfl⟩ := List.mem_replicate.mp member
    exact .next
  have preserve {x y : Shared N × List (Program (Shared N) Unit)}
      (old : inv x) (event : Step x.1 x.2 y.1 y.2) : inv y := by
    rcases x with ⟨s,xs⟩; rcases y with ⟨t,ys⟩
    dsimp only at event
    cases event with
    | atomic left right f k =>
      obtain ⟨eq,correct,owned⟩ := old
      have active := owned _ (List.mem_append_right _ List.mem_cons_self)
      have moved := Step.atomic s [] [] f k
      obtain ⟨good,residual⟩ := local_safe active moved correct
      refine ⟨(local_frame key disjoint active moved).trans eq,good,?_⟩
      intro w member
      rcases List.mem_append.mp member with before | after
      · exact owned _ (List.mem_append_left _ before)
      rcases List.mem_cons.mp after with rfl | tail
      · exact residual
      · exact owned _ (List.mem_append_right _ (List.mem_cons_of_mem _ tail))
  exact (Relation.ReflTransGen.head_induction_on run
    (motive := fun s _ => inv s → inv (h',threads)) id
    (fun step _ ih old => ih (preserve old step)) start).1

end ParallelWorkerRuntime.Wots
