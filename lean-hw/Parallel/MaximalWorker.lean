import Parallel.QueueOrder
import Parallel.TicketProjection
import Parallel.PhaseTwoObserved

namespace slhdsa.MaximalWorker
open ParallelCached ParallelCached.Tickets ParallelSigning

abbrev Jobs := List (List (Nat × Unit))
abbrev State := Tickets.State Nat Unit

/-- Put the physical store labels on the existing counter machine. Claim and
retirement leave the chronological store record untouched. -/
inductive History (jobs : Jobs) (workers : Nat) : State → List Nat → Prop where
  | start : History jobs workers (initial workers) []
  | claim {i counter cells left right order} (prior : History jobs workers ⟨i,counter,left++[]::right,cells⟩ order)
      (within : i<jobs.length) :
      History jobs workers ⟨i+1,counter+1,left++jobs[i]::right,cells⟩ order
  | store {i counter cells left right tail s v order} (prior : History jobs workers ⟨i,counter,left++((s,v)::tail)::right,cells⟩ order)
      (empty : cells s=none) :
      History jobs workers ⟨i,counter,left++tail::right,fun k => if k=s then some v else cells k⟩ (s::order)
  | retire {i counter cells left right order} (prior : History jobs workers ⟨i,counter,left++[]::right,cells⟩ order)
      (all : i=jobs.length) :
      History jobs workers ⟨i,counter+1,left++right,cells⟩ order

theorem History.reachable {jobs workers st order} (h : History jobs workers st order) : Reach jobs workers st := by
  induction h with
  | start => exact .start
  | claim _ inside ih => exact .next ih (.claim _ _ _ _ _ inside)
  | store _ empty ih => exact .next ih (.store _ _ _ _ _ _ _ _ empty)
  | retire _ last ih => exact .next ih (.retire _ _ _ _ _ last)

theorem History.recorded {jobs workers st order} (h : History jobs workers st order) :
    order.Nodup ∧ ∀ s, s∈order ↔ st.cells s=some () := by
  induction h with
  | start => simp [initial]
  | claim _ _ ih | retire _ _ ih => exact ih
  | @store i counter cells left right tail s v order prior empty ih =>
    obtain ⟨unique,read⟩ := ih
    have fresh : s∉order := fun known => by have := (read s).mp known;simp [empty] at this
    refine ⟨List.nodup_cons.mpr ⟨fresh,unique⟩,?_⟩
    intro k
    by_cases eq : k=s <;> simp [eq,read]

theorem History.advance {jobs workers before after order} (h : History jobs workers before order)
    (move : Step jobs before after) : ∃ later, History jobs workers after later ∧ order <:+ later := by
  cases move with
  | claim l r i ctr cells within => exact ⟨order,.claim h within,List.suffix_refl _⟩
  | store l r tail i ctr cells s v empty => exact ⟨s::order,.store h empty,List.suffix_cons _ _⟩
  | retire l r i ctr cells all => exact ⟨order,.retire h all,List.suffix_refl _⟩

theorem History.along {jobs workers st final order} (h : History jobs workers st order)
    (path : Relation.ReflTransGen (Step jobs) st final) :
    ∃ endOrder, History jobs workers final endOrder ∧ order <:+ endOrder := by
  induction path with
  | refl => exact ⟨order,h,List.suffix_refl _⟩
  | tail path move ih =>
    obtain ⟨current,now,past⟩ := ih
    obtain ⟨later,done,contains⟩ := now.advance move
    exact ⟨later,done,past.trans contains⟩

theorem History.extend {jobs workers st order} (h : History jobs workers st order) :
    ∃ final later, Relation.ReflTransGen (Step jobs) st final ∧ History jobs workers final later ∧
      order <:+ later ∧ ¬∃ next, Step jobs final next := by
  obtain ⟨final,path,_,stopped⟩ := maximal_extension h.reachable
  obtain ⟨log,last,suffix⟩ := h.along path
  exact ⟨final,log,path,last,suffix,stopped⟩

/-- The layout concerns ticket ownership alone, before any cryptographic result
or execution order is known. A projection can select a table from mixed jobs. -/
structure Layout (n : Nat) where
  jobs : Jobs
  reducer : List Nat
  select : Nat → Option Nat
  unique : (jobs.flatten.map Prod.fst).Nodup
  cover : (((jobs.flatten.map Prod.fst) ++ reducer).filterMap select).Perm (List.range n)

structure Maximal {n : Nat} (layout : Layout n) (workers : Nat) where
  state : State
  order : List Nat
  history : History layout.jobs workers state order
  stopped : ¬∃ next, Step layout.jobs state next

theorem order_complete {jobs workers st order} (h : History jobs workers st order)
    (unique : (jobs.flatten.map Prod.fst).Nodup) (positive : 0<workers) (stopped : ¬∃ next, Step jobs st next) :
    order.Perm (jobs.flatten.map Prod.fst) ∧ st.counter=jobs.length+workers ∧ st.live=[] := by
  obtain ⟨counter,noLive,all⟩ := maximal_join h.reachable positive unique stopped
  refine ⟨(List.perm_ext_iff_of_nodup h.recorded.1 unique).mpr ?_, counter,noLive⟩
  intro s
  rw [(h.recorded.2 s),joined all]
  have shape := Tickets.allWrites jobs
  constructor
  · rintro ⟨j,inside,member⟩
    apply List.mem_map.mpr
    exact ⟨(s,()),shape ▸ List.mem_flatMap.mpr ⟨j,List.mem_range.mpr inside,member⟩,rfl⟩
  · intro member
    obtain ⟨⟨t,u⟩,pair,rfl⟩ := List.mem_map.mp member
    rw [←shape] at pair
    obtain ⟨j,jobs,part⟩ := List.mem_flatMap.mp pair
    exact ⟨j,List.mem_range.mp jobs,part⟩

def Maximal.schedule {n workers} {layout : Layout n} (execution : Maximal layout workers) (positive : 0<workers) :
    WidthEight.Ticket.Schedule n :=
  let complete := order_complete execution.history layout.unique positive execution.stopped
  let chronology := layout.reducer.reverse++execution.order
  have all : chronology.Perm ((layout.jobs.flatten.map Prod.fst)++layout.reducer) :=
    (layout.reducer.reverse_perm.append complete.1).trans List.perm_append_comm
  ⟨n+1,chronology.filterMap layout.select,trace_of_perm ((all.filterMap layout.select).trans layout.cover),by omega⟩

/-- Queue order and multirow visibility at the last-finisher boundary match the
terminal physical table for any permutation of the jobs and ordinary writes. -/
theorem equal_at_reduction {jobs sorted : Jobs} (perm : jobs.Perm sorted) {workers st order}
    (h : History jobs workers st order) (positive : 0<workers) (unique : (jobs.flatten.map Prod.fst).Nodup)
    (stopped : ¬∃ next, Step jobs st next) {i active done cells}
    (finisher : ParallelFused.LastFinisher.History sorted i active done cells) (last : done.length=sorted.length) :
    cells=st.cells := by
  obtain ⟨_,_,terminal⟩ := maximal_join h.reachable positive unique stopped
  obtain ⟨_,final,reference,atLast⟩ := ParallelFused.LastFinisher.can_finish unique
    (ParallelFused.LastFinisher.History.start (jobs:=jobs))
  have same := ParallelFused.LastFinisher.reordered_cells perm reference atLast finisher last
  exact same.symm.trans (interleavings (ParallelFused.LastFinisher.reducer_cells reference atLast) terminal)

end slhdsa.MaximalWorker
