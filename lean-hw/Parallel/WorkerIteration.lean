import Aeneas

namespace ParallelWorkerIteration
open Aeneas Aeneas.Std ControlFlow

/-- One phase-one iteration, with its library operations supplied by the
interpreter. The extraction gate instantiates this same definition with the
actual generated expressions and checks the equality by kernel reduction. -/
def iteration {M : Type → Type} [Monad M] {I Job : Type} [DecidableEq I]
    (claim : M I) (lookup : I → M (Option Job)) (dispatch : Job → M Unit)
    (complete : M I) (increment : I → M I) (total : I) (reduce publish : M Unit) :
    M (ControlFlow Unit Unit) := do
  let ticket ← claim
  let item ← lookup ticket
  match item with
  | none => pure (done ())
  | some job =>
    dispatch job
    let old ← complete
    let count ← increment old
    if count=total then
      reduce
      publish
      pure (cont ())
    else pure (cont ())

inductive Event (Job : Type) where
  | claim (old : Nat)
  | lookup (index : Nat)
  | dispatch (job : Job)
  | complete (old : Nat)
  | reduce
  | publish

structure Shared (Job : Type) where
  next : Nat
  completed : Nat
  events : List (Event Job)

/-- A sequential interpreter for a single worker with a shared counter and
a chronological log. The concurrency simulation is in WorkerFetch. -/
def execute {Job : Type} (jobs : List Job) : StateM (Shared Job) (ControlFlow Unit Unit) :=
  iteration
    (fun s => (s.next, {s with next := s.next+1, events := s.events++[.claim s.next]}))
    (fun i s => (jobs[i]?, {s with events := s.events++[.lookup i]}))
    (fun job s => ((),{s with events := s.events++[.dispatch job]}))
    (fun s => (s.completed,{s with completed := s.completed+1,events := s.events++[.complete s.completed]}))
    (fun i => pure (i+1)) jobs.length
    (fun s => ((),{s with events := s.events++[.reduce]}))
    (fun s => ((),{s with events := s.events++[.publish]}))

theorem exhausted {Job} (jobs : List Job) (s : Shared Job) (past : jobs.length≤s.next) :
    execute jobs s = (done (),{s with next:=s.next+1,events:=s.events++[.claim s.next,.lookup s.next]}) := by
  simp [execute,iteration,Bind.bind,Pure.pure,StateT.bind,StateT.pure,List.getElem?_eq_none past]

theorem claimed {Job} (jobs : List Job) (s : Shared Job) (job : Job) (found : jobs[s.next]?=some job) :
    execute jobs s = (cont (),⟨s.next+1,s.completed+1,s.events++
      [.claim s.next,.lookup s.next,.dispatch job,.complete s.completed]++
      (if s.completed+1=jobs.length then [.reduce,.publish] else [])⟩) := by
  by_cases last : s.completed+1=jobs.length <;>
    simp [execute,iteration,Bind.bind,Pure.pure,StateT.bind,StateT.pure,found,last,List.append_assoc]

/-- The second queue uses the claimed index for both layer and root. A checked
store can fail, so its result must be consumed before starting another ticket. -/
def wots {M : Type → Type} [Monad M] {I Slot A K R V Put : Type}
    (claim : M I) (lookup : I → M (Option Slot)) (layer : I → M (A × K))
    (root : I → M R) (typed : A → M A) (keypair : A → K → M A)
    (sign : R → A → M V) (store : Slot → V → M Put) (expect : Put → M Unit) :
    M (ControlFlow Unit Unit) := do
  let j ← claim
  let dest ← lookup j
  match dest with
  | none => pure (done ())
  | some slot =>
    let (a,k) ← layer j
    let r ← root j
    let a₁ ← typed a
    let a₂ ← keypair a₁ k
    let sig ← sign r a₂
    let result ← store slot sig
    expect result
    pure (cont ())

structure WotsHeap (V : Type) where
  next : Nat
  cells : Nat → Option V

def wotsExecute {A K R V : Type} (count : Nat) (layer : Nat → A × K) (root : Nat → R)
    (typed : A → A) (keypair : A → K → A) (sign : R → A → V) :
    StateT (WotsHeap V) Option (ControlFlow Unit Unit) :=
  wots (fun s => some (s.next,{s with next:=s.next+1}))
    (fun i => pure (if i<count then some i else none)) (fun i => pure (layer i))
    (fun i => pure (root i)) (fun a => pure (typed a)) (fun a k => pure (keypair a k))
    (fun r a => pure (sign r a))
    (fun slot v s => match s.cells slot with
      | some _ => some (false,s)
      | none => some (true,{s with cells:=fun i => if i=slot then some v else s.cells i}))
    (fun accepted s => if accepted then some ((),s) else none)

theorem wots_store {A K R V} (count : Nat) (layer : Nat → A × K) (root : Nat → R)
    (typed : A → A) (keypair : A → K → A) (sign : R → A → V) (s : WotsHeap V)
    (live : s.next<count) (empty : s.cells s.next=none) :
    wotsExecute count layer root typed keypair sign s =
      some (cont (),⟨s.next+1,fun i => if i=s.next then
        some (sign (root i) (keypair (typed (layer i).1) (layer i).2)) else s.cells i⟩) := by
  simp [wotsExecute,wots,Bind.bind,Pure.pure,StateT.bind,StateT.pure,Option.bind,live,empty]
  funext i
  split <;> simp_all

theorem wots_exhausted {A K R V} (count : Nat) (layer : Nat → A × K) (root : Nat → R)
    (typed : A → A) (keypair : A → K → A) (sign : R → A → V) (s : WotsHeap V)
    (past : count≤s.next) :
    wotsExecute count layer root typed keypair sign s =
      some (done (),{s with next:=s.next+1}) := by
  simp [wotsExecute,wots,Bind.bind,Pure.pure,StateT.bind,StateT.pure,Option.bind,Nat.not_lt.mpr past]

theorem wots_duplicate {A K R V} (count : Nat) (layer : Nat → A × K) (root : Nat → R)
    (typed : A → A) (keypair : A → K → A) (sign : R → A → V) (s : WotsHeap V) (prior : V)
    (live : s.next<count) (occupied : s.cells s.next=some prior) :
    wotsExecute count layer root typed keypair sign s = none := by
  simp [wotsExecute,wots,Bind.bind,Pure.pure,StateT.bind,StateT.pure,Option.bind,live,occupied]

end ParallelWorkerIteration
