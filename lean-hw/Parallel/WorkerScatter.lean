import Parallel.WorkerInterleave

open Aeneas Aeneas.Std ParallelWorkerInterleave
namespace ParallelWorkerScatter

theorem othersStep {H A : Type} {h h' : H} {xs ys : List (Program H A)}
    (active : Program H A) (move : Step h xs h' ys) : Step h (active::xs) h' (active::ys) := by
  cases move with
  | atomic l r f k => exact Step.atomic _ (active::l) r f k

theorem othersRun {H A : Type} {h h' : H} {xs ys : List (Program H A)}
    (active : Program H A) (moves : Steps h xs h' ys) : Steps h (active::xs) h' (active::ys) := by
  let embed := fun (s : H × List (Program H A)) => (s.1, active :: s.2)
  exact moves.lift embed (fun _ _ step => othersStep active step)

/-- The selected worker stores every lane in order. Between two such stores
all other workers may execute an arbitrary finite schedule. -/
inductive Scatter {H A : Type} (limit : Nat) (store : Nat → H → Option H) :
    Nat → H → List (Program H A) → H → List (Program H A) → Prop where
  | done {i h peers} (past : limit ≤ i) : Scatter limit store i h peers h peers
  | peer {i h h' dest peers peers' finalPeers} (other : Step h peers h' peers')
      (rest : Scatter limit store i h' peers' dest finalPeers) : Scatter limit store i h peers dest finalPeers
  | next {i h h₁ h₂ final peers peers₂ finalPeers}
      (live : i < limit) (write : store i h = some h₁)
      (others : Steps h₁ peers h₂ peers₂)
      (rest : Scatter limit store (i+1) h₂ peers₂ final finalPeers) :
      Scatter limit store i h peers final finalPeers

def storeAt {H T} (refs : alloc.vec.Vec (ParallelWorkerCells.Ref H T))
    (values : List T) (idx : Nat → Nat) (lane : Nat) (h : H) : Option H := do
  let ref ← refs.val[idx lane]?
  let v ← values[lane]?
  if (ref.read h).isNone then some (ref.write v h) else none

theorem storeAt_eq {H T} (refs : alloc.vec.Vec (ParallelWorkerCells.Ref H T))
    (values : List T) (idx : Nat → Nat) (lane : Nat) (h h' : H)
    (fits : idx lane < refs.length) (live : lane < values.length) :
    storeAt refs values idx lane h = some h' ↔
    refs.val[idx lane].read h = none ∧ refs.val[idx lane].write values[lane] h = h' := by
  simp [storeAt, List.getElem?_eq_getElem fits, List.getElem?_eq_getElem live]

/-- A scatter on distinct initially empty physical locations always has a
completed schedule even if no peer takes a step. -/
theorem serial {H T A} (refs : alloc.vec.Vec (ParallelWorkerCells.Ref H T))
    (values : List T) (idx : Nat → Nat) (limit : Nat) (width : limit ≤ values.length)
    (fits : ∀ i < limit, idx i < refs.length)
    (frame : ∀ i (hi : i < limit) j (hj : j < limit), i < j → ∀ v h,
      (refs.val[idx j]'(fits j hj)).read ((refs.val[idx i]'(fits i hi)).write v h) =
      (refs.val[idx j]'(fits j hj)).read h)
    (i : Nat) (h : H) (peers : List (Program H A))
    (free : ∀ j, i ≤ j → (hj : j < limit) → (refs.val[idx j]'(fits j hj)).read h = none) :
    ∃ dest, Scatter limit (storeAt refs values idx) i h peers dest peers := by
  by_cases live : i < limit
  · let ref := refs.val[idx i]'(fits i live)
    let value := values[i]'(by omega)
    let next := ref.write value h
    have write : storeAt refs values idx i h = some next :=
      (storeAt_eq refs values idx i h next (fits i live) (by omega)).mpr ⟨free i (by omega) live,rfl⟩
    have rest (j : Nat) (ahead : i+1 ≤ j) (bound : j < limit) :
        (refs.val[idx j]'(fits j bound)).read next = none := by
      rw [show (refs.val[idx j]'(fits j bound)).read next = (refs.val[idx j]'(fits j bound)).read h from
        frame i live j bound (by omega) value h]
      exact free j (by omega) bound
    obtain ⟨dest, done⟩ := serial refs values idx limit width fits frame (i+1) next peers rest
    exact ⟨dest,.next live write .refl done⟩
  · exact ⟨h,.done (by omega)⟩
termination_by limit-i

/-- Lift the single-lane kernel equations to the whole loop. This uses
the emitted continuation at its new range, so other workers can take steps
before the next lane reads the heap. -/
theorem realize {H A} {ty : UScalarTy} (limit : UScalar ty) (store : Nat → H → Option H)
    (worker : core.ops.range.Range (UScalar ty) → Program H A) (finish : Program H A)
    (advance : ∀ (it : core.ops.range.Range (UScalar ty)) (h dest : H) (peers : List (Program H A)),
      it.end = limit → it.start.val < limit.val → store it.start.val h = some dest →
      ∃ next : core.ops.range.Range (UScalar ty), next.start.val = it.start.val+1 ∧ next.end = limit ∧
        Step h (worker it :: peers) dest (worker next :: peers))
    (exhausted : ∀ it : core.ops.range.Range (UScalar ty), it.end = limit → limit.val ≤ it.start.val →
      worker it = finish)
    {i h peers dest others} (schedule : Scatter limit.val store i h peers dest others)
    (it : core.ops.range.Range (UScalar ty)) (start : it.start.val = i) (stop : it.end = limit) :
    Steps h (worker it :: peers) dest (finish :: others) := by
  induction schedule generalizing it with
  | done past => rw [exhausted it stop (start ▸ past)]; exact .refl
  | peer move rest ih =>
    exact Relation.ReflTransGen.trans (othersStep (worker it) move).single (ih it start stop)
  | next live write moves rest ih =>
    obtain ⟨next, inc, ends, performed⟩ := advance it _ _ _ stop (start ▸ live) (start ▸ write)
    exact Relation.ReflTransGen.trans
      (Relation.ReflTransGen.trans performed.single (othersRun (worker next) moves))
      (ih next (by omega) ends)

/-- Observe a distinguished worker until it returns. Only the scheduler's
choice and the actual program transition determine the trace. A live worker
owns its target when selected; peers may execute arbitrary steps. -/
inductive Observed {H : Type} (available : Nat → H → Prop) :
    Nat → H → Program H Unit → List (Program H Unit) → H → List (Program H Unit) → Prop where
  | returned {i h xs} : Observed available i h (pure ()) xs h xs
  | own {i h p xs h' p' dest final}
      (ready : available i h) (action : Step h [p] h' [p'])
      (rest : Observed available (i+1) h' p' xs dest final) :
      Observed available i h p xs dest final
  | peer {i h p xs h' xs' dest final} (other : Step h xs h' xs')
      (rest : Observed available i h' p xs' dest final) : Observed available i h p xs dest final

private theorem returned_stuck {H} {h dest : H} {q : Program H Unit} :
    ¬ Step h [pure ()] dest [q] := by
  intro step
  obtain ⟨f,k,eq,_,_⟩ := step.single_view
  exact Aeneas.Data.Coinductive.not_vis_ret eq

/-- Every normal observed worker trace gives precisely the independently
specified stores. Determinism rules out a skipped lane, changed payload, or
an additional access by the selected worker. -/
theorem reflect {H} {ty : UScalarTy} (limit : UScalar ty) (store : Nat → H → Option H)
    (worker : core.ops.range.Range (UScalar ty) → Program H Unit)
    (possible : ∀ i < limit.val, ∃ h dest, store i h = some dest)
    (advance : ∀ (it : core.ops.range.Range (UScalar ty)) (h dest : H),
      it.end = limit → it.start.val < limit.val → store it.start.val h = some dest →
      ∃ next : core.ops.range.Range (UScalar ty), next.start.val = it.start.val+1 ∧ next.end = limit ∧
        Step h [worker it] dest [worker next])
    (exhausted : ∀ it : core.ops.range.Range (UScalar ty), it.end = limit → limit.val ≤ it.start.val →
      worker it = pure ())
    {i h p peers dest others}
    (trace : Observed (fun i h => i < limit.val → ∃ out, store i h = some out) i h p peers dest others)
    (it : core.ops.range.Range (UScalar ty)) (index : it.start.val = i) (ends : it.end = limit)
    (running : worker it = p) : Scatter limit.val store i h peers dest others := by
  induction trace generalizing it with
  | returned =>
    by_cases live : it.start.val < limit.val
    · obtain ⟨h₀,h₁,write⟩ := possible _ live
      obtain ⟨_,_,_,step⟩ := advance it h₀ h₁ ends live write
      rw [running] at step
      exact False.elim (returned_stuck step)
    · exact .done (by omega)
  | peer move rest ih => exact .peer move (ih it index ends running)
  | own ready action rest ih =>
    by_cases live : it.start.val < limit.val
    · obtain ⟨h',write⟩ := ready (index ▸ live)
      obtain ⟨next,inc,stop,expected⟩ := advance it _ h' ends live (index ▸ write)
      rw [running] at expected
      obtain ⟨same,continuation⟩ := expected.unique_worker action
      subst h'
      exact .next (by omega) write .refl (ih next (by omega) stop continuation)
    · rw [←running, exhausted it ends (by omega)] at action
      exact False.elim (returned_stuck action)

end ParallelWorkerScatter
