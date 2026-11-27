import Aeneas

open Aeneas Aeneas.Std Result ControlFlow

namespace ParallelWorkerCells

/-- A shared reference addresses a typed field of the common signer heap. -/
structure Ref (Heap T : Type) where
  read : Heap → Option T
  write : T → Heap → Heap

def get {H T} (ref : Ref H T) : StateT H Result (Option T) :=
  fun h => ok (ref.read h, h)

def set {H T} (ref : Ref H T) (v : T) : StateT H Result (core.result.Result Unit T) :=
  fun h => match ref.read h with
    | none => ok (.Ok (), ref.write v h)
    | some _ => ok (.Err v, h)

theorem set_empty {H T} (ref : Ref H T) (v : T) (h : H) (free : ref.read h = none) :
    set ref v h = ok (.Ok (), ref.write v h) := by simp [set, free]

theorem set_full {H T} (ref : Ref H T) (v old : T) (h : H) (full : ref.read h = some old) :
    set ref v h = ok (.Err v, h) := by simp [set, full]

/-- Thread the *same* heap through the extracted loop combinator. The body
may read or update it before taking either branch. -/
def runLoop {H A B : Type} (body : A → StateT H Result (ControlFlow A B))
    (a : A) : StateT H Result B :=
  fun h => loop (fun (a, h) => do
    let (next, h') ← body a h
    match next with
    | cont a' => ok (cont (a', h'))
    | done b => ok (done (b, h'))) (a, h)

theorem runLoop_done {H A B} (body : A → StateT H Result (ControlFlow A B))
    (a : A) (b : B) (h h' : H) (step : body a h = ok (done b, h')) :
    runLoop body a h = ok (b,h') := by
  unfold runLoop
  rw [loop]
  simp [step, bind_ok]

theorem runLoop_cont {H A B} (body : A → StateT H Result (ControlFlow A B))
    (a a' : A) (h h' : H) (step : body a h = ok (cont a', h')) :
    runLoop body a h = runLoop body a' h' := by
  unfold runLoop
  rw [loop]
  simp [step, bind_ok]

end ParallelWorkerCells
