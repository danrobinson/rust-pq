import Parallel.WorkerCells

open Aeneas Aeneas.Std Result ControlFlow Aeneas.Data.Coinductive

namespace ParallelWorkerInterleave

/-- The response to an atomic update is the heap at its linearization point. -/
inductive Operation (H : Type)
  | atomic (update : H → H)
  | fail (e : Error)

@[reducible] def effects (H : Type) : Effect where
  I := Operation H
  O := fun op => match op with
    | .atomic _ => H
    | .fail _ => PEmpty

abbrev Program (H A : Type) := ITree (effects H) A

def liftResult {H A : Type} (r : Result A) : Program H A :=
  match r.match with
  | .ok a => .ret a
  | .div => .div
  | .vis (.fail e) _ => .vis (.fail e) PEmpty.elim

instance {H} : MonadLift Result (Program H) where
  monadLift := liftResult

@[simp] theorem lift_ok {H A} (x : A) : (liftResult (H := H) (ok x)) = pure x := by
  simp [liftResult]

theorem lift_bind {H A B : Type} (x : Result A) (f : A → Result B) :
    liftResult (H := H) (x >>= f) = (liftResult x >>= fun v => liftResult (f v)) := by
  cases x with
  | ret x => rw [bind_tc_ok, lift_ok, pure_bind]
  | div => simp [bind_tc_eq, liftResult, Aeneas.Data.Coinductive.div_bind]
  | vis eff k =>
    cases eff with
    | fail e =>
      have eq : k = PEmpty.elim := funext (fun v => nomatch v)
      subst k
      change liftResult (H := H) (Result.fail e >>= f) = (liftResult (Result.fail e) >>= _)
      simp [bind_tc_eq, liftResult, Aeneas.Data.Coinductive.vis_bind]
      congr 1
      funext v; cases v

def get {H T} (ref : ParallelWorkerCells.Ref H T) : Program H (Option T) :=
  .vis (.atomic id) (fun h => .ret (ref.read h))

def set {H T} (ref : ParallelWorkerCells.Ref H T) (v : T) :
    Program H (core.result.Result Unit T) :=
  .vis (.atomic (fun h => match ref.read h with
    | some _ => h | none => ref.write v h))
    (fun h => .ret (match ref.read h with | some _ => .Err v | none => .Ok ()))

def runLoop {H A B} (body : A → Program H (ControlFlow A B)) (a : A) : Program H B :=
  ITree.iter (fun x => do
    match ← body x with
    | cont x' => return .inl x'
    | done b => return .inr b) a

theorem runLoop_unfold {H A B} (body : A → Program H (ControlFlow A B)) (a : A) :
    runLoop body a = (body a >>= fun x => match x with
      | cont b => runLoop body b | done val => pure val) := by
  conv => lhs; unfold runLoop; rw [ITree.iter]
  change ((body a >>= _) >>= _) = _
  rw [bind_assoc]
  congr 1
  funext next
  cases next <;> exact itree_ret_bind _ _

@[simp] theorem lifted_ok {H A : Type} (x : A) : (liftM (ok x) : Program H A) = pure x :=
  lift_ok x

/-- One currently running worker may take one visible atomic action. No event
is enabled for a failed or diverging thread; successful returns are retained. -/
inductive Step {H A : Type} : H → List (Program H A) → H → List (Program H A) → Prop where
  | atomic (h : H) (left right : List (Program H A)) (f : H → H) (k : H → Program H A) :
    Step h (left ++ ITree.vis (E := effects H) (.atomic f) k :: right) (f h) (left ++ k h :: right)

/-- Inverting a step on a specified worker recovers its current atomic request
and the continuation receiving the old heap. -/
theorem Step.single_view {H A : Type} {h h' : H} {w w' : Program H A}
    (step : Step h [w] h' [w']) :
    ∃ (f : H → H) (k : H → Program H A),
      w = ITree.vis (E := effects H) (.atomic f) k ∧ h' = f h ∧ w' = k h := by
  generalize startEq : [w] = xs at step
  generalize endEq : [w'] = ys at step
  cases step with
  | atomic l r f k =>
    cases l with
    | nil =>
      simp at startEq endEq
      exact ⟨f,k,startEq.1,rfl,endEq.1⟩
    | cons a l =>
      have sizes := congrArg List.length startEq
      simp at sizes

theorem Step.unique_worker {H A : Type} {h h₁ h₂ : H} {w w₁ w₂ : Program H A}
    (first : Step h [w] h₁ [w₁]) (second : Step h [w] h₂ [w₂]) :
    h₁ = h₂ ∧ w₁ = w₂ := by
  obtain ⟨f,k,rfl,rfl,rfl⟩ := first.single_view
  obtain ⟨g,j,eq,rfl,rfl⟩ := second.single_view
  obtain ⟨same,cont⟩ := vis_inj eq
  have fg : f = g := Operation.atomic.inj same
  subst g
  have kj : k = j := eq_of_heq cont
  subst j
  exact ⟨rfl,rfl⟩

theorem Step.continuation {H A B : Type} {h h' : H} {w w' : Program H A}
    (step : Step h [w] h' [w']) (f : A → Program H B) (l r : List (Program H B)) :
    Step h (l ++ (w >>= f) :: r) h' (l ++ (w' >>= f) :: r) := by
  obtain ⟨update,k,rfl,rfl,rfl⟩ := step.single_view
  rw [vis_bind]
  exact Step.atomic h l r update (fun old => k old >>= f)

/-- Finite schedules of workers using the same heap. -/
def Steps {H A : Type} (h : H) (threads : List (Program H A))
    (h' : H) (threads' : List (Program H A)) : Prop :=
  Relation.ReflTransGen (fun (x y : H × List (Program H A)) => Step x.1 x.2 y.1 y.2)
    (h, threads) (h', threads')

theorem Step.single {H A : Type} {h h' : H} {xs ys : List (Program H A)}
    (step : Step h xs h' ys) : Steps h xs h' ys := Relation.ReflTransGen.single step

theorem Steps.follow {H A : Type} {h mid dest : H} {xs ys zs : List (Program H A)}
    (prior : Steps h xs mid ys) (step : Step mid ys dest zs) : Steps h xs dest zs :=
  Relation.ReflTransGen.tail prior step

theorem atomic_bind {H T A} (f : H → H) (answer : H → T)
    (k : T → Program H A) :
    ((ITree.vis (E := effects H) (.atomic f) (fun h => ITree.ret (answer h))) >>= k) =
      ITree.vis (E := effects H) (.atomic f) (fun h => k (answer h)) := by
  exact (itree_vis_bind (E := effects H) (.atomic f) (fun h => ITree.ret (answer h)) k).trans
    (congrArg (ITree.vis (E := effects H) (.atomic f))
      (funext (fun h => itree_ret_bind (E := effects H) (answer h) k)))

theorem get_step {H T A} (ref : ParallelWorkerCells.Ref H T) (k : Option T → Program H A)
    (h : H) (l r : List (Program H A)) :
    Step h (l ++ (get ref >>= k) :: r) h (l ++ k (ref.read h) :: r) := by
  unfold get
  rw [atomic_bind]
  exact (Step.atomic h l r id (fun h => k (ref.read h)))

theorem set_step {H T A} (ref : ParallelWorkerCells.Ref H T) (v : T)
    (k : core.result.Result Unit T → Program H A) (h : H) (l r : List (Program H A)) :
    Step h (l ++ (set ref v >>= k) :: r)
      (match ref.read h with | some _ => h | none => ref.write v h)
      (l ++ k (match ref.read h with | some _ => .Err v | none => .Ok ()) :: r) := by
  unfold set
  rw [atomic_bind (fun h => match ref.read h with | some _ => h | none => ref.write v h)
    (fun h => match ref.read h with | some _ => .Err v | none => .Ok ()) k]
  exact (Step.atomic h l r
    (fun h => match ref.read h with | some _ => h | none => ref.write v h)
    (fun h => k (match ref.read h with | some _ => .Err v | none => .Ok ())))

end ParallelWorkerInterleave
