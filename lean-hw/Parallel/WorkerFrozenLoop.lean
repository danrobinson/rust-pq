import Parallel.WorkerFrozenReads

namespace ParallelWorkerFrozenReads
open Aeneas Aeneas.Std Result ControlFlow Aeneas.Data.Coinductive
open ParallelWorkerRuntime ParallelWorkerInterleave ParallelWorkerCounterSafety
noncomputable section
unseal Result

private def resultSem : EffectWP RustEffect where
  State := Unit
  wp _ _ _ := True

private instance : resultSem.Monotonic where
  wp_monotonic := by intros; trivial

private instance : resultSem.Conjunctive where
  wp_conj := by intros; trivial

/-- A successful evaluation of the read-only worker on the snapshot witnesses every
actual load of the running worker. The evaluator fails on uninitialized reads. -/
structure Frozen (base : Shared N) (A : Type) where
  actual : Certified N A
  eval : Result A
  sound : ∀ a, eval = ok a → Reads base actual.raw a

private def successPost {A : Type} (r : Result A) (P : A → Prop) :=
  DWLP resultSem r (fun a _ => P a) ()

private theorem success_iff {A : Type} (r : Result A) (P : A → Prop) :
    successPost r P ↔ ∀ a, r=ok a → P a := by
  cases r with
  | ret a =>
    simp only [ok.injEq,forall_eq']
    exact DWLP.ret_iff
  | div => exact ⟨by simp,fun _ => DWLP.div⟩
  | vis e k => cases e; exact ⟨by simp,fun _ => DWLP.vis trivial⟩

private def ret (v : A) : Frozen base A where
  actual := pure v
  eval := ok v
  sound := by intro a eq; cases Result.ok_injective eq; exact .done _

private def bindFrozen (p : Frozen base A) (k : A → Frozen base B) : Frozen base B where
  actual := p.actual >>= fun a => (k a).actual
  eval := p.eval >>= fun a => (k a).eval
  sound := by
    refine (success_iff _ _).mp ?_
    apply DWLP.bind ((success_iff ..).mpr p.sound)
    intro a _ read
    apply DWLP.mono ((success_iff ..).mpr (k a).sound)
    intro b _ next
    exact read.bind _ next

instance : Monad (Frozen base) where
  pure := ret
  bind := bindFrozen

instance : MonadLift Result (Frozen base) where
  monadLift r := {
    actual := liftM r
    eval := r
    sound := by intro a eq; rw [raw_lift,eq,lifted_ok]; exact .done _
  }

def frozenGet (base : Shared N) (p : Physical N T) : Frozen base (Option T) where
  actual := ParallelWorkerCounterSafety.get p
  eval := match p.ref.read base with | none => fail .panic | some v => ok (some v)
  sound := by
    intro out eq
    cases h : p.ref.read base with
    | none => simp [h] at eq
    | some v =>
      simp only [h,ok.injEq] at eq
      cases eq
      exact typed_load base p v h

def frozenLoop (body : A → Frozen base (ControlFlow A B)) (a : A) : Frozen base B where
  actual := ParallelWorkerCounterSafety.loop (fun x => (body x).actual) a
  eval := Aeneas.Std.loop (fun x => (body x).eval) a
  sound := by
    refine (success_iff _ _).mp ?_
    let actual := fun x => runLoop (fun y => (body y).actual.raw) x
    suffices all : ∀ x, successPost (Aeneas.Std.loop (fun y => (body y).eval) x) (Reads base (actual x)) from all a
    apply Aeneas.Std.loop.fixpoint_induct (fun y => (body y).eval)
      (fun f => ∀ x, successPost (f x) (Reads base (actual x)))
    · exact Lean.Order.admissible_pi_apply _ (fun x => DWLP.admissible resultSem _ ())
    · intro f ih x
      apply DWLP.bind ((success_iff ..).mpr (body x).sound)
      intro flow _ read
      have eq : actual x = ((body x).actual.raw >>= fun flow =>
          match flow with | .cont y => actual y | .done v => pure v) := runLoop_unfold _ _
      cases flow with
      | done b =>
        apply DWLP.ret_iff.mpr
        rw [eq]
        exact read.bind _ (.done _)
      | cont y =>
        apply DWLP.mono (ih y)
        intro b _ next
        rw [eq]
        exact read.bind _ next

theorem eval_bind (p : Frozen base A) (k : A → Frozen base B) :
    (p >>= k).eval = (p.eval >>= fun a => (k a).eval) := rfl
theorem eval_lift (r : Result A) : (liftM r : Frozen base A).eval = r := rfl

theorem actual_bind (p : Frozen base A) (k : A → Frozen base B) :
    (p >>= k).actual = (p.actual >>= fun a => (k a).actual) := rfl
theorem actual_lift (r : Result A) : (liftM r : Frozen base A).actual = (liftM r : Certified _ A) := rfl
theorem actual_loop (f : A → Frozen base (ControlFlow A B)) (a : A) :
    (frozenLoop f a).actual = ParallelWorkerCounterSafety.loop (fun x => (f x).actual) a := rfl

end
end ParallelWorkerFrozenReads
