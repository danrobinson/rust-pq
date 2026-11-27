import Parallel.WorkerScheduleCut
import Parallel.WorkerDispatchWrites

open Aeneas Aeneas.Std Result Aeneas.Data.Coinductive
open ParallelWorkerHeap ParallelWorkerRuntime ParallelWorkerInterleave ParallelWorkerCounterSafety
open ParallelDispatchWrites ParallelWorkerFrozenReads
namespace ParallelWorkerSplitCut

/-- A reducer segment may load immutable inputs and write computed rows. A
duplicate write takes Rust's failure path and cannot reach a normal join. -/
inductive Segment (base : Shared N) (tail : Program (Shared N) A) :
    Program (Shared N) A → List (Publication N) → Prop where
  | stop : Segment base tail tail []
  | load (k : Shared N → Program (Shared N) A) (ws : List (Publication N))
      (next : ∀ h, Extends base h → Segment base tail (k h) ws) :
      Segment base tail (.vis (.atomic id) k) ws
  | put (w : Publication N) (p : Program (Shared N) A) {ws} (next : Segment base tail p ws) :
      Segment base tail (.vis (.atomic (ParallelWorkerCounterSafety.put w.key w.value))
        (fun h => match h.cells w.key with | none => p | some _ => liftResult (fail .panic))) (w::ws)
  | failed (ws : List (Publication N)) : Segment base tail (liftResult (fail .panic)) ws

theorem Segment.read {p : Program (Shared N) A} {v : A} (read : Reads base p v)
    (k : A → Program (Shared N) B) {ws} (next : Segment base tail (k v) ws) :
    Segment base tail (p >>= k) ws := by
  induction read with
  | done x => rwa [show (ITree.ret x >>= k) = k x from itree_ret_bind _ _]
  | load cont x rest ih =>
    rw [vis_bind]
    exact .load _ _ (fun h ext => ih h ext next)

/-- The source OnceLock.set followed by Result.expect is the checked
publication primitive; the occupied-target branch cannot return. -/
theorem Segment.store {N T B} {base : Shared N} (ref : Physical N T) (v : T) (d : core.fmt.Debug T)
    (msg : Str) (p tail : Program (Shared N) B) {ws} (rest : Segment base tail p ws) :
    Segment base tail (do
      let answer ← (ParallelWorkerCounterSafety.set ref v).raw
      let _ ← liftM (core.result.Result.expect d answer msg)
      p) (⟨ref.key,ref.payloadType.symm ▸ v⟩::ws) := by
  let w : Publication N := ⟨ref.key, ref.payloadType.symm ▸ v⟩
  have done := (checkedSet ref v d msg).sound 0 [w] () (receipt_checkedSet ref v d msg 0)
  rw [live_checkedSet,raw_bind] at done
  have actual : ((ParallelWorkerCounterSafety.set ref v).raw >>= fun answer =>
      (liftM (core.result.Result.expect d answer msg) : Program (Shared N) Unit)) = action w := by
    exact (show _ = action w >>= fun _ => pure () from done).trans (_root_.bind_pure (action w))
  have combined := congrArg (fun code : Program (Shared N) Unit => code >>= fun _ => p) actual
  simp only [bind_assoc] at combined
  rw [combined]
  unfold action
  rw [vis_bind]
  convert Segment.put w p rest using 1
  congr 1
  funext h
  cases state : h.cells w.key with
  | none => exact itree_ret_bind _ _
  | some v =>
    simp only [liftResult,Result.match.fail,vis_bind]
    congr 1; funext x; cases x

def Cut (h : Shared N) (xs : List (Program (Shared N) A)) (last : Shared N)
    (out : List (Program (Shared N) A)) (tail : Program (Shared N) A) (ws : List (Publication N)) :=
  ∃ mid left right, Steps h xs mid (left++tail::right) ∧
    Steps mid (left++tail::right) last out ∧ ∀ w ∈ ws, mid.cells w.key = some w.value

/-- Locate the boundary on the original finite schedule. Both parts retain the
same peer progress, final heap and threads. -/
theorem Segment.cut {base h last : Shared N} {p tail : Program (Shared N) A} {ws}
    (cert : Segment base tail p ws) (l r : List (Program (Shared N) A))
    (ext : Extends base h) (safe : All (l++p::r)) {out} (run : Steps h (l++p::r) last out)
    (normal : ∀ t∈out, ∃ b, t=pure b) : Cut h (l++p::r) last out tail ws := by
  let start := (h,l++p::r)
  change Relation.ReflTransGen (fun (x y : Shared N × List (Program (Shared N) A)) =>
    Step x.1 x.2 y.1 y.2) start (last,out) at run
  generalize beginEq : start=z at run
  suffices result : ∀ l r p ws, z.2=l++p::r → Segment base tail p ws → Extends base z.1 →
      All z.2 → Cut z.1 z.2 last out tail ws by
    subst z; exact result l r p ws rfl cert ext safe
  clear beginEq
  induction run using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro l r p ws shape job agree safe
    have retired := normal _ (shape ▸ List.mem_append_right l List.mem_cons_self)
    cases job with
    | stop => exact ⟨last,l,r,shape ▸ .refl,shape ▸ .refl,by simp⟩
    | load | put => obtain ⟨v,bad⟩ := retired; exact False.elim (not_vis_ret bad.symm)
    | failed => obtain ⟨v,bad⟩ := retired; simp only [liftResult,Result.match.fail] at bad; exact False.elim (not_vis_ret bad.symm)
  | @head a b event more ih =>
    intro l r p ws shape job agree safe
    have keep := (published_persists safe event.single).2
    have agree' : Extends base b.1 := fun k v full => keep k v (agree k v full)
    obtain ⟨_,_,safe',_⟩ := all_interleavings .phase1Next safe event.single
    have restore {writes} (found : Cut b.1 b.2 last out tail writes) : Cut a.1 a.2 last out tail writes := by
      obtain ⟨mid,l,r,first,rest,cells⟩ := found
      exact ⟨mid,l,r,Relation.ReflTransGen.head event first,rest,cells⟩
    have edge := event
    change Step a.1 a.2 b.1 b.2 at edge
    rw [shape] at edge
    obtain ⟨q,atNext,own⟩|⟨left,right,atNext,_⟩ := focus l p r _ edge
    · cases job with
      | stop => exact ⟨a.1,l,r,shape ▸ .refl,shape ▸ Relation.ReflTransGen.head event more,by simp⟩
      | load k _ next =>
        obtain ⟨_,which⟩ := own.unique_worker (Step.atomic a.1 [] [] id k)
        exact restore (ih l r _ _ (by simpa [which] using atNext) (next _ agree) agree' safe')
      | @put w next ws rest =>
        obtain ⟨heap,which⟩ := own.unique_worker (Step.atomic a.1 [] [] _ _)
        cases target : a.1.cells w.key with
        | none =>
          simp only [target] at which
          obtain ⟨mid,ll,rr,first,after,written⟩ := ih l r _ ws (by simpa [which] using atNext) rest agree' safe'
          have installed : b.1.cells w.key=some w.value := by
            rw [heap]
            simp [ParallelWorkerCounterSafety.put,slot,target,read_after_write]
          exact ⟨mid,ll,rr,Relation.ReflTransGen.head event first,after,by
            intro u member
            rcases List.mem_cons.mp member with rfl|mem
            · exact (published_persists safe' first).2 _ _ installed
            · exact written u mem⟩
        | some old =>
          simp only [target] at which
          exact restore (ih l r _ _ (by simpa [which] using atNext) (.failed _) agree' safe')
      | failed =>
        obtain ⟨_,_,bad,_,_⟩ := own.single_view
        simp only [liftResult,Result.match.fail] at bad
        cases vis_inj_effect bad
    · exact restore (ih left right p ws atNext job agree' safe')

end ParallelWorkerSplitCut
