import Parallel.WorkerCounterSafety

namespace ParallelWorkerFrozenReads
open Aeneas Aeneas.Std Result Aeneas.Data.Coinductive
open ParallelWorkerHeap ParallelWorkerRuntime ParallelWorkerInterleave ParallelWorkerCounterSafety

def Extends (base later : Shared N) := ∀ k v, base.cells k = some v → later.cells k = some v

/-- Finite computation that only reads cells already initialized in the snapshot.
Each successive read may see a different extension of that snapshot. -/
inductive Reads (base : Shared N) : Program (Shared N) A → A → Prop where
  | done (value : A) : Reads base (.ret value) value
  | load (next : Shared N → Program (Shared N) A) (value : A)
      (rest : ∀ h, Extends base h → Reads base (next h) value) :
      Reads base (.vis (.atomic id) next) value

theorem Reads.bind {base : Shared N} {p : Program (Shared N) A} {v : A}
    (run : Reads base p v) (k : A → Program (Shared N) B) {w : B} (after : Reads base (k v) w) :
    Reads base (p >>= k) w := by
  induction run with
  | done x => rw [show (ITree.ret x >>= k) = k x from itree_ret_bind x k]; exact after
  | load next value rest ih =>
    rw [vis_bind]
    exact .load _ _ (fun h ext => ih h ext after)

private theorem advance {p : Program (Shared N) A} {base : Shared N} {v : A}
    (reads : Reads base p v) {f : Shared N → Shared N} {k : Shared N → Program (Shared N) A}
    (src : p = .vis (.atomic f) k) (h : Shared N) (ext : Extends base h) : Reads base (k h) v := by
  cases reads with
  | done => grind
  | load next value rest =>
    obtain ⟨same,cont⟩ := vis_inj src
    have changeEq := Operation.atomic.inj same
    subst f
    have eq : next=k := eq_of_heq cont
    subst k
    exact rest h ext

private theorem finished {p : Program (Shared N) A} {base : Shared N} {v out : A}
    (reads : Reads base p v) (src : p = .ret out) : out=v := by
  cases reads with
  | done => exact (ret_inj.mp src).symm
  | load => grind

theorem typed_load {N T} (base : Shared N) (p : Physical N T) (v : T)
    (full : p.ref.read base = some v) : Reads base (get p).raw (some v) := by
  obtain ⟨k,ty⟩ := p
  subst T
  apply Reads.load
  intro h ext
  change Reads base (.ret (h.cells k)) (some v)
  rw [ext k v full]
  exact .done _

private theorem raw_ext {x y : Certified N A} (eq : x.raw = y.raw) : x=y := by
  cases x; cases y; cases eq; rfl

local instance : LawfulMonad (Certified N) := LawfulMonad.mk' _
  (fun x => raw_ext (by change (x.raw >>= fun a => pure a) = x.raw; exact bind_pure x.raw))
  (fun x f => raw_ext (itree_ret_bind _ _))
  (fun x f g => raw_ext (by change (x.raw >>= _ >>= _) = (x.raw >>= _); rw [bind_assoc]; rfl))

theorem collect {N T} (base : Shared N) (refs : List (Physical N T))
    (full : ∀ ref ∈ refs, ∃ value, ref.ref.read base = some value) :
    Reads base (refs.mapM ParallelWorkerCounterSafety.get).raw (refs.map fun ref => ref.ref.read base) := by
  induction refs with
  | nil => simp only [List.mapM_nil,List.map_nil]; exact .done _
  | cons p ps ih =>
    obtain ⟨v,hv⟩ := full p (by simp)
    rw [List.mapM_cons,List.map_cons,hv,raw_bind]
    apply (typed_load base p v hv).bind
    rw [raw_bind]
    apply (ih (fun q hq => full q (by simp [hq]))).bind
    exact .done _

/-- The scheduler can run this complete read phase from any extension and
then run the original caller continuation with the resulting bytes. -/
theorem Reads.resume {base h : Shared N} (ext : Extends base h)
    {p : Program (Shared N) A} {v : A} (reads : Reads base p v)
    (k : A → Program (Shared N) B) (l r : List (Program (Shared N) B)) :
    Steps h (l ++ (p >>= k) :: r) h (l ++ k v :: r) := by
  induction reads with
  | done x => rw [show (ITree.ret x >>= k) = k x from itree_ret_bind x k]; exact .refl
  | load next value rest ih =>
    rw [vis_bind]
    exact (Step.atomic h l r id (fun h => next h >>= k)).single.trans (ih h ext)

/-- Track one physical worker by its stable position in an arbitrary schedule.
Other certified callbacks may run between any two loads. -/
theorem scheduled {base last : Shared N} {xs ys : List (Program (Shared N) A)}
    (safe : All xs) (history : Steps base xs last ys) (i : Nat) {p : Program (Shared N) A}
    (position : xs[i]? = some p) {v : A} (reads : Reads base p v) :
    ∃ out, ys[i]? = some out ∧ Reads base out v := by
  let inv := fun s : Shared N × List (Program (Shared N) A) =>
    Steps base xs s.1 s.2 ∧ ∃ w, s.2[i]? = some w ∧ Reads base w v
  have initial : inv (base,xs) := ⟨.refl,_,position,reads⟩
  have preserve {x y : Shared N × List (Program (Shared N) A)} (prev : inv x)
      (event : Step x.1 x.2 y.1 y.2) : inv y := by
    rcases x with ⟨h,ws⟩; rcases y with ⟨new,us⟩
    dsimp only at event
    cases event with
    | atomic left right f k =>
      obtain ⟨path,w,pos,pending⟩ := prev
      have ext := (published_persists safe path).2
      refine ⟨path.follow (.atomic h left right f k),?_⟩
      by_cases before : i < left.length
      · rw [List.getElem?_append_left before] at pos ⊢
        exact ⟨w,pos,pending⟩
      rw [List.getElem?_append_right (Nat.le_of_not_gt before)] at pos ⊢
      cases ix : i-left.length with
      | succ j =>
        simp only [ix,List.getElem?_cons_succ] at pos ⊢
        exact ⟨w,pos,pending⟩
      | zero =>
        simp only [ix,List.getElem?_cons_zero,Option.some.injEq] at pos
        refine ⟨_,?_,advance pending pos.symm h ext⟩
        rfl
  exact (Relation.ReflTransGen.head_induction_on history
    (motive := fun s _ => inv s → inv (last,ys)) id
    (fun event _ ih prev => ih (preserve prev event)) initial).2

theorem returned {base last : Shared N} {xs ys : List (Program (Shared N) A)}
    (safe : All xs) (history : Steps base xs last ys) (i : Nat) {p : Program (Shared N) A}
    (position : xs[i]? = some p) {v : A} (reads : Reads base p v) (out : A)
    (endAt : ys[i]? = some (.ret out)) : out=v := by
  obtain ⟨_,ep,res⟩ := scheduled safe history i position reads
  rw [endAt] at ep
  exact finished res (Option.some.inj ep).symm

end ParallelWorkerFrozenReads
