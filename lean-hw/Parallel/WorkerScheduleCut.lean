import Parallel.WorkerFrozenReads
open Aeneas Aeneas.Std Aeneas.Data.Coinductive
open ParallelWorkerInterleave ParallelWorkerCounterSafety ParallelWorkerRuntime
namespace ParallelWorkerFrozenReads

/-- Invert a scheduling action at an arbitrary worker position. If another
worker ran, its exact action also runs with any replacement in this position. -/
theorem focus {H A : Type} {h t : H} (l : List (Program H A)) (p : Program H A) (r out)
    (edge : Step h (l++p::r) t out) :
    (∃ q, out=l++q::r ∧ Step h [p] t [q]) ∨
    (∃ l' r', out=l'++p::r' ∧ ∀ other, Step h (l++other::r) t (l'++other::r')) := by
  induction l generalizing out with
  | nil =>
    generalize start : []++p::r = inputs at edge
    cases edge with
    | atomic left right f k =>
      cases left with
      | nil => cases start; exact Or.inl ⟨_,rfl,Step.atomic h [] [] f k⟩
      | cons x xs => cases start; exact Or.inr ⟨[],_,rfl,fun other => Step.atomic h (other::xs) right f k⟩
  | cons w ws ih =>
    generalize start : (w::ws)++p::r = inputs at edge
    cases edge with
    | atomic left right f k =>
      cases left with
      | nil =>
        cases start
        exact Or.inr ⟨k h::ws,r,rfl,fun other => Step.atomic h [] (ws++other::r) f k⟩
      | cons x xs =>
        injection start with same tail
        subst x
        have reduced : Step h (ws++p::r) (f h) (xs++k h::right) := by
          change ws ++ p::r = xs ++ _::right at tail
          rw [tail]; exact Step.atomic h xs right f k
        obtain ⟨q,shape,step⟩|⟨u,v,shape,peer⟩ := ih _ reduced
        · exact Or.inl ⟨q,congrArg (w::·) shape,step⟩
        · refine Or.inr ⟨w::u,v,congrArg (w::·) shape,?_⟩
          intro other
          have consStep {old new : List (Program H A)} (e : Step h old (f h) new) :
              Step h (w::old) (f h) (w::new) := by
            generalize nh : f h = ns at e ⊢
            cases e with | atomic l r f k => exact Step.atomic h (w::l) r f k
          exact consStep (peer other)

/-- Eliminate all of a reducer's read-only steps from an arbitrary normally
returning interleaving. The replacement is at the same worker position and
the resulting trace has exactly the original final heap and worker list. -/
theorem Reads.erase {N : Usize} {A B : Type} {base h last : Shared N}
    {p : Program (Shared N) A} {val : A} (reads : Reads base p val)
    (k : A → Program (Shared N) B) (l r : List (Program (Shared N) B))
    (agreement : Extends base h) (safe : All (l++(p >>= k)::r))
    {out} (run : Steps h (l++(p >>= k)::r) last out)
    (normal : ∀ t∈out, ∃ b, t=pure b) : Steps h (l++k val::r) last out := by
  let start := (h,l++(p >>= k)::r)
  change Relation.ReflTransGen (fun (x y : Shared N × List (Program (Shared N) B)) =>
    Step x.1 x.2 y.1 y.2) start (last,out) at run
  generalize startEq : start=z at run
  suffices result : ∀ l r p, z.2=l++(p >>= k)::r → Reads base p val → Extends base z.1 →
      All z.2 → Steps z.1 (l++k val::r) last out by
    subst z; exact result l r p rfl reads agreement safe
  clear startEq
  induction run using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro l r p shape pending agree certified
    cases pending with
    | done v =>
      rw [show (ITree.ret val >>= k) = k val from itree_ret_bind _ _] at shape
      exact shape ▸ .refl
    | load next value rest =>
      obtain ⟨v,bad⟩ := normal _ (shape ▸ List.mem_append_right l List.mem_cons_self)
      rw [vis_bind] at bad; exact False.elim (not_vis_ret bad.symm)
  | @head a b event more ih =>
    intro l r p shape pending agree cert
    have keep := published_persists cert event.single
    have agree' : Extends base b.1 := fun key value full => keep.2 key value (agree key value full)
    obtain ⟨_,_,cert',_⟩ := all_interleavings .phase1Next cert event.single
    have edge := event
    change Step a.1 a.2 b.1 b.2 at edge
    rw [shape] at edge
    cases pending with
    | done v =>
      rw [show (ITree.ret val >>= k) = k val from itree_ret_bind _ _] at edge
      exact Relation.ReflTransGen.head edge more
    | load next value rest =>
      obtain ⟨q,nextShape,own⟩|⟨left,right,nextShape,replay⟩ := focus l _ r _ edge
      · rw [vis_bind] at own
        obtain ⟨same,cont⟩ := own.unique_worker (Step.atomic a.1 [] [] id _)
        have followed := ih l r (next a.1) (by simpa [cont] using nextShape) (rest _ agree) agree' cert'
        simpa [same] using followed
      · exact Relation.ReflTransGen.head (replay (k val))
          (ih left right _ nextShape (.load next val rest) agree' cert')

end ParallelWorkerFrozenReads
