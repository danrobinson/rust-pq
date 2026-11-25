import Parallel.SignJoinRoundTrip
open Aeneas Aeneas.Std Result
namespace slhdsa.ParallelSignJoin

@[instance_reducible] noncomputable def replayWith (plan : PhysicalRows → Join) (threads : Usize) :
    ParallelCaller.Worker ParallelCaller.ShakeSeed where
  run p md sk seed a r tree leaf := match lookup (Shake.params p) with
    | none => ok none
    | some rows => run (ok threads) (plan rows) p md sk seed a r tree leaf

private theorem same_cont {α β : Type} (m : Result α) (f g : α → Result β)
    (eq : ∀ x, f x=g x) : (m >>= f) = (m >>= g) :=
  congrArg (fun k => m >>= k) (funext eq)

/-- After either the pool join or any Rust effect, every successful return of the
enabled worker takes the Some continuation. -/
theorem uses_some {β : Type} (planFor : PhysicalRows → Join) (threads : Usize) (enabled : 2≤threads.val) {N : Usize}
    (p : params.Params) (hp : PN p N) (member : p ∈ rustSets) (md : Slice U8)
    (sk seed : Array U8 N) (a : address.Adrs) (r : Array U8 N) (tree : U64) (leaf : U32)
    (f g : Option (alloc.vec.Vec U8) → Result β) (agree : ∀ s, f (some s)=g (some s)) :
    ((replayWith planFor threads).run p md sk seed a r tree leaf >>= f) =
      ((replayWith planFor threads).run p md sk seed a r tree leaf >>= g) := by
  obtain ⟨plan,found⟩ := rust_supported p member
  have live : ¬threads<2#usize := by scalar_tac
  have height : p.hp ≠ 0#u32 := by have h := hp.valid.hp_pos;change 0<p.hp.val at h;scalar_tac
  dsimp only [replayWith,ParallelCaller.Worker.run]
  simp only [found,run,bind_ok,ite_eq_right live,ite_eq_right height,lift,bind_tc_eq,Std.bind_assoc]
  apply same_cont
  rintro ⟨forest,auth,wots⟩
  simp only [Std.bind_assoc,bind_ok,uncurry]
  repeat' (apply same_cont;intro)
  apply agree

/-- For a supported enabled geometry, arbitrary replacement of the serial branch
preserves the returned value, panic, or divergence for every input. -/
theorem fallback_irrelevant (planFor : PhysicalRows → Join) (threads : Usize) (enabled : 2≤threads.val) {N : Usize}
    (p : params.Params) (hp : PN p N) (member : p ∈ rustSets)
    (f g : ParallelCaller.Sh.Fallback) (m sk : Slice U8) (rnd : Array U8 N)
    (prf : Array U8 N → Array U8 N → Slice U8 → Result (Array U8 N))
    (hash : params.Params → Array U8 N → Array U8 N → Array U8 N → Slice U8 → Result (alloc.vec.Vec U8)) :
    @ParallelCaller.Sh.signWith f (replayWith planFor threads) N prf hash p m sk rnd =
      @ParallelCaller.Sh.signWith g (replayWith planFor threads) N prf hash p m sk rnd := by
  unfold ParallelCaller.Sh.signWith
  repeat' first
    | apply uses_some planFor threads enabled p hp member;intro;rfl
    | apply same_cont;intro

end slhdsa.ParallelSignJoin
