import Parallel.PhaseTwoWrites
import Parallel.SignJoin

open Aeneas Aeneas.Std Result
namespace slhdsa.WidthEight.Ticket
open ParallelSigning ParallelSignJoin

/-- State entering phase two. The completed ticket list is in the counter model's
reverse order of publication. No WOTS cells have been supplied. -/
structure PublishedInputs (N : Usize) where
  forest : alloc.vec.Vec U8
  auth : alloc.vec.Vec (Array U8 N)
  layers : ParallelXmssTicket.Layers
  roots : alloc.vec.Vec (Array U8 N)
  issued : Nat
  completed : List Nat

def InputsCorrect {N : Usize} (p : params.Params) (md : Slice U8) (sk seed : Array U8 N)
    (a : address.Adrs) (tree : U64) (leaf : U32) (s : PublishedInputs N) : Prop :=
  let P := Shake.params p
  let key := bytes sk.val
  let pk := bytes seed.val
  let first := Spec.forsPkFromSig P (bytes s.forest.val) (bytes md.val) pk (adrsS a)
  bytes s.forest.val=(ParallelCached.forsRows P (bytes md.val) key pk (adrsS a)).flatten ∧
  P.d*P.hp≤s.auth.length ∧
  (∀ j<P.d, ∀ h<P.hp, let pos := loc P.hp tree.val leaf.val j
    bytes (authRows s.auth P.hp j h)=Spec.xmssNode P key ((pos.2/2^h)^^^1) h pk (addr j pos.1)) ∧
  ParallelXmssTicket.LayerTable p.hp.val tree.val leaf.val p.d.val s.layers ∧
  p.d.val≤s.roots.length ∧
  (∀ j<p.d.val, bytes s.roots.val[j]!.val=ParallelFused.message P first key pk tree.val leaf.val j) ∧
  Trace p.d.val s.issued [] s.completed ∧ p.d.val<s.issued

abbrev PhaseOne := {N : Usize} → params.Params → Slice U8 → Array U8 N → Array U8 N →
  address.Adrs → Array U8 N → U64 → U32 → Usize → Result (PublishedInputs N)

noncomputable def completedJoin (host : Platform) (prepare : PhaseOne) : Join :=
  fun p md sk seed a r tree leaf threads => do
    let inputs ← prepare p md sk seed a r tree leaf threads
    let wots ← phaseTwo host p sk seed inputs.layers inputs.roots inputs.completed
    ok (some inputs.forest,some inputs.auth,wots)

theorem joined_from_tickets (host : Platform) (prepare : PhaseOne) {N : Usize}
    (p : params.Params) (hp : PN p N)
    (inputs : ∀ (md : Slice U8) (sk seed : Array U8 N) (a : address.Adrs) (r : Array U8 N)
      (tree : U64) (leaf : U32) (threads : Usize), 2≤threads.val → md.length=(Shake.params p).mdBytes →
      tree.val<2^(p.h.val-p.hp.val) → leaf.val<2^p.hp.val → adrsS a={{Spec.Adrs.zero with tree:=tree.val}.setTypeAndClear
        Spec.FORS_TREE with keypair:=leaf.val} →
      prepare p md sk seed a r tree leaf threads ⦃ s => InputsCorrect p md sk seed a tree leaf s ⦄) :
    JoinLawAt (completedJoin host prepare) N p := by
  intro md sk seed a r tree leaf threads enabled mdLen treeBound leafBound address
  unfold completedJoin
  step with inputs md sk seed a r tree leaf threads enabled mdLen treeBound leafBound address as ⟨s,good⟩
  obtain ⟨forest,authSize,auth,table,rootCount,messages,trace,drained⟩ := good
  step with phase_two host p hp sk seed tree.val leaf.val _ s.layers s.roots table rootCount messages trace drained as ⟨wots,count,rows⟩
  exact ⟨s.forest,s.auth,rfl,rfl,forest,authSize,count.ge,auth,rows⟩

end slhdsa.WidthEight.Ticket
