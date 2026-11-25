import Armwide.RefillProgram
import Armwide.WotsRefill
namespace slhdsa.Armwide.Transitions
open WotsRefill
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

def loadPost (shared live phase more : Bool) (i : Fin 4) : Post :=
  updates[32*shared.toNat+16*live.toNat+8*phase.toNat+4*more.toNat+i.val]!

def postSpec (shared live phase more : Bool) (i : Fin 4) : Post :=
  let fresh := !live && more
  let writes := if live then [] else [⟨i,i,i.val+4⟩]
  if fresh then ⟨1,⟨13,14,15,4,4,0,9,1,1⟩,writes⟩
  else ⟨0,⟨i,i.val+4,if !shared && live && phase then 12 else i.val+8,i,i,
        if shared then 1024 else if live && !phase then 1 else 0,i,
        if shared then 1024 else 1,(phase && (shared || !live)).toNat⟩, writes⟩

/-- Complete provenance of the updated row, cursor and retired output; the Rust lift also
checks that processing this lane preserves every register of the other three lanes. -/
theorem post_correct : ∀ shared live phase more i,
    loadPost shared live phase more i = postSpec shared live phase more i := by decide

/-- The saved head and both digest halves must agree with the phase and input
chosen for the next hash. All four input rows have distinct register labels. -/
def headPhase (code : Nat) (previous : Nat → Bool) :=
  if code=15 then true else if code=12 then false else previous (code-8)

theorem post_registers : ∀ shared live phase more i,
    let r := (loadPost shared live phase more i).lane
    headPhase r.head (fun _ => phase) = (r.phase=1) ∧
      ((r.x=13 ∧ r.xb=14) ∨ (r.x=i.val ∧ r.xb=i.val+4)) := by decide

structure Stepping where
  physical : Fin 4
  before : SignLane
  digest : Spec.Bytes

private def delta (code bulk : Nat) := if code=1024 then bulk else code

abbrev Writer (α : Type) := α → Nat → Spec.Bytes → α

def transitionWith {α : Type} (write : Writer α) (sk : Spec.Bytes) (digits : Nat → Nat) (shared : Bool) (bulk : Nat)
    (s : Stepping) (queue : List Nat) (out : α) : SignLane × List Nat × α :=
  let l := s.before
  let live := decide ((if shared then bulk else 1) < l.left)
  let post := loadPost shared live l.isPrf (!queue.isEmpty) s.physical
  let r := post.lane
  let nc := queue.head!
  let row : SignLane :=
    ⟨if r.x=13 then sk else s.digest, if r.chain=4 then nc else l.chain,
     (if r.cur=4 then 0 else l.curT) + delta r.advanced bulk,
     if r.left=9 then digits nc+r.consumed else l.left-delta r.consumed bulk, headPhase r.head (fun _ => l.isPrf)⟩
  (row, queue.drop post.consumed, post.writes.foldl (fun o _ => write o l.chain s.digest) out)

abbrev transition := transitionWith setOut

/-- Run the four-lane loop in increasing register order. The compaction theorem in
Armwide.Transitions justifies retaining exactly the rows whose updated count is positive. -/
def nativeUpdates (sk : Spec.Bytes) (digits : Nat → Nat) (shared : Bool) (bulk : Nat) :
    List Stepping → List Nat → (Nat → Spec.Bytes) → List SignLane × List Nat × (Nat → Spec.Bytes)
  | [], q, o => ([],q,o)
  | l::ls, q, o =>
    let (row,q',o') := transition sk digits shared bulk l q o
    let (rest,q'',o'') := nativeUpdates sk digits shared bulk ls q' o'
    (if row.left=0 then rest else row::rest, q'',o'')

def progressed (shared : Bool) (bulk : Nat) (s : Stepping) : SignLane :=
  let l := s.before
  ⟨s.digest,l.chain,if shared then l.curT+bulk else if l.isPrf then l.curT else l.curT+1,
    l.left-(if shared then bulk else 1), if shared then l.isPrf else false⟩

/-- For arbitrary chain values, digits, and a queue of any length, the production update
loops retire, refill, and compact to the same state as the proved signing scheduler. -/
theorem native_updates_eq (sk : Spec.Bytes) (digits : Nat → Nat) (shared : Bool) (bulk : Nat)
    (lanes : List Stepping) (queue : List Nat) (out : Nat → Spec.Bytes) :
    nativeUpdates sk digits shared bulk lanes queue out =
      signRetireRefill sk digits (lanes.map (progressed shared bulk)) queue out := by
  induction lanes generalizing queue out with
  | nil => rfl
  | cons s ss ih =>
    have idx : s.physical.val ≠ 4 := by have := s.physical.isLt; omega
    have noSecret : s.physical.val ≠ 13 := by have := s.physical.isLt; omega
    have cnt : s.physical.val ≠ 9 := by have := s.physical.isLt; omega
    have tag12 : s.physical.val+8 ≠ 12 := by have := s.physical.isLt; omega
    have tag15 : s.physical.val+8 ≠ 15 := by have := s.physical.isLt; omega
    cases shared <;> cases phase : s.before.isPrf <;> cases queue <;>
      simp only [nativeUpdates,List.map_cons,signRetireRefill,transition,transitionWith,post_correct,postSpec,phase,
        progressed,headPhase,tag12,tag15,Bool.false_eq_true,Bool.true_eq_false,↓reduceIte,Bool.false_and,Bool.true_and,
        Bool.and_false,Bool.and_true,Bool.true_or,Bool.false_or,Bool.or_false,Bool.or_true,
        Bool.not_true,Bool.not_false,List.isEmpty_nil,List.isEmpty_cons,delta] <;>
      split_ifs <;> simp_all [List.head!,List.head?,delta,ih,Nat.add_comm] <;> omega

end slhdsa.Armwide.Transitions
