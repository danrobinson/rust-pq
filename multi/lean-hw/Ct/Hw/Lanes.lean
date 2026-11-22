import Ct.Hash

/-!
# Constant time: the four-lane kernel of `sha256::hw::chain_all`, the round part (generic in `N`)

Adapted from the main tree's `../../lean-hw/Ct/Hw/Lanes.lean` (copied and edited, not linked:
this tree's kernel takes the hash length `N` and the second half `efgh0` of the seed state, and
carries the value's words 4.. in `xb`).

`lane_step`, `lane_tick`, `tick`, `period` and `run` work on the vector registers of up to four
lanes. Their branches, divisions, remainders and indices are on the const-generic parameters
(the hash length `N`, `L` lanes, the `PHASE`, the tick `J`, the `LANE`) and on the period `p`
and the step count `steps`: all public. The new branches of this tree (`N = 16`, `N = 24`,
`N > 16`, `N > 24`) are on `N`, which both runs share. The slots' secret parts (the message words and first-round state) and the
lanes' registers (`x`, `xb`, `abcd`, `efgh`, the schedule) only pass through the register-only wrappers. So two runs with the same public
parameters have the same trace, whatever the slots and lanes.

`run` also advances the slots' step counters by `steps`; its postcondition says that the public
parts of the slots (`t`, `end`, `lane`) are again equal.
-/

open Aeneas Aeneas.Std Ct

namespace Ct.Hw

open slhdsa_leak

abbrev Vec := core.core_arch.arm_shared.neon.uint32x4_t
abbrev Slot := slhdsa.sha256.hw.Slot

/-- The public part of a slot: its next step, its end and the lane (block index) it holds. -/
def pub (s : Slot) : U32 × U32 × Usize := (s.t, s.«end», s.lane)

/-- The slots of the two runs agree on their public parts. -/
def SlotsRel (a a' : Array Slot 4#usize) : Prop := a.val.map pub = a'.val.map pub

theorem SlotsRel.refl (a : Array Slot 4#usize) : SlotsRel a a := rfl

theorem pub_eq {s s' : Slot} (h : pub s = pub s') :
    s.t = s'.t ∧ s.«end» = s'.«end» ∧ s.lane = s'.lane := by
  simpa [pub] using h

/-- Reading a slot. -/
theorem slots_index {a a' : Array Slot 4#usize} (h : SlotsRel a a') (j : Usize) :
    Rel (slhdsa_leak.Array.index_usize a j) (slhdsa_leak.Array.index_usize a' j) (fun s s' => pub s = pub s') := by
  intro s t s' t' h1 h2
  obtain ⟨e1, rfl⟩ := Leak.prim_eq_ok.mp h1
  obtain ⟨e2, rfl⟩ := Leak.prim_eq_ok.mp h2
  refine ⟨rfl, ?_⟩
  simp only [Aeneas.Std.Array.index_usize] at e1 e2
  split at e1 <;> split at e2 <;> simp at e1 e2
  subst e1 e2
  rename_i _ _ hy _ _ hy'
  have := congrArg (fun l => l[j.val]?) h
  simp only [List.getElem?_map, Array.getElem?_Usize_eq] at this hy hy'
  rw [hy, hy'] at this
  simpa using this

theorem SlotsRel.set {a a' : List Slot} (h : a.map pub = a'.map pub) (i : Nat) {s s' : Slot}
    (hs : pub s = pub s') : (a.set i s).map pub = (a'.set i s').map pub := by
  rw [List.map_set, List.map_set, h, hs]

@[ct_rel] theorem advanced (slot slot' : Slot) (x x' xb xb' : Vec) (steps : U32)
    (h : pub slot = pub slot') :
    Rel (sha256.hw.advanced slot x xb steps) (sha256.hw.advanced slot' x' xb' steps)
      (fun r r' => pub r = pub r') := by
  obtain ⟨ht, he, hl⟩ := pub_eq h
  unfold sha256.hw.advanced
  rw [ht]
  ct_steps
  simp_all [pub]

@[ct_rel] theorem lane_step (N L J LANE : Usize) (abcd0 abcd0' efgh0 efgh0' : Vec)
    (slots slots' : Array Slot 4#usize) (p : U32) (s s' : slhdsa.sha256.hw.Lanes) :
    Rel (sha256.hw.lane_step N L J LANE abcd0 efgh0 slots p s)
      (sha256.hw.lane_step N L J LANE abcd0' efgh0' slots' p s') (fun _ _ => True) := by
  unfold sha256.hw.lane_step
  ct_steps

@[ct_rel] theorem lane_tick (N L PHASE J LANE : Usize) (abcd0 abcd0' efgh0 efgh0' : Vec)
    (slots slots' : Array Slot 4#usize) (p : U32) (s s' : slhdsa.sha256.hw.Lanes) :
    Rel (sha256.hw.lane_tick N L PHASE J LANE abcd0 efgh0 slots p s)
      (sha256.hw.lane_tick N L PHASE J LANE abcd0' efgh0' slots' p s') (fun _ _ => True) := by
  unfold sha256.hw.lane_tick
  ct_steps

@[ct_rel] theorem tick (N L PHASE J : Usize) (abcd0 abcd0' efgh0 efgh0' : Vec)
    (slots slots' : Array Slot 4#usize) (p : U32) (s s' : slhdsa.sha256.hw.Lanes) :
    Rel (sha256.hw.tick N L PHASE J abcd0 efgh0 slots p s)
      (sha256.hw.tick N L PHASE J abcd0' efgh0' slots' p s') (fun _ _ => True) := by
  unfold sha256.hw.tick
  ct_steps

@[ct_rel] theorem period (N L PHASE : Usize) (abcd0 abcd0' efgh0 efgh0' : Vec)
    (slots slots' : Array Slot 4#usize) (p : U32) (s s' : slhdsa.sha256.hw.Lanes) :
    Rel (sha256.hw.period N L PHASE abcd0 efgh0 slots p s)
      (sha256.hw.period N L PHASE abcd0' efgh0' slots' p s') (fun _ _ => True) := by
  unfold sha256.hw.period
  ct_steps

theorem run_loop_body (N L : Usize) (slots slots' : Array Slot 4#usize) (steps : U32)
    (abcd0 abcd0' efgh0 efgh0' : Vec) (s s' : slhdsa.sha256.hw.Lanes) (p : U32) :
    Rel (sha256.hw.run_loop.body N L slots steps abcd0 efgh0 s p)
      (sha256.hw.run_loop.body N L slots' steps abcd0' efgh0' s' p)
      (CFRel (fun a b => a.2 = b.2) (fun a b => a.2 = b.2)) := by
  unfold sha256.hw.run_loop.body
  ct_steps
  all_goals simp_all

@[ct_rel] theorem run_loop (N L : Usize) (slots slots' : Array Slot 4#usize) (steps : U32)
    (abcd0 abcd0' efgh0 efgh0' : Vec) (s s' : slhdsa.sha256.hw.Lanes) (p : U32) :
    Rel (sha256.hw.run_loop N L slots steps abcd0 efgh0 s p)
      (sha256.hw.run_loop N L slots' steps abcd0' efgh0' s' p) (fun a b => a.2 = b.2) := by
  unfold sha256.hw.run_loop
  refine Rel.loop (fun a b => a.2 = b.2) ?_ rfl
  rintro ⟨x, j⟩ ⟨x', j'⟩ (rfl : j = j')
  exact run_loop_body N L slots slots' steps abcd0 abcd0' efgh0 efgh0' x x' j

instance : Inhabited Slot := ⟨⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩,
  ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, 0#u32, 0#u32, 0#usize⟩⟩

/-- `ct_step`, but a nested conditional whose result is an array of slots is stepped with the
intermediate relation `SlotsRel` (instead of the trivial one). -/
macro "ct_step_s" : tactic => `(tactic| first
  | (with_reducible refine Rel.bind_refl (fun _ _ => ?_))
  | (with_reducible refine Rel.bind (m := Ct.Leak.cond _ _ _) (R := fun (x y : Aeneas.Std.Array Ct.Hw.Slot 4#usize) => Ct.Hw.SlotsRel x y) ?_ (fun _ _ _ => ?_))
  | ct_step)

macro "ct_steps_s" : tactic => `(tactic| repeat' ct_step_s)

/-- Close a `SlotsRel` goal from the hypotheses on the updates. -/
macro "slots_tac" : tactic => `(tactic| (
  try simp only [Ct.Hw.SlotsRel] at *
  try simp only [Ct.Leak.erase_prim, Ct.Facts.erase_liftM] at *
  heads_facts
  try simp only [Aeneas.Std.Array.set_val_eq, List.map_set, *]
  all_goals first | (simp_all; done) | (simp_all [Ct.Hw.pub]; done)))

section
attribute [local ct_rel] slots_index

/-- `run`: the trace depends on `N`, `L` and `steps` only; the slots' public parts stay equal. -/
@[ct_rel] theorem run (N L : Usize) (state state' : Array U32 8#usize)
    (slots slots' : Array Slot 4#usize) (steps : U32) (h : SlotsRel slots slots') :
    Rel (sha256.hw.run N L state slots steps) (sha256.hw.run N L state' slots' steps)
      (fun r r' => SlotsRel r r') := by
  unfold sha256.hw.run
  ct_steps_s
  all_goals slots_tac

end

end Ct.Hw
