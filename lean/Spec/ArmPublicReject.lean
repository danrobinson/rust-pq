import Spec.ArmSignReject

/-! Symbolic execution of the public signing rejection path on the current
Apple arm64 consumer, including its larger stack frames and indexed register pairs. -/
namespace Spec.ArmPublicReject
open ArmSignReject

private def adjustSP (s : State) (offset : Int) : Option State := do
  let sp := s.sp + offset
  guard (sp ≤ 0 && -4096 ≤ sp && sp % 16 == 0)
  return {s with sp}

def step (ls : Bool) (op : Nat × Nat) (state : State) : Option State := do
  let (pc,w) := op
  guard (state.pc == .lit pc && pc % 4 == 0 && w < 2^32)
  let s := {state with pc := .lit (pc+4)}
  let spOp := w &&& 0xffc003ff
  if spOp == 0x910003ff || spOp == 0xd10003ff then
    let imm : Int := (w >>> 10) % 4096
    adjustSP s (if spOp == 0x910003ff then imm else -imm)
  else
    let pair := w &&& 0xffc003e0
    if pair == 0xa98003e0 || pair == 0xa8c003e0 then
      let postLoad := pair == 0xa8c003e0
      let rt := w % 32
      let rt2 := (w >>> 10) % 32
      guard (rt < 31 && rt2 < 31 && rt != rt2)
      let inc := 8 * signed ((w >>> 15) % 128) 7
      let base ← if postLoad then some s else adjustSP s inc
      let first ← transfer base postLoad false rt (.frame base.sp) 0
      let last ← transfer first postLoad false rt2 (.frame base.sp) 8
      if postLoad then adjustSP last inc else some last
    else
      ArmSignReject.step ls op state

def run (ls : Bool) (entry : Nat) (path : List (Nat × Nat)) :=
  path.foldlM (fun s op => step ls op s) (initial entry)

def checks (entry n : Nat) (det : Bool) (path : List (Nat × Nat)) : Bool :=
  match run false entry path with
  | some s => post n det s
  | none => false

def ReturnsNone (entry n : Nat) (det : Bool) (path : List (Nat × Nat)) :=
  ∀ len : BitVec 64, 255 < len.toNat →
    ∃ s, run (decide (len.toNat ≤ 255)) entry path = some s ∧ post n det s = true

theorem returnsNone_of_checks {entry n det path} (ok : checks entry n det path = true) :
    ReturnsNone entry n det path := by
  intro len large
  rw [unsigned_long len large]
  unfold checks at ok
  cases h : run false entry path with
  | none => simp [h] at ok
  | some s => exact ⟨s,rfl,by simpa [h] using ok⟩

end Spec.ArmPublicReject
