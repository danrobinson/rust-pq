import PQ.QROM.ExactTcr

/-!
# The exact SM-DT-TCR experiment: a computed value

An adversary that sends no classical request (`n = 0`) records no target, so it never wins:
`tcrExp = 0`, whatever its quantum queries and its output.  (This computes the experiment on a
class of adversaries; it shows that the winning condition is read from the game's record and
not from the adversary's output.)
-/

open MeasureTheory ENNReal Quantum Matrix
open scoped Kronecker ComplexOrder

universe u v w

set_option linter.unusedSectionVars false

namespace PQ.QROM

variable {Sd Tw Msg Y : Type} [Fintype Sd] [DecidableEq Sd] [Fintype Tw] [DecidableEq Tw]
  [Fintype Msg] [DecidableEq Msg] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
  {L : LocalSig.{u, v}} {Out : QReg → Type w} {A : QReg}

/-- Without classical requests no target is recorded and the adversary cannot win. -/
theorem tcrExp_zero_requests (I : L.Interp) (ρ : SubState A) (cap : ℕ)
    (x : IAdv L (qrom2Spec (Dom Sd Tw Msg) Y) ((Tw × Msg) ⊕ (Tw × Msg)) (Option Y) Out 0 A)
    (ph2 : Sd → ∀ u, Out u →
      QuantumComp L (qrom2Spec (Dom Sd Tw Msg) Y) (fun _ ↦ ℕ × Msg) u) :
    tcrExp I ρ cap 0 x ph2 = 0 := by
  refine le_antisymm (avg_le fun P ↦ avg_le fun Th ↦ le_of_eq ?_) zero_le
  have key : ∀ x' : QuantumComp L (qrom2Spec (Dom Sd Tw Msg) Y) Out A,
      leafProb (twoRuntime fun _ ↦ Th) I
        (QuantumComp.bind x' fun u o ↦ phase2K ph2 P u o (tcrInit (Tw := Tw) (Msg := Msg)))
        (joint ρ) (winLeaf (tcrWin (rowOf Th P))) = 0 := fun x' ↦ by
    rw [leafProb_bind _ _ (joint_posSemidef ρ)]
    simp only [tsum_eq_zero_iff]
    intro p
    rw [leafProb_phase2K _ I ph2 P p.1 p.2 tcrInit
      (((twoRuntime fun _ ↦ Th).run I x').posSemidef_branch_apply p (joint_posSemidef ρ))]
    unfold leafProb
    simp only [tsum_eq_zero_iff]
    intro l
    rw [ind_of_false (by rintro ⟨t, mj, h, -⟩; simp [tcrInit] at h), mul_zero]
  exact key x

end PQ.QROM

#print axioms PQ.QROM.tcrExp_zero_requests
