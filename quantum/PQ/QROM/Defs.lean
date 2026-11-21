import VCVio.Quantum.Oracle.Model
import VCVio.Quantum.Comp.HybridIndex

/-!
# QROM experiments: basic definitions

`PQ.QROM.qprob I H x ρ E` is the probability that the quantum query program `x` (any VCVio
`QuantumComp`: adaptive, with arbitrary local instruments under the interpretation `I`, any
workspace), run from the substate `ρ` against the oracle unitary `U_H |x, y⟩ = |x, y + H x⟩` of the
fixed function `H`, ends in a leaf satisfying `E`.  It is a Born probability: the sum of the traces
of the unnormalised post-states of the leaves in `E`.

All games in `PQ/QROM` are finite weighted averages of `qprob` over the challenger's randomness
(the random function included).
-/

open MeasureTheory ENNReal Quantum

universe u v w

namespace PQ.QROM

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
variable {L : LocalSig.{u, v}} {W : QReg → Type w} {A : QReg}

/-- Probability that `x`, run from `ρ` with quantum access to the fixed function `H`, reaches a
leaf in `E`. -/
noncomputable def qprob (I : L.Interp) (H : X → Y) (x : QuantumComp L (qromSpec X Y) W A)
    (ρ : SubState A) (E : (Σ u, W u) → Prop) : ℝ≥0∞ :=
  (additiveOracleRuntime H).evalDistMap I x ρ E {True}

/-- A program making at most `q` oracle calls on every path. -/
def QueryBounded (x : QuantumComp L (qromSpec X Y) W A) (q : ℕ) : Prop :=
  x.IsQueryBound fun _ ↦ q

end PQ.QROM
