import PQ.Interactive.QromBridgeReq
import PQ.QROM.ExactPrfTight

/-!
# One exact game end to end: the PRF game for oracle-port programs

`F : K × Dm → Y` a uniformly random function, `k : K` a uniform key.  A Part-1 program
`P : QProgC (K × Dm) Y E Dm Y α` has quantum access to `F` through its oracle port and sends
classical requests `d : Dm`, answered by `F (k, d)` (real) or by an independent uniform
`R : Dm → Y` (ideal).

* `prfRealW n P ρ Ev`, `prfIdealW n P ρ Ev`: the two game probabilities in the Part-1 model — the
  average over `(k, F)` resp. `(F, R)` of the Born weight (`qWeight`) of the compiled machine
  `compile F (fuelRun (answers) n () P)` (`U_F` an instrument on the workspace).
* `prfExactReal_toIAdv`, `prfExactIdeal_toIAdv`: these are EQUAL to the Part-2 exact experiments
  `PQ.QROM.prfExactReal/Ideal` of the interactive adversary `toIAdv n P`.
* `prf_port_real_le_ideal_add`: hence, for every program with at most `q` port calls on every
  path (`PortBound P q`), `prfRealW ≤ prfIdealW + 8 q² / |K|` — the tight Part-2 bound
  (`prfExact_tight_real_le_ideal_add`), stated purely in the Part-1 model.

Restrictions: those of `QromBridge.lean`/`QromBridgeReq.lean` (fixed register `((K × Dm) × Y) × E`,
all port calls on the same factor, no uniform-sampling nodes, request budget `n` with output
`none` beyond it).  This is the PRF game of Part 2 (`ExactPrf.lean`) for a program in Part-1
syntax; it is NOT yet the game `qPrfRealPr (skPrfC …) (qbPrfC Q)` of the SLH-DSA reduction at
`randPrims ω` (that needs the open form of `bPrfC`, request R1, and the reduction of the hash
tuple to the single function `F`).
-/

open OracleComp OracleSpec ENNReal Quantum Matrix PQ.QROM
open scoped Kronecker ComplexOrder

set_option linter.unusedSectionVars false

namespace PQ.Interactive

variable {K Dm Y E : Type} [Fintype K] [DecidableEq K] [Fintype Dm] [DecidableEq Dm] [Fintype Y]
  [DecidableEq Y] [AddCommGroup Y] [Fintype E] [DecidableEq E] {α : Type}

/-- Real PRF game of a port program, Part-1 model. -/
noncomputable def prfRealW (n : ℕ) (P : QProgC (K × Dm) Y E Dm Y α)
    (ρ : SubState (((K × Dm) × Y) × E)) (Ev : Option α × Unit → Prop) [DecidablePred Ev] : ℝ≥0∞ :=
  ∑ k : K, ∑ F : K × Dm → Y,
    ((Fintype.card K : ℝ≥0∞)⁻¹ * (Fintype.card (K × Dm → Y) : ℝ≥0∞)⁻¹) *
      qWeight Ev (compile F (fuelRun (prfExactCh fun d ↦ F (k, d)) n () P))
        (ρ.matrix ⊗ₖ (SubState.basis ()).matrix)

/-- Ideal PRF game of a port program, Part-1 model. -/
noncomputable def prfIdealW (n : ℕ) (P : QProgC (K × Dm) Y E Dm Y α)
    (ρ : SubState (((K × Dm) × Y) × E)) (Ev : Option α × Unit → Prop) [DecidablePred Ev] : ℝ≥0∞ :=
  ∑ F : K × Dm → Y, ∑ R : Dm → Y,
    ((Fintype.card (K × Dm → Y) : ℝ≥0∞)⁻¹ * (Fintype.card (Dm → Y) : ℝ≥0∞)⁻¹) *
      qWeight Ev (compile F (fuelRun (prfExactCh R) n () P))
        (ρ.matrix ⊗ₖ (SubState.basis ()).matrix)

/-- The Part-1 real game is the Part-2 exact real experiment of `toIAdv n P`. -/
theorem prfExactReal_toIAdv (n : ℕ) (P : QProgC (K × Dm) Y E Dm Y α)
    (ρ : SubState (((K × Dm) × Y) × E)) (Ev : Option α × Unit → Prop) [DecidablePred Ev] :
    prfExactReal LocalSig.Interp.instruments ρ n (toIAdv n P) (fun p ↦ Ev p.2) =
      prfRealW n P ρ Ev := by
  unfold prfExactReal prfRealW prfExactProg
  refine Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun F _ ↦ ?_
  rw [qprob_flat_toIAdv]

/-- The Part-1 ideal game is the Part-2 exact ideal experiment of `toIAdv n P`. -/
theorem prfExactIdeal_toIAdv (n : ℕ) (P : QProgC (K × Dm) Y E Dm Y α)
    (ρ : SubState (((K × Dm) × Y) × E)) (Ev : Option α × Unit → Prop) [DecidablePred Ev] :
    prfExactIdeal LocalSig.Interp.instruments ρ n (toIAdv n P) (fun p ↦ Ev p.2) =
      prfIdealW n P ρ Ev := by
  unfold prfExactIdeal prfIdealW prfExactProg
  refine Finset.sum_congr rfl fun F _ ↦ Finset.sum_congr rfl fun R _ ↦ ?_
  rw [qprob_flat_toIAdv]

/-- **PRF in the QROM for Part-1 port programs, tight.**  Every program with at most `q` oracle
port calls on every path (any number of classical requests) has
`Pr[real] ≤ Pr[ideal] + 8 q² / |K|`. -/
theorem prf_port_real_le_ideal_add [Nonempty K] [Nonempty Dm] (n q : ℕ)
    (P : QProgC (K × Dm) Y E Dm Y α) (hP : PortBound P q)
    (ρ : SubState (((K × Dm) × Y) × E)) (Ev : Option α × Unit → Prop) [DecidablePred Ev] :
    prfRealW n P ρ Ev ≤ prfIdealW n P ρ Ev + ENNReal.ofReal (8 * (q : ℝ) ^ 2 / Fintype.card K) := by
  have hx : IAdv.IsQueryBound (L := LocalSig.instruments.{0}) (spec := qromSpec (K × Dm) Y)
      (Out := fun _ ↦ Option α) n (toIAdv n P) fun _ ↦ q := isQueryBound_toIAdv n P q hP
  have h := prfExact_tight_real_le_ideal_add (K := K) (Dm := Dm) (Y := Y)
    (L := LocalSig.instruments.{0}) (Out := fun _ ↦ Option α) (A := progReg (K × Dm) Y E)
    LocalSig.Interp.instruments ρ (n := n) (q := q) (toIAdv n P) hx (fun p ↦ Ev p.2)
  rw [prfExactReal_toIAdv, prfExactIdeal_toIAdv] at h
  exact h

/-- The other direction. -/
theorem prf_port_ideal_le_real_add [Nonempty K] [Nonempty Dm] (n q : ℕ)
    (P : QProgC (K × Dm) Y E Dm Y α) (hP : PortBound P q)
    (ρ : SubState (((K × Dm) × Y) × E)) (Ev : Option α × Unit → Prop) [DecidablePred Ev] :
    prfIdealW n P ρ Ev ≤ prfRealW n P ρ Ev + ENNReal.ofReal (8 * (q : ℝ) ^ 2 / Fintype.card K) := by
  have hx : IAdv.IsQueryBound (L := LocalSig.instruments.{0}) (spec := qromSpec (K × Dm) Y)
      (Out := fun _ ↦ Option α) n (toIAdv n P) fun _ ↦ q := isQueryBound_toIAdv n P q hP
  have h := prfExact_tight_ideal_le_real_add (K := K) (Dm := Dm) (Y := Y)
    (L := LocalSig.instruments.{0}) (Out := fun _ ↦ Option α) (A := progReg (K × Dm) Y E)
    LocalSig.Interp.instruments ρ (n := n) (q := q) (toIAdv n P) hx (fun p ↦ Ev p.2)
  rw [prfExactReal_toIAdv, prfExactIdeal_toIAdv] at h
  exact h

end PQ.Interactive

open PQ.Interactive in
#print axioms prfExactReal_toIAdv
open PQ.Interactive in
#print axioms prfExactIdeal_toIAdv
open PQ.Interactive in
#print axioms prf_port_real_le_ideal_add
open PQ.Interactive in
#print axioms prf_port_ideal_le_real_add
