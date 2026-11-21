import PQ.QROM.ExactPrf
import PQ.QROM.PurifyInstances

/-!
# The exact PRF game, tight bound, unconditional

`PQ/QROM/ExactPrf.lean` proves the tight bound `c q² / |K|` for the exact PRF game conditional on
the hypothesis `PrfExactTightProgramReal … c`.  That hypothesis is `tight_view` for arbitrary
quantum query programs, which follows from `qprob_tight_avg` (`PQ/QROM/PurifyTight.lean`) with
`c = 8` (`prfExactTightProgramReal`).  Hence, unconditionally:

* `prfExact_tight_abs_le`: `|Pr_real[E] − Pr_ideal[E]| ≤ 8 q² / |K|`;
* `prfExact_tight_real_le_ideal_add`, `prfExact_tight_ideal_le_real_add`: the one-sided forms
  in `ℝ≥0∞`.

`q` is the number of quantum queries to `F`; the number `n` of classical PRF-oracle requests is
unrestricted.
-/

open ENNReal Finset Quantum

universe u v w

namespace PQ.QROM

open PQ.QROM.Tight

/-- **`tight_view` for all quantum query programs**: the hypothesis of
`prfExact_tight_abs_of_programReal` holds with `c = 8`, for every interpretation, leaf family,
initial substate and query budget. -/
theorem prfExactTightProgramReal (X Y : Type) [Fintype X] [DecidableEq X] [Fintype Y]
    [DecidableEq Y] [AddCommGroup Y] {L : LocalSig.{u, v}} (I : L.Interp) (W : QReg → Type w)
    {A : QReg} (ρ : SubState A) (q : ℕ) : PrfExactTightProgramReal X Y I W ρ q 8 := by
  intro Ω V _ _ _ wt hwt view S ε hε hH x hx Hreal Ghyb hS E
  have h := tight_view_of wt hwt (fun _ ↦ 1) (fun _ ↦ zero_le_one) (fun _ ↦ le_rfl) view S ε hε
    hH q (fun v H ↦ (qprob I H (x v) ρ (E v)).toReal)
    (fun v ↦ qprob_tightAvgBound I (x v) ρ q (hx v) (E v)) Hreal Ghyb hS
  simpa only [mul_one] using h

section ExactPrf

variable {K Dm Y : Type} [Fintype K] [DecidableEq K] [Fintype Dm] [DecidableEq Dm] [Fintype Y]
  [DecidableEq Y] [AddCommGroup Y]
  {L : LocalSig.{u, v}} {Out : QReg → Type w} {A : QReg}

/-- **Exact PRF game, tight bound.**  `F : K × Dm → Y` and the key uniform; the adversary (any
`IAdv`: quantum access to `F`, at most `q` quantum queries on every path, any number `n` of
classical PRF-oracle requests answered by `F (k, ·)` resp. an independent uniform `R`) reaches
any leaf event `E` with probabilities differing by at most `8 q² / |K|`. -/
theorem prfExact_tight_abs_le [Nonempty K] [Nonempty Dm] (I : L.Interp) (ρ : SubState A)
    {n q : ℕ} (x : IAdv L (qromSpec (K × Dm) Y) Dm Y Out n A)
    (hx : IAdv.IsQueryBound n x fun _ ↦ q) (E : (Σ u, Out u × Unit) → Prop) :
    |(prfExactReal I ρ n x E).toReal - (prfExactIdeal I ρ n x E).toReal| ≤
      8 * (q : ℝ) ^ 2 / Fintype.card K :=
  prfExact_tight_abs_of_programReal I ρ
    (prfExactTightProgramReal (K × Dm) Y I (fun u ↦ Out u × Unit) ρ q) x hx E

/-- From a real-valued two-sided bound to the one-sided `ℝ≥0∞` form. -/
theorem le_add_ofReal_of_abs_toReal {a b : ℝ≥0∞} {δ : ℝ} (ha : a ≤ 1) (hb : b ≤ 1)
    (h : |a.toReal - b.toReal| ≤ δ) : a ≤ b + ENNReal.ofReal δ := by
  have ha' : a ≠ ⊤ := ne_top_of_le_ne_top one_ne_top ha
  have hb' : b ≠ ⊤ := ne_top_of_le_ne_top one_ne_top hb
  have hδ : 0 ≤ δ := (abs_nonneg _).trans h
  rw [← ENNReal.ofReal_toReal ha', ← ENNReal.ofReal_toReal hb',
    ← ENNReal.ofReal_add ENNReal.toReal_nonneg hδ]
  exact ENNReal.ofReal_le_ofReal (by linarith [(abs_le.1 h).2])

/-- **Exact PRF game, tight bound, real ≤ ideal** (in `ℝ≥0∞`). -/
theorem prfExact_tight_real_le_ideal_add [Nonempty K] [Nonempty Dm] (I : L.Interp)
    (ρ : SubState A) {n q : ℕ} (x : IAdv L (qromSpec (K × Dm) Y) Dm Y Out n A)
    (hx : IAdv.IsQueryBound n x fun _ ↦ q) (E : (Σ u, Out u × Unit) → Prop) :
    prfExactReal I ρ n x E ≤
      prfExactIdeal I ρ n x E + ENNReal.ofReal (8 * (q : ℝ) ^ 2 / Fintype.card K) :=
  le_add_ofReal_of_abs_toReal (prfExact_le_one I ρ x hx E).1 (prfExact_le_one I ρ x hx E).2
    (prfExact_tight_abs_le I ρ x hx E)

/-- **Exact PRF game, tight bound, ideal ≤ real** (in `ℝ≥0∞`). -/
theorem prfExact_tight_ideal_le_real_add [Nonempty K] [Nonempty Dm] (I : L.Interp)
    (ρ : SubState A) {n q : ℕ} (x : IAdv L (qromSpec (K × Dm) Y) Dm Y Out n A)
    (hx : IAdv.IsQueryBound n x fun _ ↦ q) (E : (Σ u, Out u × Unit) → Prop) :
    prfExactIdeal I ρ n x E ≤
      prfExactReal I ρ n x E + ENNReal.ofReal (8 * (q : ℝ) ^ 2 / Fintype.card K) :=
  le_add_ofReal_of_abs_toReal (prfExact_le_one I ρ x hx E).2 (prfExact_le_one I ρ x hx E).1
    (by rw [abs_sub_comm]; exact prfExact_tight_abs_le I ρ x hx E)

end ExactPrf

end PQ.QROM

#print axioms PQ.QROM.prfExactTightProgramReal
#print axioms PQ.QROM.prfExact_tight_abs_le
#print axioms PQ.QROM.prfExact_tight_real_le_ideal_add
#print axioms PQ.QROM.prfExact_tight_ideal_le_real_add
