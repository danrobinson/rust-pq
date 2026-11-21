import Integration.SlhDsaComposed
import PQ.QROM.ExactPrfTight
import PQ.QROM.ExactItsr4
import PQ.QROM.ExactZeroPre
import PQ.QROM.ExactGenUd
import PQ.QROM.ExactGenPre
import PQ.QROM.ExactDsprTightGame
import PQ.Interactive.QromBridgePrf

/-!
# The composed QROM statement for SLH-DSA-SHA2-128s, with the Part-2 bounds applied

NOT part of the default target; checked by `scripts/check-integration.sh`.

## What this file proves, and what it does NOT prove

`Integration/SlhDsaComposed.lean` assumes, per term of the linear headline, the numerical bound
itself (`TermBounds`, twelve fields).  Here every numerical bound is DERIVED from the
machine-checked Part-2 theorem for the corresponding exact game:

| term(s) | Part-2 theorem used | resulting term |
|---|---|---|
| `prf`, `msg` | `prfExact_tight_real_le_ideal_add` | `8 q'² / 2^128` |
| `itsr` | `itsr4_adaptive_fors_le` | `(√((2q'+1)² p_cov(qs)) + 2 q' √(qs / 2^128))²` |
| `dspr` | `dspr_exact_tight_zeroPre_of_card` (tight, target-count-free) | `168 q'² / 2^128` |
| `tcrFv` | `tcr_fv_exact_le_zeroPre` | `(2q'+1)² / 2^128` |
| `tcr1`, `tcr2`, `tcrLen`, `tcrK`, `tcrT` | `tcr_exact_le_zeroPre` or `gen_coll_tcr_exact_le_zeroPre` | `(2q'+1)² / 2^128` |
| `ud` | `gen_ud_exact_tight_real_le_ideal_add` (`q₁ = 0`) | `8 q'² / 2^128` |
| `pre` | `gen_pre_sub_exact_le_zeroPre` | `(2q'+1)² · 2 / 2^128` |

with `q' = q + r.<term>`: the forger's `q` quantum hash queries plus the reduction machine's own
hash evaluations `r.<term>` (`openCounts128s qs`: the counts of the open programs of
`security/Reduction/Open/Bundle.lean`, `FinalResourcesOpen128s`, copied as numerals).

**NO field of `TermBounds` is discharged unconditionally.**  What remains — the hypothesis
`Bridges` — is, per term, a pure SIMULATION statement with no probabilistic analysis in it:

  the `ω`-average of the Part-1 game of the reduction machine around the forger is dominated by
  a sub-convex combination of values of the Part-2 exact game, each for a Part-2 adversary with
  no first-phase quantum queries and at most `q + r.<term>` quantum queries

(`MixLE`, `MixPair`, and the value classes `PrfValue`, `ItsrValue`, `DsprValue`, `TcrFvValue`,
`TcrValue`, `UdValue`, `PreValue`, which fix the game, the sizes `2^128` and the query budgets).
For the three real/ideal terms (`prf`, `msg`, `ud`) and for `dspr` (success / `SPprob`) the
combination must dominate the real side and be dominated on the ideal side, with the SAME
adversaries.

Each of the twelve `Bridges` fields IMPLIES the corresponding numerical bound (that is what is
proved here: `Bridges.prf_le`, …), so `Bridges` is logically at least as strong as a `TermBounds`
with the new term shapes: this file does not weaken the conditional theorem's hypothesis, it
replaces "the bound holds" by "the game is a Part-2 game with these resources", and it uses the
Part-2 theorems.  The bridge itself (Part-1 machines with `U_{enc ω}` instruments, uniform
sampling nodes, probabilistic challengers, the reduction's classical hash evaluations as oracle
calls, two ports / two phases, the reduction of the four hash components to the one function of
the Part-2 game) is NOT proved for any term.

Unproved content of each `Bridges` field, in words:
* the Part-1 machine depends on the attacked hash component only through the port instrument and
  the game's challenger (open forms R1–R3, R7 of `security/status/OPEN.md`; for `PRF`/`PRF_msg`
  the independence of the second phases from the function itself is by inspection only there);
* the first phase makes no quantum query (R4: first phases are hash-free);
* the number of oracle calls is `q + r.<term>` (R6 counts; `r` is a free parameter of the
  theorems, `openCounts128s qs` its instance);
* the sizes: `|K| = |Y| = |Mp| = 2^128`, `|Ix| = 2^h`, `|Lx| = 2^a`, `k` FORS trees, and for DSPR
  `|Y| ≤ |Msg|`;
* for ITSR: at most `qs` target requests, the digest split is uniform on `Ix × Lx^k`.

The ITSR term keeps the reprogramming loss `2 q' √(qs / 2^128)` (general regime).

The Part-2 adversaries of the classes are over local signatures `L : LocalSig.{1, 0}` (the
universe of `LocalSig.instruments.{0}`, the signature used by `PQ/Interactive/QromBridge*.lean`)
with leaf types in `Type`; `PrfValue.ofPort` shows that the PRF game of a Part-1 oracle-port
program lies in `PrfValue`.

## Consequence of the counts

At `r = openCounts128s qs` the reduction's own (classical) hash evaluations, about `2^21` per
signature, are counted as quantum queries of the Part-2 adversary, so they enter quadratically:
`composedBoundFinal_open_le` gives `≤ epsItsr (q + 269824 + 2007385·qs) qs + 84·(2M+1)²/2^128`
with `M = q + 2007385·qs + 277681`, which exceeds `1` for `qs` above about `2^39` whatever `q`
(and the ITSR term already for `qs` above about `2^28`).
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal PQ.Interactive PQ.QROM Quantum
open scoped ComplexOrder

namespace Reduction

/-! ## Sub-convex domination by values of a class -/

/-- `lhs` is at most a sub-convex combination of numbers in the class `V`. -/
def MixLE (lhs : ℝ≥0∞) (V : ℝ≥0∞ → Prop) : Prop :=
  ∃ (Θ : Type) (_ : Fintype Θ) (w v : Θ → ℝ≥0∞),
    ∑ θ, w θ ≤ 1 ∧ (∀ θ, V (v θ)) ∧ lhs ≤ ∑ θ, w θ * v θ

/-- `real` is at most, and `ideal` at least, the same sub-convex combination of pairs in the
class `V`. -/
def MixPair (real ideal : ℝ≥0∞) (V : ℝ≥0∞ → ℝ≥0∞ → Prop) : Prop :=
  ∃ (Θ : Type) (_ : Fintype Θ) (w vr vi : Θ → ℝ≥0∞),
    ∑ θ, w θ ≤ 1 ∧ (∀ θ, V (vr θ) (vi θ)) ∧ real ≤ ∑ θ, w θ * vr θ ∧ ∑ θ, w θ * vi θ ≤ ideal

theorem MixLE.le {lhs ε : ℝ≥0∞} {V : ℝ≥0∞ → Prop} (h : MixLE lhs V)
    (hV : ∀ v, V v → v ≤ ε) : lhs ≤ ε := by
  obtain ⟨Θ, _, w, v, hw, hv, hl⟩ := h
  calc lhs ≤ ∑ θ, w θ * v θ := hl
    _ ≤ ∑ θ, w θ * ε := Finset.sum_le_sum fun θ _ ↦ by
        gcongr
        exact hV _ (hv θ)
    _ = (∑ θ, w θ) * ε := (Finset.sum_mul _ _ _).symm
    _ ≤ 1 * ε := by gcongr
    _ = ε := one_mul _

theorem MixPair.le {real ideal ε : ℝ≥0∞} {V : ℝ≥0∞ → ℝ≥0∞ → Prop} (h : MixPair real ideal V)
    (hV : ∀ a b, V a b → a ≤ b + ε) : real ≤ ideal + ε := by
  obtain ⟨Θ, _, w, vr, vi, hw, hv, hr, hi⟩ := h
  calc real ≤ ∑ θ, w θ * vr θ := hr
    _ ≤ ∑ θ, w θ * (vi θ + ε) := Finset.sum_le_sum fun θ _ ↦ by
        gcongr
        exact hV _ _ (hv θ)
    _ = ∑ θ, w θ * vi θ + (∑ θ, w θ) * ε := by
        simp only [mul_add, Finset.sum_add_distrib, Finset.sum_mul]
    _ ≤ ideal + 1 * ε := by gcongr
    _ = ideal + ε := by rw [one_mul]

/-! ## The classes of Part-2 game values (sizes of SLH-DSA-SHA2-128s) -/

/-- Pairs (real, ideal) of the exact PRF game (`PQ/QROM/ExactPrf.lean`): `F : K × Dm → Y` and the
key uniform, `|K| = 2^128`, the adversary an arbitrary `IAdv` with at most `q` quantum queries to
`F` on every path (any number of classical PRF-oracle requests), any event on its output. -/
inductive PrfValue (q : ℕ) : ℝ≥0∞ → ℝ≥0∞ → Prop
  | mk {K Dm Y : Type} [Fintype K] [DecidableEq K] [Fintype Dm] [DecidableEq Dm] [Fintype Y]
      [DecidableEq Y] [AddCommGroup Y] [Nonempty K] [Nonempty Dm]
      {L : LocalSig.{1, 0}} {Out : QReg → Type} {A : QReg}
      (I : L.Interp) (ρ : SubState A) (n : ℕ) (x : IAdv L (qromSpec (K × Dm) Y) Dm Y Out n A)
      (hx : IAdv.IsQueryBound n x fun _ ↦ q) (E : (Σ u, Out u × Unit) → Prop)
      (hK : Fintype.card K = 2 ^ 128) :
      PrfValue q (prfExactReal I ρ n x E) (prfExactIdeal I ρ n x E)

/-- The PRF game of a Part-1 oracle-port program (`PQ/Interactive/QromBridgePrf.lean`: Born
weights of the compiled machine, averaged over the key and the function) is in the class: a bridge
for the PRF terms may stop at a port program with classical requests and no uniform-sampling
nodes. -/
theorem PrfValue.ofPort {K Dm Y E α : Type} [Fintype K] [DecidableEq K] [Fintype Dm]
    [DecidableEq Dm] [Fintype Y] [DecidableEq Y] [AddCommGroup Y] [Fintype E] [DecidableEq E]
    [Nonempty K] [Nonempty Dm] (n q : ℕ) (P : QProgC (K × Dm) Y E Dm Y α) (hP : PortBound P q)
    (ρ : SubState (((K × Dm) × Y) × E)) (Ev : Option α × Unit → Prop) [DecidablePred Ev]
    (hK : Fintype.card K = 2 ^ 128) :
    PrfValue q (prfRealW n P ρ Ev) (prfIdealW n P ρ Ev) := by
  have h := PrfValue.mk (q := q) (L := LocalSig.instruments.{0}) (Out := fun _ ↦ Option α)
    (A := progReg (K × Dm) Y E) LocalSig.Interp.instruments ρ n (toIAdv n P)
    (isQueryBound_toIAdv n P q hP) (fun p ↦ Ev p.2) hK
  rwa [prfExactReal_toIAdv, prfExactIdeal_toIAdv] at h

/-- Values of the adaptive ITSR game with the FORS cover relation (`PQ/QROM/ExactItsr4.lean`):
`H : K × Xm → Ix × Lx^k` uniform, `|K| = 2^128`, `|Ix| = 2^h`, `|Lx| = 2^a`, `k` trees, at most `s`
target requests and at most `q` quantum queries on every path. -/
inductive ItsrValue (q s : ℕ) : ℝ≥0∞ → Prop
  | mk {K Xm Ix Lx : Type} [Fintype K] [DecidableEq K] [Nonempty K] [Fintype Xm] [DecidableEq Xm]
      [Fintype Ix] [DecidableEq Ix] [AddCommGroup Ix] [Fintype Lx] [DecidableEq Lx]
      [AddCommGroup Lx] {L : LocalSig.{1, 0}} {A : QReg}
      (I : L.Interp) (ρ : SubState A)
      (x : IAdv L (qromSpec (K × Xm) (Ix × (Fin Link.vp.params.k → Lx))) Xm K
        (fun _ ↦ K × Xm) s A)
      (hx : IAdv.IsQueryBound s x fun _ ↦ q)
      (hK : Fintype.card K = 2 ^ 128) (hI : Fintype.card Ix = 2 ^ Link.vp.params.h)
      (hL : Fintype.card Lx = 2 ^ Link.vp.params.a) :
      ItsrValue q s
        (itsrAdaptiveExp I ρ s x (forsCov (I := Ix) (L := Lx) (k := Link.vp.params.k)))

/-- Pairs (success, `SPprob`) of the exact DSPR game with source final validity
(`PQ/QROM/ExactUd.lean`): `|Y| = 2^128 ≤ |Msg|`, no quantum query in the first phase, at most `q`
in the second. -/
inductive DsprValue (q : ℕ) : ℝ≥0∞ → ℝ≥0∞ → Prop
  | mk {Sd Tw Msg Y : Type} [Fintype Sd] [DecidableEq Sd] [Fintype Tw] [DecidableEq Tw]
      [Fintype Msg] [DecidableEq Msg] [Fintype Y] [DecidableEq Y] [AddCommGroup Y] [Inhabited Tw]
      {L : LocalSig.{1, 0}} {Out : QReg → Type} {A : QReg}
      (I : L.Interp) (ρ : SubState A) (cap n : ℕ)
      (x : IAdv L (qrom2Spec (Dom Sd Tw Msg) Y) ((Tw × Msg) ⊕ (Tw × Msg)) Y Out n A)
      (ph2 : Sd → ∀ u, Out u → QuantumComp L (qrom2Spec (Dom Sd Tw Msg) Y) (fun _ ↦ ℕ × Bool) u)
      (hx : IAdv.IsQueryBound n x (firstBudget 0))
      (h2 : ∀ P u o, (ph2 P u o).IsQueryBound (secondBudget q))
      (hY : Fintype.card Y = 2 ^ 128) (hcard : Fintype.card Y ≤ Fintype.card Msg) :
      DsprValue q (dsprSucc I ρ cap n x ph2) (dsprSP I ρ cap n x ph2)

/-- Values of the exact TCR game with source final validity (`PQ/QROM/ExactFv.lean`). -/
inductive TcrFvValue (q : ℕ) : ℝ≥0∞ → Prop
  | mk {Sd Tw Msg Y : Type} [Fintype Sd] [DecidableEq Sd] [Fintype Tw] [DecidableEq Tw]
      [Fintype Msg] [DecidableEq Msg] [Fintype Y] [DecidableEq Y] [AddCommGroup Y] [Inhabited Tw]
      {L : LocalSig.{1, 0}} {Out : QReg → Type} {A : QReg}
      (I : L.Interp) (ρ : SubState A) (cap n : ℕ)
      (x : IAdv L (qrom2Spec (Dom Sd Tw Msg) Y) ((Tw × Msg) ⊕ (Tw × Msg)) Y Out n A)
      (ph2 : Sd → ∀ u, Out u → QuantumComp L (qrom2Spec (Dom Sd Tw Msg) Y) (fun _ ↦ ℕ × Msg) u)
      (hx : IAdv.IsQueryBound n x (firstBudget 0))
      (h2 : ∀ P u o, (ph2 P u o).IsQueryBound (secondBudget q))
      (hY : Fintype.card Y = 2 ^ 128) :
      TcrFvValue q (tcrFvExp I ρ cap n x ph2)

/-- Values of the exact SM-DT-TCR game (`PQ/QROM/ExactTcr.lean`), or of its form with a general
collection family (`PQ/QROM/ExactGenColl.lean`). -/
inductive TcrValue (q : ℕ) : ℝ≥0∞ → Prop
  | plain {Sd Tw Msg Y : Type} [Fintype Sd] [DecidableEq Sd] [Fintype Tw] [DecidableEq Tw]
      [Fintype Msg] [DecidableEq Msg] [Fintype Y] [DecidableEq Y] [AddCommGroup Y] [Inhabited Tw]
      {L : LocalSig.{1, 0}} {Out : QReg → Type} {A : QReg}
      (I : L.Interp) (ρ : SubState A) (cap n : ℕ)
      (x : IAdv L (qrom2Spec (Dom Sd Tw Msg) Y) ((Tw × Msg) ⊕ (Tw × Msg)) (Option Y) Out n A)
      (ph2 : Sd → ∀ u, Out u → QuantumComp L (qrom2Spec (Dom Sd Tw Msg) Y) (fun _ ↦ ℕ × Msg) u)
      (hx : IAdv.IsQueryBound n x (firstBudget 0))
      (h2 : ∀ P u o, (ph2 P u o).IsQueryBound (secondBudget q))
      (hY : Fintype.card Y = 2 ^ 128) :
      TcrValue q (tcrExp I ρ cap n x ph2)
  | coll {Sd Tw Msg Y ι : Type} {MsgC : ι → Type} [Fintype Sd] [DecidableEq Sd] [Fintype Tw]
      [DecidableEq Tw] [Fintype Msg] [DecidableEq Msg] [Fintype Y] [DecidableEq Y]
      [AddCommGroup Y] [Inhabited Tw] [Fintype ι] [DecidableEq ι] [∀ i, Fintype (MsgC i)]
      [∀ i, DecidableEq (MsgC i)]
      {L : LocalSig.{1, 0}} {Out : QReg → Type} {A : QReg}
      (I : L.Interp) (ρ : SubState A) (cap n : ℕ)
      (x : IAdv L (qrom2Spec (Dom Sd Tw (Msg ⊕ (Σ i, MsgC i))) Y)
        ((Tw × Msg) ⊕ (Tw × (Σ i, MsgC i))) (Option Y) Out n A)
      (ph2 : Sd → ∀ u, Out u →
        QuantumComp L (qrom2Spec (Dom Sd Tw (Msg ⊕ (Σ i, MsgC i))) Y) (fun _ ↦ ℕ × Msg) u)
      (hx : IAdv.IsQueryBound n x (firstBudget 0))
      (h2 : ∀ P u o, (ph2 P u o).IsQueryBound (secondBudget q))
      (hY : Fintype.card Y = 2 ^ 128) :
      TcrValue q (genCollTcrExp I ρ cap n x ph2)

/-- Pairs (real, ideal) of the exact SM-DT-UD game in VCVio's shape (`PQ/QROM/ExactGenUd.lean`:
planted inputs in `Mp ↪ Msg`, collection family `C`), `|Mp| = 2^128`. -/
inductive UdValue (q : ℕ) : ℝ≥0∞ → ℝ≥0∞ → Prop
  | mk {Sd Tw Msg Mp C Y : Type} [Fintype Sd] [DecidableEq Sd] [Fintype Tw] [DecidableEq Tw]
      [Fintype Msg] [DecidableEq Msg] [Fintype Mp] [DecidableEq Mp] [Fintype C] [DecidableEq C]
      [Fintype Y] [DecidableEq Y] [AddCommGroup Y] [Nonempty Mp]
      {L : LocalSig.{1, 0}} {Out : QReg → Type} {A : QReg}
      (I : L.Interp) (ρ : SubState A) (cap n : ℕ) (emb : Mp ↪ Msg)
      (x : IAdv L (qrom2Spec (Dom Sd Tw (Msg ⊕ C)) Y) (Tw ⊕ (Tw × C)) (Option Y) Out n A)
      (ph2 : Sd → ∀ u, Out u →
        QuantumComp L (qrom2Spec (Dom Sd Tw (Msg ⊕ C)) Y) (fun _ ↦ Bool) u)
      (hx : IAdv.IsQueryBound n x (firstBudget 0))
      (h2 : ∀ P u o, (ph2 P u o).IsQueryBound (secondBudget q))
      (hM : Fintype.card Mp = 2 ^ 128) :
      UdValue q (genUdReal I ρ cap n emb x ph2) (genUdIdeal I ρ cap n x ph2)

/-- Values of the exact SM-DT-PRE game in VCVio's shape (`PQ/QROM/ExactGenPre.lean`: planted
inputs and the adversary's preimage in `Mp ↪ Msg`), `|Y| = |Mp| = 2^128`. -/
inductive PreValue (q : ℕ) : ℝ≥0∞ → Prop
  | mk {Sd Tw Msg Mp Y : Type} [Fintype Sd] [DecidableEq Sd] [Fintype Tw] [DecidableEq Tw]
      [Fintype Msg] [DecidableEq Msg] [Fintype Mp] [DecidableEq Mp] [Fintype Y] [DecidableEq Y]
      [AddCommGroup Y] [Inhabited Tw]
      {L : LocalSig.{1, 0}} {Out : QReg → Type} {A : QReg}
      (I : L.Interp) (ρ : SubState A) (cap n : ℕ) (emb : Mp ↪ Msg)
      (x : IAdv L (qrom2Spec (Dom Sd Tw Msg) Y) (Tw ⊕ (Tw × Msg)) (Option Y) Out n A)
      (ph2 : Sd → ∀ u, Out u → QuantumComp L (qrom2Spec (Dom Sd Tw Msg) Y) (fun _ ↦ ℕ × Mp) u)
      (hx : IAdv.IsQueryBound n x (firstBudget 0))
      (h2 : ∀ P u o, (ph2 P u o).IsQueryBound (secondBudget q))
      (hY : Fintype.card Y = 2 ^ 128) (hM : Fintype.card Mp = 2 ^ 128) :
      PreValue q (genPreSubExp I ρ cap n emb x ph2)

/-! ## The terms -/

/-- TCR term without first-phase queries: `(2q+1)² / 2^128`. -/
noncomputable def epsTcr0 (q : ℕ) : ℝ≥0∞ := (2 * (q : ℝ≥0∞) + 1) ^ 2 / N128

/-- DSPR term, tight and target-count-free, without first-phase queries: `168 q² / 2^128`
(`dspr_exact_tight_zeroPre_of_card`). -/
noncomputable def epsDsprTight (q : ℕ) : ℝ≥0∞ := ENNReal.ofReal (168 * (q : ℝ) ^ 2 / 2 ^ 128)

/-- UD term, VCVio-shaped game, without first-phase queries: `8 q² / 2^128`
(`gen_ud_exact_tight_real_le_ideal_add`). -/
noncomputable def epsUdTight (q : ℕ) : ℝ≥0∞ := ENNReal.ofReal (8 * (q : ℝ) ^ 2 / 2 ^ 128)

/-- PRE term without first-phase queries: `(2q+1)² (1/2^128 + 1/2^128)`. -/
noncomputable def epsPre0 (q : ℕ) : ℝ≥0∞ := (2 * (q : ℝ≥0∞) + 1) ^ 2 * (N128⁻¹ + N128⁻¹)

lemma card_cast_N128 {T : Type} [Fintype T] (h : Fintype.card T = 2 ^ 128) :
    (Fintype.card T : ℝ≥0∞) = N128 := by
  rw [h, Nat.cast_pow, Nat.cast_ofNat, N128]

lemma card_cast_real {T : Type} [Fintype T] (h : Fintype.card T = 2 ^ 128) :
    (Fintype.card T : ℝ) = 2 ^ 128 := by
  rw [h, Nat.cast_pow, Nat.cast_ofNat]

/-! ## Part-2 theorems on the value classes -/

theorem PrfValue.le {q : ℕ} {a b : ℝ≥0∞} (h : PrfValue q a b) : a ≤ b + epsPrf q := by
  cases h with
  | mk I ρ n x hx E hK =>
    have h := prfExact_tight_real_le_ideal_add I ρ x hx E
    rwa [card_cast_real hK] at h

theorem ItsrValue.le {q s : ℕ} {v : ℝ≥0∞} (h : ItsrValue q s v) :
    v ≤ epsItsr Link.vp.params q s := by
  cases h with
  | @mk K Xm Ix Lx _ _ _ _ _ _ _ _ _ _ _ L A I ρ x hx hK hI hL =>
    have h := itsr4_adaptive_fors_le I ρ s x q hx
    have eI : (Fintype.card Ix : ℝ≥0∞) = 2 ^ Link.vp.params.h := by
      rw [hI, Nat.cast_pow, Nat.cast_ofNat]
    have eL : (Fintype.card Lx : ℝ≥0∞) = 2 ^ Link.vp.params.a := by
      rw [hL, Nat.cast_pow, Nat.cast_ofNat]
    rw [eI, eL, card_cast_N128 hK] at h
    exact h

theorem DsprValue.le {q : ℕ} {a b : ℝ≥0∞} (h : DsprValue q a b) : a ≤ b + epsDsprTight q := by
  cases h with
  | mk I ρ cap n x ph2 hx h2 hY hcard =>
    have h := dspr_exact_tight_zeroPre_of_card (I := I) (ρ := ρ) (cap := cap)
      (by rw [hY]; norm_num) hcard hx h2
    rw [card_cast_real hY] at h
    exact tsub_le_iff_left.1 h

theorem TcrFvValue.le {q : ℕ} {v : ℝ≥0∞} (h : TcrFvValue q v) : v ≤ epsTcr0 q := by
  cases h with
  | mk I ρ cap n x ph2 hx h2 hY =>
    have h := tcr_fv_exact_le_zeroPre (I := I) (ρ := ρ) (cap := cap) hx h2
    rwa [card_cast_N128 hY] at h

theorem TcrValue.le {q : ℕ} {v : ℝ≥0∞} (h : TcrValue q v) : v ≤ epsTcr0 q := by
  cases h with
  | plain I ρ cap n x ph2 hx h2 hY =>
    have h := tcr_exact_le_zeroPre (I := I) (ρ := ρ) (cap := cap) hx h2
    rwa [card_cast_N128 hY] at h
  | coll I ρ cap n x ph2 hx h2 hY =>
    have h := gen_coll_tcr_exact_le_zeroPre (I := I) (ρ := ρ) (cap := cap) hx h2
    rwa [card_cast_N128 hY] at h

theorem UdValue.le {q : ℕ} {a b : ℝ≥0∞} (h : UdValue q a b) : a ≤ b + epsUdTight q := by
  cases h with
  | mk I ρ cap n emb x ph2 hx h2 hM =>
    have h := gen_ud_exact_tight_real_le_ideal_add (I := I) (ρ := ρ) (cap := cap) (emb := emb)
      hx h2
    rwa [card_cast_real hM, zero_add] at h

theorem PreValue.le {q : ℕ} {v : ℝ≥0∞} (h : PreValue q v) : v ≤ epsPre0 q := by
  cases h with
  | mk I ρ cap n emb x ph2 hx h2 hY hM =>
    have h := gen_pre_sub_exact_le_zeroPre (I := I) (ρ := ρ) (cap := cap) (emb := emb) hx h2
    rwa [card_cast_N128 hY, card_cast_N128 hM] at h

/-! ## Counts and the composed bound -/

/-- The reduction machines' own hash evaluations (second phases; PRF/ITSR machines: whole run),
one count per term. -/
structure RedCounts where
  prf : ℕ
  msg : ℕ
  itsr : ℕ
  dspr : ℕ
  tcrFv : ℕ
  tcr1 : ℕ
  tcr2 : ℕ
  tcrLen : ℕ
  tcrK : ℕ
  ud : ℕ
  pre : ℕ
  tcrT : ℕ

/-- The hash-query counts of the open programs of the reduction at SLH-DSA-SHA2-128s with `qs`
signing queries (`security/Reduction/Open/Bundle.lean`, `FinalResourcesOpen128s`; numerals
copied, not derived here).  They count ALL hash evaluations of each machine, also those of
components other than the one attacked in the term. -/
def openCounts128s (qs : ℕ) : RedCounts where
  prf := 269824 + qs * 2007385 + 3929
  msg := 269824 + qs * 2007385 + 3929
  itsr := 269824 + qs * 2007385
  dspr := 269839 + qs * 1950028
  tcrFv := 269839 + qs * 1950028
  tcr1 := 269824 + qs * 2007385 + 7857
  tcr2 := 269824 + qs * 2007385 + 7857
  tcrLen := 269824 + qs * 2007385 + 7857
  tcrK := 269824 + qs * 2007385 + 7857
  ud := qs * 121857 + 130239
  pre := qs * 121857 + 130274
  tcrT := qs * 121857 + 146514

/-- **The composed bound**, explicit in the forger's `q` quantum hash queries, its `qs` signing
queries and the reduction's own counts `r`. -/
noncomputable def composedBoundFinal (q qs : ℕ) (r : RedCounts) : ℝ≥0∞ :=
  epsPrf (q + r.prf) + epsPrf (q + r.msg) + epsItsr Link.vp.params (q + r.itsr) qs +
    (epsDsprTight (q + r.dspr) + 3 * epsTcr0 (q + r.tcrFv)) +
    (epsTcr0 (q + r.tcr1) + epsTcr0 (q + r.tcr2) + epsTcr0 (q + r.tcrLen) +
      epsTcr0 (q + r.tcrK)) +
    ((Link.vp.params.w - 2 : ℕ) : ℝ≥0∞) * epsUdTight (q + r.ud) + epsPre0 (q + r.pre) +
    epsTcr0 (q + r.tcrT)

/-! ## A simpler closed form at the open counts -/

/-- Upper bound on every count `q + (openCounts128s qs).<term>`. -/
def M128 (q qs : ℕ) : ℕ := q + 2007385 * qs + 277681

lemma epsTcr0_eq (q : ℕ) : epsTcr0 q = ENNReal.ofReal ((2 * (q : ℝ) + 1) ^ 2 / 2 ^ 128) := by
  unfold epsTcr0 N128
  rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_pow (by positivity),
    ENNReal.ofReal_add (by positivity) zero_le_one, ENNReal.ofReal_mul (by norm_num),
    ENNReal.ofReal_natCast, ENNReal.ofReal_pow (by norm_num)]
  simp

lemma epsTcr0_mono {a b : ℕ} (h : a ≤ b) : epsTcr0 a ≤ epsTcr0 b := by
  have h' : (a : ℝ≥0∞) ≤ b := by exact_mod_cast h
  unfold epsTcr0
  gcongr

/-- `c · 4 a² / 2^128 ≤ c · (2b+1)² / 2^128` for `a ≤ b`. -/
lemma ofReal_sq_le_mul_epsTcr0 (k : ℕ) {a b : ℕ} (h : a ≤ b) :
    ENNReal.ofReal (4 * (k : ℝ) * (a : ℝ) ^ 2 / 2 ^ 128) ≤ (k : ℝ≥0∞) * epsTcr0 b := by
  have h' : (a : ℝ) ≤ b := by exact_mod_cast h
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  rw [epsTcr0_eq, ← ENNReal.ofReal_natCast k, ← ENNReal.ofReal_mul (Nat.cast_nonneg k)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [← mul_div_assoc]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have : 4 * (a : ℝ) ^ 2 ≤ (2 * (b : ℝ) + 1) ^ 2 := by nlinarith
  nlinarith

lemma epsPrf_le {a b : ℕ} (h : a ≤ b) : epsPrf a ≤ 2 * epsTcr0 b := by
  have := ofReal_sq_le_mul_epsTcr0 2 h
  unfold epsPrf
  norm_num at this ⊢
  exact this

lemma epsUdTight_le {a b : ℕ} (h : a ≤ b) : epsUdTight a ≤ 2 * epsTcr0 b := by
  have := ofReal_sq_le_mul_epsTcr0 2 h
  unfold epsUdTight
  norm_num at this ⊢
  exact this

lemma epsDsprTight_le {a b : ℕ} (h : a ≤ b) : epsDsprTight a ≤ 42 * epsTcr0 b := by
  have := ofReal_sq_le_mul_epsTcr0 42 h
  unfold epsDsprTight
  norm_num at this ⊢
  exact this

lemma epsPre0_le {a b : ℕ} (h : a ≤ b) : epsPre0 a ≤ 2 * epsTcr0 b := by
  have e : epsPre0 a = 2 * epsTcr0 a := by
    unfold epsPre0 epsTcr0
    rw [div_eq_mul_inv]
    ring
  rw [e]
  gcongr
  exact epsTcr0_mono h

/-- **Closed form**: the ITSR term plus `84 · (2M+1)² / 2^128`, `M = q + 2007385·qs + 277681`. -/
noncomputable def closedBound128s (q qs : ℕ) : ℝ≥0∞ :=
  epsItsr Link.vp.params (q + (269824 + qs * 2007385)) qs + 84 * epsTcr0 (M128 q qs)

/-- The composed bound at the open counts is at most the closed form. -/
theorem composedBoundFinal_open_le (q qs : ℕ) :
    composedBoundFinal q qs (openCounts128s qs) ≤ closedBound128s q qs := by
  have hw : ((Link.vp.params.w - 2 : ℕ) : ℝ≥0∞) = 14 := by
    have : Link.vp.params.w - 2 = 14 := rfl
    rw [this]
    norm_num
  set T := epsTcr0 (M128 q qs) with hT
  have hP : ∀ a, a ≤ M128 q qs → epsPrf a ≤ 2 * T := fun a h ↦ epsPrf_le h
  have hD : ∀ a, a ≤ M128 q qs → epsDsprTight a ≤ 42 * T := fun a h ↦ epsDsprTight_le h
  have hU : ∀ a, a ≤ M128 q qs → epsUdTight a ≤ 2 * T := fun a h ↦ epsUdTight_le h
  have hR : ∀ a, a ≤ M128 q qs → epsPre0 a ≤ 2 * T := fun a h ↦ epsPre0_le h
  have hC : ∀ a, a ≤ M128 q qs → epsTcr0 a ≤ T := fun a h ↦ epsTcr0_mono h
  unfold composedBoundFinal closedBound128s
  rw [hw]
  simp only [openCounts128s]
  calc _ ≤ 2 * T + 2 * T + epsItsr Link.vp.params (q + (269824 + qs * 2007385)) qs +
          (42 * T + 3 * T) + (T + T + T + T) + 14 * (2 * T) + 2 * T + T := by
        refine add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add
          (add_le_add (hP _ ?_) (hP _ ?_)) le_rfl) (add_le_add (hD _ ?_)
            (mul_le_mul' le_rfl (hC _ ?_))))
          (add_le_add (add_le_add (add_le_add (hC _ ?_) (hC _ ?_)) (hC _ ?_)) (hC _ ?_)))
          (mul_le_mul' le_rfl (hU _ ?_))) (hR _ ?_)) (hC _ ?_) <;>
        (unfold M128; omega)
    _ = _ := by ring

variable {W : Type} [Fintype W]

section
variable (c : Caps)
  (optRand : ∀ ω : Ω128 c, PublicKeyCore (primsΩ ω).core → ProbComp (primsΩ ω).Y)
  (pkSeedDist : ∀ ω : Ω128 c, ProbComp (primsΩ ω).PkSeed)

/-- **The bridge hypotheses** (UNPROVED): for each term of the linear headline, the `ω`-averaged
Part-1 game of the reduction machine around `B ω` is dominated by a sub-convex combination of
Part-2 exact-game values with the stated resources. -/
structure Bridges
    (B : ∀ ω, QForger W (internalAlg Link.vp (primsΩ ω) (optRand ω) (pkSeedDist ω)))
    (R₁ I₁ R₂ I₂ : Ω128 c → ℝ≥0∞) (q qs : ℕ) (r : RedCounts) : Prop where
  /-- `PRF`. -/
  prf : MixPair (avΩ c R₁) (avΩ c I₁) (PrfValue (q + r.prf))
  /-- `PRF_msg`. -/
  msg : MixPair (avΩ c R₂) (avΩ c I₂) (PrfValue (q + r.msg))
  /-- ITSR of `H_msg`, at most `qs` target requests. -/
  itsr : MixLE
    (avΩ c fun ω ↦ qItsrAdvantage (itsrProblem Link.vp (primsΩ ω)) (qbItsrL (B ω)) (B ω).ρ₀)
    (ItsrValue (q + r.itsr) qs)
  /-- DSPR (source final validity), FORS leaves. -/
  dspr : MixPair (avΩ c fun ω ↦ qDsprFV_Success (qToDspr (B ω)))
    (avΩ c fun ω ↦ qDsprFV_SPProbability (qToDspr (B ω))) (DsprValue (q + r.dspr))
  /-- TCR (source final validity), FORS leaves. -/
  tcrFv : MixLE (avΩ c fun ω ↦ qTcrFV_Advantage (qToTcr (B ω))) (TcrFvValue (q + r.tcrFv))
  /-- SM-DT-TCR, arity 1. -/
  tcr1 : MixLE (avΩ c fun ω ↦ qSM_DT_TCR_Advantage (qbTcrArM 1 (B ω))) (TcrValue (q + r.tcr1))
  /-- SM-DT-TCR, arity 2. -/
  tcr2 : MixLE (avΩ c fun ω ↦ qSM_DT_TCR_Advantage (qbTcrArM 2 (B ω))) (TcrValue (q + r.tcr2))
  /-- SM-DT-TCR, arity `len`. -/
  tcrLen : MixLE (avΩ c fun ω ↦ qSM_DT_TCR_Advantage (qbTcrArM Link.vp.params.len (B ω)))
    (TcrValue (q + r.tcrLen))
  /-- SM-DT-TCR, arity `k`. -/
  tcrK : MixLE (avΩ c fun ω ↦ qSM_DT_TCR_Advantage (qbTcrArM Link.vp.params.k (B ω)))
    (TcrValue (q + r.tcrK))
  /-- SM-DT-UD of the WOTS chains. -/
  ud : MixPair (avΩ c fun ω ↦ qSM_DT_UD_RealSuccess (qrUd (B ω)))
    (avΩ c fun ω ↦ qSM_DT_UD_IdealSuccess (qrUd (B ω))) (UdValue (q + r.ud))
  /-- SM-DT-PRE of the WOTS chains. -/
  pre : MixLE (avΩ c fun ω ↦ qSM_DT_PRE_Advantage (qrPre (B ω))) (PreValue (q + r.pre))
  /-- SM-DT-TCR of the WOTS chains. -/
  tcrT : MixLE (avΩ c fun ω ↦ qSM_DT_TCR_Advantage (qrTcrT (B ω))) (TcrValue (q + r.tcrT))

variable {c optRand pkSeedDist}

/-- Arithmetic core with arbitrary term bounds: the averaged linear inequality and one bound per
term give the sum of the bounds. -/
theorem composed_of_linear_eps
    (B : ∀ ω, QForger W (internalAlg Link.vp (primsΩ ω) (optRand ω) (pkSeedDist ω)))
    (adv R₁ I₁ R₂ I₂ : Ω128 c → ℝ≥0∞)
    (ePrf eMsg eItsr eDspr eFv e1 e2 eLen eK eUd ePre eT : ℝ≥0∞)
    (hI₁ : ∀ ω, I₁ ω ≤ 1) (hI₂ : ∀ ω, I₂ ω ≤ 1)
    (hlin : avΩ c adv + avΩ c (fun ω ↦ qLinearIdealSide (B ω) (I₁ ω) (I₂ ω)) ≤
      avΩ c (fun ω ↦ qLinearRealSide (B ω) (R₁ ω) (R₂ ω)))
    (hprf : avΩ c R₁ ≤ avΩ c I₁ + ePrf) (hmsg : avΩ c R₂ ≤ avΩ c I₂ + eMsg)
    (hitsr : avΩ c (fun ω ↦
      qItsrAdvantage (itsrProblem Link.vp (primsΩ ω)) (qbItsrL (B ω)) (B ω).ρ₀) ≤ eItsr)
    (hdspr : avΩ c (fun ω ↦ qDsprFV_Success (qToDspr (B ω))) ≤
      avΩ c (fun ω ↦ qDsprFV_SPProbability (qToDspr (B ω))) + eDspr)
    (hfv : avΩ c (fun ω ↦ qTcrFV_Advantage (qToTcr (B ω))) ≤ eFv)
    (h1 : avΩ c (fun ω ↦ qSM_DT_TCR_Advantage (qbTcrArM 1 (B ω))) ≤ e1)
    (h2 : avΩ c (fun ω ↦ qSM_DT_TCR_Advantage (qbTcrArM 2 (B ω))) ≤ e2)
    (hLen : avΩ c (fun ω ↦ qSM_DT_TCR_Advantage (qbTcrArM Link.vp.params.len (B ω))) ≤ eLen)
    (hK : avΩ c (fun ω ↦ qSM_DT_TCR_Advantage (qbTcrArM Link.vp.params.k (B ω))) ≤ eK)
    (hud : avΩ c (fun ω ↦ qSM_DT_UD_RealSuccess (qrUd (B ω))) ≤
      avΩ c (fun ω ↦ qSM_DT_UD_IdealSuccess (qrUd (B ω))) + eUd)
    (hpre : avΩ c (fun ω ↦ qSM_DT_PRE_Advantage (qrPre (B ω))) ≤ ePre)
    (hT : avΩ c (fun ω ↦ qSM_DT_TCR_Advantage (qrTcrT (B ω))) ≤ eT) :
    avΩ c adv ≤ ePrf + eMsg + eItsr + (eDspr + 3 * eFv) + (e1 + e2 + eLen + eK) +
      ((Link.vp.params.w - 2 : ℕ) : ℝ≥0∞) * eUd + ePre + eT := by
  have hfin : avΩ c (fun ω ↦ qLinearIdealSide (B ω) (I₁ ω) (I₂ ω)) ≠ ⊤ := by
    refine avΩ_ne_top c _ fun ω ↦ ?_
    have h1 := hI₁ ω
    have h2 := hI₂ ω
    have h3 : qDsprFV_SPProbability (qToDspr (B ω)) ≤ 1 :=
      qWeight_le_one _ _ (qToDspr (B ω)).posSemidef (qToDspr (B ω)).trace_eq_one
    have h4 : qSM_DT_UD_IdealSuccess (qrUd (B ω)) ≤ 1 :=
      qWeight_le_one _ _ (qrUd (B ω)).posSemidef (qrUd (B ω)).trace_eq_one
    unfold qLinearIdealSide
    refine ne_top_of_le_ne_top (b := 1 + 1 + 1 + ((Link.vp.params.w - 2 : ℕ) : ℝ≥0∞) * 1) ?_ ?_
    · simp
    · gcongr
  have hId : avΩ c (fun ω ↦ qLinearIdealSide (B ω) (I₁ ω) (I₂ ω)) =
      avΩ c I₁ + avΩ c I₂ + avΩ c (fun ω ↦ qDsprFV_SPProbability (qToDspr (B ω))) +
        ((Link.vp.params.w - 2 : ℕ) : ℝ≥0∞) *
          avΩ c (fun ω ↦ qSM_DT_UD_IdealSuccess (qrUd (B ω))) := by
    unfold qLinearIdealSide
    simp only [avΩ_add, avΩ_const_mul]
  have hRe : avΩ c (fun ω ↦ qLinearRealSide (B ω) (R₁ ω) (R₂ ω)) =
      avΩ c R₁ + avΩ c R₂ +
        avΩ c (fun ω ↦ qItsrAdvantage (itsrProblem Link.vp (primsΩ ω)) (qbItsrL (B ω)) (B ω).ρ₀) +
        (avΩ c (fun ω ↦ qDsprFV_Success (qToDspr (B ω))) +
          3 * avΩ c (fun ω ↦ qTcrFV_Advantage (qToTcr (B ω)))) +
        (avΩ c (fun ω ↦ qSM_DT_TCR_Advantage (qbTcrArM 1 (B ω))) +
          avΩ c (fun ω ↦ qSM_DT_TCR_Advantage (qbTcrArM 2 (B ω))) +
          avΩ c (fun ω ↦ qSM_DT_TCR_Advantage (qbTcrArM Link.vp.params.len (B ω))) +
          avΩ c (fun ω ↦ qSM_DT_TCR_Advantage (qbTcrArM Link.vp.params.k (B ω)))) +
        ((Link.vp.params.w - 2 : ℕ) : ℝ≥0∞) *
          avΩ c (fun ω ↦ qSM_DT_UD_RealSuccess (qrUd (B ω))) +
        avΩ c (fun ω ↦ qSM_DT_PRE_Advantage (qrPre (B ω))) +
        avΩ c (fun ω ↦ qSM_DT_TCR_Advantage (qrTcrT (B ω))) := by
    unfold qLinearRealSide
    simp only [avΩ_add, avΩ_const_mul]
  have hle : avΩ c (fun ω ↦ qLinearRealSide (B ω) (R₁ ω) (R₂ ω)) ≤
      (ePrf + eMsg + eItsr + (eDspr + 3 * eFv) + (e1 + e2 + eLen + eK) +
        ((Link.vp.params.w - 2 : ℕ) : ℝ≥0∞) * eUd + ePre + eT) +
        avΩ c (fun ω ↦ qLinearIdealSide (B ω) (I₁ ω) (I₂ ω)) := by
    rw [hRe, hId]
    have hud' : ((Link.vp.params.w - 2 : ℕ) : ℝ≥0∞) *
          avΩ c (fun ω ↦ qSM_DT_UD_RealSuccess (qrUd (B ω))) ≤
        ((Link.vp.params.w - 2 : ℕ) : ℝ≥0∞) *
          (avΩ c (fun ω ↦ qSM_DT_UD_IdealSuccess (qrUd (B ω))) + eUd) := by
      gcongr
    have hfv' : 3 * avΩ c (fun ω ↦ qTcrFV_Advantage (qToTcr (B ω))) ≤ 3 * eFv := by
      gcongr
    calc _ ≤ (avΩ c I₁ + ePrf) + (avΩ c I₂ + eMsg) + eItsr +
          ((avΩ c (fun ω ↦ qDsprFV_SPProbability (qToDspr (B ω))) + eDspr) + 3 * eFv) +
          (e1 + e2 + eLen + eK) +
          ((Link.vp.params.w - 2 : ℕ) : ℝ≥0∞) *
            (avΩ c (fun ω ↦ qSM_DT_UD_IdealSuccess (qrUd (B ω))) + eUd) +
          ePre + eT :=
        add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add
          (add_le_add hprf hmsg) hitsr) (add_le_add hdspr hfv'))
          (add_le_add (add_le_add (add_le_add h1 h2) hLen) hK)) hud') hpre) hT
      _ = _ := by ring
  exact (ENNReal.add_le_add_iff_right hfin).1 (hlin.trans hle)

/-- **Composition with Part 2**: the averaged linear inequality and the bridge hypotheses give
the composed bound; every numerical term is supplied by the Part-2 theorem of its game. -/
theorem composed_of_bridges
    (B : ∀ ω, QForger W (internalAlg Link.vp (primsΩ ω) (optRand ω) (pkSeedDist ω)))
    (adv R₁ I₁ R₂ I₂ : Ω128 c → ℝ≥0∞) (q qs : ℕ) (r : RedCounts)
    (hI₁ : ∀ ω, I₁ ω ≤ 1) (hI₂ : ∀ ω, I₂ ω ≤ 1)
    (hlin : avΩ c adv + avΩ c (fun ω ↦ qLinearIdealSide (B ω) (I₁ ω) (I₂ ω)) ≤
      avΩ c (fun ω ↦ qLinearRealSide (B ω) (R₁ ω) (R₂ ω)))
    (hB : Bridges c optRand pkSeedDist B R₁ I₁ R₂ I₂ q qs r) :
    avΩ c adv ≤ composedBoundFinal q qs r :=
  composed_of_linear_eps B adv R₁ I₁ R₂ I₂ _ _ _ _ _ _ _ _ _ _ _ _ hI₁ hI₂ hlin
    (hB.prf.le fun _ _ ↦ PrfValue.le) (hB.msg.le fun _ _ ↦ PrfValue.le)
    (hB.itsr.le fun _ ↦ ItsrValue.le) (hB.dspr.le fun _ _ ↦ DsprValue.le)
    (hB.tcrFv.le fun _ ↦ TcrFvValue.le) (hB.tcr1.le fun _ ↦ TcrValue.le)
    (hB.tcr2.le fun _ ↦ TcrValue.le) (hB.tcrLen.le fun _ ↦ TcrValue.le)
    (hB.tcrK.le fun _ ↦ TcrValue.le) (hB.ud.le fun _ _ ↦ UdValue.le)
    (hB.pre.le fun _ ↦ PreValue.le) (hB.tcrT.le fun _ ↦ TcrValue.le)

/-- Bridge hypotheses, SUF-CMA (PRF distinguishers `qbPrfWC sufCheck`, `qbPrfMsgWL sufCheck`). -/
abbrev BridgesSuf (c : Caps)
    (optRand : ∀ ω : Ω128 c, PublicKeyCore (primsΩ ω).core → ProbComp (primsΩ ω).Y)
    (pkSeedDist : ∀ ω : Ω128 c, ProbComp (primsΩ ω).PkSeed)
    (B : ∀ ω, QForger W (internalAlg Link.vp (primsΩ ω) (optRand ω) (pkSeedDist ω)))
    (q qs : ℕ) (r : RedCounts) : Prop :=
  Bridges c optRand pkSeedDist B
    (fun ω ↦ qPrfRealPr (skPrfC Link.vp (primsΩ ω)) (qbPrfWC sufCheck (B ω)) (B ω).ρ₀)
    (fun ω ↦ qPrfIdealPr (qbPrfWC sufCheck (B ω)) (B ω).ρ₀)
    (fun ω ↦ qPrfRealPr (msgPrf Link.vp (primsΩ ω)) (qbPrfMsgWL sufCheck (B ω)) (B ω).ρ₀)
    (fun ω ↦ qPrfIdealPr (qbPrfMsgWL sufCheck (B ω)) (B ω).ρ₀) q qs r

/-- Bridge hypotheses, EUF-CMA (PRF distinguishers `qbPrfC`, `qbPrfMsgL`). -/
abbrev BridgesEuf (c : Caps)
    (optRand : ∀ ω : Ω128 c, PublicKeyCore (primsΩ ω).core → ProbComp (primsΩ ω).Y)
    (pkSeedDist : ∀ ω : Ω128 c, ProbComp (primsΩ ω).PkSeed)
    (B : ∀ ω, QForger W (internalAlg Link.vp (primsΩ ω) (optRand ω) (pkSeedDist ω)))
    (q qs : ℕ) (r : RedCounts) : Prop :=
  Bridges c optRand pkSeedDist B
    (fun ω ↦ qPrfRealPr (skPrfC Link.vp (primsΩ ω)) (qbPrfC (B ω)) (B ω).ρ₀)
    (fun ω ↦ qPrfIdealPr (qbPrfC (B ω)) (B ω).ρ₀)
    (fun ω ↦ qPrfRealPr (msgPrf Link.vp (primsΩ ω)) (qbPrfMsgL (B ω)) (B ω).ρ₀)
    (fun ω ↦ qPrfIdealPr (qbPrfMsgL (B ω)) (B ω).ρ₀) q qs r

end

section port

variable {X Y E : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
  [Fintype E] [DecidableEq E] (c : Caps)
  (optRand₀ : Bytes Link.vp.params.n → Bytes Link.vp.params.n → ProbComp (Bytes Link.vp.params.n))
  (pkSeedDist₀ : ProbComp (Bytes Link.vp.params.n))

/-- **Composed theorem modulo the bridge, SUF-CMA, FIPS 205 external pure interface on byte
strings, hash components uniformly random in `Ω128 c`.**  The only unproved hypothesis is `hB`
(the twelve bridge statements `Bridges`, with premises `hq`, `hqs`, `hcap`); all numerical bounds
are the Part-2 theorems. -/
theorem slhdsa_sha2_128s_pure_bytes_suf_cma_qrom_of_bridges
    (enc : Ω128 c → X → Y) (F : PortForger X Y E) (q qs : ℕ) (r : RedCounts)
    (hq : ∀ pk, CountBound isPort (F.main pk) q)
    (hqs : ∀ pk, CountBound isSign (F.main pk) qs)
    (hcap : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk))
    (hB : (∀ pk, CountBound isPort (F.main pk) q) → (∀ pk, CountBound isSign (F.main pk) qs) →
      (∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) →
      BridgesSuf c (optRandOf c optRand₀) (fun _ ↦ pkSeedDist₀)
        (internalΩ c optRand₀ pkSeedDist₀ enc F) q qs r) :
    avΩ c (fun ω ↦ qStrongUnforgeableAdvantage (F.at (enc ω) (algΩ c optRand₀ pkSeedDist₀ ω))) ≤
      composedBoundFinal q qs r :=
  composed_of_bridges (internalΩ c optRand₀ pkSeedDist₀ enc F) _ _ _ _ _ q qs r
    (fun ω ↦ qPrfIdealPr_le_one' _ (internalΩ c optRand₀ pkSeedDist₀ enc F ω).posSemidef
      (internalΩ c optRand₀ pkSeedDist₀ enc F ω).trace_eq_one)
    (fun ω ↦ qPrfIdealPr_le_one' _ (internalΩ c optRand₀ pkSeedDist₀ enc F ω).posSemidef
      (internalΩ c optRand₀ pkSeedDist₀ enc F ω).trace_eq_one)
    (slhdsa_sha2_128s_pure_bytes_suf_cma_linear_quantum_uniform c (optRandOf c optRand₀)
      (fun _ ↦ pkSeedDist₀) fun ω ↦ F.at (enc ω) (algΩ c optRand₀ pkSeedDist₀ ω))
    (hB hq hqs hcap)

/-- **Composed theorem modulo the bridge, EUF-CMA** (same interface and hypotheses, PRF
distinguishers `qbPrfC`, `qbPrfMsgL`). -/
theorem slhdsa_sha2_128s_pure_bytes_euf_cma_qrom_of_bridges
    (enc : Ω128 c → X → Y) (F : PortForger X Y E) (q qs : ℕ) (r : RedCounts)
    (hq : ∀ pk, CountBound isPort (F.main pk) q)
    (hqs : ∀ pk, CountBound isSign (F.main pk) qs)
    (hcap : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk))
    (hB : (∀ pk, CountBound isPort (F.main pk) q) → (∀ pk, CountBound isSign (F.main pk) qs) →
      (∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) →
      BridgesEuf c (optRandOf c optRand₀) (fun _ ↦ pkSeedDist₀)
        (internalΩ c optRand₀ pkSeedDist₀ enc F) q qs r) :
    avΩ c (fun ω ↦ qUnforgeableAdvantage (F.at (enc ω) (algΩ c optRand₀ pkSeedDist₀ ω))) ≤
      composedBoundFinal q qs r :=
  composed_of_bridges (internalΩ c optRand₀ pkSeedDist₀ enc F) _ _ _ _ _ q qs r
    (fun ω ↦ qPrfIdealPr_le_one' _ (internalΩ c optRand₀ pkSeedDist₀ enc F ω).posSemidef
      (internalΩ c optRand₀ pkSeedDist₀ enc F ω).trace_eq_one)
    (fun ω ↦ qPrfIdealPr_le_one' _ (internalΩ c optRand₀ pkSeedDist₀ enc F ω).posSemidef
      (internalΩ c optRand₀ pkSeedDist₀ enc F ω).trace_eq_one)
    (slhdsa_sha2_128s_pure_bytes_euf_cma_linear_quantum_uniform c (optRandOf c optRand₀)
      (fun _ ↦ pkSeedDist₀) fun ω ↦ F.at (enc ω) (algΩ c optRand₀ pkSeedDist₀ ω))
    (hB hq hqs hcap)

/-- **SUF-CMA, closed form at the open counts of the reduction**: the forgery probability is at
most `closedBound128s q qs`, under the bridge hypotheses with `r = openCounts128s qs`. -/
theorem slhdsa_sha2_128s_pure_bytes_suf_cma_qrom_closed
    (enc : Ω128 c → X → Y) (F : PortForger X Y E) (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q)
    (hqs : ∀ pk, CountBound isSign (F.main pk) qs)
    (hcap : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk))
    (hB : (∀ pk, CountBound isPort (F.main pk) q) → (∀ pk, CountBound isSign (F.main pk) qs) →
      (∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) →
      BridgesSuf c (optRandOf c optRand₀) (fun _ ↦ pkSeedDist₀)
        (internalΩ c optRand₀ pkSeedDist₀ enc F) q qs (openCounts128s qs)) :
    avΩ c (fun ω ↦ qStrongUnforgeableAdvantage (F.at (enc ω) (algΩ c optRand₀ pkSeedDist₀ ω))) ≤
      closedBound128s q qs :=
  (slhdsa_sha2_128s_pure_bytes_suf_cma_qrom_of_bridges c optRand₀ pkSeedDist₀ enc F q qs _
    hq hqs hcap hB).trans (composedBoundFinal_open_le q qs)

/-- **EUF-CMA, closed form at the open counts of the reduction.** -/
theorem slhdsa_sha2_128s_pure_bytes_euf_cma_qrom_closed
    (enc : Ω128 c → X → Y) (F : PortForger X Y E) (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q)
    (hqs : ∀ pk, CountBound isSign (F.main pk) qs)
    (hcap : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk))
    (hB : (∀ pk, CountBound isPort (F.main pk) q) → (∀ pk, CountBound isSign (F.main pk) qs) →
      (∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) →
      BridgesEuf c (optRandOf c optRand₀) (fun _ ↦ pkSeedDist₀)
        (internalΩ c optRand₀ pkSeedDist₀ enc F) q qs (openCounts128s qs)) :
    avΩ c (fun ω ↦ qUnforgeableAdvantage (F.at (enc ω) (algΩ c optRand₀ pkSeedDist₀ ω))) ≤
      closedBound128s q qs :=
  (slhdsa_sha2_128s_pure_bytes_euf_cma_qrom_of_bridges c optRand₀ pkSeedDist₀ enc F q qs _
    hq hqs hcap hB).trans (composedBoundFinal_open_le q qs)

end port

end Reduction

#print axioms Reduction.MixLE.le
#print axioms Reduction.MixPair.le
#print axioms Reduction.PrfValue.le
#print axioms Reduction.ItsrValue.le
#print axioms Reduction.DsprValue.le
#print axioms Reduction.TcrFvValue.le
#print axioms Reduction.TcrValue.le
#print axioms Reduction.UdValue.le
#print axioms Reduction.PreValue.le
#print axioms Reduction.composed_of_linear_eps
#print axioms Reduction.composed_of_bridges
#print axioms Reduction.slhdsa_sha2_128s_pure_bytes_suf_cma_qrom_of_bridges
#print axioms Reduction.slhdsa_sha2_128s_pure_bytes_euf_cma_qrom_of_bridges
#print axioms Reduction.composedBoundFinal_open_le
#print axioms Reduction.slhdsa_sha2_128s_pure_bytes_suf_cma_qrom_closed
#print axioms Reduction.slhdsa_sha2_128s_pure_bytes_euf_cma_qrom_closed
#print axioms Reduction.PrfValue.ofPort
