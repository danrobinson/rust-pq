import PQ.QROM.ExactPrf
import PQ.QROM.ExactTcr
import PQ.QROM.NonVacuity

/-!
# Non-vacuity of the exact two-phase / interactive games: positive values

`PQ/QROM/ExactNonVacuity.lean` computes an exact experiment that is `0`.  Here two exact
experiments are computed on toy instances where the adversary succeeds:

* **Exact PRF game** (`prfExactToy_real`, `prfExactToy_ideal`, `prfExactToy_advantage`): with a
  single key (`K = Unit`, `Dm = Unit`, `Y = Fin 2`) the adversary "request the PRF value `y`,
  query `F` at the only key, output `y = F (k, d)`" (one classical request, one query to `F`)
  has `prfExactReal = 1` and `prfExactIdeal = 1/2`: the experiments of `PQ/QROM/ExactPrf.lean`
  are distinguishable, with advantage exactly `1/2`, when the key space is trivial.  The bound
  `4 q / √|K| = 4` is consistent (and vacuous, as it must be for `|K| = 1`).
* **Exact SM-DT-TCR game** (`exactPrfNV_tcrExp_toy`): with `|Y| = 1` every pair collides; the
  adversary that requests the target `(t, false)` and outputs `(0, true)` wins `tcrExp` with
  probability exactly `1`.  So `tcrExp` is not identically small: the winning condition can be
  met through the game's record.

Both adversaries are classical strategies (the PRF one embedded via `OracleComp.toQuantum`);
they show that the experiments are not vacuous, not that there is a quantum attack.
-/

open MeasureTheory ENNReal Quantum Matrix OracleSpec
open scoped Kronecker ComplexOrder

universe u v w

namespace PQ.QROM

/-! ## Recording the challenger state does not change probabilities -/

section Stop

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
  {L : LocalSig.{u, v}} {Out : QReg → Type w} {A : QReg} {St : Type}

/-- Stopping with the output and a recorded state `s`: the probability of an event of
`(output, s)` is the probability of the corresponding event of the output. -/
theorem prfExact_qprob_bind_stop (I : L.Interp) (H : X → Y)
    (c : QuantumComp L (qromSpec X Y) Out A) (ρ : SubState A) (s : St)
    (E : (Σ u, Out u × St) → Prop) :
    qprob I H (QuantumComp.bind (X := Out) c fun u o ↦
        IAdv.stop (L := L) (spec := qromSpec X Y) u o s) ρ E =
      qprob I H c ρ fun p ↦ E ⟨p.1, (p.2, s)⟩ := by
  unfold qprob
  rw [evalDistMap_eq_leafProb, evalDistMap_eq_leafProb,
    leafProb_bind (σ := ρ.matrix ⊗ₖ (additiveOracleRuntime H).init.matrix) _ _
      (ρ.prod (additiveOracleRuntime H).init).posSemidef]
  unfold IAdv.stop
  simp only [leafProb_pure]
  rfl

end Stop

/-! ## The exact PRF game on a single key -/

section PrfToy

/-- After the classical request returned `y`: query `F` at the only point and compare. -/
def prfExactToyCont (y : Fin 2) : OracleComp ((Unit × Unit) →ₒ Fin 2) Bool := do
  let z ← liftM (((Unit × Unit) →ₒ Fin 2).query ((), ()))
  pure (decide (z = y))

theorem prfExactToyCont_bound (y : Fin 2) :
    OracleComp.IsTotalQueryBound (prfExactToyCont y) 1 := by
  rw [prfExactToyCont, OracleComp.isTotalQueryBound_query_bind_iff]
  exact ⟨Nat.one_pos, fun _ ↦ trivial⟩

/-- The toy distinguisher: one classical request `d = ()`, then one query to `F`. -/
noncomputable def prfExactToyAdv :
    IAdv LocalSig.instruments.{0} (qromSpec (Unit × Unit) (Fin 2)) Unit (Fin 2)
      (QuantumComp₂.Leaf (QReg.of Unit) Bool) 1 (QReg.of Unit) :=
  QuantumComp.pure (L := LocalSig.instruments.{0}) (spec := qromSpec (Unit × Unit) (Fin 2))
    (X := fun u ↦ QuantumComp₂.Leaf (QReg.of Unit) Bool u ⊕
      (Unit × (Fin 2 → IAdv LocalSig.instruments.{0} (qromSpec (Unit × Unit) (Fin 2)) Unit (Fin 2)
        (QuantumComp₂.Leaf (QReg.of Unit) Bool) 0 u)))
    (Sum.inr ((), fun y ↦ (prfExactToyCont y).toQuantum))

/-- The event "the output bit is `true`". -/
def prfExactToyEvent (p : Σ u, QuantumComp₂.Leaf (QReg.of Unit) Bool u × Unit) : Prop :=
  p.2.1.2 = true

/-- The toy distinguisher makes at most one quantum query, whatever the answers. -/
theorem prfExactToyAdv_bound : IAdv.IsQueryBound 1 prfExactToyAdv fun _ ↦ 1 := by
  intro St ch s
  have h := (OracleComp.isQueryBound_toQuantum (prfExactToyCont_bound (ch () s).1)).bind
    (b₂ := 0) fun u (o : QuantumComp₂.Leaf (QReg.of Unit) Bool u) ↦
      QuantumComp.isQueryBound_pure (L := LocalSig.instruments.{0})
        (spec := qromSpec (Unit × Unit) (Fin 2))
        (X := fun u ↦ QuantumComp₂.Leaf (QReg.of Unit) Bool u × St) (A := u) (o, (ch () s).2) 0
  rw [add_zero] at h
  exact h

/-- Against the answer function `f` and the oracle `F`, the toy distinguisher outputs `true`
iff `F ((), ()) = f ()`. -/
theorem prfExactToy_qprob (F : Unit × Unit → Fin 2) (f : Unit → Fin 2) :
    qprob .instruments F (prfExactProg 1 prfExactToyAdv f) (SubState.basis ())
        prfExactToyEvent = if F ((), ()) = f () then 1 else 0 := by
  have h := prfExact_qprob_bind_stop .instruments F (prfExactToyCont (f ())).toQuantum
    (SubState.basis ()) () prfExactToyEvent
  refine h.trans ?_
  refine (NonVacuity.qprob_toQuantum F (prfExactToyCont (f ())) fun b ↦ b = true).trans ?_
  change (if decide (F ((), ()) = f ()) = true then (1 : ℝ≥0∞) else 0) = _
  by_cases h : F ((), ()) = f () <;> simp [h]

/-- A sum over the functions on a one-element type. -/
theorem prfExact_sum_fun_unique {α β M : Type} [Unique α] [Fintype α] [Fintype β]
    [DecidableEq α] [AddCommMonoid M] (g : (α → β) → M) : ∑ f : α → β, g f = ∑ b, g fun _ ↦ b :=
  ((Equiv.funUnique α β).symm.sum_comp g).symm

/-- The pair of trivial registers has one element. -/
local instance prfExactUniqueUnitProd : Unique (Unit × Unit) := ⟨⟨((), ())⟩, fun _ ↦ rfl⟩

/-- **The real experiment** of the toy distinguisher has value `1`. -/
theorem prfExactToy_real :
    prfExactReal .instruments (SubState.basis ()) 1 prfExactToyAdv prfExactToyEvent = 1 := by
  unfold prfExactReal
  refine (Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun F _ ↦
    congrArg _ (prfExactToy_qprob F fun d ↦ F (k, d))).trans ?_
  simp only [ite_true, mul_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have h1 : (Fintype.card (Unit × Unit → Fin 2) : ℝ≥0∞) = 2 := by simp
  rw [h1, Fintype.card_unit, Nat.cast_one, one_mul, inv_one, one_mul,
    ENNReal.mul_inv_cancel (by simp) (by simp)]

/-- **The ideal experiment** of the toy distinguisher has value `1/2`. -/
theorem prfExactToy_ideal :
    prfExactIdeal .instruments (SubState.basis ()) 1 prfExactToyAdv prfExactToyEvent = 1 / 2 := by
  unfold prfExactIdeal
  refine (Finset.sum_congr rfl fun F _ ↦ Finset.sum_congr rfl fun R _ ↦
    congrArg _ (prfExactToy_qprob F R)).trans ?_
  rw [prfExact_sum_fun_unique]
  simp only [prfExact_sum_fun_unique, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have h1 : (Fintype.card (Unit × Unit → Fin 2) : ℝ≥0∞) = 2 := by simp
  have h2 : (Fintype.card (Unit → Fin 2) : ℝ≥0∞) = 2 := by simp
  rw [h1, h2, Fintype.card_fin, Nat.cast_ofNat, ← mul_assoc, ENNReal.mul_inv_cancel (by simp)
    (by simp), one_mul, one_div]

/-- **A distinguisher with positive advantage.**  On the single-key instance the exact PRF
experiments differ by exactly `1/2`. -/
theorem prfExactToy_advantage :
    |(prfExactReal .instruments (SubState.basis ()) 1 prfExactToyAdv prfExactToyEvent).toReal -
      (prfExactIdeal .instruments (SubState.basis ()) 1 prfExactToyAdv prfExactToyEvent).toReal| =
      1 / 2 := by
  rw [prfExactToy_real, prfExactToy_ideal]
  norm_num

/-- Consistency with `prfExact_abs_sub_le` at `q = 1`, `|K| = 1`: `1/2 ≤ 4`. -/
example : (1 / 2 : ℝ) ≤ 4 * ((1 : ℕ) : ℝ) / Real.sqrt (Fintype.card Unit) := by
  rw [← prfExactToy_advantage]
  exact prfExact_abs_sub_le .instruments (SubState.basis ()) prfExactToyAdv prfExactToyAdv_bound
    prfExactToyEvent

end PrfToy

/-! ## The exact SM-DT-TCR game with a one-element range -/

section TcrToy

/-- The toy TCR adversary, phase 1: one classical request, the target `((), false)`; no quantum
query; output `()`. -/
noncomputable def exactPrfNV_tcrAdv :
    IAdv LocalSig.instruments.{0} (qrom2Spec (Dom Unit Unit Bool) Unit)
      ((Unit × Bool) ⊕ (Unit × Bool)) (Option Unit) (fun _ ↦ Unit) 1 (QReg.of Unit) :=
  QuantumComp.pure (L := LocalSig.instruments.{0}) (spec := qrom2Spec (Dom Unit Unit Bool) Unit)
    (X := fun u ↦ Unit ⊕ (((Unit × Bool) ⊕ (Unit × Bool)) × (Option Unit →
      IAdv LocalSig.instruments.{0} (qrom2Spec (Dom Unit Unit Bool) Unit)
        ((Unit × Bool) ⊕ (Unit × Bool)) (Option Unit) (fun _ ↦ Unit) 0 u)))
    (Sum.inr (Sum.inl ((), false), fun _ ↦ QuantumComp.pure ()))

/-- The toy TCR adversary, phase 2: no quantum query; name target `0` and the message `true`. -/
noncomputable def exactPrfNV_tcrPh2 (_ : Unit) (u : QReg) (_ : Unit) :
    QuantumComp LocalSig.instruments.{0} (qrom2Spec (Dom Unit Unit Bool) Unit)
      (fun _ ↦ ℕ × Bool) u :=
  QuantumComp.pure (0, true)

/-- **A positive value of the exact SM-DT-TCR experiment.**  With a one-element range every pair
of messages collides: the adversary that requests the target `(t, false)` and then outputs
`(0, true)` wins `tcrExp` (cap `1`) with probability exactly `1`. -/
theorem exactPrfNV_tcrExp_toy :
    tcrExp (Sd := Unit) (Tw := Unit) (Msg := Bool) (Y := Unit) .instruments (SubState.basis ()) 1 1
      exactPrfNV_tcrAdv exactPrfNV_tcrPh2 = 1 := by
  have hreal : ∀ (P : Unit) (Th : Dom Unit Unit Bool → Unit),
      realProb (Sd := Unit) (Tw := Unit) (Msg := Bool) (Y := Unit) .instruments
        (SubState.basis ()) (tcrCh 1) tcrInit 1 exactPrfNV_tcrAdv exactPrfNV_tcrPh2 tcrWin P Th =
        1 := fun P Th ↦ by
    unfold realProb
    have hc : composite (tcrCh 1 (rowOf Th P)) tcrInit 1 exactPrfNV_tcrAdv exactPrfNV_tcrPh2 P =
        QuantumComp.pure ((0, true),
          (tcrCh 1 (rowOf Th P) (Sum.inl ((), false)) tcrInit).2) := rfl
    rw [hc, leafProb_pure, ind_of_true]
    · simp [joint, SubState.matrix_basis, Matrix.single_kronecker_single, Matrix.trace_single_eq_same]
    · refine ⟨(), false, ?_, Bool.noConfusion, Subsingleton.elim _ _⟩
      simp [tcrCh, tcrInit]
  unfold tcrExp twoPhaseExp
  rw [avg_congr fun P ↦ avg_congr fun Th ↦ hreal P Th]
  unfold avg
  simp only [mul_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [card_mul_inv_cancel, mul_one, card_mul_inv_cancel]

end TcrToy

end PQ.QROM

#print axioms PQ.QROM.prfExact_qprob_bind_stop
#print axioms PQ.QROM.prfExactToyAdv_bound
#print axioms PQ.QROM.prfExactToy_qprob
#print axioms PQ.QROM.prfExactToy_real
#print axioms PQ.QROM.prfExactToy_ideal
#print axioms PQ.QROM.prfExactToy_advantage
#print axioms PQ.QROM.exactPrfNV_tcrExp_toy
