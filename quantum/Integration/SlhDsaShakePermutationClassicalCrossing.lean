import Integration.SlhDsaShakePermutationClassicalCoverage
import Integration.SlhDsaShakePermutationClassicalAverage

/-! Classical SHAKE indifferentiability for bounded adaptive byte queries
and a public forward/inverse permutation. Only public queries are visible
to the simulator. Every padded block of a private query is charged. -/
namespace Reduction.ShakePermutation.Classic
open Classical OracleSpec OracleComp PQ.Interactive MLink SLHDSA
open SetOracle (uniformMean)
open scoped ENNReal
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000

abbrev charge (S : Sha2Set) (N : ℕ) : (Outer S N).Domain → ℕ :=
  Sum.elim (fun _ => 0) (cost (S := S) (N := N))

def hiddenLoss (q : ℕ) : ℝ≥0∞ := ((q*(2*q+2)+q^2 : ℕ) : ℝ≥0∞) / Fintype.card Capacity
def classicalLoss (q : ℕ) : ℝ≥0∞ := q*capLoss q + hiddenLoss q

private theorem fixed_survival (S : Sha2Set) (N T : ℕ) (cap : Completion.blockCap N ≤ T) {Z : Type}
    (P : OracleComp (Outer S N) Z) (q : ℕ) (budget : WCount (charge S N) P q) (limit : q ≤ T) (rates : Row T → Rate) :
    1 ≤ uniformMean (fun g : Row T → Capacity =>
      guarded (fun j => join (rates j) (g j)) (fun _ => 1) (driver S N T P []) (fun _ => none) []) + classicalLoss q := by
  let coin := resolve P
  let make (g : Row T → Capacity) (j : Row T) := join (rates j) (g j)
  let raw := fun x : ShakeApi.Input N => ShakeXof.head (output_sizes S).2 (Completion.bytes (rates (.inl (Completion.address cap x))))
  have same (g : Row T → Capacity) : rawOf S cap (make g) = raw := by funext x; simp [rawOf,make,raw]
  let final (g : Row T → Capacity) (c : coin.Coins) := (report S N T (make g) raw (coin.run c) (emptyReport T)).2
  let keep (g : Row T → Capacity) (c : coin.Coins) :=
    detRun (fullStep S N T (make g) raw) (fun _ s => hit s.2.isSome) (coin.run c) (emptyReport T,some (start _ _))
  let pub (g : Row T → Capacity) (c : coin.Coins) := hit ((final g c).clean = false)
  let hid (g : Row T → Capacity) (c : coin.Coins) := hit (leaked (hidden (final g c)) (denied (final g c)) g)
  let kept (g : Row T → Capacity) := guarded (make g) (fun _ => 1) (driver S N T P []) (fun _ => none) []
  let bad (g : Row T → Capacity) := publicBad S N T rates g raw P []
  have hk (g) : uniformMean (keep g) = kept g := by
    have lift := coin.correct _ (fullStep S N T (make g) raw) (fun _ s => hit s.2.isSome) (emptyReport T,some (start _ _))
    have check := inspect_driver S N T cap (make g) (fun _ s => hit s.isSome) P (emptyReport T) (some (start _ _))
    rw [same] at check
    exact lift.symm.trans (check.symm.trans (inspect_guarded (make g) (fun _ => 1) _ (start _ _) (by simp [coherent,start])))
  have hp (g) : uniformMean (pub g) = bad g := by
    have obs := report_eval S N T (Z := Z) (make g) raw (fun _ s => hit (s.clean=false))
    have lift := coin.correct _ (reportStep S N T (make g) raw) (fun _ s => hit (s.clean=false)) (emptyReport T)
    refine (congrArg uniformMean (funext fun c => (obs (coin.run c) _).symm)).trans (lift.symm.trans ?_)
    exact report_publicBad S N T rates g raw P _ rfl
  have h := mean_coverage keep pub hid kept bad (hiddenLoss q) (fun g c => by
    simpa only [keep,pub,hid,final,make,cap_join] using det_covered S N T cap (make g) raw (coin.run c) q
      (resolved_count P _ q budget c) limit) hk hp (fun c => report_hidden S N T rates raw (coin.run c) q (resolved_count P _ q budget c))
  have cb : CountBound (fun i => publicIdx (S := S) (N := N) i = true) P q := by
    apply (countBound_iff_wCount _ _ _).2 (WCount.wmono _ budget)
    rintro (n|p|h) <;> simp [publicIdx,charge,cost]
  have bound := public_risk S N T rates raw P q cb limit
  exact h.trans ((add_le_add (add_le_add le_rfl bound) le_rfl).trans_eq (add_assoc ..))

def wordBanks (T : ℕ) : ((Row T → Rate) × (Row T → Capacity)) ≃ (Row T → Words) where
  toFun z := fun j => join (z.1 j) (z.2 j)
  invFun H := (fun j => rateOf (H j),fun j => capOf (H j))
  left_inv z := by rcases z with ⟨a,b⟩; simp
  right_inv H := by funext j; simp

private theorem decompose {A B C : Type} [Fintype A] [Fintype B] [Fintype C] (e : A × B ≃ C) (f : C → ℝ≥0∞) :
    uniformMean f = uniformMean (fun a => uniformMean (fun b => f (e (a,b)))) :=
  (mean_equiv e f).symm.trans (avg_prod _)

theorem classical_crossing (S : Sha2Set) (N T : ℕ) (cap : Completion.blockCap N ≤ T)
    (P : OracleComp (Outer S N) Bool) (q : ℕ) (budget : WCount (charge S N) P q) (limit : q ≤ T) :
    uniformMean (fun π : Permutation => realOuter S N π (fun v => hit (v=true)) P) ≤
      uniformMean (fun g : Completion.Private T => uniformMean (fun raw : ShakeApi.RawTable S N =>
        uniformMean (fun k : Fix.Domain T → Capacity => uniformMean (fun u : Port → Words =>
          idealOuter S N T (banks T (Completion.complete S cap g raw) k u) raw (fun v => hit (v=true)) P [])))) +
      classicalLoss q := by
  let tested := driver S N T P []
  let keep (H : Row T → Words) := guarded H (fun _ => 1) tested (fun _ => none) []
  have cov : 1 ≤ uniformMean keep + classicalLoss q := by
    calc
      1 = uniformMean (fun _ : Row T → Rate => 1) := (avg_const _).symm
      _ ≤ uniformMean (fun r : Row T → Rate => uniformMean (fun g : Row T → Capacity =>
        keep (fun j => join (r j) (g j))) + classicalLoss q) :=
        mean_mono (fixed_survival S N T cap P q budget limit)
      _ = _ := (mean_add _ _).trans (congrArg₂ (·+·) (decompose (wordBanks T) keep).symm (avg_const _))
  have le := compare_acceptance tested (classicalLoss q) cov
  have real (π : Permutation) : eager π (fun v => hit (v=true)) (simulateQ forgetTag tested) =
      realOuter S N π (fun v => hit (v=true)) P :=
    (labelled_forget π _ tested).trans (driver_real S N T π _ P [] (by simp [Respects]))
  exact (congrArg uniformMean (funext real)).symm.le.trans (le.trans_eq
    (congrArg (· + classicalLoss q) (ideal_completion S N T cap _ P)))

set_option exponentiation.threshold 2048 in
theorem loss_benchmark : classicalLoss (2^41) ≤ (2^427 : ℝ≥0∞)⁻¹ := by
  have cap : Fintype.card Capacity = 2^512 := by
    change Fintype.card (Fin 8 → UInt64) = _
    rw [Fintype.card_fun,Fintype.card_fin,← FinEnum.card_eq_fintypeCard,FinEnum.card_UInt64]
    decide +kernel
  unfold classicalLoss capLoss hiddenLoss
  rw [cap]
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).1
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  simp only [ENNReal.toReal_mul,ENNReal.toReal_div,ENNReal.toReal_inv,ENNReal.toReal_natCast,ENNReal.toReal_pow,ENNReal.toReal_ofNat]
  norm_num

end
end Reduction.ShakePermutation.Classic
#print axioms Reduction.ShakePermutation.Classic.classical_crossing
#print axioms Reduction.ShakePermutation.Classic.loss_benchmark
