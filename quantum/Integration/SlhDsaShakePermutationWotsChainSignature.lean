import Integration.SlhDsaShakePermutationWotsChainGame
import Integration.SlhDsaShakePermutationWotsChoice

namespace Reduction.ShakePermutation.SparsePort.Wots.Chain
open Classical MLink SLHDSA SLHDSA.Security OracleComp OracleSpec PQ.Interactive PQ.QROM Quantum ENNReal TweakableHash SetOracle Resources2 ShakeApi
open scoped ComplexOrder
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option allowUnsafeReducibility true in
attribute [local reducible] ShakeSecurity.primitives
attribute [local irreducible] wotsChainTargets wotsStepTargetsT Open.wotsTcrPhase1
variable (S : Sha2Set) (rand : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node)
    {E : Type} [Fintype E] [DecidableEq E] (F : PortForger Port Words E)
local notation "N" => ShakeApi.rawCap S 67 65536
local notation "T₀" => (fun _ : ShakeApi.Input N => (default : Bytes S.vp.params.m))
local notation "P₀" => ShakeApi.primitives S (ShakeApi.extend T₀)
local notation "raw" => fun π : Permutation => ShakeApi.primitives S (ShakeApi.extend (SkCost.table S N (oracle π)))
local notation "B" => fun π : Permutation => qPureBytesToInternal (SkCost.capped S rand seeds F N π)
local notation "Work" => WS Port Words E

def selection : QSM_DT_TCR_Adversary Work (ShakeXof.baseWotsTcr S seeds) where
  State := Open.RState S.vp P₀
  choose := Open.wotsTcrPhase1 (vp:=S.vp) (prims:=P₀) seeds
  forge := fun _ _ => pure default
  ρ₀ := F.ρ₀
  posSemidef := F.posSemidef
  trace_eq_one := F.trace_eq_one
local notation "A" => selection S seeds F

def forgeMachine (H : Port → Words) (st : (A).State) (pk : S.Node) : Closed Work (ℕ × S.Node) :=
  (qrTcrT (qPureBytesToInternal (ShakeApi.forgerAt S rand seeds F (ShakeApi.extend (SkCost.table S N H)) H))).forge st pk
local notation "M" => forgeMachine S rand seeds F

private theorem forgeMachine_pue (st : (A).State) (pk : S.Node) (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hs : ∀ pk, CountBound isSign (F.main pk) qs) :
    PUE (spec:=unifSpec) (E:=E) cnt0 (fun H => M H st pk) (q+483*qmWotsTcrTHashes S.vp qs) := by
  obtain ⟨mach,cost,eq⟩ := wotsTcrT_mach_exists S N rand seeds F T₀ le_rfl st pk q qs hq hs
  exact (funext eq) ▸ cost

private theorem native_eq (π : Permutation) :
    qSM_DT_TCR_Advantage (qrTcrT (B π)) = qSM_DT_TCR_Advantage (adversary S seeds A M π) := by
  let op := (raw π).Thash
  let G (f : S.Node → Bytes 32 → List S.Node → S.Node) := tcrWithEval (ShakeXof.baseWotsTcr S seeds)
    (fun p d m => f p d [m]) (fun _ p d xs => f p d xs)
  let score (f : S.Node → Bytes 32 → List S.Node → S.Node) := qSM_DT_TCR_Advantage
    (⟨(A).State,(A).choose,M (oracle π),F.ρ₀,F.posSemidef,F.trace_eq_one⟩ : QSM_DT_TCR_Adversary Work (G f))
  let hf : Open.HashFns P₀ := ⟨(raw π).Thash,(raw π).Hmsg,(raw π).PRF,(raw π).PRFmsg⟩
  have ch : (qrTcrT (B π)).choose = (A).choose := by
    kexact Open.wotsTcrT_phase1_q1_zero (prims:=P₀) (pkSeedDist:=seeds) hf (B π).toClassical
  have same : qSM_DT_TCR_Advantage (qrTcrT (B π)) = score op := by
    kexact congrArg (fun c => qSM_DT_TCR_Advantage (⟨(A).State,c,M (oracle π),F.ρ₀,F.posSemidef,F.trace_eq_one⟩ :
      QSM_DT_TCR_Adversary Work (G op))) ch
  have eval : Wots.value S (fun _ => π) = op := funext fun pk => funext fun d => funext (value_real S π pk d)
  exact same.trans (congrArg score eval.symm)

theorem numeric (q Q : ℕ) (hq : q ≤ 2^41) (hQ : Q ≤ 2^100) : loss S q Q ≤ ((2:ℝ≥0∞)^38)⁻¹ := by
  apply le_trans _ (ArityGame.benchmark_loss S 1 (by decide) q Q hq hQ)
  have count : Fintype.card (Row S) ≤ Fintype.card (Arity.Row S 1) := Fintype.card_le_of_embedding (asArity S)
  exact add_le_add (add_le_add le_rfl (add_le_add le_rfl (mul_le_mul' le_rfl (ENNReal.div_le_div (Nat.cast_le.mpr count) le_rfl)))) le_rfl

/-- The actual WOTS chain target collision term of the linear signature inequality. -/
theorem signature_chain (hq : ∀ pk, CountBound isPort (F.main pk) (2^40))
    (hs : ∀ pk, CountBound isSign (F.main pk) 1) :
    uniformMean (fun π => qSM_DT_TCR_Advantage (qrTcrT (B π))) ≤ ((2:ℝ≥0∞)^38)⁻¹ := by
  simp_rw [native_eq S rand seeds F]
  apply (bound S seeds A M (2^40+483*qmWotsTcrTHashes S.vp 1) (2^100)
    (fun st pk => forgeMachine_pue S rand seeds F st pk _ _ hq hs) _).trans
  · exact numeric S _ _ (by cases S <;> decide +kernel) le_rfl
  · intro pk
    apply (countBound_iff_wCount _ _ _).2
    exact ((countBound_iff_wCount _ _ _).1 (prog_cost S pk _ ([],[]) _ (chain_choice_cost S (ShakeApi.extend T₀) seeds))).mono (calls_budget S)
end
end Reduction.ShakePermutation.SparsePort.Wots.Chain
#print axioms Reduction.ShakePermutation.SparsePort.Wots.Chain.signature_chain
