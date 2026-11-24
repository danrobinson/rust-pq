import Integration.SlhDsaShakePermutationWotsUdGame
import Integration.SlhDsaShakePermutationWotsChoice

namespace Reduction.ShakePermutation.SparsePort.Wots.Ud
open Classical MLink SLHDSA SLHDSA.Security OracleComp OracleSpec PQ.Interactive PQ.QROM Quantum ENNReal TweakableHash SetOracle Resources2 ShakeApi
open scoped ComplexOrder
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option allowUnsafeReducibility true in
attribute [local reducible] ShakeSecurity.primitives
attribute [local irreducible] wotsChainTargets wotsStepTargetsT Open.udPhase1
variable (S : Sha2Set) (rand : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node)
    {E : Type} [Fintype E] [DecidableEq E] (F : PortForger Port Words E)
local notation "N" => ShakeApi.rawCap S 67 65536
local notation "T₀" => (fun _ : ShakeApi.Input N => (default : Bytes S.vp.params.m))
local notation "P₀" => ShakeApi.primitives S (ShakeApi.extend T₀)
local notation "raw" => fun π : Permutation => ShakeApi.primitives S (ShakeApi.extend (SkCost.table S N (oracle π)))
local notation "B" => fun π : Permutation => qPureBytesToInternal (SkCost.capped S rand seeds F N π)
local notation "Work" => WS Port Words E

def selection : QSM_DT_UD_Adversary Work (ShakeXof.baseUd S seeds) where
  State := Open.RState S.vp P₀
  pick := Open.udPhase1 (vp:=S.vp) (prims:=P₀) seeds
  distinguish := fun _ _ => pure default
  ρ₀ := F.ρ₀
  posSemidef := F.posSemidef
  trace_eq_one := F.trace_eq_one
local notation "A" => selection S seeds F

def distMachine (H : Port → Words) (st : (A).State) (pk : S.Node) : Closed Work Bool :=
  (qrUd (qPureBytesToInternal (ShakeApi.forgerAt S rand seeds F (ShakeApi.extend (SkCost.table S N H)) H))).distinguish st pk
local notation "M" => distMachine S rand seeds F

private theorem distMachine_pue (st : (A).State) (pk : S.Node) (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hs : ∀ pk, CountBound isSign (F.main pk) qs) :
    PUE (spec:=unifSpec) (E:=E) cnt0 (fun H => M H st pk) (q+483*qmWotsUdHashes S.vp qs) := by
  obtain ⟨mach,cost,eq⟩ := wotsUd_mach_exists S N rand seeds F T₀ le_rfl st pk q qs hq hs
  exact (funext eq) ▸ cost

private theorem native_eq (π : Permutation) (world : SM_DT_UD_World) (pk : S.Node) :
    udInner world (qrUd (B π)) pk = udInner world (adversary S seeds A M π) pk := by
  let op := (raw π).Thash
  let G (f : S.Node → Bytes 32 → List S.Node → S.Node) := udWithEval (ShakeXof.baseUd S seeds)
    (fun p d m => f p d [m]) (fun _ p d xs => f p d xs)
  let score (f : S.Node → Bytes 32 → List S.Node → S.Node) := udInner world
    (⟨(A).State,(A).pick,M (oracle π),F.ρ₀,F.posSemidef,F.trace_eq_one⟩ : QSM_DT_UD_Adversary Work (G f)) pk
  let hf : Open.HashFns P₀ := ⟨(raw π).Thash,(raw π).Hmsg,(raw π).PRF,(raw π).PRFmsg⟩
  have ch : (qrUd (B π)).pick = (A).pick := by
    kexact Open.wotsUd_phase1_q1_zero (prims:=P₀) (pkSeedDist:=seeds) hf (B π).toClassical
  have same : udInner world (qrUd (B π)) pk = score op := by
    kexact congrArg (fun c => udInner world (⟨(A).State,c,M (oracle π),F.ρ₀,F.posSemidef,F.trace_eq_one⟩ :
      QSM_DT_UD_Adversary Work (G op)) pk) ch
  have eval : Wots.value S (fun _ => π) = op := funext fun pk => funext fun d => funext (value_real S π pk d)
  exact same.trans (congrArg score eval.symm)

theorem numeric (q Q : ℕ) (hq : q ≤ 2^41) (hQ : Q ≤ 2^100) : loss S q Q ≤ ((2:ℝ≥0∞)^35)⁻¹ := by
  have d : 2^128 ≤ Fintype.card S.Node := by change _ ≤ Fintype.card (Bytes _); rw [card_bytes']; cases S <;> decide +kernel
  have hr : randomLoss S q ≤ ENNReal.ofReal (8*(12*(2^41:ℝ))^2/2^128) := by
    apply ENNReal.ofReal_le_ofReal
    push_cast
    gcongr
    · exact_mod_cast hq
    · exact_mod_cast d
  have hp : penalty S Q ≤ ((2:ℝ≥0∞)^38)⁻¹ := by
    apply le_trans _ (ArityGame.benchmark_loss S 1 (by decide) q Q hq hQ)
    unfold penalty ArityGame.loss switchLoss
    apply add_le_add _ le_rfl
    apply le_trans _ le_add_self
    apply add_le_add le_rfl (mul_le_mul' le_rfl (ENNReal.div_le_div _ le_rfl))
    exact Nat.cast_le.mpr (Fintype.card_le_of_embedding (asArity S))
  apply (add_le_add hr (add_le_add hp hp)).trans
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp (disch := first | finiteness | positivity) only [ENNReal.toReal_add,ENNReal.toReal_ofReal,ENNReal.toReal_inv,
    ENNReal.toReal_pow,ENNReal.toReal_ofNat]
  norm_num

theorem signature_ud (hq : ∀ pk, CountBound isPort (F.main pk) (2^40)) (hs : ∀ pk, CountBound isSign (F.main pk) 1) :
    uniformMean (fun π => qSM_DT_UD_RealSuccess (qrUd (B π))) ≤
    uniformMean (fun π => qSM_DT_UD_IdealSuccess (qrUd (B π))) + ((2:ℝ≥0∞)^35)⁻¹ := by
  let q := 2^40+483*qmWotsUdHashes S.vp 1
  let win := fun (w : SM_DT_UD_World) (π : Permutation) pk => udInner w (qrUd (B π)) pk
  let eps : ℝ≥0∞ := ((2:ℝ≥0∞)^35)⁻¹
  have per (pk : S.Node) : uniformMean (fun π => win .real π pk) ≤ uniformMean (fun π => win .ideal π pk) + eps := by
    unfold win; simp_rw [native_eq S rand seeds F]
    apply (fixed S seeds A M pk q (2^100) (fun st => distMachine_pue S rand seeds F st pk _ _ hq hs) _).trans
    · exact add_le_add le_rfl (numeric S _ _ (by cases S <;> decide +kernel) le_rfl)
    · intro w
      apply (countBound_iff_wCount _ _ _).2
      exact ((countBound_iff_wCount _ _ _).1 (prog_cost S w pk _ ([],[]) _ (ud_choice_cost S (ShakeApi.extend T₀) seeds))).mono (calls_budget S)
  simp only [qSM_DT_UD_RealSuccess_eq_tsum,qSM_DT_UD_IdealSuccess_eq_tsum]
  change uniformMean (fun π => ∑' pk, PQ.Interactive.prob seeds (· = pk) * win .real π pk) ≤
    uniformMean (fun π => ∑' pk, PQ.Interactive.prob seeds (· = pk) * win .ideal π pk) + eps
  rw [ShakeXof.mean_seed,ShakeXof.mean_seed]
  calc _ ≤ ∑' pk, PQ.Interactive.prob seeds (· = pk) * (uniformMean (fun π => win .ideal π pk) + eps) :=
          tsum_le_tsum fun pk => mul_le_mul' le_rfl (per pk)
       _ = _ + (∑' pk, PQ.Interactive.prob seeds (· = pk)) * eps := by
          simp only [mul_add]; rw [tsum_add,ENNReal.tsum_mul_right]
       _ ≤ _ := add_le_add le_rfl ((mul_le_mul' (tsum_prob_eq_le_one seeds) le_rfl).trans (one_mul _).le)

end
end Reduction.ShakePermutation.SparsePort.Wots.Ud
#print axioms Reduction.ShakePermutation.SparsePort.Wots.Ud.signature_ud
