import Integration.SlhDsaShakePermutationWotsPreGame
import Integration.SlhDsaShakePermutationWotsChoice

namespace Reduction.ShakePermutation.SparsePort.Wots.Pre
open Classical MLink SLHDSA SLHDSA.Security OracleComp OracleSpec PQ.Interactive PQ.QROM Quantum ENNReal TweakableHash SetOracle Resources2 ShakeApi
open scoped ComplexOrder
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option allowUnsafeReducibility true in
attribute [local reducible] ShakeSecurity.primitives
attribute [local irreducible] wotsChainTargets wotsStepTargetsT Open.prePhase1
variable (S : Sha2Set) (rand : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node)
    {E : Type} [Fintype E] [DecidableEq E] (F : PortForger Port Words E)
local notation "N" => ShakeApi.rawCap S 67 65536
local notation "T₀" => (fun _ : ShakeApi.Input N => (default : Bytes S.vp.params.m))
local notation "P₀" => ShakeApi.primitives S (ShakeApi.extend T₀)
local notation "raw" => fun π : Permutation => ShakeApi.primitives S (ShakeApi.extend (SkCost.table S N (oracle π)))
local notation "B" => fun π : Permutation => qPureBytesToInternal (SkCost.capped S rand seeds F N π)
local notation "Work" => WS Port Words E

def selection : QSM_DT_PRE_Adversary Work (ShakeXof.basePre S seeds) where
  State := Open.RState S.vp P₀
  choose := Open.prePhase1 (vp:=S.vp) (prims:=P₀) seeds
  invert := fun _ _ => pure default
  ρ₀ := F.ρ₀
  posSemidef := F.posSemidef
  trace_eq_one := F.trace_eq_one
local notation "A" => selection S seeds F

def inverse (H : Port → Words) (st : (A).State) (pk : S.Node) : Closed Work (ℕ × S.Node) :=
  (qrPre (qPureBytesToInternal (ShakeApi.forgerAt S rand seeds F (ShakeApi.extend (SkCost.table S N H)) H))).invert st pk
local notation "M" => inverse S rand seeds F

private theorem inverse_pue (st : (A).State) (pk : S.Node) (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hs : ∀ pk, CountBound isSign (F.main pk) qs) :
    PUE (spec:=unifSpec) (E:=E) cnt0 (fun H => M H st pk) (q+483*qmWotsPreHashes S.vp qs) := by
  obtain ⟨mach,cost,eq⟩ := wotsPre_mach_exists S N rand seeds F T₀ le_rfl st pk q qs hq hs
  exact (funext eq) ▸ cost

private theorem native_eq (π : Permutation) :
    qSM_DT_PRE_Advantage (qrPre (B π)) = qSM_DT_PRE_Advantage (adversary S seeds A M π) := by
  let op := (raw π).Thash
  let G (f : S.Node → Bytes 32 → List S.Node → S.Node) := preWithEval (ShakeXof.basePre S seeds)
    (fun p d m => f p d [m]) (fun _ p d xs => f p d xs)
  let score (f : S.Node → Bytes 32 → List S.Node → S.Node) := qSM_DT_PRE_Advantage
    (⟨(A).State,(A).choose,M (oracle π),F.ρ₀,F.posSemidef,F.trace_eq_one⟩ : QSM_DT_PRE_Adversary Work (G f))
  let hf : Open.HashFns P₀ := ⟨(raw π).Thash,(raw π).Hmsg,(raw π).PRF,(raw π).PRFmsg⟩
  have ch : (qrPre (B π)).choose = (A).choose := by
    kexact Open.wotsPre_phase1_q1_zero (prims:=P₀) (pkSeedDist:=seeds) hf (B π).toClassical
  have same : qSM_DT_PRE_Advantage (qrPre (B π)) = score op := by
    kexact congrArg (fun c => qSM_DT_PRE_Advantage (⟨(A).State,c,M (oracle π),F.ρ₀,F.posSemidef,F.trace_eq_one⟩ :
      QSM_DT_PRE_Adversary Work (G op))) ch
  have eval : Wots.value S (fun _ => π) = op := funext fun pk => funext fun d => funext (value_real S π pk d)
  exact same.trans (congrArg score eval.symm)

theorem numeric (q Q : ℕ) (hq : q ≤ 2^41) (hQ : Q ≤ 2^100) : loss S q Q ≤ ((2:ℝ≥0∞)^37)⁻¹ := by
  let a := (2*((3*q:ℕ):ℝ≥0∞)+1)^2/Fintype.card S.Node
  let b := Q*Classic.forestPenalty Rate Words Q+Q*((Fintype.card (Arity.Row S 1):ℝ≥0∞)/Fintype.card Words)
  let c := ((2:ℝ≥0∞)^63)⁻¹+((2:ℝ≥0∞)^384)⁻¹
  have lim : (a+b)+c ≤ ((2:ℝ≥0∞)^38)⁻¹ := ArityGame.benchmark_loss S 1 (by decide) q Q hq hQ
  have small : a ≤ (a+b)+c := le_self_add.trans le_self_add
  have count : Fintype.card (Row S) ≤ Fintype.card (Arity.Row S 1) := Fintype.card_le_of_embedding (asArity S)
  have x : Q*Classic.forestPenalty Rate Words Q+Q*((Fintype.card (Row S):ℝ≥0∞)/Fintype.card Words) ≤ b :=
    add_le_add le_rfl (mul_le_mul' le_rfl (ENNReal.div_le_div (Nat.cast_le.mpr count) le_rfl))
  have ar : random_loss S q = a+a := by simp only [random_loss,a,mul_add,div_eq_mul_inv]
  calc
    loss S q Q ≤ (a+a+b)+c := by unfold loss; rw [ar]; exact add_le_add (add_le_add le_rfl x) le_rfl
    _ = a+((a+b)+c) := by simp only [add_assoc]
    _ ≤ ((2:ℝ≥0∞)^38)⁻¹ + ((2:ℝ≥0∞)^38)⁻¹ := add_le_add (small.trans lim) lim
    _ = _ := by
      apply ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness) |>.mp
      simp (disch := finiteness) only [ENNReal.toReal_add,ENNReal.toReal_inv,ENNReal.toReal_pow,ENNReal.toReal_ofNat]
      norm_num

/-- The actual WOTS preimage term of the linear signature inequality. -/
theorem signature_pre (hq : ∀ pk, CountBound isPort (F.main pk) (2^40))
    (hs : ∀ pk, CountBound isSign (F.main pk) 1) :
    uniformMean (fun π => qSM_DT_PRE_Advantage (qrPre (B π))) ≤ ((2:ℝ≥0∞)^37)⁻¹ := by
  simp_rw [native_eq S rand seeds F]
  apply (bound S seeds A M (2^40+483*qmWotsPreHashes S.vp 1) (2^100)
    (fun st pk => inverse_pue S rand seeds F st pk _ _ hq hs) _).trans
  · exact numeric S _ _ (by cases S <;> decide +kernel) le_rfl
  · intro pk
    apply (countBound_iff_wCount _ _ _).2
    exact ((countBound_iff_wCount _ _ _).1 (prog_cost S pk _ ([],[]) _ (pre_choice_cost S (ShakeApi.extend T₀) seeds))).mono (calls_budget S)
end
end Reduction.ShakePermutation.SparsePort.Wots.Pre
#print axioms Reduction.ShakePermutation.SparsePort.Wots.Pre.signature_pre
