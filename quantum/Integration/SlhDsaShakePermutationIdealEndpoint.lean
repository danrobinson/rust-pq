import Integration.SlhDsaShakePermutationIdealCount
import Integration.SlhDsaShakePermutationAccess

/-! The ideal endpoint of the public permutation comparison: start with the
original two-way public-port forger, expand its actual gate sequence, and
run private compressed masks with routed head calls to a uniform full rate
table. The byte-level signer uses the padded, truncated rows of that table. -/
namespace Reduction.ShakePermutation.IdealDriver
open MLink SLHDSA SLHDSA.Security Quantum OracleSpec OracleComp PQ.Interactive Fix Fix.Machine
open RoundPort Player ShakeXof Classical ENNReal
open scoped ComplexOrder
set_option maxHeartbeats 3600000
set_option maxRecDepth 8192

variable (S : Sha2Set) {T N : ℕ} (cap : Completion.blockCap N ≤ T)
private theorem fits_rate : S.vp.params.m ≤ 136 := by cases S <;> decide +kernel

def projected (f : Fix.Table T) : ShakeApi.RawTable S N := fun x =>
  ShakeXof.head (fits_rate S) (Completion.bytes (f (Completion.address cap x)))

theorem projected_complete (g : Completion.Private T) (H : ShakeApi.RawTable S N) :
    projected S cap (Completion.complete S cap g H) = H := by
  funext x
  exact Completion.prefix_complete S cap g H x _

variable {E : Type} [Fintype E] [DecidableEq E] (π : Permutation) (h : RateMask)
variable (F : PortForger Port Words E) (r : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node)

noncomputable def playerGame (H : ShakeApi.RawTable S N) (f : List Rate → Rate) :
    QForger (State E) (ShakeApi.scheme S r seeds (ShakeApi.extend H)) where
  main pk := Machine.ideal (transform f) ((forger π T h F).main pk)
  ρ₀ := (forger π T h F).initial
  posSemidef := (forger π T h F).pos
  trace_eq_one := (forger π T h F).trace

noncomputable def experiment (f : Fix.Table T) :=
  playerGame (T := T) S π h F r seeds (projected S cap f) (Fix.extend f)

/-- All six SHAKE parameter sets, one capped signing request and 2^40
two-way permutation calls on the expanded public-player circuit in the
ideal simulator. The bound is uniform in the private permutation and mask. -/
theorem ideal_endpoint_precise (c : Caps) (msg : c.ml = 65536) (fit : 65536+3*S.vp.params.n ≤ N)
    (hl : Completion.blockCap N ≤ 483)
    (hq : ∀ pk, CountBound isPort (F.main pk) (2^40))
    (hs : ∀ pk, CountBound isSign (F.main pk) 1)
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    SetOracle.uniformMean (fun f => qStrongUnforgeableAdvantage (experiment S cap π h F r seeds f)) ≤ ((2:ℝ≥0∞)^(8*S.vp.params.n-119))⁻¹ ∧
    SetOracle.uniformMean (fun f => qUnforgeableAdvantage (experiment S cap π h F r seeds f)) ≤ ((2:ℝ≥0∞)^(8*S.vp.params.n-119))⁻¹ := by
  let game := experiment S cap π h F r seeds
  let player := forger π T h F
  have cost := bounds π T h F c _ _ hq hs hc
  have partialBound (g : Completion.Private T) :
      SetOracle.uniformMean (fun H => qStrongUnforgeableAdvantage (game (Completion.complete S cap g H))) ≤ ((2:ℝ≥0∞)^(8*S.vp.params.n-119))⁻¹ ∧
      SetOracle.uniformMean (fun H => qUnforgeableAdvantage (game (Completion.complete S cap g H))) ≤ ((2:ℝ≥0∞)^(8*S.vp.params.n-119))⁻¹ := by
    have b := corrected_signature_precise S N (Completion.blockCap N) (Completion.access S cap g) player r seeds c msg fit hl
      (fun pk => (cost pk).1) (fun pk => (cost pk).2.1) (fun pk => (cost pk).2.2)
    let sf := fun (HH : ShakeApi.RawTable S N) (f : List Rate → Rate) => qStrongUnforgeableAdvantage (playerGame (T := T) S π h F r seeds HH f)
    let ef := fun (HH : ShakeApi.RawTable S N) (f : List Rate → Rate) => qUnforgeableAdvantage (playerGame (T := T) S π h F r seeds HH f)
    let full := Completion.complete S cap g
    let port := (Completion.access S cap g).value (Completion.blockCap N)
    change SetOracle.uniformMean (fun H => sf (projected S cap (full H)) (Fix.extend (full H))) ≤ _ ∧
      SetOracle.uniformMean (fun H => ef (projected S cap (full H)) (Fix.extend (full H))) ≤ _
    change SetOracle.uniformMean (fun H => sf H (port H)) ≤ _ ∧
      SetOracle.uniformMean (fun H => ef H (port H)) ≤ _ at b
    simpa only [port,full,projected_complete,Completion.value_access] using b
  constructor
  · rw [Completion.uniform_complete S cap (fits_rate S)]
    exact ShakeXof.mean_le_const fun g => (partialBound g).1
  · rw [Completion.uniform_complete S cap (fits_rate S)]
    exact ShakeXof.mean_le_const fun g => (partialBound g).2

theorem ideal_endpoint (c : Caps) (msg : c.ml = 65536) (fit : 65536+3*S.vp.params.n ≤ N)
    (hl : Completion.blockCap N ≤ 483)
    (hq : ∀ pk, CountBound isPort (F.main pk) (2^40))
    (hs : ∀ pk, CountBound isSign (F.main pk) 1)
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    SetOracle.uniformMean (fun f => qStrongUnforgeableAdvantage (experiment S cap π h F r seeds f)) ≤ ((2:ℝ≥0∞)^7)⁻¹ ∧
    SetOracle.uniformMean (fun f => qUnforgeableAdvantage (experiment S cap π h F r seeds f)) ≤ ((2:ℝ≥0∞)^7)⁻¹ := by
  have e := ideal_endpoint_precise S cap π h F r seeds c msg fit hl hq hs hc
  have le : ((2:ℝ≥0∞)^(8*S.vp.params.n-119))⁻¹ ≤ ((2:ℝ≥0∞)^7)⁻¹ := by
    apply ENNReal.inv_le_inv.mpr
    exact pow_le_pow_right₀ (by norm_num) (by cases S <;> decide)
  exact ⟨e.1.trans le,e.2.trans le⟩

end Reduction.ShakePermutation.IdealDriver
#print axioms Reduction.ShakePermutation.IdealDriver.ideal_endpoint
