import Integration.SlhDsaShakePermutationClassicalSourceBounds

/-! Nonvacuous classical byte-signature forgery bounds for all six
FIPS 205 SHAKE sets in the public two-way ideal-permutation model. -/
namespace Reduction.ShakePermutation.Classic
open OracleSpec OracleComp MLink SLHDSA SLHDSA.Security Classical PQ.Interactive PQ.QROM Quantum
open SetOracle (uniformMean)
open scoped ENNReal Classical
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 2048

private theorem rotate {A B C : Type} [Fintype A] [Fintype B] [Fintype C] (f : A → B → C → ℝ≥0∞) :
    uniformMean (fun a => uniformMean (fun b => uniformMean (f a b))) =
    uniformMean (fun b => uniformMean (fun c => uniformMean (fun a => f a b c))) :=
  (mean_comm (fun a b => uniformMean (f a b))).trans (congrArg uniformMean (funext fun b => mean_comm (fun a c => f a b c)))

def directLimit (S : Sha2Set) : ℝ≥0∞ := ((2:ℝ≥0∞)^(8*S.vp.params.n-89))⁻¹
def byteLimit (S : Sha2Set) : ℝ≥0∞ := directLimit S + (2^427 : ℝ≥0∞)⁻¹

def strongRule {M B : Type} (log : QueryLog (M →ₒ B)) (m : M) (sig : B) := !SignatureAlg.signingLogContains log m sig
def existRule {M B : Type} (log : QueryLog (M →ₒ B)) (m : M) (_ : B) := !log.wasQueried m
abbrev strongFresh : Fresh := strongRule
abbrev existentialFresh : Fresh := existRule
private theorem strong_at {M B K S W : Type} [Fintype W] {A : SignatureAlg ProbComp M K S B} (Q : QForger W A) :
    qStrongUnforgeableAdvantage Q = qWeight (·=true) (qSigExperiment strongRule Q) Q.ρ₀ := rfl
private theorem exist_at {M B K S W : Type} [Fintype W] {A : SignatureAlg ProbComp M K S B} (Q : QForger W A) :
    qUnforgeableAdvantage Q = qWeight (·=true) (qSigExperiment existRule Q) Q.ρ₀ := rfl

private theorem strongMean (S : Sha2Set) (r : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node)
    {E : Type} [Fintype E] [DecidableEq E] (F : PortForger Port Words E) :
    strongAdvantage S r seeds F = uniformMean (fun π : Permutation => qWeight (·=true)
      (qSigExperiment strongFresh (experiment S r seeds F π)) F.ρ₀) := by
  apply Finset.sum_congr rfl
  intro π _
  exact congrArg (fun v => unifW Permutation π * v) (strong_at (experiment S r seeds F π))
private theorem existentialMean (S : Sha2Set) (r : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node)
    {E : Type} [Fintype E] [DecidableEq E] (F : PortForger Port Words E) :
    advantage S r seeds F = uniformMean (fun π : Permutation => qWeight (·=true)
      (qSigExperiment existentialFresh (experiment S r seeds F π)) F.ρ₀) := by
  apply Finset.sum_congr rfl
  intro π _
  exact congrArg (fun v => unifW Permutation π * v) (exist_at (experiment S r seeds F π))

private theorem strongRaw (S : Sha2Set) (N : ℕ) (r : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node)
    {E : Type} [Fintype E] [DecidableEq E] (F : PortForger (ShakeApi.Input N) (Bytes S.vp.params.m) E) :
    uniformMean (fun H => qStrongUnforgeableAdvantage (ShakeApi.rawForger S N r seeds F H)) =
    uniformMean (fun H => qWeight (·=true) (qSigExperiment strongFresh (ShakeApi.rawForger S N r seeds F H)) F.ρ₀) := by
  exact congrArg uniformMean (funext fun H => strong_at (ShakeApi.rawForger S N r seeds F H))
private theorem existentialRaw (S : Sha2Set) (N : ℕ) (r : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node)
    {E : Type} [Fintype E] [DecidableEq E] (F : PortForger (ShakeApi.Input N) (Bytes S.vp.params.m) E) :
    uniformMean (fun H => qUnforgeableAdvantage (ShakeApi.rawForger S N r seeds F H)) =
    uniformMean (fun H => qWeight (·=true) (qSigExperiment existentialFresh (ShakeApi.rawForger S N r seeds F H)) F.ρ₀) := by
  exact congrArg uniformMean (funext fun H => exist_at (ShakeApi.rawForger S N r seeds F H))

variable (S : Sha2Set) (rand : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node)
    (F : CForger Port Words) (c : Caps) (msg : c.ml = 65536)
    (hp : ∀ pk, CountBound (fun i => publicRead (X := Port) (Y := Words) i = true) (F pk) (2^40))
    (hs : ∀ pk, CountBound (fun i => signRead (X := Port) (Y := Words) i = true) (F pk) 1)
    (hc : ∀ pk, AllQueries (readCap (X := Port) (Y := Words) c) (capOut c) (F pk))

abbrev inputLimit (S : Sha2Set) := 65536+3*S.vp.params.n
local notation "N" => inputLimit S
local notation "T" => (2^41 : ℕ)
local notation "F₀" => liftClassical (false,0) F

private theorem block_fit : Completion.blockCap N ≤ T := by cases S <;> decide +kernel

include c msg hp hs hc
private theorem transfer (fresh : Fresh) (source :
    ∀ g : Completion.Private T, ∀ k : Fix.Domain T → Capacity, ∀ u : Port → Words,
    let player := liftClassical (BList.ofList [] (by simp))
      (sourceForger S N T (block_fit S) g k u F)
    uniformMean (fun raw => qWeight (·=true) (qSigExperiment fresh (ShakeApi.rawForger S N rand seeds player raw)) player.ρ₀)
      ≤ directLimit S) :
    uniformMean (fun π : Permutation => qWeight (·=true) (qSigExperiment fresh (experiment S rand seeds F₀ π)) (F₀).ρ₀)
      ≤ byteLimit S := by
  let fixed : ShakeApi.Xof S := fun _ => default
  let P := byteGame S N (Honest.rawScheme S N fixed rand seeds) F fresh
  let cap := block_fit S
  have sigcap : ShakeApi.rawCap S 67 c.ml ≤ N := by rw [msg]; cases S <;> decide +kernel
  have hbounded : WCount (charge S N) P T := (byte_budget S N fixed rand seeds 483 (by cases S <;> decide +kernel)
    F fresh (2^40) 1 hp hs).mono (by have := Honest.benchmark_honest_blocks S; omega)
  have real (π : Permutation) := byte_real S N fixed rand seeds F fresh c sigcap
    (fun pk => (lift_bounds (false,0) F pk _ _ c (hp pk) (hs pk) (hc pk)).2.2) π
  let am (g : Completion.Private T) (H : ShakeApi.RawTable S N) (k : Fix.Domain T → Capacity) (u : Port → Words) :=
    idealOuter S N T (banks T (Completion.complete S cap g H) k u) H (fun v => hit (v=true)) P []
  have sim (g : Completion.Private T) (k : Fix.Domain T → Capacity) (u : Port → Words) :
      uniformMean (fun H => am g H k u) ≤ directLimit S := by
    have eq (H : ShakeApi.RawTable S N) := byte_ideal S N T cap g k u H fixed rand seeds F fresh
    exact (congrArg uniformMean (funext eq)).le.trans (source g k u)
  have ideal : uniformMean (fun g => uniformMean (fun H => uniformMean (fun k => uniformMean (fun u => am g H k u)))) ≤ directLimit S := by
    refine (mean_mono (fun g => (rotate (am g)).le.trans ?_)).trans_eq (avg_const _)
    exact (mean_mono (fun k => (mean_mono (sim g k)).trans_eq (avg_const _))).trans_eq (avg_const _)
  exact (congrArg uniformMean (funext real)).symm.le.trans
    ((classical_crossing S N T cap P T hbounded le_rfl).trans (add_le_add ideal loss_benchmark))

/-- Bounded byte messages, one signing query and 2^40 adaptive forward
or inverse public permutation queries. Freshness is tested on the exact
byte messages and signatures returned by the byte API. -/
theorem classical_signature_benchmark :
    strongAdvantage S rand seeds F₀ ≤ byteLimit S ∧ advantage S rand seeds F₀ ≤ byteLimit S := by
  have both (g : Completion.Private T) (k : Fix.Domain T → Capacity) (u : Port → Words) :=
    ShakeXof.signature_benchmark_precise S N rand seeds (liftClassical (BList.ofList [] (by simp))
      (sourceForger S N T (block_fit S) g k u F)) c msg le_rfl
      (fun pk => (source_bounds S N T (block_fit S) g k u F pk _ _ c (hp pk) (hs pk) (hc pk)).1)
      (fun pk => (source_bounds S N T (block_fit S) g k u F pk _ _ c (hp pk) (hs pk) (hc pk)).2.1)
      (fun pk => (source_bounds S N T (block_fit S) g k u F pk _ _ c (hp pk) (hs pk) (hc pk)).2.2)
  rw [strongMean,existentialMean]
  constructor
  · apply transfer S rand seeds F c msg hp hs hc strongFresh
    intro g k u
    exact (strongRaw S N rand seeds _).symm.le.trans (both g k u).1
  · apply transfer S rand seeds F c msg hp hs hc existentialFresh
    intro g k u
    exact (existentialRaw S N rand seeds _).symm.le.trans (both g k u).2

omit c msg hp hs hc in
theorem byteLimit_nonvacuous (S : Sha2Set) : byteLimit S < 1 := by
  have bits : 8*S.vp.params.n = 128 ∨ 8*S.vp.params.n = 192 ∨ 8*S.vp.params.n = 256 := by cases S <;> decide +kernel
  unfold byteLimit directLimit
  rcases bits with h|h|h <;> rw [h] <;>
    apply (ENNReal.toReal_lt_toReal (by finiteness) (by finiteness)).mp <;>
    rw [ENNReal.toReal_add (by finiteness) (by finiteness)] <;>
    norm_num [ENNReal.toReal_inv,ENNReal.toReal_pow,ENNReal.toReal_ofNat]

end
end Reduction.ShakePermutation.Classic
#print axioms Reduction.ShakePermutation.Classic.classical_signature_benchmark
#print axioms Reduction.ShakePermutation.Classic.byteLimit_nonvacuous
