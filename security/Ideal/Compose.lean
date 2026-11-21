import Ideal.Inst.SkPrf128
import Ideal.Inst.MsgPrf128
import Ideal.Inst.ForsDspr128
import Ideal.Inst.ForsTcr128
import Ideal.Inst.TcrTight128
import Ideal.Inst.WotsUd128
import Ideal.Inst.WotsPre128
import Reduction.LinearBytes

/-!
# SLH-DSA-SHA2-128s in the ideal-compression-function model: the composition

The linear standard-model headline of `Reduction/LinearBytes.lean` holds for every primitive
bundle satisfying `Reduction.Structural`, in particular for the 128s bundle `primsG (liftC g)`
built over an arbitrary SHA-256 compression table `g : CF St Blk` (`structuralG`, wire codec
`codecG g`; at `g = realCF` this is the real scheme, `bytesAlg_realCF`).  Averaging that
inequality over a uniformly random table and inserting the ideal-model bounds of `Ideal/Inst/*`
gives a bound on the table-averaged SUF-CMA (and EUF-CMA) advantage of an ideal-model forger.

* `ForgerI`: ONE oracle program with a signing oracle and access to the compression function
  (`hS St Blk`); `S.sufInst optRand pkSeedDist g` answers its compression queries with `g` and is
  a strong forger against `bytesAlg Link.vp (primsG (liftC g)) (codecG g) (optRand g) pkSeedDist`.
  `optRand` is a parameter `∀ g, PublicKeyCore (primsG (liftC g)).core → ProbComp (primsG (liftC g)).Y`
  (it depends on `g` only through the type of its argument; the two FIPS choices are
  `fun _ pk => pure pk.pkSeed` and `fun _ _ => $ᵗ (Bytes 16)`).
* `sufI`, `eufI`: the advantage for a uniformly random table (`sufI_eq_cfAvg`: the average over
  `g` of `SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp (S.sufInst … g)`).
* `cfAvg`, `cfAvg_prTrue`, `cfAvg_add`, `cfAvg_mul_left`, `cfAvg_mono`: the averaging lemma.
* **Realisability hypotheses.**  The Reduction's adversaries evaluate the hash functions as local
  pure computation; in the ideal model these evaluations have to be compression-oracle queries.
  This file does NOT prove that the twelve reduction adversaries can be rewritten in that way.
  Instead, for a family `B g` of adversaries (one per table), `RealizesPrf B q qO`, …,
  `RealizesWotsTcr B p` say: there is ONE ideal-model adversary `A` (an oracle program with
  compression queries, with the stated query bounds) such that for every table `g` the Reduction's
  experiment at `B g` has the same output distribution as at `A` instantiated at `g`.  (Equality
  of the adversaries `B g = inst A g` implies this: `RealizesTcr.ofEq` etc.)  The ITSR game of
  `H_msg` is not bounded here: its table-averaged advantage `itsrI` is bounded by hypothesis.
* `ideal_bound_core`: the composition for arbitrary families satisfying the linear inequality;
  `suf_ideal_bound`, `euf_ideal_bound`: the instances at the Reduction's adversaries.

Numeric corollaries: `Ideal/Compose128.lean`.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal TweakableHash

namespace Ideal

/-! ## 1. The scheme over a compression table -/

instance instInhabitedYC (c : CompressFn) : Inhabited (primsG c).Y := ⟨Vector.replicate 16 0⟩

/-- The structural side conditions hold for the 128s bundle over any compression function (they
do not involve the hash functions); cf. `Reduction.structural_128s`. -/
theorem structuralC (c : CompressFn) : Reduction.Structural Link.vp (primsG c) := by
  have hb : ApprovedAddressBounds Link.vp.params := fipsApprovedAddressBounds Link.S128
  refine ⟨⟨fun _ _ h => h⟩, ?_, hb.toCanonicalAddressBounds⟩
  intro a ha b hb' hkey
  obtain ⟨hac, hal, hat⟩ := sha2Domain_of_addressFacts hb ha
  obtain ⟨hbc, hbl, hbt⟩ := sha2Domain_of_addressFacts hb hb'
  exact Concrete.sha2AdrsKey_injective_of_domain hac hal hat hbc hbl hbt hkey

theorem structuralG (g : CF St Blk) : Reduction.Structural Link.vp (primsG (liftC g)) :=
  structuralC (liftC g)

/-- The atomic wire codec of the 128s bundle over a compression function: every carrier is
`Bytes 16`, encoded as itself (as `SLHDSA.Concrete.sha2WireCodec`). -/
def codecC (c : CompressFn) : CoreWireCodec Link.vp.params (primsG c).core where
  pkSeed := WireCodec.bytes Link.vp.params.n
  skSeed := WireCodec.bytes Link.vp.params.n
  skPrf := WireCodec.bytes Link.vp.params.n
  y := WireCodec.bytes Link.vp.params.n
  y_toBytes := fun _ => rfl

/-- The wire codec over the table `g`. -/
abbrev codecG (g : CF St Blk) : CoreWireCodec Link.vp.params (primsG (liftC g)).core :=
  codecC (liftC g)

/-- At the real compression function the codec is the Reduction's `codec128s`. -/
theorem codecC_compress : codecC VCVio.Algorithms.Sha2.compress = Reduction.codec128s := rfl

/-- **At the table of the real compression function the byte-level scheme is the real one**
(`Reduction.bytesAlg Link.vp Link.prims codec128s …`), for any family of `opt_rand` samplers. -/
theorem bytesAlg_realCF
    (optRand : ∀ c : CompressFn, PublicKeyCore (primsG c).core → ProbComp (primsG c).Y)
    (pkSeedDist : ProbComp (Bytes 16)) :
    Reduction.bytesAlg Link.vp (primsG (liftC realCF)) (codecG realCF) (optRand (liftC realCF))
        pkSeedDist =
      Reduction.bytesAlg Link.vp Link.prims Reduction.codec128s
        (optRand VCVio.Algorithms.Sha2.compress) pkSeedDist :=
  congrArg (fun c => Reduction.bytesAlg Link.vp (primsG c) (codecC c) (optRand c) pkSeedDist)
    liftC_realCF

/-! ## 2. Averaging over the table -/

section Avg

variable {S B : Type} [SampleableType (CF S B)]

/-- The average of `f` over a uniformly random compression table (the expectation of `f g` for
`g ← $ᵗ (CF S B)`; the table type carries the discrete σ-algebra). -/
noncomputable def cfAvg (f : CF S B → ℝ≥0∞) : ℝ≥0∞ :=
  letI : MeasurableSpace (CF S B) := ⊤
  ∫⁻ g, f g ∂𝒟[($ᵗ (CF S B) : ProbComp (CF S B))]

/-- **Averaging lemma**: the probability that an experiment run at a uniformly random table
returns `true` is the average of the per-table probabilities. -/
theorem cfAvg_prTrue (X : CF S B → ProbComp Bool) :
    𝒟[$ᵗ (CF S B) >>= X] {true} = cfAvg fun g => 𝒟[X g] {true} :=
  Reduction.prTrue_bind _ X

theorem cfAdvantage_eq_cfAvg (X : CF S B → ProbComp Bool) :
    cfAdvantage X = cfAvg fun g => 𝒟[X g] {true} := cfAvg_prTrue X

theorem cfAvg_add (f h : CF S B → ℝ≥0∞) :
    (cfAvg fun g => f g + h g) = cfAvg f + cfAvg h := by
  let : MeasurableSpace (CF S B) := ⊤
  exact MeasureTheory.lintegral_add_left Measurable.of_discrete _

theorem cfAvg_mul_left (c : ℝ≥0∞) (f : CF S B → ℝ≥0∞) :
    (cfAvg fun g => c * f g) = c * cfAvg f := by
  let : MeasurableSpace (CF S B) := ⊤
  exact MeasureTheory.lintegral_const_mul c Measurable.of_discrete

theorem cfAvg_mono {f h : CF S B → ℝ≥0∞} (hfh : ∀ g, f g ≤ h g) : cfAvg f ≤ cfAvg h := by
  let : MeasurableSpace (CF S B) := ⊤
  exact MeasureTheory.lintegral_mono hfh

theorem cfAvg_congr {f h : CF S B → ℝ≥0∞} (hfh : ∀ g, f g = h g) : cfAvg f = cfAvg h :=
  congrArg cfAvg (funext hfh)

/-- The average of per-table probabilities, when the experiments have the same distribution as
those of an instantiated ideal-model adversary. -/
theorem cfAvg_of_evalDist_eq {X Y : CF S B → ProbComp Bool} (h : ∀ g, 𝒟[X g] = 𝒟[Y g]) :
    (cfAvg fun g => 𝒟[X g] {true}) = cfAdvantage Y := by
  rw [cfAdvantage_eq_cfAvg]
  exact cfAvg_congr fun g => by rw [h g]

theorem cfAdvantage_eq_idealAdv (X : CF S B → ProbComp Bool) :
    cfAdvantage X = idealAdv S B X := rfl

theorem cfAdvantage_eq_idealAdvT (X : CF S B → ProbComp Bool) :
    cfAdvantage X = idealAdvT X := rfl

theorem cfAdvantage_le_add_boolDist (X Y : CF S B → ProbComp Bool) :
    cfAdvantage X ≤ cfAdvantage Y +
      (𝒟[do
        let g ← $ᵗ (CF S B)
        X g]).boolDist (𝒟[do
        let g ← $ᵗ (CF S B)
        Y g]) :=
  MeasureTheory.Measure.apply_true_le_add_boolDist _ _

theorem cfAdvantage_le_one (X : CF S B → ProbComp Bool) : cfAdvantage X ≤ 1 :=
  Reduction.prTrue_le_one' _

end Avg

/-! ## 3. Ideal-model forgers -/

/-- An ideal-model forger against byte-level SLH-DSA-SHA2-128s: given the public-key bytes, an
oracle program with uniform sampling, **compression-function queries** and a signing oracle
(message bytes to signature bytes), returning a message and a signature. -/
structure ForgerI where
  main : List Byte →
    OracleComp (unifSpec + (hS St Blk + (List Byte →ₒ List Byte))) (List Byte × List Byte)

section Forger

variable (S : ForgerI)
  (optRand : ∀ g : CF St Blk, PublicKeyCore (primsG (liftC g)).core → ProbComp (primsG (liftC g)).Y)
  (pkSeedDist : ProbComp (Bytes 16))

/-- The strong forger at the table `g`: compression queries are answered by `g`. -/
def ForgerI.sufInst (g : CF St Blk) :
    Reduction.BytesStrongForger Link.vp (primsG (liftC g)) (codecG g) (optRand g) pkSeedDist where
  main pk := simulateQ (instImpl g) (S.main pk)

/-- The (EUF) forger at the table `g`. -/
def ForgerI.eufInst (g : CF St Blk) :
    Reduction.BytesForger Link.vp (primsG (liftC g)) (codecG g) (optRand g) pkSeedDist where
  main pk := simulateQ (instImpl g) (S.main pk)

/-- The typed forger the Reduction builds from the strong forger at the table `g`. -/
noncomputable def ForgerI.typedS (g : CF St Blk) :
    Reduction.Forger Link.vp (primsG (liftC g)) (optRand g) pkSeedDist :=
  (Reduction.bytesToTypedS (S.sufInst optRand pkSeedDist g)).toUnforgeableAdversary

/-- The typed forger the Reduction builds from the forger at the table `g`. -/
noncomputable def ForgerI.typedE (g : CF St Blk) :
    Reduction.Forger Link.vp (primsG (liftC g)) (optRand g) pkSeedDist :=
  Reduction.bytesToTyped (S.eufInst optRand pkSeedDist g)

/-- **SUF-CMA advantage in the ideal-compression model**: the probability that the strong
unforgeability experiment of the byte-level scheme over a uniformly random table `g`, with the
forger's compression queries answered by `g`, returns `true`. -/
noncomputable def sufI : ℝ≥0∞ :=
  cfAdvantage fun g => SignatureAlg.strongUnforgeableExperiment (S.sufInst optRand pkSeedDist g)

/-- **EUF-CMA advantage in the ideal-compression model.** -/
noncomputable def eufI : ℝ≥0∞ :=
  cfAdvantage fun g => SignatureAlg.unforgeableExperiment (S.eufInst optRand pkSeedDist g)

/-- `sufI` is the table average of VCVio's SUF-CMA advantages. -/
theorem sufI_eq_cfAvg :
    sufI S optRand pkSeedDist = cfAvg fun g =>
      SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp
        (S.sufInst optRand pkSeedDist g) :=
  cfAdvantage_eq_cfAvg _

/-- `eufI` is the table average of VCVio's EUF-CMA advantages. -/
theorem eufI_eq_cfAvg :
    eufI S optRand pkSeedDist = cfAvg fun g =>
      SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp
        (S.eufInst optRand pkSeedDist g) :=
  cfAdvantage_eq_cfAvg _

end Forger

/-! ## 4. Realisability of the reduction adversaries in the ideal model -/

/-- Query parameters of a two-phase adversary without collection oracle: first-phase compression
queries, challenge queries, second-phase compression queries. -/
structure P3 where
  q₁ : ℕ
  qch : ℕ
  q₂ : ℕ

/-- Query parameters of a two-phase adversary: first-phase compression queries, challenge
queries, collection queries, continuation length (blocks after the first) of the collection
queries, second-phase compression queries. -/
structure P5 where
  q₁ : ℕ
  qch : ℕ
  qc : ℕ
  L : ℕ
  q₂ : ℕ

section Realizes

variable (pkSeedDist : ProbComp (Bytes 16))

/-- The family `B g` of `PRF` distinguishers (secret-key address domain) is realised by one
ideal-model distinguisher making at most `q` compression and `qO` oracle queries. -/
structure RealizesPrf
    (B : ∀ g : CF St Blk, PRFScheme.PRFAdversary
      ((primsG (liftC g)).PkSeed × Reduction.SkAdrs Link.vp) (primsG (liftC g)).Y)
    (q qO : ℕ) where
  A : PrfAdvI St Blk (Bytes 16) SkAd (Bytes 16)
  real : ∀ g, 𝒟[(Reduction.skPrfC Link.vp (primsG (liftC g))).prfRealExperiment (B g)] =
    𝒟[(Reduction.skPrfC Link.vp (primsG (liftC g))).prfRealExperiment (A.inst g)]
  ideal : ∀ g, 𝒟[PRFScheme.prfIdealExperiment (B g)] =
    𝒟[PRFScheme.prfIdealExperiment (A.inst g)]
  hq : IsQueryBoundP A (fun i => isCompQ i = true) q
  hO : IsQueryBoundP A (fun i => isPrfQ i = true) qO

/-- The family `B g` of `PRF_msg` distinguishers is realised by one ideal-model distinguisher
making at most `q` compression and `qO` oracle queries, on messages of at most `mlen` bytes. -/
structure RealizesMsg (B : ∀ g : CF St Blk, Reduction.MsgPrfAdv (primsG (liftC g)))
    (q qO mlen : ℕ) where
  A : MsgPrfAdvI
  real : ∀ g, 𝒟[(Reduction.msgPrf Link.vp (primsG (liftC g))).prfRealExperiment (B g)] =
    𝒟[(Reduction.msgPrf Link.vp (primsG (liftC g))).prfRealExperiment (A.inst g)]
  ideal : ∀ g, 𝒟[PRFScheme.prfIdealExperiment (B g)] =
    𝒟[PRFScheme.prfIdealExperiment (D := (primsG (liftC g)).Y × List Byte)
      (R := (primsG (liftC g)).Y) (A.inst g)]
  hq : IsQueryBoundP A (fun i => isCompQ i = true) q
  hO : IsQueryBoundP A (fun i => isPrfQ i = true) qO
  hM : AllQueriesSatisfy A (msgLenLe mlen)

/-- The family `D g` of FORS-leaf SM-DSPR adversaries is realised by one ideal-model adversary. -/
structure RealizesDspr
    (D : ∀ g : CF St Blk, SM_DT_DSPR_SourceFinalValidity.Adversary
      (Reduction.forsDsprProblem Link.vp (primsG (liftC g)) pkSeedDist)) (p : P3) where
  A : ForsDsprAdv128 pkSeedDist
  success : ∀ g, 𝒟[SM_DT_DSPR_SourceFinalValidity.experiment (D g)] =
    𝒟[SM_DT_DSPR_SourceFinalValidity.experiment (instForsDspr A g)]
  sp : ∀ g, 𝒟[SM_DT_DSPR_SourceFinalValidity.spExperiment (D g)] =
    𝒟[SM_DT_DSPR_SourceFinalValidity.spExperiment (instForsDspr A g)]
  hq₁ : A.ChooseBound p.q₁
  hch : A.ChalBound p.qch
  hq₂ : A.GuessBound p.q₂

/-- The family `T g` of FORS-leaf SM-TCR adversaries is realised by one ideal-model adversary. -/
structure RealizesForsTcr
    (T : ∀ g : CF St Blk, SM_DT_TCR_SourceFinalValidity.Adversary
      (Reduction.forsTcrProblem Link.vp (primsG (liftC g)) pkSeedDist)) (p : P3) where
  A : ForsTcrAdv128 pkSeedDist
  eq : ∀ g, 𝒟[SM_DT_TCR_SourceFinalValidity.experiment (T g)] =
    𝒟[SM_DT_TCR_SourceFinalValidity.experiment (instFors A g)]
  hq₁ : A.ChooseBound p.q₁
  hch : A.ChalBound p.qch
  hq₂ : A.ForgeBound p.q₂

/-- The family `C g` of arity-`n` SM-TCR adversaries (tight cap) is realised by one ideal-model
adversary. -/
structure RealizesTcr (n : ℕ)
    (C : ∀ g : CF St Blk, SM_DT_TCR_Adversary
      (Reduction.thashArityProblemT Link.vp (primsG (liftC g)) pkSeedDist n)) (p : P5) where
  A : TcrAdv128T pkSeedDist n
  eq : ∀ g, 𝒟[SM_DT_TCR_Experiment (C g)] = 𝒟[SM_DT_TCR_Experiment (instRT A g)]
  hq₁ : A.ChooseBound p.q₁
  hch : A.ChalBound p.qch
  hc : A.CollBound p.qc
  hL : A.CollLen p.L
  hq₂ : A.ForgeBound p.q₂

/-- The family `B g` of SM-UD adversaries on `F` is realised by one ideal-model adversary. -/
structure RealizesUd
    (B : ∀ g : CF St Blk, SM_DT_UD_Adversary
      (Reduction.wotsUdProblem Link.vp (primsG (liftC g)) pkSeedDist)) (p : P5) where
  A : WotsUdAdv128 pkSeedDist
  real : ∀ g, 𝒟[SM_DT_UD_Experiment .real (B g)] = 𝒟[SM_DT_UD_Experiment .real (instWU A g)]
  ideal : ∀ g, 𝒟[SM_DT_UD_Experiment .ideal (B g)] = 𝒟[SM_DT_UD_Experiment .ideal (instWU A g)]
  hq₁ : A.PickBound p.q₁
  hch : A.ChalBound p.qch
  hc : A.CollBound p.qc
  hL : A.CollLen p.L
  hq₂ : A.DistBound p.q₂

/-- The family `B g` of SM-PRE adversaries on `F` is realised by one ideal-model adversary. -/
structure RealizesPre
    (B : ∀ g : CF St Blk, SM_DT_PRE_Adversary
      (Reduction.wotsPreProblem Link.vp (primsG (liftC g)) pkSeedDist)) (p : P5) where
  A : WotsPreAdv128 pkSeedDist
  eq : ∀ g, 𝒟[SM_DT_PRE_Experiment (B g)] = 𝒟[SM_DT_PRE_Experiment (instWP A g)]
  hq₁ : A.ChooseBound p.q₁
  hch : A.ChalBound p.qch
  hc : A.CollBound p.qc
  hL : A.CollLen p.L
  hq₂ : A.InvertBound p.q₂

/-- The family `B g` of SM-TCR adversaries on `F` (tight cap) is realised by one ideal-model
adversary. -/
structure RealizesWotsTcr
    (B : ∀ g : CF St Blk, SM_DT_TCR_Adversary
      (Reduction.wotsTcrProblemT Link.vp (primsG (liftC g)) pkSeedDist)) (p : P5) where
  A : WotsTcrAdv128T pkSeedDist
  eq : ∀ g, 𝒟[SM_DT_TCR_Experiment (B g)] = 𝒟[SM_DT_TCR_Experiment (instWT A g)]
  hq₁ : A.ChooseBound p.q₁
  hch : A.ChalBound p.qch
  hc : A.CollBound p.qc
  hL : A.CollLen p.L
  hq₂ : A.ForgeBound p.q₂

/-! ### Satisfiability: equality of adversaries suffices -/

variable {pkSeedDist}

/-- A family that IS the instantiation of an ideal-model adversary is realised by it. -/
def RealizesTcr.ofEq {n : ℕ}
    {C : ∀ g : CF St Blk, SM_DT_TCR_Adversary
      (Reduction.thashArityProblemT Link.vp (primsG (liftC g)) pkSeedDist n)} {p : P5}
    (A : TcrAdv128T pkSeedDist n) (h : ∀ g, C g = instRT A g)
    (hq₁ : A.ChooseBound p.q₁) (hch : A.ChalBound p.qch) (hc : A.CollBound p.qc)
    (hL : A.CollLen p.L) (hq₂ : A.ForgeBound p.q₂) : RealizesTcr pkSeedDist n C p :=
  ⟨A, fun g => by rw [h g], hq₁, hch, hc, hL, hq₂⟩

def RealizesPrf.ofEq
    {B : ∀ g : CF St Blk, PRFScheme.PRFAdversary
      ((primsG (liftC g)).PkSeed × Reduction.SkAdrs Link.vp) (primsG (liftC g)).Y} {q qO : ℕ}
    (A : PrfAdvI St Blk (Bytes 16) SkAd (Bytes 16)) (h : ∀ g, B g = A.inst g)
    (hq : IsQueryBoundP A (fun i => isCompQ i = true) q)
    (hO : IsQueryBoundP A (fun i => isPrfQ i = true) qO) : RealizesPrf B q qO :=
  ⟨A, fun g => by rw [h g], fun g => by rw [h g]; rfl, hq, hO⟩

def RealizesUd.ofEq
    {B : ∀ g : CF St Blk, SM_DT_UD_Adversary
      (Reduction.wotsUdProblem Link.vp (primsG (liftC g)) pkSeedDist)} {p : P5}
    (A : WotsUdAdv128 pkSeedDist) (h : ∀ g, B g = instWU A g)
    (hq₁ : A.PickBound p.q₁) (hch : A.ChalBound p.qch) (hc : A.CollBound p.qc)
    (hL : A.CollLen p.L) (hq₂ : A.DistBound p.q₂) : RealizesUd pkSeedDist B p :=
  ⟨A, fun g => by rw [h g], fun g => by rw [h g], hq₁, hch, hc, hL, hq₂⟩

/-! ### The explicit error terms (those of the theorems of `Ideal/Inst/*`) -/

/-- `skPrf_bound_128s`. -/
noncomputable def epsPrf (q qO : ℕ) : ℝ≥0∞ :=
  (q : ℝ≥0∞) / 2 ^ 128 + (((q + qO) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256

/-- `msgPrf_bound_128s`. -/
noncomputable def epsMsg (q qO mlen : ℕ) : ℝ≥0∞ :=
  2 * (q : ℝ≥0∞) / 2 ^ 128 +
    (((q + qO * ((mlen + 24) / 64 + 1) + 2) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256

/-- `forsDspr_bound_128s`. -/
noncomputable def epsDspr (γ : ℝ≥0∞) (p : P3) : ℝ≥0∞ :=
  2 * (p.q₁ * γ) + (4 * p.q₁ + 2 * p.qch + 3 : ℕ) * ((2 : ℝ≥0∞) ^ 256)⁻¹

/-- `forsTcr_bound_128s`. -/
noncomputable def epsForsTcr (γ : ℝ≥0∞) (p : P3) : ℝ≥0∞ :=
  (p.q₂ + 1 : ℕ) * ((2 : ℝ≥0∞) ^ 128)⁻¹ + p.q₁ * γ +
    (2 * p.q₁ + p.qch + 2 : ℕ) * ((2 : ℝ≥0∞) ^ 256)⁻¹

/-- `tcrArityT_bound_128s` (`F`, `H`) and `wotsTcrT_bound_128s`. -/
noncomputable def epsTcr (γ : ℝ≥0∞) (p : P5) : ℝ≥0∞ :=
  (p.q₂ + 1 : ℕ) * ((2 : ℝ≥0∞) ^ 128)⁻¹ + p.q₁ * γ +
    (2 * p.q₁ + (p.qch + p.qc) * (1 + 2 * p.L) + 2 : ℕ) * ((2 : ℝ≥0∞) ^ 256)⁻¹

/-- `tcrLen_bound_128s` (`T_len`, arity 35). -/
noncomputable def epsTcrLen (γ : ℝ≥0∞) (p : P5) : ℝ≥0∞ :=
  (p.q₂ + 22 : ℕ) * ((2 : ℝ≥0∞) ^ 128)⁻¹ + p.q₁ * γ +
    (18 * (p.q₁ + p.q₂ + (p.qch + p.qc) * (1 + max 9 p.L) + 21) ^ 2 + 2 * p.q₁ +
      (p.qch + p.qc) * (1 + 2 * max 9 p.L) + 1 : ℕ) * ((2 : ℝ≥0∞) ^ 256)⁻¹

/-- `tcrK_bound_128s` (`T_k`, arity 14). -/
noncomputable def epsTcrK (γ : ℝ≥0∞) (p : P5) : ℝ≥0∞ :=
  (p.q₂ + 10 : ℕ) * ((2 : ℝ≥0∞) ^ 128)⁻¹ + p.q₁ * γ +
    (18 * (p.q₁ + p.q₂ + (p.qch + p.qc) * (1 + max 3 p.L) + 9) ^ 2 + 2 * p.q₁ +
      (p.qch + p.qc) * (1 + 2 * max 3 p.L) + 1 : ℕ) * ((2 : ℝ≥0∞) ^ 256)⁻¹

/-- `wotsUd_bound_128s` (error of the one-sided form). -/
noncomputable def epsUd (γ : ℝ≥0∞) (p : P5) : ℝ≥0∞ :=
  p.q₂ * ((2 : ℝ≥0∞) ^ 128)⁻¹ + 2 * p.q₁ * γ +
    (2 * (2 * p.q₁ + (p.qch + p.qc) * (1 + 2 * p.L) + 1) : ℕ) * ((2 : ℝ≥0∞) ^ 256)⁻¹

/-- `wotsPre_bound_128s`. -/
noncomputable def epsPre (γ : ℝ≥0∞) (p : P5) : ℝ≥0∞ :=
  2 * (p.q₂ + 1 : ℕ) * ((2 : ℝ≥0∞) ^ 128)⁻¹ + p.q₁ * γ +
    (2 * p.q₁ + (p.qch + p.qc) * (1 + 2 * p.L) + 2 : ℕ) * ((2 : ℝ≥0∞) ^ 256)⁻¹

/-! ### Each realiser gives the ideal-model bound for the averaged term -/

variable {γ : ℝ≥0∞}

theorem RealizesPrf.bound
    {B : ∀ g : CF St Blk, PRFScheme.PRFAdversary
      ((primsG (liftC g)).PkSeed × Reduction.SkAdrs Link.vp) (primsG (liftC g)).Y} {q qO : ℕ}
    (R : RealizesPrf B q qO) :
    (cfAvg fun g => Reduction.prfRealPr (B g)) ≤
      (cfAvg fun g => Reduction.prfIdealPr (B g)) + epsPrf q qO := by
  have h1 : (cfAvg fun g => Reduction.prfRealPr (B g)) = cfAdvantage fun g =>
      (Reduction.skPrfC Link.vp (primsG (liftC g))).prfRealExperiment (R.A.inst g) :=
    cfAvg_of_evalDist_eq R.real
  have h2 : (cfAvg fun g => Reduction.prfIdealPr (B g)) = cfAdvantage fun g =>
      PRFScheme.prfIdealExperiment (R.A.inst g) :=
    cfAvg_of_evalDist_eq R.ideal
  rw [h1, h2]
  have h3 := skPrf_bound_128s R.A q qO R.hq R.hO
  unfold skPrfAdvantageI at h3
  exact (cfAdvantage_le_add_boolDist _ _).trans (add_le_add le_rfl h3)

theorem RealizesMsg.bound {B : ∀ g : CF St Blk, Reduction.MsgPrfAdv (primsG (liftC g))}
    {q qO mlen : ℕ} (R : RealizesMsg B q qO mlen) :
    (cfAvg fun g => Reduction.msgRealPr (B g)) ≤
      (cfAvg fun g => Reduction.msgIdealPr (B g)) + epsMsg q qO mlen := by
  have h1 : (cfAvg fun g => Reduction.msgRealPr (B g)) = msgRealI R.A :=
    cfAvg_of_evalDist_eq R.real
  have h2 : (cfAvg fun g => Reduction.msgIdealPr (B g)) = msgIdealI R.A :=
    (cfAvg_of_evalDist_eq R.ideal).trans (msgIdealI_prims R.A).symm
  rw [h1, h2]
  exact (msgPrf_bound_128s R.A q qO mlen R.hq R.hO R.hM).1

theorem RealizesDspr.bound (hγ : ∀ s, Pr{let s' ← pkSeedDist}[s' = s] ≤ γ)
    {D : ∀ g : CF St Blk, SM_DT_DSPR_SourceFinalValidity.Adversary
      (Reduction.forsDsprProblem Link.vp (primsG (liftC g)) pkSeedDist)} {p : P3}
    (R : RealizesDspr pkSeedDist D p) (hq₂ : p.q₂ ≤ 2 ^ 126) :
    (cfAvg fun g => SM_DT_DSPR_SourceFinalValidity.Success (D g)) ≤
      (cfAvg fun g => SM_DT_DSPR_SourceFinalValidity.SPProbability (D g)) + epsDspr γ p := by
  have h1 : (cfAvg fun g => SM_DT_DSPR_SourceFinalValidity.Success (D g)) =
      forsDsprSuccess pkSeedDist R.A :=
    (cfAvg_of_evalDist_eq R.success).trans (cfAdvantage_eq_idealAdv _)
  have h2 : (cfAvg fun g => SM_DT_DSPR_SourceFinalValidity.SPProbability (D g)) =
      forsDsprSP pkSeedDist R.A :=
    (cfAvg_of_evalDist_eq R.sp).trans (cfAdvantage_eq_idealAdv _)
  rw [h1, h2]
  exact (forsDspr_bound_128s pkSeedDist γ hγ R.A p.q₁ p.qch p.q₂ R.hq₁ R.hch R.hq₂ hq₂).trans
    (le_of_eq (add_assoc _ _ _))

theorem RealizesForsTcr.bound (hγ : ∀ s, Pr{let s' ← pkSeedDist}[s' = s] ≤ γ)
    {T : ∀ g : CF St Blk, SM_DT_TCR_SourceFinalValidity.Adversary
      (Reduction.forsTcrProblem Link.vp (primsG (liftC g)) pkSeedDist)} {p : P3}
    (R : RealizesForsTcr pkSeedDist T p) :
    (cfAvg fun g => SM_DT_TCR_SourceFinalValidity.advantage (T g)) ≤ epsForsTcr γ p := by
  have h1 : (cfAvg fun g => SM_DT_TCR_SourceFinalValidity.advantage (T g)) =
      forsTcrAdvantage pkSeedDist R.A :=
    (cfAvg_of_evalDist_eq R.eq).trans (cfAdvantage_eq_idealAdv _)
  rw [h1]
  exact forsTcr_bound_128s pkSeedDist γ hγ R.A p.q₁ p.qch p.q₂ R.hq₁ R.hch R.hq₂

theorem RealizesTcr.avg {n : ℕ}
    {C : ∀ g : CF St Blk, SM_DT_TCR_Adversary
      (Reduction.thashArityProblemT Link.vp (primsG (liftC g)) pkSeedDist n)} {p : P5}
    (R : RealizesTcr pkSeedDist n C p) :
    (cfAvg fun g => SM_DT_TCR_Advantage (C g)) = tcrArityTAdvantage pkSeedDist n R.A :=
  (cfAvg_of_evalDist_eq R.eq).trans (cfAdvantage_eq_idealAdvT _)

theorem RealizesTcr.bound (hγ : ∀ s, Pr{let s' ← pkSeedDist}[s' = s] ≤ γ) {n : ℕ}
    (hn : n = 1 ∨ n = 2)
    {C : ∀ g : CF St Blk, SM_DT_TCR_Adversary
      (Reduction.thashArityProblemT Link.vp (primsG (liftC g)) pkSeedDist n)} {p : P5}
    (R : RealizesTcr pkSeedDist n C p) :
    (cfAvg fun g => SM_DT_TCR_Advantage (C g)) ≤ epsTcr γ p := by
  rw [R.avg]
  exact tcrArityT_bound_128s pkSeedDist n hn γ hγ R.A p.q₁ p.qch p.qc p.L p.q₂
    R.hq₁ R.hch R.hc R.hL R.hq₂

theorem RealizesTcr.bound_len (hγ : ∀ s, Pr{let s' ← pkSeedDist}[s' = s] ≤ γ) {n : ℕ}
    (hn : n = 35)
    {C : ∀ g : CF St Blk, SM_DT_TCR_Adversary
      (Reduction.thashArityProblemT Link.vp (primsG (liftC g)) pkSeedDist n)} {p : P5}
    (R : RealizesTcr pkSeedDist n C p) :
    (cfAvg fun g => SM_DT_TCR_Advantage (C g)) ≤ epsTcrLen γ p := by
  subst hn
  rw [R.avg]
  exact tcrLen_bound_128s pkSeedDist γ hγ R.A p.q₁ p.qch p.qc p.L p.q₂
    R.hq₁ R.hch R.hc R.hL R.hq₂

theorem RealizesTcr.bound_k (hγ : ∀ s, Pr{let s' ← pkSeedDist}[s' = s] ≤ γ) {n : ℕ}
    (hn : n = 14)
    {C : ∀ g : CF St Blk, SM_DT_TCR_Adversary
      (Reduction.thashArityProblemT Link.vp (primsG (liftC g)) pkSeedDist n)} {p : P5}
    (R : RealizesTcr pkSeedDist n C p) :
    (cfAvg fun g => SM_DT_TCR_Advantage (C g)) ≤ epsTcrK γ p := by
  subst hn
  rw [R.avg]
  exact tcrK_bound_128s pkSeedDist γ hγ R.A p.q₁ p.qch p.qc p.L p.q₂
    R.hq₁ R.hch R.hc R.hL R.hq₂

theorem RealizesUd.bound (hγ : ∀ s, Pr{let s' ← pkSeedDist}[s' = s] ≤ γ)
    {B : ∀ g : CF St Blk, SM_DT_UD_Adversary
      (Reduction.wotsUdProblem Link.vp (primsG (liftC g)) pkSeedDist)} {p : P5}
    (R : RealizesUd pkSeedDist B p) :
    (cfAvg fun g => SM_DT_UD_RealSuccess (B g)) ≤
      (cfAvg fun g => SM_DT_UD_IdealSuccess (B g)) + epsUd γ p := by
  have h1 : (cfAvg fun g => SM_DT_UD_RealSuccess (B g)) = wotsUdRealI pkSeedDist R.A :=
    cfAvg_of_evalDist_eq R.real
  have h2 : (cfAvg fun g => SM_DT_UD_IdealSuccess (B g)) = wotsUdIdealI pkSeedDist R.A :=
    cfAvg_of_evalDist_eq R.ideal
  rw [h1, h2]
  refine (wotsUd_bound_128s pkSeedDist γ hγ R.A p.q₁ p.qch p.qc p.L p.q₂
    R.hq₁ R.hch R.hc R.hL R.hq₂).trans (le_of_eq ?_)
  unfold epsUd
  ring

theorem RealizesPre.bound (hγ : ∀ s, Pr{let s' ← pkSeedDist}[s' = s] ≤ γ)
    {B : ∀ g : CF St Blk, SM_DT_PRE_Adversary
      (Reduction.wotsPreProblem Link.vp (primsG (liftC g)) pkSeedDist)} {p : P5}
    (R : RealizesPre pkSeedDist B p) :
    (cfAvg fun g => SM_DT_PRE_Advantage (B g)) ≤ epsPre γ p := by
  have h1 : (cfAvg fun g => SM_DT_PRE_Advantage (B g)) = wotsPreAdvantage pkSeedDist R.A :=
    cfAvg_of_evalDist_eq R.eq
  rw [h1]
  exact wotsPre_bound_128s pkSeedDist γ hγ R.A p.q₁ p.qch p.qc p.L p.q₂
    R.hq₁ R.hch R.hc R.hL R.hq₂

theorem RealizesWotsTcr.bound (hγ : ∀ s, Pr{let s' ← pkSeedDist}[s' = s] ≤ γ)
    {B : ∀ g : CF St Blk, SM_DT_TCR_Adversary
      (Reduction.wotsTcrProblemT Link.vp (primsG (liftC g)) pkSeedDist)} {p : P5}
    (R : RealizesWotsTcr pkSeedDist B p) :
    (cfAvg fun g => SM_DT_TCR_Advantage (B g)) ≤ epsTcr γ p := by
  have h1 : (cfAvg fun g => SM_DT_TCR_Advantage (B g)) = wotsTcrTAdvantage pkSeedDist R.A :=
    (cfAvg_of_evalDist_eq R.eq).trans (cfAdvantage_eq_idealAdvT _)
  rw [h1]
  exact wotsTcrT_bound_128s pkSeedDist γ hγ R.A p.q₁ p.qch p.qc p.L p.q₂
    R.hq₁ R.hch R.hc R.hL R.hq₂

end Realizes

/-! ## 5. The composition -/

private theorem compose_arith
    {adv r1 i1 a1 r2 i2 a2 c c' Ds S dv T T' X X' n R I aU p p' t t' : ℝ≥0∞}
    (h1 : r1 ≤ i1 + a1) (h2 : r2 ≤ i2 + a2) (h3 : Ds ≤ S + dv) (h4 : R ≤ I + aU)
    (hc : c ≤ c') (hT : T ≤ T') (hX : X ≤ X') (hp : p ≤ p') (ht : t ≤ t')
    (hfin : i1 + i2 + S + n * I ≠ ⊤)
    (h : adv + (i1 + i2 + S + n * I) ≤ r1 + r2 + c + (Ds + 3 * T) + X + n * R + p + t) :
    adv ≤ a1 + a2 + c' + (dv + 3 * T') + X' + n * aU + p' + t' := by
  have h' : adv + (i1 + i2 + S + n * I) ≤
      (a1 + a2 + c' + (dv + 3 * T') + X' + n * aU + p' + t') + (i1 + i2 + S + n * I) :=
    calc adv + (i1 + i2 + S + n * I)
        ≤ r1 + r2 + c + (Ds + 3 * T) + X + n * R + p + t := h
      _ ≤ (i1 + a1) + (i2 + a2) + c' + ((S + dv) + 3 * T') + X' + n * (I + aU) + p' + t' := by
          gcongr
      _ = _ := by ring
  exact (ENNReal.add_le_add_iff_right hfin).1 h'

theorem w_sub_two_128s : Link.vp.params.w - 2 = 14 := by decide

section Core

variable {pkSeedDist : ProbComp (Bytes 16)} {γ : ℝ≥0∞}

/-- **The composition, for arbitrary families.**  Let `a g` and adversaries `B₁ g, …, B₈ g`
satisfy the Reduction's linear inequality at the bundle over every table `g`.  If every family
is realised in the ideal-compression model and the table-averaged ITSR advantage is at most
`εI`, then the table average of `a` is at most the sum of the ideal-model bounds. -/
theorem ideal_bound_core (hγ : ∀ s, Pr{let s' ← pkSeedDist}[s' = s] ≤ γ)
    (a : CF St Blk → ℝ≥0∞)
    (B₁ : ∀ g : CF St Blk, PRFScheme.PRFAdversary
      ((primsG (liftC g)).PkSeed × Reduction.SkAdrs Link.vp) (primsG (liftC g)).Y)
    (B₂ : ∀ g : CF St Blk, Reduction.MsgPrfAdv (primsG (liftC g)))
    (B₃ : ∀ g : CF St Blk, KeyedHash.ITSRAdversary (Reduction.itsrProblem Link.vp (primsG (liftC g))))
    (D : ∀ g : CF St Blk, SM_DT_DSPR_SourceFinalValidity.Adversary
      (Reduction.forsDsprProblem Link.vp (primsG (liftC g)) pkSeedDist))
    (T : ∀ g : CF St Blk, SM_DT_TCR_SourceFinalValidity.Adversary
      (Reduction.forsTcrProblem Link.vp (primsG (liftC g)) pkSeedDist))
    (C₁ : ∀ g : CF St Blk, SM_DT_TCR_Adversary
      (Reduction.thashArityProblemT Link.vp (primsG (liftC g)) pkSeedDist 1))
    (C₂ : ∀ g : CF St Blk, SM_DT_TCR_Adversary
      (Reduction.thashArityProblemT Link.vp (primsG (liftC g)) pkSeedDist 2))
    (C₃ : ∀ g : CF St Blk, SM_DT_TCR_Adversary
      (Reduction.thashArityProblemT Link.vp (primsG (liftC g)) pkSeedDist Link.vp.params.len))
    (C₄ : ∀ g : CF St Blk, SM_DT_TCR_Adversary
      (Reduction.thashArityProblemT Link.vp (primsG (liftC g)) pkSeedDist Link.vp.params.k))
    (B₆ : ∀ g : CF St Blk, SM_DT_UD_Adversary
      (Reduction.wotsUdProblem Link.vp (primsG (liftC g)) pkSeedDist))
    (B₇ : ∀ g : CF St Blk, SM_DT_PRE_Adversary
      (Reduction.wotsPreProblem Link.vp (primsG (liftC g)) pkSeedDist))
    (B₈ : ∀ g : CF St Blk, SM_DT_TCR_Adversary
      (Reduction.wotsTcrProblemT Link.vp (primsG (liftC g)) pkSeedDist))
    (hlin : ∀ g, a g + Reduction.linearIdealSide (B₁ g) (B₂ g) (D g) (B₆ g) ≤
      Reduction.linearRealSide pkSeedDist (B₁ g) (B₂ g) (B₃ g) (D g) (T g) (C₁ g) (C₂ g) (C₃ g)
        (C₄ g) (B₆ g) (B₇ g) (B₈ g))
    {εI : ℝ≥0∞} (hI : (cfAvg fun g => KeyedHash.ITSRAdvantage (B₃ g)) ≤ εI)
    {q qO : ℕ} (R₁ : RealizesPrf B₁ q qO)
    {qm qOm mlen : ℕ} (R₂ : RealizesMsg B₂ qm qOm mlen)
    {pD : P3} (RD : RealizesDspr pkSeedDist D pD) (hD : pD.q₂ ≤ 2 ^ 126)
    {pT : P3} (RT : RealizesForsTcr pkSeedDist T pT)
    {pF pH pL pK : P5} (RF : RealizesTcr pkSeedDist 1 C₁ pF) (RH : RealizesTcr pkSeedDist 2 C₂ pH)
    (RL : RealizesTcr pkSeedDist Link.vp.params.len C₃ pL)
    (RK : RealizesTcr pkSeedDist Link.vp.params.k C₄ pK)
    {pU pP pW : P5} (RU : RealizesUd pkSeedDist B₆ pU) (RP : RealizesPre pkSeedDist B₇ pP)
    (RW : RealizesWotsTcr pkSeedDist B₈ pW) :
    cfAvg a ≤ epsPrf q qO + epsMsg qm qOm mlen + εI +
      (epsDspr γ pD + 3 * epsForsTcr γ pT) +
      (epsTcr γ pF + epsTcr γ pH + epsTcrLen γ pL + epsTcrK γ pK) +
      14 * epsUd γ pU + epsPre γ pP + epsTcr γ pW := by
  have havg := cfAvg_mono hlin
  simp only [Reduction.linearIdealSide, Reduction.linearRealSide, cfAvg_add, cfAvg_mul_left]
    at havg
  rw [w_sub_two_128s] at havg
  have i1 : (cfAvg fun g => Reduction.prfIdealPr (B₁ g)) ≤ 1 := by
    rw [show (cfAvg fun g => Reduction.prfIdealPr (B₁ g)) = _ from cfAvg_of_evalDist_eq R₁.ideal]
    exact cfAdvantage_le_one _
  have i2 : (cfAvg fun g => Reduction.msgIdealPr (B₂ g)) ≤ 1 := by
    rw [show (cfAvg fun g => Reduction.msgIdealPr (B₂ g)) = _ from cfAvg_of_evalDist_eq R₂.ideal]
    exact cfAdvantage_le_one _
  have i3 : (cfAvg fun g => SM_DT_DSPR_SourceFinalValidity.SPProbability (D g)) ≤ 1 := by
    rw [show (cfAvg fun g => SM_DT_DSPR_SourceFinalValidity.SPProbability (D g)) = _ from
      cfAvg_of_evalDist_eq RD.sp]
    exact cfAdvantage_le_one _
  have i4 : (cfAvg fun g => SM_DT_UD_IdealSuccess (B₆ g)) ≤ 1 := by
    rw [show (cfAvg fun g => SM_DT_UD_IdealSuccess (B₆ g)) = _ from cfAvg_of_evalDist_eq RU.ideal]
    exact cfAdvantage_le_one _
  have hfin : (cfAvg fun g => Reduction.prfIdealPr (B₁ g)) +
      (cfAvg fun g => Reduction.msgIdealPr (B₂ g)) +
      (cfAvg fun g => SM_DT_DSPR_SourceFinalValidity.SPProbability (D g)) +
      ((14 : ℕ) : ℝ≥0∞) * (cfAvg fun g => SM_DT_UD_IdealSuccess (B₆ g)) ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2
      ⟨(i1.trans_lt ENNReal.one_lt_top).ne, (i2.trans_lt ENNReal.one_lt_top).ne⟩,
      (i3.trans_lt ENNReal.one_lt_top).ne⟩,
      ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (i4.trans_lt ENNReal.one_lt_top).ne⟩
  have key := compose_arith R₁.bound R₂.bound (RD.bound hγ hD) (RU.bound hγ) hI (RT.bound hγ)
    (add_le_add (add_le_add (add_le_add (RF.bound hγ (Or.inl rfl)) (RH.bound hγ (Or.inr rfl)))
      (RL.bound_len hγ len_128s)) (RK.bound_k hγ k_128s))
    (RP.bound hγ) (RW.bound hγ) hfin havg
  simpa using key

end Core

section Main

variable (S : ForgerI)
  (optRand : ∀ g : CF St Blk, PublicKeyCore (primsG (liftC g)).core → ProbComp (primsG (liftC g)).Y)
  (pkSeedDist : ProbComp (Bytes 16))

/-- Table-averaged ITSR advantage of the Reduction's ITSR adversary built from the strong
forger (not bounded in this development: a hypothesis of `suf_ideal_bound`). -/
noncomputable def itsrSufI : ℝ≥0∞ :=
  cfAvg fun g => KeyedHash.ITSRAdvantage
    (Reduction.Lazy.bItsrL (S.typedS optRand pkSeedDist g))

/-- The same for the EUF forger. -/
noncomputable def itsrEufI : ℝ≥0∞ :=
  cfAvg fun g => KeyedHash.ITSRAdvantage
    (Reduction.Lazy.bItsrL (S.typedE optRand pkSeedDist g))

variable {S optRand pkSeedDist} {γ : ℝ≥0∞}

/-- **SUF-CMA security of SLH-DSA-SHA2-128s (byte level) in the ideal-compression-function
model**, conditional on the realisability of the Reduction's twelve adversaries as ideal-model
adversaries (eleven realisers and the bound `εI` on the averaged ITSR advantage).  With
`T g := S.typedS optRand pkSeedDist g` the typed forger at the table `g`. -/
theorem suf_ideal_bound (hγ : ∀ s, Pr{let s' ← pkSeedDist}[s' = s] ≤ γ)
    {εI : ℝ≥0∞} (hI : itsrSufI S optRand pkSeedDist ≤ εI)
    {q qO : ℕ} (R₁ : RealizesPrf
      (fun g => Reduction.bPrfWC Reduction.sufCheck (S.typedS optRand pkSeedDist g)) q qO)
    {qm qOm mlen : ℕ} (R₂ : RealizesMsg
      (fun g => Reduction.Lazy.bPrfMsgWL Reduction.sufCheck (S.typedS optRand pkSeedDist g))
      qm qOm mlen)
    {pD : P3} (RD : RealizesDspr pkSeedDist
      (fun g => Reduction.toDspr (Reduction.Lazy.bOpenPreS (S.typedS optRand pkSeedDist g))) pD)
    (hD : pD.q₂ ≤ 2 ^ 126)
    {pT : P3} (RT : RealizesForsTcr pkSeedDist
      (fun g => Reduction.toTcr (Reduction.Lazy.bOpenPreS (S.typedS optRand pkSeedDist g))) pT)
    {pF pH pL pK : P5}
    (RF : RealizesTcr pkSeedDist 1
      (fun g => Reduction.bTcrArM 1 (S.typedS optRand pkSeedDist g)) pF)
    (RH : RealizesTcr pkSeedDist 2
      (fun g => Reduction.bTcrArM 2 (S.typedS optRand pkSeedDist g)) pH)
    (RL : RealizesTcr pkSeedDist Link.vp.params.len
      (fun g => Reduction.bTcrArM Link.vp.params.len (S.typedS optRand pkSeedDist g)) pL)
    (RK : RealizesTcr pkSeedDist Link.vp.params.k
      (fun g => Reduction.bTcrArM Link.vp.params.k (S.typedS optRand pkSeedDist g)) pK)
    {pU pP pW : P5}
    (RU : RealizesUd pkSeedDist (fun g => Reduction.rUd pkSeedDist
      (Reduction.Lazy.bWotsS (S.typedS optRand pkSeedDist g))) pU)
    (RP : RealizesPre pkSeedDist (fun g => Reduction.rPre pkSeedDist
      (Reduction.Lazy.bWotsS (S.typedS optRand pkSeedDist g))) pP)
    (RW : RealizesWotsTcr pkSeedDist (fun g => Reduction.rTcrT pkSeedDist
      (Reduction.Lazy.bWotsS (S.typedS optRand pkSeedDist g))) pW) :
    sufI S optRand pkSeedDist ≤ epsPrf q qO + epsMsg qm qOm mlen + εI +
      (epsDspr γ pD + 3 * epsForsTcr γ pT) +
      (epsTcr γ pF + epsTcr γ pH + epsTcrLen γ pL + epsTcrK γ pK) +
      14 * epsUd γ pU + epsPre γ pP + epsTcr γ pW := by
  rw [sufI_eq_cfAvg]
  exact ideal_bound_core hγ _ _ _ _ _ _ _ _ _ _ _ _ _
    (fun g => Reduction.slhdsa_bytes_suf_cma_linear (structuralG g) (S.sufInst optRand pkSeedDist g))
    hI R₁ R₂ RD hD RT RF RH RL RK RU RP RW

/-- **EUF-CMA security of SLH-DSA-SHA2-128s (byte level) in the ideal-compression-function
model**, conditional on the realisability of the Reduction's twelve EUF adversaries. -/
theorem euf_ideal_bound (hγ : ∀ s, Pr{let s' ← pkSeedDist}[s' = s] ≤ γ)
    {εI : ℝ≥0∞} (hI : itsrEufI S optRand pkSeedDist ≤ εI)
    {q qO : ℕ} (R₁ : RealizesPrf
      (fun g => Reduction.bPrfC (S.typedE optRand pkSeedDist g)) q qO)
    {qm qOm mlen : ℕ} (R₂ : RealizesMsg
      (fun g => Reduction.Lazy.bPrfMsgL (S.typedE optRand pkSeedDist g)) qm qOm mlen)
    {pD : P3} (RD : RealizesDspr pkSeedDist
      (fun g => Reduction.toDspr (Reduction.Lazy.bOpenPreS (S.typedE optRand pkSeedDist g))) pD)
    (hD : pD.q₂ ≤ 2 ^ 126)
    {pT : P3} (RT : RealizesForsTcr pkSeedDist
      (fun g => Reduction.toTcr (Reduction.Lazy.bOpenPreS (S.typedE optRand pkSeedDist g))) pT)
    {pF pH pL pK : P5}
    (RF : RealizesTcr pkSeedDist 1
      (fun g => Reduction.bTcrArM 1 (S.typedE optRand pkSeedDist g)) pF)
    (RH : RealizesTcr pkSeedDist 2
      (fun g => Reduction.bTcrArM 2 (S.typedE optRand pkSeedDist g)) pH)
    (RL : RealizesTcr pkSeedDist Link.vp.params.len
      (fun g => Reduction.bTcrArM Link.vp.params.len (S.typedE optRand pkSeedDist g)) pL)
    (RK : RealizesTcr pkSeedDist Link.vp.params.k
      (fun g => Reduction.bTcrArM Link.vp.params.k (S.typedE optRand pkSeedDist g)) pK)
    {pU pP pW : P5}
    (RU : RealizesUd pkSeedDist (fun g => Reduction.rUd pkSeedDist
      (Reduction.Lazy.bWotsS (S.typedE optRand pkSeedDist g))) pU)
    (RP : RealizesPre pkSeedDist (fun g => Reduction.rPre pkSeedDist
      (Reduction.Lazy.bWotsS (S.typedE optRand pkSeedDist g))) pP)
    (RW : RealizesWotsTcr pkSeedDist (fun g => Reduction.rTcrT pkSeedDist
      (Reduction.Lazy.bWotsS (S.typedE optRand pkSeedDist g))) pW) :
    eufI S optRand pkSeedDist ≤ epsPrf q qO + epsMsg qm qOm mlen + εI +
      (epsDspr γ pD + 3 * epsForsTcr γ pT) +
      (epsTcr γ pF + epsTcr γ pH + epsTcrLen γ pL + epsTcrK γ pK) +
      14 * epsUd γ pU + epsPre γ pP + epsTcr γ pW := by
  rw [eufI_eq_cfAvg]
  exact ideal_bound_core hγ _ _ _ _ _ _ _ _ _ _ _ _ _
    (fun g => Reduction.slhdsa_bytes_euf_cma_linear (structuralG g) (S.eufInst optRand pkSeedDist g))
    hI R₁ R₂ RD hD RT RF RH RL RK RU RP RW

end Main

end Ideal

#print axioms Ideal.structuralG
#print axioms Ideal.bytesAlg_realCF
#print axioms Ideal.cfAvg_prTrue
#print axioms Ideal.sufI_eq_cfAvg
#print axioms Ideal.ideal_bound_core
#print axioms Ideal.suf_ideal_bound
#print axioms Ideal.euf_ideal_bound
