import Reduction.PrfDomain
import Reduction.NonVacuity
import Reduction.Instance128s
import Link.Security
import Link.Hash

/-!
# The domain-restricted `PRF` game: non-vacuity, and the SHA2-128s facts

1. **Non-vacuity of the new game** (`skPrfC`, `Reduction.PrfDomain`).  It can be lost
   (`prfC_const_adv_zero`: a constant distinguisher has advantage `0`, for every bundle) and, on
   the toy bundle whose `PRF` is constant, won (`prfTesterC_adv`, `toy_prfC`: advantage `1/2`).
2. **The out-of-domain artefact of the SHA-2 bundle is outside the new domain.**
   * `canonical_256`: the address `⟨256,0,0,0,0,0⟩` *is* FIPS-canonical (four-byte layer), so a
     canonical-only domain would not have removed the artefact;
   * `not_skDom_256`, `not_skDom_badAdrs`, `not_skDom_of_not_sha2Domain`: no address outside the
     checked `ADRSc` domain (in particular neither `⟨256,0,0,0,0,0⟩` nor `Link.badAdrs`) is an
     element of the new domain, for every parameter set with the approved address widths;
   * `sha2PRFChecked_ok_128s`, `prf_128s_spec`, `prf_128s_thash`: on the new domain the SHA-2 `PRF`
     never takes the fallback branch; it is `Trunc_16(SHA-256(PK.seed ‖ 0^48 ‖ ADRSc ‖ SK.seed))`.
3. **The old game is broken at 128s** (`sha2PRF_eq_zero_of_not_sha2Domain`, `prf_256_eq_zero`,
   `skPrf_broken_128s`, `skPrf_broken_128s_half`): the one-query distinguisher `prfTester` at
   `⟨256,0,0,0,0,0⟩` has advantage `1 − 1/|Y| ≥ 1/2` against `skPrf Link.vp Link.prims`.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security SLHDSA.Concrete ENNReal MeasureTheory

namespace Reduction

set_option linter.unusedSectionVars false

/-! ## Non-vacuity of the new game -/

section Generic

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed]

/-- The new PRF game can be lost: a constant distinguisher has advantage `0`. -/
theorem prfC_const_adv_zero :
    (skPrfC vp prims).prfAdvantage
      (pure true :
        OracleComp (PRFScheme.PRFOracleSpec (prims.PkSeed × SkAdrs vp) prims.Y) Bool) = 0 := by
  have h1 : 𝒟[(skPrfC vp prims).prfRealExperiment
      (pure true :
        OracleComp (PRFScheme.PRFOracleSpec (prims.PkSeed × SkAdrs vp) prims.Y) Bool)]
      {true} = 1 :=
    prTrue_eq_one_of_support _ (by
      intro x hx; simp [PRFScheme.prfRealExperiment] at hx; exact hx.2)
  have h2 : 𝒟[PRFScheme.prfIdealExperiment
      (pure true :
        OracleComp (PRFScheme.PRFOracleSpec (prims.PkSeed × SkAdrs vp) prims.Y) Bool)]
      {true} = 1 :=
    prTrue_eq_one_of_support _ (by
      intro x hx; simp [PRFScheme.prfIdealExperiment] at hx; exact hx)
  simp [PRFScheme.prfAdvantage, Measure.boolDist, h1, h2]

/-- The distinguisher that queries one point of the new domain and tests the answer against `c`. -/
def prfTesterC (pk : prims.PkSeed) (a : SkAdrs vp) (c : prims.Y) :
    OracleComp (PRFScheme.PRFOracleSpec (prims.PkSeed × SkAdrs vp) prims.Y) Bool := do
  let y ← PRFScheme.functionQuery (pk, a)
  pure (decide (y = c))

/-- The new PRF game can be won: if `PRF(pk, ·, a)` is the constant `c` at an address `a` of the
domain, `prfTesterC` has advantage `1 − 1/|Y|`. -/
theorem prfTesterC_adv [Fintype prims.Y] (pk : prims.PkSeed) (a : SkAdrs vp) (c : prims.Y)
    (hconst : ∀ k, prims.PRF pk k a.val = c) :
    (skPrfC vp prims).prfAdvantage (prfTesterC pk a c) =
      1 - (Fintype.card prims.Y : ℝ≥0∞)⁻¹ := by
  have h1 : 𝒟[(skPrfC vp prims).prfRealExperiment (prfTesterC pk a c)] {true} = 1 := by
    apply prTrue_eq_one_of_support
    intro x hx
    simp [PRFScheme.prfRealExperiment, prfTesterC, skPrfC, hconst] at hx
    exact hx
  have h2 : 𝒟[PRFScheme.prfIdealExperiment (prfTesterC pk a c)] {true} =
      (Fintype.card prims.Y : ℝ≥0∞)⁻¹ := by
    simp [PRFScheme.prfIdealExperiment, prfTesterC, PRFScheme.functionQuery]
    exact prTrue_map_decide_uniform c
  rw [PRFScheme.prfAdvantage, Measure.boolDist, h1, h2, absDiff_one_inv_card]

end Generic

/-- The domain is inhabited for every parameter set: the `WOTS_PRF` address of layer `0`,
tree `0`, key pair `0`, chain `0`. -/
def skAdrs0 (vp : ValidatedParams) : SkAdrs vp :=
  ⟨⟨0, 0, 5, 0, 0, 0⟩, by decide, .inl rfl, vp.valid.d_pos, by positivity⟩

/-- On the toy bundle (constant `PRF`) the new game is won with advantage `1/2`. -/
theorem toy_prfC (vp : ValidatedParams) :
    ∃ B, (skPrfC vp (toyPrims vp.params)).prfAdvantage B = 2⁻¹ := by
  refine ⟨_, (prfTesterC_adv (prims := toyPrims vp.params) () (skAdrs0 vp) false
    fun _ => rfl).trans ?_⟩
  change 1 - ((Fintype.card Bool : ℕ) : ℝ≥0∞)⁻¹ = 2⁻¹
  rw [Fintype.card_bool]
  exact ENNReal.one_sub_inv_two

/-- On the toy bundle the new game is lost by the constant distinguisher. -/
theorem toy_prfC_lost (vp : ValidatedParams) :
    ∃ B, (skPrfC vp (toyPrims vp.params)).prfAdvantage B = 0 :=
  ⟨_, prfC_const_adv_zero⟩

/-! ## The SHA-2 fallback is outside the new domain -/

/-- Under the approved (compressed) address widths, every address of the new domain is in the
checked SHA-2 `ADRSc` domain. -/
theorem SkDom.sha2Domain {vp : ValidatedParams} (hb : ApprovedAddressBounds vp.params) {a : Adrs}
    (h : SkDom vp a) : Sha2Domain a :=
  sha2Domain_of_addressFacts hb h.addressFacts

/-- No address outside the checked `ADRSc` domain belongs to the new domain. -/
theorem not_skDom_of_not_sha2Domain {vp : ValidatedParams} (hb : ApprovedAddressBounds vp.params)
    {a : Adrs} (h : ¬ Sha2Domain a) : ¬ SkDom vp a :=
  fun hd => h (hd.sha2Domain hb)

/-- The old attack address is FIPS-canonical (the full `ADRS` has a four-byte layer word): a
domain cut out by `isCanonical` alone would still contain it. -/
theorem canonical_256 : (⟨256, 0, 0, 0, 0, 0⟩ : Adrs).isCanonical = true := by decide

/-- The old attack address is outside the checked `ADRSc` domain (layer `256` needs two bytes). -/
theorem not_sha2Domain_256 : ¬ Sha2Domain (⟨256, 0, 0, 0, 0, 0⟩ : Adrs) :=
  fun h => absurd h.2.1 (by decide)

/-- The old attack address is not an element of the new domain, for any parameter set: its type is
`WOTS_HASH`, not a secret-key type. -/
theorem not_skDom_256 (vp : ValidatedParams) : ¬ SkDom vp ⟨256, 0, 0, 0, 0, 0⟩ :=
  fun h => absurd h.2.1 (by decide)

/-- Nor is the secret-key-typed variant `Link.badAdrs = ⟨256,0,5,0,0,0⟩` of `Link.not_hprf`. -/
theorem not_skDom_badAdrs : ¬ SkDom Link.vp Link.badAdrs :=
  not_skDom_of_not_sha2Domain (fipsApprovedAddressBounds Link.S128)
    fun h => absurd h.2.1 (by decide)

/-- Every address of the new domain at SHA2-128s is in `Link.Dom`. -/
theorem skAdrs_dom_128s (a : SkAdrs Link.vp) : Link.Dom a.val :=
  a.2.sha2Domain (fipsApprovedAddressBounds Link.S128)

private theorem prefixChecked_ok' (b : ByteArray) (n : ℕ) (h : n ≤ b.size) :
    ∃ v : Bytes n, byteArrayPrefixChecked b n = .ok v := by
  have hraw : (b.extract 0 n).toList = b.data.toList.take n := by
    rw [ByteArray.toList_eq_toList_data, ByteArray.data_extract, Array.toList_extract]
    simp
  have hl : (b.extract 0 n).toList.length = n := by
    rw [hraw, List.length_take]
    have : b.data.toList.length = b.size := by rw [Array.length_toList]; rfl
    omega
  exact ⟨⟨(b.extract 0 n).toList.toArray, by simpa using hl⟩, by
    simp [byteArrayPrefixChecked, decodeExact, hl]⟩

/-- **No fallback on the new domain.**  For every address of the new domain, the checked SHA-2
`PRF` succeeds, on the proof-carrying compressed address, and `Link.prims.PRF` is its value:
the first 16 bytes of `SHA-256(PK.seed ‖ 0^48 ‖ ADRSc ‖ SK.seed)`. -/
theorem sha2PRFChecked_ok_128s (pk k : Link.Node) (a : SkAdrs Link.vp) :
    sha2PRFChecked pk k a.val = .ok (Link.prims.PRF pk k a.val) ∧
    byteArrayPrefixChecked (VCVio.Algorithms.Sha2.sha256
        (sha2Prefix256 pk ⟨a.val, (skAdrs_dom_128s a).1, (skAdrs_dom_128s a).2.1,
          (skAdrs_dom_128s a).2.2⟩ ++ bytesToByteArray k)) 16 =
      .ok (Link.prims.PRF pk k a.val) := by
  have h := skAdrs_dom_128s a
  obtain ⟨v, hv⟩ := prefixChecked_ok' (VCVio.Algorithms.Sha2.sha256
    (sha2Prefix256 pk ⟨a.val, h.1, h.2.1, h.2.2⟩ ++ bytesToByteArray k)) 16 (by simp)
  have hc : sha2PRFChecked pk k a.val = .ok v := by
    simp only [sha2PRFChecked, Sha2Address.ofAdrs, h.1, h.2.1, h.2.2, dite_true]
    exact hv
  have e : Link.prims.PRF pk k a.val = v := by
    show checkedNodeOrZero (sha2PRFChecked pk k a.val) = v
    rw [hc]; rfl
  rw [e]
  exact ⟨hc, hv⟩

/-- On the new domain, `Link.prims.PRF` is the FIPS 205 transcription `Spec.PRF`
(`Trunc_16(SHA-256(PK.seed ‖ 0^48 ‖ ADRSc ‖ SK.seed))`). -/
theorem prf_128s_spec (pk k : Link.Node) (a : SkAdrs Link.vp) :
    Link.nd (Link.prims.PRF pk k a.val) = Spec.PRF (Link.nd pk) (Link.nd k) (Link.adr a.val) :=
  Link.PRF_eq pk k a.val (skAdrs_dom_128s a)

/-- On the new domain, `Link.prims.PRF` is the bundle's tweakable hash at the (non-fallback)
compressed address key applied to `[SK.seed]`. -/
theorem prf_128s_thash (pk k : Link.Node) (a : SkAdrs Link.vp) :
    Link.prims.PRF pk k a.val = Link.prims.Thash pk (Link.prims.adrsToKey a.val) [k] :=
  (Link.hprf_dom pk k a.val (skAdrs_dom_128s a)).symm

/-! ## The old game is broken at SHA2-128s -/

/-- Outside the checked `ADRSc` domain the SHA-2 `PRF` is the all-zero node, for every key. -/
theorem sha2PRF_eq_zero_of_not_sha2Domain (p : Params) (pk k : Bytes p.n) {a : Adrs}
    (h : ¬ Sha2Domain a) : (sha2Primitives p).PRF pk k a = zeroBytes p.n := by
  show checkedNodeOrZero (sha2PRFChecked pk k a) = _
  unfold Sha2Domain at h
  unfold sha2PRFChecked Sha2Address.ofAdrs
  by_cases h1 : a.isCanonical = true
  · by_cases h2 : Adrs.Fits 1 a.layer = true
    · by_cases h3 : Adrs.Fits 8 a.tree = true
      · exact absurd ⟨h1, h2, h3⟩ h
      · simp only [h1, h2, h3, dite_true]; rfl
    · simp only [h1, h2, dite_true]; rfl
  · simp only [h1]; rfl

/-- `PRF(pk, k, ⟨256,0,0,0,0,0⟩) = 0^16` for all `pk`, `k` at SHA2-128s. -/
theorem prf_256_eq_zero (pk k : Link.Node) :
    Link.prims.PRF pk k ⟨256, 0, 0, 0, 0, 0⟩ = zeroBytes 16 :=
  sha2PRF_eq_zero_of_not_sha2Domain Link.vp.params pk k not_sha2Domain_256

/-- Finiteness of the node type at 128s (needed only to state `1/|Y|`). -/
@[reducible] def fintypeY128 : Fintype Link.prims.Y := inferInstanceAs (Fintype (Vector UInt8 16))

attribute [local instance] fintypeY128

/-- **The unrestricted PRF assumption is false at SLH-DSA-SHA2-128s.**  The one-query
distinguisher at the (canonical, out-of-`ADRSc`-domain) address `⟨256,0,0,0,0,0⟩` has advantage
`1 − 1/|Y|` against `skPrf Link.vp Link.prims`. -/
theorem skPrf_broken_128s (pk : Link.prims.PkSeed) :
    (skPrf Link.vp Link.prims).prfAdvantage
        (prfTester (prims := Link.prims) pk ⟨256, 0, 0, 0, 0, 0⟩ (zeroBytes 16)) =
      1 - (Fintype.card Link.prims.Y : ℝ≥0∞)⁻¹ :=
  prfTester_adv (vp := Link.vp) (prims := Link.prims) pk _ _ fun k => prf_256_eq_zero pk k

/-- In particular that advantage is at least `1/2`. -/
theorem skPrf_broken_128s_half (pk : Link.prims.PkSeed) :
    2⁻¹ ≤ (skPrf Link.vp Link.prims).prfAdvantage
        (prfTester (prims := Link.prims) pk ⟨256, 0, 0, 0, 0, 0⟩ (zeroBytes 16)) := by
  rw [skPrf_broken_128s]
  have hcard : (2 : ℝ≥0∞) ≤ (Fintype.card Link.prims.Y : ℝ≥0∞) := by
    have : 1 < Fintype.card Link.prims.Y :=
      Fintype.one_lt_card_iff.2 ⟨(Vector.replicate 16 0 : Vector UInt8 16),
        (Vector.replicate 16 1 : Vector UInt8 16),
        show (Vector.replicate 16 0 : Vector UInt8 16) ≠ Vector.replicate 16 1 from by decide⟩
    exact_mod_cast this
  calc (2⁻¹ : ℝ≥0∞) = 1 - 2⁻¹ := ENNReal.one_sub_inv_two.symm
    _ ≤ 1 - (Fintype.card Link.prims.Y : ℝ≥0∞)⁻¹ :=
      tsub_le_tsub_left (ENNReal.inv_le_inv.2 hcard) 1

/-- Step 1 on the secret-key address domain at SLH-DSA-SHA2-128s (no hypothesis). -/
theorem stepPRFC_128s
    (optRand : PublicKeyCore Link.prims.core → ProbComp Link.prims.Y)
    (pkSeedDist : ProbComp Link.prims.PkSeed)
    (A : Forger Link.vp Link.prims optRand pkSeedDist) :
    prTrue (g0 A) ≤ prTrue (g1 A) + (skPrfC Link.vp Link.prims).prfAdvantage (bPrfC A) :=
  stepPRFC structural_128s A

#print axioms Reduction.stepPRFC_128s
#print axioms Reduction.prfC_const_adv_zero
#print axioms Reduction.prfTesterC_adv
#print axioms Reduction.toy_prfC
#print axioms Reduction.not_skDom_256
#print axioms Reduction.not_skDom_badAdrs
#print axioms Reduction.canonical_256
#print axioms Reduction.sha2PRFChecked_ok_128s
#print axioms Reduction.prf_128s_spec
#print axioms Reduction.prf_128s_thash
#print axioms Reduction.prf_256_eq_zero
#print axioms Reduction.skPrf_broken_128s
#print axioms Reduction.skPrf_broken_128s_half

end Reduction
