import Ideal.Games.Ud
import Ideal.Inst.WotsPre128

/-!
# SM-UD of the SLH-DSA-SHA2-128s `F` in the ideal-compression model

The Reduction's SM-UD problem on `F` (the WOTS+ chains),
`Reduction.wotsUdProblem Link.vp prims pkSeedDist`, taken at the generic SHA-256 primitives
`primsG (liftC g)` over a compression table `g`, is the SM-UD problem of the Merkle–Damgård
family `FWotsPre128 pkSeedDist` (the family of the SM-PRE instance: same hash, collection and
target cap) with `emb = id` and uniform hidden inputs / ideal responses
(`wotsUdProblem_eq_udProb`); at `g = realCF` it is the Reduction's own problem at `Link.prims`
(`wotsUdProblem_realCF`).

`wotsUdRealI`, `wotsUdIdealI` are VCVio's `SM_DT_UD_RealSuccess`, `SM_DT_UD_IdealSuccess` on the
Reduction's problem, averaged over a uniform table.  `Ideal.ud_bound` gives the one-sided bound
(the form consumed by the Reduction's linear headline)

`wotsUdRealI ≤ wotsUdIdealI + q₂/2^128 + 2·q₁·γ + 2·(2 q₁ + (qch + qc)(1 + 2 L) + 1)/2^256`,

and `Ideal.ud_bound_ge` the reverse inequality with the same error.
-/

open OracleComp OracleSpec ENNReal

namespace Ideal

open TweakableHash SLHDSA

/-- The SM-UD experiment depends on the problem only through its components; adversaries with
the same components against problems with equal hash functions have the same experiment. -/
theorem SM_DT_UD_Experiment_congr {ι PkSeed Tweak M M' Y : Type}
    {iT iT' : DecidableEq Tweak} (world : SM_DT_UD_World)
    (sg : ProbComp PkSeed) (e e' : PkSeed → Tweak → M → Y) (emb : M' → M)
    (hemb hemb' : Function.Injective emb) (ig : ProbComp M') (og : ProbComp Y) (Msg : ι → Type)
    (ce ce' : (i : ι) → PkSeed → Tweak → Msg i → Y) (N : ℕ) (he : e = e') (hc : ce = ce')
    (State : Type)
    (pick : OracleComp (unifSpec + (SM_DT_UD_challengeSpec Tweak Y +
      (((i : ι) × Tweak × Msg i) →ₒ Option Y))) State)
    (distinguish : State → PkSeed → ProbComp Bool) :
    @SM_DT_UD_Experiment ι PkSeed Tweak M M' Y iT world
        { th := { seedGen := sg, eval := e }, emb := emb, emb_injective := hemb,
          inputGen := ig, outputGen := og,
          thColl := { Msg := Msg, eval := ce }, numTargets := N }
        { State := State, pick := pick, distinguish := distinguish } =
      @SM_DT_UD_Experiment ι PkSeed Tweak M M' Y iT' world
        { th := { seedGen := sg, eval := e' }, emb := emb, emb_injective := hemb',
          inputGen := ig, outputGen := og,
          thColl := { Msg := Msg, eval := ce' }, numTargets := N }
        { State := State, pick := pick, distinguish := distinguish } := by
  subst he hc
  obtain rfl := Subsingleton.elim iT iT'
  rfl

/-- The Reduction's SM-UD problem on `F` at the generic primitives over the table `g` is the
SM-UD problem of `FWotsPre128` at `g` (hidden inputs `M' = Bytes 16`, `emb = id`, uniform
`inputGen` and `outputGen`). -/
theorem wotsUdProblem_eq_udProb (pkSeedDist : ProbComp (Bytes 16)) (g : CF St Blk) :
    Reduction.wotsUdProblem Link.vp (primsG (liftC g)) pkSeedDist =
      @THFam.udProb St Blk (Bytes 16) (Bytes 22) (Bytes 16) (Bytes 16) (Bytes 16) Unit
        (FWotsPre128 pkSeedDist) sampY128 sampY128 id Function.injective_id g := by
  have h : (primsG (liftC g)).Thash =
      fun pk a xs => out16 (keyedChain IV128 sb128 g pk (tblocks a xs)) := by
    funext pk a xs
    exact primsG_Thash_shape g pk a xs
  show ({ th := { seedGen := pkSeedDist, eval := fun pk t x => (primsG (liftC g)).Thash pk t [x] },
          emb := id, emb_injective := Function.injective_id,
          inputGen := @uniformSample (Bytes 16) sampY128,
          outputGen := @uniformSample (Bytes 16) sampY128,
          thColl := { Msg := fun _ => List (Bytes 16), eval := fun _ => (primsG (liftC g)).Thash },
          numTargets := Reduction.wotsChainTargets Link.vp } :
        SM_DT_UD_Problem Unit (Bytes 16) (Bytes 22) (Bytes 16) (Bytes 16) (Bytes 16)) = _
  rw [h]
  simp only [THFam.udProb, THFam.coll, FWotsPre128]
  rfl

/-- At the real compression function the problem is the Reduction's own. -/
theorem wotsUdProblem_realCF (pkSeedDist : ProbComp (Bytes 16)) :
    Reduction.wotsUdProblem Link.vp (primsG (liftC realCF)) pkSeedDist =
      Reduction.wotsUdProblem Link.vp Link.prims pkSeedDist := by
  have h := congrArg (fun c : CompressFn =>
    (show SM_DT_UD_Problem Unit (Bytes 16) (Bytes 22) (Bytes 16) (Bytes 16) (Bytes 16) from
      Reduction.wotsUdProblem Link.vp (primsG c) pkSeedDist))
    liftC_realCF
  exact h

/-- Ideal-model adversaries against the Reduction's SM-UD game on `F`. -/
abbrev WotsUdAdv128 (pkSeedDist : ProbComp (Bytes 16)) := UdAdv (FWotsPre128 pkSeedDist)

/-- The adversary against the Reduction's SM-UD problem on `F` at the table `g`. -/
def instWU {pkSeedDist : ProbComp (Bytes 16)} (A : WotsUdAdv128 pkSeedDist) (g : CF St Blk) :
    SM_DT_UD_Adversary (Reduction.wotsUdProblem Link.vp (primsG (liftC g)) pkSeedDist) where
  State := A.State
  pick := simulateQ (instImpl g) A.pick
  distinguish := fun st pk => simulateQ (instImpl₀ g) (A.distinguish st pk)

/-- Real-world success probability in the Reduction's SM-UD game on `F` in the
ideal-compression model: `SM_DT_UD_RealSuccess (instWU A g)` (the Reduction's experiment at the
primitives built from `g`, the adversary's compression queries answered by `g`) averaged over a
uniformly random table `g`, i.e.
`𝒟[do let g ← $ᵗ (CF St Blk); SM_DT_UD_Experiment .real (instWU A g)] {true}`. -/
noncomputable def wotsUdRealI (pkSeedDist : ProbComp (Bytes 16))
    (A : WotsUdAdv128 pkSeedDist) : ℝ≥0∞ :=
  cfAdvantage fun g => SM_DT_UD_Experiment .real (instWU A g)

/-- Ideal-world success probability, likewise:
`𝒟[do let g ← $ᵗ (CF St Blk); SM_DT_UD_Experiment .ideal (instWU A g)] {true}`. -/
noncomputable def wotsUdIdealI (pkSeedDist : ProbComp (Bytes 16))
    (A : WotsUdAdv128 pkSeedDist) : ℝ≥0∞ :=
  cfAdvantage fun g => SM_DT_UD_Experiment .ideal (instWU A g)

theorem udRealI_eq_cfAdvantage {St Blk PkSeed Tweak M M' Y ι : Type} [DecidableEq Tweak]
    [SampleableType M'] [SampleableType Y] [SampleableType (CF St Blk)]
    (F : THFam St Blk PkSeed Tweak M Y ι) (emb : M' → M) (hemb : Function.Injective emb)
    (A : UdAdv F) :
    udRealI F emb hemb A =
      cfAdvantage fun g => SM_DT_UD_Experiment .real (A.inst emb hemb g) := rfl

theorem udIdealI_eq_cfAdvantage {St Blk PkSeed Tweak M M' Y ι : Type} [DecidableEq Tweak]
    [SampleableType M'] [SampleableType Y] [SampleableType (CF St Blk)]
    (F : THFam St Blk PkSeed Tweak M Y ι) (emb : M' → M) (hemb : Function.Injective emb)
    (A : UdAdv F) :
    udIdealI F emb hemb A =
      cfAdvantage fun g => SM_DT_UD_Experiment .ideal (A.inst emb hemb g) := rfl

/-- The Reduction's experiment at the instantiated adversary is the generic one. -/
theorem wotsUd_experiment_eq (world : SM_DT_UD_World) (pkSeedDist : ProbComp (Bytes 16))
    (A : WotsUdAdv128 pkSeedDist) (g : CF St Blk) :
    SM_DT_UD_Experiment world (instWU A g) =
      SM_DT_UD_Experiment world
        (@UdAdv.inst St Blk (Bytes 16) (Bytes 22) (Bytes 16) (Bytes 16) (Bytes 16) Unit
          (FWotsPre128 pkSeedDist) sampY128 sampY128 A id Function.injective_id g) := by
  have h : (primsG (liftC g)).Thash =
      fun pk a xs => out16 (keyedChain IV128 sb128 g pk (tblocks a xs)) := by
    funext pk a xs
    exact primsG_Thash_shape g pk a xs
  have he : (fun (pk : Bytes 16) (t : Bytes 22) (x : Bytes 16) =>
      (primsG (liftC g)).Thash pk t [x]) = (FWotsPre128 pkSeedDist).evalT g := by
    rw [h]; rfl
  have hc : (fun (_ : Unit) => (primsG (liftC g)).Thash) = (FWotsPre128 pkSeedDist).evalC g := by
    rw [h]; rfl
  have e1 : SM_DT_UD_Experiment world (instWU A g) =
      @SM_DT_UD_Experiment Unit (Bytes 16) (Bytes 22) (Bytes 16) (Bytes 16) (Bytes 16) _ world
        { th := { seedGen := pkSeedDist,
                  eval := fun pk t x => (primsG (liftC g)).Thash pk t [x] },
          emb := id, emb_injective := Function.injective_id,
          inputGen := @uniformSample (Bytes 16) sampY128,
          outputGen := @uniformSample (Bytes 16) sampY128,
          thColl := { Msg := fun _ => List (Bytes 16),
                      eval := fun _ => (primsG (liftC g)).Thash },
          numTargets := Reduction.wotsChainTargets Link.vp }
        { State := A.State, pick := simulateQ (instImpl g) A.pick,
          distinguish := fun st pk => simulateQ (instImpl₀ g) (A.distinguish st pk) } := rfl
  have e2 : SM_DT_UD_Experiment world
        (@UdAdv.inst St Blk (Bytes 16) (Bytes 22) (Bytes 16) (Bytes 16) (Bytes 16) Unit
          (FWotsPre128 pkSeedDist) sampY128 sampY128 A id Function.injective_id g) =
      @SM_DT_UD_Experiment Unit (Bytes 16) (Bytes 22) (Bytes 16) (Bytes 16) (Bytes 16) _ world
        { th := { seedGen := pkSeedDist, eval := (FWotsPre128 pkSeedDist).evalT g },
          emb := id, emb_injective := Function.injective_id,
          inputGen := @uniformSample (Bytes 16) sampY128,
          outputGen := @uniformSample (Bytes 16) sampY128,
          thColl := { Msg := fun _ => List (Bytes 16),
                      eval := (FWotsPre128 pkSeedDist).evalC g },
          numTargets := Reduction.wotsChainTargets Link.vp }
        { State := A.State, pick := simulateQ (instImpl g) A.pick,
          distinguish := fun st pk => simulateQ (instImpl₀ g) (A.distinguish st pk) } := rfl
  exact e1.trans ((SM_DT_UD_Experiment_congr world pkSeedDist _ _ id Function.injective_id
    Function.injective_id _ _ (fun _ => List (Bytes 16)) _ _ (Reduction.wotsChainTargets Link.vp)
    he hc A.State _ _).trans e2.symm)

theorem wotsUdRealI_eq (pkSeedDist : ProbComp (Bytes 16)) (A : WotsUdAdv128 pkSeedDist) :
    wotsUdRealI pkSeedDist A =
      @udRealI St Blk (Bytes 16) (Bytes 22) (Bytes 16) (Bytes 16) (Bytes 16) Unit
        _ sampY128 sampY128 _ (FWotsPre128 pkSeedDist) id Function.injective_id A := by
  rw [udRealI_eq_cfAdvantage]
  exact congrArg cfAdvantage (funext fun g => wotsUd_experiment_eq .real pkSeedDist A g)

theorem wotsUdIdealI_eq (pkSeedDist : ProbComp (Bytes 16)) (A : WotsUdAdv128 pkSeedDist) :
    wotsUdIdealI pkSeedDist A =
      @udIdealI St Blk (Bytes 16) (Bytes 22) (Bytes 16) (Bytes 16) (Bytes 16) Unit
        _ sampY128 sampY128 _ (FWotsPre128 pkSeedDist) id Function.injective_id A := by
  rw [udIdealI_eq_cfAdvantage]
  exact congrArg cfAdvantage (funext fun g => wotsUd_experiment_eq .ideal pkSeedDist A g)

private theorem card_bytes16_inv_ud :
    (Fintype.card (Bytes 16) : ℝ≥0∞)⁻¹ = ((2 : ℝ≥0∞) ^ 128)⁻¹ := by
  rw [card_bytes]
  norm_num

private theorem card_St_inv_ud : (Fintype.card St : ℝ≥0∞)⁻¹ = ((2 : ℝ≥0∞) ^ 256)⁻¹ := by
  rw [card_St, Nat.cast_pow, Nat.cast_ofNat]

/-- **SM-UD of the 128s `F` in the ideal-compression model, one-sided.**  `q₁`, `qch`, `qc`
bound the first phase's compression, challenge and collection queries, `L` the number of blocks
after the first of a collection query, `q₂` the second phase's compression queries, and `γ` the
point probabilities of the public-seed distribution. -/
theorem wotsUd_bound_128s (pkSeedDist : ProbComp (Bytes 16))
    (γ : ℝ≥0∞) (hγ : ∀ s, Pr{let s' ← pkSeedDist}[s' = s] ≤ γ)
    (A : WotsUdAdv128 pkSeedDist) (q₁ qch qc L q₂ : ℕ)
    (hq₁ : A.PickBound q₁) (hch : A.ChalBound qch) (hc : A.CollBound qc)
    (hL : A.CollLen L) (hq₂ : A.DistBound q₂) :
    wotsUdRealI pkSeedDist A ≤
      wotsUdIdealI pkSeedDist A + q₂ * ((2 : ℝ≥0∞) ^ 128)⁻¹ + 2 * q₁ * γ +
        (2 * (2 * q₁ + (qch + qc) * (1 + 2 * L) + 1) : ℕ) * ((2 : ℝ≥0∞) ^ 256)⁻¹ := by
  have hs : ∀ (t : Bytes 22) (x : Bytes 16), (tblocks t [x]).2 = [] :=
    fun t x => tblocks_snd_of_length_one t [x] rfl
  rw [wotsUdRealI_eq, wotsUdIdealI_eq, ← card_St_inv_ud, ← card_bytes16_inv_ud]
  exact @ud_bound St Blk (Bytes 16) (Bytes 22) (Bytes 16) (Bytes 16) (Bytes 16) Unit
    _ _ _ _ _ _ _ sampY128 _ sampY128 _
    (FWotsPre128 pkSeedDist) id Function.injective_id sb128_injective γ hγ hs btw128
    (fun t x => btw128_tblocks t [x]) (fun _ t m => btw128_tblocks t m)
    (fun t x x' h => List.singleton_injective
      (tblocks_injective (Prod.ext h ((hs t x).trans (hs t x').symm))).2)
    prEvent_out16 A q₁ qch qc L q₂ hq₁ hch hc hL hq₂

/-- The reverse inequality of `wotsUd_bound_128s`, with the same error. -/
theorem wotsUd_bound_128s_ge (pkSeedDist : ProbComp (Bytes 16))
    (γ : ℝ≥0∞) (hγ : ∀ s, Pr{let s' ← pkSeedDist}[s' = s] ≤ γ)
    (A : WotsUdAdv128 pkSeedDist) (q₁ qch qc L q₂ : ℕ)
    (hq₁ : A.PickBound q₁) (hch : A.ChalBound qch) (hc : A.CollBound qc)
    (hL : A.CollLen L) (hq₂ : A.DistBound q₂) :
    wotsUdIdealI pkSeedDist A ≤
      wotsUdRealI pkSeedDist A + q₂ * ((2 : ℝ≥0∞) ^ 128)⁻¹ + 2 * q₁ * γ +
        (2 * (2 * q₁ + (qch + qc) * (1 + 2 * L) + 1) : ℕ) * ((2 : ℝ≥0∞) ^ 256)⁻¹ := by
  have hs : ∀ (t : Bytes 22) (x : Bytes 16), (tblocks t [x]).2 = [] :=
    fun t x => tblocks_snd_of_length_one t [x] rfl
  rw [wotsUdRealI_eq, wotsUdIdealI_eq, ← card_St_inv_ud, ← card_bytes16_inv_ud]
  exact @ud_bound_ge St Blk (Bytes 16) (Bytes 22) (Bytes 16) (Bytes 16) (Bytes 16) Unit
    _ _ _ _ _ _ _ sampY128 _ sampY128 _
    (FWotsPre128 pkSeedDist) id Function.injective_id sb128_injective γ hγ hs btw128
    (fun t x => btw128_tblocks t [x]) (fun _ t m => btw128_tblocks t m)
    (fun t x x' h => List.singleton_injective
      (tblocks_injective (Prod.ext h ((hs t x).trans (hs t x').symm))).2)
    prEvent_out16 A q₁ qch qc L q₂ hq₁ hch hc hL hq₂

private theorem prEvent_uniform_bytes16_eq_ud (s : Bytes 16) :
    Pr{let s' ← $ᵗ (Bytes 16)}[s' = s] = ((2 : ℝ≥0∞) ^ 128)⁻¹ := by
  rw [SampleableType.prEvent_uniformSample_eq_singleton, card_bytes]
  norm_num

/-- `wotsUd_bound_128s` for a uniform public seed. -/
theorem wotsUd_bound_128s_uniform
    (A : WotsUdAdv128 ($ᵗ (Bytes 16))) (q₁ qch qc L q₂ : ℕ)
    (hq₁ : A.PickBound q₁) (hch : A.ChalBound qch) (hc : A.CollBound qc)
    (hL : A.CollLen L) (hq₂ : A.DistBound q₂) :
    wotsUdRealI ($ᵗ (Bytes 16)) A ≤
      wotsUdIdealI ($ᵗ (Bytes 16)) A + q₂ * ((2 : ℝ≥0∞) ^ 128)⁻¹ +
        2 * q₁ * ((2 : ℝ≥0∞) ^ 128)⁻¹ +
        (2 * (2 * q₁ + (qch + qc) * (1 + 2 * L) + 1) : ℕ) * ((2 : ℝ≥0∞) ^ 256)⁻¹ :=
  wotsUd_bound_128s _ _ (fun s => (prEvent_uniform_bytes16_eq_ud s).le) A q₁ qch qc L q₂
    hq₁ hch hc hL hq₂

/-- `wotsUd_bound_128s_ge` for a uniform public seed. -/
theorem wotsUd_bound_128s_ge_uniform
    (A : WotsUdAdv128 ($ᵗ (Bytes 16))) (q₁ qch qc L q₂ : ℕ)
    (hq₁ : A.PickBound q₁) (hch : A.ChalBound qch) (hc : A.CollBound qc)
    (hL : A.CollLen L) (hq₂ : A.DistBound q₂) :
    wotsUdIdealI ($ᵗ (Bytes 16)) A ≤
      wotsUdRealI ($ᵗ (Bytes 16)) A + q₂ * ((2 : ℝ≥0∞) ^ 128)⁻¹ +
        2 * q₁ * ((2 : ℝ≥0∞) ^ 128)⁻¹ +
        (2 * (2 * q₁ + (qch + qc) * (1 + 2 * L) + 1) : ℕ) * ((2 : ℝ≥0∞) ^ 256)⁻¹ :=
  wotsUd_bound_128s_ge _ _ (fun s => (prEvent_uniform_bytes16_eq_ud s).le) A q₁ qch qc L q₂
    hq₁ hch hc hL hq₂

end Ideal

#print axioms Ideal.wotsUdProblem_eq_udProb
#print axioms Ideal.wotsUdProblem_realCF
#print axioms Ideal.wotsUdRealI_eq
#print axioms Ideal.wotsUdIdealI_eq
#print axioms Ideal.wotsUd_bound_128s
#print axioms Ideal.wotsUd_bound_128s_ge
#print axioms Ideal.wotsUd_bound_128s_uniform
#print axioms Ideal.wotsUd_bound_128s_ge_uniform
