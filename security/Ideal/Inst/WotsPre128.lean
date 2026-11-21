import Ideal.Games.Pre
import Ideal.Sha.Shape
import Reduction.Basic

/-!
# SM-PRE of the SLH-DSA-SHA2-128s `F` in the ideal-compression model

The Reduction's SM-PRE problem on `F` (the WOTS+ chains),
`Reduction.wotsPreProblem Link.vp prims pkSeedDist`, taken at the generic SHA-256 primitives
`primsG (liftC g)` over a compression table `g`, is the SM-PRE problem of the Merkle–Damgård
family `FWotsPre128 pkSeedDist` with `emb = id` (`wotsPreProblem_eq_preProb`); at `g = realCF`
it is the Reduction's own problem at `Link.prims` (`wotsPreProblem_realCF`).  `Ideal.pre_bound`
gives, for the advantage averaged over a uniform table,
`2 (q₂ + 1)/2^128 + q₁·γ + (2 q₁ + (qch + qc)(1 + 2 L) + 2)/2^256`.
-/

open OracleComp OracleSpec ENNReal

namespace Ideal

open TweakableHash SLHDSA

/-- The SM-PRE experiment depends on the problem only through its components; adversaries with
the same components against problems with equal hash functions have the same experiment. -/
theorem SM_DT_PRE_Experiment_congr {ι PkSeed Tweak M M' Y : Type}
    {iT iT' : DecidableEq Tweak} {iY iY' : DecidableEq Y} [iS : SampleableType M']
    (sg : ProbComp PkSeed) (e e' : PkSeed → Tweak → M → Y) (emb : M' → M)
    (hemb hemb' : Function.Injective emb) (Msg : ι → Type)
    (ce ce' : (i : ι) → PkSeed → Tweak → Msg i → Y) (N : ℕ) (he : e = e') (hc : ce = ce')
    (State : Type)
    (choose : OracleComp (unifSpec + (SM_DT_PRE_challengeSpec Tweak Y +
      (((i : ι) × Tweak × Msg i) →ₒ Option Y))) State)
    (invert : State → PkSeed → ProbComp (ℕ × M')) :
    @SM_DT_PRE_Experiment ι PkSeed Tweak M M' Y iT iY iS
        { th := { seedGen := sg, eval := e }, emb := emb, emb_injective := hemb,
          thColl := { Msg := Msg, eval := ce }, numTargets := N }
        { State := State, choose := choose, invert := invert } =
      @SM_DT_PRE_Experiment ι PkSeed Tweak M M' Y iT' iY' iS
        { th := { seedGen := sg, eval := e' }, emb := emb, emb_injective := hemb',
          thColl := { Msg := Msg, eval := ce' }, numTargets := N }
        { State := State, choose := choose, invert := invert } := by
  subst he hc
  obtain rfl := Subsingleton.elim iT iT'
  obtain rfl := Subsingleton.elim iY iY'
  rfl

/-- `F = Thash` at arity one, with the whole `Thash` as collection and the WOTS+ chain count as
target cap, as a Merkle–Damgård family. -/
def FWotsPre128 (pkSeedDist : ProbComp (Bytes 16)) :
    THFam St Blk (Bytes 16) (Bytes 22) (Bytes 16) (Bytes 16) Unit where
  IV := IV128
  sb := sb128
  seedGen := pkSeedDist
  tch := fun t x => tblocks t [x]
  out := out16
  Msg := fun _ => List (Bytes 16)
  cch := fun _ t xs => tblocks t xs
  cout := fun _ => out16
  numTargets := Reduction.wotsChainTargets Link.vp

/-- The Reduction's SM-PRE problem on `F` at the generic primitives over the table `g` is the
SM-PRE problem of `FWotsPre128` at `g` (hidden inputs `M' = Bytes 16`, `emb = id`). -/
theorem wotsPreProblem_eq_preProb (pkSeedDist : ProbComp (Bytes 16)) (g : CF St Blk) :
    Reduction.wotsPreProblem Link.vp (primsG (liftC g)) pkSeedDist =
      (FWotsPre128 pkSeedDist).preProb id Function.injective_id g := by
  have h : (primsG (liftC g)).Thash =
      fun pk a xs => out16 (keyedChain IV128 sb128 g pk (tblocks a xs)) := by
    funext pk a xs
    exact primsG_Thash_shape g pk a xs
  show ({ th := { seedGen := pkSeedDist, eval := fun pk t x => (primsG (liftC g)).Thash pk t [x] },
          emb := id, emb_injective := Function.injective_id,
          thColl := { Msg := fun _ => List (Bytes 16), eval := fun _ => (primsG (liftC g)).Thash },
          numTargets := Reduction.wotsChainTargets Link.vp } :
        SM_DT_PRE_Problem Unit (Bytes 16) (Bytes 22) (Bytes 16) (Bytes 16) (Bytes 16)) = _
  rw [h]
  simp only [THFam.preProb, THFam.coll, FWotsPre128]
  rfl

/-- At the real compression function the problem is the Reduction's own. -/
theorem wotsPreProblem_realCF (pkSeedDist : ProbComp (Bytes 16)) :
    Reduction.wotsPreProblem Link.vp (primsG (liftC realCF)) pkSeedDist =
      Reduction.wotsPreProblem Link.vp Link.prims pkSeedDist := by
  have h := congrArg (fun c : CompressFn =>
    (show SM_DT_PRE_Problem Unit (Bytes 16) (Bytes 22) (Bytes 16) (Bytes 16) (Bytes 16) from
      Reduction.wotsPreProblem Link.vp (primsG c) pkSeedDist))
    liftC_realCF
  exact h

/-- Ideal-model adversaries against the Reduction's SM-PRE game on `F`. -/
abbrev WotsPreAdv128 (pkSeedDist : ProbComp (Bytes 16)) :=
  PreAdv (FWotsPre128 pkSeedDist) (Bytes 16)

/-- The adversary against the Reduction's SM-PRE problem on `F` at the table `g`. -/
def instWP {pkSeedDist : ProbComp (Bytes 16)} (A : WotsPreAdv128 pkSeedDist) (g : CF St Blk) :
    SM_DT_PRE_Adversary (Reduction.wotsPreProblem Link.vp (primsG (liftC g)) pkSeedDist) where
  State := A.State
  choose := simulateQ (instImpl g) A.choose
  invert := fun st pk => simulateQ (instImpl₀ g) (A.invert st pk)

/-- The probability that an experiment depending on the compression table returns `true`, for a
uniformly random table. -/
noncomputable def cfAdvantage {St Blk : Type} [SampleableType (CF St Blk)]
    (X : CF St Blk → ProbComp Bool) : ℝ≥0∞ :=
  𝒟[do
    let g ← $ᵗ (CF St Blk)
    X g] {true}

/-- `preAdvantage` is `cfAdvantage` of VCVio's SM-PRE experiment at the instantiated
adversary. -/
theorem preAdvantage_eq_cfAdvantage {St Blk PkSeed Tweak M M' Y ι : Type} [DecidableEq Tweak]
    [DecidableEq Y] [SampleableType M'] [SampleableType (CF St Blk)]
    (F : THFam St Blk PkSeed Tweak M Y ι) (emb : M' → M) (hemb : Function.Injective emb)
    (A : PreAdv F M') :
    preAdvantage F emb hemb A =
      cfAdvantage fun g => SM_DT_PRE_Experiment (A.inst emb hemb g) := rfl

/-- Advantage against the Reduction's SM-PRE game on `F` in the ideal-compression model: the
Reduction's experiment at the primitives built from `g`, the adversary's compression queries
answered by `g`, with `g` a uniformly random table, i.e.
`𝒟[do let g ← $ᵗ (CF St Blk); SM_DT_PRE_Experiment (instWP A g)] {true}`. -/
noncomputable def wotsPreAdvantage (pkSeedDist : ProbComp (Bytes 16))
    (A : WotsPreAdv128 pkSeedDist) : ℝ≥0∞ :=
  cfAdvantage fun g => SM_DT_PRE_Experiment (instWP A g)

/-- The sampler of hidden inputs used by the Reduction's SM-PRE game at the generic primitives
(the `Bytes` sampler at the scheme's `n = 16`; it does not depend on the table). -/
@[instance_reducible] noncomputable def sampY128 : SampleableType (Bytes 16) :=
  inferInstanceAs (SampleableType (Bytes Link.vp.params.n))

theorem wotsPreAdvantage_eq (pkSeedDist : ProbComp (Bytes 16)) (A : WotsPreAdv128 pkSeedDist) :
    wotsPreAdvantage pkSeedDist A =
      @preAdvantage St Blk (Bytes 16) (Bytes 22) (Bytes 16) (Bytes 16) (Bytes 16) Unit
        _ _ sampY128 _ (FWotsPre128 pkSeedDist) id Function.injective_id A := by
  rw [preAdvantage_eq_cfAdvantage]
  refine congrArg cfAdvantage (funext fun g => ?_)
  have h : (primsG (liftC g)).Thash =
      fun pk a xs => out16 (keyedChain IV128 sb128 g pk (tblocks a xs)) := by
    funext pk a xs
    exact primsG_Thash_shape g pk a xs
  have he : (fun (pk : Bytes 16) (t : Bytes 22) (x : Bytes 16) =>
      (primsG (liftC g)).Thash pk t [x]) = (FWotsPre128 pkSeedDist).evalT g := by
    rw [h]; rfl
  have hc : (fun (_ : Unit) => (primsG (liftC g)).Thash) = (FWotsPre128 pkSeedDist).evalC g := by
    rw [h]; rfl
  have e1 : SM_DT_PRE_Experiment (instWP A g) =
      @SM_DT_PRE_Experiment Unit (Bytes 16) (Bytes 22) (Bytes 16) (Bytes 16) (Bytes 16)
        _ _ sampY128
        { th := { seedGen := pkSeedDist,
                  eval := fun pk t x => (primsG (liftC g)).Thash pk t [x] },
          emb := id, emb_injective := Function.injective_id,
          thColl := { Msg := fun _ => List (Bytes 16),
                      eval := fun _ => (primsG (liftC g)).Thash },
          numTargets := Reduction.wotsChainTargets Link.vp }
        { State := A.State, choose := simulateQ (instImpl g) A.choose,
          invert := fun st pk => simulateQ (instImpl₀ g) (A.invert st pk) } := rfl
  have e2 : @SM_DT_PRE_Experiment Unit (Bytes 16) (Bytes 22) (Bytes 16) (Bytes 16) (Bytes 16)
        _ _ sampY128
        ((FWotsPre128 pkSeedDist).preProb id Function.injective_id g)
        (A.inst id Function.injective_id g) =
      @SM_DT_PRE_Experiment Unit (Bytes 16) (Bytes 22) (Bytes 16) (Bytes 16) (Bytes 16)
        _ _ sampY128
        { th := { seedGen := pkSeedDist, eval := (FWotsPre128 pkSeedDist).evalT g },
          emb := id, emb_injective := Function.injective_id,
          thColl := { Msg := fun _ => List (Bytes 16),
                      eval := (FWotsPre128 pkSeedDist).evalC g },
          numTargets := Reduction.wotsChainTargets Link.vp }
        { State := A.State, choose := simulateQ (instImpl g) A.choose,
          invert := fun st pk => simulateQ (instImpl₀ g) (A.invert st pk) } := rfl
  exact e1.trans ((SM_DT_PRE_Experiment_congr pkSeedDist _ _ id Function.injective_id
    Function.injective_id (fun _ => List (Bytes 16)) _ _ (Reduction.wotsChainTargets Link.vp)
    he hc A.State _ _).trans e2.symm)

private theorem card_bytes16_inv :
    (Fintype.card (Bytes 16) : ℝ≥0∞)⁻¹ = ((2 : ℝ≥0∞) ^ 128)⁻¹ := by
  rw [card_bytes]
  norm_num

private theorem card_St_inv' : (Fintype.card St : ℝ≥0∞)⁻¹ = ((2 : ℝ≥0∞) ^ 256)⁻¹ := by
  rw [card_St, Nat.cast_pow, Nat.cast_ofNat]

/-- **SM-PRE of the 128s `F` in the ideal-compression model.**  `q₁`, `qch`, `qc` bound the
first phase's compression, challenge and collection queries, `L` the number of blocks after
the first of a collection query, `q₂` the second phase's compression queries, and `γ` the
point probabilities of the public-seed distribution. -/
theorem wotsPre_bound_128s (pkSeedDist : ProbComp (Bytes 16))
    (γ : ℝ≥0∞) (hγ : ∀ s, Pr{let s' ← pkSeedDist}[s' = s] ≤ γ)
    (A : WotsPreAdv128 pkSeedDist) (q₁ qch qc L q₂ : ℕ)
    (hq₁ : A.ChooseBound q₁) (hch : A.ChalBound qch) (hc : A.CollBound qc)
    (hL : A.CollLen L) (hq₂ : A.InvertBound q₂) :
    wotsPreAdvantage pkSeedDist A ≤ 2 * (q₂ + 1 : ℕ) * ((2 : ℝ≥0∞) ^ 128)⁻¹ + q₁ * γ +
      (2 * q₁ + (qch + qc) * (1 + 2 * L) + 2 : ℕ) * ((2 : ℝ≥0∞) ^ 256)⁻¹ := by
  have hs : ∀ (t : Bytes 22) (x : Bytes 16), (tblocks t [x]).2 = [] :=
    fun t x => tblocks_snd_of_length_one t [x] rfl
  rw [wotsPreAdvantage_eq, ← card_St_inv']
  refine (@pre_bound St Blk (Bytes 16) (Bytes 22) (Bytes 16) (Bytes 16) (Bytes 16) Unit
    _ _ _ _ _ _ _ _ sampY128 _
    (FWotsPre128 pkSeedDist) id Function.injective_id sb128_injective γ hγ hs btw128
    (fun t x => btw128_tblocks t [x]) (fun _ t m => btw128_tblocks t m)
    (fun t x x' h => List.singleton_injective
      (tblocks_injective (Prod.ext h ((hs t x).trans (hs t x').symm))).2)
    _ (fun y => (prEvent_out16_eq y).le) A q₁ qch qc L q₂ hq₁ hch hc hL hq₂).trans (le_of_eq ?_)
  rw [card_bytes16_inv]
  ring

private theorem prEvent_uniform_bytes16_eq' (s : Bytes 16) :
    Pr{let s' ← $ᵗ (Bytes 16)}[s' = s] = ((2 : ℝ≥0∞) ^ 128)⁻¹ := by
  rw [SampleableType.prEvent_uniformSample_eq_singleton, card_bytes]
  norm_num

/-- `wotsPre_bound_128s` for a uniform public seed. -/
theorem wotsPre_bound_128s_uniform
    (A : WotsPreAdv128 ($ᵗ (Bytes 16))) (q₁ qch qc L q₂ : ℕ)
    (hq₁ : A.ChooseBound q₁) (hch : A.ChalBound qch) (hc : A.CollBound qc)
    (hL : A.CollLen L) (hq₂ : A.InvertBound q₂) :
    wotsPreAdvantage ($ᵗ (Bytes 16)) A ≤
      2 * (q₂ + 1 : ℕ) * ((2 : ℝ≥0∞) ^ 128)⁻¹ + q₁ * ((2 : ℝ≥0∞) ^ 128)⁻¹ +
      (2 * q₁ + (qch + qc) * (1 + 2 * L) + 2 : ℕ) * ((2 : ℝ≥0∞) ^ 256)⁻¹ :=
  wotsPre_bound_128s _ _ (fun s => (prEvent_uniform_bytes16_eq' s).le) A q₁ qch qc L q₂
    hq₁ hch hc hL hq₂

end Ideal

#print axioms Ideal.wotsPreProblem_eq_preProb
#print axioms Ideal.wotsPreProblem_realCF
#print axioms Ideal.wotsPreAdvantage_eq
#print axioms Ideal.wotsPre_bound_128s
#print axioms Ideal.wotsPre_bound_128s_uniform
