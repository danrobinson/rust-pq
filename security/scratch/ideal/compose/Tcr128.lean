import Ideal.Games.Tcr
import Ideal.Sha.Shape
import Reduction.TcrSplitFinal

/-!
# SM-TCR of the SLH-DSA-SHA2-128s tweakable hash in the ideal-compression model

The Reduction's per-arity SM-TCR problem `Reduction.thashArityProblem Link.vp prims pkSeedDist n`
and its SM-TCR problem on `F`, `Reduction.wotsTcrProblem Link.vp prims pkSeedDist`, taken at the
generic SHA-256 primitives `primsG (liftC g)` over a compression table `g`, are the problems of
the Merkle–Damgård families `F128 pkSeedDist n` and `FWots128 pkSeedDist`
(`thashArityProblem_eq_tcrProb`, `wotsTcrProblem_eq_tcrProb`); at `g = realCF` they are the
Reduction's own problems at `Link.prims`.  For arities `n = 1, 2` (one block after the seed
block) and for `F`, `Ideal.tcr_bound` gives
`(q₂ + 1)/2^128 + q₁·γ + (2 q₁ + (qch + qc)(1 + 2 L) + 2)/2^256`.
-/

open OracleComp OracleSpec ENNReal

namespace Ideal

open TweakableHash SLHDSA

/-- The SM-TCR experiment depends on the problem only through its components; adversaries with
the same components against problems with equal hash functions have the same experiment. -/
theorem SM_DT_TCR_Experiment_congr {ι PkSeed Tweak M Y : Type}
    {iT iT' : DecidableEq Tweak} {iM iM' : DecidableEq M} {iY iY' : DecidableEq Y}
    (sg : ProbComp PkSeed) (e e' : PkSeed → Tweak → M → Y) (Msg : ι → Type)
    (ce ce' : (i : ι) → PkSeed → Tweak → Msg i → Y) (N N' : ℕ) (he : e = e') (hc : ce = ce')
    (hN : N = N')
    (State : Type)
    (choose : OracleComp (unifSpec + (SM_DT_TCR_challengeSpec Tweak M Y +
      (((i : ι) × Tweak × Msg i) →ₒ Option Y))) State)
    (forge : State → PkSeed → ProbComp (ℕ × M)) :
    @SM_DT_TCR_Experiment ι PkSeed Tweak M Y iT iM iY
        { th := { seedGen := sg, eval := e }, thColl := { Msg := Msg, eval := ce },
          numTargets := N }
        { State := State, choose := choose, forge := forge } =
      @SM_DT_TCR_Experiment ι PkSeed Tweak M Y iT' iM' iY'
        { th := { seedGen := sg, eval := e' }, thColl := { Msg := Msg, eval := ce' },
          numTargets := N' }
        { State := State, choose := choose, forge := forge } := by
  subst he hc hN
  obtain rfl := Subsingleton.elim iT iT'
  obtain rfl := Subsingleton.elim iM iM'
  obtain rfl := Subsingleton.elim iY iY'
  rfl

theorem prEvent_uniform_bytes16_eq (s : Bytes 16) :
    Pr{let s' ← $ᵗ (Bytes 16)}[s' = s] = ((2 : ℝ≥0∞) ^ 128)⁻¹ := by
  rw [SampleableType.prEvent_uniformSample_eq_singleton, card_bytes]
  norm_num

theorem card_St_inv : (Fintype.card St : ℝ≥0∞)⁻¹ = ((2 : ℝ≥0∞) ^ 256)⁻¹ := by
  rw [card_St, Nat.cast_pow, Nat.cast_ofNat]

/-! ## `Thash` at arity `n` -/

/-- The 128s tweakable hash restricted to arity `n`, with the whole `Thash` as collection, as a
Merkle–Damgård family. -/
def F128 (pkSeedDist : ProbComp (Bytes 16)) (n : ℕ) :
    THFam St Blk (Bytes 16) (Bytes 22) {xs : List (Bytes 16) // xs.length = n} (Bytes 16) Unit where
  IV := IV128
  sb := sb128
  seedGen := pkSeedDist
  tch := fun t m => tblocks t m.1
  out := out16
  Msg := fun _ => List (Bytes 16)
  cch := fun _ t xs => tblocks t xs
  cout := fun _ => out16
  numTargets := Reduction.tcrTargets Link.vp

/-- The Reduction's arity-`n` SM-TCR problem at the generic primitives over the table `g` is the
problem of `F128` at `g`. -/
theorem thashArityProblem_eq_tcrProb (pkSeedDist : ProbComp (Bytes 16)) (n : ℕ) (g : CF St Blk) :
    Reduction.thashArityProblem Link.vp (primsG (liftC g)) pkSeedDist n =
      (F128 pkSeedDist n).tcrProb g := by
  have h : (primsG (liftC g)).Thash =
      fun pk a xs => out16 (keyedChain IV128 sb128 g pk (tblocks a xs)) := by
    funext pk a xs
    exact primsG_Thash_shape g pk a xs
  show ({ th := { seedGen := pkSeedDist, eval := fun pk t m => (primsG (liftC g)).Thash pk t m.1 },
          thColl := { Msg := fun _ => List (Bytes 16), eval := fun _ => (primsG (liftC g)).Thash },
          numTargets := Reduction.tcrTargets Link.vp } :
        SM_DT_TCR_Problem Unit (Bytes 16) (Bytes 22) {xs : List (Bytes 16) // xs.length = n}
          (Bytes 16)) = _
  rw [h]
  simp only [THFam.tcrProb, THFam.coll, F128]
  rfl

/-- At the real compression function the problem is the Reduction's own. -/
theorem thashArityProblem_realCF (pkSeedDist : ProbComp (Bytes 16)) (n : ℕ) :
    Reduction.thashArityProblem Link.vp (primsG (liftC realCF)) pkSeedDist n =
      Reduction.thashArityProblem Link.vp Link.prims pkSeedDist n := by
  exact @congrArg CompressFn (SM_DT_TCR_Problem Unit (Bytes 16) (Bytes 22) {xs : List (Bytes 16) // xs.length = n}
    (Bytes 16)) _ _ (fun c => Reduction.thashArityProblem Link.vp (primsG c) pkSeedDist n) liftC_realCF

/-- Ideal-model adversaries against the Reduction's arity-`n` SM-TCR game. -/
abbrev TcrAdv128 (pkSeedDist : ProbComp (Bytes 16)) (n : ℕ) := TcrAdv (F128 pkSeedDist n)

/-- The adversary against the Reduction's arity-`n` problem at the table `g`. -/
def instR {pkSeedDist : ProbComp (Bytes 16)} {n : ℕ} (A : TcrAdv128 pkSeedDist n)
    (g : CF St Blk) :
    SM_DT_TCR_Adversary (Reduction.thashArityProblem Link.vp (primsG (liftC g)) pkSeedDist n) where
  State := A.State
  choose := simulateQ (instImpl g) A.choose
  forge := fun st pk => simulateQ (instImpl₀ g) (A.forge st pk)

/-- Advantage against the Reduction's arity-`n` SM-TCR game in the ideal-compression model. -/
noncomputable def tcrArityAdvantage (pkSeedDist : ProbComp (Bytes 16)) (n : ℕ)
    (A : TcrAdv128 pkSeedDist n) : ℝ≥0∞ :=
  idealAdv fun g => SM_DT_TCR_Experiment (instR A g)

theorem tcrArityAdvantage_def (pkSeedDist : ProbComp (Bytes 16)) (n : ℕ)
    (A : TcrAdv128 pkSeedDist n) :
    tcrArityAdvantage pkSeedDist n A = 𝒟[do
      let g ← $ᵗ (CF St Blk)
      SM_DT_TCR_Experiment (instR A g)] {true} :=
  idealAdv_def _

theorem tcrArityAdvantage_eq (pkSeedDist : ProbComp (Bytes 16)) (n : ℕ)
    (A : TcrAdv128 pkSeedDist n) :
    tcrArityAdvantage pkSeedDist n A = tcrAdvantage (F128 pkSeedDist n) A := by
  refine (idealAdv_congr fun g => ?_).trans (tcrAdvantage_eq_idealAdv (F128 pkSeedDist n) A).symm
  exact SM_DT_TCR_Experiment_congr (ι := Unit) (PkSeed := Bytes 16) (Tweak := Bytes 22)
    (M := {xs : List (Bytes 16) // xs.length = n}) (Y := Bytes 16) pkSeedDist
    (fun pk t m => (primsG (liftC g)).Thash pk t m.1) ((F128 pkSeedDist n).evalT g)
    (fun _ => List (Bytes 16)) (fun _ => (primsG (liftC g)).Thash) ((F128 pkSeedDist n).evalC g)
    (Reduction.tcrTargets Link.vp) (F128 pkSeedDist n).numTargets
    (by funext pk t m; exact primsG_Thash_shape g pk t m.1)
    (by funext _ pk t xs; exact primsG_Thash_shape g pk t xs)
    (by simp only [F128])
    A.State (simulateQ (instImpl g) A.choose)
    (fun st pk => simulateQ (instImpl₀ g) (A.forge st pk))

/-- SM-TCR of the 128s `Thash` at arity `1` (`F`) or `2` (`H`) in the ideal-compression model. -/
theorem tcrArity_bound_128s (pkSeedDist : ProbComp (Bytes 16)) (n : ℕ) (hn : n = 1 ∨ n = 2)
    (γ : ℝ≥0∞) (hγ : ∀ s, Pr{let s' ← pkSeedDist}[s' = s] ≤ γ)
    (A : TcrAdv128 pkSeedDist n) (q₁ qch qc L q₂ : ℕ)
    (hq₁ : A.ChooseBound q₁) (hch : A.ChalBound qch) (hc : A.CollBound qc)
    (hL : A.CollLen L) (hq₂ : A.ForgeBound q₂) :
    tcrArityAdvantage pkSeedDist n A ≤ (q₂ + 1 : ℕ) * ((2 : ℝ≥0∞) ^ 128)⁻¹ + q₁ * γ +
      (2 * q₁ + (qch + qc) * (1 + 2 * L) + 2 : ℕ) * ((2 : ℝ≥0∞) ^ 256)⁻¹ := by
  have hs : ∀ (t : Bytes 22) (m : {xs : List (Bytes 16) // xs.length = n}),
      (tblocks t m.1).2 = [] := by
    intro t m
    rcases hn with rfl | rfl
    · exact tblocks_snd_of_length_one t m.1 m.2
    · exact tblocks_snd_of_length_two t m.1 m.2
  rw [tcrArityAdvantage_eq, ← card_St_inv]
  exact tcr_bound (F128 pkSeedDist n) sb128_injective γ hγ hs btw128
    (fun t m => btw128_tblocks t m.1) (fun _ t m => btw128_tblocks t m)
    (fun t m m' h => Subtype.ext (tblocks_injective (Prod.ext h ((hs t m).trans (hs t m').symm))).2)
    _ (fun y => (prEvent_out16_eq y).le) A q₁ qch qc L q₂ hq₁ hch hc hL hq₂

/-- `tcrArity_bound_128s` for a uniform public seed. -/
theorem tcrArity_bound_128s_uniform (n : ℕ) (hn : n = 1 ∨ n = 2)
    (A : TcrAdv128 ($ᵗ (Bytes 16)) n) (q₁ qch qc L q₂ : ℕ)
    (hq₁ : A.ChooseBound q₁) (hch : A.ChalBound qch) (hc : A.CollBound qc)
    (hL : A.CollLen L) (hq₂ : A.ForgeBound q₂) :
    tcrArityAdvantage ($ᵗ (Bytes 16)) n A ≤
      (q₂ + 1 : ℕ) * ((2 : ℝ≥0∞) ^ 128)⁻¹ + q₁ * ((2 : ℝ≥0∞) ^ 128)⁻¹ +
      (2 * q₁ + (qch + qc) * (1 + 2 * L) + 2 : ℕ) * ((2 : ℝ≥0∞) ^ 256)⁻¹ :=
  tcrArity_bound_128s _ n hn _ (fun s => (prEvent_uniform_bytes16_eq s).le) A q₁ qch qc L q₂
    hq₁ hch hc hL hq₂

/-! ## SM-TCR on `F` (the WOTS+ chain steps) -/

/-- `F = Thash` at arity one, with the whole `Thash` as collection, as a Merkle–Damgård family. -/
def FWots128 (pkSeedDist : ProbComp (Bytes 16)) :
    THFam St Blk (Bytes 16) (Bytes 22) (Bytes 16) (Bytes 16) Unit where
  IV := IV128
  sb := sb128
  seedGen := pkSeedDist
  tch := fun t x => tblocks t [x]
  out := out16
  Msg := fun _ => List (Bytes 16)
  cch := fun _ t xs => tblocks t xs
  cout := fun _ => out16
  numTargets := Reduction.wotsStepTargets Link.vp

/-- The Reduction's SM-TCR problem on `F` at the generic primitives over the table `g` is the
problem of `FWots128` at `g`. -/
theorem wotsTcrProblem_eq_tcrProb (pkSeedDist : ProbComp (Bytes 16)) (g : CF St Blk) :
    Reduction.wotsTcrProblem Link.vp (primsG (liftC g)) pkSeedDist =
      (FWots128 pkSeedDist).tcrProb g := by
  have h : (primsG (liftC g)).Thash =
      fun pk a xs => out16 (keyedChain IV128 sb128 g pk (tblocks a xs)) := by
    funext pk a xs
    exact primsG_Thash_shape g pk a xs
  show ({ th := { seedGen := pkSeedDist, eval := fun pk t x => (primsG (liftC g)).Thash pk t [x] },
          thColl := { Msg := fun _ => List (Bytes 16), eval := fun _ => (primsG (liftC g)).Thash },
          numTargets := Reduction.wotsStepTargets Link.vp } :
        SM_DT_TCR_Problem Unit (Bytes 16) (Bytes 22) (Bytes 16) (Bytes 16)) = _
  rw [h]
  simp only [THFam.tcrProb, THFam.coll, FWots128]
  rfl

/-- At the real compression function the problem is the Reduction's own. -/
theorem wotsTcrProblem_realCF (pkSeedDist : ProbComp (Bytes 16)) :
    Reduction.wotsTcrProblem Link.vp (primsG (liftC realCF)) pkSeedDist =
      Reduction.wotsTcrProblem Link.vp Link.prims pkSeedDist := by
  exact @congrArg CompressFn (SM_DT_TCR_Problem Unit (Bytes 16) (Bytes 22) (Bytes 16)
    (Bytes 16)) _ _ (fun c => Reduction.wotsTcrProblem Link.vp (primsG c) pkSeedDist) liftC_realCF

/-- Ideal-model adversaries against the Reduction's SM-TCR game on `F`. -/
abbrev WotsTcrAdv128 (pkSeedDist : ProbComp (Bytes 16)) := TcrAdv (FWots128 pkSeedDist)

/-- The adversary against the Reduction's SM-TCR problem on `F` at the table `g`. -/
def instW {pkSeedDist : ProbComp (Bytes 16)} (A : WotsTcrAdv128 pkSeedDist) (g : CF St Blk) :
    SM_DT_TCR_Adversary (Reduction.wotsTcrProblem Link.vp (primsG (liftC g)) pkSeedDist) where
  State := A.State
  choose := simulateQ (instImpl g) A.choose
  forge := fun st pk => simulateQ (instImpl₀ g) (A.forge st pk)

/-- Advantage against the Reduction's SM-TCR game on `F` in the ideal-compression model. -/
noncomputable def wotsTcrAdvantage (pkSeedDist : ProbComp (Bytes 16))
    (A : WotsTcrAdv128 pkSeedDist) : ℝ≥0∞ :=
  idealAdv fun g => SM_DT_TCR_Experiment (instW A g)

theorem wotsTcrAdvantage_def (pkSeedDist : ProbComp (Bytes 16)) (A : WotsTcrAdv128 pkSeedDist) :
    wotsTcrAdvantage pkSeedDist A = 𝒟[do
      let g ← $ᵗ (CF St Blk)
      SM_DT_TCR_Experiment (instW A g)] {true} :=
  idealAdv_def _

theorem wotsTcrAdvantage_eq (pkSeedDist : ProbComp (Bytes 16)) (A : WotsTcrAdv128 pkSeedDist) :
    wotsTcrAdvantage pkSeedDist A = tcrAdvantage (FWots128 pkSeedDist) A := by
  refine (idealAdv_congr fun g => ?_).trans (tcrAdvantage_eq_idealAdv (FWots128 pkSeedDist) A).symm
  exact SM_DT_TCR_Experiment_congr (ι := Unit) (PkSeed := Bytes 16) (Tweak := Bytes 22)
    (M := Bytes 16) (Y := Bytes 16) pkSeedDist
    (fun pk t x => (primsG (liftC g)).Thash pk t [x]) ((FWots128 pkSeedDist).evalT g)
    (fun _ => List (Bytes 16)) (fun _ => (primsG (liftC g)).Thash) ((FWots128 pkSeedDist).evalC g)
    (Reduction.wotsStepTargets Link.vp) (FWots128 pkSeedDist).numTargets
    (by funext pk t x; exact primsG_Thash_shape g pk t [x])
    (by funext _ pk t xs; exact primsG_Thash_shape g pk t xs)
    (by simp only [FWots128])
    A.State (simulateQ (instImpl g) A.choose)
    (fun st pk => simulateQ (instImpl₀ g) (A.forge st pk))

/-- SM-TCR of the 128s `F` in the ideal-compression model. -/
theorem wotsTcr_bound_128s (pkSeedDist : ProbComp (Bytes 16))
    (γ : ℝ≥0∞) (hγ : ∀ s, Pr{let s' ← pkSeedDist}[s' = s] ≤ γ)
    (A : WotsTcrAdv128 pkSeedDist) (q₁ qch qc L q₂ : ℕ)
    (hq₁ : A.ChooseBound q₁) (hch : A.ChalBound qch) (hc : A.CollBound qc)
    (hL : A.CollLen L) (hq₂ : A.ForgeBound q₂) :
    wotsTcrAdvantage pkSeedDist A ≤ (q₂ + 1 : ℕ) * ((2 : ℝ≥0∞) ^ 128)⁻¹ + q₁ * γ +
      (2 * q₁ + (qch + qc) * (1 + 2 * L) + 2 : ℕ) * ((2 : ℝ≥0∞) ^ 256)⁻¹ := by
  have hs : ∀ (t : Bytes 22) (x : Bytes 16), (tblocks t [x]).2 = [] :=
    fun t x => tblocks_snd_of_length_one t [x] rfl
  rw [wotsTcrAdvantage_eq, ← card_St_inv]
  exact tcr_bound (FWots128 pkSeedDist) sb128_injective γ hγ hs btw128
    (fun t x => btw128_tblocks t [x]) (fun _ t m => btw128_tblocks t m)
    (fun t x x' h => List.singleton_injective
      (tblocks_injective (Prod.ext h ((hs t x).trans (hs t x').symm))).2)
    _ (fun y => (prEvent_out16_eq y).le) A q₁ qch qc L q₂ hq₁ hch hc hL hq₂

/-- `wotsTcr_bound_128s` for a uniform public seed. -/
theorem wotsTcr_bound_128s_uniform
    (A : WotsTcrAdv128 ($ᵗ (Bytes 16))) (q₁ qch qc L q₂ : ℕ)
    (hq₁ : A.ChooseBound q₁) (hch : A.ChalBound qch) (hc : A.CollBound qc)
    (hL : A.CollLen L) (hq₂ : A.ForgeBound q₂) :
    wotsTcrAdvantage ($ᵗ (Bytes 16)) A ≤
      (q₂ + 1 : ℕ) * ((2 : ℝ≥0∞) ^ 128)⁻¹ + q₁ * ((2 : ℝ≥0∞) ^ 128)⁻¹ +
      (2 * q₁ + (qch + qc) * (1 + 2 * L) + 2 : ℕ) * ((2 : ℝ≥0∞) ^ 256)⁻¹ :=
  wotsTcr_bound_128s _ _ (fun s => (prEvent_uniform_bytes16_eq s).le) A q₁ qch qc L q₂
    hq₁ hch hc hL hq₂

end Ideal

#print axioms Ideal.thashArityProblem_eq_tcrProb
#print axioms Ideal.thashArityProblem_realCF
#print axioms Ideal.tcrArityAdvantage_def
#print axioms Ideal.tcrArityAdvantage_eq
#print axioms Ideal.tcrArity_bound_128s
#print axioms Ideal.tcrArity_bound_128s_uniform
#print axioms Ideal.wotsTcrProblem_eq_tcrProb
#print axioms Ideal.wotsTcrProblem_realCF
#print axioms Ideal.wotsTcrAdvantage_def
#print axioms Ideal.wotsTcrAdvantage_eq
#print axioms Ideal.wotsTcr_bound_128s
#print axioms Ideal.wotsTcr_bound_128s_uniform
