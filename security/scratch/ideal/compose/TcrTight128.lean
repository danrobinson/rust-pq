import Ideal.Games.TcrMulti
import Ideal.Inst.Tcr128
import Reduction.TightCapsHeadline

/-!
# SM-TCR of the SLH-DSA-SHA2-128s tweakable hash, tight-cap problems, ideal-compression model

The Reduction's tight-cap SM-TCR problems `Reduction.thashArityProblemT Link.vp prims pkSeedDist n`
(cap `Reduction.arityTargets Link.vp n`) and `Reduction.wotsTcrProblemT Link.vp prims pkSeedDist`
(cap `Reduction.wotsStepTargetsT Link.vp`), at the generic SHA-256 primitives `primsG (liftC g)`
over a compression table `g`, are the problems of the Merkle–Damgård families `F128T pkSeedDist n`
and `FWots128T pkSeedDist`.  Bounds:

* arities `1`, `2` and `F` (single block after the seed block; `Ideal.tcr_bound`):
  `(q₂ + 1)/2^128 + q₁·γ + (2 q₁ + (qch + qc)(1 + 2 L) + 2)/2^256`;
* any arity `n`, with `Ln = (22 + 16 n + 8)/64` continuation blocks (`Ideal.tcr_bound_multi`):
  `(q₂ + 2 Ln + 4)/2^128 + q₁·γ + (18 Q² + 2 q₁ + (qch + qc)(1 + 2 max Ln L) + 1)/2^256`,
  `Q = q₁ + q₂ + (qch + qc)(1 + max Ln L) + 2 (Ln + 1) + 1`; `Ln = 9` for `n = len = 35`
  (`tcrLen_bound_128s`) and `Ln = 3` for `n = k = 14` (`tcrK_bound_128s`).

The bounds do not depend on the cap.
-/

open OracleComp OracleSpec ENNReal

namespace Ideal

open TweakableHash SLHDSA

-- The caps are never evaluated.
attribute [local irreducible] Reduction.arityTargets Reduction.tcrTargets
  Reduction.wotsStepTargetsT Reduction.wotsStepTargets

/-! ## `Thash` at arity `n`, tight cap -/

/-- `F128 pkSeedDist n` with the tight cap `Reduction.arityTargets Link.vp n`. -/
def F128T (pkSeedDist : ProbComp (Bytes 16)) (n : ℕ) :
    THFam St Blk (Bytes 16) (Bytes 22) {xs : List (Bytes 16) // xs.length = n} (Bytes 16) Unit where
  IV := IV128
  sb := sb128
  seedGen := pkSeedDist
  tch := fun t m => tblocks t m.1
  out := out16
  Msg := fun _ => List (Bytes 16)
  cch := fun _ t xs => tblocks t xs
  cout := fun _ => out16
  numTargets := Reduction.arityTargets Link.vp n

/-- The Reduction's tight-cap arity-`n` SM-TCR problem at the generic primitives over the table
`g` is the problem of `F128T` at `g`. -/
theorem thashArityProblemT_eq_tcrProb (pkSeedDist : ProbComp (Bytes 16)) (n : ℕ) (g : CF St Blk) :
    Reduction.thashArityProblemT Link.vp (primsG (liftC g)) pkSeedDist n =
      (F128T pkSeedDist n).tcrProb g := by
  have h : (primsG (liftC g)).Thash =
      fun pk a xs => out16 (keyedChain IV128 sb128 g pk (tblocks a xs)) := by
    funext pk a xs
    exact primsG_Thash_shape g pk a xs
  show ({ th := { seedGen := pkSeedDist, eval := fun pk t m => (primsG (liftC g)).Thash pk t m.1 },
          thColl := { Msg := fun _ => List (Bytes 16), eval := fun _ => (primsG (liftC g)).Thash },
          numTargets := Reduction.arityTargets Link.vp n } :
        SM_DT_TCR_Problem Unit (Bytes 16) (Bytes 22) {xs : List (Bytes 16) // xs.length = n}
          (Bytes 16)) = _
  rw [h]
  simp only [THFam.tcrProb, THFam.coll, F128T]
  rfl

/-- At the real compression function the problem is the Reduction's own. -/
theorem thashArityProblemT_realCF (pkSeedDist : ProbComp (Bytes 16)) (n : ℕ) :
    Reduction.thashArityProblemT Link.vp (primsG (liftC realCF)) pkSeedDist n =
      Reduction.thashArityProblemT Link.vp Link.prims pkSeedDist n := by
  exact @congrArg CompressFn (SM_DT_TCR_Problem Unit (Bytes 16) (Bytes 22)
    {xs : List (Bytes 16) // xs.length = n} (Bytes 16)) _ _
    (fun c => Reduction.thashArityProblemT Link.vp (primsG c) pkSeedDist n) liftC_realCF

/-- Ideal-model adversaries against the Reduction's tight-cap arity-`n` SM-TCR game. -/
abbrev TcrAdv128T (pkSeedDist : ProbComp (Bytes 16)) (n : ℕ) := TcrAdv (F128T pkSeedDist n)

/-- The adversary against the Reduction's tight-cap arity-`n` problem at the table `g`. -/
def instRT {pkSeedDist : ProbComp (Bytes 16)} {n : ℕ} (A : TcrAdv128T pkSeedDist n)
    (g : CF St Blk) :
    SM_DT_TCR_Adversary (Reduction.thashArityProblemT Link.vp (primsG (liftC g)) pkSeedDist n) where
  State := A.State
  choose := simulateQ (instImpl g) A.choose
  forge := fun st pk => simulateQ (instImpl₀ g) (A.forge st pk)

/-- Advantage against the Reduction's tight-cap arity-`n` SM-TCR game in the ideal-compression
model. -/
noncomputable def tcrArityTAdvantage (pkSeedDist : ProbComp (Bytes 16)) (n : ℕ)
    (A : TcrAdv128T pkSeedDist n) : ℝ≥0∞ :=
  idealAdv fun g => SM_DT_TCR_Experiment (instRT A g)

theorem tcrArityTAdvantage_def (pkSeedDist : ProbComp (Bytes 16)) (n : ℕ)
    (A : TcrAdv128T pkSeedDist n) :
    tcrArityTAdvantage pkSeedDist n A = 𝒟[do
      let g ← $ᵗ (CF St Blk)
      SM_DT_TCR_Experiment (instRT A g)] {true} :=
  idealAdv_def _

theorem tcrArityTAdvantage_eq (pkSeedDist : ProbComp (Bytes 16)) (n : ℕ)
    (A : TcrAdv128T pkSeedDist n) :
    tcrArityTAdvantage pkSeedDist n A = tcrAdvantage (F128T pkSeedDist n) A := by
  refine (idealAdv_congr fun g => ?_).trans (tcrAdvantage_eq_idealAdv (F128T pkSeedDist n) A).symm
  exact SM_DT_TCR_Experiment_congr (ι := Unit) (PkSeed := Bytes 16) (Tweak := Bytes 22)
    (M := {xs : List (Bytes 16) // xs.length = n}) (Y := Bytes 16) pkSeedDist
    (fun pk t m => (primsG (liftC g)).Thash pk t m.1) ((F128T pkSeedDist n).evalT g)
    (fun _ => List (Bytes 16)) (fun _ => (primsG (liftC g)).Thash) ((F128T pkSeedDist n).evalC g)
    (Reduction.arityTargets Link.vp n) (F128T pkSeedDist n).numTargets
    (by funext pk t m; exact primsG_Thash_shape g pk t m.1)
    (by funext _ pk t xs; exact primsG_Thash_shape g pk t xs)
    (by simp only [F128T])
    A.State (simulateQ (instImpl g) A.choose)
    (fun st pk => simulateQ (instImpl₀ g) (A.forge st pk))

/-- SM-TCR of the 128s `Thash` at arity `1` (`F`) or `2` (`H`), tight cap, in the
ideal-compression model. -/
theorem tcrArityT_bound_128s (pkSeedDist : ProbComp (Bytes 16)) (n : ℕ) (hn : n = 1 ∨ n = 2)
    (γ : ℝ≥0∞) (hγ : ∀ s, Pr{let s' ← pkSeedDist}[s' = s] ≤ γ)
    (A : TcrAdv128T pkSeedDist n) (q₁ qch qc L q₂ : ℕ)
    (hq₁ : A.ChooseBound q₁) (hch : A.ChalBound qch) (hc : A.CollBound qc)
    (hL : A.CollLen L) (hq₂ : A.ForgeBound q₂) :
    tcrArityTAdvantage pkSeedDist n A ≤ (q₂ + 1 : ℕ) * ((2 : ℝ≥0∞) ^ 128)⁻¹ + q₁ * γ +
      (2 * q₁ + (qch + qc) * (1 + 2 * L) + 2 : ℕ) * ((2 : ℝ≥0∞) ^ 256)⁻¹ := by
  have hs : ∀ (t : Bytes 22) (m : {xs : List (Bytes 16) // xs.length = n}),
      (tblocks t m.1).2 = [] := by
    intro t m
    rcases hn with rfl | rfl
    · exact tblocks_snd_of_length_one t m.1 m.2
    · exact tblocks_snd_of_length_two t m.1 m.2
  rw [tcrArityTAdvantage_eq, ← card_St_inv]
  exact tcr_bound (F128T pkSeedDist n) sb128_injective γ hγ hs btw128
    (fun t m => btw128_tblocks t m.1) (fun _ t m => btw128_tblocks t m)
    (fun t m m' h => Subtype.ext (tblocks_injective (Prod.ext h ((hs t m).trans (hs t m').symm))).2)
    _ (fun y => (prEvent_out16_eq y).le) A q₁ qch qc L q₂ hq₁ hch hc hL hq₂

/-- `tcrArityT_bound_128s` for a uniform public seed. -/
theorem tcrArityT_bound_128s_uniform (n : ℕ) (hn : n = 1 ∨ n = 2)
    (A : TcrAdv128T ($ᵗ (Bytes 16)) n) (q₁ qch qc L q₂ : ℕ)
    (hq₁ : A.ChooseBound q₁) (hch : A.ChalBound qch) (hc : A.CollBound qc)
    (hL : A.CollLen L) (hq₂ : A.ForgeBound q₂) :
    tcrArityTAdvantage ($ᵗ (Bytes 16)) n A ≤ (q₂ + 1 : ℕ) * ((2 : ℝ≥0∞) ^ 128)⁻¹ + q₁ * ((2 : ℝ≥0∞) ^ 128)⁻¹ +
      (2 * q₁ + (qch + qc) * (1 + 2 * L) + 2 : ℕ) * ((2 : ℝ≥0∞) ^ 256)⁻¹ :=
  tcrArityT_bound_128s _ n hn _ (fun s => (prEvent_uniform_bytes16_eq s).le) A q₁ qch qc L q₂ hq₁ hch hc hL hq₂

/-- SM-TCR of the 128s `Thash` at any arity `n`, tight cap, in the ideal-compression model.  An
arity-`n` input spans `(22 + 16 n + 8)/64` blocks after the first message block; `L` bounds the
continuation length of the adversary's collection queries. -/
theorem tcrArityT_bound_128s_multi (pkSeedDist : ProbComp (Bytes 16)) (n : ℕ)
    (γ : ℝ≥0∞) (hγ : ∀ s, Pr{let s' ← pkSeedDist}[s' = s] ≤ γ)
    (A : TcrAdv128T pkSeedDist n) (q₁ qch qc L q₂ : ℕ)
    (hq₁ : A.ChooseBound q₁) (hch : A.ChalBound qch) (hc : A.CollBound qc)
    (hL : A.CollLen L) (hq₂ : A.ForgeBound q₂) :
    tcrArityTAdvantage pkSeedDist n A ≤ (q₂ + 2 * ((22 + 16 * n + 8) / 64) + 4 : ℕ) * ((2 : ℝ≥0∞) ^ 128)⁻¹ + q₁ * γ +
      (18 * tcrMultiQ q₁ qch qc L q₂ ((22 + 16 * n + 8) / 64) ^ 2 + 2 * q₁ +
        (qch + qc) * (1 + 2 * max ((22 + 16 * n + 8) / 64) L) + 1 : ℕ) * ((2 : ℝ≥0∞) ^ 256)⁻¹ := by
  rw [tcrArityTAdvantage_eq, ← card_St_inv]
  exact tcr_bound_multi (F128T pkSeedDist n) sb128_injective γ hγ _
    (fun t m => (tblocks_snd_length t m.1).trans (by rw [m.2])) btw128
    (fun t m => btw128_tblocks t m.1) (fun _ t m => btw128_tblocks t m)
    (fun t m m' h => Subtype.ext (tblocks_injective h).2)
    _ (fun y => (prEvent_out16_eq y).le) A q₁ qch qc L q₂ hq₁ hch hc hL hq₂

/-- `tcrArityT_bound_128s_multi` for a uniform public seed. -/
theorem tcrArityT_bound_128s_multi_uniform (n : ℕ)
    (A : TcrAdv128T ($ᵗ (Bytes 16)) n) (q₁ qch qc L q₂ : ℕ)
    (hq₁ : A.ChooseBound q₁) (hch : A.ChalBound qch) (hc : A.CollBound qc)
    (hL : A.CollLen L) (hq₂ : A.ForgeBound q₂) :
    tcrArityTAdvantage ($ᵗ (Bytes 16)) n A ≤ (q₂ + 2 * ((22 + 16 * n + 8) / 64) + 4 : ℕ) * ((2 : ℝ≥0∞) ^ 128)⁻¹ + q₁ * ((2 : ℝ≥0∞) ^ 128)⁻¹ +
      (18 * tcrMultiQ q₁ qch qc L q₂ ((22 + 16 * n + 8) / 64) ^ 2 + 2 * q₁ +
        (qch + qc) * (1 + 2 * max ((22 + 16 * n + 8) / 64) L) + 1 : ℕ) * ((2 : ℝ≥0∞) ^ 256)⁻¹ :=
  tcrArityT_bound_128s_multi _ n _ (fun s => (prEvent_uniform_bytes16_eq s).le) A q₁ qch qc L q₂ hq₁ hch hc hL hq₂

/-- SM-TCR of the 128s `T_len` (arity `len = 35`, nine blocks after the first message block), tight cap. -/
theorem tcrLen_bound_128s (pkSeedDist : ProbComp (Bytes 16))
    (γ : ℝ≥0∞) (hγ : ∀ s, Pr{let s' ← pkSeedDist}[s' = s] ≤ γ)
    (A : TcrAdv128T pkSeedDist 35) (q₁ qch qc L q₂ : ℕ)
    (hq₁ : A.ChooseBound q₁) (hch : A.ChalBound qch) (hc : A.CollBound qc)
    (hL : A.CollLen L) (hq₂ : A.ForgeBound q₂) :
    tcrArityTAdvantage pkSeedDist 35 A ≤ (q₂ + 22 : ℕ) * ((2 : ℝ≥0∞) ^ 128)⁻¹ + q₁ * γ +
      (18 * (q₁ + q₂ + (qch + qc) * (1 + max 9 L) + 21) ^ 2 + 2 * q₁ +
        (qch + qc) * (1 + 2 * max 9 L) + 1 : ℕ) * ((2 : ℝ≥0∞) ^ 256)⁻¹ := by
  have h := tcrArityT_bound_128s_multi pkSeedDist 35 γ hγ A q₁ qch qc L q₂ hq₁ hch hc hL hq₂
  have e0 : (22 + 16 * 35 + 8) / 64 = 9 := rfl
  have e1 : q₂ + 2 * 9 + 4 = q₂ + 22 := rfl
  have e2 : tcrMultiQ q₁ qch qc L q₂ 9 =
      q₁ + q₂ + (qch + qc) * (1 + max 9 L) + 21 := rfl
  rw [e0, e1, e2] at h
  exact h

/-- `tcrLen_bound_128s` for a uniform public seed. -/
theorem tcrLen_bound_128s_uniform
    (A : TcrAdv128T ($ᵗ (Bytes 16)) 35) (q₁ qch qc L q₂ : ℕ)
    (hq₁ : A.ChooseBound q₁) (hch : A.ChalBound qch) (hc : A.CollBound qc)
    (hL : A.CollLen L) (hq₂ : A.ForgeBound q₂) :
    tcrArityTAdvantage ($ᵗ (Bytes 16)) 35 A ≤ (q₂ + 22 : ℕ) * ((2 : ℝ≥0∞) ^ 128)⁻¹ + q₁ * ((2 : ℝ≥0∞) ^ 128)⁻¹ +
      (18 * (q₁ + q₂ + (qch + qc) * (1 + max 9 L) + 21) ^ 2 + 2 * q₁ +
        (qch + qc) * (1 + 2 * max 9 L) + 1 : ℕ) * ((2 : ℝ≥0∞) ^ 256)⁻¹ :=
  tcrLen_bound_128s _ _ (fun s => (prEvent_uniform_bytes16_eq s).le) A q₁ qch qc L q₂ hq₁ hch hc hL hq₂

/-- SM-TCR of the 128s `T_k` (arity `k = 14`, three blocks after the first message block), tight cap. -/
theorem tcrK_bound_128s (pkSeedDist : ProbComp (Bytes 16))
    (γ : ℝ≥0∞) (hγ : ∀ s, Pr{let s' ← pkSeedDist}[s' = s] ≤ γ)
    (A : TcrAdv128T pkSeedDist 14) (q₁ qch qc L q₂ : ℕ)
    (hq₁ : A.ChooseBound q₁) (hch : A.ChalBound qch) (hc : A.CollBound qc)
    (hL : A.CollLen L) (hq₂ : A.ForgeBound q₂) :
    tcrArityTAdvantage pkSeedDist 14 A ≤ (q₂ + 10 : ℕ) * ((2 : ℝ≥0∞) ^ 128)⁻¹ + q₁ * γ +
      (18 * (q₁ + q₂ + (qch + qc) * (1 + max 3 L) + 9) ^ 2 + 2 * q₁ +
        (qch + qc) * (1 + 2 * max 3 L) + 1 : ℕ) * ((2 : ℝ≥0∞) ^ 256)⁻¹ := by
  have h := tcrArityT_bound_128s_multi pkSeedDist 14 γ hγ A q₁ qch qc L q₂ hq₁ hch hc hL hq₂
  have e0 : (22 + 16 * 14 + 8) / 64 = 3 := rfl
  have e1 : q₂ + 2 * 3 + 4 = q₂ + 10 := rfl
  have e2 : tcrMultiQ q₁ qch qc L q₂ 3 =
      q₁ + q₂ + (qch + qc) * (1 + max 3 L) + 9 := rfl
  rw [e0, e1, e2] at h
  exact h

/-- `tcrK_bound_128s` for a uniform public seed. -/
theorem tcrK_bound_128s_uniform
    (A : TcrAdv128T ($ᵗ (Bytes 16)) 14) (q₁ qch qc L q₂ : ℕ)
    (hq₁ : A.ChooseBound q₁) (hch : A.ChalBound qch) (hc : A.CollBound qc)
    (hL : A.CollLen L) (hq₂ : A.ForgeBound q₂) :
    tcrArityTAdvantage ($ᵗ (Bytes 16)) 14 A ≤ (q₂ + 10 : ℕ) * ((2 : ℝ≥0∞) ^ 128)⁻¹ + q₁ * ((2 : ℝ≥0∞) ^ 128)⁻¹ +
      (18 * (q₁ + q₂ + (qch + qc) * (1 + max 3 L) + 9) ^ 2 + 2 * q₁ +
        (qch + qc) * (1 + 2 * max 3 L) + 1 : ℕ) * ((2 : ℝ≥0∞) ^ 256)⁻¹ :=
  tcrK_bound_128s _ _ (fun s => (prEvent_uniform_bytes16_eq s).le) A q₁ qch qc L q₂ hq₁ hch hc hL hq₂

theorem len_128s : Link.vp.params.len = 35 := by decide

theorem k_128s : Link.vp.params.k = 14 := by decide

/-! ## SM-TCR on `F` (the WOTS+ chain steps), tight cap -/

/-- `FWots128 pkSeedDist` with the tight cap `Reduction.wotsStepTargetsT Link.vp`. -/
def FWots128T (pkSeedDist : ProbComp (Bytes 16)) :
    THFam St Blk (Bytes 16) (Bytes 22) (Bytes 16) (Bytes 16) Unit where
  IV := IV128
  sb := sb128
  seedGen := pkSeedDist
  tch := fun t x => tblocks t [x]
  out := out16
  Msg := fun _ => List (Bytes 16)
  cch := fun _ t xs => tblocks t xs
  cout := fun _ => out16
  numTargets := Reduction.wotsStepTargetsT Link.vp

/-- The Reduction's tight-cap SM-TCR problem on `F` at the generic primitives over the table `g`
is the problem of `FWots128T` at `g`. -/
theorem wotsTcrProblemT_eq_tcrProb (pkSeedDist : ProbComp (Bytes 16)) (g : CF St Blk) :
    Reduction.wotsTcrProblemT Link.vp (primsG (liftC g)) pkSeedDist =
      (FWots128T pkSeedDist).tcrProb g := by
  have h : (primsG (liftC g)).Thash =
      fun pk a xs => out16 (keyedChain IV128 sb128 g pk (tblocks a xs)) := by
    funext pk a xs
    exact primsG_Thash_shape g pk a xs
  show ({ th := { seedGen := pkSeedDist, eval := fun pk t x => (primsG (liftC g)).Thash pk t [x] },
          thColl := { Msg := fun _ => List (Bytes 16), eval := fun _ => (primsG (liftC g)).Thash },
          numTargets := Reduction.wotsStepTargetsT Link.vp } :
        SM_DT_TCR_Problem Unit (Bytes 16) (Bytes 22) (Bytes 16) (Bytes 16)) = _
  rw [h]
  simp only [THFam.tcrProb, THFam.coll, FWots128T]
  rfl

/-- At the real compression function the problem is the Reduction's own. -/
theorem wotsTcrProblemT_realCF (pkSeedDist : ProbComp (Bytes 16)) :
    Reduction.wotsTcrProblemT Link.vp (primsG (liftC realCF)) pkSeedDist =
      Reduction.wotsTcrProblemT Link.vp Link.prims pkSeedDist := by
  exact @congrArg CompressFn (SM_DT_TCR_Problem Unit (Bytes 16) (Bytes 22) (Bytes 16)
    (Bytes 16)) _ _ (fun c => Reduction.wotsTcrProblemT Link.vp (primsG c) pkSeedDist) liftC_realCF

/-- Ideal-model adversaries against the Reduction's tight-cap SM-TCR game on `F`. -/
abbrev WotsTcrAdv128T (pkSeedDist : ProbComp (Bytes 16)) := TcrAdv (FWots128T pkSeedDist)

/-- The adversary against the Reduction's tight-cap SM-TCR problem on `F` at the table `g`. -/
def instWT {pkSeedDist : ProbComp (Bytes 16)} (A : WotsTcrAdv128T pkSeedDist) (g : CF St Blk) :
    SM_DT_TCR_Adversary (Reduction.wotsTcrProblemT Link.vp (primsG (liftC g)) pkSeedDist) where
  State := A.State
  choose := simulateQ (instImpl g) A.choose
  forge := fun st pk => simulateQ (instImpl₀ g) (A.forge st pk)

/-- Advantage against the Reduction's tight-cap SM-TCR game on `F` in the ideal-compression
model. -/
noncomputable def wotsTcrTAdvantage (pkSeedDist : ProbComp (Bytes 16))
    (A : WotsTcrAdv128T pkSeedDist) : ℝ≥0∞ :=
  idealAdv fun g => SM_DT_TCR_Experiment (instWT A g)

theorem wotsTcrTAdvantage_def (pkSeedDist : ProbComp (Bytes 16)) (A : WotsTcrAdv128T pkSeedDist) :
    wotsTcrTAdvantage pkSeedDist A = 𝒟[do
      let g ← $ᵗ (CF St Blk)
      SM_DT_TCR_Experiment (instWT A g)] {true} :=
  idealAdv_def _

theorem wotsTcrTAdvantage_eq (pkSeedDist : ProbComp (Bytes 16)) (A : WotsTcrAdv128T pkSeedDist) :
    wotsTcrTAdvantage pkSeedDist A = tcrAdvantage (FWots128T pkSeedDist) A := by
  refine (idealAdv_congr fun g => ?_).trans (tcrAdvantage_eq_idealAdv (FWots128T pkSeedDist) A).symm
  exact SM_DT_TCR_Experiment_congr (ι := Unit) (PkSeed := Bytes 16) (Tweak := Bytes 22)
    (M := Bytes 16) (Y := Bytes 16) pkSeedDist
    (fun pk t x => (primsG (liftC g)).Thash pk t [x]) ((FWots128T pkSeedDist).evalT g)
    (fun _ => List (Bytes 16)) (fun _ => (primsG (liftC g)).Thash) ((FWots128T pkSeedDist).evalC g)
    (Reduction.wotsStepTargetsT Link.vp) (FWots128T pkSeedDist).numTargets
    (by funext pk t x; exact primsG_Thash_shape g pk t [x])
    (by funext _ pk t xs; exact primsG_Thash_shape g pk t xs)
    (by simp only [FWots128T])
    A.State (simulateQ (instImpl g) A.choose)
    (fun st pk => simulateQ (instImpl₀ g) (A.forge st pk))

/-- SM-TCR of the 128s `F`, tight cap, in the ideal-compression model. -/
theorem wotsTcrT_bound_128s (pkSeedDist : ProbComp (Bytes 16))
    (γ : ℝ≥0∞) (hγ : ∀ s, Pr{let s' ← pkSeedDist}[s' = s] ≤ γ)
    (A : WotsTcrAdv128T pkSeedDist) (q₁ qch qc L q₂ : ℕ)
    (hq₁ : A.ChooseBound q₁) (hch : A.ChalBound qch) (hc : A.CollBound qc)
    (hL : A.CollLen L) (hq₂ : A.ForgeBound q₂) :
    wotsTcrTAdvantage pkSeedDist A ≤ (q₂ + 1 : ℕ) * ((2 : ℝ≥0∞) ^ 128)⁻¹ + q₁ * γ +
      (2 * q₁ + (qch + qc) * (1 + 2 * L) + 2 : ℕ) * ((2 : ℝ≥0∞) ^ 256)⁻¹ := by
  have hs : ∀ (t : Bytes 22) (x : Bytes 16), (tblocks t [x]).2 = [] :=
    fun t x => tblocks_snd_of_length_one t [x] rfl
  rw [wotsTcrTAdvantage_eq, ← card_St_inv]
  exact tcr_bound (FWots128T pkSeedDist) sb128_injective γ hγ hs btw128
    (fun t x => btw128_tblocks t [x]) (fun _ t m => btw128_tblocks t m)
    (fun t x x' h => List.singleton_injective
      (tblocks_injective (Prod.ext h ((hs t x).trans (hs t x').symm))).2)
    _ (fun y => (prEvent_out16_eq y).le) A q₁ qch qc L q₂ hq₁ hch hc hL hq₂

/-- `wotsTcrT_bound_128s` for a uniform public seed. -/
theorem wotsTcrT_bound_128s_uniform
    (A : WotsTcrAdv128T ($ᵗ (Bytes 16))) (q₁ qch qc L q₂ : ℕ)
    (hq₁ : A.ChooseBound q₁) (hch : A.ChalBound qch) (hc : A.CollBound qc)
    (hL : A.CollLen L) (hq₂ : A.ForgeBound q₂) :
    wotsTcrTAdvantage ($ᵗ (Bytes 16)) A ≤ (q₂ + 1 : ℕ) * ((2 : ℝ≥0∞) ^ 128)⁻¹ + q₁ * ((2 : ℝ≥0∞) ^ 128)⁻¹ +
      (2 * q₁ + (qch + qc) * (1 + 2 * L) + 2 : ℕ) * ((2 : ℝ≥0∞) ^ 256)⁻¹ :=
  wotsTcrT_bound_128s _ _ (fun s => (prEvent_uniform_bytes16_eq s).le) A q₁ qch qc L q₂ hq₁ hch hc hL hq₂

end Ideal

#print axioms Ideal.thashArityProblemT_eq_tcrProb
#print axioms Ideal.thashArityProblemT_realCF
#print axioms Ideal.tcrArityTAdvantage_def
#print axioms Ideal.tcrArityTAdvantage_eq
#print axioms Ideal.tcrArityT_bound_128s
#print axioms Ideal.tcrArityT_bound_128s_uniform
#print axioms Ideal.tcrArityT_bound_128s_multi
#print axioms Ideal.tcrArityT_bound_128s_multi_uniform
#print axioms Ideal.tcrLen_bound_128s
#print axioms Ideal.tcrLen_bound_128s_uniform
#print axioms Ideal.tcrK_bound_128s
#print axioms Ideal.tcrK_bound_128s_uniform
#print axioms Ideal.wotsTcrProblemT_eq_tcrProb
#print axioms Ideal.wotsTcrProblemT_realCF
#print axioms Ideal.wotsTcrTAdvantage_def
#print axioms Ideal.wotsTcrTAdvantage_eq
#print axioms Ideal.wotsTcrT_bound_128s
#print axioms Ideal.wotsTcrT_bound_128s_uniform
