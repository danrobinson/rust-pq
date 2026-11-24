import MIdeal.MixedTables
import Ideal.Inst.TcrTight128

namespace MIdeal.Hash128f
open Ideal MLink TweakableHash SLHDSA OracleComp OracleSpec ENNReal

abbrev vp := Sha2Set.s128f.vp
abbrev primitives (g : CompressionTables) := tablePrimitives g vp.params

attribute [local irreducible] Reduction.arityTargets Reduction.tcrTargets
  Reduction.wotsStepTargetsT Reduction.wotsStepTargets

theorem shape (g : CompressionTables) (pk : Bytes 16) (a : Bytes 22) (xs : List (Bytes 16)) :
    (primitives g).Thash pk a xs = out16 (keyedChain IV128 sb128 g.1 pk (tblocks a xs)) := by
  apply Eq.trans _ (primsG_Thash_shape g.1 pk a xs)
  change sha2ThashMixed (liftC g.1) (lift512 g.2) vp.params pk a xs =
    sha2ThashG (liftC g.1) Link.vp.params pk a xs
  simp only [sha2ThashMixed, sha2ThashG, show vp.params.n = 16 from rfl,
    show Link.vp.params.n = 16 from rfl, ite_eq_left, ite_self]
  rfl

def F128T (pkSeedDist : ProbComp (Bytes 16)) (n : ℕ) :
    THFam St Blk (Bytes 16) (Bytes 22) {xs : List (Bytes 16) // xs.length = n} (Bytes 16) Unit :=
  { Ideal.F128T pkSeedDist n with numTargets := Reduction.arityTargets vp n }

/-- The Reduction's tight-cap arity-`n` SM-TCR problem at the generic primitives over the table
`g` is the problem of `F128T` at `g`. -/
theorem thashArityProblemT_eq_tcrProb (pkSeedDist : ProbComp (Bytes 16)) (n : ℕ) (g : CompressionTables) :
    Reduction.thashArityProblemT vp (primitives g) pkSeedDist n =
      (F128T pkSeedDist n).tcrProb g.1 := by
  have h : (primitives g).Thash =
      fun pk a xs => out16 (keyedChain IV128 sb128 g.1 pk (tblocks a xs)) := by
    funext pk a xs
    exact shape g pk a xs
  show ({ th := { seedGen := pkSeedDist, eval := fun pk t m => (primitives g).Thash pk t m.1 },
          thColl := { Msg := fun _ => List (Bytes 16), eval := fun _ => (primitives g).Thash },
          numTargets := Reduction.arityTargets vp n } :
        SM_DT_TCR_Problem Unit (Bytes 16) (Bytes 22) {xs : List (Bytes 16) // xs.length = n}
          (Bytes 16)) = _
  rw [h]
  simp only [THFam.tcrProb, THFam.coll, F128T]
  rfl

theorem tcrArityT_bound_multi (pkSeedDist : ProbComp (Bytes 16)) (n : ℕ)
    (γ : ℝ≥0∞) (hγ : ∀ s, Pr{let s' ← pkSeedDist}[s' = s] ≤ γ)
    (A : TcrAdv (F128T pkSeedDist n)) (q₁ qch qc L q₂ : ℕ)
    (hq₁ : A.ChooseBound q₁) (hch : A.ChalBound qch) (hc : A.CollBound qc)
    (hL : A.CollLen L) (hq₂ : A.ForgeBound q₂) :
    tcrAdvantage (F128T pkSeedDist n) A ≤ (q₂ + 2 * ((22 + 16 * n + 8) / 64) + 4 : ℕ) * ((2 : ℝ≥0∞) ^ 128)⁻¹ + q₁ * γ +
      (18 * tcrMultiQ q₁ qch qc L q₂ ((22 + 16 * n + 8) / 64) ^ 2 + 2 * q₁ +
        (qch + qc) * (1 + 2 * max ((22 + 16 * n + 8) / 64) L) + 1 : ℕ) * ((2 : ℝ≥0∞) ^ 256)⁻¹ := by
  rw [← card_St_inv]
  exact tcr_bound_multi (F128T pkSeedDist n) sb128_injective γ hγ _
    (fun t m => (tblocks_snd_length t m.1).trans (by rw [m.2])) btw128
    (fun t m => btw128_tblocks t m.1) (fun _ t m => btw128_tblocks t m)
    (fun t m m' h => Subtype.ext (tblocks_injective h).2)
    _ (fun y => (prEvent_out16_eq y).le) A q₁ qch qc L q₂ hq₁ hch hc hL hq₂

def FWots128T (pkSeedDist : ProbComp (Bytes 16)) :
    THFam St Blk (Bytes 16) (Bytes 22) (Bytes 16) (Bytes 16) Unit :=
  { Ideal.FWots128T pkSeedDist with numTargets := Reduction.wotsStepTargetsT vp }

/-- The Reduction's tight-cap SM-TCR problem on `F` at the generic primitives over the table `g`
is the problem of `FWots128T` at `g`. -/
theorem wotsTcrProblemT_eq_tcrProb (pkSeedDist : ProbComp (Bytes 16)) (g : CompressionTables) :
    Reduction.wotsTcrProblemT vp (primitives g) pkSeedDist =
      (FWots128T pkSeedDist).tcrProb g.1 := by
  have h : (primitives g).Thash =
      fun pk a xs => out16 (keyedChain IV128 sb128 g.1 pk (tblocks a xs)) := by
    funext pk a xs
    exact shape g pk a xs
  show ({ th := { seedGen := pkSeedDist, eval := fun pk t x => (primitives g).Thash pk t [x] },
          thColl := { Msg := fun _ => List (Bytes 16), eval := fun _ => (primitives g).Thash },
          numTargets := Reduction.wotsStepTargetsT vp } :
        SM_DT_TCR_Problem Unit (Bytes 16) (Bytes 22) (Bytes 16) (Bytes 16)) = _
  rw [h]
  simp only [THFam.tcrProb, THFam.coll, FWots128T]
  rfl

theorem wotsTcr_bound (pkSeedDist : ProbComp (Bytes 16))
    (γ : ℝ≥0∞) (hγ : ∀ s, Pr{let s' ← pkSeedDist}[s' = s] ≤ γ)
    (A : TcrAdv (FWots128T pkSeedDist)) (q₁ qch qc L q₂ : ℕ)
    (hq₁ : A.ChooseBound q₁) (hch : A.ChalBound qch) (hc : A.CollBound qc)
    (hL : A.CollLen L) (hq₂ : A.ForgeBound q₂) :
    tcrAdvantage (FWots128T pkSeedDist) A ≤ (q₂ + 1 : ℕ) * ((2 : ℝ≥0∞) ^ 128)⁻¹ + q₁ * γ +
      (2 * q₁ + (qch + qc) * (1 + 2 * L) + 2 : ℕ) * ((2 : ℝ≥0∞) ^ 256)⁻¹ := by
  have hs : ∀ (t : Bytes 22) (x : Bytes 16), (tblocks t [x]).2 = [] :=
    fun t x => tblocks_snd_of_length_one t [x] rfl
  rw [← card_St_inv]
  exact tcr_bound (FWots128T pkSeedDist) sb128_injective γ hγ hs btw128
    (fun t x => btw128_tblocks t [x]) (fun _ t m => btw128_tblocks t m)
    (fun t x x' h => List.singleton_injective
      (tblocks_injective (Prod.ext h ((hs t x).trans (hs t x').symm))).2)
    _ (fun y => (prEvent_out16_eq y).le) A q₁ qch qc L q₂ hq₁ hch hc hL hq₂

end MIdeal.Hash128f
