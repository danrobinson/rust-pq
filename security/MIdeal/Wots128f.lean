import MIdeal.Hash128f
import Ideal.Inst.WotsUd128

namespace MIdeal.Hash128f
open Ideal MLink TweakableHash SLHDSA OracleComp OracleSpec ENNReal

attribute [local irreducible] Reduction.wotsChainTargets

def chainFamily (seeds : ProbComp (Bytes 16)) :=
  { FWots128T seeds with numTargets := Reduction.wotsChainTargets vp }

theorem wotsPreProblem_eq_preProb (pkSeedDist : ProbComp (Bytes 16)) (g : CompressionTables) :
    Reduction.wotsPreProblem vp (primitives g) pkSeedDist =
      (chainFamily pkSeedDist).preProb id Function.injective_id g.1 := by
  have h : (primitives g).Thash =
      fun pk a xs => out16 (keyedChain IV128 sb128 g.1 pk (tblocks a xs)) := by
    funext pk a xs
    exact shape g pk a xs
  show ({ th := { seedGen := pkSeedDist, eval := fun pk t x => (primitives g).Thash pk t [x] },
          emb := id, emb_injective := Function.injective_id,
          thColl := { Msg := fun _ => List (Bytes 16), eval := fun _ => (primitives g).Thash },
          numTargets := Reduction.wotsChainTargets vp } :
        SM_DT_PRE_Problem Unit (Bytes 16) (Bytes 22) (Bytes 16) (Bytes 16) (Bytes 16)) = _
  rw [h]
  simp only [THFam.preProb, THFam.coll, chainFamily, FWots128T]
  rfl

noncomputable local instance (g : CompressionTables) : SampleableType (primitives g).Y := sampY128

theorem wotsUdProblem_eq_udProb (pkSeedDist : ProbComp (Bytes 16)) (g : CompressionTables) :
    Reduction.wotsUdProblem vp (primitives g) pkSeedDist =
      @THFam.udProb St Blk (Bytes 16) (Bytes 22) (Bytes 16) (Bytes 16) (Bytes 16) Unit
        (chainFamily pkSeedDist) sampY128 sampY128 id Function.injective_id g.1 := by
  have h : (primitives g).Thash =
      fun pk a xs => out16 (keyedChain IV128 sb128 g.1 pk (tblocks a xs)) := by
    funext pk a xs
    exact shape g pk a xs
  show ({ th := { seedGen := pkSeedDist, eval := fun pk t x => (primitives g).Thash pk t [x] },
          emb := id, emb_injective := Function.injective_id,
          inputGen := @uniformSample (Bytes 16) sampY128,
          outputGen := @uniformSample (Bytes 16) sampY128,
          thColl := { Msg := fun _ => List (Bytes 16), eval := fun _ => (primitives g).Thash },
          numTargets := Reduction.wotsChainTargets vp } :
        SM_DT_UD_Problem Unit (Bytes 16) (Bytes 22) (Bytes 16) (Bytes 16) (Bytes 16)) = _
  rw [h]
  simp only [THFam.udProb, THFam.coll, chainFamily, FWots128T]
  rfl

private theorem card_bytes16_inv :
    (Fintype.card (Bytes 16) : ℝ≥0∞)⁻¹ = ((2 : ℝ≥0∞) ^ 128)⁻¹ := by
  rw [card_bytes]
  norm_num

theorem wotsPre_bound (pkSeedDist : ProbComp (Bytes 16))
    (γ : ℝ≥0∞) (hγ : ∀ s, Pr{let s' ← pkSeedDist}[s' = s] ≤ γ)
    (A : PreAdv (chainFamily pkSeedDist) (Bytes 16)) (q₁ qch qc L q₂ : ℕ)
    (hq₁ : A.ChooseBound q₁) (hch : A.ChalBound qch) (hc : A.CollBound qc)
    (hL : A.CollLen L) (hq₂ : A.InvertBound q₂) :
    @preAdvantage St Blk (Bytes 16) (Bytes 22) (Bytes 16) (Bytes 16) (Bytes 16) Unit
      _ _ sampY128 _ (chainFamily pkSeedDist) id Function.injective_id A ≤ 2 * (q₂ + 1 : ℕ) * ((2 : ℝ≥0∞) ^ 128)⁻¹ + q₁ * γ +
      (2 * q₁ + (qch + qc) * (1 + 2 * L) + 2 : ℕ) * ((2 : ℝ≥0∞) ^ 256)⁻¹ := by
  have hs : ∀ (t : Bytes 22) (x : Bytes 16), (tblocks t [x]).2 = [] :=
    fun t x => tblocks_snd_of_length_one t [x] rfl
  rw [← card_St_inv]
  refine (@pre_bound St Blk (Bytes 16) (Bytes 22) (Bytes 16) (Bytes 16) (Bytes 16) Unit
    _ _ _ _ _ _ _ _ sampY128 _
    (chainFamily pkSeedDist) id Function.injective_id sb128_injective γ hγ hs btw128
    (fun t x => btw128_tblocks t [x]) (fun _ t m => btw128_tblocks t m)
    (fun t x x' h => List.singleton_injective
      (tblocks_injective (Prod.ext h ((hs t x).trans (hs t x').symm))).2)
    _ (fun y => (prEvent_out16_eq y).le) A q₁ qch qc L q₂ hq₁ hch hc hL hq₂).trans (le_of_eq ?_)
  rw [card_bytes16_inv]
  ring

theorem wotsUd_bound (pkSeedDist : ProbComp (Bytes 16))
    (γ : ℝ≥0∞) (hγ : ∀ s, Pr{let s' ← pkSeedDist}[s' = s] ≤ γ)
    (A : UdAdv (chainFamily pkSeedDist)) (q₁ qch qc L q₂ : ℕ)
    (hq₁ : A.PickBound q₁) (hch : A.ChalBound qch) (hc : A.CollBound qc)
    (hL : A.CollLen L) (hq₂ : A.DistBound q₂) :
    @udRealI St Blk (Bytes 16) (Bytes 22) (Bytes 16) (Bytes 16) (Bytes 16) Unit
        _ sampY128 sampY128 _ (chainFamily pkSeedDist) id Function.injective_id A ≤
      @udIdealI St Blk (Bytes 16) (Bytes 22) (Bytes 16) (Bytes 16) (Bytes 16) Unit
        _ sampY128 sampY128 _ (chainFamily pkSeedDist) id Function.injective_id A + q₂ * ((2 : ℝ≥0∞) ^ 128)⁻¹ + 2 * q₁ * γ +
        (2 * (2 * q₁ + (qch + qc) * (1 + 2 * L) + 1) : ℕ) * ((2 : ℝ≥0∞) ^ 256)⁻¹ := by
  have hs : ∀ (t : Bytes 22) (x : Bytes 16), (tblocks t [x]).2 = [] :=
    fun t x => tblocks_snd_of_length_one t [x] rfl
  rw [← card_St_inv, ← card_bytes16_inv]
  exact @ud_bound St Blk (Bytes 16) (Bytes 22) (Bytes 16) (Bytes 16) (Bytes 16) Unit
    _ _ _ _ _ _ _ sampY128 _ sampY128 _
    (chainFamily pkSeedDist) id Function.injective_id sb128_injective γ hγ hs btw128
    (fun t x => btw128_tblocks t [x]) (fun _ t m => btw128_tblocks t m)
    (fun t x x' h => List.singleton_injective
      (tblocks_injective (Prod.ext h ((hs t x).trans (hs t x').symm))).2)
    prEvent_out16 A q₁ qch qc L q₂ hq₁ hch hc hL hq₂

/-- The reverse inequality of `wotsUd_bound`, with the same error. -/
theorem wotsUd_bound_ge (pkSeedDist : ProbComp (Bytes 16))
    (γ : ℝ≥0∞) (hγ : ∀ s, Pr{let s' ← pkSeedDist}[s' = s] ≤ γ)
    (A : UdAdv (chainFamily pkSeedDist)) (q₁ qch qc L q₂ : ℕ)
    (hq₁ : A.PickBound q₁) (hch : A.ChalBound qch) (hc : A.CollBound qc)
    (hL : A.CollLen L) (hq₂ : A.DistBound q₂) :
    @udIdealI St Blk (Bytes 16) (Bytes 22) (Bytes 16) (Bytes 16) (Bytes 16) Unit
        _ sampY128 sampY128 _ (chainFamily pkSeedDist) id Function.injective_id A ≤
      @udRealI St Blk (Bytes 16) (Bytes 22) (Bytes 16) (Bytes 16) (Bytes 16) Unit
        _ sampY128 sampY128 _ (chainFamily pkSeedDist) id Function.injective_id A + q₂ * ((2 : ℝ≥0∞) ^ 128)⁻¹ + 2 * q₁ * γ +
        (2 * (2 * q₁ + (qch + qc) * (1 + 2 * L) + 1) : ℕ) * ((2 : ℝ≥0∞) ^ 256)⁻¹ := by
  have hs : ∀ (t : Bytes 22) (x : Bytes 16), (tblocks t [x]).2 = [] :=
    fun t x => tblocks_snd_of_length_one t [x] rfl
  rw [← card_St_inv, ← card_bytes16_inv]
  exact @ud_bound_ge St Blk (Bytes 16) (Bytes 22) (Bytes 16) (Bytes 16) (Bytes 16) Unit
    _ _ _ _ _ _ _ sampY128 _ sampY128 _
    (chainFamily pkSeedDist) id Function.injective_id sb128_injective γ hγ hs btw128
    (fun t x => btw128_tblocks t [x]) (fun _ t m => btw128_tblocks t m)
    (fun t x x' h => List.singleton_injective
      (tblocks_injective (Prod.ext h ((hs t x).trans (hs t x').symm))).2)
    prEvent_out16 A q₁ qch qc L q₂ hq₁ hch hc hL hq₂

end MIdeal.Hash128f
