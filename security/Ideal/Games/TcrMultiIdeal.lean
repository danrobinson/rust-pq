import Ideal.Games.TcrMultiPhase1
import Ideal.Games.TcrMultiPhase2
import Ideal.Games.TcrMultiDom

/-!
# SM-TCR in the ideal-compression model: the ideal game for multi-block members

`tcr_ideal_multi_le`: when every input of the attacked member spans `L + 1` message blocks after
the seed block, the ideal game of `tcrProg₁ A`, `tcrP₂ A` is won with probability at most
`(q₂ + 2 L + 4)·δ + 18·Q²/|St|`, where `δ` bounds the probability that the output map hits a
fixed value on a uniform chaining value, `q₂` is the number of compression queries of the
adversary's second phase and `Q = tcrMultiQ …` bounds the number of table cells sampled in the
game.  `δ` is multiplied neither by the number of targets nor by the number of first-phase
queries.  `tcr_ideal_multi_le'` is the same bound with the explicit polynomial.

Proof (files `TcrMultiBasic`, `TcrMultiSym`, `TcrMultiBuild`, `TcrMultiDom`, `TcrMultiPhase1`,
`TcrMultiPhase2`).

* Phase one (`tcr_multi_phase1_le`).  The invariant `MInv` of the cache after phase one (cached
  cells have pairwise distinct values, none equal to `IV`; every target's block list is complete
  and is the only complete block list of its length with the target's tweak) holds except with
  probability `O(Q²)/|St|`.  The intermediate chaining values of a target are hidden from the
  adversary; this is proved by comparing the real phase one (`conG`) with a symbolic one in
  which a target is answered by its private-row cell alone and its `L` hidden values are drawn
  separately: the eager symbolic game `symE` dominates the real one through `fbuild` until a
  public cell is cached in a hidden row (`dominated_symE`, VCVio's `DominatedUntilBad`), and
  drawing the hidden values commutes with the deferred symbolic game `symD` (`IntertwinesOn`),
  so they may be drawn after phase one, when hitting the cache is a fresh-sample event
  (`prEvent_drawN_not_fillNice`, `build_good`).
* Phase two (`tcr_multi_phase2_le`).  `cv` avoids `IV` and the cached values except with
  probability `(N + 1)/|St|`; then every fresh sample keeps the good predicate (injectivity, no
  value `IV` or `cv`, no complete block list with a target's tweak and the target's output
  other than the target's) except with probability `δ + (2 N + 3)/|St|`: by injectivity the
  block list completed by a fresh cell is unique, so a single target is at risk.  A win
  contradicts the good predicate of the final cache.
-/

open OracleComp OracleSpec ENNReal

namespace Ideal

open TweakableHash

variable {St Blk PkSeed Tweak M Y ι : Type} {F : THFam St Blk PkSeed Tweak M Y ι}

/-- The ideal game with a phase-one invariant that may fail: if `Inv` fails of the phase-one
output and cache with probability at most `ε₁`, and from every output and cache satisfying
`Inv` and every seed the draw of `cv` followed by phase two returns `true` with probability at
most `ε₂`, the ideal game returns `true` with probability at most `ε₁ + ε₂`. -/
theorem idealGame_le_of_prInv [DecidableEq St] [DecidableEq Blk] [SampleableType St]
    {PkSeed σ : Type} (IV : St) (sb : PkSeed → Blk) (seedGen : ProbComp PkSeed)
    (prog₁ : OracleComp (unifSpec + (hS St Blk + chainS St Blk)) σ)
    (P₂ : PkSeed → σ → OracleComp (unifSpec + hS St Blk) Bool)
    (Inv : σ → Cache St Blk → Prop) (ε₁ ε₂ : ℝ≥0∞)
    (h1 : Pr{let z ← (simulateQ (hS St Blk + tS St Blk).romImpl
      (simulateQ chainToT prog₁)).run ∅}[¬ Inv z.1 z.2] ≤ ε₁)
    (h2 : ∀ x c seed, Inv x c →
      Pr{let cv ← ($ᵗ St : ProbComp St);
         let b ← (simulateQ (routeRO IV (sb seed) cv) (P₂ seed x)).run' c}[b = true] ≤ ε₂) :
    𝒟[idealGame IV sb seedGen prog₁ P₂] {true} ≤ ε₁ + ε₂ := by
  rw [← prEvent_eq_evalDist_singleton]
  unfold idealGame idealProg
  rw [simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind]
  refine (prEvent_bind_le_prEvent_add _ _ (fun z => ¬ Inv z.1 z.2) _ (ε := ε₂)
    fun z hz => ?_).trans (add_le_add h1 le_rfl)
  rw [not_not] at hz
  rw [← StateT.run'_eq, simulateQ_bind, roSim.run'_liftM_bind]
  refine prEvent_bind_le_of_forall_le _ _ _ fun seed => ?_
  rw [simulateQ_bind, roSim.run'_liftM_bind]
  refine le_trans (le_of_eq ?_) (h2 z.1 z.2 seed hz)
  simp only [simulateQ_romImpl_route, map_bind]

/-- The bound on the number of table cells sampled in the multi-block SM-TCR game. -/
def tcrMultiQ (q₁ qch qc Lc q₂ L : ℕ) : ℕ :=
  q₁ + q₂ + (qch + qc) * (1 + max L Lc) + 2 * (L + 1) + 1

/-- **The multi-block ideal game, explicit polynomial.** -/
theorem tcr_ideal_multi_le' [Fintype St] [DecidableEq St] [DecidableEq Blk] [SampleableType St]
    [DecidableEq Tweak] [DecidableEq M] [DecidableEq Y]
    (L : ℕ) (hlen : ∀ t m, (F.tch t m).2.length = L)
    (btw : Blk → Tweak) (hbtwT : ∀ t m, btw (F.tch t m).1 = t)
    (hbtwC : ∀ i t m, btw (F.cch i t m).1 = t)
    (hinj : ∀ t m m', F.tch t m = F.tch t m' → m = m')
    (δ : ℝ≥0∞) (hδ : ∀ y, Pr{let u ← $ᵗ St}[F.out u = y] ≤ δ)
    (A : TcrAdv F) (q₁ qch qc Lc q₂ : ℕ) (hq₁ : A.ChooseBound q₁) (hqch : A.ChalBound qch)
    (hqc : A.CollBound qc) (hLc : A.CollLen Lc) (hq₂ : A.ForgeBound q₂) :
    𝒟[idealGame F.IV F.sb F.seedGen (tcrProg₁ A) (tcrP₂ A)] {true} ≤
      (q₂ + 2 * L + 4 : ℕ) * δ +
        ((q₁ + (qch + qc) * (1 + Lc)) * (q₁ + (qch + qc) * (1 + Lc) + 1) +
          (qch * L) * (qch * L + 2 * (q₁ + (qch + qc) * (1 + Lc)) + 1) +
          ((q₂ + 2 * L + 4) *
            (2 * (q₁ + (qch + qc) * (1 + Lc) + qch * (L + 1) + q₂ + 2 * L + 4) + 3) +
            (q₁ + (qch + qc) * (1 + Lc) + qch * (L + 1)) + 1) : ℕ) *
          (Fintype.card St : ℝ≥0∞)⁻¹ := by
  have h1 := tcr_multi_phase1_le L hlen btw hbtwT hbtwC
    (dominated_symE F L hlen btw hbtwT hbtwC) A q₁ qch qc Lc hq₁ hqch hqc hLc
  refine (idealGame_le_of_prInv F.IV F.sb F.seedGen (tcrProg₁ A) (tcrP₂ A)
    (fun x c => MInv F btw L x.2.1 (look c) ∧
      CFin (look c) (q₁ + (qch + qc) * (1 + Lc) + qch * (L + 1))) _ _ h1
    fun x c seed hI => tcr_multi_phase2_le L hlen btw hbtwT hinj δ hδ A q₂ hq₂ x c seed _
      hI.1 hI.2).trans (le_of_eq ?_)
  push_cast
  ring

/-- **The multi-block ideal game.**  With `Q = tcrMultiQ q₁ qch qc Lc q₂ L`. -/
theorem tcr_ideal_multi_le [Fintype St] [DecidableEq St] [DecidableEq Blk] [SampleableType St]
    [DecidableEq Tweak] [DecidableEq M] [DecidableEq Y]
    (L : ℕ) (hlen : ∀ t m, (F.tch t m).2.length = L)
    (btw : Blk → Tweak) (hbtwT : ∀ t m, btw (F.tch t m).1 = t)
    (hbtwC : ∀ i t m, btw (F.cch i t m).1 = t)
    (hinj : ∀ t m m', F.tch t m = F.tch t m' → m = m')
    (δ : ℝ≥0∞) (hδ : ∀ y, Pr{let u ← $ᵗ St}[F.out u = y] ≤ δ)
    (A : TcrAdv F) (q₁ qch qc Lc q₂ : ℕ) (hq₁ : A.ChooseBound q₁) (hqch : A.ChalBound qch)
    (hqc : A.CollBound qc) (hLc : A.CollLen Lc) (hq₂ : A.ForgeBound q₂) :
    𝒟[idealGame F.IV F.sb F.seedGen (tcrProg₁ A) (tcrP₂ A)] {true} ≤
      (q₂ + 2 * L + 4 : ℕ) * δ +
        (18 * tcrMultiQ q₁ qch qc Lc q₂ L ^ 2 : ℕ) * (Fintype.card St : ℝ≥0∞)⁻¹ := by
  refine (tcr_ideal_multi_le' L hlen btw hbtwT hbtwC hinj δ hδ A q₁ qch qc Lc q₂ hq₁ hqch hqc
    hLc hq₂).trans (add_le_add le_rfl (mul_le_mul' (Nat.cast_le.mpr ?_) le_rfl))
  unfold tcrMultiQ
  have hm1 : (qch + qc) * (1 + Lc) ≤ (qch + qc) * (1 + max L Lc) :=
    Nat.mul_le_mul_left _ (by have := le_max_right L Lc; omega)
  have hm2 : qch * (L + 1) ≤ (qch + qc) * (1 + max L Lc) :=
    Nat.mul_le_mul (by omega) (by have := le_max_left L Lc; omega)
  have hm3 : qch * L ≤ qch * (L + 1) := Nat.mul_le_mul_left _ (by omega)
  generalize (qch + qc) * (1 + Lc) = a at *
  generalize (qch + qc) * (1 + max L Lc) = m at *
  generalize qch * (L + 1) = b at *
  generalize qch * L = d at *
  nlinarith [Nat.zero_le q₁, Nat.zero_le q₂, Nat.zero_le L, Nat.zero_le a, Nat.zero_le d,
    Nat.zero_le b, Nat.zero_le m, Nat.mul_le_mul hm1 hm1, Nat.mul_le_mul hm2 hm2,
    Nat.mul_le_mul hm3 hm3, Nat.mul_le_mul hm1 hm2, Nat.mul_le_mul hm3 hm2,
    Nat.mul_le_mul hm3 hm1]

end Ideal

#print axioms Ideal.tcr_ideal_multi_le'
#print axioms Ideal.tcr_ideal_multi_le
