import Ideal.Games.DsprBridge
import Ideal.Games.DsprIdeal
import Ideal.Core.HiddenPrefix
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Source-final-validity SM-DSPR (stand-alone) in the ideal-compression model: the bound

`Ideal.dspr_bound`: for a Merkle–Damgård tweakable hash whose attacked member has a single
block after the seed block, with that block injective in the message and determining the tweak,

`Success(A) ≤ SPprob(A) + 2·q₁·γ + (4·q₁ + 2·qch + 3)/|St|`

(`dsprSuccessI`, `dsprSPI`: VCVio's `Success` and `SPProbability` averaged over a uniform
compression table), where `q₁`, `q₂` bound the compression queries of the two phases of `A`,
`qch` its challenge queries, `γ` is the guessing probability of the seed, and `ρ ≤ 1` bounds the
probability that the output map misses a fixed value on a uniform chaining value, with
`ρ ^ (|M| - 1 - q₂) ≤ 1/2`.  `dspr_bound_uniform`: the last condition holds when the output of a
uniform chaining value hits every value with probability exactly `1/|M|`, `32 ≤ |M|` and
`4·q₂ ≤ |M|` (`pow_le_half`).

Proof: bridges (`dsprSuccessI_eq_realGame`, `dsprSPI_eq_realGame`); `hiddenPrefix` applied to
the DSPR game (real ≤ ideal + err) and to the negated `SPprob` game (ideal ≤ real + err,
`idealGame_le_realGame`), `err = q₁·γ + (2·q₁ + qch + 1)/|St|`; `dspr_ideal_le` (ideal DSPR
≤ ideal `SPprob` + `1/|St|`).
-/

open OracleComp OracleSpec ENNReal

namespace Ideal

open TweakableHash Ideal.HP

/-! ## Negating phase two -/

section Neg

variable {St Blk PkSeed σ : Type}

theorem prT_not_map (X : ProbComp Bool) : prT (not <$> X) = 1 - prT X := by
  unfold prT
  rw [prEvent_map, ← prEvent_not_eq_one_sub]
  congr 2
  funext b
  cases b <;> simp

theorem realGame_not [SampleableType (CF St Blk)] (IV : St) (sb : PkSeed → Blk)
    (seedGen : ProbComp PkSeed)
    (prog₁ : OracleComp (unifSpec + (hS St Blk + chainS St Blk)) σ)
    (P₂ : PkSeed → σ → OracleComp (unifSpec + hS St Blk) Bool) :
    realGame IV sb seedGen prog₁ (fun pk x => not <$> P₂ pk x) =
      not <$> realGame IV sb seedGen prog₁ P₂ := by
  simp only [realGame, simulateQ_map, map_bind]

theorem idealGame_not [DecidableEq St] [DecidableEq Blk] [SampleableType St] (IV : St)
    (sb : PkSeed → Blk) (seedGen : ProbComp PkSeed)
    (prog₁ : OracleComp (unifSpec + (hS St Blk + chainS St Blk)) σ)
    (P₂ : PkSeed → σ → OracleComp (unifSpec + hS St Blk) Bool) :
    idealGame IV sb seedGen prog₁ (fun pk x => not <$> P₂ pk x) =
      not <$> idealGame IV sb seedGen prog₁ P₂ := by
  simp only [idealGame_eq_phases, simulateQ_map, map_bind, StateT.run'_eq, StateT.run_map,
    Functor.map_map]

/-- **The hidden-prefix hop in the other direction**: the ideal game returns `true` at most as
often as the real game, up to the same error (`hiddenPrefix` applied to the negated phase
two). -/
theorem idealGame_le_realGame [Fintype St] [DecidableEq St] [DecidableEq Blk]
    [SampleableType St] [Finite Blk] [SampleableType (CF St Blk)]
    (IV : St) (sb : PkSeed → Blk) (hsb : Function.Injective sb) (seedGen : ProbComp PkSeed)
    (γ : ℝ≥0∞) (hγ : ∀ s, Pr{let s' ← seedGen}[s' = s] ≤ γ)
    (prog₁ : OracleComp (unifSpec + (hS St Blk + chainS St Blk)) σ)
    (P₂ : PkSeed → σ → OracleComp (unifSpec + hS St Blk) Bool) (q₁ C L : ℕ)
    (hq : IsQueryBoundP prog₁ (fun i => isPub i = true) q₁)
    (hC : IsQueryBoundP prog₁ (fun i => isChain i = true) C)
    (hL : AllQueriesSatisfy prog₁ (chainLenLe L)) :
    𝒟[idealGame IV sb seedGen prog₁ P₂] {true} ≤
      𝒟[realGame IV sb seedGen prog₁ P₂] {true} + q₁ * γ +
        (2 * q₁ + C * (1 + 2 * L) + 1 : ℕ) * (Fintype.card St : ℝ≥0∞)⁻¹ := by
  have h := hiddenPrefix IV sb hsb seedGen γ hγ prog₁ (fun pk x => not <$> P₂ pk x) q₁ C L
    hq hC hL
  rw [← prT_eq, ← prT_eq, realGame_not, idealGame_not, prT_not_map, prT_not_map] at h
  rw [← prT_eq, ← prT_eq]
  have hi : prT (idealGame IV sb seedGen prog₁ P₂) ≤ 1 := prT_le_one _
  rw [← ENNReal.sub_sub_cancel one_ne_top hi, tsub_le_iff_left]
  rw [tsub_le_iff_right] at h
  refine h.trans (le_of_eq ?_)
  ring

end Neg

/-! ## The exponent condition -/

/-- `(1 - 1/N)^(N - 1 - q) ≤ 1/2` when `32 ≤ N` and `4·q ≤ N`. -/
theorem real_pow_le_half (N q : ℕ) (hN : 32 ≤ N) (hq : 4 * q ≤ N) :
    (1 - (N : ℝ)⁻¹) ^ (N - 1 - q) ≤ 1 / 2 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have h0 : (0 : ℝ) ≤ 1 - (N : ℝ)⁻¹ := by
    rw [sub_nonneg]
    exact inv_le_one_of_one_le₀ (by exact_mod_cast (show 1 ≤ N by omega))
  have h1 : 1 - (N : ℝ)⁻¹ ≤ Real.exp (-(N : ℝ)⁻¹) := by
    have := Real.add_one_le_exp (-(N : ℝ)⁻¹)
    linarith
  have hk : (23 : ℝ) / 32 ≤ ((N - 1 - q : ℕ) : ℝ) * (N : ℝ)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hN0]
    have : 23 * N ≤ 32 * (N - 1 - q) := by omega
    have h' : ((23 * N : ℕ) : ℝ) ≤ ((32 * (N - 1 - q) : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at h'
    linarith
  have h2 : (2 : ℝ) ≤ Real.exp (23 / 32) := by
    have e : Real.exp (23 / 32) = Real.exp (23 / 512) ^ 16 := by
      rw [← Real.exp_nat_mul]
      norm_num
    rw [e]
    have h3 : (1 + 23 / 512 : ℝ) ≤ Real.exp (23 / 512) := by
      have := Real.add_one_le_exp (23 / 512 : ℝ)
      linarith
    refine le_trans ?_ (pow_le_pow_left₀ (by norm_num) h3 16)
    norm_num
  calc (1 - (N : ℝ)⁻¹) ^ (N - 1 - q) ≤ Real.exp (-(N : ℝ)⁻¹) ^ (N - 1 - q) :=
        pow_le_pow_left₀ h0 h1 _
    _ = Real.exp (-(((N - 1 - q : ℕ) : ℝ) * (N : ℝ)⁻¹)) := by
        rw [← Real.exp_nat_mul]
        ring_nf
    _ ≤ Real.exp (-(23 / 32)) := Real.exp_le_exp.mpr (by linarith)
    _ ≤ 1 / 2 := by
        rw [Real.exp_neg, one_div]
        exact inv_anti₀ (by norm_num) h2

/-- `real_pow_le_half` in `ℝ≥0∞`. -/
theorem pow_le_half (N q : ℕ) (hN : 32 ≤ N) (hq : 4 * q ≤ N) :
    (1 - (N : ℝ≥0∞)⁻¹) ^ (N - 1 - q) ≤ 2⁻¹ := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have e : (1 - (N : ℝ≥0∞)⁻¹) = ENNReal.ofReal (1 - (N : ℝ)⁻¹) := by
    rw [ENNReal.ofReal_sub _ (inv_nonneg.mpr hN0.le), ENNReal.ofReal_one,
      ENNReal.ofReal_inv_of_pos hN0, ENNReal.ofReal_natCast]
  rw [e, ← ENNReal.ofReal_pow (by
    rw [sub_nonneg]
    exact inv_le_one_of_one_le₀ (by exact_mod_cast (show 1 ≤ N by omega)))]
  refine (ENNReal.ofReal_le_ofReal (real_pow_le_half N q hN hq)).trans (le_of_eq ?_)
  rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num)]
  norm_num

/-! ## The bound -/

variable {St Blk PkSeed Tweak M Y : Type} {F : THFam St Blk PkSeed Tweak M Y Empty}

/-- **SM-DSPR (source final validity) in the ideal-compression model.** -/
theorem dspr_bound [Fintype St] [DecidableEq St] [DecidableEq Blk] [SampleableType St]
    [Finite Blk] [SampleableType (CF St Blk)]
    [Fintype M] [DecidableEq Tweak] [DecidableEq M] [DecidableEq Y]
    (hsb : Function.Injective F.sb)
    (γ : ℝ≥0∞) (hγ : ∀ s, Pr{let s' ← F.seedGen}[s' = s] ≤ γ)
    (hsingle : ∀ t m, (F.tch t m).2 = [])
    (btw : Blk → Tweak) (hbtwT : ∀ t m, btw (F.tch t m).1 = t)
    (hinj : ∀ t m m', (F.tch t m).1 = (F.tch t m').1 → m = m')
    (ρ : ℝ≥0∞) (hρ : ∀ y, Pr{let u ← $ᵗ St}[F.out u ≠ y] ≤ ρ) (hρ1 : ρ ≤ 1)
    (A : DsprAdv F) (q₁ qch q₂ : ℕ)
    (hq₁ : A.ChooseBound q₁) (hqch : A.ChalBound qch) (hq₂ : A.GuessBound q₂)
    (hhalf : ρ ^ (Fintype.card M - 1 - q₂) ≤ 2⁻¹) :
    dsprSuccessI F A ≤ dsprSPI F A + 2 * (q₁ * γ) +
      (4 * q₁ + 2 * qch + 3 : ℕ) * (Fintype.card St : ℝ≥0∞)⁻¹ := by
  have hL : AllQueriesSatisfy (dsprProg₁ A) (chainLenLe 0) :=
    dsprProg₁_chainLen A fun t m => by rw [hsingle]; exact le_rfl
  rw [dsprSuccessI_eq_realGame, dsprSPI_eq_realGame]
  refine (hiddenPrefix F.IV F.sb hsb F.seedGen γ hγ (dsprProg₁ A) (dsprP₂ winS A) q₁ qch 0
    (dsprProg₁_pubBound A hq₁) (dsprProg₁_chainBound A hqch) hL).trans ?_
  refine (add_le_add_left (add_le_add_left
    ((dspr_ideal_le hsingle btw hbtwT hinj ρ hρ hρ1 A q₂ hq₂ hhalf).trans
      (add_le_add_left (idealGame_le_realGame F.IV F.sb hsb F.seedGen γ hγ (dsprProg₁ A)
        (dsprP₂ winSP A) q₁ qch 0 (dsprProg₁_pubBound A hq₁) (dsprProg₁_chainBound A hqch) hL)
        _)) _) _).trans (le_of_eq ?_)
  push_cast
  ring

/-- `dspr_bound` when the output of a uniform chaining value is uniform on a set of the size of
the message space: the exponent condition holds for `32 ≤ |M|` and `q₂ ≤ |M|/4`. -/
theorem dspr_bound_uniform [Fintype St] [DecidableEq St] [DecidableEq Blk] [SampleableType St]
    [Finite Blk] [SampleableType (CF St Blk)]
    [Fintype M] [DecidableEq Tweak] [DecidableEq M] [DecidableEq Y]
    (hsb : Function.Injective F.sb)
    (γ : ℝ≥0∞) (hγ : ∀ s, Pr{let s' ← F.seedGen}[s' = s] ≤ γ)
    (hsingle : ∀ t m, (F.tch t m).2 = [])
    (btw : Blk → Tweak) (hbtwT : ∀ t m, btw (F.tch t m).1 = t)
    (hinj : ∀ t m m', (F.tch t m).1 = (F.tch t m').1 → m = m')
    (hout : ∀ y, Pr{let u ← $ᵗ St}[F.out u = y] = (Fintype.card M : ℝ≥0∞)⁻¹)
    (hM : 32 ≤ Fintype.card M)
    (A : DsprAdv F) (q₁ qch q₂ : ℕ)
    (hq₁ : A.ChooseBound q₁) (hqch : A.ChalBound qch) (hq₂ : A.GuessBound q₂)
    (hq₂M : 4 * q₂ ≤ Fintype.card M) :
    dsprSuccessI F A ≤ dsprSPI F A + 2 * (q₁ * γ) +
      (4 * q₁ + 2 * qch + 3 : ℕ) * (Fintype.card St : ℝ≥0∞)⁻¹ :=
  dspr_bound hsb γ hγ hsingle btw hbtwT hinj (1 - (Fintype.card M : ℝ≥0∞)⁻¹)
    (fun y => by rw [prEvent_not_eq_one_sub, hout]) tsub_le_self A q₁ qch q₂ hq₁ hqch hq₂
    (pow_le_half _ _ hM hq₂M)

end Ideal

#print axioms Ideal.idealGame_le_realGame
#print axioms Ideal.pow_le_half
#print axioms Ideal.dspr_bound
#print axioms Ideal.dspr_bound_uniform
