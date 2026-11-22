import Ideal.Realize.TcrWotsFine

/-!
# The single-block SM-TCR legs with message blocks uncharged

`tcr_bound_fine` (`Games/TcrFine.lean`) instantiated at the 128s families of `tcr_bound`:

* `tcrArityT_bound_128s_fine` (class TCR, arities `1`, `2`), `wotsTcrT_bound_128s_fine`
  (WOTS-chain TCR);
* `epsTcrF γ p qM`: the fine error, `epsTcrF_le_t` its normal form;
* `classTcrLeg_fine(E)` (arities `1`, `2`, the answer-storing realiser `Tcr.realizesTcr3S`, raw
  cap `Tcr.qMT qf`) and `wotsTcrLeg_fine(E)` (`Wots.realizesWotsTcrL`, raw cap `Wots.qMW qf qs`):
  the averaged advantages of the Reduction's adversaries.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security TweakableHash ENNReal

namespace Ideal

open Ideal.Realize

attribute [local irreducible] Reduction.arityTargets Reduction.tcrTargets
attribute [local irreducible] Reduction.Lazy.sparseTable Reduction.Lazy.structSecIdx

/-- The fine SM-TCR error (`tcr_bound_fine` at `β = γ`). -/
noncomputable def epsTcrF (γ : ℝ≥0∞) (p : P5) (qM : ℕ) : ℝ≥0∞ :=
  (qM + 1 : ℕ) * ((2 : ℝ≥0∞) ^ 128)⁻¹ + (p.q₂ + 1 : ℕ) * ((2 : ℝ≥0∞) ^ 128)⁻¹ * γ + p.q₁ * γ +
    (2 * p.q₁ + (p.qch + p.qc) * (1 + 2 * p.L) + 2 + 2 * ((p.q₁ + (p.qch + p.qc)) * max 1 p.L) +
      2 * p.q₂ : ℕ) * ((2 : ℝ≥0∞) ^ 256)⁻¹

theorem tcrArityT_bound_128s_fine (pkSeedDist : ProbComp (Bytes 16)) (n : ℕ) (hn : n = 1 ∨ n = 2)
    (γ : ℝ≥0∞) (hγ : ∀ s, Pr{let s' ← pkSeedDist}[s' = s] ≤ γ)
    (A : TcrAdv128T pkSeedDist n) (q₁ qch qc L q₂ : ℕ)
    (hq₁ : A.ChooseBound q₁) (hch : A.ChalBound qch) (hc : A.CollBound qc)
    (hL : A.CollLen L) (hq₂ : A.ForgeBound q₂)
    (fC : A.State → Bytes 16 → OracleComp (pcS St Blk) (ℕ × {xs : List (Bytes 16) // xs.length = n}))
    (hfC : ∀ st pk, A.forge st pk = simulateQ (expandImpl IV128) (fC st pk))
    (bad : Bytes 16 → Prop) (β : ℝ≥0∞) (hβ : Pr{let s ← pkSeedDist}[bad s] ≤ β) (qM : ℕ)
    (hqM : ∀ st pk, ¬ bad pk → IsQueryBoundP (fC st pk) (fun t => isRawC t = true) qM)
    (hfree : ∀ st pk, ¬ bad pk → AllQueriesSatisfy (fC st pk) (freeC (sb128 pk))) :
    tcrArityTAdvantage pkSeedDist n A ≤
      (qM + 1 : ℕ) * ((2 : ℝ≥0∞) ^ 128)⁻¹ + (q₂ + 1 : ℕ) * ((2 : ℝ≥0∞) ^ 128)⁻¹ * β + q₁ * γ +
        (2 * q₁ + (qch + qc) * (1 + 2 * L) + 2 + 2 * ((q₁ + (qch + qc)) * max 1 L) + 2 * q₂ : ℕ) *
          ((2 : ℝ≥0∞) ^ 256)⁻¹ := by
  have hs : ∀ (t : Bytes 22) (m : {xs : List (Bytes 16) // xs.length = n}),
      (tblocks t m.1).2 = [] := by
    intro t m
    rcases hn with rfl | rfl
    · exact tblocks_snd_of_length_one t m.1 m.2
    · exact tblocks_snd_of_length_two t m.1 m.2
  rw [tcrArityTAdvantage_eq, ← card_St_inv]
  exact tcr_bound_fine (F := F128T pkSeedDist n) sb128_injective γ hγ hs btw128
    (fun t m => btw128_tblocks t m.1) (fun _ t m => btw128_tblocks t m)
    (fun t m m' h => Subtype.ext (tblocks_injective (Prod.ext h ((hs t m).trans (hs t m').symm))).2)
    _ (fun y => (prEvent_out16_eq y).le) A q₁ qch qc L q₂ hq₁ hch hc hL hq₂ fC hfC bad β hβ qM
    hqM hfree

theorem wotsTcrT_bound_128s_fine (pkSeedDist : ProbComp (Bytes 16))
    (γ : ℝ≥0∞) (hγ : ∀ s, Pr{let s' ← pkSeedDist}[s' = s] ≤ γ)
    (A : WotsTcrAdv128T pkSeedDist) (q₁ qch qc L q₂ : ℕ)
    (hq₁ : A.ChooseBound q₁) (hch : A.ChalBound qch) (hc : A.CollBound qc)
    (hL : A.CollLen L) (hq₂ : A.ForgeBound q₂)
    (fC : A.State → Bytes 16 → OracleComp (pcS St Blk) (ℕ × Bytes 16))
    (hfC : ∀ st pk, A.forge st pk = simulateQ (expandImpl IV128) (fC st pk))
    (bad : Bytes 16 → Prop) (β : ℝ≥0∞) (hβ : Pr{let s ← pkSeedDist}[bad s] ≤ β) (qM : ℕ)
    (hqM : ∀ st pk, ¬ bad pk → IsQueryBoundP (fC st pk) (fun t => isRawC t = true) qM)
    (hfree : ∀ st pk, ¬ bad pk → AllQueriesSatisfy (fC st pk) (freeC (sb128 pk))) :
    wotsTcrTAdvantage pkSeedDist A ≤
      (qM + 1 : ℕ) * ((2 : ℝ≥0∞) ^ 128)⁻¹ + (q₂ + 1 : ℕ) * ((2 : ℝ≥0∞) ^ 128)⁻¹ * β + q₁ * γ +
        (2 * q₁ + (qch + qc) * (1 + 2 * L) + 2 + 2 * ((q₁ + (qch + qc)) * max 1 L) + 2 * q₂ : ℕ) *
          ((2 : ℝ≥0∞) ^ 256)⁻¹ := by
  have hs : ∀ (t : Bytes 22) (x : Bytes 16), (tblocks t [x]).2 = [] :=
    fun t x => tblocks_snd_of_length_one t [x] rfl
  rw [wotsTcrTAdvantage_eq, ← card_St_inv]
  exact tcr_bound_fine (F := FWots128T pkSeedDist) sb128_injective γ hγ hs btw128
    (fun t x => btw128_tblocks t [x]) (fun _ t m => btw128_tblocks t m)
    (fun t x x' h => List.singleton_injective
      (tblocks_injective (Prod.ext h ((hs t x).trans (hs t x').symm))).2)
    _ (fun y => (prEvent_out16_eq y).le) A q₁ qch qc L q₂ hq₁ hch hc hL hq₂ fC hfC bad β hβ qM
    hqM hfree

section Legs

variable {S : ForgerI} {oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)}
  {pkSeedDist : ProbComp (Bytes 16)} {γ : ℝ≥0∞} {qf qs ℓ : ℕ}
  (hγ : ∀ s, Pr{let s' ← pkSeedDist}[s' = s] ≤ γ)
  (hqf : ∀ pk, IsQueryBoundP (S.main pk)
    (fun i => Ideal.Realize.isPortQ (S := List Byte) i = true) qf)
  (hqs : ∀ pk, IsQueryBoundP (S.main pk)
    (fun i => Ideal.Realize.isSignQ (S := List Byte) i = true) qs)
  (hlong : ∀ pk, IsQueryBoundP (S.main pk)
    (fun i => Ideal.Realize.isLongQ (S := List Byte) ℓ i = true) 0)
  (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ)

include hγ hqf hqs hlong hout

/-- **The class-TCR leg at arity `1` or `2` with the message blocks uncharged (SUF).** -/
theorem classTcrLeg_fine (n : ℕ) (hn : n = 1 ∨ n = 2) :
    (cfAvg fun g => SM_DT_TCR_Advantage (Reduction.bTcrArM n
        (S.typedS (optRandU oR) pkSeedDist g))) ≤
      epsTcrF γ (Tcr.tcrP3 qf qs ℓ) (Tcr.qMT qf) := by
  let R := Tcr.realizesTcr3S S oR pkSeedDist n hqf hqs hlong hout
  rw [R.avg]
  refine (tcrArityT_bound_128s_fine pkSeedDist n hn γ hγ R.A _ _ _ _ _ R.hq₁ R.hch R.hc R.hL R.hq₂
    (fun st pk => Tcr.forgeP3GC S oR n st.1 (clampL Tcr.Bmax st.2.1) st.2.2 pk)
    (fun st pk => Tcr.forgeP3G_eq_expand S oR n _ _ _ pk) (· = Wots.zero16) γ (hγ _) (Tcr.qMT qf)
    (fun st pk h => Tcr.forgeP3GC_boundR S oR n hqf hqs hlong hout st.1 _
      (clampL_mem _ _) st.2.2 pk h)
    (fun st pk _ => Tcr.forgeP3GC_free S oR n _ _ _ pk)).trans (le_of_eq ?_)
  rw [epsTcrF]

/-- **The class-TCR leg at arity `1` or `2` with the message blocks uncharged (EUF).** -/
theorem classTcrLeg_fineE (n : ℕ) (hn : n = 1 ∨ n = 2) :
    (cfAvg fun g => SM_DT_TCR_Advantage (Reduction.bTcrArM n
        (S.typedE (optRandU oR) pkSeedDist g))) ≤
      epsTcrF γ (Tcr.tcrP3 qf qs ℓ) (Tcr.qMT qf) := by
  let R := Tcr.realizesTcr3E S oR pkSeedDist n hqf hqs hlong hout
  rw [R.avg]
  refine (tcrArityT_bound_128s_fine pkSeedDist n hn γ hγ R.A _ _ _ _ _ R.hq₁ R.hch R.hc R.hL R.hq₂
    (fun st pk => Tcr.forgeP3GC S oR n st.1 (clampL Tcr.Bmax st.2.1) st.2.2 pk)
    (fun st pk => Tcr.forgeP3G_eq_expand S oR n _ _ _ pk) (· = Wots.zero16) γ (hγ _) (Tcr.qMT qf)
    (fun st pk h => Tcr.forgeP3GC_boundR S oR n hqf hqs hlong hout st.1 _
      (clampL_mem _ _) st.2.2 pk h)
    (fun st pk _ => Tcr.forgeP3GC_free S oR n _ _ _ pk)).trans (le_of_eq ?_)
  rw [epsTcrF]

/-- **The WOTS-chain TCR leg with the message blocks uncharged (SUF).** -/
theorem wotsTcrLeg_fine :
    (cfAvg fun g => SM_DT_TCR_Advantage (Reduction.rTcrT pkSeedDist
        (Reduction.Lazy.bWotsS (S.typedS (optRandU oR) pkSeedDist g)))) ≤
      epsTcrF γ (Wots.pWL qf qs ℓ) (Wots.qMW qf qs) := by
  let R := Wots.realizesWotsTcrL (oR := oR) (pkSeedDist := pkSeedDist) hqf hqs hlong hout
  have h1 : (cfAvg fun g => SM_DT_TCR_Advantage (Reduction.rTcrT pkSeedDist
      (Reduction.Lazy.bWotsS (S.typedS (optRandU oR) pkSeedDist g)))) =
      wotsTcrTAdvantage pkSeedDist R.A :=
    (cfAvg_of_evalDist_eq R.eq).trans (cfAdvantage_eq_idealAdvT _)
  rw [h1]
  refine (wotsTcrT_bound_128s_fine pkSeedDist γ hγ R.A _ _ _ _ _ R.hq₁ R.hch R.hc R.hL R.hq₂
    (Wots.tcrForgeC S oR) (fun st pk => Wots.tcrForge_eq_expand S oR st pk) (· = Wots.zero16) γ
    (hγ _) (Wots.qMW qf qs) (fun st pk h => Wots.tcrForgeC_boundR S oR hqf hqs hlong hout st pk h)
    (fun st pk _ => Wots.tcrForgeC_free S oR st pk)).trans (le_of_eq ?_)
  rw [epsTcrF]

/-- **The WOTS-chain TCR leg with the message blocks uncharged (EUF).** -/
theorem wotsTcrLeg_fineE :
    (cfAvg fun g => SM_DT_TCR_Advantage (Reduction.rTcrT pkSeedDist
        (Reduction.Lazy.bWotsS (S.typedE (optRandU oR) pkSeedDist g)))) ≤
      epsTcrF γ (Wots.pWL qf qs ℓ) (Wots.qMW qf qs) := by
  let R := Wots.realizesWotsTcrLE (oR := oR) (pkSeedDist := pkSeedDist) hqf hqs hlong hout
  have h1 : (cfAvg fun g => SM_DT_TCR_Advantage (Reduction.rTcrT pkSeedDist
      (Reduction.Lazy.bWotsS (S.typedE (optRandU oR) pkSeedDist g)))) =
      wotsTcrTAdvantage pkSeedDist R.A :=
    (cfAvg_of_evalDist_eq R.eq).trans (cfAdvantage_eq_idealAdvT _)
  rw [h1]
  refine (wotsTcrT_bound_128s_fine pkSeedDist γ hγ R.A _ _ _ _ _ R.hq₁ R.hch R.hc R.hL R.hq₂
    (Wots.tcrForgeC S oR) (fun st pk => Wots.tcrForge_eq_expand S oR st pk) (· = Wots.zero16) γ
    (hγ _) (Wots.qMW qf qs) (fun st pk h => Wots.tcrForgeC_boundR S oR hqf hqs hlong hout st pk h)
    (fun st pk _ => Wots.tcrForgeC_free S oR st pk)).trans (le_of_eq ?_)
  rw [epsTcrF]

end Legs

/-- The fine SM-TCR error in normal form. -/
theorem epsTcrF_le_t {p : P5} {Qc N Q qM : ℕ} (h : p.Le Qc N) (h0 : p.q₁ = 0) (hQ : qM ≤ Q) :
    epsTcrF γu p qM ≤ nf (Q + 1) (2 * Qc + 42 * N + 2 + (Qc + 40 * N + 1)) := by
  have hc := coll_le h (1 + 2 * p.L) 21 (by have := h.2.2.2.1; omega)
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have e : epsTcrF γu p qM =
      nf (qM + 1) ((p.q₂ + 1) + (2 * p.q₁ + (p.qch + p.qc) * (1 + 2 * p.L) + 2 +
        2 * ((p.q₁ + (p.qch + p.qc)) * max 1 p.L) + 2 * p.q₂)) := by
    unfold epsTcrF nf
    rw [h0]
    have : ((2 : ℝ≥0∞) ^ 256)⁻¹ = ((2 : ℝ≥0∞) ^ 128)⁻¹ * ((2 : ℝ≥0∞) ^ 128)⁻¹ := by
      rw [← ENNReal.mul_inv (Or.inl (by positivity)) (Or.inl (by simp)), ← pow_add]
    rw [this]
    push_cast
    ring
  rw [e]
  have hm : max 1 p.L ≤ 10 := max_le (by norm_num) h4
  have hq : (0 + (p.qch + p.qc)) * max 1 p.L ≤ 20 * N := by
    rw [zero_add]
    calc (p.qch + p.qc) * max 1 p.L ≤ (2 * N) * 10 := Nat.mul_le_mul (by omega) hm
      _ = 20 * N := by ring
  rw [h0]
  exact nf_mono (by omega) (by omega)

end Ideal

#print axioms Ideal.tcrArityT_bound_128s_fine
#print axioms Ideal.wotsTcrT_bound_128s_fine
#print axioms Ideal.classTcrLeg_fine
#print axioms Ideal.wotsTcrLeg_fine
#print axioms Ideal.epsTcrF_le_t
