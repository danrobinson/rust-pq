import Ideal.Games.UdFine
import Ideal.Games.Tcr
import Ideal.Games.TcrFV

/-!
# SM-TCR (with collection, and stand-alone source-final-validity) with free chain queries

The fine second-phase accounting of `Games/UdFine.lean` for the two single-block SM-TCR games of
`Games/Tcr.lean` (`tcr_bound`: class TCR at arities `1`, `2`; WOTS-chain TCR) and
`Games/TcrFV.lean` (`tcrFV_bound`: FORS-leaf TCR):

* `prEvent_chainRO_pubHit_le`, `prT_cvBad_le_of`: after the generic phase one (`chainRO`), a fixed
  value is a public value with probability `≤ (q₁ + C)·max 1 L/|St|`; averaged over `cv`, the
  event `cv = IV ∨ PubBad IV cv c` has probability `≤ (1 + 2(q₁ + C)·max 1 L)/|St|`;
* `idealGame_le_of_inv_fine`: `idealGame_le_of_inv` with the phase-two bound required only from
  caches that are not `PubBad`, and allowed to be larger on a set `bad` of seeds;
* `tcr_bound_fine`, `tcrFV_bound_fine`: `(q₂ + 1)·δ` becomes `(qM + 1)·δ + β·(q₂ + 1)·δ` plus
  `(2 q₂ + 1 + 2 (q₁ + C)·max 1 L)/|St|`, for a forger that is the expansion of a program with
  at most `qM` raw compression queries and only free chain queries outside `bad`.
-/

open OracleComp OracleSpec ENNReal

namespace Ideal

open TweakableHash

section Generic

variable {St Blk PkSeed σ : Type} [DecidableEq St] [DecidableEq Blk] [SampleableType St]
  [Fintype St]

/-- **Phase one, generic: a fixed public value.** -/
theorem prEvent_chainRO_pubHit_le (w : St)
    (prog₁ : OracleComp (unifSpec + (hS St Blk + chainS St Blk)) σ) (q₁ C L : ℕ)
    (hq : IsQueryBoundP prog₁ (fun i => isPub i = true) q₁)
    (hC : IsQueryBoundP prog₁ (fun i => isChain i = true) C)
    (hL : AllQueriesSatisfy prog₁ (chainLenLe L)) :
    Pr{let z ← (simulateQ chainRO prog₁).run ∅}[PubHit w z.2] ≤
      ((q₁ + C) * max 1 L : ℕ) * (Fintype.card St : ℝ≥0∞)⁻¹ := by
  classical
  have key := prEvent_bad_le_of_step_ok (chainRO (St := St) (Blk := Blk)) (PubHit w)
    (fun t => isPub t = true ∨ isChain t = true) (chainLenLe L)
    ((max 1 L : ℕ) * (Fintype.card St : ℝ≥0∞)⁻¹) ?_ ?_ prog₁ (q₁ + C) (hq.or hC) hL ∅ (by
      rintro ⟨q, hq⟩; simp at hq)
  · refine key.trans (le_of_eq ?_)
    push_cast
    ring
  · rintro (n | q | q) s hs hpt hok
    · simp [isPub, isChain] at hpt
    · rw [chainRO_run_pub]
      refine (prEvent_randomOracle_pub_pubHit_le w q s hs).trans ?_
      calc (Fintype.card St : ℝ≥0∞)⁻¹ = (1 : ℕ) * (Fintype.card St : ℝ≥0∞)⁻¹ := by simp
        _ ≤ _ := by gcongr; exact le_max_left 1 L
    · rw [chainRO_run_chain]
      refine prEvent_bind_le_of_forall_le_of_support _ _ _ fun z₁ hz₁ => ?_
      have hrow : ¬ PubHit w z₁.2 := by
        rintro ⟨q', hq'⟩
        rcases randomOracle_run_row_cases q.1 s with ⟨v, -, h⟩ | ⟨-, h⟩
        · rw [h, support_pure, Set.mem_singleton_iff] at hz₁
          rw [hz₁] at hq'
          exact hs ⟨q', hq'⟩
        · rw [h, support_map] at hz₁
          obtain ⟨u, -, rfl⟩ := hz₁
          exact hs ⟨q', by rwa [QueryCache.cacheQuery_of_ne (t := .inr _) s u (by simp)] at hq'⟩
      refine (prEvent_romImpl_pubHit_le w _ _ (foldlM_pub_bound _ z₁.1) z₁.2 hrow).trans ?_
      gcongr
      exact (show q.2.length ≤ L from hok).trans (le_max_right 1 L)
  · rintro (n | q | q) s hs hpt z hz
    · rw [chainRO_run_inl, support_map] at hz
      obtain ⟨u, -, rfl⟩ := hz
      exact hs
    · simp [isPub, isChain] at hpt
    · simp [isPub, isChain] at hpt

open Classical in
/-- Averaged over a uniform `cv` drawn after phase one: `cv = IV`, or a public value equal to `IV`
or `cv`. -/
theorem prT_cvBad_le_of (IV : St) (mz : ProbComp (σ × Cache St Blk)) (K : ℝ≥0∞)
    (hK : ∀ w, Pr{let z ← mz}[PubHit w z.2] ≤ K) :
    HP.prT (mz >>= fun z => ($ᵗ St : ProbComp St) >>= fun cv =>
        pure (decide (cv = IV ∨ PubBad IV cv z.2))) ≤
      (Fintype.card St : ℝ≥0∞)⁻¹ + 2 * K := by
  rw [prT_bind_bind_decide]
  set mw := mz >>= fun z => ($ᵗ St : ProbComp St) >>= fun cv => pure (z, cv)
  have e1 : Pr{let w ← mw}[w.2 = IV] = (Fintype.card St : ℝ≥0∞)⁻¹ := by
    rw [← prT_bind_bind_decide (P := fun (_ : σ × Cache St Blk) cv => cv = IV),
      HP.prT_bind_const, HP.prT_bind_pure]
    simp only [decide_eq_true_eq]
    exact SampleableType.prEvent_uniformSample_eq_singleton IV
  have e2 : Pr{let w ← mw}[PubHit IV w.1.2] ≤ K := by
    rw [← prT_bind_bind_decide (P := fun (z : σ × Cache St Blk) (_ : St) => PubHit IV z.2)]
    rw [HP.prT_bind_congr mz _ (fun z : σ × Cache St Blk => pure (decide (PubHit IV z.2)))
      (fun z _ => HP.prT_bind_const _ _), HP.prT_bind_pure]
    simp only [decide_eq_true_eq]
    exact hK IV
  have e3 : Pr{let w ← mw}[PubHit w.2 w.1.2] ≤ K := by
    rw [← prT_bind_bind_decide (P := fun (z : σ × Cache St Blk) (cv : St) => PubHit cv z.2),
      HP.prT_swap]
    refine HP.prT_bind_le_of_forall_le _ _ fun cv _ => ?_
    rw [HP.prT_bind_pure]
    simp only [decide_eq_true_eq]
    exact hK cv
  calc Pr{let w ← mw}[w.2 = IV ∨ PubBad IV w.2 w.1.2]
      ≤ Pr{let w ← mw}[w.2 = IV] +
          (Pr{let w ← mw}[PubHit IV w.1.2] + Pr{let w ← mw}[PubHit w.2 w.1.2]) :=
        (prEvent_or_le _ _ _).trans (add_le_add le_rfl (prEvent_or_le _ _ _))
    _ ≤ (Fintype.card St : ℝ≥0∞)⁻¹ + (K + K) := by rw [e1]; gcongr
    _ = _ := by ring

theorem arith_avg2 (a P b p β : ℝ≥0∞) (h : p ≤ β) :
    a + 1 * P + b * p ≤ a + b * β + 1 * P :=
  calc a + 1 * P + b * p ≤ a + 1 * P + b * β := by gcongr
    _ = _ := by ring

open Classical in
/-- **`idealGame_le_of_inv`, fine form.**  The phase-two bound is required only for `cv ≠ IV`
and caches that are not `PubBad`, and may be larger by `b` on a set `bad` of seeds of
probability `≤ β`. -/
theorem idealGame_le_of_inv_fine (IV : St) (sb : PkSeed → Blk) (seedGen : ProbComp PkSeed)
    (prog₁ : OracleComp (unifSpec + (hS St Blk + chainS St Blk)) σ)
    (P₂ : PkSeed → σ → OracleComp (unifSpec + hS St Blk) Bool)
    (Inv : σ → Cache St Blk → Prop) (a b β : ℝ≥0∞) (bad : PkSeed → Prop)
    (hβ : Pr{let s ← seedGen}[bad s] ≤ β)
    (h1 : ∀ z ∈ support ((simulateQ (hS St Blk + tS St Blk).romImpl
      (simulateQ chainToT prog₁)).run ∅), Inv z.1 z.2)
    (h2 : ∀ x c seed cv, Inv x c → cv ≠ IV → ¬ PubBad IV cv c →
      Pr{let r ← (simulateQ (routeRO IV (sb seed) cv) (P₂ seed x)).run' c}[r = true] ≤
        a + (if bad seed then b else 0))
    (q₁ C L : ℕ) (hq : IsQueryBoundP prog₁ (fun i => isPub i = true) q₁)
    (hC : IsQueryBoundP prog₁ (fun i => isChain i = true) C)
    (hL : AllQueriesSatisfy prog₁ (chainLenLe L)) :
    𝒟[idealGame IV sb seedGen prog₁ P₂] {true} ≤
      a + b * β + (1 + 2 * ((q₁ + C) * max 1 L) : ℕ) * (Fintype.card St : ℝ≥0∞)⁻¹ := by
  have hmz : ∀ w, Pr{let z ← (simulateQ (hS St Blk + tS St Blk).romImpl
      (simulateQ chainToT prog₁)).run ∅}[PubHit w z.2] ≤
        ((q₁ + C) * max 1 L : ℕ) * (Fintype.card St : ℝ≥0∞)⁻¹ := fun w => by
    rw [simulateQ_romImpl_chainToT]
    exact prEvent_chainRO_pubHit_le w prog₁ q₁ C L hq hC hL
  rw [← HP.prT_eq, idealGame_eq_phases]
  set mz := (simulateQ (hS St Blk + tS St Blk).romImpl (simulateQ chainToT prog₁)).run ∅
  refine (prT_bind_le_add_mul mz _ (fun _ => pure false) (fun z => ($ᵗ St : ProbComp St) >>=
      fun cv => pure (decide (cv = IV ∨ PubBad IV cv z.2))) (a + b * β) 1 fun z hz => ?_).trans ?_
  · rw [HP.prT_pure, if_neg (by simp), zero_add]
    refine (prT_bind_le_add_mul seedGen _ (fun _ => pure false) (fun seed => pure (decide (bad seed)))
      (a + 1 * HP.prT (($ᵗ St : ProbComp St) >>=
        fun cv => pure (decide (cv = IV ∨ PubBad IV cv z.2)))) b fun seed _ => ?_).trans ?_
    · rw [HP.prT_pure, if_neg (by simp), zero_add]
      refine (prT_bind_le_add_mul ($ᵗ St) _ (fun _ => pure false)
        (fun cv => pure (decide (cv = IV ∨ PubBad IV cv z.2))) (a + (if bad seed then b else 0)) 1
        fun cv _ => ?_).trans ?_
      · rw [HP.prT_pure, if_neg (by simp), zero_add]
        by_cases hb : cv = IV ∨ PubBad IV cv z.2
        · rw [prT_pure_decide, if_pos hb, one_mul]
          exact (HP.prT_le_one _).trans le_add_self
        · rw [prT_pure_decide, if_neg hb, mul_zero, add_zero]
          simp only [not_or] at hb
          exact h2 z.1 z.2 seed cv (h1 z hz) hb.1 hb.2
      · rw [HP.prT_bind_const, HP.prT_pure, if_neg (by simp), zero_add, prT_pure_decide]
        split_ifs <;> simp only [mul_one, mul_zero, add_zero] <;> exact le_of_eq (by ring)
    · rw [HP.prT_bind_const, HP.prT_pure, if_neg (by simp), zero_add]
      exact arith_avg2 _ _ _ _ _ (by rw [HP.prT_bind_pure]; simpa using hβ)
  · rw [HP.prT_bind_const, HP.prT_pure, if_neg (by simp), zero_add, one_mul]
    refine add_le_add le_rfl ((prT_cvBad_le_of IV mz _ hmz).trans (le_of_eq ?_))
    push_cast
    ring

end Generic

/-! ## The SM-TCR game with collection -/

section Tcr

variable {St Blk PkSeed Tweak M Y ι : Type} {F : THFam St Blk PkSeed Tweak M Y ι}
  [DecidableEq St] [DecidableEq Blk] [SampleableType St] [Fintype St]

/-- Phase two, fine form, from a cache satisfying the invariant that is not `PubBad`. -/
theorem prEvent_tcr_phase2_le_fine [DecidableEq M] [DecidableEq Y]
    (hsingle : ∀ t m, (F.tch t m).2 = [])
    (btw : Blk → Tweak) (hbtwT : ∀ t m, btw (F.tch t m).1 = t)
    (hinj : ∀ t m m', (F.tch t m).1 = (F.tch t m').1 → m = m')
    (δ : ℝ≥0∞) (hδ : ∀ y, Pr{let u ← $ᵗ St}[F.out u = y] ≤ δ)
    (A : TcrAdv F) (q₂ : ℕ) (hq₂ : A.ForgeBound q₂)
    (x : A.State × SM_DT_TCR_State Tweak M) (c : Cache St Blk) (seed : PkSeed) (cv : St)
    (fC : OracleComp (pcS St Blk) (ℕ × M))
    (hfC : A.forge x.1 seed = simulateQ (expandImpl F.IV) fC) (qM : ℕ)
    (hqM : IsQueryBoundP fC (fun t => isRawC t = true) qM)
    (hfree : AllQueriesSatisfy fC (freeC (F.sb seed)))
    (hInv : TcrInv F btw x.2 c) (hcv : cv ≠ F.IV) (hpb : ¬ PubBad F.IV cv c) :
    Pr{let b ← (simulateQ (routeRO F.IV (F.sb seed) cv) (tcrP₂ A seed x)).run' c}[b = true] ≤
      (qM + 1 : ℕ) * δ + q₂ * (2 * (Fintype.card St : ℝ≥0∞)⁻¹) := by
  classical
  have hG := hInv.good
  unfold tcrP₂
  rw [simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind]
  refine (prEvent_bind_le_prEvent_add _ _
    (fun z => ¬ TcrGood F btw x.2.1 z.2 ∨ PubBad F.IV cv z.2) _ (ε := δ) fun z hz => ?_).trans ?_
  · simp only [not_or, not_not] at hz
    obtain ⟨⟨j, m⟩, c₂⟩ := z
    rw [← StateT.run'_eq]
    dsimp only
    cases hj : x.2.1[j]? with
    | none => simp
    | some tm =>
      obtain ⟨t, mj⟩ := tm
      exact prEvent_tcr_final_le hsingle btw hbtwT hinj δ hδ seed cv hcv hz.1 t m mj
        (List.mem_of_getElem? hj)
  · have hb := prEvent_routeRO_bad_fine F.IV (F.sb seed) cv hcv
      (fun c => ¬ TcrGood F btw x.2.1 c) δ
      (fun c q u hc _ => not_not.mpr ((not_not.mp hc).cacheQuery_pub q u))
      (fun c B hc hB => prEvent_not_tcrGood_cacheQuery_row_le hInv.1 δ hδ (not_not.mp hc) B hB)
      fC qM hqM hfree c (not_not.mpr hG)
    have hp := prEvent_routeRO_pubBad_le F.IV (F.sb seed) cv (A.forge x.1 seed) q₂
      (hq₂ x.1 seed) c hpb
    rw [hfC] at hp ⊢
    calc Pr{let z ← (simulateQ (routeRO F.IV (F.sb seed) cv)
            (simulateQ (expandImpl F.IV) fC)).run c}[
            ¬ TcrGood F btw x.2.1 z.2 ∨ PubBad F.IV cv z.2] + δ
        ≤ (Pr{let z ← (simulateQ (routeRO F.IV (F.sb seed) cv)
              (simulateQ (expandImpl F.IV) fC)).run c}[
              ¬ TcrGood F btw x.2.1 z.2 ∧ ¬ PubBad F.IV cv z.2] +
            Pr{let z ← (simulateQ (routeRO F.IV (F.sb seed) cv)
              (simulateQ (expandImpl F.IV) fC)).run c}[PubBad F.IV cv z.2]) + δ := by
          gcongr
          refine (prEvent_mono _ _ _ fun z h => ?_).trans (prEvent_or_le _ _ _)
          by_cases hpz : PubBad F.IV cv z.2
          · exact .inr hpz
          · exact .inl ⟨h.resolve_right hpz, hpz⟩
      _ ≤ (qM * δ + q₂ * (2 * (Fintype.card St : ℝ≥0∞)⁻¹)) + δ := by gcongr
      _ = _ := by push_cast; ring

/-- **The ideal SM-TCR game, fine form.** -/
theorem tcr_ideal_le_fine [DecidableEq Tweak] [DecidableEq M] [DecidableEq Y]
    (hsingle : ∀ t m, (F.tch t m).2 = [])
    (btw : Blk → Tweak) (hbtwT : ∀ t m, btw (F.tch t m).1 = t)
    (hbtwC : ∀ i t m, btw (F.cch i t m).1 = t)
    (hinj : ∀ t m m', (F.tch t m).1 = (F.tch t m').1 → m = m')
    (δ : ℝ≥0∞) (hδ : ∀ y, Pr{let u ← $ᵗ St}[F.out u = y] ≤ δ)
    (A : TcrAdv F) (q₁ qch qc L q₂ : ℕ) (hq₁ : A.ChooseBound q₁) (hch : A.ChalBound qch)
    (hc : A.CollBound qc) (hL : A.CollLen L) (hq₂ : A.ForgeBound q₂)
    (fC : A.State → PkSeed → OracleComp (pcS St Blk) (ℕ × M))
    (hfC : ∀ st pk, A.forge st pk = simulateQ (expandImpl F.IV) (fC st pk))
    (bad : PkSeed → Prop) (β : ℝ≥0∞) (hβ : Pr{let s ← F.seedGen}[bad s] ≤ β) (qM : ℕ)
    (hqM : ∀ st pk, ¬ bad pk → IsQueryBoundP (fC st pk) (fun t => isRawC t = true) qM)
    (hfree : ∀ st pk, ¬ bad pk → AllQueriesSatisfy (fC st pk) (freeC (F.sb pk))) :
    𝒟[idealGame F.IV F.sb F.seedGen (tcrProg₁ A) (tcrP₂ A)] {true} ≤
      ((qM + 1 : ℕ) * δ + q₂ * (2 * (Fintype.card St : ℝ≥0∞)⁻¹)) + (q₂ + 1 : ℕ) * δ * β +
        (1 + 2 * ((q₁ + (qch + qc)) * max 1 L) : ℕ) * (Fintype.card St : ℝ≥0∞)⁻¹ := by
  classical
  refine idealGame_le_of_inv_fine F.IV F.sb F.seedGen (tcrProg₁ A) (tcrP₂ A)
    (fun x c => TcrInv F btw x.2 c) _ _ β bad hβ (tcrInv_phase1 btw hbtwT hbtwC A)
    (fun x c seed cv hInv hcv hpb => ?_) q₁ (qch + qc) L (tcrProg₁_pubBound A hq₁)
    (tcrProg₁_chainBound A hch hc)
    (tcrProg₁_chainLen A (fun t m => by rw [hsingle]; exact Nat.zero_le _) hL)
  by_cases hs : bad seed
  · rw [if_pos hs]
    exact (prEvent_tcr_phase2_le hsingle btw hbtwT hinj δ hδ A q₂ hq₂ x c seed cv hInv hcv).trans
      le_add_self
  · rw [if_neg hs, add_zero]
    exact prEvent_tcr_phase2_le_fine hsingle btw hbtwT hinj δ hδ A q₂ hq₂ x c seed cv
      (fC x.1 seed) (hfC x.1 seed) qM (hqM x.1 seed hs) (hfree x.1 seed hs) hInv hcv hpb

/-- **SM-TCR, fine accounting** (`tcr_bound` with `tcr_ideal_le_fine`). -/
theorem tcr_bound_fine [Finite Blk] [SampleableType (CF St Blk)]
    [DecidableEq Tweak] [DecidableEq M] [DecidableEq Y]
    (hsb : Function.Injective F.sb)
    (γ : ℝ≥0∞) (hγ : ∀ s, Pr{let s' ← F.seedGen}[s' = s] ≤ γ)
    (hsingle : ∀ t m, (F.tch t m).2 = [])
    (btw : Blk → Tweak) (hbtwT : ∀ t m, btw (F.tch t m).1 = t)
    (hbtwC : ∀ i t m, btw (F.cch i t m).1 = t)
    (hinj : ∀ t m m', (F.tch t m).1 = (F.tch t m').1 → m = m')
    (δ : ℝ≥0∞) (hδ : ∀ y, Pr{let u ← $ᵗ St}[F.out u = y] ≤ δ)
    (A : TcrAdv F) (q₁ qch qc L q₂ : ℕ)
    (hq₁ : A.ChooseBound q₁) (hch : A.ChalBound qch) (hc : A.CollBound qc)
    (hL : A.CollLen L) (hq₂ : A.ForgeBound q₂)
    (fC : A.State → PkSeed → OracleComp (pcS St Blk) (ℕ × M))
    (hfC : ∀ st pk, A.forge st pk = simulateQ (expandImpl F.IV) (fC st pk))
    (bad : PkSeed → Prop) (β : ℝ≥0∞) (hβ : Pr{let s ← F.seedGen}[bad s] ≤ β) (qM : ℕ)
    (hqM : ∀ st pk, ¬ bad pk → IsQueryBoundP (fC st pk) (fun t => isRawC t = true) qM)
    (hfree : ∀ st pk, ¬ bad pk → AllQueriesSatisfy (fC st pk) (freeC (F.sb pk))) :
    tcrAdvantage F A ≤ (qM + 1 : ℕ) * δ + (q₂ + 1 : ℕ) * δ * β + q₁ * γ +
      (2 * q₁ + (qch + qc) * (1 + 2 * L) + 2 + 2 * ((q₁ + (qch + qc)) * max 1 L) + 2 * q₂ : ℕ) *
        (Fintype.card St : ℝ≥0∞)⁻¹ := by
  rw [tcrAdvantage_eq_realGame]
  have h1 := hiddenPrefix F.IV F.sb hsb F.seedGen γ hγ (tcrProg₁ A) (tcrP₂ A) q₁ (qch + qc) L
    (tcrProg₁_pubBound A hq₁) (tcrProg₁_chainBound A hch hc)
    (tcrProg₁_chainLen A (fun t m => by rw [hsingle]; exact Nat.zero_le _) hL)
  have h2 := tcr_ideal_le_fine hsingle btw hbtwT hbtwC hinj δ hδ A q₁ qch qc L q₂ hq₁ hch hc hL
    hq₂ fC hfC bad β hβ qM hqM hfree
  refine h1.trans ((add_le_add (add_le_add h2 le_rfl) le_rfl).trans (le_of_eq ?_))
  push_cast
  ring

end Tcr

end Ideal

#print axioms Ideal.prEvent_chainRO_pubHit_le
#print axioms Ideal.idealGame_le_of_inv_fine
#print axioms Ideal.tcr_ideal_le_fine
#print axioms Ideal.tcr_bound_fine
