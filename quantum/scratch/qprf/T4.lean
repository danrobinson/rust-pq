import Integration.SlhDsaBridgeInd

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal PQ.Interactive PQ.QROM Quantum
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Reduction.QMsg
open Reduction.QInd

variable {W : Type} [Fintype W] {α : Type}

section Restrict
variable {D D' R : Type} [Inhabited R] (r : D → Option D')

lemma liftQ_restrict_unif (n : ℕ) :
    (liftQ (Restrict.restrictImpl (V := R) r (.inl n)) :
        QOC W (PRFScheme.PRFOracleSpec D' R) _) =
      liftM ((instrSpec W + PRFScheme.PRFOracleSpec D' R).query (Sum.inr (Sum.inl n))) := by
  simp [Restrict.restrictImpl, liftQ]
  rfl

lemma liftQ_restrict_some (d : D) (d' : D') (h : r d = some d') :
    (liftQ (Restrict.restrictImpl (V := R) r (.inr d)) :
        QOC W (PRFScheme.PRFOracleSpec D' R) _) =
      liftM ((instrSpec W + PRFScheme.PRFOracleSpec D' R).query (Sum.inr (Sum.inr d'))) := by
  simp [Restrict.restrictImpl, h, liftQ, PRFScheme.functionQuery]

lemma liftQ_restrict_none (d : D) (h : r d = none) :
    (liftQ (Restrict.restrictImpl (V := R) r (.inr d)) :
        QOC W (PRFScheme.PRFOracleSpec D' R) _) = pure default := by
  simp [Restrict.restrictImpl, h]

theorem ansRun_restrict (f : D → R) (f' : D' → R)
    (hf : ∀ d, f d = match r d with | some d' => f' d' | none => default)
    (Q : QOC W (PRFScheme.PRFOracleSpec D R) α) :
    ansRun f Q = ansRun f' (wrap0 (Restrict.restrictImpl r) Q) := by
  induction Q using OracleComp.inductionOn with
  | pure a => simp [ansRun_pure]
  | query_bind t k ih =>
    rcases t with j | n | d
    · rw [wrap0_instr_bind, ansRun_instr, ansRun_instr]
      simp only [ih]
    · rw [wrap0_query_bind, liftQ_restrict_unif, ansRun_unif, ansRun_unif]
      simp only [ih]
    · rw [wrap0_query_bind, ansRun_oracle]
      rcases hr : r d with _ | d'
      · rw [liftQ_restrict_none r d hr, pure_bind, ih, hf d, hr]
      · rw [liftQ_restrict_some r d d' hr, ansRun_oracle, ih, hf d, hr]

theorem qPrfRealPr_restrict {K : Type} (P : PRFScheme K D R) (P' : PRFScheme K D' R)
    (hk : P.keygen = P'.keygen)
    (he : ∀ k d, P.eval k d = match r d with | some d' => P'.eval k d' | none => default)
    (Q : QOC W (PRFScheme.PRFOracleSpec D R) Bool) (ρ : Matrix W W ℂ) :
    qPrfRealPr P Q ρ = qPrfRealPr P' (wrap0 (Restrict.restrictImpl r) Q) ρ := by
  unfold qPrfRealPr qPrfRealExperiment
  rw [hk]
  congr 2
  funext k
  exact ansRun_restrict r (P.eval k) (P'.eval k) (he k) Q

/-- Every function query of a PRF distinguisher is in the domain of `r`. -/
def InDom : (instrSpec W + PRFScheme.PRFOracleSpec D R).Domain → Prop
  | .inr (.inr d) => (r d).isSome
  | _ => True

variable [DecidableEq D] [DecidableEq D'] [SampleableType R]

theorem idealRun_restrict
    (hinj : ∀ d₁ d₂ d', r d₁ = some d' → r d₂ = some d' → d₁ = d₂)
    (Q : QOC W (PRFScheme.PRFOracleSpec D R) α) (hQ : AllQueries (InDom (W := W) (R := R) r)
      (fun _ ↦ True) Q) :
    ∀ (c : (D →ₒ R).QueryCache) (c' : (D' →ₒ R).QueryCache),
      (∀ d d', r d = some d' → c d = c' d') →
      idealRun Q c = idealRun (wrap0 (Restrict.restrictImpl r) Q) c' := by
  induction Q using OracleComp.inductionOn with
  | pure a => intro c c' _; simp [idealRun_pure]
  | query_bind t k ih =>
    intro c c' hc
    have hQ' : InDom (W := W) (R := R) r t ∧ ∀ u, AllQueries (InDom (W := W) (R := R) r)
        (fun _ ↦ True) (k u) := hQ
    rcases t with j | n | d
    · rw [wrap0_instr_bind, idealRun_instr, idealRun_instr]
      simp only [fun i ↦ ih i (hQ'.2 i) c c' hc]
    · rw [wrap0_query_bind, liftQ_restrict_unif, idealRun_unif, idealRun_unif]
      simp only [fun i ↦ ih i (hQ'.2 i) c c' hc]
    · obtain ⟨d', hd'⟩ := Option.isSome_iff_exists.1 hQ'.1
      rw [wrap0_query_bind, liftQ_restrict_some r d d' hd']
      rcases hcd : c d with _ | v
      · have hcd' : c' d' = none := (hc d d' hd').symm.trans hcd
        rw [idealRun_oracle_none _ _ _ hcd, idealRun_oracle_none _ _ _ hcd']
        refine bind_congr fun v ↦ ih v (hQ'.2 v) _ _ ?_
        intro d₁ d₁' h₁
        by_cases e : d₁ = d
        · subst e
          rw [hd'] at h₁
          cases h₁
          simp
        · have e' : d₁' ≠ d' := fun e' ↦ e (hinj _ _ _ h₁ (e' ▸ hd'))
          rw [QueryCache.cacheQuery_of_ne _ _ e, QueryCache.cacheQuery_of_ne _ _ e']
          exact hc d₁ d₁' h₁
      · have hcd' : c' d' = some v := (hc d d' hd').symm.trans hcd
        rw [idealRun_oracle_some _ _ _ v hcd, idealRun_oracle_some _ _ _ v hcd']
        exact ih v (hQ'.2 v) c c' hc

theorem qPrfIdealPr_restrict
    (hinj : ∀ d₁ d₂ d', r d₁ = some d' → r d₂ = some d' → d₁ = d₂)
    (Q : QOC W (PRFScheme.PRFOracleSpec D R) Bool)
    (hQ : AllQueries (InDom (W := W) (R := R) r) (fun _ ↦ True) Q) (ρ : Matrix W W ℂ) :
    qPrfIdealPr Q ρ = qPrfIdealPr (wrap0 (Restrict.restrictImpl r) Q) ρ := by
  unfold qPrfIdealPr qPrfIdealExperiment
  have h := idealRun_restrict r hinj Q hQ ∅ ∅ (fun _ _ _ ↦ rfl)
  unfold idealRun at h
  rw [h]

end Restrict
end Reduction.QMsg
