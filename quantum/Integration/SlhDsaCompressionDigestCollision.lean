import Integration.SlhDsaCompressionHmacTrunc

namespace Reduction.Compression.DigestCollision
open OracleComp OracleSpec PQ.Interactive Quantum ENNReal
open scoped ComplexOrder
variable {W D T R α : Type} [Fintype W] [DecidableEq D] [DecidableEq T]
    [Inhabited R] [SampleableType R] [Fintype R] [DecidableEq R]

private abbrev PS (D R : Type) := PRFScheme.PRFOracleSpec D R

/-- A replay of the ideal message experiment that returns the first pair of distinct
queries mapped to the same digest, or none when the machine finishes. -/
noncomputable def watch (h : D → T) (Q : QOC W (PS D R) α) :
    (T → Option D) → (D →ₒ R).QueryCache → Closed W (Option (D × D)) :=
  OracleComp.construct (C := fun _ => (T → Option D) → (D →ₒ R).QueryCache → Closed W (Option (D × D)))
    (fun _ _ _ => pure none)
    (fun t _ ih seen c => match t, ih with
      | .inl j, ih => liftM ((instrSpec W + unifSpec).query (.inl j)) >>= fun x => ih x seen c
      | .inr (.inl n), ih => liftM ((instrSpec W + unifSpec).query (.inr n)) >>= fun x => ih x seen c
      | .inr (.inr d), ih =>
        if (seen (h d)).any (· != d) then pure ((seen (h d)).map (·,d)) else
        match c d with
        | some v => ih v seen c
        | none => liftU ($ᵗ R) >>= fun v => ih v (Function.update seen (h d) (some d)) (c.cacheQuery d v)) Q

omit [Inhabited R] [Fintype R] [DecidableEq R] in
private theorem watch_query (h : D → T) (d : D) (k : R → QOC W (PS D R) α) (seen) (c) :
    watch h (liftM ((instrSpec W + PS D R).query (.inr (.inr d))) >>= k) seen c =
      if (seen (h d)).any (· != d) then pure ((seen (h d)).map (·,d)) else
      match c d with
      | some v => watch h (k v) seen c
      | none => liftU ($ᵗ R) >>= fun v => watch h (k v) (Function.update seen (h d) (some d)) (c.cacheQuery d v) := rfl

private def coherent (h : D → T) (seen : T → Option D) (c : (D →ₒ R).QueryCache)
    (t : (T →ₒ R).QueryCache) := ∀ d, (seen (h d)).any (· != d) = false → c d = t (h d)

omit [Inhabited R] [SampleableType R] [Fintype R] [DecidableEq R] in
private theorem coherent_set {h : D → T} {seen : T → Option D} {c : (D →ₒ R).QueryCache}
    {t : (T →ₒ R).QueryCache} (hc : coherent h seen c t) (d : D) (v : R) :
    coherent h (Function.update seen (h d) (some d)) (c.cacheQuery d v) (t.cacheQuery (h d) v) := by
  intro x hx
  by_cases e : h x = h d
  · rw [e, Function.update_self] at hx
    have : x = d := by
      by_contra hn
      simp [Ne.symm hn] at hx
    subst x
    rw [QueryCache.cacheQuery_self, QueryCache.cacheQuery_self]
  · rw [Function.update_of_ne e] at hx
    have ne : x ≠ d := fun p => e (congrArg h p)
    rw [QueryCache.cacheQuery_of_ne _ _ ne, QueryCache.cacheQuery_of_ne _ _ e]
    exact hc x hx

def found (h : D → T) (v : Option (D × D)) : Bool :=
  v.any (fun p => decide (p.1 ≠ p.2 ∧ h p.1 = h p.2))

private def valid (h : D → T) (seen : T → Option D) := ∀ t d, seen t = some d → h d = t

omit [DecidableEq D] in
private theorem valid_set {h : D → T} {seen : T → Option D} (hs : valid h seen) (d : D) :
    valid h (Function.update seen (h d) (some d)) := by
  intro t x e
  by_cases he : t = h d
  · subst t
    rw [Function.update_self] at e
    exact congrArg h (Option.some.inj e).symm
  · rw [Function.update_of_ne he] at e
    exact hs t x e

noncomputable def hashed (h : D → T) (Q : QOC W (PS D R) α) : QOC W (PS T R) α :=
  wrap0 (Restrict.restrictImpl (V := R) (fun d => some (h d))) Q

set_option maxRecDepth 4096 in
private theorem compare (h : D → T) (p : α → Prop) [DecidablePred p] (Q : QOC W (PS D R) α) :
    ∀ seen c t (M : Matrix W W ℂ), M.PosSemidef → valid h seen → coherent h seen c t →
    qWeight p (idealRun (hashed h Q) t) M ≤ qWeight p (idealRun Q c) M +
      qWeight (fun v => found h v = true) (watch h Q seen c) M := by
  induction Q using OracleComp.inductionOn with
  | pure a => intro seen c t M _ _ _; simp [hashed, watch, found, idealRun_pure]
  | query_bind a k ih =>
    intro seen c t M hm hv hc
    rcases a with j | n | d
    · simp only [hashed, wrap0_instr_bind, idealRun_instr]
      change _ ≤ _ + qWeight _ (liftM ((instrSpec W + unifSpec).query (.inl j)) >>= _) M
      simp only [qWeight_instr_bind, ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun x _ => ih x seen c t _ (posSemidef_branch j x hm) hv hc
    · simp only [hashed, wrap0_query_bind, QMsg.liftQ_restrict_unif, idealRun_unif]
      change _ ≤ _ + qWeight _ (liftM ((instrSpec W + unifSpec).query (.inr n)) >>= _) M
      simp only [qWeight_unif_bind, ← mul_add, ← Finset.sum_add_distrib]
      exact mul_le_mul' le_rfl (Finset.sum_le_sum fun x _ => ih x seen c t M hm hv hc)
    · unfold hashed
      rw [wrap0_query_bind, QMsg.liftQ_restrict_some _ d (h d) rfl]
      rw [watch_query]
      by_cases bad : (seen (h d)).any (· != d) = true
      · rw [ite_eq_left bad]
        cases e : seen (h d) with
        | none => simp [e] at bad
        | some d' =>
          have ne : d' ≠ d := by simpa only [e, Option.any_some, bne_iff_ne] using bad
          have win : found h (some (d',d)) = true := by simp [found, ne, hv _ _ e]
          simp only [Option.map_some, qWeight_pure, win, ite_true]
          exact (qWeight_le_trace _ _ hm).trans (le_add_self)
      · have good := Bool.eq_false_iff.mpr bad
        have eq := hc d good
        rw [ite_eq_right bad]
        cases he : c d with
        | some v =>
          rw [idealRun_oracle_some _ _ _ _ (eq.symm.trans he), idealRun_oracle_some _ _ _ _ he]
          exact ih v seen c t M hm hv hc
        | none =>
          rw [idealRun_oracle_none _ _ _ (eq.symm.trans he), idealRun_oracle_none _ _ _ he]
          simp only [qWeight_liftU_uniform_bind, ← mul_add, ← Finset.sum_add_distrib]
          exact mul_le_mul' le_rfl (Finset.sum_le_sum fun v _ => ih v _ _ _ M hm (valid_set hv d) (coherent_set hc d v))

/-- A uniformly random output function indexed by a digest can outperform the
ideal message oracle only to the extent that the monitored message experiment
produces distinct queried inputs with the same digest. -/
theorem eager_le_ideal_add_collision [Fintype T] [Nonempty T] (h : D → T)
    (Q : QOC W (PS D R) Bool) (M : Matrix W W ℂ) (hm : M.PosSemidef) :
    (Fintype.card (T → R) : ℝ≥0∞)⁻¹ * ∑ f : T → R,
      qWeight (· = true) (ansRun (fun d => f (h d)) Q) M ≤
      qPrfIdealPr Q M + qWeight (fun v => found h v = true) (watch h Q (fun _ => none) ∅) M := by
  have e := lazy_eq_avg (Dm := T) id Function.injective_id (· = true) (hashed h Q) M
  have answer (f : T → R) : ansRun (fun d => f (id d)) (hashed h Q) = ansRun (fun d => f (h d)) Q :=
    (QMsg.ansRun_restrict (fun d => some (h d)) _ f (fun _ => rfl) Q).symm
  simp only [answer] at e
  rw [← e]
  exact compare h _ Q (fun _ => none) ∅ ∅ M hm (by intro t d e; cases e) (fun _ _ => rfl)

end Reduction.Compression.DigestCollision

#print axioms Reduction.Compression.DigestCollision.eager_le_ideal_add_collision
