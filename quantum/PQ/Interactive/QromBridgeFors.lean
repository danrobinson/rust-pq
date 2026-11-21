import PQ.Interactive.QromBridgeTcr
import PQ.QROM.ForsPullback

/-!
# The FORS-leaf bridges (TCR and DSPR with source final validity), game side: generic part

Generic (no SLH-DSA) facts about VCVio's source-final-validity SM-DT-TCR game with a quantum
second phase, at the EMPTY collection (`ι = Empty`, the stand-alone games of the FORS leaves).

* `FvExt`, `fv_run_ext`: along a run of the selection phase the challenge history only grows,
  and if the final state is valid, then the initial one was valid and the new entries have
  pairwise distinct tweaks, fresh for the initial history.
* `fv_run_prob_congr`: the probability that the selection phase ends in a VALID state `z` whose
  challenge history contains `(t₀, m₀)` is unchanged when the attacked hash is changed at the
  points `(t₀, m)`, `m ≠ m₀` (a second challenge at the tweak `t₀` poisons the state).
* **`tcrFv_row_avg_le`**: the row-average of the per-seed winning weight of the game is at most
  `(2q+1)²/|Y|` if the second phase is described by a `q`-query hybrid model over the row.
-/

open OracleComp OracleSpec ENNReal Quantum MeasureTheory

set_option linter.unusedSectionVars false

namespace PQ.Interactive

open TweakableHash

section fvrun

variable {PkSeed Tw M Y : Type} [DecidableEq Tw]

/-- `P` with the evaluation of the attacked hash replaced. -/
abbrev fvWithEval (P : SM_DT_TCR_SourceFinalValidity.Problem Empty PkSeed Tw M Y)
    (th : PkSeed → Tw → M → Y) : SM_DT_TCR_SourceFinalValidity.Problem Empty PkSeed Tw M Y where
  th := ⟨P.th.seedGen, th⟩
  thColl := P.thColl
  numTargets := P.numTargets

/-- Interface of the selection phase. -/
abbrev FvSpec (P : SM_DT_TCR_SourceFinalValidity.Problem Empty PkSeed Tw M Y) :=
  unifSpec + (SM_DT_TCR_SourceFinalValidity.challengeSpec Tw M Y +
    SourceFinalValidity.collectionSpec P.thColl)

/-- `τ` extends `σ`: the challenge history grows; if `τ` is valid, so is `σ`, and the new
entries have distinct tweaks, fresh for the history of `σ`. -/
def FvExt (σ τ : SM_DT_TCR_SourceFinalValidity.State Tw M) : Prop :=
  ∃ s, τ.challenges = σ.challenges ++ s ∧
    (τ.valid = true → σ.valid = true ∧ (s.map Prod.fst).Nodup ∧
      ∀ e ∈ s, e.1 ∉ σ.challenges.map Prod.fst)

theorem fvExt_refl (σ : SM_DT_TCR_SourceFinalValidity.State Tw M) : FvExt σ σ :=
  ⟨[], by simp, fun h ↦ ⟨h, by simp, by simp⟩⟩

theorem fvExt_trans {σ τ υ : SM_DT_TCR_SourceFinalValidity.State Tw M} (h₁ : FvExt σ τ)
    (h₂ : FvExt τ υ) : FvExt σ υ := by
  obtain ⟨s, hs, hv⟩ := h₁
  obtain ⟨s', hs', hv'⟩ := h₂
  refine ⟨s ++ s', by rw [hs', hs, List.append_assoc], fun hυ ↦ ?_⟩
  obtain ⟨hτ, hn', hf'⟩ := hv' hυ
  obtain ⟨hσ, hn, hf⟩ := hv hτ
  refine ⟨hσ, ?_, ?_⟩
  · rw [List.map_append, List.nodup_append]
    refine ⟨hn, hn', ?_⟩
    intro a ha b hb hab
    subst hab
    obtain ⟨e', he', rfl⟩ := List.mem_map.1 hb
    refine hf' e' he' ?_
    rw [hs, List.map_append]
    exact List.mem_append_right _ ha
  · intro e he
    rcases List.mem_append.1 he with he | he
    · exact hf e he
    · intro hm
      refine hf' e he ?_
      rw [hs, List.map_append]
      exact List.mem_append_left _ hm

/-- One oracle step of the game extends the state. -/
theorem fv_step_ext (P : SM_DT_TCR_SourceFinalValidity.Problem Empty PkSeed Tw M Y) (pk : PkSeed)
    (q : (FvSpec P).Domain) (σ : SM_DT_TCR_SourceFinalValidity.State Tw M) :
    ∀ p ∈ support ((SM_DT_TCR_SourceFinalValidity.oracles P pk q).run σ), FvExt σ p.2 := by
  rcases q with n | ⟨t, m⟩ | q
  · intro p hp
    have h : (SM_DT_TCR_SourceFinalValidity.oracles P pk (.inl n)).run σ =
        (fun u => (u, σ)) <$> (liftM (unifSpec.query n) : ProbComp _) := by
      simp [SM_DT_TCR_SourceFinalValidity.oracles]
    rw [h] at hp
    simp only [support_map, Set.mem_image] at hp
    obtain ⟨u, -, rfl⟩ := hp
    exact fvExt_refl _
  · intro p hp
    have h : (SM_DT_TCR_SourceFinalValidity.oracles P pk (.inr (.inl (t, m)))).run σ =
        pure (P.th.eval pk t m, σ.recordTarget P.numTargets Prod.fst (t, m)) :=
      SM_DT_TCR_SourceFinalValidity.challengeOracle_run
    rw [h] at hp
    simp only [support_pure, Set.mem_singleton_iff] at hp
    subst hp
    refine ⟨[(t, m)], rfl, fun hv ↦ ?_⟩
    simp only [SourceFinalValidity.State.recordTarget, Bool.and_eq_true, decide_eq_true_eq] at hv
    obtain ⟨⟨hv, -⟩, hfr, -⟩ := hv
    refine ⟨hv, by simp, ?_⟩
    intro e he
    simp only [List.mem_singleton] at he
    subst he
    intro hm
    obtain ⟨e', he', h'⟩ := List.mem_map.1 hm
    exact hfr ⟨e', he', h'⟩
  · exact q.1.elim

/-- A run of the selection phase extends the state. -/
theorem fv_run_ext (P : SM_DT_TCR_SourceFinalValidity.Problem Empty PkSeed Tw M Y) (pk : PkSeed)
    {S : Type} (oa : OracleComp (FvSpec P) S) (σ : SM_DT_TCR_SourceFinalValidity.State Tw M) :
    ∀ z ∈ support ((simulateQ (SM_DT_TCR_SourceFinalValidity.oracles P pk) oa).run σ),
      FvExt σ z.2 := by
  induction oa using OracleComp.inductionOn generalizing σ with
  | pure x =>
    intro z hz
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact fvExt_refl _
  | query_bind q k ih =>
    intro z hz
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind] at hz
    obtain ⟨p, hp, hz⟩ := (mem_support_bind_iff ..).mp hz
    exact fvExt_trans (fv_step_ext P pk q σ p hp) (ih p.1 p.2 z hz)

/-- Valid reachable challenge histories have distinct tweaks. -/
theorem fv_run_nodup (P : SM_DT_TCR_SourceFinalValidity.Problem Empty PkSeed Tw M Y) (pk : PkSeed)
    {S : Type} (oa : OracleComp (FvSpec P) S) :
    ∀ z ∈ support ((simulateQ (SM_DT_TCR_SourceFinalValidity.oracles P pk) oa).run .initial),
      z.2.valid = true → (z.2.challenges.map Prod.fst).Nodup := by
  intro z hz hv
  obtain ⟨s, hs, hsv⟩ := fv_run_ext P pk oa .initial z hz
  obtain ⟨-, hn, -⟩ := hsv hv
  rw [hs]
  simpa [SourceFinalValidity.State.initial] using hn

/-- **Row modification at a non-target point of a target tweak.** -/
theorem fv_run_prob_congr (P : SM_DT_TCR_SourceFinalValidity.Problem Empty PkSeed Tw M Y)
    (pk : PkSeed) (th₁ th₂ : PkSeed → Tw → M → Y) (t₀ : Tw) (m₀ : M)
    (hth : ∀ t m, (t = t₀ → m = m₀) → th₁ pk t m = th₂ pk t m) {S : Type}
    (oa : OracleComp (FvSpec P) S) (σ : SM_DT_TCR_SourceFinalValidity.State Tw M)
    (z : S × SM_DT_TCR_SourceFinalValidity.State Tw M) (hz : (t₀, m₀) ∈ z.2.challenges)
    (hzv : z.2.valid = true) :
    PQ.Interactive.prob ((simulateQ (SM_DT_TCR_SourceFinalValidity.oracles
        (fvWithEval P th₁) pk) oa).run σ) (· = z) =
      PQ.Interactive.prob ((simulateQ (SM_DT_TCR_SourceFinalValidity.oracles
        (fvWithEval P th₂) pk) oa).run σ) (· = z) := by
  induction oa using OracleComp.inductionOn generalizing σ with
  | pure x => simp
  | query_bind q k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rcases q with n | ⟨t, m⟩ | q
    · have h : ∀ th : PkSeed → Tw → M → Y,
          (SM_DT_TCR_SourceFinalValidity.oracles (fvWithEval P th) pk (.inl n)).run σ =
            (fun u => (u, σ)) <$> (liftM (unifSpec.query n) : ProbComp _) := by
        intro th
        simp [SM_DT_TCR_SourceFinalValidity.oracles]
      rw [h th₁, h th₂]
      exact PQ.Interactive.prob_bind_congr_tcr _ _ _ _ fun p ↦ ih p.1 p.2
    · have h : ∀ th : PkSeed → Tw → M → Y,
          (SM_DT_TCR_SourceFinalValidity.oracles (fvWithEval P th) pk (.inr (.inl (t, m)))).run σ =
            pure (th pk t m, σ.recordTarget P.numTargets Prod.fst (t, m)) := fun th ↦
        SM_DT_TCR_SourceFinalValidity.challengeOracle_run
      rw [h th₁, h th₂, pure_bind, pure_bind]
      by_cases he : t = t₀ → m = m₀
      · rw [hth t m he]
        exact ih _ _
      · have ⟨ht, hm⟩ : t = t₀ ∧ m ≠ m₀ := ⟨by tauto, by tauto⟩
        subst ht
        have hzero : ∀ (th : PkSeed → Tw → M → Y) (u : Y),
            PQ.Interactive.prob ((simulateQ (SM_DT_TCR_SourceFinalValidity.oracles
              (fvWithEval P th) pk) (k u)).run
                (σ.recordTarget P.numTargets Prod.fst (t, m))) (· = z) = 0 := by
          intro th u
          refine prob_eq_zero_of_forall_ne _ _ fun w hw hwz ↦ ?_
          subst hwz
          obtain ⟨s, hs, hsv⟩ := fv_run_ext (fvWithEval P th) pk (k u) _ w hw
          obtain ⟨hv, -, hsf⟩ := hsv hzv
          simp only [SourceFinalValidity.State.recordTarget, Bool.and_eq_true,
            decide_eq_true_eq] at hv
          obtain ⟨-, hfr, -⟩ := hv
          rw [hs] at hz
          simp only [SourceFinalValidity.State.recordTarget, List.append_assoc, List.mem_append,
            List.mem_singleton] at hz
          rcases hz with hz | hz | hz
          · exact hfr ⟨_, hz, rfl⟩
          · exact hm (Prod.ext_iff.1 hz).2.symm
          · exact hsf _ hz (by simp [SourceFinalValidity.State.recordTarget])
        rw [hzero th₁, hzero th₂]
    · exact q.1.elim

end fvrun

/-! ## The generic row bound, TCR with source final validity -/

section rowtcr

variable {PkSeed Tw M Y : Type} [DecidableEq Tw]

/-- The empty event has weight zero. -/
lemma qWeight_false_fors {W : Type} [Fintype W] {α : Type} (X : Closed W α) (ρ : Matrix W W ℂ) :
    qWeight (fun _ ↦ False) X ρ = 0 := by
  induction X using OracleComp.inductionOn generalizing ρ with
  | pure a => simp [qWeight_pure]
  | query_bind t k ih =>
    rcases t with j | n
    · rw [qWeight_instr_bind]
      simp [ih]
    · rw [qWeight_unif_bind]
      simp [ih]

/-- The winning event of the TCR-FV game for the final state `(L, v)` and row `R`. -/
def fvTcrWin (L : List (Tw × M)) (v : Bool) (R : Tw × M → Y) (jm : ℕ × M) : Prop :=
  v = true ∧ ∃ tm, L[jm.1]? = some tm ∧ jm.2 ≠ tm.2 ∧ R (tm.1, jm.2) = R tm

variable [Fintype Tw] [Fintype M] [DecidableEq M] [Fintype Y] [DecidableEq Y]
  [Nonempty Tw] [Nonempty Y] [AddCommGroup Y]

/-- **Generic row bound for SM-TCR with source final validity and a quantum second phase.**
The attacked hash at the seed `pk` is a uniformly random row `R : Tw × M → Y` (`hth`); the
collection is empty; the selection program `choose` is fixed; the second-phase machine
`forge R s` is described, for every state `s`, by a `q`-query hybrid model over the row
(`hModel`).  Then the row-average of the winning weight at `pk` is at most `(2q+1)²/|Y|`. -/
theorem tcrFv_row_avg_le (P : SM_DT_TCR_SourceFinalValidity.Problem Empty PkSeed Tw M Y)
    (pk : PkSeed)
    (thR : (Tw × M → Y) → PkSeed → Tw → M → Y) (hth : ∀ R t m, thR R pk t m = R (t, m))
    {S : Type} (choose : OracleComp (FvSpec P) S)
    {W : Type} [Fintype W] (forge : (Tw × M → Y) → S → Closed W (ℕ × M))
    (ρ : Matrix W W ℂ) (q : ℕ)
    (hModel : ∀ s, ∃ Mo : PQ.QROM.HybridModel (Tw × M) Y (ℕ × M) q,
      ∀ R (Ev : ℕ × M → Prop) [DecidablePred Ev], Mo.prob R Ev = qWeight Ev (forge R s) ρ) :
    ∑ R : Tw × M → Y, (Fintype.card (Tw × M → Y) : ℝ≥0∞)⁻¹ *
      qWeight (· = true)
        (liftU ((simulateQ (SM_DT_TCR_SourceFinalValidity.oracles (fvWithEval P (thR R)) pk)
            choose).run .initial) >>= fun r ↦
          forge R r.1 >>= fun jm ↦
            liftU (match r.2.challenges[jm.1]? with
              | none => pure false
              | some tm => pure (r.2.valid && decide (jm.2 ≠ tm.2 ∧
                  thR R pk tm.1 jm.2 = thR R pk tm.1 tm.2)))) ρ ≤
      (2 * (q : ℝ≥0∞) + 1) ^ 2 / (Fintype.card Y : ℝ≥0∞) := by
  classical
  set u : ℝ≥0∞ := (Fintype.card (Tw × M → Y) : ℝ≥0∞)⁻¹ with hu
  set ε : ℝ≥0∞ := (2 * (q : ℝ≥0∞) + 1) ^ 2 / (Fintype.card Y : ℝ≥0∞) with hε
  let run : (Tw × M → Y) → ProbComp (S × SM_DT_TCR_SourceFinalValidity.State Tw M) := fun R ↦
    (simulateQ (SM_DT_TCR_SourceFinalValidity.oracles (fvWithEval P (thR R)) pk) choose).run
      .initial
  -- step 1: decompose each game over the first-phase output
  have hdec : ∀ R : Tw × M → Y,
      qWeight (· = true)
        (liftU (run R) >>= fun r ↦
          forge R r.1 >>= fun jm ↦
            liftU (match r.2.challenges[jm.1]? with
              | none => pure false
              | some tm => pure (r.2.valid && decide (jm.2 ≠ tm.2 ∧
                  thR R pk tm.1 jm.2 = thR R pk tm.1 tm.2)))) ρ =
        ∑' r, PQ.Interactive.prob (run R) (· = r) *
          qWeight (fvTcrWin r.2.challenges r.2.valid R) (forge R r.1) ρ := by
    intro R
    rw [qWeight_liftU_bind_tsum]
    refine tsum_congr fun r ↦ ?_
    congr 1
    have hc : (fun jm : ℕ × M ↦
        (liftU (match r.2.challenges[jm.1]? with
          | none => pure false
          | some tm => pure (r.2.valid && decide (jm.2 ≠ tm.2 ∧
              thR R pk tm.1 jm.2 = thR R pk tm.1 tm.2))) : Closed W Bool)) =
        fun jm ↦ pure (decide (fvTcrWin r.2.challenges r.2.valid R jm)) := by
      funext jm
      cases h : r.2.challenges[jm.1]? with
      | none => simp [fvTcrWin, h]
      | some tm => simp [fvTcrWin, h, hth]
    rw [hc, qWeight_bind_pure_decide]
  change ∑ R : Tw × M → Y, u * qWeight (· = true) (liftU (run R) >>= _) ρ ≤ ε
  simp only [hdec]
  -- step 2: exchange the row average and the sum over first-phase outputs
  have hswap : ∑ R : Tw × M → Y, u *
      ∑' r, PQ.Interactive.prob (run R) (· = r) *
        qWeight (fvTcrWin r.2.challenges r.2.valid R) (forge R r.1) ρ =
      ∑' r, ∑ R : Tw × M → Y, u *
        (PQ.Interactive.prob (run R) (· = r) *
          qWeight (fvTcrWin r.2.challenges r.2.valid R) (forge R r.1) ρ) := by
    simp only [← ENNReal.tsum_mul_left]
    exact (Summable.tsum_finsetSum (fun _ _ ↦ CompleteLattice.summable)).symm
  rw [hswap]
  -- step 3: for each first-phase output, the weighted SPR bound on the row
  have hper : ∀ r : S × SM_DT_TCR_SourceFinalValidity.State Tw M,
      ∑ R : Tw × M → Y, u * (PQ.Interactive.prob (run R) (· = r) *
        qWeight (fvTcrWin r.2.challenges r.2.valid R) (forge R r.1) ρ) ≤
      ε * ∑ R : Tw × M → Y, u * PQ.Interactive.prob (run R) (· = r) := by
    intro r
    by_cases hv : r.2.valid = true
    swap
    · have h0 : ∀ R : Tw × M → Y,
          qWeight (fvTcrWin r.2.challenges r.2.valid R) (forge R r.1) ρ = 0 := by
        intro R
        refine le_antisymm ?_ zero_le
        refine (qWeight_mono (q := fun _ ↦ False) (fun jm h ↦ hv h.1) _ ρ).trans ?_
        rw [qWeight_false_fors]
      simp [h0]
    obtain ⟨Mo, hMo⟩ := hModel r.1
    let c : Tw → Option M := tcrTargets r.2.challenges
    let out : ℕ × M → Tw × M := fun l ↦ (tweakAt r.2.challenges l.1, l.2)
    have hobs : ∀ (k : Tw × M) (m : M), c k.1 = some m → k.2 ≠ m →
        ∀ (R : Tw × M → Y) (v : Y), PQ.Interactive.prob (run (Function.update R k v)) (· = r) =
          PQ.Interactive.prob (run R) (· = r) := by
      intro k m hc hk R v
      refine fv_run_prob_congr P pk (thR (Function.update R k v)) (thR R) k.1 m ?_ choose
        .initial r (mem_of_tcrTargets hc) hv
      intro t m' h
      rw [hth, hth]
      refine Function.update_of_ne (fun hk' ↦ ?_) _ _
      have h1 : t = k.1 := by rw [← hk']
      have h2 : m' = k.2 := by rw [← hk']
      exact hk (h2 ▸ h h1)
    have hspr := PQ.QROM.spr_embedded_obs_weighted_le (Function.Embedding.refl (Tw × M))
      (fun _ ↦ Classical.arbitrary Y) c (fun R ↦ PQ.Interactive.prob (run R) (· = r)) hobs
      (fun _ ↦ Mo) (fun _ ↦ out) id
    simp only [patch_refl_eq, id] at hspr
    refine le_trans (Finset.sum_le_sum fun R _ ↦ ?_) hspr
    refine mul_le_mul' le_rfl ?_
    by_cases h0 : PQ.Interactive.prob (run R) (· = r) = 0
    · simp [h0]
    · have hsupp : r ∈ support (run R) := by
        by_contra hn
        exact h0 (prob_eq_zero_of_forall_ne _ _ fun w hw hwr ↦ hn (hwr ▸ hw))
      have hnd := fv_run_nodup (fvWithEval P (thR R)) pk choose r hsupp hv
      rw [← hMo R (fvTcrWin r.2.challenges r.2.valid R)]
      refine mul_le_mul' le_rfl (Mo.prob_mono R ?_)
      rintro jm ⟨-, tm, htm, hne, heq⟩
      have hmem : tm ∈ r.2.challenges := List.mem_of_getElem? htm
      have hout : out jm = (tm.1, jm.2) := by simp [out, tweakAt, htm]
      refine ⟨tm.2, ?_, ?_, ?_⟩
      · rw [hout]
        exact tcrTargets_of_mem hnd hmem
      · rw [hout]
        exact hne
      · rw [hout]
        exact heq
  -- step 4: sum over first-phase outputs
  have hsumu : ∑ _R : Tw × M → Y, u = 1 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hu]
    exact PQ.QROM.natCast_mul_inv_cancel Fintype.card_ne_zero
  calc ∑' r, ∑ R : Tw × M → Y, u * (PQ.Interactive.prob (run R) (· = r) *
          qWeight (fvTcrWin r.2.challenges r.2.valid R) (forge R r.1) ρ)
      ≤ ∑' r, ε * ∑ R : Tw × M → Y, u * PQ.Interactive.prob (run R) (· = r) :=
        tsum_le_tsum fun r ↦ hper r
    _ = ε * ∑ R : Tw × M → Y, u * ∑' r, PQ.Interactive.prob (run R) (· = r) := by
        rw [ENNReal.tsum_mul_left]
        congr 1
        simp only [← ENNReal.tsum_mul_left]
        exact Summable.tsum_finsetSum (fun _ _ ↦ CompleteLattice.summable)
    _ ≤ ε * ∑ _R : Tw × M → Y, u * 1 := by
        gcongr with R
        exact tsum_prob_eq_le_one _
    _ = ε := by simp only [mul_one, hsumu]

end rowtcr

/-! ## The experiment at a fixed seed -/

section seed

variable {W : Type} [Fintype W] {ι PkSeed Tweak M Y : Type} [DecidableEq Tweak] [DecidableEq M]
  [DecidableEq Y]

/-- The winning weight of a quantum TCR-FV adversary once the seed `pk` is drawn. -/
noncomputable def tcrFvInner {P : SM_DT_TCR_SourceFinalValidity.Problem ι PkSeed Tweak M Y}
    (adv : QTcrFV_Adversary W P) (pk : PkSeed) : ℝ≥0∞ :=
  qWeight (· = true)
    (liftU ((simulateQ (SM_DT_TCR_SourceFinalValidity.oracles P pk) adv.choose).run
        .initial) >>= fun r ↦
      adv.forge r.1 pk >>= fun jm ↦
        liftU (match r.2.challenges[jm.1]? with
          | none => pure false
          | some tm => pure (r.2.valid && decide
              (jm.2 ≠ tm.2 ∧ P.th.eval pk tm.1 jm.2 = P.th.eval pk tm.1 tm.2)))) adv.ρ₀

/-- The quantum TCR-FV advantage is the seed average of `tcrFvInner` (any seed distribution). -/
theorem qTcrFV_Advantage_eq_tsum {P : SM_DT_TCR_SourceFinalValidity.Problem ι PkSeed Tweak M Y}
    (adv : QTcrFV_Adversary W P) :
    qTcrFV_Advantage adv =
      ∑' pk, PQ.Interactive.prob P.th.seedGen (· = pk) * tcrFvInner adv pk := by
  unfold qTcrFV_Advantage qTcrFV_Experiment tcrFvInner
  simp only [liftU_bind, liftU_pure, bind_assoc, pure_bind]
  rw [qWeight_liftU_bind_tsum]
  rfl

end seed

/-! ## The generic row bound, DSPR with source final validity (tight) -/

section rowdspr

variable {PkSeed Tw M Y : Type} [DecidableEq Tw]

/-- The second-preimage predicate of the target `tm` in the row `R`. -/
def fvSPE (R : Tw × M → Y) (tm : Tw × M) : Prop := ∃ m', tm.2 ≠ m' ∧ R tm = R (tm.1, m')

/-- The success event of the DSPR-FV game for the final state `(L, v)` and row `R`. -/
def fvDsprS (L : List (Tw × M)) (v : Bool) (R : Tw × M → Y) (jb : ℕ × Bool) : Prop :=
  v = true ∧ ∃ tm, L[jb.1]? = some tm ∧ (fvSPE R tm ↔ jb.2 = true)

/-- The baseline (`SPprob`) event of the DSPR-FV game. -/
def fvDsprP (L : List (Tw × M)) (v : Bool) (R : Tw × M → Y) (jb : ℕ × Bool) : Prop :=
  v = true ∧ ∃ tm, L[jb.1]? = some tm ∧ fvSPE R tm

variable [Fintype Tw] [Fintype M] [DecidableEq M] [Fintype Y] [DecidableEq Y]
  [Nonempty Tw] [AddCommGroup Y]

theorem rowSP_tcrTargets {L : List (Tw × M)} (hnd : (L.map Prod.fst).Nodup) {tm : Tw × M}
    (hmem : tm ∈ L) (R : Tw × M → Y) :
    PQ.QROM.rowSP (tcrTargets L) R tm.1 ↔ fvSPE R tm := by
  have hc := tcrTargets_of_mem hnd hmem
  constructor
  · rintro ⟨m, hm, m', hne, heq⟩
    rw [hc] at hm
    cases hm
    exact ⟨m', fun h ↦ hne h.symm, heq.symm⟩
  · rintro ⟨m', hne, heq⟩
    exact ⟨tm.2, hc, m', fun h ↦ hne h.symm, heq.symm⟩

lemma prob_eq_le_one_fors {S : Type} (mx : ProbComp S) (z : S) : PQ.Interactive.prob mx (· = z) ≤ 1 :=
  (le_tsum (fun x ↦ PQ.Interactive.prob mx (· = x)) z).trans (tsum_prob_eq_le_one mx)

open Classical in
/-- **Generic row bound for SM-DSPR with source final validity and a quantum second phase,
tight and target-count-free.**  As `tcrFv_row_avg_le`, with the second phase described for every
state by an ADDITIVE `q`-query hybrid model satisfying the rows bound (`hModel`), and
`2 ≤ |Y| ≤ |M|`: the row-average of the success weight at `pk` exceeds that of the baseline by at
most `168 q² / |Y|`.  The final decisions `winS`, `winP` are those of the game (`hwinS`,
`hwinP`). -/
theorem dsprFv_row_avg_le (P : SM_DT_TCR_SourceFinalValidity.Problem Empty PkSeed Tw M Y)
    (pk : PkSeed)
    (thR : (Tw × M → Y) → PkSeed → Tw → M → Y) (hth : ∀ R t m, thR R pk t m = R (t, m))
    {S : Type} (choose : OracleComp (FvSpec P) S)
    {W : Type} [Fintype W] (guess : (Tw × M → Y) → S → Closed W (ℕ × Bool))
    (ρ : Matrix W W ℂ) (q : ℕ)
    (hModel : ∀ s, ∃ Mo : PQ.QROM.HybridModel (Tw × M) Y (ℕ × Bool) q,
      Mo.Additive ∧ PQ.QROM.Rows.RowsBound (fun H E ↦ (Mo.prob H E).toReal) q ∧
      ∀ R (Ev : ℕ × Bool → Prop) [DecidablePred Ev], Mo.prob R Ev = qWeight Ev (guess R s) ρ)
    (hY : 2 ≤ Fintype.card Y) (hcard : Fintype.card Y ≤ Fintype.card M)
    (winS winP : (Tw × M → Y) → S × SM_DT_TCR_SourceFinalValidity.State Tw M → ℕ × Bool →
      ProbComp Bool)
    (hwinS : ∀ R r jb, winS R r jb = pure (decide (fvDsprS r.2.challenges r.2.valid R jb)))
    (hwinP : ∀ R r jb, winP R r jb = pure (decide (fvDsprP r.2.challenges r.2.valid R jb))) :
    ∑ R : Tw × M → Y, (Fintype.card (Tw × M → Y) : ℝ≥0∞)⁻¹ *
      qWeight (· = true)
        (liftU ((simulateQ (SM_DT_TCR_SourceFinalValidity.oracles (fvWithEval P (thR R)) pk)
            choose).run .initial) >>= fun r ↦
          guess R r.1 >>= fun jb ↦ liftU (winS R r jb)) ρ ≤
      ∑ R : Tw × M → Y, (Fintype.card (Tw × M → Y) : ℝ≥0∞)⁻¹ *
        qWeight (· = true)
          (liftU ((simulateQ (SM_DT_TCR_SourceFinalValidity.oracles (fvWithEval P (thR R)) pk)
              choose).run .initial) >>= fun r ↦
            guess R r.1 >>= fun jb ↦ liftU (winP R r jb)) ρ +
        ENNReal.ofReal (168 * (q : ℝ) ^ 2 / Fintype.card Y) := by
  have : Nonempty M := Fintype.card_pos_iff.1 (by omega)
  have : Nontrivial Y := Fintype.one_lt_card_iff_nontrivial.1 (by omega)
  have : Nonempty Y := inferInstance
  set u : ℝ≥0∞ := (Fintype.card (Tw × M → Y) : ℝ≥0∞)⁻¹ with hu
  set ε : ℝ≥0∞ := ENNReal.ofReal (168 * (q : ℝ) ^ 2 / Fintype.card Y) with hε
  let run : (Tw × M → Y) → ProbComp (S × SM_DT_TCR_SourceFinalValidity.State Tw M) := fun R ↦
    (simulateQ (SM_DT_TCR_SourceFinalValidity.oracles (fvWithEval P (thR R)) pk) choose).run
      .initial
  let pr : (S × SM_DT_TCR_SourceFinalValidity.State Tw M) → (Tw × M → Y) → ℝ≥0∞ :=
    fun r R ↦ PQ.Interactive.prob (run R) (· = r)
  -- step 1: decompose each game over the first-phase output
  have hdec : ∀ (Ev : List (Tw × M) → Bool → (Tw × M → Y) → ℕ × Bool → Prop)
      (win : (Tw × M → Y) → S × SM_DT_TCR_SourceFinalValidity.State Tw M → ℕ × Bool →
        ProbComp Bool)
      (_hw : ∀ R r jb, win R r jb = pure (decide (Ev r.2.challenges r.2.valid R jb)))
      (R : Tw × M → Y),
      qWeight (· = true)
        (liftU (run R) >>= fun r ↦ guess R r.1 >>= fun jb ↦ liftU (win R r jb)) ρ =
        ∑' r, pr r R * qWeight (Ev r.2.challenges r.2.valid R) (guess R r.1) ρ := by
    intro Ev win hw R
    rw [qWeight_liftU_bind_tsum]
    refine tsum_congr fun r ↦ ?_
    congr 1
    have hc : (fun jb : ℕ × Bool ↦ (liftU (win R r jb) : Closed W Bool)) =
        fun jb ↦ pure (decide (Ev r.2.challenges r.2.valid R jb)) := by
      funext jb
      rw [hw, liftU_pure]
    rw [hc, qWeight_bind_pure_decide]
  change ∑ R : Tw × M → Y, u * qWeight (· = true) (liftU (run R) >>= _) ρ ≤
    ∑ R : Tw × M → Y, u * qWeight (· = true) (liftU (run R) >>= _) ρ + ε
  rw [Finset.sum_congr rfl fun R _ ↦ congrArg (u * ·) (hdec fvDsprS winS hwinS R),
    Finset.sum_congr rfl fun R _ ↦ congrArg (u * ·) (hdec fvDsprP winP hwinP R)]
  -- step 2: exchange
  have hswap : ∀ f : (S × SM_DT_TCR_SourceFinalValidity.State Tw M) → (Tw × M → Y) → ℝ≥0∞,
      ∑ R : Tw × M → Y, u * ∑' r, f r R = ∑' r, ∑ R : Tw × M → Y, u * f r R := by
    intro f
    simp only [← ENNReal.tsum_mul_left]
    exact (Summable.tsum_finsetSum (fun _ _ ↦ CompleteLattice.summable)).symm
  rw [hswap, hswap]
  -- step 3: per first-phase output
  have hper : ∀ r : S × SM_DT_TCR_SourceFinalValidity.State Tw M,
      ∑ R : Tw × M → Y, u * (pr r R *
        qWeight (fvDsprS r.2.challenges r.2.valid R) (guess R r.1) ρ) ≤
      ∑ R : Tw × M → Y, u * (pr r R *
        qWeight (fvDsprP r.2.challenges r.2.valid R) (guess R r.1) ρ) +
        ε * ∑ R : Tw × M → Y, u * pr r R := by
    intro r
    by_cases hsup : ∃ R₀, r ∈ support (run R₀)
    swap
    · have h0 : ∀ R, pr r R = 0 := fun R ↦
        prob_eq_zero_of_forall_ne _ _ fun w hw hwr ↦ hsup ⟨R, hwr ▸ hw⟩
      simp [h0]
    obtain ⟨R₀, hR₀⟩ := hsup
    by_cases hv : r.2.valid = true
    swap
    · have h0 : ∀ R : Tw × M → Y,
          qWeight (fvDsprS r.2.challenges r.2.valid R) (guess R r.1) ρ = 0 := by
        intro R
        refine le_antisymm ?_ zero_le
        refine (qWeight_mono (q := fun _ ↦ False) (fun jm h ↦ hv h.1) _ ρ).trans ?_
        rw [qWeight_false_fors]
      simp [h0]
    have hnd := fv_run_nodup (fvWithEval P (thR R₀)) pk choose r hR₀ hv
    obtain ⟨Mo, hadd, hrows, hMo⟩ := hModel r.1
    set L := r.2.challenges with hL
    let c : Tw → Option M := tcrTargets L
    set o : (Tw × M → Y) → ℝ≥0∞ := pr r with ho
    have hobs : ∀ (k : Tw × M) (m : M), c k.1 = some m → k.2 ≠ m →
        ∀ (R : Tw × M → Y) (v : Y), o (Function.update R k v) = o R := by
      intro k m hc hk R v
      refine fv_run_prob_congr P pk (thR (Function.update R k v)) (thR R) k.1 m ?_ choose
        .initial r (mem_of_tcrTargets hc) hv
      intro t m' h
      rw [hth, hth]
      refine Function.update_of_ne (fun hk' ↦ ?_) _ _
      have h1 : t = k.1 := by rw [← hk']
      have h2 : m' = k.2 := by rw [← hk']
      exact hk (h2 ▸ h h1)
    let V : ℝ≥0∞ → ℕ × Bool → Prop := fun _ l ↦ (L[l.1]?).isSome = true
    let tw : ℝ≥0∞ → ℕ × Bool → Tw := fun _ l ↦ tweakAt L l.1
    let b : ℝ≥0∞ → ℕ × Bool → Prop := fun _ l ↦ l.2 = true
    have hV : ∀ a l, V a l → ∃ m, c (tw a l) = some m := by
      intro a l hl
      obtain ⟨tm, htm⟩ := Option.isSome_iff_exists.1 hl
      refine ⟨tm.2, ?_⟩
      have : tw a l = tm.1 := by simp [tw, tweakAt, htm]
      rw [this]
      exact tcrTargets_of_mem hnd (List.mem_of_getElem? htm)
    have hS : ∀ R, fvDsprS L r.2.valid R = PQ.QROM.dsprEvS c o V tw b R := by
      intro R
      funext l
      apply propext
      cases htm : L[l.1]? with
      | none =>
        simp only [fvDsprS, PQ.QROM.dsprEvS, V, htm, Option.isSome_none]
        simp
      | some tm =>
        have htw : tw (o R) l = tm.1 := by simp [tw, tweakAt, htm]
        simp only [fvDsprS, PQ.QROM.dsprEvS, V, b, htm, htw, hv, Option.isSome_some,
          Option.some.injEq, true_and, exists_eq_left']
        rw [rowSP_tcrTargets hnd (List.mem_of_getElem? htm)]
    have hP : ∀ R, fvDsprP L r.2.valid R = PQ.QROM.dsprEvP c o V tw R := by
      intro R
      funext l
      apply propext
      cases htm : L[l.1]? with
      | none =>
        simp only [fvDsprP, PQ.QROM.dsprEvP, V, htm, Option.isSome_none]
        simp
      | some tm =>
        have htw : tw (o R) l = tm.1 := by simp [tw, tweakAt, htm]
        simp only [fvDsprP, PQ.QROM.dsprEvP, V, htm, htw, hv, Option.isSome_some,
          Option.some.injEq, true_and, exists_eq_left']
        rw [rowSP_tcrTargets hnd (List.mem_of_getElem? htm)]
    have hML := PQ.QROM.markLaw_of_obs (Function.Embedding.refl (Tw × M)) c o hobs
    have hT := PQ.QROM.dspr_embedded_tight (Function.Embedding.refl (Tw × M))
      (fun _ ↦ Classical.arbitrary Y) c o (fun _ ↦ Mo) (fun _ ↦ hadd) V tw b hV
      (fun _ ↦ hrows) hML (fun a ↦ a.toReal) (fun _ ↦ ENNReal.toReal_nonneg) 0 le_rfl
      (by have := PQ.QROM.Tight.pow_noSP_le_half' (X := M) (Y := Y) hY hcard; linarith)
    simp only [patch_refl_eq, zero_add] at hT
    -- the two weights as model probabilities
    have eS : ∀ R, qWeight (fvDsprS L r.2.valid R) (guess R r.1) ρ =
        Mo.prob R (PQ.QROM.dsprEvS c o V tw b R) := by
      intro R; rw [← hS R, hMo R]
    have eP : ∀ R, qWeight (fvDsprP L r.2.valid R) (guess R r.1) ρ =
        Mo.prob R (PQ.QROM.dsprEvP c o V tw R) := by
      intro R; rw [← hP R, hMo R]
    simp only [eS, eP]
    have hpr1 : ∀ R, pr r R ≠ ⊤ := fun R ↦ ne_top_of_le_ne_top one_ne_top (prob_eq_le_one_fors _ _)
    have hMo1 : ∀ R E, Mo.prob R E ≠ ⊤ := fun R E ↦
      ne_top_of_le_ne_top one_ne_top (Mo.prob_le_one R E)
    have hu1 : u ≠ ⊤ := ENNReal.inv_ne_top.2 (Nat.cast_ne_zero.2 Fintype.card_ne_zero)
    have hfS : ∀ R, u * (pr r R * Mo.prob R (PQ.QROM.dsprEvS c o V tw b R)) ≠ ⊤ := fun R ↦
      ENNReal.mul_ne_top hu1 (ENNReal.mul_ne_top (hpr1 R) (hMo1 _ _))
    have hfP : ∀ R, u * (pr r R * Mo.prob R (PQ.QROM.dsprEvP c o V tw R)) ≠ ⊤ := fun R ↦
      ENNReal.mul_ne_top hu1 (ENNReal.mul_ne_top (hpr1 R) (hMo1 _ _))
    have hfW : ∀ R, u * pr r R ≠ ⊤ := fun R ↦ ENNReal.mul_ne_top hu1 (hpr1 R)
    refine PQ.QROM.ennreal_le_add_of_toReal (ENNReal.sum_ne_top.2 fun R _ ↦ hfS R)
      (ENNReal.sum_ne_top.2 fun R _ ↦ hfP R) (ENNReal.sum_ne_top.2 fun R _ ↦ hfW R)
      (by positivity) ?_
    rw [ENNReal.toReal_sum fun R _ ↦ hfS R, ENNReal.toReal_sum fun R _ ↦ hfP R,
      ENNReal.toReal_sum fun R _ ↦ hfW R, ← Finset.sum_sub_distrib]
    simp only [ENNReal.toReal_mul]
    have hu0 : 0 ≤ u.toReal := ENNReal.toReal_nonneg
    have key := mul_le_mul_of_nonneg_left hT hu0
    refine le_trans (le_of_eq ?_) (key.trans (le_of_eq ?_))
    · rw [ho]
      simp only [Finset.mul_sum]
      exact Finset.sum_congr rfl fun R _ ↦ by ring
    · rw [ho]
      simp only [Finset.mul_sum]
      exact Finset.sum_congr rfl fun R _ ↦ by ring
  -- step 4: sum over first-phase outputs
  have hsumu : ∑ _R : Tw × M → Y, u = 1 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hu]
    exact PQ.QROM.natCast_mul_inv_cancel Fintype.card_ne_zero
  have hC : ∑' r, ∑ R : Tw × M → Y, u * pr r R ≤ 1 := by
    rw [← hswap]
    calc ∑ R : Tw × M → Y, u * ∑' r, pr r R ≤ ∑ _R : Tw × M → Y, u * 1 := by
          gcongr with R
          exact tsum_prob_eq_le_one _
      _ = 1 := by simp only [mul_one, hsumu]
  calc ∑' r, ∑ R : Tw × M → Y, u * (pr r R *
          qWeight (fvDsprS r.2.challenges r.2.valid R) (guess R r.1) ρ)
      ≤ ∑' r, (∑ R : Tw × M → Y, u * (pr r R *
          qWeight (fvDsprP r.2.challenges r.2.valid R) (guess R r.1) ρ) +
          ε * ∑ R : Tw × M → Y, u * pr r R) := tsum_le_tsum fun r ↦ hper r
    _ = ∑' r, ∑ R : Tw × M → Y, u * (pr r R *
          qWeight (fvDsprP r.2.challenges r.2.valid R) (guess R r.1) ρ) +
          ε * ∑' r, ∑ R : Tw × M → Y, u * pr r R := by
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_left]
    _ ≤ _ := by
        gcongr
        exact (mul_le_mul' le_rfl hC).trans (mul_one ε).le

end rowdspr

section seeddspr

variable {W : Type} [Fintype W] {ι PkSeed Tweak M Y : Type} [Fintype M] [DecidableEq Tweak]
  [DecidableEq M] [DecidableEq Y]

/-- The success weight of a quantum DSPR-FV adversary once the seed `pk` is drawn. -/
noncomputable def dsprFvSuccInner {P : SM_DT_DSPR_SourceFinalValidity.Problem ι PkSeed Tweak M Y}
    (adv : QDsprFV_Adversary W P) (pk : PkSeed) : ℝ≥0∞ :=
  qWeight (· = true)
    (liftU ((simulateQ (SM_DT_DSPR_SourceFinalValidity.oracles P pk) adv.choose).run
        .initial) >>= fun r ↦
      adv.guess r.1 pk >>= fun jb ↦
        liftU (match r.2.challenges[jb.1]? with
          | none => pure false
          | some tm => pure (r.2.valid && decide
              (TweakableHash.SecondPreimageExists P.th pk tm.1 tm.2 ↔ jb.2 = true)))) adv.ρ₀

/-- The baseline weight of a quantum DSPR-FV adversary once the seed `pk` is drawn. -/
noncomputable def dsprFvSPInner {P : SM_DT_DSPR_SourceFinalValidity.Problem ι PkSeed Tweak M Y}
    (adv : QDsprFV_Adversary W P) (pk : PkSeed) : ℝ≥0∞ :=
  qWeight (· = true)
    (liftU ((simulateQ (SM_DT_DSPR_SourceFinalValidity.oracles P pk) adv.choose).run
        .initial) >>= fun r ↦
      adv.guess r.1 pk >>= fun jb ↦
        liftU (match r.2.challenges[jb.1]? with
          | none => pure false
          | some tm => pure (r.2.valid && decide
              (TweakableHash.SecondPreimageExists P.th pk tm.1 tm.2)))) adv.ρ₀

theorem qDsprFV_Success_eq_tsum {P : SM_DT_DSPR_SourceFinalValidity.Problem ι PkSeed Tweak M Y}
    (adv : QDsprFV_Adversary W P) :
    qDsprFV_Success adv =
      ∑' pk, PQ.Interactive.prob P.th.seedGen (· = pk) * dsprFvSuccInner adv pk := by
  unfold qDsprFV_Success qDsprFV_Experiment dsprFvSuccInner
  simp only [liftU_bind, liftU_pure, bind_assoc, pure_bind]
  rw [qWeight_liftU_bind_tsum]
  rfl

theorem qDsprFV_SPProbability_eq_tsum
    {P : SM_DT_DSPR_SourceFinalValidity.Problem ι PkSeed Tweak M Y}
    (adv : QDsprFV_Adversary W P) :
    qDsprFV_SPProbability adv =
      ∑' pk, PQ.Interactive.prob P.th.seedGen (· = pk) * dsprFvSPInner adv pk := by
  unfold qDsprFV_SPProbability qDsprFV_SpExperiment dsprFvSPInner
  simp only [liftU_bind, liftU_pure, bind_assoc, pure_bind]
  rw [qWeight_liftU_bind_tsum]
  rfl

end seeddspr

end PQ.Interactive

#print axioms PQ.Interactive.fv_run_ext
#print axioms PQ.Interactive.fv_run_nodup
#print axioms PQ.Interactive.fv_run_prob_congr
#print axioms PQ.Interactive.tcrFv_row_avg_le
#print axioms PQ.Interactive.qTcrFV_Advantage_eq_tsum
#print axioms PQ.Interactive.dsprFv_row_avg_le
#print axioms PQ.Interactive.qDsprFV_Success_eq_tsum
#print axioms PQ.Interactive.qDsprFV_SPProbability_eq_tsum
