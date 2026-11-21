import PQ.Interactive.ApproxGames
import PQ.Interactive.GamesGeneral

/-!
# Limit collapse for GENERAL quantum two-phase adversaries

In the general two-phase games of `GamesGeneral.lean` both phases are quantum machines and the
workspace state is carried across the seed reveal.  To classicalise such an adversary the classical
first phase must hand the (unnormalised) post-measurement state to the classical second phase:

* `toProbCompStWith samp Q ρ : OracleComp (unifSpec + spec') (α × Matrix W W ℂ)` and
  `toProbCompCStWith samp X ρ : ProbComp (α × Matrix W W ℂ)` — the classical strategies of
  `Approx.lean` that also RETURN the tracked unnormalised post-state, for every sampler;
* `tendsto_bind_closedSt`, `tendsto_close_bindSt` — limit collapse with continuations that
  receive the post-state;
* `tendsto_twoPhaseG` — limit collapse for a game "classical pre-processing, quantum first phase
  against a classical oracle implementation, quantum second phase on the same workspace,
  classical post-processing";
* for each general game, the classical approximants `adv.toClassicalWith s` (a VCVio adversary
  with classical state `adv.State × Matrix W W ℂ`: the first phase is `toProbCompStWith s choose
  ρ₀`, the second phase is `toProbCompCWith s (forge st pk) ρ'` started from the state `ρ'` handed
  over) and
  `Tendsto (fun n ↦ classical advantage (adv.toClassicalWith (samp n))) atTop
    (𝓝 (general quantum advantage adv))`
  for every `BornApprox` sequence of samplers, in particular the rational samplers `sampN`
  (`…G_N` corollaries): `tendsto_SM_DT_TCR_AdvantageG`, `tendsto_SM_DT_PRE_AdvantageG`,
  `tendsto_SM_DT_UD_AdvantageG`, `tendsto_tcrFV_advantageG`, `tendsto_dsprFV_advantageG`.

Consequences (`…_le_of_forall`): every bound valid for all classical VCVio adversaries of a game —
in particular a bound by a constant `ε` — holds for every general quantum adversary of the general
quantum game.  Together with `…AdvantageG_ofClassical` (the classical game is the special case)
this says: the set of advantages of the general quantum game lies in the closure of the set of
classical advantages and contains it; the general quantum games are well-posed relative to
VCVio's definitions.  (The classical approximants are not efficient: they carry a density
matrix.  The statement is about the definitions, not about complexity.)

No rationality hypothesis anywhere.
-/

open OracleComp OracleSpec ENNReal Quantum MeasureTheory Topology
open Filter (Tendsto atTop)
open scoped ComplexOrder

namespace PQ.Interactive

variable {W : Type} [Fintype W] {α β γ δ : Type}
variable {ι' : Type} {spec' : OracleSpec ι'} {σ : Type}

/-! ## State-returning classical strategies -/

/-- The classical strategy of the open machine `Q` for the sampler `samp`, returning the output
together with the tracked unnormalised post-measurement state. -/
noncomputable def toProbCompStWith (samp : Sampler W) (Q : QOC W (unifSpec + spec') α) :
    Matrix W W ℂ → OracleComp (unifSpec + spec') (α × Matrix W W ℂ) :=
  OracleComp.construct
    (C := fun _ ↦ Matrix W W ℂ → OracleComp (unifSpec + spec') (α × Matrix W W ℂ))
    (fun a ρ ↦ pure (a, ρ))
    (fun t _ ih ρ ↦
      match t, ih with
      | .inl j, ih => liftL (samp j ρ) >>= fun i ↦ ih i (j.2.1.branch i ρ)
      | .inr t, ih => liftM ((unifSpec + spec').query t) >>= fun u ↦ ih u ρ) Q

/-- The classical strategy of the closed machine `X` for the sampler `samp`, returning the output
together with the tracked unnormalised post-measurement state. -/
noncomputable def toProbCompCStWith (samp : Sampler W) (X : Closed W α) :
    Matrix W W ℂ → ProbComp (α × Matrix W W ℂ) :=
  OracleComp.construct (C := fun _ ↦ Matrix W W ℂ → ProbComp (α × Matrix W W ℂ))
    (fun a ρ ↦ pure (a, ρ))
    (fun t _ ih ρ ↦
      match t, ih with
      | .inl j, ih => samp j ρ >>= fun i ↦ ih i (j.2.1.branch i ρ)
      | .inr n, ih => liftM (unifSpec.query n) >>= fun u ↦ ih u ρ) X

variable (samp : Sampler W)

@[simp] lemma toProbCompStWith_pure (a : α) (ρ : Matrix W W ℂ) :
    toProbCompStWith samp (pure a : QOC W (unifSpec + spec') α) ρ = pure (a, ρ) := rfl

lemma toProbCompStWith_instr_bind (j : InstrIdx W)
    (k : Fin (j.1 + 1) → QOC W (unifSpec + spec') α) (ρ : Matrix W W ℂ) :
    toProbCompStWith samp (liftM ((instrSpec W + (unifSpec + spec')).query (Sum.inl j)) >>= k) ρ =
      liftL (samp j ρ) >>= fun i ↦ toProbCompStWith samp (k i) (j.2.1.branch i ρ) := rfl

lemma toProbCompStWith_query_bind (t : (unifSpec + spec').Domain)
    (k : (unifSpec + spec').Range t → QOC W (unifSpec + spec') α) (ρ : Matrix W W ℂ) :
    toProbCompStWith samp (liftM ((instrSpec W + (unifSpec + spec')).query (Sum.inr t)) >>= k) ρ =
      liftM ((unifSpec + spec').query t) >>= fun u ↦ toProbCompStWith samp (k u) ρ := rfl

@[simp] lemma toProbCompCStWith_pure (a : α) (ρ : Matrix W W ℂ) :
    toProbCompCStWith samp (pure a : Closed W α) ρ = pure (a, ρ) := rfl

lemma toProbCompCStWith_instr_bind (j : InstrIdx W) (k : Fin (j.1 + 1) → Closed W α)
    (ρ : Matrix W W ℂ) :
    toProbCompCStWith samp (liftM ((instrSpec W + unifSpec).query (Sum.inl j)) >>= k) ρ =
      samp j ρ >>= fun i ↦ toProbCompCStWith samp (k i) (j.2.1.branch i ρ) := rfl

lemma toProbCompCStWith_unif_bind (n : ℕ) (k : Fin (n + 1) → Closed W α) (ρ : Matrix W W ℂ) :
    toProbCompCStWith samp (liftM ((instrSpec W + unifSpec).query (Sum.inr n)) >>= k) ρ =
      liftM (unifSpec.query n) >>= fun u ↦ toProbCompCStWith samp (k u) ρ := rfl

/-- Forgetting the returned state gives the strategy of `Approx.lean`. -/
theorem fst_map_toProbCompStWith (Q : QOC W (unifSpec + spec') α) (ρ : Matrix W W ℂ) :
    Prod.fst <$> toProbCompStWith samp Q ρ = toProbCompWith samp Q ρ := by
  induction Q using OracleComp.inductionOn generalizing ρ with
  | pure a => simp
  | query_bind t k ih =>
    rcases t with j | t
    · rw [toProbCompStWith_instr_bind, toProbCompWith_instr_bind, map_bind]
      simp only [ih]
    · rw [toProbCompStWith_query_bind, toProbCompWith_query_bind, map_bind]
      simp only [ih]

theorem fst_map_toProbCompCStWith (X : Closed W α) (ρ : Matrix W W ℂ) :
    Prod.fst <$> toProbCompCStWith samp X ρ = toProbCompCWith samp X ρ := by
  induction X using OracleComp.inductionOn generalizing ρ with
  | pure a => simp
  | query_bind t k ih =>
    rcases t with j | n
    · rw [toProbCompCStWith_instr_bind, toProbCompCWith_instr_bind, map_bind]
      simp only [ih]
    · rw [toProbCompCStWith_unif_bind, toProbCompCWith_unif_bind, map_bind]
      simp only [ih]

/-- Classical code does not change the tracked state. -/
lemma toProbCompCStWith_liftU_bind (oa : ProbComp γ) (F : γ → Closed W α) (ρ : Matrix W W ℂ) :
    toProbCompCStWith samp (liftU oa >>= F) ρ = oa >>= fun x ↦ toProbCompCStWith samp (F x) ρ := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp
  | query_bind n k ih =>
    rw [liftU_query_bind, bind_assoc, toProbCompCStWith_unif_bind, bind_assoc]
    simp only [ih]

/-- **Closing commutes with the state-returning classicalisation** (up to reordering the output
`((a, s'), ρ') ↔ ((a, ρ'), s')`). -/
theorem toProbCompCStWith_close (impl : QueryImpl (unifSpec + spec') (StateT σ ProbComp))
    (himpl : ForwardsUnif impl) (Q : QOC W (unifSpec + spec') α) (s : σ) (ρ : Matrix W W ℂ) :
    toProbCompCStWith samp (close impl Q s) ρ =
      (fun z : (α × Matrix W W ℂ) × σ ↦ ((z.1.1, z.2), z.1.2)) <$>
        (simulateQ impl (toProbCompStWith samp Q ρ)).run s := by
  induction Q using OracleComp.inductionOn generalizing s ρ with
  | pure a => simp
  | query_bind t k ih =>
    rcases t with j | t
    · rw [close_instr_bind, toProbCompCStWith_instr_bind, toProbCompStWith_instr_bind,
        himpl.run_simulateQ_liftL_bind, map_bind]
      simp only [ih]
    · rw [close_query_bind, toProbCompCStWith_liftU_bind, toProbCompStWith_query_bind,
        simulateQ_bind, StateT.run_bind, simulateQ_spec_query, map_bind]
      simp only [ih]

/-! ## Limit collapse with state-dependent continuations -/

/-- **Limit collapse of a closed machine, continuations receiving the post-state.**  The classical
continuation `g n` reads the output `x` and the unnormalised post-state `ρ'`; if, from every
positive-semidefinite `ρ'`, it converges to the quantum continuation `f x` started in `ρ'`, the
composites converge. -/
theorem tendsto_bind_closedSt {samp : ℕ → Sampler W} (hs : BornApprox samp)
    (p : β → Prop) [DecidablePred p] (f : α → Closed W β)
    (g : ℕ → α × Matrix W W ℂ → ProbComp β)
    (hfg : ∀ x (ρ' : Matrix W W ℂ), ρ'.PosSemidef →
      Tendsto (fun n ↦ ENNReal.ofReal ρ'.trace.re * prob (g n (x, ρ')) p) atTop
        (𝓝 (qWeight p (f x) ρ')))
    (X : Closed W α) (ρ : Matrix W W ℂ) (hρ : ρ.PosSemidef) :
    Tendsto (fun n ↦ ENNReal.ofReal ρ.trace.re *
        prob (toProbCompCStWith (samp n) X ρ >>= g n) p) atTop
      (𝓝 (qWeight p (X >>= f) ρ)) := by
  induction X using OracleComp.inductionOn generalizing ρ with
  | pure a => simpa using hfg a ρ hρ
  | query_bind t k ih =>
    rcases t with j | m
    · rw [bind_assoc, qWeight_instr_bind]
      simp only [toProbCompCStWith_instr_bind, bind_assoc]
      have hnn : ∀ i, 0 ≤ (j.2.1.branch i ρ).trace.re := fun i ↦
        (posSemidef_branch j i hρ).trace_re_nonneg
      have hsum : ∑ i, (j.2.1.branch i ρ).trace.re = ρ.trace.re := by
        rw [← Complex.re_sum]
        exact congrArg Complex.re (j.2.2.sum_trace_eq (s := Finset.univ) (by simp) ρ)
      by_cases hc : ρ.trace.re = 0
      · have h0 : ∀ i, (j.2.1.branch i ρ).trace.re = 0 := fun i ↦
          (Finset.sum_eq_zero_iff_of_nonneg fun i _ ↦ hnn i).mp (hsum.trans hc) i
            (Finset.mem_univ i)
        have hz : ∀ i, qWeight p (k i >>= f) (j.2.1.branch i ρ) = 0 := fun i ↦ by
          have := qWeight_le_trace p (k i >>= f) (posSemidef_branch j i hρ)
          simpa [h0 i] using this
        simp [hz, hc]
      · have hcpos : 0 < ρ.trace.re := lt_of_le_of_ne hρ.trace_re_nonneg (Ne.symm hc)
        obtain ⟨w, hw, hwlim⟩ := hs j ρ hρ hc
        simp only [hw, Finset.mul_sum]
        refine tendsto_finsetSum _ fun i _ ↦ ?_
        simp only [← mul_assoc]
        refine tendsto_mul_of_le_one (t := ENNReal.ofReal (j.2.1.branch i ρ).trace.re)
          ENNReal.ofReal_ne_top ?_ (fun n ↦ prob_le_one _ _)
          (ih i _ (posSemidef_branch j i hρ))
        have := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal ρ.trace.re) (hwlim i)
          (Or.inr ENNReal.ofReal_ne_top)
        rwa [bornW, ← ENNReal.ofReal_mul hcpos.le, mul_div_cancel₀ _ hc] at this
    · rw [bind_assoc, qWeight_unif_bind]
      refine (ENNReal.Tendsto.const_mul (a := ((m : ℝ≥0∞) + 1)⁻¹)
        (tendsto_finsetSum _ fun i _ ↦ ih i ρ hρ) (Or.inr (by simp))).congr fun n ↦ ?_
      rw [toProbCompCStWith_unif_bind, bind_assoc, prob_unif_query_bind]
      simp only [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ ↦ mul_left_comm _ _ _

/-- **Limit collapse of an open machine against a classical oracle implementation,
continuations receiving the post-state.** -/
theorem tendsto_close_bindSt {samp : ℕ → Sampler W} (hs : BornApprox samp)
    (impl : QueryImpl (unifSpec + spec') (StateT σ ProbComp)) (himpl : ForwardsUnif impl)
    (p : β → Prop) [DecidablePred p] (f : α × σ → Closed W β)
    (g : ℕ → (α × Matrix W W ℂ) × σ → ProbComp β)
    (hfg : ∀ (x : α × σ) (ρ' : Matrix W W ℂ), ρ'.PosSemidef →
      Tendsto (fun n ↦ ENNReal.ofReal ρ'.trace.re * prob (g n ((x.1, ρ'), x.2)) p) atTop
        (𝓝 (qWeight p (f x) ρ')))
    (Q : QOC W (unifSpec + spec') α) (s : σ) (ρ : Matrix W W ℂ) (hρ : ρ.PosSemidef) :
    Tendsto (fun n ↦ ENNReal.ofReal ρ.trace.re *
        prob ((simulateQ impl (toProbCompStWith (samp n) Q ρ)).run s >>= g n) p) atTop
      (𝓝 (qWeight p (close impl Q s >>= f) ρ)) := by
  refine (tendsto_bind_closedSt hs p f
    (fun n (y : (α × σ) × Matrix W W ℂ) ↦ g n ((y.1.1, y.2), y.1.2)) hfg
    (close impl Q s) ρ hρ).congr fun n ↦ ?_
  rw [toProbCompCStWith_close _ impl himpl, bind_map_left]

/-- **Limit collapse for general two-phase games.**  Classical pre-processing `pre`; a quantum
first phase `Q a` against the classical oracle implementation `impl a`; a quantum second phase
`X a x` on the same workspace (no oracle), reading the classical output `x` of the first phase;
classical post-processing reading the final oracle state.  The classical game played by the
state-passing classical approximants converges to the Born probability. -/
theorem tendsto_twoPhaseG {samp : ℕ → Sampler W} (hs : BornApprox samp) (pre : ProbComp γ)
    (impl : γ → QueryImpl (unifSpec + spec') (StateT σ ProbComp))
    (himpl : ∀ a, ForwardsUnif (impl a)) (s₀ : γ → σ) (Q : γ → QOC W (unifSpec + spec') α)
    (X : γ → α → Closed W δ) (post : γ → σ → δ → ProbComp β) (p : β → Prop) [DecidablePred p]
    (ρ : Matrix W W ℂ) (hρ : ρ.PosSemidef) (h1 : ρ.trace = 1) :
    Tendsto (fun n ↦ prob (pre >>= fun a ↦
        (simulateQ (impl a) (toProbCompStWith (samp n) (Q a) ρ)).run (s₀ a) >>= fun r ↦
          toProbCompCWith (samp n) (X a r.1.1) r.1.2 >>= post a r.2) p) atTop
      (𝓝 (qWeight p (liftU pre >>= fun a ↦ close (impl a) (Q a) (s₀ a) >>= fun r ↦
        X a r.1 >>= fun x ↦ liftU (post a r.2 x)) ρ)) := by
  have h1' : ENNReal.ofReal ρ.trace.re = 1 := by simp [h1]
  have key : ∀ a, Tendsto (fun n ↦ (1 : ℝ≥0∞) * prob
        ((simulateQ (impl a) (toProbCompStWith (samp n) (Q a) ρ)).run (s₀ a) >>= fun r ↦
          toProbCompCWith (samp n) (X a r.1.1) r.1.2 >>= post a r.2) p) atTop
      (𝓝 (qWeight p (close (impl a) (Q a) (s₀ a) >>= fun r ↦
        X a r.1 >>= fun x ↦ liftU (post a r.2 x)) ρ)) := by
    intro a
    have hpost : ∀ (s' : σ) (y : δ) (ρ'' : Matrix W W ℂ), ρ''.PosSemidef →
        Tendsto (fun _ : ℕ ↦ ENNReal.ofReal ρ''.trace.re * prob (post a s' y) p) atTop
          (𝓝 (qWeight p (liftU (post a s' y) : Closed W β) ρ'')) := by
      intro s' y ρ'' _
      rw [qWeight_liftU]
      exact tendsto_const_nhds
    have hfg : ∀ (x : α × σ) (ρ' : Matrix W W ℂ), ρ'.PosSemidef →
        Tendsto (fun n ↦ ENNReal.ofReal ρ'.trace.re *
          prob (toProbCompCWith (samp n) (X a x.1) ρ' >>= post a x.2) p) atTop
          (𝓝 (qWeight p (X a x.1 >>= fun y ↦ liftU (post a x.2 y)) ρ')) :=
      fun x ρ' hρ' ↦ tendsto_bind_closed hs p (fun y ↦ liftU (post a x.2 y))
        (fun _ ↦ post a x.2) (fun y ρ'' h'' ↦ hpost x.2 y ρ'' h'') (X a x.1) ρ' hρ'
    have := tendsto_close_bindSt hs (impl a) (himpl a) p
      (fun x ↦ X a x.1 >>= fun y ↦ liftU (post a x.2 y))
      (fun n z ↦ toProbCompCWith (samp n) (X a z.1.1) z.1.2 >>= post a z.2)
      hfg (Q a) (s₀ a) ρ hρ
    rw [h1'] at this
    exact this
  have := tendsto_liftU_bind p pre _ _ 1 ρ key
  simp only [one_mul] at this
  exact this

lemma tendsto_nhds_of_eq {F : ℕ → ℝ≥0∞} {A B : ℝ≥0∞} (h : Tendsto F atTop (𝓝 A)) (e : B = A) :
    Tendsto F atTop (𝓝 B) := e ▸ h

/-! ## SM-DT-TCR -/

section smtcr

open TweakableHash

variable {ι PkSeed Tweak M Y : Type} {samp : ℕ → Sampler W}

/-- The classical approximant of a general quantum SM-DT-TCR adversary for the sampler `s`: the
first phase is the state-returning classical strategy of `choose`; the classical state carries
the unnormalised workspace state, from which the second phase runs the classical strategy of
`forge`. -/
noncomputable def QSM_DT_TCR_AdversaryG.toClassicalWith (s : Sampler W)
    {P : SM_DT_TCR_Problem ι PkSeed Tweak M Y} (adv : QSM_DT_TCR_AdversaryG W P) :
    SM_DT_TCR_Adversary P where
  State := adv.State × Matrix W W ℂ
  choose := toProbCompStWith s adv.choose adv.ρ₀
  forge st pk := toProbCompCWith s (adv.forge st.1 pk) st.2

/-- **The general quantum SM-DT-TCR advantage is the limit of the classical SM-DT-TCR advantages
of the classical approximants.** -/
theorem tendsto_SM_DT_TCR_AdvantageG [DecidableEq Tweak] [DecidableEq M] [DecidableEq Y]
    (hs : BornApprox samp) {P : SM_DT_TCR_Problem ι PkSeed Tweak M Y}
    (adv : QSM_DT_TCR_AdversaryG W P) :
    Tendsto (fun n ↦ SM_DT_TCR_Advantage (adv.toClassicalWith (samp n))) atTop
      (𝓝 (qSM_DT_TCR_AdvantageG adv)) := by
  have key := tendsto_twoPhaseG hs P.th.seedGen (fun pk ↦ SM_DT_TCR_oracles P pk)
    (fun pk ↦ forwardsUnif_ofLift_add _) (fun _ ↦ (([], []) : SM_DT_TCR_State Tweak M))
    (fun _ ↦ adv.choose) (fun pk st ↦ adv.forge st pk)
    (fun pk gs jm ↦ (match gs.1[jm.1]? with
      | none => pure false
      | some tm => pure (decide (jm.2 ≠ tm.2 ∧
          P.th.eval pk tm.1 jm.2 = P.th.eval pk tm.1 tm.2)) : ProbComp Bool))
    (· = true) adv.ρ₀ adv.posSemidef adv.trace_eq_one
  refine (tendsto_nhds_of_eq key ?_).congr fun n ↦ ?_
  · unfold qSM_DT_TCR_AdvantageG qSM_DT_TCR_ExperimentG
    congr 1
    refine bind_congr fun pk ↦ bind_congr fun r ↦ bind_congr fun jm ↦ ?_
    cases r.2.1[jm.1]? <;> simp
  · rw [SM_DT_TCR_Advantage, ← prob_eq_evalDist_true]
    congr 1
    unfold SM_DT_TCR_Experiment
    refine bind_congr fun pk ↦ bind_congr fun r ↦ ?_
    obtain ⟨⟨st, ρ'⟩, qs, tw⟩ := r
    refine bind_congr fun jm ↦ ?_
    obtain ⟨j, m⟩ := jm
    dsimp only
    cases qs[j]? with
    | none => rfl
    | some tm => rfl

/-- **Well-posedness.**  A bound valid for all classical SM-DT-TCR adversaries holds for every
general quantum SM-DT-TCR adversary. -/
theorem qSM_DT_TCR_AdvantageG_le_of_forall [DecidableEq Tweak] [DecidableEq M] [DecidableEq Y]
    {P : SM_DT_TCR_Problem ι PkSeed Tweak M Y} (adv : QSM_DT_TCR_AdversaryG W P) (ε : ℝ≥0∞)
    (h : ∀ A : SM_DT_TCR_Adversary P, SM_DT_TCR_Advantage A ≤ ε) :
    qSM_DT_TCR_AdvantageG adv ≤ ε :=
  le_of_tendsto' (tendsto_SM_DT_TCR_AdvantageG bornApprox_sampN adv) fun _ ↦ h _

end smtcr

/-! ## SM-DT-PRE -/

section smpre

open TweakableHash

variable {ι PkSeed Tweak M M' Y : Type} {samp : ℕ → Sampler W}

/-- The classical approximant of a general quantum SM-DT-PRE adversary. -/
noncomputable def QSM_DT_PRE_AdversaryG.toClassicalWith (s : Sampler W)
    {P : SM_DT_PRE_Problem ι PkSeed Tweak M M' Y} (adv : QSM_DT_PRE_AdversaryG W P) :
    SM_DT_PRE_Adversary P where
  State := adv.State × Matrix W W ℂ
  choose := toProbCompStWith s adv.choose adv.ρ₀
  invert st pk := toProbCompCWith s (adv.invert st.1 pk) st.2

/-- **The general quantum SM-DT-PRE advantage is the limit of the classical SM-DT-PRE advantages
of the classical approximants.** -/
theorem tendsto_SM_DT_PRE_AdvantageG [DecidableEq Tweak] [DecidableEq Y] [SampleableType M']
    (hs : BornApprox samp) {P : SM_DT_PRE_Problem ι PkSeed Tweak M M' Y}
    (adv : QSM_DT_PRE_AdversaryG W P) :
    Tendsto (fun n ↦ SM_DT_PRE_Advantage (adv.toClassicalWith (samp n))) atTop
      (𝓝 (qSM_DT_PRE_AdvantageG adv)) := by
  have key := tendsto_twoPhaseG hs P.th.seedGen (fun pk ↦ SM_DT_PRE_oracles P pk)
    (fun pk ↦ forwardsUnif_ofLift_add _) (fun _ ↦ (([], []) : SM_DT_PRE_State Tweak M'))
    (fun _ ↦ adv.choose) (fun pk st ↦ adv.invert st pk)
    (fun pk gs jm ↦ (match gs.1[jm.1]? with
      | none => pure false
      | some tx => pure (decide
          (P.th.eval pk tx.1 (P.emb jm.2) = P.th.eval pk tx.1 (P.emb tx.2))) : ProbComp Bool))
    (· = true) adv.ρ₀ adv.posSemidef adv.trace_eq_one
  refine (tendsto_nhds_of_eq key rfl).congr fun n ↦ ?_
  rw [SM_DT_PRE_Advantage, ← prob_eq_evalDist_true]
  congr 1
  unfold SM_DT_PRE_Experiment
  refine bind_congr fun pk ↦ bind_congr fun r ↦ ?_
  obtain ⟨⟨st, ρ'⟩, qs, tw⟩ := r
  refine bind_congr fun jm ↦ ?_
  obtain ⟨j, m⟩ := jm
  dsimp only
  cases qs[j]? with
  | none => rfl
  | some tm => rfl

theorem qSM_DT_PRE_AdvantageG_le_of_forall [DecidableEq Tweak] [DecidableEq Y]
    [SampleableType M'] {P : SM_DT_PRE_Problem ι PkSeed Tweak M M' Y}
    (adv : QSM_DT_PRE_AdversaryG W P) (ε : ℝ≥0∞)
    (h : ∀ A : SM_DT_PRE_Adversary P, SM_DT_PRE_Advantage A ≤ ε) :
    qSM_DT_PRE_AdvantageG adv ≤ ε :=
  le_of_tendsto' (tendsto_SM_DT_PRE_AdvantageG bornApprox_sampN adv) fun _ ↦ h _

end smpre

/-! ## SM-DT-UD -/

section smud

open TweakableHash

variable {ι PkSeed Tweak M M' Y : Type} {samp : ℕ → Sampler W}

/-- The classical approximant of a general quantum SM-DT-UD adversary. -/
noncomputable def QSM_DT_UD_AdversaryG.toClassicalWith (s : Sampler W)
    {P : SM_DT_UD_Problem ι PkSeed Tweak M M' Y} (adv : QSM_DT_UD_AdversaryG W P) :
    SM_DT_UD_Adversary P where
  State := adv.State × Matrix W W ℂ
  pick := toProbCompStWith s adv.pick adv.ρ₀
  distinguish st pk := toProbCompCWith s (adv.distinguish st.1 pk) st.2

theorem tendsto_SM_DT_UD_ExperimentG [DecidableEq Tweak] (hs : BornApprox samp)
    (world : SM_DT_UD_World) {P : SM_DT_UD_Problem ι PkSeed Tweak M M' Y}
    (adv : QSM_DT_UD_AdversaryG W P) :
    Tendsto (fun n ↦ 𝒟[SM_DT_UD_Experiment world (adv.toClassicalWith (samp n))] {true}) atTop
      (𝓝 (qWeight (· = true) (qSM_DT_UD_ExperimentG world adv) adv.ρ₀)) := by
  have key := tendsto_twoPhaseG hs P.th.seedGen (fun pk ↦ SM_DT_UD_oracles world P pk)
    (fun pk ↦ forwardsUnif_ofLift_add _) (fun _ ↦ (([], []) : SM_DT_UD_State Tweak))
    (fun _ ↦ adv.pick) (fun pk st ↦ adv.distinguish st pk)
    (fun _ _ b ↦ (pure b : ProbComp Bool))
    (· = true) adv.ρ₀ adv.posSemidef adv.trace_eq_one
  refine (tendsto_nhds_of_eq key ?_).congr fun n ↦ ?_
  · unfold qSM_DT_UD_ExperimentG
    simp only [liftU_pure, bind_pure]
  · rw [← prob_eq_evalDist_true]
    congr 1
    unfold SM_DT_UD_Experiment
    simp only [bind_pure]
    rfl

/-- **The general quantum SM-DT-UD advantage is the limit of the classical SM-DT-UD advantages of
the classical approximants.** -/
theorem tendsto_SM_DT_UD_AdvantageG [DecidableEq Tweak] (hs : BornApprox samp)
    {P : SM_DT_UD_Problem ι PkSeed Tweak M M' Y} (adv : QSM_DT_UD_AdversaryG W P) :
    Tendsto (fun n ↦ SM_DT_UD_Advantage (adv.toClassicalWith (samp n))) atTop
      (𝓝 (qSM_DT_UD_AdvantageG adv)) :=
  tendsto_absDiff (tendsto_SM_DT_UD_ExperimentG hs .real adv)
    (tendsto_SM_DT_UD_ExperimentG hs .ideal adv) (qWeight_ne_top _ _ adv.posSemidef)
    (qWeight_ne_top _ _ adv.posSemidef)

theorem qSM_DT_UD_AdvantageG_le_of_forall [DecidableEq Tweak]
    {P : SM_DT_UD_Problem ι PkSeed Tweak M M' Y} (adv : QSM_DT_UD_AdversaryG W P) (ε : ℝ≥0∞)
    (h : ∀ A : SM_DT_UD_Adversary P, SM_DT_UD_Advantage A ≤ ε) :
    qSM_DT_UD_AdvantageG adv ≤ ε :=
  le_of_tendsto' (tendsto_SM_DT_UD_AdvantageG bornApprox_sampN adv) fun _ ↦ h _

end smud

/-! ## Source-final-validity SM-DT-TCR -/

section tcrfv

open TweakableHash

variable {ι PkSeed Tweak M Y : Type} {samp : ℕ → Sampler W}

/-- The classical approximant of a general quantum source-final-validity SM-DT-TCR adversary. -/
noncomputable def QTcrFV_AdversaryG.toClassicalWith (s : Sampler W)
    {P : SM_DT_TCR_SourceFinalValidity.Problem ι PkSeed Tweak M Y}
    (adv : QTcrFV_AdversaryG W P) : SM_DT_TCR_SourceFinalValidity.Adversary P where
  State := adv.State × Matrix W W ℂ
  choose := toProbCompStWith s adv.choose adv.ρ₀
  forge st pk := toProbCompCWith s (adv.forge st.1 pk) st.2

/-- **General quantum = limit of classical for source-final-validity SM-DT-TCR.** -/
theorem tendsto_tcrFV_advantageG [DecidableEq Tweak] [DecidableEq M] [DecidableEq Y]
    (hs : BornApprox samp) {P : SM_DT_TCR_SourceFinalValidity.Problem ι PkSeed Tweak M Y}
    (adv : QTcrFV_AdversaryG W P) :
    Tendsto (fun n ↦ SM_DT_TCR_SourceFinalValidity.advantage (adv.toClassicalWith (samp n)))
      atTop (𝓝 (qTcrFV_AdvantageG adv)) := by
  have key := tendsto_twoPhaseG hs P.th.seedGen
    (fun pk ↦ SM_DT_TCR_SourceFinalValidity.oracles P pk)
    (fun pk ↦ forwardsUnif_ofLift_add _)
    (fun _ ↦ (.initial : SM_DT_TCR_SourceFinalValidity.State Tweak M))
    (fun _ ↦ adv.choose) (fun pk st ↦ adv.forge st pk)
    (fun pk gs jm ↦ (match gs.challenges[jm.1]? with
      | none => pure false
      | some tm => pure (gs.valid && decide
          (jm.2 ≠ tm.2 ∧ P.th.eval pk tm.1 jm.2 = P.th.eval pk tm.1 tm.2)) : ProbComp Bool))
    (· = true) adv.ρ₀ adv.posSemidef adv.trace_eq_one
  refine (tendsto_nhds_of_eq key rfl).congr fun n ↦ ?_
  rw [SM_DT_TCR_SourceFinalValidity.advantage, ← prob_eq_evalDist_true]
  congr 1
  unfold SM_DT_TCR_SourceFinalValidity.experiment
  refine bind_congr fun pk ↦ bind_congr fun r ↦ ?_
  obtain ⟨⟨st, ρ'⟩, gs⟩ := r
  refine bind_congr fun jm ↦ ?_
  obtain ⟨j, m⟩ := jm
  dsimp only
  cases gs.challenges[j]? with
  | none => rfl
  | some tm => rfl

theorem qTcrFV_AdvantageG_le_of_forall [DecidableEq Tweak] [DecidableEq M] [DecidableEq Y]
    {P : SM_DT_TCR_SourceFinalValidity.Problem ι PkSeed Tweak M Y}
    (adv : QTcrFV_AdversaryG W P) (ε : ℝ≥0∞)
    (h : ∀ A : SM_DT_TCR_SourceFinalValidity.Adversary P,
      SM_DT_TCR_SourceFinalValidity.advantage A ≤ ε) :
    qTcrFV_AdvantageG adv ≤ ε :=
  le_of_tendsto' (tendsto_tcrFV_advantageG bornApprox_sampN adv) fun _ ↦ h _

end tcrfv

/-! ## Source-final-validity SM-DT-DSPR -/

section dsprfv

open TweakableHash

variable {ι PkSeed Tweak M Y : Type} {samp : ℕ → Sampler W}

/-- The classical approximant of a general quantum source-final-validity SM-DT-DSPR adversary. -/
noncomputable def QDsprFV_AdversaryG.toClassicalWith (s : Sampler W)
    {P : SM_DT_DSPR_SourceFinalValidity.Problem ι PkSeed Tweak M Y}
    (adv : QDsprFV_AdversaryG W P) : SM_DT_DSPR_SourceFinalValidity.Adversary P where
  State := adv.State × Matrix W W ℂ
  choose := toProbCompStWith s adv.choose adv.ρ₀
  guess st pk := toProbCompCWith s (adv.guess st.1 pk) st.2

theorem tendsto_qDsprFV_SuccessG [Fintype M] [DecidableEq Tweak] [DecidableEq M] [DecidableEq Y]
    (hs : BornApprox samp) {P : SM_DT_DSPR_SourceFinalValidity.Problem ι PkSeed Tweak M Y}
    (adv : QDsprFV_AdversaryG W P) :
    Tendsto (fun n ↦ SM_DT_DSPR_SourceFinalValidity.Success (adv.toClassicalWith (samp n)))
      atTop (𝓝 (qDsprFV_SuccessG adv)) := by
  have key := tendsto_twoPhaseG hs P.th.seedGen
    (fun pk ↦ SM_DT_DSPR_SourceFinalValidity.oracles P pk)
    (fun pk ↦ forwardsUnif_ofLift_add _)
    (fun _ ↦ (.initial : SM_DT_DSPR_SourceFinalValidity.State Tweak M))
    (fun _ ↦ adv.choose) (fun pk st ↦ adv.guess st pk)
    (fun pk gs jb ↦ (match gs.challenges[jb.1]? with
      | none => pure false
      | some tm => pure (gs.valid && decide
          (TweakableHash.SecondPreimageExists P.th pk tm.1 tm.2 ↔ jb.2 = true)) :
        ProbComp Bool))
    (· = true) adv.ρ₀ adv.posSemidef adv.trace_eq_one
  refine (tendsto_nhds_of_eq key rfl).congr fun n ↦ ?_
  rw [SM_DT_DSPR_SourceFinalValidity.Success, ← prob_eq_evalDist_true]
  congr 1
  unfold SM_DT_DSPR_SourceFinalValidity.experiment
  refine bind_congr fun pk ↦ bind_congr fun r ↦ ?_
  obtain ⟨⟨st, ρ'⟩, gs⟩ := r
  refine bind_congr fun jb ↦ ?_
  obtain ⟨j, b⟩ := jb
  dsimp only
  cases gs.challenges[j]? with
  | none => rfl
  | some tm => rfl

theorem tendsto_qDsprFV_SPProbabilityG [Fintype M] [DecidableEq Tweak] [DecidableEq M]
    [DecidableEq Y] (hs : BornApprox samp)
    {P : SM_DT_DSPR_SourceFinalValidity.Problem ι PkSeed Tweak M Y}
    (adv : QDsprFV_AdversaryG W P) :
    Tendsto (fun n ↦ SM_DT_DSPR_SourceFinalValidity.SPProbability
        (adv.toClassicalWith (samp n))) atTop (𝓝 (qDsprFV_SPProbabilityG adv)) := by
  have key := tendsto_twoPhaseG hs P.th.seedGen
    (fun pk ↦ SM_DT_DSPR_SourceFinalValidity.oracles P pk)
    (fun pk ↦ forwardsUnif_ofLift_add _)
    (fun _ ↦ (.initial : SM_DT_DSPR_SourceFinalValidity.State Tweak M))
    (fun _ ↦ adv.choose) (fun pk st ↦ adv.guess st pk)
    (fun pk gs jb ↦ (match gs.challenges[jb.1]? with
      | none => pure false
      | some tm => pure (gs.valid && decide
          (TweakableHash.SecondPreimageExists P.th pk tm.1 tm.2)) : ProbComp Bool))
    (· = true) adv.ρ₀ adv.posSemidef adv.trace_eq_one
  refine (tendsto_nhds_of_eq key rfl).congr fun n ↦ ?_
  rw [SM_DT_DSPR_SourceFinalValidity.SPProbability, ← prob_eq_evalDist_true]
  congr 1
  unfold SM_DT_DSPR_SourceFinalValidity.spExperiment
  refine bind_congr fun pk ↦ bind_congr fun r ↦ ?_
  obtain ⟨⟨st, ρ'⟩, gs⟩ := r
  refine bind_congr fun jb ↦ ?_
  obtain ⟨j, b⟩ := jb
  dsimp only
  cases gs.challenges[j]? with
  | none => rfl
  | some tm => rfl

/-- **General quantum = limit of classical for source-final-validity SM-DT-DSPR** (truncated
difference `Pr[DSPR] - Pr[SPprob]`). -/
theorem tendsto_dsprFV_advantageG [Fintype M] [DecidableEq Tweak] [DecidableEq M] [DecidableEq Y]
    (hs : BornApprox samp) {P : SM_DT_DSPR_SourceFinalValidity.Problem ι PkSeed Tweak M Y}
    (adv : QDsprFV_AdversaryG W P) :
    Tendsto (fun n ↦ SM_DT_DSPR_SourceFinalValidity.advantage (adv.toClassicalWith (samp n)))
      atTop (𝓝 (qDsprFV_AdvantageG adv)) :=
  ENNReal.Tendsto.sub (tendsto_qDsprFV_SuccessG hs adv) (tendsto_qDsprFV_SPProbabilityG hs adv)
    (Or.inl (qWeight_ne_top _ _ adv.posSemidef))

theorem qDsprFV_AdvantageG_le_of_forall [Fintype M] [DecidableEq Tweak] [DecidableEq M]
    [DecidableEq Y] {P : SM_DT_DSPR_SourceFinalValidity.Problem ι PkSeed Tweak M Y}
    (adv : QDsprFV_AdversaryG W P) (ε : ℝ≥0∞)
    (h : ∀ A : SM_DT_DSPR_SourceFinalValidity.Adversary P,
      SM_DT_DSPR_SourceFinalValidity.advantage A ≤ ε) :
    qDsprFV_AdvantageG adv ≤ ε :=
  le_of_tendsto' (tendsto_dsprFV_advantageG bornApprox_sampN adv) fun _ ↦ h _

end dsprfv

end PQ.Interactive

open PQ.Interactive in
#print axioms toProbCompCStWith_close
open PQ.Interactive in
#print axioms tendsto_bind_closedSt
open PQ.Interactive in
#print axioms tendsto_close_bindSt
open PQ.Interactive in
#print axioms tendsto_twoPhaseG
open PQ.Interactive in
#print axioms tendsto_SM_DT_TCR_AdvantageG
open PQ.Interactive in
#print axioms tendsto_SM_DT_PRE_AdvantageG
open PQ.Interactive in
#print axioms tendsto_SM_DT_UD_AdvantageG
open PQ.Interactive in
#print axioms tendsto_tcrFV_advantageG
open PQ.Interactive in
#print axioms tendsto_dsprFV_advantageG
open PQ.Interactive in
#print axioms qSM_DT_TCR_AdvantageG_le_of_forall
open PQ.Interactive in
#print axioms qDsprFV_AdvantageG_le_of_forall
