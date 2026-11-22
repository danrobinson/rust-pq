import Ideal.Core.HPBasic
import VCVio.OracleComp.EvalDist.Sum
import VCVio.OracleComp.SimSemantics.StateT.PreservesInv

/-!
# Generic engine for the direct ideal-model proof

* `ex mx f`: the expectation of `f` under the output distribution of `mx` (a `tsum`; VCVio's
  `wp` lives in `ProgramLogic`, which is not built in this workspace), with `ex_bind`,
  `ex_mono_of_support`, `prEvent_eq_ex`.
* `hz P Ψ s` (`= 1` if the hazard `P` holds of `s`, else the pending charge `Ψ s`) and
  `ex_hz_le_of_step`: a **pending-charge supermartingale bound**.  If every step of a stateful
  handler, out of a state where the hazard `P` fails, has expected `hz` at most `Ψ s` plus a
  per-step charge (`ε` on the charged queries, `0` on the others), then a computation with at
  most `n` charged queries ends with expected `hz` at most `hz s + n ε`.  Unlike
  `Ideal.prEvent_bad_le_of_step`, a step may *defer* its charge: it raises `Ψ` (a candidate that
  fires only when a value sampled LATER hits it), and a later sample that resolves the candidate
  lowers `Ψ` by the probability with which it fires.  So a query is charged once, whichever order
  the two events happen in.
* `prT_le_untilBad`: identical until bad for two handlers that agree, up to a projection of the
  state, on every step that does not fire a monotone bad predicate.
* `prEvent_exists_list_le`: a union bound over a list of targets.
* `ex_hz_fresh_le`: the step bound for a single fresh sample.
-/

open OracleComp OracleSpec ENNReal

namespace Ideal.Direct

/-! ## Expectations -/

section Ex

variable {α β : Type}

/-- The expectation of `f` under the output distribution of `mx`. -/
noncomputable def ex (mx : ProbComp α) (f : α → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' x, Pr{let z ← mx}[z = x] * f x

open Classical in
/-- `1` if `P` holds, else `0`. -/
noncomputable def propInd (P : Prop) : ℝ≥0∞ := if P then 1 else 0

theorem propInd_eq_one_iff {P : Prop} : propInd P = 1 ↔ P := by
  unfold propInd; split_ifs with h <;> simp [h]

theorem propInd_eq_zero_iff {P : Prop} : propInd P = 0 ↔ ¬ P := by
  unfold propInd; split_ifs with h <;> simp [h]

theorem propInd_mono {P Q : Prop} (h : P → Q) : propInd P ≤ propInd Q := by
  unfold propInd; split_ifs with h1 h2 <;> simp_all

theorem ex_pure (a : α) (f : α → ℝ≥0∞) : ex (pure a) f = f a := by
  classical
  unfold ex
  rw [tsum_eq_single a fun x hx => by
    rw [prEvent_pure, if_neg (Ne.symm hx : ¬ a = x), zero_mul]]
  rw [prEvent_pure, if_pos rfl, one_mul]

theorem ex_bind (mx : ProbComp α) (g : α → ProbComp β) (f : β → ℝ≥0∞) :
    ex (mx >>= g) f = ex mx fun x => ex (g x) f := by
  unfold ex
  have hb : ∀ y, Pr{let z ← mx >>= g}[z = y] = ∑' x, Pr{let z ← mx}[z = x] *
      Pr{let z ← g x}[z = y] := fun y => prEvent_bind_eq_tsum mx g (· = y)
  simp_rw [hb, ← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun x => ?_
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr fun y => ?_
  ring

theorem ex_map (h : α → β) (mx : ProbComp α) (f : β → ℝ≥0∞) :
    ex (h <$> mx) f = ex mx (f ∘ h) := by
  rw [map_eq_bind_pure_comp, ex_bind]
  simp only [Function.comp_apply, ex_pure]
  rfl

theorem ex_const (mx : ProbComp α) (c : ℝ≥0∞) : ex mx (fun _ => c) = c := by
  unfold ex
  rw [ENNReal.tsum_mul_right, tsum_prEvent_eq_one, one_mul]

theorem ex_add (mx : ProbComp α) (f g : α → ℝ≥0∞) :
    ex mx (fun x => f x + g x) = ex mx f + ex mx g := by
  unfold ex
  simp_rw [mul_add]
  exact tsum_add

theorem ex_mono (mx : ProbComp α) {f g : α → ℝ≥0∞} (h : ∀ x, f x ≤ g x) : ex mx f ≤ ex mx g :=
  tsum_le_tsum fun x => by gcongr; exact h x

theorem ex_mono_of_support (mx : ProbComp α) {f g : α → ℝ≥0∞}
    (h : ∀ x ∈ support mx, f x ≤ g x) : ex mx f ≤ ex mx g := by
  refine tsum_le_tsum fun x => ?_
  by_cases hx : x ∈ support mx
  · gcongr; exact h x hx
  · rw [prEvent_eq_zero_of_forall_mem_support mx _ fun y hy (hyx : y = x) => hx (hyx ▸ hy)]
    simp

theorem prEvent_eq_ex (mx : ProbComp α) (p : α → Prop) :
    Pr{let x ← mx}[p x] = ex mx fun x => propInd (p x) := by
  classical
  rw [prEvent_eq_tsum_ite]
  unfold ex propInd
  refine tsum_congr fun x => ?_
  by_cases hx : p x <;> simp [hx]

end Ex

/-! ## The pending-charge supermartingale -/

section Engine

open Classical in
/-- `1` if the hazard holds, else the pending charge. -/
noncomputable def hz {σ : Type} (P : σ → Prop) (Ψ : σ → ℝ≥0∞) (s : σ) : ℝ≥0∞ :=
  if P s then 1 else Ψ s

theorem hz_of_P {σ : Type} {P : σ → Prop} {Ψ : σ → ℝ≥0∞} {s : σ} (h : P s) : hz P Ψ s = 1 := by
  simp [hz, h]

theorem hz_of_not_P {σ : Type} {P : σ → Prop} {Ψ : σ → ℝ≥0∞} {s : σ} (h : ¬ P s) :
    hz P Ψ s = Ψ s := by
  simp [hz, h]

theorem propInd_le_hz {σ : Type} (P : σ → Prop) (Ψ : σ → ℝ≥0∞) (s : σ) :
    propInd (P s) ≤ hz P Ψ s := by
  by_cases h : P s
  · rw [hz_of_P h, propInd_eq_one_iff.2 h]
  · rw [propInd_eq_zero_iff.2 h]; exact zero_le

theorem hz_le_propInd_add {σ : Type} (P : σ → Prop) (Ψ : σ → ℝ≥0∞) (s : σ) :
    hz P Ψ s ≤ propInd (P s) + Ψ s := by
  by_cases h : P s
  · rw [hz_of_P h, propInd_eq_one_iff.2 h]; exact le_self_add
  · rw [hz_of_not_P h, propInd_eq_zero_iff.2 h, zero_add]

variable {ι : Type} {spec : OracleSpec ι} {σ α : Type}

/-- **Pending-charge supermartingale bound.** -/
theorem ex_hz_le_of_step (so : QueryImpl spec (StateT σ ProbComp)) (I P : σ → Prop)
    (Ψ : σ → ℝ≥0∞) (p : ι → Prop) [DecidablePred p] (ε : ℝ≥0∞)
    (hI : ∀ t s, I s → ∀ z ∈ support ((so t).run s), I z.2)
    (habs : ∀ t s, I s → P s → ∀ z ∈ support ((so t).run s), P z.2)
    (hstep : ∀ t s, I s → ¬ P s →
      ex ((so t).run s) (fun z => hz P Ψ z.2) ≤ Ψ s + (if p t then ε else 0))
    (oa : OracleComp spec α) (n : ℕ) (hn : IsQueryBoundP oa p n) (s : σ) (hs : I s) :
    ex ((simulateQ so oa).run s) (fun z => hz P Ψ z.2) ≤ hz P Ψ s + n * ε := by
  induction oa using OracleComp.inductionOn generalizing n s with
  | pure x =>
    simp only [simulateQ_pure, StateT.run_pure, ex_pure]
    exact le_self_add
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hn
    rw [run_simulateQ_query_bind, ex_bind]
    set n' := if p t then n - 1 else n with hn'
    have hrest : ∀ z ∈ support ((so t).run s),
        ex ((simulateQ so (k z.1)).run z.2) (fun z => hz P Ψ z.2) ≤ hz P Ψ z.2 + n' * ε :=
      fun z hz' => ih z.1 n' (hn.2 z.1) z.2 (hI t s hs z hz')
    have hcount : n' * ε + (if p t then ε else 0) ≤ n * ε := by
      by_cases hpt : p t
      · have hn0 : 0 < n := hn.1.resolve_left (not_not.2 hpt)
        obtain ⟨n'', rfl⟩ : ∃ n'', n = n'' + 1 := ⟨n - 1, by omega⟩
        simp [hn', hpt, add_mul]
      · simp [hn', hpt]
    by_cases hPs : P s
    · refine (ex_mono_of_support _ (g := fun _ => 1 + n' * ε)
        fun z hz' => (hrest z hz').trans ?_).trans ?_
      · exact le_of_eq (congrArg (· + _) (hz_of_P (habs t s hs hPs z hz')))
      · rw [ex_const, hz_of_P hPs]
        exact add_le_add le_rfl (le_trans le_self_add hcount)
    · refine (ex_mono_of_support _ hrest).trans ?_
      rw [ex_add, ex_const]
      calc _ ≤ (Ψ s + (if p t then ε else 0)) + n' * ε := by gcongr; exact hstep t s hs hPs
        _ ≤ hz P Ψ s + n * ε := by
          rw [hz_of_not_P hPs, add_assoc]; gcongr; rw [add_comm]; exact hcount

/-- The probability of the hazard at the end is at most the expected `hz`. -/
theorem prEvent_le_ex_hz (mx : ProbComp α) (P : α → Prop) (Ψ : α → ℝ≥0∞) :
    Pr{let z ← mx}[P z] ≤ ex mx (hz P Ψ) := by
  rw [prEvent_eq_ex]
  exact ex_mono _ fun z => propInd_le_hz P Ψ z

end Engine

/-! ## Identical until bad -/

section UntilBad

variable {ι : Type} {spec : OracleSpec ι} {σ₁ σ₂ α : Type}

/-- **Identical until bad.**  `h₂` runs on a richer state, projected to the state of `h₁` by
`proj`; `bad` is monotone along `h₂`.  If every step of `h₂` out of a non-bad state either surely
ends bad, or agrees with the step of `h₁` after projection, then an event of the `h₁`-run is at
most as likely as the same event or `bad` in the `h₂`-run. -/
theorem prEvent_le_untilBad (h₁ : QueryImpl spec (StateT σ₁ ProbComp))
    (h₂ : QueryImpl spec (StateT σ₂ ProbComp)) (proj : σ₂ → σ₁) (bad : σ₂ → Prop)
    (hmono : ∀ t s, bad s → ∀ z ∈ support ((h₂ t).run s), bad z.2)
    (hagree : ∀ t s, ¬ bad s → (∀ z ∈ support ((h₂ t).run s), bad z.2) ∨
      (fun z => (z.1, proj z.2)) <$> (h₂ t).run s = (h₁ t).run (proj s))
    (E : α × σ₁ → Prop) (oa : OracleComp spec α) (s : σ₂) :
    Pr{let z ← (simulateQ h₁ oa).run (proj s)}[E z] ≤
      Pr{let z ← (simulateQ h₂ oa).run s}[E (z.1, proj z.2) ∨ bad z.2] := by
  classical
  have hpres : ∀ (oa' : OracleComp spec α) (s' : σ₂), bad s' →
      ∀ z ∈ support ((simulateQ h₂ oa').run s'), bad z.2 :=
    fun oa' s' hs' z hz => simulateQ_run_preservesInv h₂ bad
      (fun t s hs z hz => hmono t s hs z hz) oa' s' hs' z hz
  induction oa using OracleComp.inductionOn generalizing s with
  | pure x =>
    simp only [simulateQ_pure, StateT.run_pure]
    rw [prEvent_pure, prEvent_pure]
    by_cases h : E (x, proj s)
    · simp [h]
    · simp only [h, if_false]; exact zero_le
  | query_bind t k ih =>
    by_cases hs : bad s
    · refine (prEvent_le_one _).trans (le_of_eq ?_)
      exact ((OracleComp.prEvent_eq_one_iff _ _).2 fun z hz => .inr (hpres _ s hs z hz)).symm
    · rw [run_simulateQ_query_bind, run_simulateQ_query_bind]
      rcases hagree t s hs with hall | heq
      · refine (prEvent_le_one _).trans (le_of_eq ?_)
        refine ((OracleComp.prEvent_eq_one_iff _ _).2 fun z hz => ?_).symm
        rw [mem_support_bind_iff] at hz
        obtain ⟨y, hy, hz⟩ := hz
        exact .inr (hpres _ _ (hall y hy) z hz)
      · rw [← heq, bind_map_left]
        exact prEvent_bind_mono_of_forall_le_of_support _ _ _ _ _ fun y _ => ih y.1 y.2

end UntilBad

/-! ## Union bound and single fresh samples -/

section Fresh

variable {β γ : Type}

/-- Union bound over a list of targets. -/
theorem prEvent_exists_list_le (mx : ProbComp β) (l : List γ) (p : γ → β → Prop) (δ : ℝ≥0∞)
    (h : ∀ e ∈ l, Pr{let u ← mx}[p e u] ≤ δ) :
    Pr{let u ← mx}[∃ e ∈ l, p e u] ≤ l.length * δ := by
  induction l with
  | nil => simp
  | cons e l ih =>
    refine (prEvent_mono _ _ (fun u => p e u ∨ ∃ e' ∈ l, p e' u) fun u hu => ?_).trans
      ((prEvent_or_le _ _ _).trans ?_)
    · obtain ⟨e', he', hp⟩ := hu
      rcases List.mem_cons.mp he' with rfl | he'
      · exact .inl hp
      · exact .inr ⟨e', he', hp⟩
    · refine (add_le_add (h e (by simp)) (ih fun e' he' => h e' (by simp [he']))).trans
        (le_of_eq ?_)
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
      ring

/-- **A single fresh sample.**  If after the sample `u` the new state fires the hazard only on
an event `F u` of probability at most `D`, and its pending charge is at most `Ψ'`, the expected
`hz` after the sample is at most `D + Ψ'`. -/
theorem ex_hz_fresh_le {σ : Type} (mx : ProbComp β) (upd : β → σ) (P : σ → Prop)
    (Ψ : σ → ℝ≥0∞) (F : β → Prop) (D Ψ' : ℝ≥0∞) (hF : ∀ u, P (upd u) → F u)
    (hD : Pr{let u ← mx}[F u] ≤ D) (hΨ : ∀ u, Ψ (upd u) ≤ Ψ') :
    ex mx (fun u => hz P Ψ (upd u)) ≤ D + Ψ' := by
  refine (ex_mono _ fun u => (hz_le_propInd_add P Ψ (upd u)).trans
    (add_le_add (propInd_mono (hF u)) (hΨ u))).trans ?_
  rw [ex_add, ex_const, ← prEvent_eq_ex]
  exact add_le_add hD le_rfl

end Fresh

end Ideal.Direct

#print axioms Ideal.Direct.ex_hz_le_of_step
#print axioms Ideal.Direct.prEvent_le_untilBad
#print axioms Ideal.Direct.prEvent_exists_list_le
#print axioms Ideal.Direct.ex_hz_fresh_le
