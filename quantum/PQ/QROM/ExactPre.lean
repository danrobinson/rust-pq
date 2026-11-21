import PQ.QROM.ExactTcr
import PQ.QROM.PreGiven

/-!
# The exact SM-DT-PRE game in the QROM

The two-phase, adaptive-target game of VCVio's `TweakableHash.SM_DT_PRE_Experiment`
(`VCVio/CryptoFoundations/HardnessAssumptions/TweakableHash/SMDTPRE.lean`), with the tweakable
hash a uniformly random function `Th : Sd × (Tw × Msg) → Y` and a quantum-query adversary in
both phases.  The general model is described in `PQ/QROM/TwoPhaseGame.lean`.

## Correspondence with `SM_DT_PRE_Experiment`

* `pk ← prob.th.seedGen`: here `P : Sd` uniform.  `prob.th.eval pk t m` is `Th (P, (t, m))`.
* The challenge oracle `SM_DT_PRE_challengeOracle` draws, at each accepted query `t`, a message
  `x ← M'` uniformly and answers `th.eval pk t (emb x)`.  Here the planted messages are drawn up
  front, `xs : Tw → Msg` uniform and independent of `P` and `Th`, and the accepted query `t`
  uses `xs t`.  Since a tweak is accepted at most once this is the same distribution.  The
  planted message type is the message type itself (`M' = M`, `emb = id`).
* `adv.choose`: the interactive adversary `x : IAdv … (Tw ⊕ (Tw × Msg)) (Option Y) Out n A`,
  answered by `preCh cap xs (rowOf Th P)`:
  - `Sum.inl t` (challenge oracle): rejected (`none`, state unchanged) when the cap is reached,
    when `t` occurs in the challenge history or when `t` has been spent on the collection
    oracle; otherwise answered `some (Th (P, (t, xs t)))` and `t` is appended to the challenge
    history.  (VCVio records `(t, x)`; here `x = xs t` is recovered from `xs`.)
  - `Sum.inr (t, m)` (collection oracle): rejected when `t` occurs in the challenge history;
    otherwise answered `some (Th (P, (t, m)))` and recorded.  As for TCR the collection is
    modelled as the same random function at the hidden seed on tweaks disjoint from the target
    tweaks.
* `adv.invert st pk`: `ph2 P u o`, returning `(j, m) : ℕ × Msg`.
* Win (`preWin`): the `j`-th entry `t` of the challenge history exists and
  `Th (P, (t, m)) = Th (P, (t, xs t))`.

## Result

`pre_exact_le`: `Pr[win] ≤ (√((2 q₂ + 1)² (1/|Y| + 1/|Msg|)) + 2 q₁ / √|Sd|)²`.
-/

open MeasureTheory ENNReal Quantum Matrix
open scoped Kronecker ComplexOrder

universe u v w

set_option linter.unusedSectionVars false

namespace PQ.QROM

variable {Sd Tw Msg Y : Type}

/-! ## Games with challenger randomness -/

section Rand

variable [Fintype Sd] [DecidableEq Sd] [Fintype Tw] [DecidableEq Tw] [Fintype Msg]
  [DecidableEq Msg] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
  {L : LocalSig.{u, v}} {Out : QReg → Type w} {A : QReg} {Req Resp St Res Ω : Type} [Fintype Ω]
  {I : L.Interp} {ρ : SubState A} {ch : Ω → (Tw × Msg → Y) → Req → St → Resp × St} {s₀ : St}
  {n : ℕ} {x : IAdv L (qrom2Spec (Dom Sd Tw Msg) Y) Req Resp Out n A}
  {ph2 : Sd → ∀ u, Out u → QuantumComp L (qrom2Spec (Dom Sd Tw Msg) Y) (fun _ ↦ Res) u}
  {win : Ω → (Tw × Msg → Y) → Res → St → Prop} {q₁ q₂ : ℕ}

/-- **From leaves to the hybrid game, with challenger randomness `ω`.** -/
theorem avg_twoPhaseHyb_le_of_leaf {ε : ℝ≥0∞} (hx : IAdv.IsQueryBound n x (firstBudget q₁))
    (hleaf : ∀ (P : Sd) (F : Dom Sd Tw Msg → Y) (p : Σ u, Out u × St),
      (avg fun ω : Ω ↦ avg fun R : Tw × Msg → Y ↦
        leafProb (twoRuntime (ports F (patchRow F P R))) I (ph2 P p.1 p.2.1)
          (postOf I ρ (ch ω) s₀ n x F R p) (fun l ↦ win ω R l.2 p.2.2)) ≤
      ε * avg fun ω : Ω ↦ avg fun R : Tw × Msg → Y ↦
        ENNReal.ofReal (postOf I ρ (ch ω) s₀ n x F R p).trace.re) :
    (avg fun ω : Ω ↦ twoPhaseHyb I ρ (ch ω) s₀ n x ph2 (win ω)) ≤ ε := by
  unfold twoPhaseHyb
  rw [avg_comm]
  refine avg_le fun P ↦ ?_
  rw [avg_comm]
  refine avg_le fun F ↦ ?_
  simp only [hybProb_eq_tsum hx]
  simp only [avg_tsum]
  refine (tsum_le_tsum (hleaf P F)).trans ?_
  rw [ENNReal.tsum_mul_left]
  simp only [← avg_tsum]
  refine (mul_le_mul' le_rfl (avg_le (c := 1) fun ω ↦ avg_le fun R ↦ ?_)).trans (mul_one _).le
  exact (tsum_leaf_le (R := twoRuntime fun _ ↦ F) (I := I)
    (phase1 (ch ω R) s₀ n x) (joint_posSemidef ρ)).trans (ofReal_trace_joint_le_one ρ)

/-- **Two-phase games with challenger randomness, from leaf bounds**:
`√Pr[win] ≤ √ε + 2 q₁ / √|Sd|`. -/
theorem avg_twoPhaseExp_sqrt_le_of_leaf {ε : ℝ≥0∞}
    (hx : IAdv.IsQueryBound n x (firstBudget q₁))
    (h2 : ∀ P u o, (ph2 P u o).IsQueryBound (secondBudget q₂))
    (hleaf : ∀ (P : Sd) (F : Dom Sd Tw Msg → Y) (p : Σ u, Out u × St),
      (avg fun ω : Ω ↦ avg fun R : Tw × Msg → Y ↦
        leafProb (twoRuntime (ports F (patchRow F P R))) I (ph2 P p.1 p.2.1)
          (postOf I ρ (ch ω) s₀ n x F R p) (fun l ↦ win ω R l.2 p.2.2)) ≤
      ε * avg fun ω : Ω ↦ avg fun R : Tw × Msg → Y ↦
        ENNReal.ofReal (postOf I ρ (ch ω) s₀ n x F R p).trace.re) :
    (avg fun ω : Ω ↦ twoPhaseExp I ρ (ch ω) s₀ n x ph2 (win ω)) ^ (2⁻¹ : ℝ) ≤
      ε ^ (2⁻¹ : ℝ) + 2 * q₁ * ((Fintype.card Sd : ℝ≥0∞)⁻¹) ^ (2⁻¹ : ℝ) := by
  have h := sqrt_avg_le (fun ω : Ω ↦ twoPhaseExp I ρ (ch ω) s₀ n x ph2 (win ω))
    (fun ω ↦ twoPhaseHyb I ρ (ch ω) s₀ n x ph2 (win ω))
    (fun _ ↦ (2 * (q₁ : ℝ≥0∞) * ((Fintype.card Sd : ℝ≥0∞)⁻¹) ^ (2⁻¹ : ℝ)) ^ 2)
    (fun ω ↦ by rw [sqrt_sq]; exact seed_hiding hx h2)
  refine h.trans (add_le_add (sqrt_le_sqrt (avg_twoPhaseHyb_le_of_leaf hx hleaf)) ?_)
  refine (sqrt_le_sqrt (avg_le fun _ ↦ le_rfl)).trans ?_
  rw [sqrt_sq]

end Rand

/-! ## The challenger -/

/-- The state of the SM-DT-PRE game: the challenge history (accepted target tweaks, in issue
order) and the collection history. -/
structure PreState (Tw Msg : Type) where
  /-- The accepted target tweaks, in issue order. -/
  chal : List Tw
  /-- The accepted collection queries. -/
  coll : List (Tw × Msg)
  /-- No collection query is on a target tweak. -/
  disj : ∀ p ∈ coll, p.1 ∉ chal

/-- The empty histories. -/
def preInit : PreState Tw Msg := ⟨[], [], fun _ h ↦ by simp at h⟩

/-- The two classical oracles of SM-DT-PRE with answer table `y` for the challenge oracle and
answers `a` for the collection oracle. -/
def preChT [DecidableEq Tw] (cap : ℕ) (y : Tw → Y) (a : Tw × Msg → Y) :
    Tw ⊕ (Tw × Msg) → PreState Tw Msg → Option Y × PreState Tw Msg
  | .inl t, s =>
    if h : cap ≤ s.chal.length ∨ t ∈ s.chal ∨ t ∈ s.coll.map Prod.fst then (none, s)
    else (some (y t), ⟨s.chal ++ [t], s.coll, by
        intro p hp hmem
        rw [List.mem_append, List.mem_singleton] at hmem
        rcases hmem with hmem | hmem
        · exact s.disj p hp hmem
        · exact h (Or.inr (Or.inr (hmem ▸ List.mem_map.2 ⟨p, hp, rfl⟩)))⟩)
  | .inr tm, s =>
    if h : tm.1 ∈ s.chal then (none, s)
    else (some (a tm), ⟨s.chal, s.coll ++ [tm], by
        intro p hp
        rw [List.mem_append, List.mem_singleton] at hp
        rcases hp with hp | hp
        · exact s.disj p hp
        · rw [hp]; exact h⟩)

/-- The two classical oracles of SM-DT-PRE for the planted messages `xs` and the row `a` of the
hash at the seed. -/
def preCh [DecidableEq Tw] (cap : ℕ) (xs : Tw → Msg) (a : Tw × Msg → Y) :
    Tw ⊕ (Tw × Msg) → PreState Tw Msg → Option Y × PreState Tw Msg :=
  preChT cap (fun t ↦ a (t, xs t)) a

/-- The winning condition of SM-DT-PRE: the result `(j, m)` names a recorded target tweak `t`
and a message with the image of the planted message of `t` under the row `a`. -/
def preWin (xs : Tw → Msg) (a : Tw × Msg → Y) (r : ℕ × Msg) (s : PreState Tw Msg) : Prop :=
  ∃ t, s.chal[r.1]? = some t ∧ a (t, r.2) = a (t, xs t)

section Challenger

variable [DecidableEq Tw]

/-- `t` extends `s`. -/
def PreState.Ext (s t : PreState Tw Msg) : Prop := s.chal <+: t.chal ∧ s.coll <+: t.coll

theorem preChT_ext (cap : ℕ) (y : Tw → Y) (a : Tw × Msg → Y) (req : Tw ⊕ (Tw × Msg))
    (s t : PreState Tw Msg) (h : (preChT cap y a req s).2.Ext t) : s.Ext t := by
  cases req with
  | inl tw =>
    simp only [preChT] at h
    split_ifs at h with hc
    · exact h
    · exact ⟨(List.prefix_append _ _).trans h.1, h.2⟩
  | inr tm =>
    simp only [preChT] at h
    split_ifs at h with hc
    · exact h
    · exact ⟨h.1, (List.prefix_append _ _).trans h.2⟩

theorem preChT_loc (cap : ℕ) (y y' : Tw → Y) (a a' : Tw × Msg → Y) (t : PreState Tw Msg)
    (hy : ∀ tw ∈ t.chal, y tw = y' tw) (ha : ∀ tm ∈ t.coll, a tm = a' tm)
    (req : Tw ⊕ (Tw × Msg)) (s : PreState Tw Msg) :
    preChT cap y a req s = preChT cap y' a' req s ∨
      (¬ (preChT cap y a req s).2.Ext t ∧ ¬ (preChT cap y' a' req s).2.Ext t) := by
  cases req with
  | inl tw =>
    simp only [preChT]
    split_ifs with hc
    · exact Or.inl rfl
    · by_cases he : y tw = y' tw
      · left
        rw [he]
      · right
        have hn : ¬ (s.chal ++ [tw]) <+: t.chal := fun hp ↦
          he (hy tw (hp.subset (by simp)))
        exact ⟨fun h ↦ hn h.1, fun h ↦ hn h.1⟩
  | inr tm =>
    simp only [preChT]
    split_ifs with hc
    · exact Or.inl rfl
    · by_cases he : a tm = a' tm
      · left
        rw [he]
      · right
        have hn : ¬ (s.coll ++ [tm]) <+: t.coll := fun hp ↦
          he (ha tm (hp.subset (by simp)))
        exact ⟨fun h ↦ hn h.2, fun h ↦ hn h.2⟩

end Challenger

/-! ## The experiment -/

section Exp

variable [Fintype Sd] [DecidableEq Sd] [Fintype Tw] [DecidableEq Tw] [Fintype Msg]
  [DecidableEq Msg] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
  {L : LocalSig.{u, v}} {Out : QReg → Type w} {A : QReg}

/-- **The exact SM-DT-PRE experiment in the QROM** (target cap `cap`): the probability, over
the uniform planted messages `xs`, the uniform seed `P`, the uniform hash `Th` and the run, that
the two-phase quantum adversary `(x, ph2)` started on `ρ` wins. -/
noncomputable def preExp (I : L.Interp) (ρ : SubState A) (cap n : ℕ)
    (x : IAdv L (qrom2Spec (Dom Sd Tw Msg) Y) (Tw ⊕ (Tw × Msg)) (Option Y) Out n A)
    (ph2 : Sd → ∀ u, Out u →
      QuantumComp L (qrom2Spec (Dom Sd Tw Msg) Y) (fun _ ↦ ℕ × Msg) u) : ℝ≥0∞ :=
  avg fun xs : Tw → Msg ↦ twoPhaseExp I ρ (preCh cap xs) preInit n x ph2 (preWin xs)

variable {I : L.Interp} {ρ : SubState A} {cap n q₁ q₂ : ℕ}
  {x : IAdv L (qrom2Spec (Dom Sd Tw Msg) Y) (Tw ⊕ (Tw × Msg)) (Option Y) Out n A}
  {ph2 : Sd → ∀ u, Out u → QuantumComp L (qrom2Spec (Dom Sd Tw Msg) Y) (fun _ ↦ ℕ × Msg) u}

/-- The post-state of the leaf `p` of phase 1 run with quantum access to `F`, with answer table
`ya.1` for the challenge oracle and answers `ya.2` for the collection oracle. -/
noncomputable def prePost (I : L.Interp) (ρ : SubState A) (cap n : ℕ)
    (x : IAdv L (qrom2Spec (Dom Sd Tw Msg) Y) (Tw ⊕ (Tw × Msg)) (Option Y) Out n A)
    (F : Dom Sd Tw Msg → Y) (p : Σ u, Out u × PreState Tw Msg)
    (ya : (Tw → Y) × (Tw × Msg → Y)) : Matrix (p.1 × Unit) (p.1 × Unit) ℂ :=
  ((twoRuntime fun _ ↦ F).run I (phase1 (preChT cap ya.1 ya.2) preInit n x)).branch p (joint ρ)

/-- What the leaf with histories `t` has seen: the target values of its target tweaks and the
values of the row at its collection queries. -/
def preSeen (t : PreState Tw Msg) (yv : Tw → Option Y) (R : Tw × Msg → Y) (_ : Tw → Msg) :
    (Tw → Y) × (Tw × Msg → Y) :=
  (fun tw ↦ if tw ∈ t.chal then (yv tw).getD 0 else 0, fun tm ↦ if tm ∈ t.coll then R tm else 0)

theorem postOf_eq_preSeen (F : Dom Sd Tw Msg → Y) (R : Tw × Msg → Y) (xs : Tw → Msg)
    (p : Σ u, Out u × PreState Tw Msg) :
    postOf I ρ (preCh cap xs) preInit n x F R p =
      prePost I ρ cap n x F p
        (preSeen p.2.2 (tvals (fun tw ↦ decide (tw ∈ p.2.2.chal)) R xs) R xs) := by
  obtain ⟨u, o, t⟩ := p
  unfold postOf prePost preCh
  exact DFunLike.congr_fun (flat_branch_congr (twoRuntime fun _ ↦ F) I
    (preChT cap (fun tw ↦ R (tw, xs tw)) R)
    (preChT cap _ _) PreState.Ext (fun _ ↦ ⟨List.prefix_refl _, List.prefix_refl _⟩)
    (fun req s t ↦ preChT_ext cap _ _ req s t) (fun req s t ↦ preChT_ext cap _ _ req s t) t
    (preChT_loc cap _ _ _ _ t (fun tw htw ↦ by simp [preSeen, tvals, htw])
      (fun tm htm ↦ by simp [preSeen, htm])) n preInit x u o) (joint ρ)

/-- **The preimage step.** In the hybrid game the adversary wins with probability at most
`(2 q₂ + 1)² (1/|Y| + 1/|Msg|)`, on average over the planted messages. -/
theorem avg_twoPhaseHyb_pre_le [Inhabited Tw]
    (hx : IAdv.IsQueryBound n x (firstBudget q₁))
    (h2 : ∀ P u o, (ph2 P u o).IsQueryBound (secondBudget q₂)) :
    (avg fun xs : Tw → Msg ↦
      twoPhaseHyb I ρ (preCh cap xs) preInit n x ph2 (preWin xs)) ≤
      (2 * (q₂ : ℝ≥0∞) + 1) ^ 2 *
        ((Fintype.card Y : ℝ≥0∞)⁻¹ + (Fintype.card Msg : ℝ≥0∞)⁻¹) := by
  refine avg_twoPhaseHyb_le_of_leaf (ch := fun xs ↦ preCh cap xs) (win := fun xs ↦ preWin xs)
    hx fun P F p ↦ ?_
  have hτ : ∀ ya, (prePost I ρ cap n x F p ya).PosSemidef := fun ya ↦
    ((twoRuntime fun _ ↦ F).run I
      (phase1 (preChT cap ya.1 ya.2) preInit n x)).posSemidef_branch_apply p (joint_posSemidef ρ)
  let M : (Tw → Y) × (Tw × Msg → Y) → HybridModel (Dom Sd Tw Msg) Y (ℕ × Msg) q₂ := fun ya ↦
    HybridModel.ofSecondPort I F (ph2 P p.1 p.2.1) (prePost I ρ cap n x F p ya) (hτ ya) q₂
      (h2 P p.1 p.2.1) Sigma.snd
  let out : (Tw → Y) × (Tw × Msg → Y) → ℕ × Msg → Tw × Msg := fun _ l ↦
    ((p.2.2.chal[l.1]?).getD default, l.2)
  have h := pre_embedded_obs_weighted_le (rowEmb P) F (fun tw ↦ decide (tw ∈ p.2.2.chal))
    (preSeen p.2.2)
    (fun k hk yv R xs v ↦ by
      have hk' : k.1 ∈ p.2.2.chal := by simpa using hk
      unfold preSeen
      refine Prod.ext rfl ?_
      funext tm
      simp only
      split_ifs with hm
      · exact Function.update_of_ne (fun heq ↦ p.2.2.disj tm hm (by rw [heq]; exact hk')) _ _
      · rfl)
    (fun _ _ _ _ _ _ ↦ rfl) M out fun ya ↦ ENNReal.ofReal (prePost I ρ cap n x F p ya).trace.re
  have hconv : ∀ f : (Tw × Msg → Y) → (Tw → Msg) → ℝ≥0∞,
      (avg fun xs : Tw → Msg ↦ avg fun R : Tw × Msg → Y ↦ f R xs) =
        ∑ R : Tw × Msg → Y, ∑ xs : Tw → Msg,
          ((Fintype.card (Tw × Msg → Y) : ℝ≥0∞)⁻¹ * (Fintype.card (Tw → Msg) : ℝ≥0∞)⁻¹) *
            f R xs := by
    intro f
    unfold avg
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun R _ ↦ Finset.sum_congr rfl fun xs _ ↦ by
      rw [← mul_assoc, mul_comm (Fintype.card (Tw → Msg) : ℝ≥0∞)⁻¹]
  rw [hconv, hconv]
  refine le_trans (Finset.sum_le_sum fun R _ ↦ Finset.sum_le_sum fun xs _ ↦
    mul_le_mul' le_rfl ?_) (le_trans h (le_of_eq ?_))
  · rw [HybridModel.ofSecondPort_prob, postOf_eq_preSeen, ← patchRow_eq_patch]
    refine leafProb_mono _ _ fun l hl ↦ ?_
    obtain ⟨t, hget, heq⟩ := hl
    have hmem : t ∈ p.2.2.chal := List.mem_of_getElem? hget
    refine ⟨?_, ?_⟩
    · simp only [out, hget, Option.getD_some]
      simpa using hmem
    · simp only [out, hget, Option.getD_some]
      exact heq
  · congr 1
    exact Finset.sum_congr rfl fun R _ ↦ Finset.sum_congr rfl fun xs _ ↦ by
      rw [postOf_eq_preSeen]

/-- **SM-DT-PRE in the QROM, exact adaptive two-phase game**, square-root form. -/
theorem pre_exact_sqrt_le [Inhabited Tw]
    (hx : IAdv.IsQueryBound n x (firstBudget q₁))
    (h2 : ∀ P u o, (ph2 P u o).IsQueryBound (secondBudget q₂)) :
    preExp I ρ cap n x ph2 ^ (2⁻¹ : ℝ) ≤
      ((2 * (q₂ : ℝ≥0∞) + 1) ^ 2 *
        ((Fintype.card Y : ℝ≥0∞)⁻¹ + (Fintype.card Msg : ℝ≥0∞)⁻¹)) ^ (2⁻¹ : ℝ) +
        2 * q₁ * ((Fintype.card Sd : ℝ≥0∞)⁻¹) ^ (2⁻¹ : ℝ) := by
  have h := sqrt_avg_le
    (fun xs : Tw → Msg ↦ twoPhaseExp I ρ (preCh cap xs) preInit n x ph2 (preWin xs))
    (fun xs ↦ twoPhaseHyb I ρ (preCh cap xs) preInit n x ph2 (preWin xs))
    (fun _ ↦ (2 * (q₁ : ℝ≥0∞) * ((Fintype.card Sd : ℝ≥0∞)⁻¹) ^ (2⁻¹ : ℝ)) ^ 2)
    (fun xs ↦ by rw [sqrt_sq]; exact seed_hiding hx h2)
  refine h.trans (add_le_add (sqrt_le_sqrt (avg_twoPhaseHyb_pre_le hx h2)) ?_)
  refine (sqrt_le_sqrt (avg_le fun _ ↦ le_rfl)).trans ?_
  rw [sqrt_sq]

/-- **SM-DT-PRE in the QROM, exact adaptive two-phase game**:
`Pr[win] ≤ (√((2 q₂ + 1)² (1/|Y| + 1/|Msg|)) + 2 q₁ / √|Sd|)²`. -/
theorem pre_exact_le [Inhabited Tw]
    (hx : IAdv.IsQueryBound n x (firstBudget q₁))
    (h2 : ∀ P u o, (ph2 P u o).IsQueryBound (secondBudget q₂)) :
    preExp I ρ cap n x ph2 ≤
      (((2 * (q₂ : ℝ≥0∞) + 1) ^ 2 *
        ((Fintype.card Y : ℝ≥0∞)⁻¹ + (Fintype.card Msg : ℝ≥0∞)⁻¹)) ^ (2⁻¹ : ℝ) +
        2 * q₁ * ((Fintype.card Sd : ℝ≥0∞)⁻¹) ^ (2⁻¹ : ℝ)) ^ 2 := by
  have h := pre_exact_sqrt_le (I := I) (ρ := ρ) (cap := cap) hx h2
  calc preExp I ρ cap n x ph2 = (preExp I ρ cap n x ph2 ^ (2⁻¹ : ℝ)) ^ 2 := (sq_sqrt _).symm
    _ ≤ _ := pow_le_pow_left' h 2

/-- The experiment is a probability. -/
theorem preExp_le_one : preExp I ρ cap n x ph2 ≤ 1 :=
  avg_le fun _ ↦ twoPhaseExp_le_one

end Exp

end PQ.QROM

#print axioms PQ.QROM.avg_twoPhaseHyb_pre_le
#print axioms PQ.QROM.pre_exact_sqrt_le
#print axioms PQ.QROM.pre_exact_le
#print axioms PQ.QROM.preExp_le_one
