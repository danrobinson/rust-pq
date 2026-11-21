import PQ.QROM.TwoPhaseGame
import PQ.QROM.SprGiven

/-!
# The exact SM-DT-TCR game in the QROM

The two-phase, adaptive-target game of VCVio's `TweakableHash.SM_DT_TCR_Experiment`
(`VCVio/CryptoFoundations/HardnessAssumptions/TweakableHash/SMDTTCR.lean`), with the tweakable
hash a uniformly random function `Th : Sd × (Tw × Msg) → Y` and a quantum-query adversary in
both phases.  The general model (seed-keyed random oracle, two ports, hidden-then-revealed seed,
interactive first phase) is described in `PQ/QROM/TwoPhaseGame.lean`.

## Correspondence with `SM_DT_TCR_Experiment`

* `pk ← prob.th.seedGen`: here `P : Sd` uniform.  `prob.th.eval pk t m` is `Th (P, (t, m))`.
* `adv.choose`, run against `SM_DT_TCR_oracles prob pk`: here the interactive adversary
  `x : IAdv … ((Tw × Msg) ⊕ (Tw × Msg)) (Option Y) Out n A`.  Its classical requests are answered
  by the challenger `tcrCh cap (rowOf Th P)`, whose state `TcrState` is the pair of histories of
  VCVio's game, recorded by the game:
  - `Sum.inl (t, m)` is a query to the challenge oracle `SM_DT_TCR_challengeOracle`.  It is
    rejected (`none`, state unchanged) when the cap `cap = prob.numTargets` is reached, when `t`
    occurs in the challenge history, or when `t` has been spent on the collection oracle;
    otherwise the answer is `some (Th (P, (t, m)))` and `(t, m)` is appended to the challenge
    history (issue order).
  - `Sum.inr (t, m)` is a query to the collection oracle `collectionOracle`.  It is rejected
    when `t` occurs in the challenge history; otherwise the answer is `some (Th (P, (t, m)))`
    and the query is appended to the collection history.  The collection is modelled as further
    evaluations of the same random function at the hidden seed, on tweaks kept disjoint from
    the target tweaks by the two oracles, as in VCVio's game.  (VCVio's state keeps the
    collection tweaks only; here the whole query is kept, which records more and changes no
    answer.)
  `choose` does not receive `pk`: `x` does not depend on `P`.  Unlike in VCVio's game, where
  `choose` reaches the hash only through the two oracles, here phase 1 also has quantum access
  to the whole random function, at every seed.  The stand-alone problem
  (`SM_DT_TCR_Problem.standalone`) is the case of adversaries that send no `Sum.inr` request.
* `adv.forge st pk`: here `ph2 P u o`, a quantum query program continuing on the register `u`
  left by phase 1, with the classical output `o` of phase 1 and the revealed seed `P`; it has
  no challenge or collection oracle and returns `(j, m) : ℕ × Msg`.
* Win (`tcrWin`): the `j`-th entry `(t, mj)` of the challenge history exists, `m ≠ mj` and
  `Th (P, (t, m)) = Th (P, (t, mj))`.  An index outside the history loses.

## Result

`tcr_exact_sqrt_le` / `tcr_exact_le`:
`Pr[win] ≤ (√((2 q₂ + 1)² / |Y|) + 2 q₁ / √|Sd|)²`, independently of the number of targets and
of the number of classical requests, for every adversary with at most `q₁` quantum queries in
phase 1 and `q₂` in phase 2.
-/

open MeasureTheory ENNReal Quantum Matrix
open scoped Kronecker ComplexOrder

universe u v w

set_option linter.unusedSectionVars false

namespace PQ.QROM

variable {Sd Tw Msg Y : Type}

/-! ## The challenger -/

/-- The state of the SM-DT-TCR game: the challenge history (accepted targets, in issue order)
and the collection history (accepted collection queries).  By construction the target tweaks
are pairwise distinct and no collection query is on a target tweak. -/
structure TcrState (Tw Msg : Type) where
  /-- The accepted targets, in issue order. -/
  chal : List (Tw × Msg)
  /-- The accepted collection queries. -/
  coll : List (Tw × Msg)
  /-- The target tweaks are pairwise distinct. -/
  nodup : (chal.map Prod.fst).Nodup
  /-- No collection query is on a target tweak. -/
  disj : ∀ p ∈ coll, p.1 ∉ chal.map Prod.fst

/-- The empty histories. -/
def tcrInit : TcrState Tw Msg := ⟨[], [], List.nodup_nil, fun _ h ↦ by simp at h⟩

/-- The two classical oracles of SM-DT-TCR for the row `a` of the hash at the seed, with target
cap `cap`.  `Sum.inl (t, m)`: challenge oracle.  `Sum.inr (t, m)`: collection oracle. -/
def tcrCh [DecidableEq Tw] (cap : ℕ) (a : Tw × Msg → Y) :
    (Tw × Msg) ⊕ (Tw × Msg) → TcrState Tw Msg → Option Y × TcrState Tw Msg
  | .inl tm, s =>
    if h : cap ≤ s.chal.length ∨ tm.1 ∈ s.chal.map Prod.fst ∨ tm.1 ∈ s.coll.map Prod.fst then
      (none, s)
    else (some (a tm), ⟨s.chal ++ [tm], s.coll, by
        rw [List.map_append, List.map_singleton]
        exact List.Nodup.append s.nodup (List.nodup_singleton _) (by
          intro t ht ht'
          rw [List.mem_singleton] at ht'
          exact h (Or.inr (Or.inl (ht' ▸ ht)))), by
        intro p hp hmem
        rw [List.map_append, List.map_singleton, List.mem_append, List.mem_singleton] at hmem
        rcases hmem with hmem | hmem
        · exact s.disj p hp hmem
        · exact h (Or.inr (Or.inr (hmem ▸ List.mem_map.2 ⟨p, hp, rfl⟩)))⟩)
  | .inr tm, s =>
    if h : tm.1 ∈ s.chal.map Prod.fst then (none, s)
    else (some (a tm), ⟨s.chal, s.coll ++ [tm], s.nodup, by
        intro p hp
        rw [List.mem_append, List.mem_singleton] at hp
        rcases hp with hp | hp
        · exact s.disj p hp
        · rw [hp]; exact h⟩)

/-- The winning condition of SM-DT-TCR: the result `(j, m)` names a recorded target
`(t, mj)` and a message `m ≠ mj` colliding with it under the row `a`. -/
def tcrWin (a : Tw × Msg → Y) (r : ℕ × Msg) (s : TcrState Tw Msg) : Prop :=
  ∃ t mj, s.chal[r.1]? = some (t, mj) ∧ r.2 ≠ mj ∧ a (t, r.2) = a (t, mj)

section Challenger

variable [DecidableEq Tw]

/-- The targets of a history, as a partial function of the tweak. -/
def cOf (s : TcrState Tw Msg) : Tw → Option Msg :=
  fun t ↦ (s.chal.find? fun e ↦ decide (e.1 = t)).map Prod.snd

theorem find_of_mem {l : List (Tw × Msg)} (hl : (l.map Prod.fst).Nodup) {t : Tw} {m : Msg}
    (h : (t, m) ∈ l) : (l.find? fun e ↦ decide (e.1 = t)).map Prod.snd = some m := by
  induction l with
  | nil => simp at h
  | cons hd tl ih =>
    rw [List.map_cons, List.nodup_cons] at hl
    rcases List.mem_cons.1 h with heq | hmem
    · subst heq
      simp
    · have hne : hd.1 ≠ t := fun he ↦ hl.1 (by
        rw [he]
        exact List.mem_map.2 ⟨(t, m), hmem, rfl⟩)
      rw [List.find?_cons_of_neg (by simpa using hne)]
      exact ih hl.2 hmem

theorem cOf_of_mem (s : TcrState Tw Msg) {t : Tw} {m : Msg} (h : (t, m) ∈ s.chal) :
    cOf s t = some m :=
  find_of_mem s.nodup h

/-- A tweak with a target occurs in the challenge history. -/
theorem mem_of_cOf (s : TcrState Tw Msg) {t : Tw} {m : Msg} (h : cOf s t = some m) :
    t ∈ s.chal.map Prod.fst := by
  unfold cOf at h
  cases hf : s.chal.find? fun e ↦ decide (e.1 = t) with
  | none => rw [hf] at h; simp at h
  | some e =>
    have h1 := List.find?_some hf
    have h2 := List.mem_of_find?_eq_some hf
    exact List.mem_map.2 ⟨e, h2, by simpa using h1⟩

/-- `t` extends `s`: both histories of `s` are prefixes of those of `t`. -/
def TcrState.Ext (s t : TcrState Tw Msg) : Prop := s.chal <+: t.chal ∧ s.coll <+: t.coll

/-- Every step of the challenger extends the histories. -/
theorem tcrCh_ext (cap : ℕ) (a : Tw × Msg → Y) (req : (Tw × Msg) ⊕ (Tw × Msg))
    (s t : TcrState Tw Msg) (h : (tcrCh cap a req s).2.Ext t) : s.Ext t := by
  cases req with
  | inl tm =>
    simp only [tcrCh] at h
    split_ifs at h with hc
    · exact h
    · exact ⟨(List.prefix_append _ _).trans h.1, h.2⟩
  | inr tm =>
    simp only [tcrCh] at h
    split_ifs at h with hc
    · exact h
    · exact ⟨h.1, (List.prefix_append _ _).trans h.2⟩

/-- Two rows that agree on the recorded queries of the histories `t` are answered in the same
way, except after requests that make `t` unreachable. -/
theorem tcrCh_loc (cap : ℕ) (a a' : Tw × Msg → Y) (t : TcrState Tw Msg)
    (haa : ∀ tm, tm ∈ t.chal ∨ tm ∈ t.coll → a tm = a' tm) (req : (Tw × Msg) ⊕ (Tw × Msg))
    (s : TcrState Tw Msg) :
    tcrCh cap a req s = tcrCh cap a' req s ∨
      (¬ (tcrCh cap a req s).2.Ext t ∧ ¬ (tcrCh cap a' req s).2.Ext t) := by
  cases req with
  | inl tm =>
    simp only [tcrCh]
    split_ifs with hc
    · exact Or.inl rfl
    · by_cases he : a tm = a' tm
      · left
        rw [he]
      · right
        have hn : ¬ (s.chal ++ [tm]) <+: t.chal := fun hp ↦
          he (haa tm (Or.inl (hp.subset (by simp))))
        exact ⟨fun h ↦ hn h.1, fun h ↦ hn h.1⟩
  | inr tm =>
    simp only [tcrCh]
    split_ifs with hc
    · exact Or.inl rfl
    · by_cases he : a tm = a' tm
      · left
        rw [he]
      · right
        have hn : ¬ (s.coll ++ [tm]) <+: t.coll := fun hp ↦
          he (haa tm (Or.inr (hp.subset (by simp))))
        exact ⟨fun h ↦ hn h.2, fun h ↦ hn h.2⟩

end Challenger

/-! ## The experiment -/

section Exp

variable [Fintype Sd] [DecidableEq Sd] [Fintype Tw] [DecidableEq Tw] [Fintype Msg]
  [DecidableEq Msg] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
  {L : LocalSig.{u, v}} {Out : QReg → Type w} {A : QReg}

/-- **The exact SM-DT-TCR experiment in the QROM** (target cap `cap`): the probability, over
the uniform seed `P`, the uniform hash `Th` and the run, that the two-phase quantum adversary
`(x, ph2)` started on `ρ` wins. -/
noncomputable def tcrExp (I : L.Interp) (ρ : SubState A) (cap n : ℕ)
    (x : IAdv L (qrom2Spec (Dom Sd Tw Msg) Y) ((Tw × Msg) ⊕ (Tw × Msg)) (Option Y) Out n A)
    (ph2 : Sd → ∀ u, Out u →
      QuantumComp L (qrom2Spec (Dom Sd Tw Msg) Y) (fun _ ↦ ℕ × Msg) u) : ℝ≥0∞ :=
  twoPhaseExp I ρ (tcrCh cap) tcrInit n x ph2 tcrWin

/-- The row of the seed `P`, as an embedding of `Tw × Msg` into the domain. -/
def rowEmb (P : Sd) : Tw × Msg ↪ Dom Sd Tw Msg :=
  ⟨fun tm ↦ (P, tm), fun _ _ h ↦ (Prod.ext_iff.1 h).2⟩

theorem patchRow_eq_patch (F : Dom Sd Tw Msg → Y) (P : Sd) (R : Tw × Msg → Y) :
    patchRow F P R = patch F (rowEmb P) R := by
  funext z
  by_cases h : z.1 = P
  · obtain ⟨s, tm⟩ := z
    simp only at h
    subst h
    exact (by simp [patchRow] : patchRow F s R (s, tm) = R tm).trans
      (patch_apply F (rowEmb s) R tm).symm
  · rw [patch_of_not_range]
    · simp [patchRow, h]
    · rintro ⟨p, hp⟩
      exact h (by rw [← hp]; rfl)

/-- What the leaf with histories `t` has seen of the row `R`: its values at the recorded
queries (and `0` elsewhere). -/
def seenOf (t : TcrState Tw Msg) (R : Tw × Msg → Y) : Tw × Msg → Y :=
  fun tm ↦ if tm ∈ t.chal ∨ tm ∈ t.coll then R tm else 0

/-- Changing the row at a non-target point of a target tweak is not seen. -/
theorem seenOf_update (t : TcrState Tw Msg) (k : Tw × Msg) (m : Msg) (hc : cOf t k.1 = some m)
    (hk : k.2 ≠ m) (R : Tw × Msg → Y) (v : Y) :
    seenOf t (Function.update R k v) = seenOf t R := by
  funext tm
  unfold seenOf
  split_ifs with h
  · refine Function.update_of_ne (fun heq ↦ ?_) _ _
    subst heq
    rcases h with h | h
    · exact hk (Option.some.inj ((cOf_of_mem t (t := tm.1) (m := tm.2) h).symm.trans hc))
    · exact t.disj tm h (mem_of_cOf t hc)
  · rfl

/-- **Locality of the classical oracles.** The post-state of a leaf of phase 1 with histories
`t` only depends on the values of the row at the recorded queries of `t`. -/
theorem tcr_branch_congr (R : QuantumRuntime (qrom2Spec (Dom Sd Tw Msg) Y)) (I : L.Interp)
    (cap n : ℕ)
    (x : IAdv L (qrom2Spec (Dom Sd Tw Msg) Y) ((Tw × Msg) ⊕ (Tw × Msg)) (Option Y) Out n A)
    (a a' : Tw × Msg → Y) (u : QReg) (o : Out u) (t : TcrState Tw Msg)
    (haa : ∀ tm, tm ∈ t.chal ∨ tm ∈ t.coll → a tm = a' tm) :
    (R.run I (phase1 (tcrCh cap a) tcrInit n x)).branch ⟨u, (o, t)⟩ =
      (R.run I (phase1 (tcrCh cap a') tcrInit n x)).branch ⟨u, (o, t)⟩ :=
  flat_branch_congr R I (tcrCh cap a) (tcrCh cap a') TcrState.Ext
    (fun _ ↦ ⟨List.prefix_refl _, List.prefix_refl _⟩) (fun req s t ↦ tcrCh_ext cap a req s t)
    (fun req s t ↦ tcrCh_ext cap a' req s t) t (tcrCh_loc cap a a' t haa) n tcrInit x u o

variable {I : L.Interp} {ρ : SubState A} {cap n q₁ q₂ : ℕ}
  {x : IAdv L (qrom2Spec (Dom Sd Tw Msg) Y) ((Tw × Msg) ⊕ (Tw × Msg)) (Option Y) Out n A}
  {ph2 : Sd → ∀ u, Out u → QuantumComp L (qrom2Spec (Dom Sd Tw Msg) Y) (fun _ ↦ ℕ × Msg) u}

theorem postOf_eq_seen (F : Dom Sd Tw Msg → Y) (R : Tw × Msg → Y)
    (p : Σ u, Out u × TcrState Tw Msg) :
    postOf I ρ (tcrCh cap) tcrInit n x F R p =
      postOf I ρ (tcrCh cap) tcrInit n x F (seenOf p.2.2 R) p := by
  obtain ⟨u, o, t⟩ := p
  unfold postOf
  rw [tcr_branch_congr (twoRuntime fun _ ↦ F) I cap n x R (seenOf t R) u o t fun tm htm ↦ by
    simp [seenOf, htm]]

/-- **The collision step.** In the hybrid game, where the row of the hash at the seed is
independent of what phase 1 saw except for the answers of the classical oracles, the adversary
wins with probability at most `(2 q₂ + 1)² / |Y|`. -/
theorem twoPhaseHyb_tcr_le [Inhabited Tw]
    (hx : IAdv.IsQueryBound n x (firstBudget q₁))
    (h2 : ∀ P u o, (ph2 P u o).IsQueryBound (secondBudget q₂)) :
    twoPhaseHyb I ρ (tcrCh cap) tcrInit n x ph2 tcrWin ≤
      (2 * (q₂ : ℝ≥0∞) + 1) ^ 2 / (Fintype.card Y : ℝ≥0∞) := by
  refine twoPhaseHyb_le_of_leaf hx fun P F p ↦ ?_
  let τ : (Tw × Msg → Y) → Matrix (p.1 × Unit) (p.1 × Unit) ℂ :=
    fun a ↦ postOf I ρ (tcrCh cap) tcrInit n x F a p
  have hτ : ∀ a, (τ a).PosSemidef := fun a ↦ postOf_posSemidef F a p
  let M : (Tw × Msg → Y) → HybridModel (Dom Sd Tw Msg) Y (ℕ × Msg) q₂ := fun a ↦
    HybridModel.ofSecondPort I F (ph2 P p.1 p.2.1) (τ a) (hτ a) q₂ (h2 P p.1 p.2.1) Sigma.snd
  let out : (Tw × Msg → Y) → ℕ × Msg → Tw × Msg := fun _ l ↦
    (((p.2.2.chal[l.1]?).map Prod.fst).getD default, l.2)
  have hpost : ∀ R : Tw × Msg → Y,
      postOf I ρ (tcrCh cap) tcrInit n x F R p = τ (seenOf p.2.2 R) :=
    fun R ↦ postOf_eq_seen F R p
  have h := spr_embedded_obs_weighted_le (rowEmb P) F (cOf p.2.2) (seenOf p.2.2)
    (fun k m hc hk R v ↦ seenOf_update p.2.2 k m hc hk R v) M out
    fun a ↦ ENNReal.ofReal (τ a).trace.re
  refine le_trans (avg_mono fun R ↦ ?_) (le_trans h (le_of_eq ?_))
  · rw [HybridModel.ofSecondPort_prob, hpost R, ← patchRow_eq_patch]
    refine leafProb_mono _ _ fun l hl ↦ ?_
    obtain ⟨t, mj, hget, hne, heq⟩ := hl
    have hmem : (t, mj) ∈ p.2.2.chal := List.mem_of_getElem? hget
    refine ⟨mj, ?_, hne, ?_⟩
    · simp only [out, hget, Option.map_some, Option.getD_some]
      exact cOf_of_mem p.2.2 hmem
    · simp only [out, hget, Option.map_some, Option.getD_some]
      exact heq
  · congr 1
    exact Finset.sum_congr rfl fun R _ ↦ by beta_reduce; rw [hpost R]

/-- **SM-DT-TCR in the QROM, exact adaptive two-phase game**, square-root form:
`√Pr[win] ≤ √((2 q₂ + 1)² / |Y|) + 2 q₁ / √|Sd|`. -/
theorem tcr_exact_sqrt_le [Inhabited Tw]
    (hx : IAdv.IsQueryBound n x (firstBudget q₁))
    (h2 : ∀ P u o, (ph2 P u o).IsQueryBound (secondBudget q₂)) :
    tcrExp I ρ cap n x ph2 ^ (2⁻¹ : ℝ) ≤
      ((2 * (q₂ : ℝ≥0∞) + 1) ^ 2 / (Fintype.card Y : ℝ≥0∞)) ^ (2⁻¹ : ℝ) +
        2 * q₁ * ((Fintype.card Sd : ℝ≥0∞)⁻¹) ^ (2⁻¹ : ℝ) :=
  (seed_hiding hx h2).trans
    (add_le_add (sqrt_le_sqrt (twoPhaseHyb_tcr_le hx h2)) le_rfl)

/-- **SM-DT-TCR in the QROM, exact adaptive two-phase game**:
`Pr[win] ≤ (√((2 q₂ + 1)² / |Y|) + 2 q₁ / √|Sd|)²`, for every two-phase quantum adversary with
at most `q₁` queries before and `q₂` queries after the seed is revealed, any number of
adaptively chosen targets and any number of collection queries. -/
theorem tcr_exact_le [Inhabited Tw]
    (hx : IAdv.IsQueryBound n x (firstBudget q₁))
    (h2 : ∀ P u o, (ph2 P u o).IsQueryBound (secondBudget q₂)) :
    tcrExp I ρ cap n x ph2 ≤
      (((2 * (q₂ : ℝ≥0∞) + 1) ^ 2 / (Fintype.card Y : ℝ≥0∞)) ^ (2⁻¹ : ℝ) +
        2 * q₁ * ((Fintype.card Sd : ℝ≥0∞)⁻¹) ^ (2⁻¹ : ℝ)) ^ 2 := by
  have h := tcr_exact_sqrt_le (I := I) (ρ := ρ) (cap := cap) hx h2
  calc tcrExp I ρ cap n x ph2 = (tcrExp I ρ cap n x ph2 ^ (2⁻¹ : ℝ)) ^ 2 := (sq_sqrt _).symm
    _ ≤ _ := pow_le_pow_left' h 2

/-- The experiment is a probability. -/
theorem tcrExp_le_one : tcrExp I ρ cap n x ph2 ≤ 1 :=
  twoPhaseExp_le_one

end Exp

end PQ.QROM

#print axioms PQ.QROM.seed_hiding
#print axioms PQ.QROM.twoPhaseHyb_tcr_le
#print axioms PQ.QROM.tcr_exact_sqrt_le
#print axioms PQ.QROM.tcr_exact_le
#print axioms PQ.QROM.tcrExp_le_one
