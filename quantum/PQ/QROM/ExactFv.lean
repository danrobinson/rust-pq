import PQ.QROM.ExactTcr

/-!
# The exact source-final-validity SM-DT-TCR game in the QROM

The game of VCVio's `TweakableHash.SM_DT_TCR_SourceFinalValidity.experiment`
(`…/TweakableHash/SMDTTCRFinalValidity.lean`), with the tweakable hash a uniformly random
function and a quantum-query adversary in both phases (model: `PQ/QROM/TwoPhaseGame.lean`).

## Correspondence

* The two first-phase oracles always answer and always record:
  `Sum.inl (t, m)` (target oracle `challengeOracle`) returns `Th (P, (t, m))` and appends
  `(t, m)` to the challenge history; `Sum.inr (t, m)` (collection oracle
  `SourceFinalValidity.collectionOracle`) returns `Th (P, (t, m))` and appends the query to the
  collection history (`fvCh`).  The collection is modelled as the same random function at the
  hidden seed, as for `PQ/QROM/ExactTcr.lean`; the game state keeps whole collection queries
  rather than their tweaks only.
* Final validity (`FvValid cap`): at most `cap = numTargets` targets, pairwise distinct target
  tweaks, and no collection query on a target tweak.  This is VCVio's
  `SourceFinalValidity.Valid`, which its sticky bit `gameState.valid` decides on every reachable
  state (`valid_eq_decide_valid_of_reachable`); here the final predicate is used directly.
* Win (`fvWin`): final validity holds, the `j`-th entry `(t, mj)` of the challenge history
  exists, `m ≠ mj` and `Th (P, (t, m)) = Th (P, (t, mj))`.

## Result

`tcr_fv_exact_le`: `Pr[win] ≤ (√((2 q₂ + 1)² / |Y|) + 2 q₁ / √|Sd|)²`.
-/

open MeasureTheory ENNReal Quantum Matrix
open scoped Kronecker ComplexOrder

universe u v w

set_option linter.unusedSectionVars false

namespace PQ.QROM

variable {Sd Tw Msg Y : Type}

/-- The histories of the source-final-validity game: every target query and every collection
query, in issue order. -/
structure FvState (Tw Msg : Type) where
  /-- Every target query. -/
  chal : List (Tw × Msg)
  /-- Every collection query. -/
  coll : List (Tw × Msg)

/-- The empty histories. -/
def fvInit : FvState Tw Msg := ⟨[], []⟩

/-- The always-answering oracles for the row `a` of the hash at the seed. -/
def fvCh (a : Tw × Msg → Y) : (Tw × Msg) ⊕ (Tw × Msg) → FvState Tw Msg → Y × FvState Tw Msg
  | .inl tm, s => (a tm, ⟨s.chal ++ [tm], s.coll⟩)
  | .inr tm, s => (a tm, ⟨s.chal, s.coll ++ [tm]⟩)

/-- Final validity: at most `cap` targets, distinct target tweaks, no collection query on a
target tweak. -/
def FvValid (cap : ℕ) (s : FvState Tw Msg) : Prop :=
  s.chal.length ≤ cap ∧ (s.chal.map Prod.fst).Nodup ∧ ∀ p ∈ s.coll, p.1 ∉ s.chal.map Prod.fst

/-- The winning condition: final validity and a collision with a recorded target. -/
def fvWin (cap : ℕ) (a : Tw × Msg → Y) (r : ℕ × Msg) (s : FvState Tw Msg) : Prop :=
  FvValid cap s ∧ ∃ t mj, s.chal[r.1]? = some (t, mj) ∧ r.2 ≠ mj ∧ a (t, r.2) = a (t, mj)

/-- `t` extends `s`. -/
def FvState.Ext (s t : FvState Tw Msg) : Prop := s.chal <+: t.chal ∧ s.coll <+: t.coll

theorem fvCh_ext (a : Tw × Msg → Y) (req : (Tw × Msg) ⊕ (Tw × Msg)) (s t : FvState Tw Msg)
    (h : (fvCh a req s).2.Ext t) : s.Ext t := by
  cases req with
  | inl tm => exact ⟨(List.prefix_append _ _).trans h.1, h.2⟩
  | inr tm => exact ⟨h.1, (List.prefix_append _ _).trans h.2⟩

theorem fvCh_loc (a a' : Tw × Msg → Y) (t : FvState Tw Msg)
    (haa : ∀ tm, tm ∈ t.chal ∨ tm ∈ t.coll → a tm = a' tm) (req : (Tw × Msg) ⊕ (Tw × Msg))
    (s : FvState Tw Msg) :
    fvCh a req s = fvCh a' req s ∨ (¬ (fvCh a req s).2.Ext t ∧ ¬ (fvCh a' req s).2.Ext t) := by
  cases req with
  | inl tm =>
    by_cases he : a tm = a' tm
    · left
      simp only [fvCh, he]
    · right
      have hn : ¬ (s.chal ++ [tm]) <+: t.chal := fun hp ↦
        he (haa tm (Or.inl (hp.subset (by simp))))
      exact ⟨fun h ↦ hn h.1, fun h ↦ hn h.1⟩
  | inr tm =>
    by_cases he : a tm = a' tm
    · left
      simp only [fvCh, he]
    · right
      have hn : ¬ (s.coll ++ [tm]) <+: t.coll := fun hp ↦
        he (haa tm (Or.inr (hp.subset (by simp))))
      exact ⟨fun h ↦ hn h.2, fun h ↦ hn h.2⟩

section Exp

variable [Fintype Sd] [DecidableEq Sd] [Fintype Tw] [DecidableEq Tw] [Fintype Msg]
  [DecidableEq Msg] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
  {L : LocalSig.{u, v}} {Out : QReg → Type w} {A : QReg}

/-- **The exact source-final-validity SM-DT-TCR experiment in the QROM.** -/
noncomputable def tcrFvExp (I : L.Interp) (ρ : SubState A) (cap n : ℕ)
    (x : IAdv L (qrom2Spec (Dom Sd Tw Msg) Y) ((Tw × Msg) ⊕ (Tw × Msg)) Y Out n A)
    (ph2 : Sd → ∀ u, Out u →
      QuantumComp L (qrom2Spec (Dom Sd Tw Msg) Y) (fun _ ↦ ℕ × Msg) u) : ℝ≥0∞ :=
  twoPhaseExp I ρ fvCh fvInit n x ph2 (fvWin cap)

/-- The targets of a history. -/
def fvC (t : FvState Tw Msg) : Tw → Option Msg :=
  fun tw ↦ (t.chal.find? fun e ↦ decide (e.1 = tw)).map Prod.snd

theorem mem_of_fvC (t : FvState Tw Msg) {tw : Tw} {m : Msg} (h : fvC t tw = some m) :
    tw ∈ t.chal.map Prod.fst := by
  unfold fvC at h
  cases hf : t.chal.find? fun e ↦ decide (e.1 = tw) with
  | none => rw [hf] at h; simp at h
  | some e =>
    have h1 := List.find?_some hf
    have h2 := List.mem_of_find?_eq_some hf
    exact List.mem_map.2 ⟨e, h2, by simpa using h1⟩

/-- What the leaf with histories `t` has seen of the row. -/
def fvSeen (t : FvState Tw Msg) (R : Tw × Msg → Y) : Tw × Msg → Y :=
  fun tm ↦ if tm ∈ t.chal ∨ tm ∈ t.coll then R tm else 0

theorem fvSeen_update (cap : ℕ) (t : FvState Tw Msg) (hv : FvValid cap t) (k : Tw × Msg)
    (m : Msg) (hc : fvC t k.1 = some m) (hk : k.2 ≠ m) (R : Tw × Msg → Y) (v : Y) :
    fvSeen t (Function.update R k v) = fvSeen t R := by
  funext tm
  unfold fvSeen
  split_ifs with h
  · refine Function.update_of_ne (fun heq ↦ ?_) _ _
    subst heq
    rcases h with h | h
    · exact hk (Option.some.inj ((find_of_mem hv.2.1 (t := tm.1) (m := tm.2) h).symm.trans hc))
    · exact hv.2.2 tm h (mem_of_fvC t hc)
  · rfl

variable {I : L.Interp} {ρ : SubState A} {cap n q₁ q₂ : ℕ}
  {x : IAdv L (qrom2Spec (Dom Sd Tw Msg) Y) ((Tw × Msg) ⊕ (Tw × Msg)) Y Out n A}
  {ph2 : Sd → ∀ u, Out u → QuantumComp L (qrom2Spec (Dom Sd Tw Msg) Y) (fun _ ↦ ℕ × Msg) u}

theorem postOf_eq_fvSeen (F : Dom Sd Tw Msg → Y) (R : Tw × Msg → Y)
    (p : Σ u, Out u × FvState Tw Msg) :
    postOf I ρ fvCh fvInit n x F R p = postOf I ρ fvCh fvInit n x F (fvSeen p.2.2 R) p := by
  obtain ⟨u, o, t⟩ := p
  unfold postOf
  exact DFunLike.congr_fun (flat_branch_congr (twoRuntime fun _ ↦ F) I (fvCh R)
    (fvCh (fvSeen t R)) FvState.Ext (fun _ ↦ ⟨List.prefix_refl _, List.prefix_refl _⟩)
    (fun req s t ↦ fvCh_ext R req s t) (fun req s t ↦ fvCh_ext _ req s t) t
    (fvCh_loc R _ t fun tm htm ↦ by simp [fvSeen, htm]) n fvInit x u o) (joint ρ)

/-- **The collision step** for the source-final-validity game. -/
theorem twoPhaseHyb_tcrFv_le [Inhabited Tw]
    (hx : IAdv.IsQueryBound n x (firstBudget q₁))
    (h2 : ∀ P u o, (ph2 P u o).IsQueryBound (secondBudget q₂)) :
    twoPhaseHyb I ρ fvCh fvInit n x ph2 (fvWin cap) ≤
      (2 * (q₂ : ℝ≥0∞) + 1) ^ 2 / (Fintype.card Y : ℝ≥0∞) := by
  refine twoPhaseHyb_le_of_leaf hx fun P F p ↦ ?_
  by_cases hv : FvValid cap p.2.2
  swap
  · refine le_trans (le_of_eq ?_) zero_le
    have h0 : ∀ R : Tw × Msg → Y,
        leafProb (twoRuntime (ports F (patchRow F P R))) I (ph2 P p.1 p.2.1)
          (postOf I ρ fvCh fvInit n x F R p) (fun l ↦ fvWin cap R l.2 p.2.2) = 0 := fun R ↦ by
      unfold leafProb
      simp only [tsum_eq_zero_iff]
      intro l
      rw [ind_of_false fun h ↦ hv h.1, mul_zero]
    simp only [h0]
    exact le_antisymm (avg_le fun _ ↦ le_rfl) zero_le
  let τ : (Tw × Msg → Y) → Matrix (p.1 × Unit) (p.1 × Unit) ℂ :=
    fun a ↦ postOf I ρ fvCh fvInit n x F a p
  have hτ : ∀ a, (τ a).PosSemidef := fun a ↦ postOf_posSemidef F a p
  let M : (Tw × Msg → Y) → HybridModel (Dom Sd Tw Msg) Y (ℕ × Msg) q₂ := fun a ↦
    HybridModel.ofSecondPort I F (ph2 P p.1 p.2.1) (τ a) (hτ a) q₂ (h2 P p.1 p.2.1) Sigma.snd
  let out : (Tw × Msg → Y) → ℕ × Msg → Tw × Msg := fun _ l ↦
    (((p.2.2.chal[l.1]?).map Prod.fst).getD default, l.2)
  have hpost : ∀ R : Tw × Msg → Y, postOf I ρ fvCh fvInit n x F R p = τ (fvSeen p.2.2 R) :=
    fun R ↦ postOf_eq_fvSeen F R p
  have h := spr_embedded_obs_weighted_le (rowEmb P) F (fvC p.2.2) (fvSeen p.2.2)
    (fun k m hc hk R v ↦ fvSeen_update cap p.2.2 hv k m hc hk R v) M out
    fun a ↦ ENNReal.ofReal (τ a).trace.re
  refine le_trans (avg_mono fun R ↦ ?_) (le_trans h (le_of_eq ?_))
  · rw [HybridModel.ofSecondPort_prob, hpost R, ← patchRow_eq_patch]
    refine leafProb_mono _ _ fun l hl ↦ ?_
    obtain ⟨-, t, mj, hget, hne, heq⟩ := hl
    have hmem : (t, mj) ∈ p.2.2.chal := List.mem_of_getElem? hget
    refine ⟨mj, ?_, hne, ?_⟩
    · simp only [out, hget, Option.map_some, Option.getD_some]
      exact find_of_mem hv.2.1 hmem
    · simp only [out, hget, Option.map_some, Option.getD_some]
      exact heq
  · congr 1
    exact Finset.sum_congr rfl fun R _ ↦ by beta_reduce; rw [hpost R]

/-- **Source-final-validity SM-DT-TCR in the QROM**, square-root form. -/
theorem tcr_fv_exact_sqrt_le [Inhabited Tw]
    (hx : IAdv.IsQueryBound n x (firstBudget q₁))
    (h2 : ∀ P u o, (ph2 P u o).IsQueryBound (secondBudget q₂)) :
    tcrFvExp I ρ cap n x ph2 ^ (2⁻¹ : ℝ) ≤
      ((2 * (q₂ : ℝ≥0∞) + 1) ^ 2 / (Fintype.card Y : ℝ≥0∞)) ^ (2⁻¹ : ℝ) +
        2 * q₁ * ((Fintype.card Sd : ℝ≥0∞)⁻¹) ^ (2⁻¹ : ℝ) :=
  (seed_hiding hx h2).trans
    (add_le_add (sqrt_le_sqrt (twoPhaseHyb_tcrFv_le hx h2)) le_rfl)

/-- **Source-final-validity SM-DT-TCR in the QROM**:
`Pr[win] ≤ (√((2 q₂ + 1)² / |Y|) + 2 q₁ / √|Sd|)²`. -/
theorem tcr_fv_exact_le [Inhabited Tw]
    (hx : IAdv.IsQueryBound n x (firstBudget q₁))
    (h2 : ∀ P u o, (ph2 P u o).IsQueryBound (secondBudget q₂)) :
    tcrFvExp I ρ cap n x ph2 ≤
      (((2 * (q₂ : ℝ≥0∞) + 1) ^ 2 / (Fintype.card Y : ℝ≥0∞)) ^ (2⁻¹ : ℝ) +
        2 * q₁ * ((Fintype.card Sd : ℝ≥0∞)⁻¹) ^ (2⁻¹ : ℝ)) ^ 2 := by
  have h := tcr_fv_exact_sqrt_le (I := I) (ρ := ρ) (cap := cap) hx h2
  calc tcrFvExp I ρ cap n x ph2 = (tcrFvExp I ρ cap n x ph2 ^ (2⁻¹ : ℝ)) ^ 2 :=
        (sq_sqrt _).symm
    _ ≤ _ := pow_le_pow_left' h 2

end Exp

end PQ.QROM

#print axioms PQ.QROM.twoPhaseHyb_tcrFv_le
#print axioms PQ.QROM.tcr_fv_exact_sqrt_le
#print axioms PQ.QROM.tcr_fv_exact_le
