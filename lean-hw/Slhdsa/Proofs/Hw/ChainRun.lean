import Slhdsa.Proofs.Hw.ChainLane
open Aeneas Aeneas.Std Result

/-! `period` and `run` of the hardware chain kernel. -/

namespace slhdsa
open Spec.SHA256

set_option linter.unusedSimpArgs false

theorem period_spec (hw : Arm.haveSha2 = true) (L PHASE : Usize) (abcd0 : U4) (slots : Array sha256.hw.Slot 4#usize)
    (p : U32) (s : sha256.hw.Lanes) (steps : Nat)
    (hL : L.val ≤ 4) (hs : 1 ≤ steps) (hph : PhaseOk PHASE.val p.val steps)
    (hov : ∀ l < L.val, (slots.val[l]!).t.val + steps ≤ U32.max)
    (hg : ∀ l < L.val, Good abcd0 (slots.val[l]!) (gidx (15 * l / L.val) steps (15 * p.val))
      (lane s l)) :
    sha256.hw.period L PHASE abcd0 slots p s ⦃ r =>
      ∀ l < L.val, Good abcd0 (slots.val[l]!) (gidx (15 * l / L.val) steps (15 * p.val + 15))
        (lane r l) ⦄ := by
  unfold sha256.hw.period
  step with tick_spec hw L PHASE 0#usize abcd0 slots p s steps hL (by decide) hs hph hov hg as ⟨s1, g1⟩
  step with tick_spec hw L PHASE 1#usize abcd0 slots p s1 steps hL (by decide) hs hph hov g1 as ⟨s2, g2⟩
  step with tick_spec hw L PHASE 2#usize abcd0 slots p s2 steps hL (by decide) hs hph hov g2 as ⟨s3, g3⟩
  step with tick_spec hw L PHASE 3#usize abcd0 slots p s3 steps hL (by decide) hs hph hov g3 as ⟨s4, g4⟩
  step with tick_spec hw L PHASE 4#usize abcd0 slots p s4 steps hL (by decide) hs hph hov g4 as ⟨s5, g5⟩
  step with tick_spec hw L PHASE 5#usize abcd0 slots p s5 steps hL (by decide) hs hph hov g5 as ⟨s6, g6⟩
  step with tick_spec hw L PHASE 6#usize abcd0 slots p s6 steps hL (by decide) hs hph hov g6 as ⟨s7, g7⟩
  step with tick_spec hw L PHASE 7#usize abcd0 slots p s7 steps hL (by decide) hs hph hov g7 as ⟨s8, g8⟩
  step with tick_spec hw L PHASE 8#usize abcd0 slots p s8 steps hL (by decide) hs hph hov g8 as ⟨s9, g9⟩
  step with tick_spec hw L PHASE 9#usize abcd0 slots p s9 steps hL (by decide) hs hph hov g9 as ⟨s10, g10⟩
  step with tick_spec hw L PHASE 10#usize abcd0 slots p s10 steps hL (by decide) hs hph hov g10 as ⟨s11, g11⟩
  step with tick_spec hw L PHASE 11#usize abcd0 slots p s11 steps hL (by decide) hs hph hov g11 as ⟨s12, g12⟩
  step with tick_spec hw L PHASE 12#usize abcd0 slots p s12 steps hL (by decide) hs hph hov g12 as ⟨s13, g13⟩
  step with tick_spec hw L PHASE 13#usize abcd0 slots p s13 steps hL (by decide) hs hph hov g13 as ⟨s14, g14⟩
  exact tick_spec hw L PHASE 14#usize abcd0 slots p s14 steps hL (by decide) hs hph hov g14

theorem gidx_zero (off steps : Nat) : gidx off steps (15 * 0) = 0 := by
  simp [gidx]

theorem gidx_end (off steps : Nat) (hoff : off < 15) :
    gidx off steps (15 * steps + 15) = 15 * steps := by
  unfold gidx; omega

theorem off_lt' (L l : Nat) (h : l < L) : 15 * l / L < 15 := off_lt L l h

theorem run_loop_spec (hw : Arm.haveSha2 = true) (L : Usize) (slots : Array sha256.hw.Slot 4#usize) (steps : U32) (abcd0 : U4)
    (s : sha256.hw.Lanes) (p : U32)
    (hL : L.val ≤ 4) (hp : 1 ≤ p.val ∧ p.val ≤ steps.val)
    (hov : ∀ l < L.val, (slots.val[l]!).t.val + steps.val ≤ U32.max)
    (hg : ∀ l < L.val, Good abcd0 (slots.val[l]!) (gidx (15 * l / L.val) steps.val (15 * p.val))
      (lane s l)) :
    sha256.hw.run_loop L slots steps abcd0 s p ⦃ r =>
      r.2.val = steps.val ∧
      ∀ l < L.val, Good abcd0 (slots.val[l]!) (gidx (15 * l / L.val) steps.val (15 * r.2.val))
        (lane r.1 l) ⦄ := by
  unfold sha256.hw.run_loop
  apply loop.spec_decr_nat
    (measure := fun (q : sha256.hw.Lanes × U32) => steps.val - q.2.val)
    (inv := fun q => (1 ≤ q.2.val ∧ q.2.val ≤ steps.val) ∧
      ∀ l < L.val, Good abcd0 (slots.val[l]!) (gidx (15 * l / L.val) steps.val (15 * q.2.val))
        (lane q.1 l))
  · rintro ⟨s, p⟩ ⟨hp, hg⟩
    simp only [sha256.hw.run_loop.body]
    simp only at hp hg
    split
    · step with period_spec hw L 1#usize abcd0 slots p s steps.val hL (by omega)
        (by unfold PhaseOk; right; left; scalar_tac) hov hg as ⟨s1, h1⟩
      step*
      refine ⟨by scalar_tac, by scalar_tac, ?_, by scalar_tac⟩
      rw [p1_post, show 15 * (p.val + 1) = 15 * p.val + 15 by ring]
      exact h1
    · simp only [WP.spec_ok]
      refine ⟨by scalar_tac, hg⟩
  · exact ⟨hp, hg⟩

/-- Slot `sl'` is slot `sl` after `k` more steps that left it at value `x`. -/
def Adv (sl sl' : sha256.hw.Slot) (x : Arm.V) (k : Nat) : Prop :=
  sl' = { sl with x := x, t := sl'.t } ∧ sl'.t.val = sl.t.val + k

@[step]
theorem advanced_spec (slot : sha256.hw.Slot) (x : U4) (steps : U32)
    (h : slot.t.val + steps.val ≤ U32.max) :
    sha256.hw.advanced slot x steps ⦃ r => Adv slot r x steps.val ⦄ := by
  unfold sha256.hw.advanced
  step*
  exact ⟨rfl, by simp [i_post]⟩

theorem getElem!_set_ite {α} [Inhabited α] (l : List α) (i j : Nat) (x : α) (h : i < l.length) :
    (l.set i x)[j]! = if i = j then x else l[j]! := by
  split
  · subst_vars; exact getElem!_set_self' _ _ _ h
  · exact getElem!_set_ne' _ _ _ _ (by assumption)

theorem run_finish (slots : Array sha256.hw.Slot 4#usize) (k : Nat) (hk : k < 4) (r : sha256.hw.Slot)
    (x : U4) (X : Arm.V) (steps : Nat) (hX : x = X)
    (h : Adv (slots.val[k]'(by simp; omega)) r x steps) : Adv (slots.val[k]!) r X steps := by
  rw [getElem!_eq _ _ (by simp; omega), ← hX]; exact h

theorem run_spec (hw : Arm.haveSha2 = true) (L : Usize) (state : Array U32 8#usize) (slots : Array sha256.hw.Slot 4#usize)
    (steps : U32) (hL1 : 1 ≤ L.val) (hL : L.val ≤ 4) (hs : 1 ≤ steps.val)
    (hov : ∀ l < L.val, (slots.val[l]!).t.val + steps.val ≤ U32.max) :
    sha256.hw.run L state slots steps ⦃ r => ∀ l < 4,
      (l < L.val → Adv (slots.val[l]!) (r.val[l]!)
        (Xseq (vOf (wv state.val) 0) (slots.val[l]!) steps.val) steps.val) ∧
      (¬ l < L.val → r.val[l]! = slots.val[l]!) ⦄ := by
  unfold sha256.hw.run
  step*
  step with period_spec hw L 0#usize abcd0 slots 0#u32
    ({ x := Array.make 4#usize [s1.x, s2.x, s3.x, s4.x], abcd := Array.repeat 4#usize z,
       efgh := Array.repeat 4#usize z, m := Array.repeat 4#usize (Array.repeat 4#usize z) } :
      sha256.hw.Lanes) steps.val hL hs
    (by unfold PhaseOk; left; simp) hov (by
      intro l hl
      have hl4 : l < 4 := by omega
      rw [show gidx (15 * l / L.val) steps.val (15 * (0#u32).val) = 0 by simp [gidx]]
      apply Good_zero
      simp only [lane, Array.make_val]
      interval_cases l
      · rw [s1_post, getElem!_eq slots.val 0 (by simp)]; rfl
      · rw [s2_post, getElem!_eq slots.val 1 (by simp)]; rfl
      · rw [s3_post, getElem!_eq slots.val 2 (by simp)]; rfl
      · rw [s4_post, getElem!_eq slots.val 3 (by simp)]; rfl) as ⟨s5, h5⟩
  step with run_loop_spec hw L slots steps abcd0 s5 1#u32 hL (by simp; omega) hov h5 as ⟨s6, p, hp, h6⟩
  step with period_spec hw L 2#usize abcd0 slots p s6 steps.val hL hs
    (by unfold PhaseOk; right; right; simp [hp]) hov h6 as ⟨s7, h7⟩
  have hx : ∀ l < L.val, s7.x.val[l]! = Xseq (vOf (wv state.val) 0) (slots.val[l]!) steps.val := by
    intro l hl
    have := Good_final _ _ _ _ (by
      have h := h7 l hl
      rwa [hp, gidx_end _ _ (off_lt' _ _ hl)] at h)
    rw [abcd0_post, s_post, Array.val_to_slice] at this
    exact this
  have hx' : ∀ l (hl : l < L.val), s7.x.val[l]'(by simp; omega) =
      Xseq (vOf (wv state.val) 0) (slots.val[l]!) steps.val := by
    intro l hl; rw [← getElem!_eq]; exact hx l hl
  rcases (by omega : L.val = 1 ∨ L.val = 2 ∨ L.val = 3 ∨ L.val = 4) with h | h | h | h
  · simp only [eq_true (show (0#usize < L) by scalar_tac), eq_false (show ¬ (1#usize < L) by scalar_tac), eq_false (show ¬ (2#usize < L) by scalar_tac), eq_false (show ¬ (3#usize < L) by scalar_tac),
      ↓reduceIte]
    step*
    all_goals subst_vars
    all_goals try simp only [Array.set_val_eq, show (0#usize : Usize).val = 0 from rfl, show (1#usize : Usize).val = 1 from rfl, show (2#usize : Usize).val = 2 from rfl, show (3#usize : Usize).val = 3 from rfl]
    all_goals try simp only [Array.set_val_eq, show (0#usize : Usize).val = 0 from rfl,
      show (1#usize : Usize).val = 1 from rfl, show (2#usize : Usize).val = 2 from rfl,
      show (3#usize : Usize).val = 3 from rfl, List.getElem_set_ne, ne_eq, Nat.reduceEqDiff,
      not_false_eq_true] at *
    all_goals first
      | (rw [← getElem!_eq slots.val _ (by simp)]; exact hov _ (by omega))
      | ((try intro l hl4)
         refine ⟨fun hk => ?_, fun hk => ?_⟩
         · interval_cases l <;> (try omega) <;>
             (repeat rw [getElem!_set_ite _ _ _ _ (by simp)]) <;>
             exact run_finish slots _ (by omega) _ _ _ _ (hx' _ (by omega)) (by assumption)
         · interval_cases l <;> (try omega) <;>
             (repeat rw [getElem!_set_ite _ _ _ _ (by simp)]) <;> rfl)
  · simp only [eq_true (show (0#usize < L) by scalar_tac), eq_true (show (1#usize < L) by scalar_tac), eq_false (show ¬ (2#usize < L) by scalar_tac), eq_false (show ¬ (3#usize < L) by scalar_tac),
      ↓reduceIte]
    step*
    all_goals subst_vars
    all_goals try simp only [Array.set_val_eq, show (0#usize : Usize).val = 0 from rfl, show (1#usize : Usize).val = 1 from rfl, show (2#usize : Usize).val = 2 from rfl, show (3#usize : Usize).val = 3 from rfl]
    all_goals try simp only [Array.set_val_eq, show (0#usize : Usize).val = 0 from rfl,
      show (1#usize : Usize).val = 1 from rfl, show (2#usize : Usize).val = 2 from rfl,
      show (3#usize : Usize).val = 3 from rfl, List.getElem_set_ne, ne_eq, Nat.reduceEqDiff,
      not_false_eq_true] at *
    all_goals first
      | (rw [← getElem!_eq slots.val _ (by simp)]; exact hov _ (by omega))
      | ((try intro l hl4)
         refine ⟨fun hk => ?_, fun hk => ?_⟩
         · interval_cases l <;> (try omega) <;>
             (repeat rw [getElem!_set_ite _ _ _ _ (by simp)]) <;>
             exact run_finish slots _ (by omega) _ _ _ _ (hx' _ (by omega)) (by assumption)
         · interval_cases l <;> (try omega) <;>
             (repeat rw [getElem!_set_ite _ _ _ _ (by simp)]) <;> rfl)
  · simp only [eq_true (show (0#usize < L) by scalar_tac), eq_true (show (1#usize < L) by scalar_tac), eq_true (show (2#usize < L) by scalar_tac), eq_false (show ¬ (3#usize < L) by scalar_tac),
      ↓reduceIte]
    step*
    all_goals subst_vars
    all_goals try simp only [Array.set_val_eq, show (0#usize : Usize).val = 0 from rfl, show (1#usize : Usize).val = 1 from rfl, show (2#usize : Usize).val = 2 from rfl, show (3#usize : Usize).val = 3 from rfl]
    all_goals try simp only [Array.set_val_eq, show (0#usize : Usize).val = 0 from rfl,
      show (1#usize : Usize).val = 1 from rfl, show (2#usize : Usize).val = 2 from rfl,
      show (3#usize : Usize).val = 3 from rfl, List.getElem_set_ne, ne_eq, Nat.reduceEqDiff,
      not_false_eq_true] at *
    all_goals first
      | (rw [← getElem!_eq slots.val _ (by simp)]; exact hov _ (by omega))
      | ((try intro l hl4)
         refine ⟨fun hk => ?_, fun hk => ?_⟩
         · interval_cases l <;> (try omega) <;>
             (repeat rw [getElem!_set_ite _ _ _ _ (by simp)]) <;>
             exact run_finish slots _ (by omega) _ _ _ _ (hx' _ (by omega)) (by assumption)
         · interval_cases l <;> (try omega) <;>
             (repeat rw [getElem!_set_ite _ _ _ _ (by simp)]) <;> rfl)
  · simp only [eq_true (show (0#usize < L) by scalar_tac), eq_true (show (1#usize < L) by scalar_tac), eq_true (show (2#usize < L) by scalar_tac), eq_true (show (3#usize < L) by scalar_tac),
      ↓reduceIte]
    step*
    all_goals subst_vars
    all_goals try simp only [Array.set_val_eq, show (0#usize : Usize).val = 0 from rfl, show (1#usize : Usize).val = 1 from rfl, show (2#usize : Usize).val = 2 from rfl, show (3#usize : Usize).val = 3 from rfl]
    all_goals try simp only [Array.set_val_eq, show (0#usize : Usize).val = 0 from rfl,
      show (1#usize : Usize).val = 1 from rfl, show (2#usize : Usize).val = 2 from rfl,
      show (3#usize : Usize).val = 3 from rfl, List.getElem_set_ne, ne_eq, Nat.reduceEqDiff,
      not_false_eq_true] at *
    all_goals first
      | (rw [← getElem!_eq slots.val _ (by simp)]; exact hov _ (by omega))
      | ((try intro l hl4)
         refine ⟨fun hk => ?_, fun hk => ?_⟩
         · interval_cases l <;> (try omega) <;>
             (repeat rw [getElem!_set_ite _ _ _ _ (by simp)]) <;>
             exact run_finish slots _ (by omega) _ _ _ _ (hx' _ (by omega)) (by assumption)
         · interval_cases l <;> (try omega) <;>
             (repeat rw [getElem!_set_ite _ _ _ _ (by simp)]) <;> rfl)


end slhdsa
