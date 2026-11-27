import Armwide.Funs
import Spec.SlhDsa

open ArmwideRust Aeneas Aeneas.Std Result

/-!
# Longest-First Bucket-Sorted Dynamic 4-Lane Refill WOTS+ Scheduler (`Armwide.WotsRefill`)

Formally verifies the bucket-sorted dynamic lane-refill WOTS+ scheduling logic
in `rust/src/sha256/arm_wide.rs`:

1. **`sort_descending_spec`** (directly on Aeneas-extracted
   `sha256.arm_wide.sort_descending`): proves that bucket-sorting `weights`
   (`weights[i] ∈ 0..=15`, `weights.length ≤ 67`) produces a duplicate-free list
   of exactly `{ c < weights.length | weights[c] > 0 }` in descending order of
   weight, with zero arithmetic or index overflows.
2. **`recover_scheduler_eq_fips`** & **`recover_with_extracted_sort`**: proves
   that the `wots_recover` scheduler — copying `digit == 15` directly, filling
   up to 4 lanes from the sorted queue, running `min_left` lockstep chain
   iterations, retiring finished lanes (`left == 0`) to their original chain
   index, refilling from the queue, compacting, and draining the 1..3-lane tail
   — computes exact FIPS 205 `Spec.chain` for every chain `0 ≤ c < len`
   (including `digit == 0` and `digit == 15` edge cases).
3. **`sign_fused_scheduler_eq_fips`** (with `sign_fused_digit_zero` and
   `sign_fused_digit_fifteen` edge-case corollaries): proves that the
   `wots_sign_fused` scheduler — bucket-sorting all `len` chains by `digits[c]`,
   fusing `PRF` and `chain` steps with the fast `min_left` lockstep path when
   all 4 lanes are in the `WOTS_HASH` phase, the 1-step mixed `PRF`/`HASH` path,
   retiring finished lanes (`left == 0`, including immediate retirement after
   `PRF` when `digit == 0`), refilling, compacting, and draining the tail —
   computes exact FIPS 205 `Spec.chain (Spec.PRF ...)` for every chain `0 ≤ c < len`.
-/

namespace slhdsa.Armwide.WotsRefill

/-! ## Part 1: Verification of Aeneas-extracted `sha256::arm_wide::sort_descending` -/

/-- Number of indices `j < n` with `weights[j] = b`. -/
def countEq (ws : List U32) (n b : Nat) : Nat :=
  ((List.range n).filter fun j => (ws[j]!).val == b).length

/-- Number of indices `j < ws.length` with `weights[j] > b`. -/
def countGt (ws : List U32) (b : Nat) : Nat :=
  ((List.range ws.length).filter fun j => b < (ws[j]!).val).length

/-- Exact target slot in `order` of chain index `c` (when `weights[c] > 0`). -/
def slotOf (ws : List U32) (c : Nat) : Nat :=
  countGt ws (ws[c]!).val + countEq ws c (ws[c]!).val

theorem countEq_zero (ws : List U32) (b : Nat) : countEq ws 0 b = 0 := rfl

theorem countEq_succ (ws : List U32) (n b : Nat) :
    countEq ws (n + 1) b = countEq ws n b + if (ws[n]!).val = b then 1 else 0 := by
  unfold countEq
  rw [List.range_succ, List.filter_append, List.length_append]
  simp only [List.filter_cons, List.filter_nil, beq_iff_eq]
  split <;> simp

theorem countEq_le (ws : List U32) (n b : Nat) : countEq ws n b ≤ n := by
  unfold countEq
  calc ((List.range n).filter _).length ≤ (List.range n).length := List.length_filter_le _ _
    _ = n := List.length_range

private theorem countEq_mono (ws : List U32) {m n : Nat} (h : m ≤ n) (b : Nat) :
    countEq ws m b ≤ countEq ws n b := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => rw [countEq_succ]; omega

theorem countEq_strict_mono (ws : List U32) {c1 c2 : Nat} (h : c1 < c2) (b : Nat)
    (hc1 : (ws[c1]!).val = b) :
    countEq ws c1 b < countEq ws c2 b := by
  have h1 : countEq ws (c1 + 1) b ≤ countEq ws c2 b := countEq_mono ws (by omega) b
  rw [countEq_succ, ite_eq_left hc1] at h1
  omega

theorem countGt_15 (ws : List U32) (hb : ∀ j < ws.length, (ws[j]!).val ≤ 15) :
    countGt ws 15 = 0 := by
  unfold countGt
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro j hj
  simp only [List.mem_range] at hj
  have hle := hb j hj
  simp only [decide_eq_true_eq, not_lt]
  exact hle

theorem filter_disjoint_add {α} (l : List α) (p q : α → Bool)
    (hdisj : ∀ x ∈ l, !(p x && q x)) :
    (l.filter fun x => p x || q x).length = (l.filter p).length + (l.filter q).length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have hd := hdisj a (by simp)
    have ih' := ih (fun x hx => hdisj x (by simp [hx]))
    cases hp : p a <;> cases hq : q a <;> simp_all <;> omega

theorem countGt_step (ws : List U32) (b : Nat) (hb : 1 ≤ b) :
    countGt ws (b - 1) = countGt ws b + countEq ws ws.length b := by
  unfold countGt countEq
  have hpred : (fun j : Nat => decide (b - 1 < (ws[j]!).val)) =
      (fun j : Nat => decide (b < (ws[j]!).val) || ((ws[j]!).val == b)) := by
    funext j
    generalize (ws[j]!).val = v
    by_cases h1 : b < v
    · simp [h1, show b - 1 < v by omega]
    · by_cases h2 : v = b
      · simp [h1, h2, show b - 1 < b by omega]
      · simp [h1, h2, show ¬(b - 1 < v) by omega]
  rw [hpred]
  exact filter_disjoint_add (List.range ws.length) _ _ fun j _ => by
    generalize (ws[j]!).val = v
    by_cases h : b < v <;> simp [h]; omega

private theorem countGt_le_len (ws : List U32) (b : Nat) : countGt ws b ≤ ws.length := by
  unfold countGt
  calc ((List.range ws.length).filter _).length ≤ (List.range ws.length).length := List.length_filter_le _ _
    _ = ws.length := List.length_range

private theorem countGt_antitone (ws : List U32) {b1 b2 : Nat} (h : b1 ≤ b2) :
    countGt ws b2 ≤ countGt ws b1 := by
  induction h with
  | refl => exact le_rfl
  | @step m hm ih =>
    have hs := countGt_step ws (m + 1) (by omega)
    simp only [Nat.add_sub_cancel] at hs
    have hsucc : Nat.succ m = m + 1 := rfl
    rw [hsucc]; omega

private theorem slotOf_lt_total (ws : List U32) (c : Nat) (hc : c < ws.length)
    (hw : 0 < (ws[c]!).val) :
    slotOf ws c < countGt ws 0 := by
  unfold slotOf
  have h1 : countEq ws c (ws[c]!).val < countEq ws ws.length (ws[c]!).val :=
    countEq_strict_mono ws hc (ws[c]!).val rfl
  have h2 := countGt_step ws (ws[c]!).val hw
  have h3 := countGt_antitone ws (Nat.zero_le ((ws[c]!).val - 1))
  omega

private theorem slotOf_lt_of_gt (ws : List U32) {c1 c2 : Nat} (hc1 : c1 < ws.length)
    (hgt : (ws[c2]!).val < (ws[c1]!).val) :
    slotOf ws c1 < slotOf ws c2 := by
  unfold slotOf
  have h1 : countEq ws c1 (ws[c1]!).val < countEq ws ws.length (ws[c1]!).val :=
    countEq_strict_mono ws hc1 (ws[c1]!).val rfl
  have h2 := countGt_step ws (ws[c1]!).val (by omega)
  have h3 := countGt_antitone ws (show (ws[c2]!).val ≤ (ws[c1]!).val - 1 by omega)
  omega

theorem slotOf_inj (ws : List U32) {c1 c2 : Nat} (hc1 : c1 < ws.length) (hc2 : c2 < ws.length)
    (heq : slotOf ws c1 = slotOf ws c2) : c1 = c2 := by
  by_cases hlt : (ws[c1]!).val < (ws[c2]!).val
  · have := slotOf_lt_of_gt ws hc2 hlt; omega
  · by_cases hgt : (ws[c2]!).val < (ws[c1]!).val
    · have := slotOf_lt_of_gt ws hc1 hgt; omega
    · have hw : (ws[c1]!).val = (ws[c2]!).val := by omega
      by_cases h1 : c1 < c2
      · have hsm := countEq_strict_mono ws h1 (ws[c1]!).val rfl
        unfold slotOf at heq; rw [hw] at heq hsm; omega
      · by_cases h2 : c2 < c1
        · have hsm := countEq_strict_mono ws h2 (ws[c2]!).val rfl
          unfold slotOf at heq; rw [← hw] at heq hsm; omega
        · omega

private theorem slotOf_surj_bucket (ws : List U32) (n b k : Nat) (hk : k < countEq ws n b) :
    ∃ c < n, (ws[c]!).val = b ∧ countEq ws c b = k := by
  induction n with
  | zero => simp [countEq_zero] at hk
  | succ n ih =>
    rw [countEq_succ] at hk
    by_cases h : (ws[n]!).val = b
    · rw [ite_eq_left h] at hk
      by_cases hk' : k < countEq ws n b
      · obtain ⟨c, hc, hwc, heq⟩ := ih hk'
        exact ⟨c, by omega, hwc, heq⟩
      · exact ⟨n, by omega, h, by omega⟩
    · rw [ite_eq_right h] at hk
      obtain ⟨c, hc, hwc, heq⟩ := ih (by omega)
      exact ⟨c, by omega, hwc, heq⟩

private theorem slotOf_surj (ws : List U32) (hb : ∀ j < ws.length, (ws[j]!).val ≤ 15)
    (p : Nat) (hp : p < countGt ws 0) :
    ∃ c < ws.length, 0 < (ws[c]!).val ∧ slotOf ws c = p := by
  have hex : ∀ m ≤ 15, countGt ws m ≤ p → p < countGt ws 0 →
      ∃ b, 1 ≤ b ∧ b ≤ m ∧ countGt ws b ≤ p ∧ p < countGt ws (b - 1) := by
    intro m hm
    induction m with
    | zero => intro h1 h2; omega
    | succ m ih =>
      intro hlo hhi
      by_cases hlt : p < countGt ws m
      · exact ⟨m + 1, by omega, le_rfl, hlo, by simpa using hlt⟩
      · obtain ⟨b, hb1, hb2, h3, h4⟩ := ih (by omega) (by omega) hhi
        exact ⟨b, hb1, by omega, h3, h4⟩
  obtain ⟨b, hb1, _, hlo, hhi⟩ := hex 15 le_rfl (by rw [countGt_15 ws hb]; omega) hp
  have hstep := countGt_step ws b hb1
  obtain ⟨c, hc, hwc, heq⟩ := slotOf_surj_bucket ws ws.length b (p - countGt ws b) (by omega)
  refine ⟨c, hc, by omega, ?_⟩
  unfold slotOf
  rw [hwc, heq]
  omega

private theorem sort_loop0_spec (weights : Slice U32) (hlen : weights.length ≤ 67)
    (hb : ∀ j < weights.length, (weights.val[j]!).val ≤ 15) :
    sha256.arm_wide.sort_descending_loop0 ⟨weights, 0⟩ (Array.repeat 16#usize 0#u8) ⦃ counts =>
      ∀ b, 1 ≤ b → b ≤ 15 → (counts.val[b]!).val = countEq weights.val weights.length b ⦄ := by
  unfold sha256.arm_wide.sort_descending_loop0
  apply loop.spec_decr_nat
    (measure := fun (p : core.slice.iter.Iter U32 × Array U8 16#usize) => weights.length - p.1.i)
    (inv := fun p => p.1.slice = weights ∧ p.1.i ≤ weights.length ∧
      ∀ b, 1 ≤ b → b ≤ 15 → (p.2.val[b]!).val = countEq weights.val p.1.i b)
  · rintro ⟨it, counts⟩ ⟨hslice, hi, hcnt⟩
    unfold sha256.arm_wide.sort_descending_loop0.body
    simp only at hslice hi hcnt ⊢
    by_cases more : it.i < weights.length
    · let next := { it with i := it.i + 1 }
      have hnext : core.slice.iter.IteratorSliceIter.next it = ok (some weights.val[it.i], next) := by
        simp [core.slice.iter.IteratorSliceIter.next, next, hslice, more]
      rw [hnext]; simp only [step_simps]
      have hw_get : (weights.val[it.i]!).val = (weights.val[it.i]).val := by
        rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem more]; rfl
      have hw_le : (weights.val[it.i]).val ≤ 15 := by
        rw [← hw_get]; exact hb it.i more
      spec_split
      · have hw_pos : 1 ≤ (weights.val[it.i]).val := by scalar_tac
        let* ⟨ i, i_post ⟩ ← UScalar.cast.step_spec
        have hi_val : i.val = (weights.val[it.i]).val := by simp [i_post]
        let* ⟨ i1, i1_post ⟩ ← Array.index_usize_spec
        have hi1_val : i1.val = countEq weights.val it.i (weights.val[it.i]).val := by
          have := hcnt (weights.val[it.i]).val hw_pos hw_le
          have hget : counts.val[i.val]'(by simp; omega) = counts.val[(weights.val[it.i]).val]! := by
            rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (by simp; omega), Option.getD_some]
            have hidx : ∀ (a b : Nat) (ha : a < counts.val.length) (hb : b < counts.val.length),
                a = b → counts.val[a] = counts.val[b] := fun _ _ _ _ h => by subst h; rfl
            exact hidx _ _ _ _ hi_val
          rw [← this, i1_post, hget]
        have hi1_le : i1.val ≤ 67 := by
          have := countEq_le weights.val it.i (weights.val[it.i]).val
          omega
        let* ⟨ i2, i2_post ⟩ ← U8.add_spec
        let* ⟨ a, a_post ⟩ ← Array.update_spec
        have ha_val : a.val = counts.val.set (weights.val[it.i]).val i2 := by
          rw [a_post, Array.set_val_eq, hi_val]
        refine ⟨hslice, by change it.i + 1 ≤ weights.length; omega, ?_,
          by change weights.length - (it.i + 1) < weights.length - it.i; omega⟩
        intro b hb1 hb2
        change (a.val[b]!).val = countEq weights.val (it.i + 1) b
        rw [countEq_succ, hw_get]
        by_cases hbw : b = (weights.val[it.i]).val
        · subst hbw
          rw [ite_eq_left rfl, ha_val, List.getElem!_eq_getElem?_getD,
            List.getElem?_set_self (by simp; omega)]
          simp [i2_post, hi1_val]
        · rw [ite_eq_right (Ne.symm hbw), ha_val, List.getElem!_eq_getElem?_getD,
            List.getElem?_set_ne (by omega)]
          simpa [List.getElem!_eq_getElem?_getD] using hcnt b hb1 hb2
      · simp only [step_simps]
        have hw0 : (weights.val[it.i]).val = 0 := by scalar_tac
        refine ⟨hslice, by change it.i + 1 ≤ weights.length; omega, ?_,
          by change weights.length - (it.i + 1) < weights.length - it.i; omega⟩
        intro b hb1 hb2
        change (counts.val[b]!).val = countEq weights.val (it.i + 1) b
        rw [countEq_succ, hw_get, ite_eq_right (by omega), Nat.add_zero]
        exact hcnt b hb1 hb2
    · have hdone : core.slice.iter.IteratorSliceIter.next it = ok (none, it) := by
        simp [core.slice.iter.IteratorSliceIter.next, hslice, more, Slice.length] at *
      rw [hdone]; simp only [step_simps]
      have hie : it.i = weights.length := by omega
      simpa [hie] using hcnt
  · refine ⟨rfl, Nat.zero_le _, fun b hb1 hb2 => ?_⟩
    simp only [Array.repeat_val, List.getElem!_eq_getElem?_getD, List.getElem?_replicate,
      show b < (16#usize).val by scalar_tac, ↓reduceIte, countEq_zero]
    rfl

private theorem sort_loop1_spec (ws : List U32) (hlen : ws.length ≤ 67)
    (hb : ∀ j < ws.length, (ws[j]!).val ≤ 15)
    (counts : Array U8 16#usize)
    (hcnt : ∀ b, 1 ≤ b → b ≤ 15 → (counts.val[b]!).val = countEq ws ws.length b) :
    sha256.arm_wide.sort_descending_loop1 counts (Array.repeat 16#usize 0#usize) 0#usize 15#usize ⦃ r =>
      r.2.val = countGt ws 0 ∧
      ∀ k, 1 ≤ k → k ≤ 15 → (r.1.val[k]!).val = countGt ws k ⦄ := by
  unfold sha256.arm_wide.sort_descending_loop1
  apply loop.spec_decr_nat
    (measure := fun (p : Array Usize 16#usize × Usize × Usize) => p.2.2.val)
    (inv := fun p => p.2.2.val ≤ 15 ∧ p.2.1.val = countGt ws p.2.2.val ∧
      ∀ k, p.2.2.val < k → k ≤ 15 → (p.1.val[k]!).val = countGt ws k)
  · rintro ⟨offsets, total, b⟩ ⟨hb15, htot, hoff⟩
    unfold sha256.arm_wide.sort_descending_loop1.body
    simp only at hb15 htot hoff ⊢
    spec_split
    · have hb1 : 1 ≤ b.val := by scalar_tac
      let* ⟨ a, a_post ⟩ ← Array.update_spec
      let* ⟨ i, i_post ⟩ ← Array.index_usize_spec
      let* ⟨ i1, i1_post ⟩ ← UScalar.cast.step_spec
      have hi_val : i1.val = countEq ws ws.length b.val := by
        have hc := hcnt b.val hb1 hb15
        have h1 : i1.val = i.val := by simp [i1_post]
        rw [h1, i_post, ← hc, List.getElem!_eq_getElem?_getD,
          List.getElem?_eq_getElem (by simp; omega)]
        rfl
      have htot_next : total.val + i1.val = countGt ws (b.val - 1) := by
        rw [htot, hi_val, countGt_step ws b.val hb1]
      have htot_le : total.val + i1.val ≤ 67 := by
        rw [htot_next]; have := countGt_le_len ws (b.val - 1); omega
      let* ⟨ total1, total1_post ⟩ ← Usize.add_spec
      let* ⟨ b1, b1_post, b1_post1 ⟩ ← Usize.sub_spec
      have ha_val : a.val = offsets.val.set b.val total := by
        rw [a_post, Array.set_val_eq]
      refine ⟨by scalar_tac, ?_, ?_, by scalar_tac⟩
      · rw [total1_post, htot_next, b1_post]
      · intro k hk1 hk2
        have hcases : k = b.val ∨ b.val < k := by scalar_tac
        rcases hcases with rfl | hgt
        · rw [ha_val, List.getElem!_eq_getElem?_getD, List.getElem?_set_self (by simp; omega)]
          simpa using htot
        · rw [ha_val, List.getElem!_eq_getElem?_getD, List.getElem?_set_ne (by omega)]
          simpa [List.getElem!_eq_getElem?_getD] using hoff k hgt hk2
    · simp only [step_simps]
      have hb0 : b.val = 0 := by scalar_tac
      rw [hb0] at htot hoff
      exact ⟨htot, fun k hk1 hk2 => hoff k (by omega) hk2⟩
  · refine ⟨by decide, ?_, fun k hk1 hk2 => by scalar_tac⟩
    simp [countGt_15 ws hb]

private theorem sort_loop2_spec (weights : Slice U32) (hlen : weights.length ≤ 67)
    (hb : ∀ j < weights.length, (weights.val[j]!).val ≤ 15)
    (order : Array U8 67#usize) (offsets : Array Usize 16#usize)
    (hoff : ∀ k, 1 ≤ k → k ≤ 15 → (offsets.val[k]!).val = countGt weights.val k) :
    sha256.arm_wide.sort_descending_loop2 ⟨⟨weights, 0⟩, 0#usize⟩ order offsets ⦃ order' =>
      ∀ c < weights.length, 0 < (weights.val[c]!).val →
        (order'.val[slotOf weights.val c]!).val = c ⦄ := by
  unfold sha256.arm_wide.sort_descending_loop2
  apply loop.spec_decr_nat
    (measure := fun (p : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter U32) ×
        Array U8 67#usize × Array Usize 16#usize) => weights.length - p.1.iter.i)
    (inv := fun p => p.1.iter.slice = weights ∧ p.1.iter.i ≤ weights.length ∧
      p.1.count.val = p.1.iter.i ∧
      (∀ k, 1 ≤ k → k ≤ 15 → (p.2.2.val[k]!).val = countGt weights.val k + countEq weights.val p.1.iter.i k) ∧
      (∀ c < p.1.iter.i, 0 < (weights.val[c]!).val →
        (p.2.1.val[slotOf weights.val c]!).val = c))
  · rintro ⟨it, ord, offs⟩ ⟨hslice, hi, hcnt, hoffs, hord⟩
    unfold sha256.arm_wide.sort_descending_loop2.body
    simp only at hslice hi hcnt hoffs hord ⊢
    by_cases more : it.iter.i < weights.length
    · let nextInner : core.slice.iter.Iter U32 := { it.iter with i := it.iter.i + 1 }
      have hinner : core.slice.iter.IteratorSliceIter.next it.iter = ok (some weights.val[it.iter.i], nextInner) := by
        simp [core.slice.iter.IteratorSliceIter.next, nextInner, hslice, more]
      dsimp only [core.iter.adapters.enumerate.IteratorEnumerate.next,
        core.iter.traits.iterator.IteratorSliceIter]
      rw [hinner]
      simp only [bind_ok, bind_assoc]
      let* ⟨ cnt', cnt'_post ⟩ ← Usize.add_spec
      have hw_get : (weights.val[it.iter.i]!).val = (weights.val[it.iter.i]).val := by
        rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem more]; rfl
      have hw_le : (weights.val[it.iter.i]).val ≤ 15 := by
        rw [← hw_get]; exact hb it.iter.i more
      spec_split
      · have hw_pos : 1 ≤ (weights.val[it.iter.i]).val := by scalar_tac
        let* ⟨ i1, i1_post ⟩ ← UScalar.cast.step_spec
        have hi1_val : i1.val = (weights.val[it.iter.i]).val := by simp [i1_post]
        let* ⟨ pos, pos_post ⟩ ← Array.index_usize_spec
        have hpos_val : pos.val = slotOf weights.val it.iter.i := by
          have ho := hoffs (weights.val[it.iter.i]).val hw_pos hw_le
          have hp : pos.val = (offs.val[(weights.val[it.iter.i]).val]!).val := by
            have hget : offs.val[i1.val]'(by simp; omega) = offs.val[(weights.val[it.iter.i]).val]! := by
              rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (by simp; omega), Option.getD_some]
              have hidx : ∀ (a b : Nat) (ha : a < offs.val.length) (hb : b < offs.val.length),
                  a = b → offs.val[a] = offs.val[b] := fun _ _ _ _ h => by subst h; rfl
              exact hidx _ _ _ _ hi1_val
            rw [pos_post, hget]
          rw [hp, ho]; unfold slotOf; rw [hw_get]
        have hwl : weights.val.length = weights.length := rfl
        have hpos_lt : pos.val < 67 := by
          rw [hpos_val]
          have h1 := slotOf_lt_total weights.val it.iter.i more (by omega)
          have h2 := countGt_le_len weights.val 0
          omega
        let* ⟨ i2, i2_post ⟩ ← UScalar.cast.step_spec
        have hi2_val : i2.val = it.iter.i := by
          simp [i2_post, hcnt, Nat.mod_eq_of_lt (by omega : it.iter.i < 256)]
        let* ⟨ a, a_post ⟩ ← Array.update_spec
        let* ⟨ i3, i3_post ⟩ ← Usize.add_spec
        let* ⟨ i4, i4_post ⟩ ← UScalar.cast.step_spec
        have hi4_val : i4.val = (weights.val[it.iter.i]).val := by simp [i4_post]
        let* ⟨ a1, a1_post ⟩ ← Array.update_spec
        have ha_val : a.val = ord.val.set pos.val i2 := by rw [a_post, Array.set_val_eq]
        have ha1_val : a1.val = offs.val.set (weights.val[it.iter.i]).val i3 := by
          rw [a1_post, Array.set_val_eq, hi4_val]
        refine ⟨hslice, by change it.iter.i + 1 ≤ weights.length; omega,
          by change cnt'.val = it.iter.i + 1; omega, ?_, ?_,
          by change weights.length - (it.iter.i + 1) < weights.length - it.iter.i; omega⟩
        · intro k hk1 hk2
          change (a1.val[k]!).val = countGt weights.val k + countEq weights.val (it.iter.i + 1) k
          rw [countEq_succ, hw_get]
          by_cases hkw : k = (weights.val[it.iter.i]).val
          · subst hkw
            rw [ite_eq_left rfl, ha1_val, List.getElem!_eq_getElem?_getD,
              List.getElem?_set_self (by simp; omega)]
            simp only [Option.getD_some, i3_post, hpos_val]
            unfold slotOf; rw [hw_get]; omega
          · rw [ite_eq_right (Ne.symm hkw), Nat.add_zero, ha1_val, List.getElem!_eq_getElem?_getD,
              List.getElem?_set_ne (by omega)]
            simpa [List.getElem!_eq_getElem?_getD] using hoffs k hk1 hk2
        · intro c hc hwc
          have hc' : c < it.iter.i + 1 := hc
          rcases Nat.lt_succ_iff_lt_or_eq.mp hc' with hlt | rfl
          · have hne : pos.val ≠ slotOf weights.val c := by
              rw [hpos_val]
              intro heq
              have := slotOf_inj weights.val more (by omega) heq
              omega
            rw [ha_val, List.getElem!_eq_getElem?_getD, List.getElem?_set_ne hne]
            simpa [List.getElem!_eq_getElem?_getD] using hord c hlt hwc
          · rw [← hpos_val, ha_val, List.getElem!_eq_getElem?_getD,
              List.getElem?_set_self (by simp; omega)]
            simpa using hi2_val
      · simp only [step_simps]
        have hw0 : (weights.val[it.iter.i]).val = 0 := by scalar_tac
        refine ⟨hslice, by change it.iter.i + 1 ≤ weights.length; omega,
          by change cnt'.val = it.iter.i + 1; omega, ?_, ?_,
          by change weights.length - (it.iter.i + 1) < weights.length - it.iter.i; omega⟩
        · intro k hk1 hk2
          change (offs.val[k]!).val = countGt weights.val k + countEq weights.val (it.iter.i + 1) k
          rw [countEq_succ, hw_get, ite_eq_right (by omega), Nat.add_zero]
          exact hoffs k hk1 hk2
        · intro c hc hwc
          have hc' : c < it.iter.i + 1 := hc
          rcases Nat.lt_succ_iff_lt_or_eq.mp hc' with hlt | rfl
          · exact hord c hlt hwc
          · omega
    · have hinner : core.slice.iter.IteratorSliceIter.next it.iter = ok (none, it.iter) := by
        simp [core.slice.iter.IteratorSliceIter.next, hslice, more, Slice.length] at *
      have henum : core.iter.adapters.enumerate.IteratorEnumerate.next
          (core.iter.traits.iterator.IteratorSliceIter U32) it = ok (none, it) := by
        simp [core.iter.adapters.enumerate.IteratorEnumerate.next,
          core.iter.traits.iterator.IteratorSliceIter, hinner]
      rw [henum]; simp only [step_simps]
      have hie : it.iter.i = weights.length := by omega
      simpa [hie] using hord
  · refine ⟨rfl, Nat.zero_le _, rfl, fun k hk1 hk2 => ?_, fun _ hc => by change _ < 0 at hc; omega⟩
    simp only [countEq_zero, Nat.add_zero]
    exact hoff k hk1 hk2

/-- **Extracted Rust `sort_descending` specification**:
Given any slice `weights` of length `≤ 67` with entries in `0..=15`,
`sha256::arm_wide::sort_descending` succeeds without panic or overflow and
returns `(total, order')` such that `ord := (order'.val.take total.val).map (·.val)`
is a duplicate-free list containing exactly `{ c < weights.length | weights[c] > 0 }`,
sorted in descending order of `weights`. -/
theorem sort_descending_spec (weights : Slice U32) (order : Array U8 67#usize)
    (hlen : weights.length ≤ 67) (hb : ∀ j < weights.length, (weights.val[j]!).val ≤ 15) :
    sha256.arm_wide.sort_descending weights order ⦃ r =>
      let ord := (r.2.val.take r.1.val).map (·.val)
      r.1.val ≤ weights.length ∧
      ord.length = r.1.val ∧
      ord.Nodup ∧
      (∀ c, c ∈ ord ↔ c < weights.length ∧ 0 < (weights.val[c]!).val) ∧
      (∀ i j, i < j → j < ord.length →
        (weights.val[ord[j]!]!).val ≤ (weights.val[ord[i]!]!).val) ⦄ := by
  unfold sha256.arm_wide.sort_descending
  simp only [SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter,
    core.slice.Slice.iter, core.iter.traits.iterator.Iterator.enumerate.trait_default,
    core.iter.traits.iterator.Iterator.enumerate.default, bind_ok]
  step with sort_loop0_spec weights hlen hb as ⟨counts1, hcnt⟩
  step with sort_loop1_spec weights.val hlen hb counts1 hcnt as ⟨offsets1, total, htot, hoff⟩
  step with sort_loop2_spec weights hlen hb order offsets1 hoff as ⟨order1, hord⟩
  set ord := (order1.val.take total.val).map (·.val)
  have htot_le : total.val ≤ weights.length := by rw [htot]; exact countGt_le_len weights.val 0
  have htot_67 : total.val ≤ 67 := by omega
  have hord_len : ord.length = total.val := by simp [ord, htot_67]
  have hget_pos : ∀ p < total.val,
      ∃ c < weights.length, 0 < (weights.val[c]!).val ∧ slotOf weights.val c = p ∧ ord[p]! = c := by
    intro p hp
    obtain ⟨c, hc, hwc, hslot⟩ := slotOf_surj weights.val hb p (by rw [← htot]; exact hp)
    refine ⟨c, hc, hwc, hslot, ?_⟩
    have hp_ord : p < ord.length := by omega
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hp_ord]
    simp only [Option.getD_some, ord, List.getElem_map, List.getElem_take]
    have h1 := hord c hc hwc
    rw [hslot, List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (by simp; omega)] at h1
    exact h1
  refine ⟨htot_le, hord_len, ?_, ?_, ?_⟩
  · rw [List.nodup_iff_injective_getElem]
    intro ⟨i, hi⟩ ⟨j, hj⟩ heq
    simp only [Fin.mk.injEq]
    obtain ⟨ci, hci, _, hsi, hgi⟩ := hget_pos i (by omega)
    obtain ⟨cj, hcj, _, hsj, hgj⟩ := hget_pos j (by omega)
    have h1 : ord[i] = ci := by
      simpa [List.getElem!_eq_getElem?_getD, hi] using hgi
    have h2 : ord[j] = cj := by
      simpa [List.getElem!_eq_getElem?_getD, hj] using hgj
    dsimp only at heq
    have hceq : ci = cj := by rw [← h1, ← h2, heq]
    rw [← hsi, ← hsj, hceq]
  · intro c
    constructor
    · intro hmem
      rw [List.mem_iff_getElem] at hmem
      obtain ⟨p, hp, hpc⟩ := hmem
      obtain ⟨c', hc', hwc', _, hgp⟩ := hget_pos p (by omega)
      have : ord[p] = c' := by simpa [List.getElem!_eq_getElem?_getD, hp] using hgp
      rw [← hpc, this]
      exact ⟨hc', hwc'⟩
    · rintro ⟨hc, hwc⟩
      have hslot := slotOf_lt_total weights.val c hc hwc
      rw [← htot] at hslot
      rw [List.mem_iff_getElem]
      refine ⟨slotOf weights.val c, by omega, ?_⟩
      simp only [ord, List.getElem_map, List.getElem_take]
      have h1 := hord c hc hwc
      rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (by simp; omega)] at h1
      exact h1
  · intro i j hij hj
    obtain ⟨ci, hci, _, hsi, hgi⟩ := hget_pos i (by omega)
    obtain ⟨cj, hcj, _, hsj, hgj⟩ := hget_pos j (by omega)
    rw [hgi, hgj]
    by_contra hlt
    have hgt : (weights.val[ci]!).val < (weights.val[cj]!).val := by omega
    have := slotOf_lt_of_gt weights.val hcj hgt
    omega

/-! ## Part 2: Chain composition laws for FIPS 205 `Spec.chain` -/

theorem chain_zero (p : Spec.Params) (x : Spec.Bytes) (i : Nat) (pk : Spec.Bytes) (adrs : Spec.Adrs) :
    Spec.chain p x i 0 pk adrs = x := rfl

theorem chain_one (p : Spec.Params) (x : Spec.Bytes) (i : Nat) (pk : Spec.Bytes) (adrs : Spec.Adrs) :
    Spec.chain p x i 1 pk adrs = Spec.F p pk { adrs with word3 := i } x := rfl

theorem chain_add (p : Spec.Params) (x : Spec.Bytes) (i s1 s2 : Nat) (pk : Spec.Bytes) (adrs : Spec.Adrs) :
    Spec.chain p (Spec.chain p x i s1 pk adrs) (i + s1) s2 pk adrs =
      Spec.chain p x i (s1 + s2) pk adrs := by
  induction s2 with
  | zero => simp [Spec.chain]
  | succ s2 ih =>
    unfold Spec.chain at ih ⊢
    rw [show s1 + (s2 + 1) = (s1 + s2) + 1 by omega, List.range_succ, List.range_succ,
      List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil,
      List.foldl_cons, List.foldl_nil, ih, Nat.add_assoc]

/-- Function update at a single chain index. -/
def setOut (out : Nat → Spec.Bytes) (c : Nat) (v : Spec.Bytes) : Nat → Spec.Bytes :=
  fun i => if i = c then v else out i

/-! ## Part 3: Dynamic 4-Lane Refill Scheduler for `wots_recover` -/

/-- State of one active lane in `wots_recover`. -/
structure RecoverLane where
  x : Spec.Bytes
  chain : Nat
  curT : Nat
  left : Nat

/-- Total remaining steps across all active lanes. -/
def recoverSumLeft (lanes : List RecoverLane) : Nat :=
  lanes.foldl (fun acc l => acc + l.left) 0

private theorem recoverSumLeft_nil : recoverSumLeft [] = 0 := rfl

private theorem recoverSumLeft_cons (l : RecoverLane) (ls : List RecoverLane) :
    recoverSumLeft (l :: ls) = l.left + recoverSumLeft ls := by
  unfold recoverSumLeft
  have hgen : ∀ a, ls.foldl (fun acc x => acc + x.left) a = a + ls.foldl (fun acc x => acc + x.left) 0 := by
    induction ls with
    | nil => intro a; simp
    | cons x xs ih =>
      intro a
      simp only [List.foldl_cons, Nat.zero_add]
      rw [ih (a + x.left), ih x.left, Nat.add_assoc]
  simpa [List.foldl_cons] using hgen l.left

private theorem recoverSumLeft_map_sub (lanes : List RecoverLane) (f : RecoverLane → RecoverLane) (m : Nat)
    (hne : lanes ≠ []) (hm_pos : 0 < m)
    (hle : ∀ l ∈ lanes, m ≤ l.left)
    (hf : ∀ l ∈ lanes, (f l).left = l.left - m) :
    recoverSumLeft (lanes.map f) < recoverSumLeft lanes := by
  induction lanes with
  | nil => contradiction
  | cons l ls ih =>
    simp only [List.map_cons, recoverSumLeft_cons]
    have hml : m ≤ l.left := hle l (by simp)
    have hfl : (f l).left = l.left - m := hf l (by simp)
    cases ls with
    | nil => simp [recoverSumLeft_nil]; omega
    | cons l' ls' =>
      have hsub := ih (by simp) (fun x hx => hle x (by simp [hx])) (fun x hx => hf x (by simp [hx]))
      omega

/-- Minimum `left` across a non-empty list of lanes (`left[0].min(left[1]).min(left[2]).min(left[3])`). -/
def minLeft : List RecoverLane → Nat
  | [] => 0
  | [l] => l.left
  | l :: ls => min l.left (minLeft ls)

private theorem minLeft_pos {lanes : List RecoverLane} (hne : lanes ≠ [])
    (hpos : ∀ l ∈ lanes, 0 < l.left) : 0 < minLeft lanes := by
  induction lanes with
  | nil => contradiction
  | cons l ls ih =>
    cases ls with
    | nil => exact hpos l (by simp)
    | cons l' ls' =>
      simp only [minLeft]
      exact Nat.lt_min.mpr ⟨hpos l (by simp), ih (by simp) (fun x hx => hpos x (by simp [hx]))⟩

private theorem minLeft_le {lanes : List RecoverLane} {l : RecoverLane} (hl : l ∈ lanes) :
    minLeft lanes ≤ l.left := by
  induction lanes with
  | nil => contradiction
  | cons a ls ih =>
    cases ls with
    | nil =>
      simp only [List.mem_singleton] at hl
      subst hl; exact le_rfl
    | cons b ls' =>
      simp only [minLeft]
      simp only [List.mem_cons] at hl
      rcases hl with rfl | hl'
      · exact Nat.min_le_left _ _
      · exact le_trans (Nat.min_le_right _ _) (ih (by simp [hl']))

/-- Process retiring/refilling a list of stepped lanes left-to-right (exact loop `for l in 0..4`
followed by compaction in `wots_recover_active`). -/
def recoverRetireRefill (sig : Nat → Spec.Bytes) (digits : Nat → Nat) :
    List RecoverLane → List Nat → (Nat → Spec.Bytes) →
    List RecoverLane × List Nat × (Nat → Spec.Bytes)
  | [], queue, out => ([], queue, out)
  | l :: ls, queue, out =>
    if l.left = 0 then
      let out' := setOut out l.chain l.x
      match queue with
      | [] => recoverRetireRefill sig digits ls [] out'
      | nc :: rest =>
        let nl : RecoverLane := ⟨sig nc, nc, digits nc, 15 - digits nc⟩
        let (ls', q', out'') := recoverRetireRefill sig digits ls rest out'
        (nl :: ls', q', out'')
    else
      let (ls', q', out') := recoverRetireRefill sig digits ls queue out
      (l :: ls', q', out')

/-- One 4-lane lockstep `min_left` iteration of `wots_recover_active`. -/
def recoverStep4 (p : Spec.Params) (pkSeed : Spec.Bytes) (adrs : Spec.Adrs)
    (sig : Nat → Spec.Bytes) (digits : Nat → Nat)
    (active : List RecoverLane) (queue : List Nat) (out : Nat → Spec.Bytes) :
    List RecoverLane × List Nat × (Nat → Spec.Bytes) :=
  let m := minLeft active
  let stepped := active.map fun l =>
    ⟨Spec.chain p l.x l.curT m pkSeed { adrs with word2 := l.chain },
      l.chain, l.curT + m, l.left - m⟩
  recoverRetireRefill sig digits stepped queue out

/-- One 1-step tail iteration (for 1, 2, or 3 active lanes) of `wots_recover_active`. -/
def recoverStepTail (p : Spec.Params) (pkSeed : Spec.Bytes) (adrs : Spec.Adrs)
    (active : List RecoverLane) (out : Nat → Spec.Bytes) :
    List RecoverLane × (Nat → Spec.Bytes) :=
  let stepped := active.map fun l =>
    ⟨Spec.F p pkSeed { adrs with word2 := l.chain, word3 := l.curT } l.x,
      l.chain, l.curT + 1, l.left - 1⟩
  let (rem, _, out') := recoverRetireRefill (fun _ => []) (fun _ => 0) stepped [] out
  (rem, out')

/-- Termination measure for `recoverRun`: strictly decreases on every 4-lane or tail step. -/
def recoverMeasure (active : List RecoverLane) (queue : List Nat) : Nat :=
  queue.length * 16 + recoverSumLeft active

private theorem recoverRetireRefill_nil_queue (sig : Nat → Spec.Bytes) (digits : Nat → Nat)
    (lanes : List RecoverLane) (out : Nat → Spec.Bytes) :
    (recoverRetireRefill sig digits lanes [] out).2.1 = [] := by
  induction lanes generalizing out with
  | nil => rfl
  | cons l ls ih =>
    simp only [recoverRetireRefill]
    split
    · exact ih _
    · exact ih _

private theorem recoverRetireRefill_nil_indep (sig1 sig2 : Nat → Spec.Bytes) (d1 d2 : Nat → Nat)
    (lanes : List RecoverLane) (out : Nat → Spec.Bytes) :
    recoverRetireRefill sig1 d1 lanes [] out = recoverRetireRefill sig2 d2 lanes [] out := by
  induction lanes generalizing out with
  | nil => rfl
  | cons l ls ih =>
    simp only [recoverRetireRefill]
    split
    · exact ih _
    · rw [ih]

private theorem recoverRetireRefill_measure (sig : Nat → Spec.Bytes) (digits : Nat → Nat)
    (lanes : List RecoverLane) (queue : List Nat) (out : Nat → Spec.Bytes)
    (hq : ∀ c ∈ queue, digits c < 15) :
    let (a', q', _) := recoverRetireRefill sig digits lanes queue out
    recoverMeasure a' q' ≤ recoverMeasure lanes queue := by
  induction lanes generalizing queue out with
  | nil => simp [recoverRetireRefill, recoverMeasure]
  | cons l ls ih =>
    simp only [recoverRetireRefill]
    split
    · cases queue with
      | nil =>
        have h := ih [] (setOut out l.chain l.x) (by simp)
        simp only [recoverMeasure, recoverSumLeft_cons] at h ⊢
        omega
      | cons nc rest =>
        have hnc : digits nc < 15 := hq nc (by simp)
        have h := ih rest (setOut out l.chain l.x) (fun c hc => hq c (by simp [hc]))
        simp only [recoverMeasure, recoverSumLeft_cons, List.length_cons] at h ⊢
        omega
    · have h := ih queue out hq
      simp only [recoverMeasure, recoverSumLeft_cons] at h ⊢
      omega

private theorem recoverRetireRefill_len_le (sig : Nat → Spec.Bytes) (digits : Nat → Nat)
    (lanes : List RecoverLane) (queue : List Nat) (out : Nat → Spec.Bytes) :
    (recoverRetireRefill sig digits lanes queue out).1.length ≤ lanes.length := by
  induction lanes generalizing queue out with
  | nil => simp [recoverRetireRefill]
  | cons l ls ih =>
    simp only [recoverRetireRefill]
    split
    · cases queue with
      | nil =>
        have := ih [] (setOut out l.chain l.x)
        simp only [List.length_cons]; omega
      | cons nc rest =>
        have := ih rest (setOut out l.chain l.x)
        simp only [List.length_cons]; omega
    · have := ih queue out
      simp only [List.length_cons]; omega

private theorem recoverRetireRefill_len_lt_queue_nil (sig : Nat → Spec.Bytes) (digits : Nat → Nat)
    (lanes : List RecoverLane) (queue : List Nat) (out : Nat → Spec.Bytes)
    (hlt : (recoverRetireRefill sig digits lanes queue out).1.length < lanes.length) :
    (recoverRetireRefill sig digits lanes queue out).2.1 = [] := by
  induction lanes generalizing queue out with
  | nil => simp [recoverRetireRefill] at hlt
  | cons l ls ih =>
    simp only [recoverRetireRefill] at hlt ⊢
    split at hlt
    · rename_i hl0
      rw [ite_eq_left hl0]
      cases queue with
      | nil => exact recoverRetireRefill_nil_queue sig digits ls (setOut out l.chain l.x)
      | cons nc rest =>
        simp only [List.length_cons] at hlt
        exact ih rest (setOut out l.chain l.x) (by omega)
    · rename_i hne0
      rw [ite_eq_right hne0]
      simp only [List.length_cons] at hlt
      exact ih queue out (by omega)

/-- Exact specification invariant for `wots_recover`. -/
structure RecoverInv (p : Spec.Params) (pkSeed : Spec.Bytes) (adrs : Spec.Adrs)
    (sig : Nat → Spec.Bytes) (digits : Nat → Nat) (len : Nat)
    (active : List RecoverLane) (queue : List Nat) (out : Nat → Spec.Bytes) : Prop where
  lanes_valid : ∀ l ∈ active,
    l.chain < len ∧ l.curT + l.left = 15 ∧ 0 < l.left ∧ digits l.chain ≤ l.curT ∧
    l.x = Spec.chain p (sig l.chain) (digits l.chain) (l.curT - digits l.chain) pkSeed { adrs with word2 := l.chain }
  queue_valid : ∀ c ∈ queue, c < len ∧ digits c < 15
  nodup_all : (active.map (·.chain) ++ queue).Nodup
  out_done : ∀ c < len, c ∉ active.map (·.chain) → c ∉ queue →
    out c = Spec.chain p (sig c) (digits c) (15 - digits c) pkSeed { adrs with word2 := c }

private theorem recoverRetireRefill_spec (p : Spec.Params) (pkSeed : Spec.Bytes) (adrs : Spec.Adrs)
    (sig : Nat → Spec.Bytes) (digits : Nat → Nat) (len : Nat)
    (stepped : List RecoverLane) (queue : List Nat) (out : Nat → Spec.Bytes)
    (hstep : ∀ l ∈ stepped,
      l.chain < len ∧ l.curT + l.left = 15 ∧ digits l.chain ≤ l.curT ∧
      l.x = Spec.chain p (sig l.chain) (digits l.chain) (l.curT - digits l.chain) pkSeed { adrs with word2 := l.chain })
    (hq : ∀ c ∈ queue, c < len ∧ digits c < 15)
    (hnd : (stepped.map (·.chain) ++ queue).Nodup) :
    let (a', q', out') := recoverRetireRefill sig digits stepped queue out
    (∀ l ∈ a',
      l.chain < len ∧ l.curT + l.left = 15 ∧ 0 < l.left ∧ digits l.chain ≤ l.curT ∧
      l.x = Spec.chain p (sig l.chain) (digits l.chain) (l.curT - digits l.chain) pkSeed { adrs with word2 := l.chain }) ∧
    (∀ c ∈ q', c < len ∧ digits c < 15) ∧
    (a'.map (·.chain) ++ q').Nodup ∧
    (∀ c, c ∈ a'.map (·.chain) ++ q' → c ∈ stepped.map (·.chain) ++ queue) ∧
    (∀ c, c ∈ stepped.map (·.chain) ++ queue → c ∉ a'.map (·.chain) ++ q' →
      out' c = Spec.chain p (sig c) (digits c) (15 - digits c) pkSeed { adrs with word2 := c }) ∧
    (∀ c, c ∉ stepped.map (·.chain) → out' c = out c) := by
  induction stepped generalizing queue out with
  | nil =>
    simp only [recoverRetireRefill]
    refine ⟨by simp, hq, by simpa using hnd, fun _ h => h, fun c hc hnc => absurd hc hnc,
      fun _ _ => trivial⟩
  | cons l ls ih =>
    simp only [recoverRetireRefill]
    obtain ⟨hl_lt, hl_sum, hl_dig, hl_x⟩ := hstep l (by simp)
    have hstep_ls : ∀ x ∈ ls, x.chain < len ∧ x.curT + x.left = 15 ∧ digits x.chain ≤ x.curT ∧
        x.x = Spec.chain p (sig x.chain) (digits x.chain) (x.curT - digits x.chain) pkSeed { adrs with word2 := x.chain } :=
      fun x hx => hstep x (by simp [hx])
    simp only [List.map_cons, List.cons_append, List.nodup_cons, List.mem_append, not_or] at hnd
    obtain ⟨⟨hl_not_ls, hl_not_q⟩, hnd_ls⟩ := hnd
    split
    · rename_i hl0
      have hl_done : l.x = Spec.chain p (sig l.chain) (digits l.chain) (15 - digits l.chain) pkSeed { adrs with word2 := l.chain } := by
        rw [hl_x, show l.curT - digits l.chain = 15 - digits l.chain by omega]
      cases queue with
      | nil =>
        have hih := ih [] (setOut out l.chain l.x) hstep_ls (by simp) hnd_ls
        rcases hres : recoverRetireRefill sig digits ls [] (setOut out l.chain l.x) with ⟨a', q', out'⟩
        rw [hres] at hih
        obtain ⟨ha', hq', hnd', hsub', hret', hpres'⟩ := hih
        dsimp only
        refine ⟨ha', hq', hnd', fun c hc => by
          have h := hsub' c hc; simp only [List.append_nil] at h; simp [h], ?_, ?_⟩
        · intro c hc hnc
          simp only [List.map_cons, List.cons_append, List.mem_cons] at hc
          rcases hc with rfl | hc_ls
          · rw [hpres' l.chain hl_not_ls]; simp [setOut, hl_done]
          · exact hret' c hc_ls hnc
        · intro c hnc
          simp only [List.map_cons, List.mem_cons, not_or] at hnc
          rw [hpres' c hnc.2]; simp [setOut, hnc.1]
      | cons nc rest =>
        obtain ⟨hnc_lt, hnc_dig⟩ := hq nc (by simp)
        have hq_rest : ∀ c ∈ rest, c < len ∧ digits c < 15 := fun c hc => hq c (by simp [hc])
        have hnd_split : (ls.map (·.chain) ++ rest).Nodup ∧ nc ∉ ls.map (·.chain) ∧ nc ∉ rest := by
          have h1 := List.nodup_append.mp hnd_ls
          simp only [List.nodup_cons] at h1
          refine ⟨List.nodup_append.mpr ⟨h1.1, h1.2.1.2, fun a ha b hb => h1.2.2 a ha b (by simp [hb])⟩,
            fun h => h1.2.2 nc h nc (by simp) rfl, h1.2.1.1⟩
        have hih := ih rest (setOut out l.chain l.x) hstep_ls hq_rest hnd_split.1
        rcases hres : recoverRetireRefill sig digits ls rest (setOut out l.chain l.x) with ⟨a', q', out'⟩
        rw [hres] at hih
        obtain ⟨ha', hq', hnd', hsub', hret', hpres'⟩ := hih
        have hnc_not_out : nc ∉ a'.map (·.chain) ++ q' := fun h => by
          have := hsub' nc h
          simp only [List.mem_append] at this
          rcases this with h1 | h2
          · exact hnd_split.2.1 h1
          · exact hnd_split.2.2 h2
        dsimp only
        rw [hres]
        dsimp only
        refine ⟨?_, hq', ?_, ?_, ?_, ?_⟩
        · intro x hx
          simp only [List.mem_cons] at hx
          rcases hx with rfl | hx'
          · dsimp only
            exact ⟨hnc_lt, by omega, by omega, le_rfl, by simp [Spec.chain]⟩
          · exact ha' x hx'
        · simp only [List.map_cons, List.cons_append, List.nodup_cons]
          exact ⟨hnc_not_out, hnd'⟩
        · intro c hc
          simp only [List.map_cons, List.cons_append, List.mem_cons, List.mem_append] at hc ⊢
          rcases hc with rfl | hc'
          · exact Or.inr (Or.inr (Or.inl rfl))
          · have hmem := hsub' c (by simpa [List.mem_append] using hc')
            simp only [List.mem_append] at hmem
            rcases hmem with h1 | h2
            · exact Or.inr (Or.inl h1)
            · exact Or.inr (Or.inr (Or.inr h2))
        · intro c hc hnc
          simp only [List.map_cons, List.cons_append, List.mem_cons, List.mem_append, not_or] at hc hnc
          rcases hc with rfl | hc_ls | rfl | hc_rest
          · rw [hpres' l.chain hl_not_ls]; simp [setOut, hl_done]
          · exact hret' c (by simp [hc_ls]) (by simp [hnc.2])
          · exact absurd rfl hnc.1
          · exact hret' c (by simp [hc_rest]) (by simp [hnc.2])
        · intro c hnc
          simp only [List.map_cons, List.mem_cons, not_or] at hnc
          rw [hpres' c hnc.2]; simp [setOut, hnc.1]
    · rename_i hl_ne0
      have hih := ih queue out hstep_ls hq hnd_ls
      rcases hres : recoverRetireRefill sig digits ls queue out with ⟨a', q', out'⟩
      rw [hres] at hih
      obtain ⟨ha', hq', hnd', hsub', hret', hpres'⟩ := hih
      have hl_not_out : l.chain ∉ a'.map (·.chain) ++ q' := fun h => by
        have := hsub' l.chain h
        simp only [List.mem_append] at this
        rcases this with h1 | h2
        · exact hl_not_ls h1
        · exact hl_not_q h2
      dsimp only
      refine ⟨?_, hq', ?_, ?_, ?_, ?_⟩
      · intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx'
        · exact ⟨hl_lt, hl_sum, by omega, hl_dig, hl_x⟩
        · exact ha' x hx'
      · simp only [List.map_cons, List.cons_append, List.nodup_cons]
        exact ⟨hl_not_out, hnd'⟩
      · intro c hc
        simp only [List.map_cons, List.cons_append, List.mem_cons] at hc ⊢
        rcases hc with rfl | hc'
        · exact Or.inl rfl
        · exact Or.inr (hsub' c hc')
      · intro c hc hnc
        simp only [List.map_cons, List.cons_append, List.mem_cons, not_or] at hc hnc
        rcases hc with rfl | hc'
        · exact absurd rfl hnc.1
        · exact hret' c hc' hnc.2
      · intro c hnc
        simp only [List.map_cons, List.mem_cons, not_or] at hnc
        exact hpres' c hnc.2

/-- Full dynamic 4-lane refill loop + tail drain loop for `wots_recover`. -/
def recoverRun (p : Spec.Params) (pkSeed : Spec.Bytes) (adrs : Spec.Adrs)
    (sig : Nat → Spec.Bytes) (digits : Nat → Nat)
    (active : List RecoverLane) (queue : List Nat) (out : Nat → Spec.Bytes)
    (fuel : Nat) : Nat → Spec.Bytes :=
  match fuel with
  | 0 => out
  | fuel' + 1 =>
    if active.length = 4 then
      let (a', q', out') := recoverStep4 p pkSeed adrs sig digits active queue out
      recoverRun p pkSeed adrs sig digits a' q' out' fuel'
    else if active.length > 0 then
      let (a', out') := recoverStepTail p pkSeed adrs active out
      recoverRun p pkSeed adrs sig digits a' queue out' fuel'
    else
      out

/-- Full `wots_recover` scheduler: pre-pass for `digit == 15`, initial fill of up to 4 lanes
from `order`, then `recoverRun`. -/
def recoverFull (p : Spec.Params) (pkSeed : Spec.Bytes) (adrs : Spec.Adrs)
    (sig : Nat → Spec.Bytes) (digits : Nat → Nat) (order : List Nat) : Nat → Spec.Bytes :=
  let out0 : Nat → Spec.Bytes := fun c => if digits c = 15 then sig c else []
  let initActive := (order.take 4).map fun c => ⟨sig c, c, digits c, 15 - digits c⟩
  let initQueue := order.drop 4
  recoverRun p pkSeed adrs sig digits initActive initQueue out0
    (recoverMeasure initActive initQueue + 1)

private theorem recoverRun_eq_fips (p : Spec.Params) (pkSeed : Spec.Bytes) (adrs : Spec.Adrs)
    (sig : Nat → Spec.Bytes) (digits : Nat → Nat) (len : Nat)
    (active : List RecoverLane) (queue : List Nat) (out : Nat → Spec.Bytes) (fuel : Nat)
    (hinv : RecoverInv p pkSeed adrs sig digits len active queue out)
    (hlen_le : active.length ≤ 4)
    (hqueue_empty : active.length ≠ 4 → queue = [])
    (hfuel : recoverMeasure active queue < fuel) :
    ∀ c < len, recoverRun p pkSeed adrs sig digits active queue out fuel c =
      Spec.chain p (sig c) (digits c) (15 - digits c) pkSeed { adrs with word2 := c } := by
  induction fuel generalizing active queue out with
  | zero => omega
  | succ fuel' ih =>
    intro c hc
    unfold recoverRun
    split
    · rename_i hlen4
      have hne : active ≠ [] := by intro h; simp [h] at hlen4
      have hm_pos : 0 < minLeft active := minLeft_pos hne (fun l hl => (hinv.lanes_valid l hl).2.2.1)
      let fStep : RecoverLane → RecoverLane := fun l =>
        ⟨Spec.chain p l.x l.curT (minLeft active) pkSeed { adrs with word2 := l.chain },
          l.chain, l.curT + minLeft active, l.left - minLeft active⟩
      let stepped := active.map fStep
      have hstep : ∀ l ∈ stepped,
          l.chain < len ∧ l.curT + l.left = 15 ∧ digits l.chain ≤ l.curT ∧
          l.x = Spec.chain p (sig l.chain) (digits l.chain) (l.curT - digits l.chain) pkSeed { adrs with word2 := l.chain } := by
        intro l' hl'
        rw [List.mem_map] at hl'
        obtain ⟨l, hl, rfl⟩ := hl'
        obtain ⟨hlt, hsum, _, hdig, hx⟩ := hinv.lanes_valid l hl
        have hm_le : minLeft active ≤ l.left := minLeft_le hl
        dsimp only [fStep]
        refine ⟨hlt, by omega, by omega, ?_⟩
        have hsub : l.curT - digits l.chain + minLeft active = l.curT + minLeft active - digits l.chain := by omega
        rw [hx, ← hsub, ← chain_add, show digits l.chain + (l.curT - digits l.chain) = l.curT by omega]
      have hchains : stepped.map (·.chain) = active.map (·.chain) := by
        simp [stepped, fStep, List.map_map, Function.comp_def]
      have hspec := recoverRetireRefill_spec p pkSeed adrs sig digits len stepped queue out hstep
        hinv.queue_valid (by rw [hchains]; exact hinv.nodup_all)
      have hmeas_rr := recoverRetireRefill_measure sig digits stepped queue out
        (fun c hc => (hinv.queue_valid c hc).2)
      have hmeas_step : recoverMeasure stepped queue < recoverMeasure active queue := by
        unfold recoverMeasure
        have hsum : recoverSumLeft stepped < recoverSumLeft active :=
          recoverSumLeft_map_sub active fStep (minLeft active) hne hm_pos
            (fun l hl => minLeft_le hl) (fun _ _ => rfl)
        omega
      have hstep_len : stepped.length = 4 := by simp [stepped, hlen4]
      have hlen_rr := recoverRetireRefill_len_le sig digits stepped queue out
      have hlt_rr := recoverRetireRefill_len_lt_queue_nil sig digits stepped queue out
      dsimp only [recoverStep4]
      change (let (a', q', out') := recoverRetireRefill sig digits stepped queue out
        recoverRun p pkSeed adrs sig digits a' q' out' fuel') c = _
      rcases hres : recoverRetireRefill sig digits stepped queue out with ⟨a', q', out'⟩
      rw [hres] at hspec hmeas_rr hlen_rr hlt_rr
      simp only at hlen_rr hlt_rr
      obtain ⟨ha', hq', hnd', _, hret', hpres'⟩ := hspec
      apply ih a' q' out' _ (by omega) (fun hne4 => hlt_rr (by omega)) (by omega) c hc
      refine ⟨ha', hq', hnd', ?_⟩
      intro c' hc' hna hnq
      by_cases hprev : c' ∈ active.map (·.chain) ++ queue
      · exact hret' c' (by rw [hchains]; exact hprev) (by simp [hna, hnq])
      · simp only [List.mem_append, not_or] at hprev
        rw [hpres' c' (by rw [hchains]; exact hprev.1)]
        exact hinv.out_done c' hc' hprev.1 hprev.2
    · rename_i hne4
      have hq_nil : queue = [] := hqueue_empty hne4
      subst hq_nil
      split
      · rename_i hpos
        have hne : active ≠ [] := by intro h; simp [h] at hpos
        let fStep : RecoverLane → RecoverLane := fun l =>
          ⟨Spec.F p pkSeed { adrs with word2 := l.chain, word3 := l.curT } l.x,
            l.chain, l.curT + 1, l.left - 1⟩
        let stepped := active.map fStep
        have hstep : ∀ l ∈ stepped,
            l.chain < len ∧ l.curT + l.left = 15 ∧ digits l.chain ≤ l.curT ∧
            l.x = Spec.chain p (sig l.chain) (digits l.chain) (l.curT - digits l.chain) pkSeed { adrs with word2 := l.chain } := by
          intro l' hl'
          rw [List.mem_map] at hl'
          obtain ⟨l, hl, rfl⟩ := hl'
          obtain ⟨hlt, hsum, hlpos, hdig, hx⟩ := hinv.lanes_valid l hl
          dsimp only [fStep]
          refine ⟨hlt, by omega, by omega, ?_⟩
          have h1 : Spec.F p pkSeed { adrs with word2 := l.chain, word3 := l.curT } l.x =
              Spec.chain p l.x l.curT 1 pkSeed { adrs with word2 := l.chain } := rfl
          have hsub : l.curT - digits l.chain + 1 = l.curT + 1 - digits l.chain := by omega
          rw [h1, hx, ← hsub, ← chain_add, show digits l.chain + (l.curT - digits l.chain) = l.curT by omega]
        have hchains : stepped.map (·.chain) = active.map (·.chain) := by
          simp [stepped, fStep, List.map_map, Function.comp_def]
        have hrr_indep := recoverRetireRefill_nil_indep (fun _ => []) sig (fun _ => 0) digits stepped out
        have hspec := recoverRetireRefill_spec p pkSeed adrs sig digits len stepped [] out hstep
          (by simp) (by rw [hchains]; exact hinv.nodup_all)
        have hmeas_rr := recoverRetireRefill_measure sig digits stepped [] out (by simp)
        have hmeas_step : recoverMeasure stepped [] < recoverMeasure active [] := by
          unfold recoverMeasure
          have hsum : recoverSumLeft stepped < recoverSumLeft active :=
            recoverSumLeft_map_sub active fStep 1 hne (by omega)
              (fun l hl => (hinv.lanes_valid l hl).2.2.1) (fun _ _ => rfl)
          omega
        have hlen_rr := recoverRetireRefill_len_le sig digits stepped [] out
        have hstep_len : stepped.length = active.length := by simp [stepped]
        have hq0 := recoverRetireRefill_nil_queue sig digits stepped out
        dsimp only [recoverStepTail]
        change (let (rem, _, out') := recoverRetireRefill (fun _ => []) (fun _ => 0) stepped [] out
          recoverRun p pkSeed adrs sig digits rem [] out' fuel') c = _
        rw [hrr_indep]
        rcases hres : recoverRetireRefill sig digits stepped [] out with ⟨a', q', out'⟩
        rw [hres] at hq0
        simp only at hq0
        subst hq0
        rw [hres] at hspec hmeas_rr hlen_rr
        simp only at hlen_rr
        obtain ⟨ha', _, hnd', _, hret', hpres'⟩ := hspec
        apply ih a' [] out' _ (by omega) (fun _ => rfl) (by omega) c hc
        refine ⟨ha', by simp, hnd', ?_⟩
        intro c' hc' hna _
        by_cases hprev : c' ∈ active.map (·.chain)
        · exact hret' c' (by rw [hchains]; simp [hprev]) (by simp [hna])
        · rw [hpres' c' (by rw [hchains]; exact hprev)]
          exact hinv.out_done c' hc' hprev (by simp)
      · rename_i hzero
        have ha_nil : active = [] := List.eq_nil_of_length_eq_zero (by omega)
        exact hinv.out_done c hc (by simp [ha_nil]) (by simp)

/-- **Main theorem for `wots_recover`**:
For ANY duplicate-free schedule `order` covering `{ c < len | digits c < 15 }`
(in particular, the bucket-sorted descending output of `sha256::arm_wide::sort_descending`),
running `recoverFull` produces the exact FIPS 205 `Spec.chain` value for EVERY
chain `0 ≤ c < len` (including both `digits c = 0` and `digits c = 15`). -/
theorem recover_scheduler_eq_fips (p : Spec.Params) (pkSeed : Spec.Bytes) (adrs : Spec.Adrs)
    (sig : Nat → Spec.Bytes) (digits : Nat → Nat) (len : Nat) (order : List Nat)
    (hdig : ∀ c < len, digits c ≤ 15)
    (hnd : order.Nodup)
    (hmem : ∀ c, c ∈ order ↔ c < len ∧ digits c < 15) :
    ∀ c < len, recoverFull p pkSeed adrs sig digits order c =
      Spec.chain p (sig c) (digits c) (15 - digits c) pkSeed { adrs with word2 := c } := by
  unfold recoverFull
  set out0 : Nat → Spec.Bytes := fun c => if digits c = 15 then sig c else []
  set initActive := (order.take 4).map fun c => (⟨sig c, c, digits c, 15 - digits c⟩ : RecoverLane)
  set initQueue := order.drop 4
  have hchains : initActive.map (·.chain) ++ initQueue = order := by
    simp [initActive, initQueue, List.map_map, Function.comp_def, List.take_append_drop]
  apply recoverRun_eq_fips p pkSeed adrs sig digits len initActive initQueue out0 _
  · refine ⟨?_, ?_, by rw [hchains]; exact hnd, ?_⟩
    · intro l hl
      rw [List.mem_map] at hl
      obtain ⟨c, hc, rfl⟩ := hl
      have hc' : c ∈ order := List.mem_of_mem_take hc
      obtain ⟨hlt, hdlt⟩ := (hmem c).mp hc'
      dsimp only
      exact ⟨hlt, by omega, by omega, le_rfl, by simp [Spec.chain]⟩
    · intro c hc
      exact (hmem c).mp (List.mem_of_mem_drop hc)
    · intro c hc hna hnq
      have hnot : c ∉ order := by
        rw [← hchains, List.mem_append, not_or]; exact ⟨hna, hnq⟩
      have hd15 : digits c = 15 := by
        have hle := hdig c hc
        by_contra hne
        exact hnot ((hmem c).mpr ⟨hc, by omega⟩)
      simp [out0, hd15, Spec.chain]
  · simp [initActive]
  · intro hne4
    have hlt : order.length < 4 := by
      simp only [initActive, List.length_map, List.length_take] at hne4
      omega
    exact List.drop_eq_nil_of_le (by omega)
  · exact Nat.lt_succ_self _

/-- **End-to-end composition of extracted `sort_descending` + `recoverFull`**:
Sorting `rem_weights[i] = 15 - digits[i]` via the Aeneas-extracted Rust function
`sha256::arm_wide::sort_descending` and feeding the resulting `order[..total]` into
`recoverFull` computes exact FIPS 205 `Spec.chain` for every chain `0 ≤ c < len`. -/
theorem recover_with_extracted_sort (p : Spec.Params) (pkSeed : Spec.Bytes) (adrs : Spec.Adrs)
    (sig : Nat → Spec.Bytes) (digits : Nat → Nat)
    (weights : Slice U32) (orderBuf : Array U8 67#usize)
    (hlen : weights.length ≤ 67)
    (hdig : ∀ c < weights.length, digits c ≤ 15)
    (hw : ∀ c < weights.length, (weights.val[c]!).val = 15 - digits c) :
    sha256.arm_wide.sort_descending weights orderBuf ⦃ r =>
      let ord := (r.2.val.take r.1.val).map (·.val)
      ∀ c < weights.length, recoverFull p pkSeed adrs sig digits ord c =
        Spec.chain p (sig c) (digits c) (15 - digits c) pkSeed { adrs with word2 := c } ⦄ := by
  have hb : ∀ j < weights.length, (weights.val[j]!).val ≤ 15 := by
    intro j hj; rw [hw j hj]; omega
  apply WP.spec_mono (sort_descending_spec weights orderBuf hlen hb)
  rintro ⟨total, order'⟩ ⟨_, _, hnd, hmem, _⟩
  apply recover_scheduler_eq_fips p pkSeed adrs sig digits weights.length _ hdig hnd
  intro c
  rw [hmem c]
  constructor
  · rintro ⟨hc, hpos⟩; rw [hw c hc] at hpos; exact ⟨hc, by omega⟩
  · rintro ⟨hc, hlt⟩; exact ⟨hc, by rw [hw c hc]; omega⟩

/-- Edge-case corollary: when all digits are 15 (`total = 0`, `order = []`),
`recoverFull` returns `sig c` unchanged for every chain. -/
theorem recover_all_fifteen (p : Spec.Params) (pkSeed : Spec.Bytes) (adrs : Spec.Adrs)
    (sig : Nat → Spec.Bytes) (len : Nat) :
    ∀ c < len, recoverFull p pkSeed adrs sig (fun _ => 15) [] c = sig c := by
  intro c hc
  have h := recover_scheduler_eq_fips p pkSeed adrs sig (fun _ => 15) len []
    (fun _ _ => le_rfl) List.nodup_nil (by simp) c hc
  simpa [Spec.chain] using h

/-- Edge-case corollary: when all digits are 0, `recoverFull` computes 15 chain steps
for every chain `0 ≤ c < len`. -/
theorem recover_all_zero (p : Spec.Params) (pkSeed : Spec.Bytes) (adrs : Spec.Adrs)
    (sig : Nat → Spec.Bytes) (len : Nat) (order : List Nat)
    (hnd : order.Nodup) (hmem : ∀ c, c ∈ order ↔ c < len) :
    ∀ c < len, recoverFull p pkSeed adrs sig (fun _ => 0) order c =
      Spec.chain p (sig c) 0 15 pkSeed { adrs with word2 := c } := by
  intro c hc
  exact recover_scheduler_eq_fips p pkSeed adrs sig (fun _ => 0) len order
    (fun _ _ => by omega) hnd (by intro x; simpa using hmem x) c hc

/-! ## Part 4: Dynamic 4-Lane Refill Scheduler for `wots_sign_fused` -/

/-- State of one active lane in `wots_sign_fused`. -/
structure SignLane where
  x : Spec.Bytes
  chain : Nat
  curT : Nat
  left : Nat
  isPrf : Bool

/-- Total remaining steps across all active lanes in `wots_sign_fused`. -/
def signSumLeft (lanes : List SignLane) : Nat :=
  lanes.foldl (fun acc l => acc + l.left) 0

private theorem signSumLeft_nil : signSumLeft [] = 0 := rfl

private theorem signSumLeft_cons (l : SignLane) (ls : List SignLane) :
    signSumLeft (l :: ls) = l.left + signSumLeft ls := by
  unfold signSumLeft
  have hgen : ∀ a, ls.foldl (fun acc x => acc + x.left) a = a + ls.foldl (fun acc x => acc + x.left) 0 := by
    induction ls with
    | nil => intro a; simp
    | cons x xs ih =>
      intro a
      simp only [List.foldl_cons, Nat.zero_add]
      rw [ih (a + x.left), ih x.left, Nat.add_assoc]
  simpa [List.foldl_cons] using hgen l.left

private theorem signSumLeft_map_sub (lanes : List SignLane) (f : SignLane → SignLane) (m : Nat)
    (hne : lanes ≠ []) (hm_pos : 0 < m)
    (hle : ∀ l ∈ lanes, m ≤ l.left)
    (hf : ∀ l ∈ lanes, (f l).left = l.left - m) :
    signSumLeft (lanes.map f) < signSumLeft lanes := by
  induction lanes with
  | nil => contradiction
  | cons l ls ih =>
    simp only [List.map_cons, signSumLeft_cons]
    have hml : m ≤ l.left := hle l (by simp)
    have hfl : (f l).left = l.left - m := hf l (by simp)
    cases ls with
    | nil => simp [signSumLeft_nil]; omega
    | cons l' ls' =>
      have hsub := ih (by simp) (fun x hx => hle x (by simp [hx])) (fun x hx => hf x (by simp [hx]))
      omega

/-- Minimum `left` across active lanes in `wots_sign_fused` (fast path when all `isPrf = false`). -/
def signMinLeft : List SignLane → Nat
  | [] => 0
  | [l] => l.left
  | l :: ls => min l.left (signMinLeft ls)

theorem signMinLeft_pos {lanes : List SignLane} (hne : lanes ≠ [])
    (hpos : ∀ l ∈ lanes, 0 < l.left) : 0 < signMinLeft lanes := by
  induction lanes with
  | nil => contradiction
  | cons l ls ih =>
    cases ls with
    | nil => exact hpos l (by simp)
    | cons l' ls' =>
      simp only [signMinLeft]
      exact Nat.lt_min.mpr ⟨hpos l (by simp), ih (by simp) (fun x hx => hpos x (by simp [hx]))⟩

theorem signMinLeft_le {lanes : List SignLane} {l : SignLane} (hl : l ∈ lanes) :
    signMinLeft lanes ≤ l.left := by
  induction lanes with
  | nil => contradiction
  | cons a ls ih =>
    cases ls with
    | nil =>
      simp only [List.mem_singleton] at hl
      subst hl; exact le_rfl
    | cons b ls' =>
      simp only [signMinLeft]
      simp only [List.mem_cons] at hl
      rcases hl with rfl | hl'
      · exact Nat.min_le_left _ _
      · exact le_trans (Nat.min_le_right _ _) (ih (by simp [hl']))

/-- Target FIPS 205 WOTS+ signature element for chain `c`: `chain(PRF(sk, adrs_prf), 0, digits[c])`. -/
def wotsSignTarget (p : Spec.Params) (pkSeed skSeed : Spec.Bytes) (adrs : Spec.Adrs)
    (digits : Nat → Nat) (c : Nat) : Spec.Bytes :=
  Spec.chain p (Spec.PRF p pkSeed skSeed { Spec.wotsSkAdrs adrs with word2 := c })
    0 (digits c) pkSeed { adrs with word2 := c }

/-- Retire finished lanes (`left == 0`) into `out[chain]`, refill from `queue` with
`(skSeed, nc, curT := 0, left := 1 + digits nc, isPrf := true)`, and compact. -/
def signRetireRefill (skSeed : Spec.Bytes) (digits : Nat → Nat) :
    List SignLane → List Nat → (Nat → Spec.Bytes) →
    List SignLane × List Nat × (Nat → Spec.Bytes)
  | [], queue, out => ([], queue, out)
  | l :: ls, queue, out =>
    if l.left = 0 then
      let out' := setOut out l.chain l.x
      match queue with
      | [] => signRetireRefill skSeed digits ls [] out'
      | nc :: rest =>
        let nl : SignLane := ⟨skSeed, nc, 0, 1 + digits nc, true⟩
        let (ls', q', out'') := signRetireRefill skSeed digits ls rest out'
        (nl :: ls', q', out'')
    else
      let (ls', q', out') := signRetireRefill skSeed digits ls queue out
      (l :: ls', q', out')

/-- One 1-step transition of a `SignLane` (matching the `else` branch of `wots_sign_fused_active`
and the 1..3-lane tail drain loop). -/
def signStepOneLane (p : Spec.Params) (pkSeed : Spec.Bytes) (adrs : Spec.Adrs)
    (l : SignLane) : SignLane :=
  if l.isPrf then
    let nx := Spec.PRF p pkSeed l.x { Spec.wotsSkAdrs adrs with word2 := l.chain }
    let nleft := l.left - 1
    ⟨nx, l.chain, l.curT, nleft, false⟩
  else
    let nx := Spec.F p pkSeed { adrs with word2 := l.chain, word3 := l.curT } l.x
    let nleft := l.left - 1
    ⟨nx, l.chain, l.curT + 1, nleft, false⟩

/-- One 4-lane iteration of `wots_sign_fused_active`. -/
def signStep4 (p : Spec.Params) (pkSeed skSeed : Spec.Bytes) (adrs : Spec.Adrs)
    (digits : Nat → Nat) (active : List SignLane) (queue : List Nat) (out : Nat → Spec.Bytes) :
    List SignLane × List Nat × (Nat → Spec.Bytes) :=
  if active.any (·.isPrf) then
    let stepped := active.map (signStepOneLane p pkSeed adrs)
    signRetireRefill skSeed digits stepped queue out
  else
    let m := signMinLeft active
    let stepped := active.map fun l =>
      ⟨Spec.chain p l.x l.curT m pkSeed { adrs with word2 := l.chain },
        l.chain, l.curT + m, l.left - m, false⟩
    signRetireRefill skSeed digits stepped queue out

/-- One 1-step tail iteration (for 1, 2, or 3 active lanes) of `wots_sign_fused_active`. -/
def signStepTail (p : Spec.Params) (pkSeed : Spec.Bytes) (adrs : Spec.Adrs)
    (active : List SignLane) (out : Nat → Spec.Bytes) :
    List SignLane × (Nat → Spec.Bytes) :=
  let stepped := active.map (signStepOneLane p pkSeed adrs)
  let (rem, _, out') := signRetireRefill [] (fun _ => 0) stepped [] out
  (rem, out')

/-- Termination measure for `signRun`. -/
def signMeasure (active : List SignLane) (queue : List Nat) : Nat :=
  queue.length * 17 + signSumLeft active

private theorem signRetireRefill_nil_queue (skSeed : Spec.Bytes) (digits : Nat → Nat)
    (lanes : List SignLane) (out : Nat → Spec.Bytes) :
    (signRetireRefill skSeed digits lanes [] out).2.1 = [] := by
  induction lanes generalizing out with
  | nil => rfl
  | cons l ls ih =>
    simp only [signRetireRefill]
    split
    · exact ih _
    · exact ih _

private theorem signRetireRefill_nil_indep (sk1 sk2 : Spec.Bytes) (d1 d2 : Nat → Nat)
    (lanes : List SignLane) (out : Nat → Spec.Bytes) :
    signRetireRefill sk1 d1 lanes [] out = signRetireRefill sk2 d2 lanes [] out := by
  induction lanes generalizing out with
  | nil => rfl
  | cons l ls ih =>
    simp only [signRetireRefill]
    split
    · exact ih _
    · rw [ih]

private theorem signRetireRefill_measure (skSeed : Spec.Bytes) (digits : Nat → Nat)
    (lanes : List SignLane) (queue : List Nat) (out : Nat → Spec.Bytes)
    (hq : ∀ c ∈ queue, digits c ≤ 15) :
    let (a', q', _) := signRetireRefill skSeed digits lanes queue out
    signMeasure a' q' ≤ signMeasure lanes queue := by
  induction lanes generalizing queue out with
  | nil => simp [signRetireRefill, signMeasure]
  | cons l ls ih =>
    simp only [signRetireRefill]
    split
    · cases queue with
      | nil =>
        have h := ih [] (setOut out l.chain l.x) (by simp)
        simp only [signMeasure, signSumLeft_cons] at h ⊢
        omega
      | cons nc rest =>
        have hnc : digits nc ≤ 15 := hq nc (by simp)
        have h := ih rest (setOut out l.chain l.x) (fun c hc => hq c (by simp [hc]))
        simp only [signMeasure, signSumLeft_cons, List.length_cons] at h ⊢
        omega
    · have h := ih queue out hq
      simp only [signMeasure, signSumLeft_cons] at h ⊢
      omega

private theorem signRetireRefill_len_le (skSeed : Spec.Bytes) (digits : Nat → Nat)
    (lanes : List SignLane) (queue : List Nat) (out : Nat → Spec.Bytes) :
    (signRetireRefill skSeed digits lanes queue out).1.length ≤ lanes.length := by
  induction lanes generalizing queue out with
  | nil => simp [signRetireRefill]
  | cons l ls ih =>
    simp only [signRetireRefill]
    split
    · cases queue with
      | nil =>
        have := ih [] (setOut out l.chain l.x)
        simp only [List.length_cons]; omega
      | cons nc rest =>
        have := ih rest (setOut out l.chain l.x)
        simp only [List.length_cons]; omega
    · have := ih queue out
      simp only [List.length_cons]; omega

private theorem signRetireRefill_len_lt_queue_nil (skSeed : Spec.Bytes) (digits : Nat → Nat)
    (lanes : List SignLane) (queue : List Nat) (out : Nat → Spec.Bytes)
    (hlt : (signRetireRefill skSeed digits lanes queue out).1.length < lanes.length) :
    (signRetireRefill skSeed digits lanes queue out).2.1 = [] := by
  induction lanes generalizing queue out with
  | nil => simp [signRetireRefill] at hlt
  | cons l ls ih =>
    simp only [signRetireRefill] at hlt ⊢
    split at hlt
    · rename_i hl0
      rw [ite_eq_left hl0]
      cases queue with
      | nil => exact signRetireRefill_nil_queue skSeed digits ls (setOut out l.chain l.x)
      | cons nc rest =>
        simp only [List.length_cons] at hlt
        exact ih rest (setOut out l.chain l.x) (by omega)
    · rename_i hne0
      rw [ite_eq_right hne0]
      simp only [List.length_cons] at hlt
      exact ih queue out (by omega)

/-- Exact specification invariant for `wots_sign_fused`. -/
structure SignInv (p : Spec.Params) (pkSeed skSeed : Spec.Bytes) (adrs : Spec.Adrs)
    (digits : Nat → Nat) (len : Nat)
    (active : List SignLane) (queue : List Nat) (out : Nat → Spec.Bytes) : Prop where
  lanes_valid : ∀ l ∈ active,
    l.chain < len ∧ 0 < l.left ∧
    (l.isPrf = true → l.curT = 0 ∧ l.left = 1 + digits l.chain ∧ l.x = skSeed) ∧
    (l.isPrf = false → l.curT + l.left = digits l.chain ∧
      l.x = Spec.chain p (Spec.PRF p pkSeed skSeed { Spec.wotsSkAdrs adrs with word2 := l.chain })
        0 l.curT pkSeed { adrs with word2 := l.chain })
  queue_valid : ∀ c ∈ queue, c < len ∧ digits c ≤ 15
  nodup_all : (active.map (·.chain) ++ queue).Nodup
  out_done : ∀ c < len, c ∉ active.map (·.chain) → c ∉ queue →
    out c = wotsSignTarget p pkSeed skSeed adrs digits c

/-- Post-step lane predicate (before retire/refill). -/
private def SignSteppedValid (p : Spec.Params) (pkSeed skSeed : Spec.Bytes) (adrs : Spec.Adrs)
    (digits : Nat → Nat) (len : Nat) (l : SignLane) : Prop :=
  l.chain < len ∧ l.isPrf = false ∧ l.curT + l.left = digits l.chain ∧
  l.x = Spec.chain p (Spec.PRF p pkSeed skSeed { Spec.wotsSkAdrs adrs with word2 := l.chain })
    0 l.curT pkSeed { adrs with word2 := l.chain }

private theorem signRetireRefill_spec (p : Spec.Params) (pkSeed skSeed : Spec.Bytes) (adrs : Spec.Adrs)
    (digits : Nat → Nat) (len : Nat)
    (stepped : List SignLane) (queue : List Nat) (out : Nat → Spec.Bytes)
    (hstep : ∀ l ∈ stepped, SignSteppedValid p pkSeed skSeed adrs digits len l)
    (hq : ∀ c ∈ queue, c < len ∧ digits c ≤ 15)
    (hnd : (stepped.map (·.chain) ++ queue).Nodup) :
    let (a', q', out') := signRetireRefill skSeed digits stepped queue out
    (∀ l ∈ a',
      l.chain < len ∧ 0 < l.left ∧
      (l.isPrf = true → l.curT = 0 ∧ l.left = 1 + digits l.chain ∧ l.x = skSeed) ∧
      (l.isPrf = false → l.curT + l.left = digits l.chain ∧
        l.x = Spec.chain p (Spec.PRF p pkSeed skSeed { Spec.wotsSkAdrs adrs with word2 := l.chain })
          0 l.curT pkSeed { adrs with word2 := l.chain })) ∧
    (∀ c ∈ q', c < len ∧ digits c ≤ 15) ∧
    (a'.map (·.chain) ++ q').Nodup ∧
    (∀ c, c ∈ a'.map (·.chain) ++ q' → c ∈ stepped.map (·.chain) ++ queue) ∧
    (∀ c, c ∈ stepped.map (·.chain) ++ queue → c ∉ a'.map (·.chain) ++ q' →
      out' c = wotsSignTarget p pkSeed skSeed adrs digits c) ∧
    (∀ c, c ∉ stepped.map (·.chain) → out' c = out c) := by
  induction stepped generalizing queue out with
  | nil =>
    simp only [signRetireRefill]
    refine ⟨by simp, hq, by simpa using hnd, fun _ h => h,
      fun c hc hnc => absurd hc hnc, fun _ _ => trivial⟩
  | cons l ls ih =>
    simp only [signRetireRefill]
    obtain ⟨hl_lt, hl_prf, hl_sum, hl_x⟩ := hstep l (by simp)
    have hstep_ls : ∀ x ∈ ls, SignSteppedValid p pkSeed skSeed adrs digits len x :=
      fun x hx => hstep x (by simp [hx])
    simp only [List.map_cons, List.cons_append, List.nodup_cons, List.mem_append, not_or] at hnd
    obtain ⟨⟨hl_not_ls, hl_not_q⟩, hnd_ls⟩ := hnd
    split
    · rename_i hl0
      have hl_done : l.x = wotsSignTarget p pkSeed skSeed adrs digits l.chain := by
        unfold wotsSignTarget
        rw [hl_x, show l.curT = digits l.chain by omega]
      cases queue with
      | nil =>
        have hih := ih [] (setOut out l.chain l.x) hstep_ls (by simp) hnd_ls
        rcases hres : signRetireRefill skSeed digits ls [] (setOut out l.chain l.x) with ⟨a', q', out'⟩
        rw [hres] at hih
        obtain ⟨ha', hq', hnd', hsub', hret', hpres'⟩ := hih
        dsimp only
        refine ⟨ha', hq', hnd', fun c hc => by
          have h := hsub' c hc; simp only [List.append_nil] at h; simp [h], ?_, ?_⟩
        · intro c hc hnc
          simp only [List.map_cons, List.cons_append, List.mem_cons] at hc
          rcases hc with rfl | hc_ls
          · rw [hpres' l.chain hl_not_ls]; simp [setOut, hl_done]
          · exact hret' c hc_ls hnc
        · intro c hnc
          simp only [List.map_cons, List.mem_cons, not_or] at hnc
          rw [hpres' c hnc.2]; simp [setOut, hnc.1]
      | cons nc rest =>
        obtain ⟨hnc_lt, hnc_dig⟩ := hq nc (by simp)
        have hq_rest : ∀ c ∈ rest, c < len ∧ digits c ≤ 15 := fun c hc => hq c (by simp [hc])
        have hnd_split : (ls.map (·.chain) ++ rest).Nodup ∧ nc ∉ ls.map (·.chain) ∧ nc ∉ rest := by
          have h1 := List.nodup_append.mp hnd_ls
          simp only [List.nodup_cons] at h1
          refine ⟨List.nodup_append.mpr ⟨h1.1, h1.2.1.2, fun a ha b hb => h1.2.2 a ha b (by simp [hb])⟩,
            fun h => h1.2.2 nc h nc (by simp) rfl, h1.2.1.1⟩
        have hih := ih rest (setOut out l.chain l.x) hstep_ls hq_rest hnd_split.1
        rcases hres : signRetireRefill skSeed digits ls rest (setOut out l.chain l.x) with ⟨a', q', out'⟩
        rw [hres] at hih
        obtain ⟨ha', hq', hnd', hsub', hret', hpres'⟩ := hih
        have hnc_not_out : nc ∉ a'.map (·.chain) ++ q' := fun h => by
          have := hsub' nc h
          simp only [List.mem_append] at this
          rcases this with h1 | h2
          · exact hnd_split.2.1 h1
          · exact hnd_split.2.2 h2
        dsimp only
        rw [hres]
        dsimp only
        refine ⟨?_, hq', ?_, ?_, ?_, ?_⟩
        · intro x hx
          simp only [List.mem_cons] at hx
          rcases hx with rfl | hx'
          · dsimp only
            exact ⟨hnc_lt, by omega, (fun _ => ⟨rfl, rfl, rfl⟩), (fun h => by cases h)⟩
          · exact ha' x hx'
        · simp only [List.map_cons, List.cons_append, List.nodup_cons]
          exact ⟨hnc_not_out, hnd'⟩
        · intro c hc
          simp only [List.map_cons, List.cons_append, List.mem_cons, List.mem_append] at hc ⊢
          rcases hc with rfl | hc'
          · exact Or.inr (Or.inr (Or.inl rfl))
          · have hmem := hsub' c (by simpa [List.mem_append] using hc')
            simp only [List.mem_append] at hmem
            rcases hmem with h1 | h2
            · exact Or.inr (Or.inl h1)
            · exact Or.inr (Or.inr (Or.inr h2))
        · intro c hc hnc
          simp only [List.map_cons, List.cons_append, List.mem_cons, List.mem_append, not_or] at hc hnc
          rcases hc with rfl | hc_ls | rfl | hc_rest
          · rw [hpres' l.chain hl_not_ls]; simp [setOut, hl_done]
          · exact hret' c (by simp [hc_ls]) (by simp [hnc.2])
          · exact absurd rfl hnc.1
          · exact hret' c (by simp [hc_rest]) (by simp [hnc.2])
        · intro c hnc
          simp only [List.map_cons, List.mem_cons, not_or] at hnc
          rw [hpres' c hnc.2]; simp [setOut, hnc.1]
    · rename_i hl_ne0
      have hih := ih queue out hstep_ls hq hnd_ls
      rcases hres : signRetireRefill skSeed digits ls queue out with ⟨a', q', out'⟩
      rw [hres] at hih
      obtain ⟨ha', hq', hnd', hsub', hret', hpres'⟩ := hih
      have hl_not_out : l.chain ∉ a'.map (·.chain) ++ q' := fun h => by
        have := hsub' l.chain h
        simp only [List.mem_append] at this
        rcases this with h1 | h2
        · exact hl_not_ls h1
        · exact hl_not_q h2
      dsimp only
      refine ⟨?_, hq', ?_, ?_, ?_, ?_⟩
      · intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx'
        · exact ⟨hl_lt, by omega, (fun h => by rw [hl_prf] at h; cases h), (fun _ => ⟨hl_sum, hl_x⟩)⟩
        · exact ha' x hx'
      · simp only [List.map_cons, List.cons_append, List.nodup_cons]
        exact ⟨hl_not_out, hnd'⟩
      · intro c hc
        simp only [List.map_cons, List.cons_append, List.mem_cons] at hc ⊢
        rcases hc with rfl | hc'
        · exact Or.inl rfl
        · exact Or.inr (hsub' c hc')
      · intro c hc hnc
        simp only [List.map_cons, List.cons_append, List.mem_cons, not_or] at hc hnc
        rcases hc with rfl | hc'
        · exact absurd rfl hnc.1
        · exact hret' c hc' hnc.2
      · intro c hnc
        simp only [List.map_cons, List.mem_cons, not_or] at hnc
        exact hpres' c hnc.2

/-- Full dynamic 4-lane refill loop + tail drain loop for `wots_sign_fused`. -/
abbrev FourStep := List SignLane → List Nat → (Nat → Spec.Bytes) →
  List SignLane × List Nat × (Nat → Spec.Bytes)
abbrev TailStep := List SignLane → (Nat → Spec.Bytes) → List SignLane × (Nat → Spec.Bytes)

def signRunUsing (four : FourStep) (tail : TailStep) (active : List SignLane) (queue : List Nat) (out : Nat → Spec.Bytes)
    (fuel : Nat) : Nat → Spec.Bytes :=
  match fuel with
  | 0 => out
  | fuel' + 1 =>
    if active.length = 4 then
      let (a', q', out') := four active queue out
      signRunUsing four tail a' q' out' fuel'
    else if active.length > 0 then
      let (a', out') := tail active out
      signRunUsing four tail a' queue out' fuel'
    else
      out

def signRun (p : Spec.Params) (pkSeed skSeed : Spec.Bytes) (adrs : Spec.Adrs) (digits : Nat → Nat) :=
  signRunUsing (signStep4 p pkSeed skSeed adrs digits) (signStepTail p pkSeed adrs)

/-- Full `wots_sign_fused` scheduler: initial fill of up to 4 lanes from `order`
(bucket-sorted descending by `digits`), then `signRun`. -/
def signFusedUsing (skSeed : Spec.Bytes) (digits : Nat → Nat) (order : List Nat) (four : FourStep) (tail : TailStep) : Nat → Spec.Bytes :=
  let initActive := (order.take 4).map fun c => (⟨skSeed, c, 0, 1 + digits c, true⟩ : SignLane)
  let initQueue := order.drop 4
  signRunUsing four tail initActive initQueue (fun _ => [])
    (signMeasure initActive initQueue + 1)

def signFusedFull (p : Spec.Params) (pkSeed skSeed : Spec.Bytes) (adrs : Spec.Adrs)
    (digits : Nat → Nat) (order : List Nat) : Nat → Spec.Bytes :=
  signFusedUsing skSeed digits order (signStep4 p pkSeed skSeed adrs digits) (signStepTail p pkSeed adrs)

private theorem signStepOneLane_valid (p : Spec.Params) (pkSeed skSeed : Spec.Bytes) (adrs : Spec.Adrs)
    (digits : Nat → Nat) (len : Nat) (l : SignLane)
    (hl : l.chain < len ∧ 0 < l.left ∧
      (l.isPrf = true → l.curT = 0 ∧ l.left = 1 + digits l.chain ∧ l.x = skSeed) ∧
      (l.isPrf = false → l.curT + l.left = digits l.chain ∧
        l.x = Spec.chain p (Spec.PRF p pkSeed skSeed { Spec.wotsSkAdrs adrs with word2 := l.chain })
          0 l.curT pkSeed { adrs with word2 := l.chain })) :
    SignSteppedValid p pkSeed skSeed adrs digits len (signStepOneLane p pkSeed adrs l) := by
  obtain ⟨hlt, hpos, hprf, hhash⟩ := hl
  unfold signStepOneLane
  cases hp : l.isPrf
  · obtain ⟨hsum, hx⟩ := hhash hp
    simp only [Bool.false_eq_true, ↓reduceIte, SignSteppedValid]
    refine ⟨hlt, trivial, by omega, ?_⟩
    have h1 : Spec.F p pkSeed { adrs with word2 := l.chain, word3 := l.curT } l.x =
        Spec.chain p l.x l.curT 1 pkSeed { adrs with word2 := l.chain } := rfl
    rw [h1, hx, ← chain_add]
    simp [Nat.zero_add]
  · obtain ⟨ht0, hl1, hx⟩ := hprf hp
    simp only [↓reduceIte, SignSteppedValid, ht0, hl1, hx]
    exact ⟨hlt, trivial, by omega, by simp [Spec.chain]⟩

theorem signRunUsing_eq_fips (p : Spec.Params) (pkSeed skSeed : Spec.Bytes) (adrs : Spec.Adrs)
    (digits : Nat → Nat) (len : Nat) (four : FourStep) (tail : TailStep)
    (four_ok : ∀ a q o, SignInv p pkSeed skSeed adrs digits len a q o → a.length = 4 →
      four a q o = signStep4 p pkSeed skSeed adrs digits a q o)
    (tail_ok : ∀ a o, SignInv p pkSeed skSeed adrs digits len a [] o → 0 < a.length → a.length < 4 →
      tail a o = signStepTail p pkSeed adrs a o)
    (active : List SignLane) (queue : List Nat) (out : Nat → Spec.Bytes) (fuel : Nat)
    (hinv : SignInv p pkSeed skSeed adrs digits len active queue out)
    (hlen_le : active.length ≤ 4)
    (hqueue_empty : active.length ≠ 4 → queue = [])
    (hfuel : signMeasure active queue < fuel) :
    ∀ c < len, signRunUsing four tail active queue out fuel c =
      wotsSignTarget p pkSeed skSeed adrs digits c := by
  induction fuel generalizing active queue out with
  | zero => omega
  | succ fuel' ih =>
    intro c hc
    unfold signRunUsing
    split
    · rename_i hlen4
      have hne : active ≠ [] := by intro h; simp [h] at hlen4
      rw [four_ok active queue out hinv hlen4]
      dsimp only [signStep4]
      split
      · -- Mixed PRF/HASH path (1 step per lane)
        let stepped := active.map (signStepOneLane p pkSeed adrs)
        have hstep : ∀ l ∈ stepped, SignSteppedValid p pkSeed skSeed adrs digits len l := by
          intro l' hl'
          rw [List.mem_map] at hl'
          obtain ⟨l, hl, rfl⟩ := hl'
          exact signStepOneLane_valid p pkSeed skSeed adrs digits len l (hinv.lanes_valid l hl)
        have hchains : stepped.map (·.chain) = active.map (·.chain) := by
          simp only [stepped, List.map_map]
          apply List.map_congr_left
          intro l _; simp [signStepOneLane]; split <;> rfl
        have hspec := signRetireRefill_spec p pkSeed skSeed adrs digits len stepped queue out hstep
          hinv.queue_valid (by rw [hchains]; exact hinv.nodup_all)
        have hmeas_rr := signRetireRefill_measure skSeed digits stepped queue out
          (fun c hc => (hinv.queue_valid c hc).2)
        have hmeas_step : signMeasure stepped queue < signMeasure active queue := by
          unfold signMeasure
          have hsum : signSumLeft stepped < signSumLeft active :=
            signSumLeft_map_sub active (signStepOneLane p pkSeed adrs) 1 hne (by omega)
              (fun l hl => (hinv.lanes_valid l hl).2.1)
              (fun l _ => by unfold signStepOneLane; split <;> rfl)
          omega
        have hstep_len : stepped.length = 4 := by simp [stepped, hlen4]
        have hlen_rr := signRetireRefill_len_le skSeed digits stepped queue out
        have hlt_rr := signRetireRefill_len_lt_queue_nil skSeed digits stepped queue out
        change (let (a', q', out') := signRetireRefill skSeed digits stepped queue out
          signRunUsing four tail a' q' out' fuel') c = _
        rcases hres : signRetireRefill skSeed digits stepped queue out with ⟨a', q', out'⟩
        rw [hres] at hspec hmeas_rr hlen_rr hlt_rr
        simp only at hlen_rr hlt_rr
        obtain ⟨ha', hq', hnd', _, hret', hpres'⟩ := hspec
        apply ih a' q' out' _ (by omega) (fun hne4 => hlt_rr (by omega)) (by omega) c hc
        refine ⟨ha', hq', hnd', ?_⟩
        intro c' hc' hna hnq
        by_cases hprev : c' ∈ active.map (·.chain) ++ queue
        · exact hret' c' (by rw [hchains]; exact hprev) (by simp [hna, hnq])
        · simp only [List.mem_append, not_or] at hprev
          rw [hpres' c' (by rw [hchains]; exact hprev.1)]
          exact hinv.out_done c' hc' hprev.1 hprev.2
      · -- Fast path: all 4 lanes have `isPrf = false`, advance by `signMinLeft`
        rename_i hno_prf
        have hall_hash : ∀ l ∈ active, l.isPrf = false := by
          intro l hl
          cases hp : l.isPrf
          · rfl
          · exfalso; apply hno_prf; exact List.any_eq_true.mpr ⟨l, hl, hp⟩
        have hm_pos : 0 < signMinLeft active :=
          signMinLeft_pos hne (fun l hl => (hinv.lanes_valid l hl).2.1)
        let fStep : SignLane → SignLane := fun l =>
          ⟨Spec.chain p l.x l.curT (signMinLeft active) pkSeed { adrs with word2 := l.chain },
            l.chain, l.curT + signMinLeft active, l.left - signMinLeft active, false⟩
        let stepped := active.map fStep
        have hstep : ∀ l ∈ stepped, SignSteppedValid p pkSeed skSeed adrs digits len l := by
          intro l' hl'
          rw [List.mem_map] at hl'
          obtain ⟨l, hl, rfl⟩ := hl'
          obtain ⟨hlt, _, _, hhash⟩ := hinv.lanes_valid l hl
          obtain ⟨hsum, hx⟩ := hhash (hall_hash l hl)
          have hm_le : signMinLeft active ≤ l.left := signMinLeft_le hl
          dsimp only [fStep, SignSteppedValid]
          refine ⟨hlt, rfl, by omega, ?_⟩
          rw [hx, ← chain_add]
          simp [Nat.zero_add]
        have hchains : stepped.map (·.chain) = active.map (·.chain) := by
          simp [stepped, fStep, List.map_map, Function.comp_def]
        have hspec := signRetireRefill_spec p pkSeed skSeed adrs digits len stepped queue out hstep
          hinv.queue_valid (by rw [hchains]; exact hinv.nodup_all)
        have hmeas_rr := signRetireRefill_measure skSeed digits stepped queue out
          (fun c hc => (hinv.queue_valid c hc).2)
        have hmeas_step : signMeasure stepped queue < signMeasure active queue := by
          unfold signMeasure
          have hsum : signSumLeft stepped < signSumLeft active :=
            signSumLeft_map_sub active fStep (signMinLeft active) hne hm_pos
              (fun l hl => signMinLeft_le hl) (fun _ _ => rfl)
          omega
        have hstep_len : stepped.length = 4 := by simp [stepped, hlen4]
        have hlen_rr := signRetireRefill_len_le skSeed digits stepped queue out
        have hlt_rr := signRetireRefill_len_lt_queue_nil skSeed digits stepped queue out
        change (let (a', q', out') := signRetireRefill skSeed digits stepped queue out
          signRunUsing four tail a' q' out' fuel') c = _
        rcases hres : signRetireRefill skSeed digits stepped queue out with ⟨a', q', out'⟩
        rw [hres] at hspec hmeas_rr hlen_rr hlt_rr
        simp only at hlen_rr hlt_rr
        obtain ⟨ha', hq', hnd', _, hret', hpres'⟩ := hspec
        apply ih a' q' out' _ (by omega) (fun hne4 => hlt_rr (by omega)) (by omega) c hc
        refine ⟨ha', hq', hnd', ?_⟩
        intro c' hc' hna hnq
        by_cases hprev : c' ∈ active.map (·.chain) ++ queue
        · exact hret' c' (by rw [hchains]; exact hprev) (by simp [hna, hnq])
        · simp only [List.mem_append, not_or] at hprev
          rw [hpres' c' (by rw [hchains]; exact hprev.1)]
          exact hinv.out_done c' hc' hprev.1 hprev.2
    · rename_i hne4
      have hq_nil : queue = [] := hqueue_empty hne4
      subst hq_nil
      split
      · rename_i hpos
        have hne : active ≠ [] := by intro h; simp [h] at hpos
        let stepped := active.map (signStepOneLane p pkSeed adrs)
        have hstep : ∀ l ∈ stepped, SignSteppedValid p pkSeed skSeed adrs digits len l := by
          intro l' hl'
          rw [List.mem_map] at hl'
          obtain ⟨l, hl, rfl⟩ := hl'
          exact signStepOneLane_valid p pkSeed skSeed adrs digits len l (hinv.lanes_valid l hl)
        have hchains : stepped.map (·.chain) = active.map (·.chain) := by
          simp only [stepped, List.map_map]
          apply List.map_congr_left
          intro l _; simp [signStepOneLane]; split <;> rfl
        have hrr_indep := signRetireRefill_nil_indep [] skSeed (fun _ => 0) digits stepped out
        have hspec := signRetireRefill_spec p pkSeed skSeed adrs digits len stepped [] out hstep
          (by simp) (by rw [hchains]; exact hinv.nodup_all)
        have hmeas_rr := signRetireRefill_measure skSeed digits stepped [] out (by simp)
        have hmeas_step : signMeasure stepped [] < signMeasure active [] := by
          unfold signMeasure
          have hsum : signSumLeft stepped < signSumLeft active :=
            signSumLeft_map_sub active (signStepOneLane p pkSeed adrs) 1 hne (by omega)
              (fun l hl => (hinv.lanes_valid l hl).2.1)
              (fun l _ => by unfold signStepOneLane; split <;> rfl)
          omega
        have hlen_rr := signRetireRefill_len_le skSeed digits stepped [] out
        have hstep_len : stepped.length = active.length := by simp [stepped]
        have hq0 := signRetireRefill_nil_queue skSeed digits stepped out
        rw [tail_ok active out hinv hpos (by omega)]
        dsimp only [signStepTail]
        change (let (rem, _, out') := signRetireRefill [] (fun _ => 0) stepped [] out
          signRunUsing four tail rem [] out' fuel') c = _
        rw [hrr_indep]
        rcases hres : signRetireRefill skSeed digits stepped [] out with ⟨a', q', out'⟩
        rw [hres] at hq0
        simp only at hq0
        subst hq0
        rw [hres] at hspec hmeas_rr hlen_rr
        simp only at hlen_rr
        obtain ⟨ha', _, hnd', _, hret', hpres'⟩ := hspec
        apply ih a' [] out' _ (by omega) (fun _ => rfl) (by omega) c hc
        refine ⟨ha', by simp, hnd', ?_⟩
        intro c' hc' hna _
        by_cases hprev : c' ∈ active.map (·.chain)
        · exact hret' c' (by rw [hchains]; simp [hprev]) (by simp [hna])
        · rw [hpres' c' (by rw [hchains]; exact hprev)]
          exact hinv.out_done c' hc' hprev (by simp)
      · rename_i hzero
        have ha_nil : active = [] := List.eq_nil_of_length_eq_zero (by omega)
        exact hinv.out_done c hc (by simp [ha_nil]) (by simp)

/-- **Main theorem for `wots_sign_fused`**:
For ANY duplicate-free schedule `order` covering all chains `0..len` (in particular,
the bucket-sorted descending order of `digits` in `wots_sign_fused_active`),
running `signFusedFull` produces the exact FIPS 205 WOTS+ signature element
`Spec.chain p (Spec.PRF p pkSeed skSeed { wotsSkAdrs adrs with word2 := c }) 0 (digits c) pkSeed { adrs with word2 := c }`
for EVERY chain `0 ≤ c < len` (including `digits c = 0` and `digits c = 15`). -/
theorem sign_using_scheduler_eq_fips (p : Spec.Params) (pkSeed skSeed : Spec.Bytes) (adrs : Spec.Adrs)
    (digits : Nat → Nat) (len : Nat) (order : List Nat)
    (four : FourStep) (tail : TailStep)
    (four_ok : ∀ a q o, SignInv p pkSeed skSeed adrs digits len a q o → a.length = 4 →
      four a q o = signStep4 p pkSeed skSeed adrs digits a q o)
    (tail_ok : ∀ a o, SignInv p pkSeed skSeed adrs digits len a [] o → 0 < a.length → a.length < 4 →
      tail a o = signStepTail p pkSeed adrs a o)
    (hdig : ∀ c < len, digits c ≤ 15)
    (hnd : order.Nodup)
    (hmem : ∀ c, c ∈ order ↔ c < len) :
    ∀ c < len, signFusedUsing skSeed digits order four tail c =
      Spec.chain p (Spec.PRF p pkSeed skSeed { Spec.wotsSkAdrs adrs with word2 := c })
        0 (digits c) pkSeed { adrs with word2 := c } := by
  unfold signFusedUsing
  set initActive := (order.take 4).map fun c => (⟨skSeed, c, 0, 1 + digits c, true⟩ : SignLane)
  set initQueue := order.drop 4
  have hchains : initActive.map (·.chain) ++ initQueue = order := by
    simp [initActive, initQueue, List.map_map, Function.comp_def, List.take_append_drop]
  apply signRunUsing_eq_fips p pkSeed skSeed adrs digits len four tail four_ok tail_ok initActive initQueue (fun _ => []) _
  · refine ⟨?_, ?_, by rw [hchains]; exact hnd, ?_⟩
    · intro l hl
      rw [List.mem_map] at hl
      obtain ⟨c, hc, rfl⟩ := hl
      have hc' : c < len := (hmem c).mp (List.mem_of_mem_take hc)
      dsimp only
      exact ⟨hc', by omega, fun _ => ⟨rfl, rfl, rfl⟩, fun h => by cases h⟩
    · intro c hc
      have hc' : c < len := (hmem c).mp (List.mem_of_mem_drop hc)
      exact ⟨hc', hdig c hc'⟩
    · intro c hc hna hnq
      exfalso
      have hnot : c ∉ order := by
        rw [← hchains, List.mem_append, not_or]; exact ⟨hna, hnq⟩
      exact hnot ((hmem c).mpr hc)
  · simp [initActive]
  · intro hne4
    have hlt : order.length < 4 := by
      simp only [initActive, List.length_map, List.length_take] at hne4
      omega
    exact List.drop_eq_nil_of_le (by omega)
  · exact Nat.lt_succ_self _

theorem sign_fused_scheduler_eq_fips (p : Spec.Params) (pkSeed skSeed : Spec.Bytes) (adrs : Spec.Adrs)
    (digits : Nat → Nat) (len : Nat) (order : List Nat)
    (hdig : ∀ c < len, digits c ≤ 15)
    (hnd : order.Nodup)
    (hmem : ∀ c, c ∈ order ↔ c < len) :
    ∀ c < len, signFusedFull p pkSeed skSeed adrs digits order c =
      Spec.chain p (Spec.PRF p pkSeed skSeed { Spec.wotsSkAdrs adrs with word2 := c })
        0 (digits c) pkSeed { adrs with word2 := c } :=
  sign_using_scheduler_eq_fips p pkSeed skSeed adrs digits len order
    (signStep4 p pkSeed skSeed adrs digits) (signStepTail p pkSeed adrs)
    (by intros; rfl) (by intros; rfl) hdig hnd hmem

/-- Edge-case corollary: for a chain with `digits c = 0`, `signFusedFull` retires immediately
after `PRF` with 0 `F` steps, outputting `Spec.PRF p pkSeed skSeed { wotsSkAdrs adrs with word2 := c }`. -/
theorem sign_fused_digit_zero (p : Spec.Params) (pkSeed skSeed : Spec.Bytes) (adrs : Spec.Adrs)
    (digits : Nat → Nat) (len : Nat) (order : List Nat) (c : Nat)
    (hdig : ∀ i < len, digits i ≤ 15) (hnd : order.Nodup) (hmem : ∀ i, i ∈ order ↔ i < len)
    (hc : c < len) (hz : digits c = 0) :
    signFusedFull p pkSeed skSeed adrs digits order c =
      Spec.PRF p pkSeed skSeed { Spec.wotsSkAdrs adrs with word2 := c } := by
  have h := sign_fused_scheduler_eq_fips p pkSeed skSeed adrs digits len order hdig hnd hmem c hc
  simpa [hz, Spec.chain] using h

/-- Edge-case corollary: for a chain with `digits c = 15`, `signFusedFull` computes `PRF`
followed by all 15 FIPS 205 `chain` steps. -/
theorem sign_fused_digit_fifteen (p : Spec.Params) (pkSeed skSeed : Spec.Bytes) (adrs : Spec.Adrs)
    (digits : Nat → Nat) (len : Nat) (order : List Nat) (c : Nat)
    (hdig : ∀ i < len, digits i ≤ 15) (hnd : order.Nodup) (hmem : ∀ i, i ∈ order ↔ i < len)
    (hc : c < len) (hf : digits c = 15) :
    signFusedFull p pkSeed skSeed adrs digits order c =
      Spec.chain p (Spec.PRF p pkSeed skSeed { Spec.wotsSkAdrs adrs with word2 := c })
        0 15 pkSeed { adrs with word2 := c } := by
  have h := sign_fused_scheduler_eq_fips p pkSeed skSeed adrs digits len order hdig hnd hmem c hc
  simpa [hf] using h

#print axioms sort_descending_spec
#print axioms recover_scheduler_eq_fips
#print axioms recover_with_extracted_sort
#print axioms recover_all_fifteen
#print axioms recover_all_zero
#print axioms sign_fused_scheduler_eq_fips
#print axioms sign_fused_digit_zero
#print axioms sign_fused_digit_fifteen

end slhdsa.Armwide.WotsRefill
