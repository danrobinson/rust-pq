import Shakeopt.Sort.Funs
import Shakeopt.ForsHoriz
import Mathlib.Data.List.Perm.Basic
import Mathlib.Tactic.Ring

/-!
# Dynamic Lane-Refill SHAKE WOTS+ (`rust/src/shake/batch.rs`)

Proves:
1. Extracted `shake::batch::sort_descending` terminates and returns `(order, total)`
   forming a descending-sorted bijection onto `{i < steps.len() | steps[i] > 0}`
   (and a permutation of `0..len` when all steps are nonzero).
2. Batched `shake::batch::keygen` equals FIPS 205 Algorithm 6 (`Spec.wotsPkGen`).
3. Dynamic lane-refill engine (`permute_active` + refill / swap-remove compaction)
   terminates and computes exact chain endpoints for every chain `0..len`, yielding:
   - `wots_sign_refill_eq`: FIPS 205 Algorithm 7 (`Spec.wotsSign`),
   - `wots_recover_refill_eq`: FIPS 205 Algorithm 8 (`Spec.wotsPkFromSig`).
-/

namespace Shakeopt.WotsRefill

open Aeneas Aeneas.Std Result
open Spec

/-! ## Part 1: Extracted `shake::batch::sort_descending` -/

/-- Number of entries strictly greater than `d` in `xs`. -/
def above (xs : List U32) (d : Nat) : Nat :=
  xs.countP (fun x => decide (d < x.val))

/-- Number of entries equal to `d` in the first `n` elements of `xs`. -/
def counted (xs : List U32) (n d : Nat) : Nat :=
  (xs.take n).countP (fun x => decide (x.val = d))

/-- Descending counting-sort output slot for index `i` (with `steps[i] > 0`). -/
def descRank (xs : List U32) (i : Nat) : Nat :=
  above xs xs[i]!.val + counted xs i xs[i]!.val

private theorem above_pred (xs : List U32) {d : Nat} (hd : 1 ≤ d) :
    above xs (d - 1) = above xs d + counted xs xs.length d := by
  simp only [above, counted, List.take_length]
  induction xs with
  | nil => simp
  | cons x rest ih =>
    simp only [List.countP_cons, decide_eq_true_eq]
    split_ifs <;> omega

private theorem above_mono (xs : List U32) {a b : Nat} (hle : a ≤ b) :
    above xs b ≤ above xs a :=
  List.countP_mono_left (by intro x _ h; simp only [decide_eq_true_eq] at h ⊢; omega)

private theorem above_top (xs : List U32) (hsmall : ∀ i < xs.length, xs[i]!.val < 16) :
    above xs 15 = 0 := by
  unfold above
  rw [List.countP_eq_zero]
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
  have hlt := hsmall i hi
  rw [getElem!_pos xs i hi] at hlt
  simp only [decide_eq_true_eq]
  omega

private theorem above_le_length (xs : List U32) (d : Nat) : above xs d ≤ xs.length :=
  List.countP_le_length

private theorem count_next (xs : List U32) (i d : Nat) (hi : i < xs.length) :
    counted xs (i + 1) d = counted xs i d + (if xs[i]!.val = d then 1 else 0) := by
  rw [counted, List.take_succ_eq_append_getElem hi, List.countP_append]
  simp [counted, hi]

private theorem count_mono (xs : List U32) (d : Nat) {a b : Nat} (hle : a ≤ b) :
    counted xs a d ≤ counted xs b d := by
  unfold counted
  rw [show b = a + (b - a) by omega, List.take_add, List.countP_append]
  omega

private theorem count_strict (xs : List U32) {a b : Nat} (ha : a < xs.length) (hab : a < b) :
    counted xs a xs[a]!.val < counted xs b xs[a]!.val := by
  have hmono := count_mono xs xs[a]!.val (show a + 1 ≤ b by omega)
  rw [count_next xs a _ ha, ite_eq_left rfl] at hmono
  omega

private theorem in_desc_bucket (xs : List U32) {i : Nat} (hi : i < xs.length)
    (hpos : 0 < xs[i]!.val) :
    above xs xs[i]!.val ≤ descRank xs i ∧ descRank xs i < above xs (xs[i]!.val - 1) := by
  have hless := count_strict xs hi hi
  simp only [descRank, above_pred xs (show 1 ≤ xs[i]!.val by omega)]
  omega

theorem descRank_lt (xs : List U32) {i : Nat} (hi : i < xs.length) (hpos : 0 < xs[i]!.val) :
    descRank xs i < above xs 0 :=
  Nat.lt_of_lt_of_le (in_desc_bucket xs hi hpos).2 (above_mono xs (Nat.zero_le _))

theorem descRank_injective (xs : List U32) {i j : Nat}
    (hi : i < xs.length) (hj : j < xs.length)
    (hpi : 0 < xs[i]!.val) (hpj : 0 < xs[j]!.val)
    (heq : descRank xs i = descRank xs j) : i = j := by
  have bi := in_desc_bucket xs hi hpi
  have bj := in_desc_bucket xs hj hpj
  have hval : xs[i]!.val = xs[j]!.val := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · have hle : above xs (xs[j]!.val - 1) ≤ above xs xs[i]!.val := above_mono xs (by omega)
      omega
    · have hle : above xs (xs[i]!.val - 1) ≤ above xs xs[j]!.val := above_mono xs (by omega)
      omega
  unfold descRank at heq
  rw [hval] at heq
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · have h := count_strict xs hi hlt; rw [hval] at h; omega
  · have h := count_strict xs hj hgt; omega

theorem descRank_antitone (xs : List U32) {i j : Nat}
    (hi : i < xs.length) (hj : j < xs.length)
    (hpi : 0 < xs[i]!.val) (hpj : 0 < xs[j]!.val)
    (hle : descRank xs i ≤ descRank xs j) : xs[j]!.val ≤ xs[i]!.val := by
  by_contra hgt
  have hlt : xs[i]!.val < xs[j]!.val := by omega
  have bi := in_desc_bucket xs hi hpi
  have bj := in_desc_bucket xs hj hpj
  have hab : above xs (xs[j]!.val - 1) ≤ above xs xs[i]!.val := above_mono xs (by omega)
  omega

private theorem exists_with_counted (xs : List U32) (d : Nat) :
    ∀ n ≤ xs.length, ∀ r < counted xs n d,
      ∃ i < n, xs[i]!.val = d ∧ counted xs i d = r
  | 0, _, _, hr => by simp [counted] at hr
  | n + 1, hn, r, hr => by
    rw [count_next xs n d (by omega)] at hr
    by_cases hlt : r < counted xs n d
    · obtain ⟨i, hi, hv, hc⟩ := exists_with_counted xs d n (by omega) r hlt
      exact ⟨i, by omega, hv, hc⟩
    · split_ifs at hr with heq
      · exact ⟨n, Nat.lt_succ_self n, heq, by omega⟩
      · omega

private theorem exists_bucket (xs : List U32) (j : Nat) :
    ∀ b, above xs b ≤ j → j < above xs 0 →
      ∃ d, 1 ≤ d ∧ d ≤ b ∧ above xs d ≤ j ∧ j < above xs (d - 1)
  | 0, hlo, hhi => by omega
  | b + 1, hlo, hhi => by
    by_cases hlt : j < above xs b
    · exact ⟨b + 1, by omega, Nat.le_refl _, hlo, hlt⟩
    · obtain ⟨d, h1, hle, h2, h3⟩ := exists_bucket xs j b (by omega) hhi
      exact ⟨d, h1, by omega, h2, h3⟩

theorem descRank_surjective (xs : List U32) (hsmall : ∀ i < xs.length, xs[i]!.val < 16)
    {j : Nat} (hj : j < above xs 0) :
    ∃ i < xs.length, 0 < xs[i]!.val ∧ descRank xs i = j := by
  have htop : above xs 15 = 0 := above_top xs hsmall
  obtain ⟨d, hd1, _, hlo, hhi⟩ := exists_bucket xs j 15 (by omega) hj
  rw [above_pred xs hd1] at hhi
  obtain ⟨i, hi, hval, hcnt⟩ :=
    exists_with_counted xs d xs.length (Nat.le_refl _) (j - above xs d) (by omega)
  refine ⟨i, hi, by omega, ?_⟩
  simp only [descRank, hval, hcnt]
  omega

private theorem set_getElem!_same {α : Type _} [Inhabited α] (xs : List α) (i : Nat) (v : α)
    (hi : i < xs.length) : (xs.set i v)[i]! = v := by
  rw [getElem!_pos (xs.set i v) i (by simp [hi]), List.getElem_set_self]

private theorem set_getElem!_ne {α : Type _} [Inhabited α] (xs : List α) (i j : Nat) (v : α)
    (hne : i ≠ j) : (xs.set i v)[j]! = xs[j]! := by
  by_cases hj : j < xs.length
  · rw [getElem!_pos (xs.set i v) j (by simp [hj]), getElem!_pos xs j hj, List.getElem_set_ne hne]
  · rw [getElem!_neg (xs.set i v) j (by simp [hj]), getElem!_neg xs j hj]

private theorem posCount_next (xs : List U32) (i : Nat) (hi : i < xs.length) :
    (xs.take (i + 1)).countP (fun x => decide (0 < x.val)) =
      (xs.take i).countP (fun x => decide (0 < x.val)) + (if 0 < xs[i]!.val then 1 else 0) := by
  rw [List.take_succ_eq_append_getElem hi, List.countP_append]
  simp [hi]

private theorem sort_descending_loop0_spec (steps : Slice U32) (hlen : steps.length ≤ 67)
    (hsmall : ∀ i < steps.length, steps.val[i]!.val < 16) :
    ShakeoptSort.shake.batch.sort_descending_loop0 ⟨steps, 0⟩ (Array.repeat 16#usize 0#usize) 0#usize
      ⦃ out =>
        (∀ d, 1 ≤ d → d < 16 → out.1.val[d]!.val = counted steps.val steps.length d) ∧
        out.2.val = above steps.val 0 ⦄ := by
  unfold ShakeoptSort.shake.batch.sort_descending_loop0
  apply loop.spec_decr_nat
    (measure := fun q : core.slice.iter.Iter U32 × Array Usize 16#usize × Usize => steps.length - q.1.i)
    (inv := fun q =>
      q.1.slice = steps ∧ q.1.i ≤ steps.length ∧
      (∀ d, 1 ≤ d → d < 16 → q.2.1.val[d]!.val = counted steps.val q.1.i d) ∧
      q.2.2.val = (steps.val.take q.1.i).countP (fun x => decide (0 < x.val)))
  · rintro ⟨⟨ds, i⟩, counts, total⟩ ⟨rfl, hle, hcnt, htot⟩
    simp only at hle hcnt htot hlen hsmall
    unfold ShakeoptSort.shake.batch.sort_descending_loop0.body core.slice.iter.IteratorSliceIter.next
    by_cases live : i < ds.length
    · have sz : i < ds.val.length := live
      have hl : i < ds.len.val := by simpa using live
      simp only [dite_eq_left hl, bind_ok]
      change (if ds[i] > 0#u32 then _ else _) ⦃ _ ⦄
      split_ifs with hgt
      · have hpos : 0 < ds.val[i]!.val := by
          rw [getElem!_pos ds.val i sz]
          exact hgt
        simp only [lift]
        have hdigit := hsmall i live
        have hidx : (UScalar.cast .Usize ds[i]).val = ds.val[i]!.val := by
          rw [UScalar.cast_val_eq, getElem!_pos ds.val i sz, Nat.mod_eq_of_lt (by scalar_tac)]
          rfl
        step as ⟨old, hget⟩
        have hold : old.val = counted ds.val i ds.val[i]!.val := by
          rw [hget, ← getElem!_pos, hidx, hcnt _ (by omega) hdigit]
        have hmaxc : counted ds.val i ds.val[i]!.val ≤ ds.length := by
          have := List.countP_le_length (p := fun x : U32 => decide (x.val = ds.val[i]!.val)) (l := ds.val.take i)
          simp only [counted, List.length_take] at this ⊢; omega
        have hmaxt : total.val ≤ ds.length := by
          rw [htot]
          have := List.countP_le_length (p := fun x : U32 => decide (0 < x.val)) (l := ds.val.take i)
          simp only [List.length_take] at this; omega
        step as ⟨newC, hnewC⟩
        step as ⟨counts', hset⟩
        step as ⟨total', htot'⟩
        refine ⟨by omega, ?_, ?_, by omega⟩
        · intro d hd1 hd16
          rw [count_next _ _ _ sz, hset, Array.set_val_eq, hidx]
          by_cases hsame : ds.val[i]!.val = d
          · subst d
            rw [set_getElem!_same _ _ _ (by simpa using hdigit), hnewC, hold, ite_eq_left rfl]
          · rw [set_getElem!_ne _ _ _ _ hsame, hcnt _ hd1 hd16, ite_eq_right hsame, Nat.add_zero]
        · rw [posCount_next ds.val i sz, ite_eq_left hpos, htot', htot]
      · have hzero : ¬ 0 < ds.val[i]!.val := by
          rw [getElem!_pos ds.val i sz]
          intro hc; exact hgt hc
        simp only [step_simps]
        refine ⟨by omega, ?_, ?_, by omega⟩
        · intro d hd1 hd16
          rw [count_next _ _ _ sz, ite_eq_right (by omega), Nat.add_zero]
          exact hcnt d hd1 hd16
        · rw [posCount_next ds.val i sz, ite_eq_right hzero, Nat.add_zero, htot]
    · have hl : ¬ i < ds.len.val := by simpa using live
      simp only [dite_eq_right hl, step_simps]
      have hend : i = ds.length := by omega
      subst hend
      exact ⟨hcnt, by simpa [above, Slice.length] using htot⟩
  · refine ⟨rfl, Nat.zero_le _, ?_, by simp⟩
    intro d hd1 hd16
    change ((Array.repeat 16#usize 0#usize).val[d]!).val = 0
    rw [Array.repeat_val, List.getElem!_replicate 0#usize (show d < (16#usize).val from hd16)]
    rfl

private theorem rev_range_next_spec (r : core.ops.range.Range Usize) :
    core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
      (core.ops.range.Range.Insts.DoubleEndedIterator core.iter.range.StepUsize) ⟨r⟩
      ⦃ o it =>
        if r.start.val < r.«end».val then
          ∃ e' : Usize, o = some e' ∧ e'.val = r.«end».val - 1 ∧
            it = ⟨{ r with «end» := e' }⟩
        else
          o = none ∧ it = ⟨r⟩ ⦄ := by
  simp only [core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next,
    core.ops.range.Range.Insts.CoreIterTraitsDoubleEndedIterator.next_back,
    core.iter.range.StepUsize, core.iter.range.UScalarStep,
    core.iter.range.UScalarStep.backward_checked, bind_ok]
  have hlt_eq : core.cmp.impls.PartialOrdUsize.lt r.start r.«end» = decide (r.start.val < r.«end».val) := rfl
  rw [hlt_eq]
  by_cases hlt : r.start.val < r.«end».val
  · simp only [hlt, decide_true, ↓reduceIte]
    have hge1 : (1#usize).val ≤ r.«end».val := by scalar_tac
    simp only [hge1, ↓reduceDIte, bind_ok]
    simp [WP.spec_ok, UScalar.ofNatCore_val_eq]
  · simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte, bind_ok]
    simp [WP.spec_ok]

private theorem sort_descending_loop1_spec (steps : Slice U32) (_hlen : steps.length ≤ 67)
    (hsmall : ∀ i < steps.length, steps.val[i]!.val < 16)
    (counts : Array Usize 16#usize)
    (hcnt : ∀ d, 1 ≤ d → d < 16 → counts.val[d]!.val = counted steps.val steps.length d) :
    ShakeoptSort.shake.batch.sort_descending_loop1
      ⟨{ start := 1#usize, «end» := 16#usize }⟩ counts (Array.repeat 16#usize 0#usize) 0#usize
      ⦃ offsets =>
        ∀ d, 1 ≤ d → d < 16 → offsets.val[d]!.val = above steps.val d ⦄ := by
  unfold ShakeoptSort.shake.batch.sort_descending_loop1
  apply loop.spec_decr_nat
    (measure := fun q : core.iter.adapters.rev.Rev (core.ops.range.Range Usize) × Array Usize 16#usize × Usize =>
      q.1.iter.«end».val - 1)
    (inv := fun q =>
      q.1.iter.start = 1#usize ∧ 1 ≤ q.1.iter.«end».val ∧ q.1.iter.«end».val ≤ 16 ∧
      q.2.2.val = above steps.val (q.1.iter.«end».val - 1) ∧
      ∀ d, q.1.iter.«end».val ≤ d → d < 16 → q.2.1.val[d]!.val = above steps.val d)
  · rintro ⟨⟨r⟩, offsets, pos⟩ ⟨hstart, hge1, hle16, hpos, hoff⟩
    simp only at hstart hge1 hle16 hpos hoff
    unfold ShakeoptSort.shake.batch.sort_descending_loop1.body
    let* ⟨ o, it, hp ⟩ ← rev_range_next_spec r
    by_cases hlt : r.start.val < r.«end».val
    · simp only [hlt, ↓reduceIte] at hp
      rcases hp with ⟨b, rfl, hbval, rfl⟩
      have hb_ge1 : 1 ≤ b.val := by rw [hbval]; rw [hstart] at hlt; scalar_tac
      have hb_lt16 : b.val < 16 := by omega
      step as ⟨offsets', hset⟩
      step as ⟨c, hc⟩
      have hcval : c.val = counted steps.val steps.length b.val := by
        rw [hc, ← getElem!_pos, hcnt _ hb_ge1 hb_lt16]
      have hsum_le : pos.val + c.val ≤ steps.length := by
        rw [hpos, hcval, show r.«end».val - 1 = b.val by omega, ← above_pred steps.val hb_ge1]
        exact above_le_length steps.val (b.val - 1)
      step as ⟨pos', hpos'⟩
      refine ⟨hstart, by omega, by omega, ?_, ?_, by omega⟩
      · rw [hpos', hpos, hcval, show r.«end».val - 1 = b.val by omega, ← above_pred steps.val hb_ge1]
      · intro d hd_ge hd_lt
        rw [hset, Array.set_val_eq]
        by_cases hsame : b.val = d
        · subst d
          rw [set_getElem!_same _ _ _ (by simpa using hb_lt16), hpos, show r.«end».val - 1 = b.val by omega]
        · rw [set_getElem!_ne _ _ _ _ hsame]
          exact hoff d (by omega) hd_lt
    · simp only [hlt, ↓reduceIte] at hp
      rcases hp with ⟨rfl, rfl⟩
      simp only [step_simps]
      have hend1 : r.«end».val = 1 := by rw [hstart] at hlt; scalar_tac
      intro d hd1 hd16
      exact hoff d (by omega) hd16
  · simp only
    refine ⟨trivial, by decide, by decide, ?_, fun d hd1 hd2 => by scalar_tac⟩
    change (0#usize).val = above steps.val (16 - 1)
    exact (above_top steps.val hsmall).symm

private theorem sort_descending_loop2_spec (steps : Slice U32) (hlen : steps.length ≤ 67)
    (hsmall : ∀ i < steps.length, steps.val[i]!.val < 16)
    (offsets : Array Usize 16#usize)
    (hoff : ∀ d, 1 ≤ d → d < 16 → offsets.val[d]!.val = above steps.val d) :
    ShakeoptSort.shake.batch.sort_descending_loop2
      { iter := ⟨steps, 0⟩, count := 0#usize } offsets (Array.repeat 67#usize 0#usize)
      ⦃ order =>
        ∀ i < steps.length, 0 < steps.val[i]!.val → order.val[descRank steps.val i]!.val = i ⦄ := by
  unfold ShakeoptSort.shake.batch.sort_descending_loop2
  apply loop.spec_decr_nat
    (measure := fun q : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter U32) ×
        Array Usize 16#usize × Array Usize 67#usize => steps.length - q.1.iter.i)
    (inv := fun q =>
      q.1.iter.slice = steps ∧ q.1.iter.i ≤ steps.length ∧ q.1.count.val = q.1.iter.i ∧
      (∀ d, 1 ≤ d → d < 16 → q.2.1.val[d]!.val = above steps.val d + counted steps.val q.1.iter.i d) ∧
      (∀ i < q.1.iter.i, 0 < steps.val[i]!.val → q.2.2.val[descRank steps.val i]!.val = i))
  · rintro ⟨⟨⟨ds, i⟩, cnt⟩, offs, ord⟩ ⟨rfl, hle, hcnt_eq, hoffs, hord⟩
    simp only at hle hcnt_eq hoffs hord hlen hsmall
    unfold ShakeoptSort.shake.batch.sort_descending_loop2.body
      core.iter.adapters.enumerate.IteratorEnumerate.next
      core.iter.traits.iterator.IteratorSliceIter
      core.slice.iter.IteratorSliceIter.next
    by_cases live : i < ds.length
    · have sz : i < ds.val.length := live
      have hl : i < ds.len.val := by simpa using live
      simp only [dite_eq_left hl, bind_ok]
      have hcnt_room : cnt.val + 1 ≤ Usize.max := by scalar_tac
      step as ⟨cnt1, hcnt1⟩
      change (if ds[i] > 0#u32 then _ else _) ⦃ _ ⦄
      split_ifs with hgt
      · have hpos : 0 < ds.val[i]!.val := by
          rw [getElem!_pos ds.val i sz]; exact hgt
        simp only [lift]
        have hdigit := hsmall i live
        have hidx : (UScalar.cast .Usize ds[i]).val = ds.val[i]!.val := by
          rw [UScalar.cast_val_eq, getElem!_pos ds.val i sz, Nat.mod_eq_of_lt (by scalar_tac)]
          rfl
        step as ⟨slot, back, hslot, hback⟩
        have hslot_eq : slot.val = descRank ds.val i := by
          rw [hslot, ← getElem!_pos, hidx, hoffs _ (by omega) hdigit]; rfl
        have hslot_lt : slot.val < 67 := by
          have h1 := descRank_lt ds.val sz hpos
          have h2 := above_le_length ds.val 0
          have h3 : ds.val.length ≤ 67 := hlen
          omega
        step as ⟨ord', hord'⟩
        step as ⟨slot1, hslot1⟩
        refine ⟨by omega, by omega, ?_, ?_, by omega⟩
        · intro d hd1 hd16
          rw [hback, Array.set_val_eq, hidx, count_next _ _ _ sz]
          by_cases hsame : ds.val[i]!.val = d
          · subst d
            rw [set_getElem!_same _ _ _ (by simpa using hdigit), hslot1, hslot_eq, ite_eq_left rfl]
            simp only [descRank]; omega
          · rw [set_getElem!_ne _ _ _ _ hsame, hoffs _ hd1 hd16, ite_eq_right hsame, Nat.add_zero]
        · intro k hk hpk
          rw [hord', Array.set_val_eq, hslot_eq]
          by_cases hki : k = i
          · subst k
            rw [set_getElem!_same _ _ _ (by rw [← hslot_eq]; simpa using hslot_lt), hcnt_eq]
          · have hne : descRank ds.val i ≠ descRank ds.val k := by
              intro heq
              exact hki (descRank_injective ds.val (by omega) sz hpk hpos heq.symm)
            rw [set_getElem!_ne _ _ _ _ hne]
            exact hord k (by omega) hpk
      · have hzero : ¬ 0 < ds.val[i]!.val := by
          rw [getElem!_pos ds.val i sz]; intro hc; exact hgt hc
        simp only [step_simps]
        refine ⟨by omega, by omega, ?_, ?_, by omega⟩
        · intro d hd1 hd16
          rw [count_next _ _ _ sz, ite_eq_right (by omega), Nat.add_zero]
          exact hoffs d hd1 hd16
        · intro k hk hpk
          have hki : k ≠ i := by intro heq; subst heq; exact hzero hpk
          exact hord k (by omega) hpk
    · have hl : ¬ i < ds.len.val := by simpa using live
      simp only [dite_eq_right hl, bind_ok, step_simps]
      have hend : i = ds.length := by omega
      subst hend
      exact hord
  · simp only
    refine ⟨trivial, Nat.zero_le _, rfl, ?_, fun _ h => by omega⟩
    intro d hd1 hd16
    rw [show counted steps.val 0 d = 0 from rfl, Nat.add_zero]
    exact hoff d hd1 hd16

/-- **Headline Theorem (Extracted `sort_descending` Correctness)**:
    For every `steps` slice of length `≤ 67` with values `< 16`, the extracted Rust function
    `shake::batch::sort_descending` terminates and returns `(order, total)` where:
    - `total` is the exact count of nonzero entries,
    - `order[0..total]` is a bijection onto `{i < steps.len() | steps[i] > 0}`,
    - `order[0..total]` is pairwise distinct (`Nodup`), and
    - `steps[order[j]]` is monotonically non-increasing for `j ∈ 0..total`. -/
theorem sort_descending_spec (steps : Slice U32) (hlen : steps.length ≤ 67)
    (hsmall : ∀ i < steps.length, steps.val[i]!.val < 16) :
    ShakeoptSort.shake.batch.sort_descending steps ⦃ res =>
      let order := res.1
      let total := res.2
      total.val = above steps.val 0 ∧
      total.val ≤ steps.length ∧
      (∀ i < steps.length, 0 < steps.val[i]!.val →
        descRank steps.val i < total.val ∧ order.val[descRank steps.val i]!.val = i) ∧
      (∀ j < total.val,
        order.val[j]!.val < steps.length ∧
        0 < steps.val[order.val[j]!.val]!.val ∧
        descRank steps.val (order.val[j]!.val) = j) ∧
      ((order.val.take total.val).map UScalar.val).Nodup ∧
      (∀ j₁ j₂, j₁ ≤ j₂ → j₂ < total.val →
        steps.val[order.val[j₂]!.val]!.val ≤ steps.val[order.val[j₁]!.val]!.val) ⦄ := by
  unfold ShakeoptSort.shake.batch.sort_descending
  simp only [SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter, bind_ok]
  let* ⟨ counts1, total1, hcnt, htot ⟩ ← sort_descending_loop0_spec steps hlen hsmall
  simp only [core.iter.traits.iterator.Iterator.rev.trait_default,
    core.iter.traits.iterator.Iterator.rev.default, bind_ok]
  let* ⟨ offsets, hoff ⟩ ← sort_descending_loop1_spec steps hlen hsmall counts1 hcnt
  simp only [core.slice.Slice.iter, core.iter.traits.iterator.Iterator.enumerate.trait_default,
    core.iter.traits.iterator.Iterator.enumerate.default, bind_ok]
  let* ⟨ order, hord ⟩ ← sort_descending_loop2_spec steps hlen hsmall offsets hoff
  have hle_len : total1.val ≤ steps.length := by rw [htot]; exact above_le_length steps.val 0
  have hinv : ∀ j < total1.val,
      order.val[j]!.val < steps.length ∧
      0 < steps.val[order.val[j]!.val]!.val ∧
      descRank steps.val (order.val[j]!.val) = j := by
    intro j hj
    rw [htot] at hj
    obtain ⟨i, hi, hpi, hr⟩ := descRank_surjective steps.val hsmall hj
    have hget := hord i hi hpi
    rw [hr] at hget
    rw [hget]
    exact ⟨hi, hpi, hr⟩
  have hnodup : ((order.val.take total1.val).map UScalar.val).Nodup := by
    rw [List.nodup_iff_injective_getElem]
    intro ⟨a, ha⟩ ⟨b, hb⟩ heq
    have hlen_ord : order.val.length = 67 := by simp
    have ha' : a < total1.val := by simp [hlen_ord] at ha; omega
    have hb' : b < total1.val := by simp [hlen_ord] at hb; omega
    simp only [List.getElem_map, List.getElem_take] at heq
    have hfa := (hinv a ha').2.2
    have hfb := (hinv b hb').2.2
    rw [getElem!_pos order.val a (by omega)] at hfa
    rw [getElem!_pos order.val b (by omega)] at hfb
    ext
    exact hfa.symm.trans ((congrArg (descRank steps.val) heq).trans hfb)
  refine ⟨htot, hle_len, ?_, hinv, hnodup, ?_⟩
  · intro i hi hpi
    exact ⟨by rw [htot]; exact descRank_lt steps.val hi hpi, hord i hi hpi⟩
  · intro j₁ j₂ h12 hj2
    have h1 := hinv j₁ (by omega)
    have h2 := hinv j₂ hj2
    exact descRank_antitone steps.val h1.1 h2.1 h1.2.1 h2.2.1 (by omega)

/-- Corollary: when all entries of `steps` are positive (`steps[i] > 0`), `sort_descending`
    returns `total = steps.len()` and `order[0..len]` is a permutation of `0..len`. -/
theorem sort_descending_perm (steps : Slice U32) (hlen : steps.length ≤ 67)
    (hsmall : ∀ i < steps.length, steps.val[i]!.val < 16)
    (hallpos : ∀ i < steps.length, 0 < steps.val[i]!.val) :
    ShakeoptSort.shake.batch.sort_descending steps ⦃ res =>
      res.2.val = steps.length ∧
      List.Perm ((res.1.val.take res.2.val).map UScalar.val) (List.range steps.length) ⦄ := by
  apply WP.spec_mono (sort_descending_spec steps hlen hsmall)
  rintro ⟨order, total⟩ ⟨htot, hle, hfwd, hinv, hnodup, _⟩
  have habove_all : above steps.val 0 = steps.length := by
    unfold above
    rw [List.countP_eq_length]
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
    have hp := hallpos i hi
    rw [getElem!_pos steps.val i hi] at hp
    simpa using hp
  have htot_eq : total.val = steps.length := by rw [htot, habove_all]
  refine ⟨htot_eq, ?_⟩
  rw [List.perm_ext_iff_of_nodup hnodup List.nodup_range]
  intro x
  simp only [List.mem_range, List.mem_map]
  constructor
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hu
    have hord_len : order.val.length = 67 := by simp
    have hj_lt : j < total.val := by
      rw [List.length_take, hord_len] at hj; omega
    have h := (hinv j hj_lt).1
    rw [getElem!_pos order.val j (by omega)] at h
    simpa only [List.getElem_take] using h
  · intro hx
    obtain ⟨hrlt, hget⟩ := hfwd x hx (hallpos x hx)
    have hord_len : order.val.length = 67 := by simp
    refine ⟨order.val[descRank steps.val x]!, ?_, hget⟩
    rw [getElem!_pos order.val _ (by omega)]
    have hmem : order.val[descRank steps.val x]'(by omega) =
        (order.val.take total.val)[descRank steps.val x]'(by rw [List.length_take, hord_len]; omega) :=
      (List.getElem_take (xs := order.val) (i := descRank steps.val x) (j := total.val)
        (h := by rw [List.length_take, hord_len]; omega)).symm
    rw [hmem]
    exact List.getElem_mem _

/-! ## Part 2: Batched `keygen` (FIPS 205 Algorithm 6) -/

/-- One WOTS+ chain stepped `steps` times from `x` at chain index `id` starting at `start`. -/
private theorem chain_succ (p : Params) (x pk : Bytes) (adrs : Adrs) (start s : Nat) :
    chain p x start (s + 1) pk adrs =
      F p pk { adrs with word3 := start + s } (chain p x start s pk adrs) := by
  simp [chain, List.range_succ]

/-- Model of `shake::batch::keygen` (lines 184–212): processes `p.len` chains in active
    batches of `width`, running `WOTS_PRF` + `p.w - 1` rounds of `WOTS_HASH` and absorbing
    endpoints in ascending order into the `WOTS_PK` sponge. -/
def wotsKeygenBatch (width : Nat) (hw : 0 < width) (p : Params) (sk pk : Bytes) (adrs : Adrs) :
    Bytes :=
  let endpoints := ForsHoriz.batchChunks width p.len hw fun i =>
    let secret := PRF p pk sk { wotsSkAdrs adrs with word2 := i }
    (List.range (p.w - 1)).foldl
      (fun v step => F p pk { adrs with word2 := i, word3 := step } v)
      secret
  T p pk (wotsPkAdrs adrs) endpoints.flatten

/-- **Headline Theorem (Batched SHAKE WOTS+ Keygen = FIPS 205 Algorithm 6)**:
    For every batch width `width >= 1`, `shake::batch::keygen` computes `Spec.wotsPkGen`. -/
theorem wots_keygen_batch_eq (width : Nat) (hw : 0 < width)
    (p : Params) (sk pk : Bytes) (adrs : Adrs) :
    wotsKeygenBatch width hw p sk pk adrs = wotsPkGen p sk pk adrs := by
  unfold wotsKeygenBatch wotsPkGen
  dsimp only
  rw [ForsHoriz.batchChunks_eq, ← List.flatMap_def]
  apply congrArg (T p pk (wotsPkAdrs adrs))
  apply List.flatMap_congr
  intro i _
  unfold chain
  simp only [Nat.zero_add]

/-! ## Part 3: Dynamic Lane-Refill Engine (`sign` and `recover` = FIPS 205 Algorithms 7 & 8) -/

/-- Runtime state of the dynamic lane-refill scheduler shared by `shake::batch::sign`
    and `shake::batch::recover`. -/
structure RefillState where
  active : Nat
  next : Nat
  laneId : Nat → Nat
  laneStep : Nat → Nat
  laneEnd : Nat → Nat
  laneVal : Nat → Bytes
  out : Nat → Bytes

/-- Remaining chain hash steps across all currently active lanes. -/
def activeRem (st : RefillState) : Nat :=
  ((List.range st.active).map fun l => st.laneEnd l - st.laneStep l).sum

/-- Remaining chain hash steps across all queued chains `order[next..]`. -/
def queuedRem (startStep endStep : Nat → Nat) (order : List Nat) (next : Nat) : Nat :=
  ((order.drop next).map fun id => endStep id - startStep id).sum

/-- Total remaining work (strict termination measure for the outer `while active > 0` loop). -/
def totalRem (startStep endStep : Nat → Nat) (order : List Nat) (st : RefillState) : Nat :=
  activeRem st + queuedRem startStep endStep order st.next

/-- Apply one parallel `permute_active` step across all active lanes `0..active`. -/
def permuteActiveStep (p : Params) (pk : Bytes) (adrs : Adrs) (st : RefillState) : RefillState :=
  { st with
    laneVal := fun l =>
      if l < st.active then
        F p pk { adrs with word2 := st.laneId l, word3 := st.laneStep l } (st.laneVal l)
      else st.laneVal l }

/-- Inner `while lane < active` compaction and refill loop (lines 323–354 / 424–456):
    increments `lane_step[lane]`; if finished, writes `out[id]` and either refills from
    `order[next]` (advancing `lane += 1`) or swap-removes with `active - 1` (keeping `lane`
    so the swapped lane is processed next). -/
def postLoop (initVal : Nat → Bytes) (startStep endStep : Nat → Nat) (order : List Nat)
    (lane : Nat) (st : RefillState) : RefillState :=
  if _h : lane < st.active then
    let step1 := st.laneStep lane + 1
    if step1 = st.laneEnd lane then
      let id := st.laneId lane
      let out' := fun k => if k = id then st.laneVal lane else st.out k
      if st.next < order.length then
        let nid := order[st.next]!
        let st' : RefillState := {
          active := st.active
          next := st.next + 1
          laneId := fun l => if l = lane then nid else st.laneId l
          laneStep := fun l => if l = lane then startStep nid else st.laneStep l
          laneEnd := fun l => if l = lane then endStep nid else st.laneEnd l
          laneVal := fun l => if l = lane then initVal nid else st.laneVal l
          out := out'
        }
        postLoop initVal startStep endStep order (lane + 1) st'
      else
        let act' := st.active - 1
        let st' : RefillState :=
          if lane < act' then
            {
              active := act'
              next := st.next
              laneId := fun l => if l = lane then st.laneId act' else st.laneId l
              laneStep := fun l => if l = lane then st.laneStep act' else st.laneStep l
              laneEnd := fun l => if l = lane then st.laneEnd act' else st.laneEnd l
              laneVal := fun l => if l = lane then st.laneVal act' else st.laneVal l
              out := out'
            }
          else
            { st with active := act', out := out' }
        postLoop initVal startStep endStep order lane st'
    else
      let st' : RefillState := {
        st with laneStep := fun l => if l = lane then step1 else st.laneStep l
      }
      postLoop initVal startStep endStep order (lane + 1) st'
  else st
termination_by st.active - lane
decreasing_by
  · omega
  · split_ifs <;> dsimp only <;> omega
  · omega

/-- Outer `while active > 0` loop bounded by fuel (proved below to terminate within
    `totalRem` steps with `active = 0`). -/
def refillLoop (p : Params) (pk : Bytes) (adrs : Adrs)
    (initVal : Nat → Bytes) (startStep endStep : Nat → Nat) (order : List Nat) :
    Nat → RefillState → RefillState
  | 0, st => st
  | fuel + 1, st =>
    if st.active = 0 then st
    else
      let stepped := permuteActiveStep p pk adrs st
      let st' := postLoop initVal startStep endStep order 0 stepped
      refillLoop p pk adrs initVal startStep endStep order fuel st'

/-- Initial state before entering `while active > 0`. -/
def initRefill (width : Nat) (initVal : Nat → Bytes) (startStep endStep : Nat → Nat)
    (order : List Nat) : RefillState :=
  let act := min order.length width
  {
    active := act
    next := act
    laneId := fun l => order[l]!
    laneStep := fun l => startStep order[l]!
    laneEnd := fun l => endStep order[l]!
    laneVal := fun l => initVal order[l]!
    out := initVal
  }

/-- Complete execution of the dynamic lane-refill engine. -/
def runRefill (width : Nat) (p : Params) (pk : Bytes) (adrs : Adrs)
    (initVal : Nat → Bytes) (startStep endStep : Nat → Nat) (order : List Nat) : RefillState :=
  let st0 := initRefill width initVal startStep endStep order
  refillLoop p pk adrs initVal startStep endStep order (totalRem startStep endStep order st0) st0

/-- Exact lane-wise invariant at the top of each `while active > 0` iteration. -/
private def OuterInv (p : Params) (pk : Bytes) (adrs : Adrs)
    (len : Nat) (initVal : Nat → Bytes) (startStep endStep : Nat → Nat)
    (order : List Nat) (st : RefillState) : Prop :=
  st.next ≤ order.length ∧
  (st.active = 0 → st.next = order.length) ∧
  (∀ l < st.active,
    st.laneId l ∈ order.take st.next ∧
    startStep (st.laneId l) ≤ st.laneStep l ∧
    st.laneStep l < st.laneEnd l ∧
    st.laneEnd l = endStep (st.laneId l) ∧
    st.laneVal l = chain p (initVal (st.laneId l)) (startStep (st.laneId l))
      (st.laneStep l - startStep (st.laneId l)) pk { adrs with word2 := st.laneId l }) ∧
  (∀ l₁ l₂, l₁ < st.active → l₂ < st.active → st.laneId l₁ = st.laneId l₂ → l₁ = l₂) ∧
  (∀ id ∈ order.take st.next,
    (∀ l < st.active, st.laneId l ≠ id) →
    st.out id = chain p (initVal id) (startStep id) (endStep id - startStep id)
      pk { adrs with word2 := id }) ∧
  (∀ id < len, startStep id = endStep id → st.out id = initVal id)

/-- Inner invariant inside `postLoop` at index `lane ≤ st.active`:
    lanes `< lane` are already stepped/refilled (holding their exact chain value at `laneStep`),
    while lanes `lane ..< st.active` hold their post-`permuteActiveStep` value (i.e. at `laneStep + 1`!). -/
private def InnerInv (p : Params) (pk : Bytes) (adrs : Adrs)
    (len : Nat) (initVal : Nat → Bytes) (startStep endStep : Nat → Nat)
    (order : List Nat) (lane : Nat) (st : RefillState) : Prop :=
  lane ≤ st.active ∧
  st.next ≤ order.length ∧
  (st.active = 0 → st.next = order.length) ∧
  (∀ l < st.active,
    st.laneId l ∈ order.take st.next ∧
    startStep (st.laneId l) ≤ st.laneStep l ∧
    st.laneStep l < st.laneEnd l ∧
    st.laneEnd l = endStep (st.laneId l) ∧
    if l < lane then
      st.laneVal l = chain p (initVal (st.laneId l)) (startStep (st.laneId l))
        (st.laneStep l - startStep (st.laneId l)) pk { adrs with word2 := st.laneId l }
    else
      st.laneVal l = chain p (initVal (st.laneId l)) (startStep (st.laneId l))
        (st.laneStep l + 1 - startStep (st.laneId l)) pk { adrs with word2 := st.laneId l }) ∧
  (∀ l₁ l₂, l₁ < st.active → l₂ < st.active → st.laneId l₁ = st.laneId l₂ → l₁ = l₂) ∧
  (∀ id ∈ order.take st.next,
    (∀ l < st.active, st.laneId l ≠ id) →
    st.out id = chain p (initVal id) (startStep id) (endStep id - startStep id)
      pk { adrs with word2 := id }) ∧
  (∀ id < len, startStep id = endStep id → st.out id = initVal id)

private theorem sum_range_map_congr {n : Nat} {f g : Nat → Nat} (h : ∀ i < n, f i = g i) :
    ((List.range n).map f).sum = ((List.range n).map g).sum := by
  congr 1
  apply List.map_congr_left
  intro i hi
  exact h i (List.mem_range.mp hi)

private theorem sum_range_split (n k : Nat) (hk : k ≤ n) (f : Nat → Nat) :
    ((List.range n).map f).sum =
      ((List.range k).map f).sum + ((List.range (n - k)).map fun j => f (k + j)).sum := by
  have h1 : n = k + (n - k) := by omega
  conv_lhs => rw [h1, List.range_add, List.map_append, List.sum_append, List.map_map]
  rfl

private theorem sum_range_update (n idx : Nat) (hidx : idx < n) (f : Nat → Nat) (v : Nat) :
    ((List.range n).map (fun l => if l = idx then v else f l)).sum + f idx =
      ((List.range n).map f).sum + v := by
  induction n with
  | zero => omega
  | succ m ih =>
    simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil, List.sum_append,
      List.sum_cons, List.sum_nil, Nat.add_zero]
    by_cases heq : m = idx
    · subst heq
      have hcongr : ((List.range m).map (fun l => if l = m then v else f l)).sum =
          ((List.range m).map f).sum :=
        sum_range_map_congr (fun i hi => ite_eq_right (by omega))
      rw [ite_eq_left rfl, hcongr]; omega
    · rw [ite_eq_right heq]
      have := ih (by omega)
      omega

private theorem sum_range_swap_remove (m idx : Nat) (hidx : idx < m) (f : Nat → Nat) :
    ((List.range m).map (fun l => if l = idx then f m else f l)).sum + f idx =
      ((List.range (m + 1)).map f).sum := by
  rw [List.range_succ, List.map_append, List.map_cons, List.map_nil, List.sum_append,
    List.sum_cons, List.sum_nil, Nat.add_zero]
  exact sum_range_update m idx hidx f (f m)

/-- Remaining work accounting for `postLoop`: each unprocessed lane `l ∈ [lane, active)`
    will drop its remaining count by 1 (either incrementing `laneStep` by 1 or finishing and
    transferring a queued chain from `queuedRem` into `activeRem` or shrinking `active`). -/
private theorem postLoop_spec (p : Params) (pk : Bytes) (adrs : Adrs)
    (len : Nat) (initVal : Nat → Bytes) (startStep endStep : Nat → Nat) (order : List Nat)
    (hnodup : order.Nodup)
    (hord_valid : ∀ id ∈ order, id < len ∧ startStep id < endStep id)
    (lane : Nat) (st : RefillState)
    (hinv : InnerInv p pk adrs len initVal startStep endStep order lane st) :
    OuterInv p pk adrs len initVal startStep endStep order
      (postLoop initVal startStep endStep order lane st) ∧
    totalRem startStep endStep order (postLoop initVal startStep endStep order lane st) +
      (st.active - lane) =
      totalRem startStep endStep order st := by
  rcases hinv with ⟨hlane_le, hnext_le, hact0, hlanes, hinj, hdone, hzero⟩
  unfold postLoop
  by_cases hlt : lane < st.active
  · simp only [hlt, ↓reduceDIte]
    have hcur := hlanes lane hlt
    rcases hcur with ⟨hmem_cur, hst_le, hst_lt, hend_eq, hval_cur⟩
    simp only [Nat.lt_irrefl, ↓reduceIte] at hval_cur
    by_cases hfin : st.laneStep lane + 1 = st.laneEnd lane
    · simp only [hfin, ↓reduceIte]
      have hcur_done : st.laneVal lane =
          chain p (initVal (st.laneId lane)) (startStep (st.laneId lane))
            (endStep (st.laneId lane) - startStep (st.laneId lane)) pk
            { adrs with word2 := st.laneId lane } := by
        rw [hval_cur, hfin, hend_eq]
      have hcur_rem : st.laneEnd lane - st.laneStep lane = 1 := by omega
      by_cases hmore : st.next < order.length
      · -- Case 1: chain finishes and we refill lane from `order[st.next]`!
        simp only [hmore, ↓reduceIte]
        set nid := order[st.next]!
        have hnid_def : nid = order[st.next]'hmore := getElem!_pos order st.next hmore
        have hnid_mem : nid ∈ order := by
          rw [hnid_def]
          exact List.getElem_mem hmore
        have hnid_valid := hord_valid nid hnid_mem
        have hnid_not_take : nid ∉ order.take st.next := by
          intro hmem
          obtain ⟨j, hj, hjeq⟩ := List.mem_iff_getElem.mp hmem
          have hj_lt : j < st.next := by rw [List.length_take] at hj; omega
          simp only [List.getElem_take] at hjeq
          have hnid_eq : order[st.next]'hmore = order[j]'(by omega) :=
            hnid_def.symm.trans hjeq.symm
          have hidx_eq := (List.nodup_iff_injective_getElem.mp hnodup)
            (a₁ := ⟨st.next, hmore⟩) (a₂ := ⟨j, by omega⟩) hnid_eq
          simp at hidx_eq; omega
        have htake_succ : order.take (st.next + 1) = order.take st.next ++ [nid] := by
          rw [List.take_succ_eq_append_getElem hmore, hnid_def]
        set st1 : RefillState := {
          active := st.active
          next := st.next + 1
          laneId := fun l => if l = lane then nid else st.laneId l
          laneStep := fun l => if l = lane then startStep nid else st.laneStep l
          laneEnd := fun l => if l = lane then endStep nid else st.laneEnd l
          laneVal := fun l => if l = lane then initVal nid else st.laneVal l
          out := fun k => if k = st.laneId lane then st.laneVal lane else st.out k
        }
        have hinv1 : InnerInv p pk adrs len initVal startStep endStep order (lane + 1) st1 := by
          refine ⟨by dsimp only [st1]; omega, by dsimp only [st1]; omega, fun h0 => by dsimp only [st1] at h0; omega, ?_, ?_, ?_, ?_⟩
          · intro l hl
            by_cases hll : l = lane
            · subst hll
              refine ⟨by simp [st1, htake_succ], by simp [st1], by simp [st1, hnid_valid.2],
                by simp [st1], ?_⟩
              simp [st1, chain]
            · have hl_old := hlanes l hl
              refine ⟨by simp only [st1, hll, ↓reduceIte, htake_succ, List.mem_append]; exact Or.inl hl_old.1,
                by simp [st1, hll, hl_old.2.1], by simp [st1, hll, hl_old.2.2.1],
                by simp [st1, hll, hl_old.2.2.2.1], ?_⟩
              have hlt_iff : (l < lane + 1) ↔ (l < lane) := by omega
              simp only [st1, hll, ↓reduceIte, hlt_iff]
              exact hl_old.2.2.2.2
          · intro l₁ l₂ h1 h2 heq
            simp only [st1] at heq
            by_cases h1l : l₁ = lane <;> by_cases h2l : l₂ = lane
            · omega
            · subst h1l; simp only [↓reduceIte, h2l] at heq
              exact False.elim (hnid_not_take (heq ▸ (hlanes l₂ h2).1))
            · subst h2l; simp only [↓reduceIte, h1l] at heq
              exact False.elim (hnid_not_take (heq.symm ▸ (hlanes l₁ h1).1))
            · simp only [h1l, h2l, ↓reduceIte] at heq
              exact hinj l₁ l₂ h1 h2 heq
          · intro id hid hnotact
            dsimp only [st1] at hid
            rw [htake_succ, List.mem_append, List.mem_singleton] at hid
            rcases hid with hid_old | rfl
            · by_cases hid_cur : id = st.laneId lane
              · subst hid_cur
                simp only [st1, ↓reduceIte]
                exact hcur_done
              · simp only [st1, hid_cur, ↓reduceIte]
                apply hdone id hid_old
                intro l hl
                by_cases hll : l = lane
                · subst hll; exact Ne.symm hid_cur
                · have hne := hnotact l hl
                  simpa [st1, hll] using hne
            · have hne := hnotact lane hlt
              simp [st1] at hne
          · intro id hid hzeq
            have hne : id ≠ st.laneId lane := by
              intro heq; subst heq
              have := hord_valid (st.laneId lane) (List.mem_of_mem_take hmem_cur)
              omega
            simp only [st1, hne, ↓reduceIte]
            exact hzero id hid hzeq
        obtain ⟨hout, hrem⟩ := postLoop_spec p pk adrs len initVal startStep endStep order
          hnodup hord_valid (lane + 1) st1 hinv1
        refine ⟨hout, ?_⟩
        have hact_eq : activeRem st1 + 1 = activeRem st + (endStep nid - startStep nid) := by
          unfold activeRem
          have h1 := sum_range_update st.active lane hlt
            (fun l => st.laneEnd l - st.laneStep l) (endStep nid - startStep nid)
          have hcongr : ((List.range st.active).map fun l => st1.laneEnd l - st1.laneStep l).sum =
              ((List.range st.active).map fun l => if l = lane then endStep nid - startStep nid else st.laneEnd l - st.laneStep l).sum :=
            sum_range_map_congr (fun l _ => by by_cases h : l = lane <;> simp [st1, h])
          change ((List.range st.active).map fun l => st1.laneEnd l - st1.laneStep l).sum + 1 = _
          rw [hcongr]
          omega
        have hq_eq : queuedRem startStep endStep order st.next =
            (endStep nid - startStep nid) + queuedRem startStep endStep order (st.next + 1) := by
          unfold queuedRem
          rw [← List.cons_getElem_drop_succ (h := hmore), List.map_cons, List.sum_cons, hnid_def]
        have hrem' : totalRem startStep endStep order
            (postLoop initVal startStep endStep order (lane + 1) st1) + (st.active - (lane + 1)) =
            activeRem st1 + queuedRem startStep endStep order (st.next + 1) := hrem
        have : totalRem startStep endStep order st =
            activeRem st + queuedRem startStep endStep order st.next := rfl
        omega
      · -- Case 2: chain finishes and `st.next = order.length`: swap-remove compaction!
        simp only [hmore, ↓reduceIte]
        have hnext_eq : st.next = order.length := by omega
        set act' := st.active - 1
        set st1 : RefillState :=
          if lane < act' then
            {
              active := act'
              next := st.next
              laneId := fun l => if l = lane then st.laneId act' else st.laneId l
              laneStep := fun l => if l = lane then st.laneStep act' else st.laneStep l
              laneEnd := fun l => if l = lane then st.laneEnd act' else st.laneEnd l
              laneVal := fun l => if l = lane then st.laneVal act' else st.laneVal l
              out := fun k => if k = st.laneId lane then st.laneVal lane else st.out k
            }
          else
            { st with active := act', out := fun k => if k = st.laneId lane then st.laneVal lane else st.out k }
        have hst1_act : st1.active = act' := by by_cases h : lane < act' <;> simp [st1, h]
        have hst1_next : st1.next = st.next := by by_cases h : lane < act' <;> simp [st1, h]
        have hinv1 : InnerInv p pk adrs len initVal startStep endStep order lane st1 := by
          by_cases hswap : lane < act'
          · simp only [st1, hswap, ↓reduceIte]
            refine ⟨by dsimp only; omega, by dsimp only; exact hnext_le, fun _ => hnext_eq, ?_, ?_, ?_, ?_⟩
            · intro l hl
              dsimp only at hl ⊢
              by_cases hll : l = lane
              · subst hll
                have hlast := hlanes act' (by omega)
                simp only [↓reduceIte, show ¬ (act' < l) by omega, Nat.lt_irrefl] at hlast ⊢
                exact hlast
              · have hl_old := hlanes l (by omega)
                simp only [hll, ↓reduceIte]
                exact hl_old
            · intro l₁ l₂ h1 h2 heq
              dsimp only at h1 h2 heq
              by_cases h1l : l₁ = lane <;> by_cases h2l : l₂ = lane
              · omega
              · subst h1l; simp only [↓reduceIte, h2l] at heq
                have := hinj act' l₂ (by omega) (by omega) heq; omega
              · subst h2l; simp only [↓reduceIte, h1l] at heq
                have := hinj l₁ act' (by omega) (by omega) heq; omega
              · simp only [h1l, h2l, ↓reduceIte] at heq
                exact hinj l₁ l₂ (by omega) (by omega) heq
            · intro id hid hnotact
              dsimp only at hid hnotact ⊢
              by_cases hid_cur : id = st.laneId lane
              · subst hid_cur; simp only [↓reduceIte]; exact hcur_done
              · simp only [hid_cur, ↓reduceIte]
                apply hdone id hid
                intro l hl
                by_cases hll : l = lane
                · subst hll; exact Ne.symm hid_cur
                · by_cases hlast : l = act'
                  · subst hlast
                    have hne := hnotact lane hswap
                    simpa only [↓reduceIte] using hne
                  · have hne := hnotact l (by omega)
                    simpa only [hll, ↓reduceIte] using hne
            · intro id hid hzeq
              dsimp only
              have hne : id ≠ st.laneId lane := by
                intro heq; subst heq
                have := hord_valid (st.laneId lane) (List.mem_of_mem_take hmem_cur)
                omega
              simp only [hne, ↓reduceIte]
              exact hzero id hid hzeq
          · -- lane = act' (removing the last active lane)
            have hlane_last : lane = act' := by omega
            simp only [st1, hswap, ↓reduceIte]
            refine ⟨by dsimp only; omega, by dsimp only; exact hnext_le, fun _ => hnext_eq, ?_, ?_, ?_, ?_⟩
            · intro l hl
              dsimp only at hl ⊢
              exact hlanes l (by omega)
            · intro l₁ l₂ h1 h2 heq
              dsimp only at h1 h2 heq
              exact hinj l₁ l₂ (by omega) (by omega) heq
            · intro id hid hnotact
              dsimp only at hid hnotact ⊢
              by_cases hid_cur : id = st.laneId lane
              · subst hid_cur; simp only [↓reduceIte]; exact hcur_done
              · simp only [hid_cur, ↓reduceIte]
                apply hdone id hid
                intro l hl
                by_cases hll : l = lane
                · subst hll; exact Ne.symm hid_cur
                · exact hnotact l (by omega)
            · intro id hid hzeq
              dsimp only
              have hne : id ≠ st.laneId lane := by
                intro heq; subst heq
                have := hord_valid (st.laneId lane) (List.mem_of_mem_take hmem_cur)
                omega
              simp only [hne, ↓reduceIte]
              exact hzero id hid hzeq
        obtain ⟨hout, hrem⟩ := postLoop_spec p pk adrs len initVal startStep endStep order
          hnodup hord_valid lane st1 hinv1
        refine ⟨hout, ?_⟩
        have hact_eq : activeRem st1 + 1 = activeRem st := by
          unfold activeRem
          rw [hst1_act]
          by_cases hswap : lane < act'
          · have hcongr : ((List.range act').map fun l => st1.laneEnd l - st1.laneStep l).sum =
                ((List.range act').map fun l => if l = lane then st.laneEnd act' - st.laneStep act'
                  else st.laneEnd l - st.laneStep l).sum :=
              sum_range_map_congr (fun l _ => by by_cases h : l = lane <;> simp [st1, hswap, h])
            have hsr := sum_range_swap_remove act' lane hswap (fun l => st.laneEnd l - st.laneStep l)
            have hst_act : act' + 1 = st.active := by omega
            rw [hst_act] at hsr
            rw [hcongr]; omega
          · have hlane_last : lane = act' := by omega
            have hst_act : st.active = act' + 1 := by omega
            rw [hst_act, List.range_succ, List.map_append, List.map_cons, List.map_nil,
              List.sum_append, List.sum_cons, List.sum_nil, Nat.add_zero]
            have hcongr : ((List.range act').map fun l => st1.laneEnd l - st1.laneStep l).sum =
                ((List.range act').map fun l => st.laneEnd l - st.laneStep l).sum :=
              sum_range_map_congr (fun l _ => by simp [st1, hswap])
            rw [hcongr, ← hlane_last]; omega
        have hq_eq : queuedRem startStep endStep order st1.next =
            queuedRem startStep endStep order st.next := by
          rw [hst1_next]
        unfold totalRem at hrem ⊢
        rw [hst1_act] at hrem
        omega
    · -- Case 3: chain does not finish yet; advance `laneStep[lane] += 1` and `lane += 1`.
      simp only [hfin, ↓reduceIte]
      set st1 : RefillState := {
        st with laneStep := fun l => if l = lane then st.laneStep lane + 1 else st.laneStep l
      }
      have hinv1 : InnerInv p pk adrs len initVal startStep endStep order (lane + 1) st1 := by
        refine ⟨by dsimp only [st1]; omega, hnext_le, hact0, ?_, hinj, hdone, hzero⟩
        intro l hl
        by_cases hll : l = lane
        · subst hll
          refine ⟨hmem_cur, by simp [st1]; omega, by simp [st1]; omega, by simp [st1, hend_eq], ?_⟩
          simp only [st1, ↓reduceIte, Nat.lt_succ_self]
          exact hval_cur
        · have hl_old := hlanes l hl
          have hlt_iff : (l < lane + 1) ↔ (l < lane) := by omega
          refine ⟨hl_old.1, by simp [st1, hll, hl_old.2.1], by simp [st1, hll, hl_old.2.2.1],
            by simp [st1, hl_old.2.2.2.1], ?_⟩
          simp only [st1, hll, ↓reduceIte, hlt_iff]
          exact hl_old.2.2.2.2
      obtain ⟨hout, hrem⟩ := postLoop_spec p pk adrs len initVal startStep endStep order
        hnodup hord_valid (lane + 1) st1 hinv1
      refine ⟨hout, ?_⟩
      have hact_eq : activeRem st1 + 1 = activeRem st := by
        unfold activeRem
        have h1 := sum_range_update st.active lane hlt
          (fun l => st.laneEnd l - st.laneStep l) (st.laneEnd lane - (st.laneStep lane + 1))
        have hcongr : ((List.range st.active).map fun l => st1.laneEnd l - st1.laneStep l).sum =
            ((List.range st.active).map fun l =>
              if l = lane then st.laneEnd lane - (st.laneStep lane + 1)
              else st.laneEnd l - st.laneStep l).sum :=
          sum_range_map_congr (fun l _ => by by_cases h : l = lane <;> simp [st1, h])
        change ((List.range st.active).map fun l => st1.laneEnd l - st1.laneStep l).sum + 1 = _
        rw [hcongr]
        omega
      unfold totalRem at hrem ⊢
      have hst1_act : st1.active = st.active := rfl
      have hst1_next : st1.next = st.next := rfl
      rw [hst1_act, hst1_next] at hrem
      omega
  · -- Base case: `lane = st.active`, inner loop terminates!
    simp only [hlt, ↓reduceDIte]
    have hlane_eq : lane = st.active := by omega
    refine ⟨⟨hnext_le, hact0, ?_, hinj, hdone, hzero⟩, by omega⟩
    intro l hl
    have := hlanes l hl
    simpa [hlane_eq, hl] using this
termination_by st.active - lane
decreasing_by
  · omega
  · rw [hst1_act]; omega
  · omega

private theorem permute_to_inner (p : Params) (pk : Bytes) (adrs : Adrs)
    (len : Nat) (initVal : Nat → Bytes) (startStep endStep : Nat → Nat) (order : List Nat)
    (st : RefillState) (hout : OuterInv p pk adrs len initVal startStep endStep order st) :
    InnerInv p pk adrs len initVal startStep endStep order 0 (permuteActiveStep p pk adrs st) := by
  rcases hout with ⟨hnext_le, hact0, hlanes, hinj, hdone, hzero⟩
  refine ⟨Nat.zero_le _, hnext_le, hact0, ?_, hinj, hdone, hzero⟩
  intro l hl
  have hl' : l < st.active := hl
  obtain ⟨hmem, hle, hlt, hend, hval⟩ := hlanes l hl'
  refine ⟨hmem, hle, hlt, hend, ?_⟩
  simp only [permuteActiveStep, ↓reduceIte, Nat.not_lt_zero, hl']
  have hsub : st.laneStep l + 1 - startStep (st.laneId l) =
      (st.laneStep l - startStep (st.laneId l)) + 1 := by omega
  rw [hsub, chain_succ, ← hval]
  have hword : startStep (st.laneId l) + (st.laneStep l - startStep (st.laneId l)) = st.laneStep l := by
    omega
  rw [hword]

private theorem refillLoop_spec (p : Params) (pk : Bytes) (adrs : Adrs)
    (len : Nat) (initVal : Nat → Bytes) (startStep endStep : Nat → Nat) (order : List Nat)
    (hnodup : order.Nodup)
    (hord_valid : ∀ id ∈ order, id < len ∧ startStep id < endStep id) :
    ∀ fuel st,
      OuterInv p pk adrs len initVal startStep endStep order st →
      totalRem startStep endStep order st ≤ fuel →
      let fin := refillLoop p pk adrs initVal startStep endStep order fuel st
      OuterInv p pk adrs len initVal startStep endStep order fin ∧ fin.active = 0
  | 0, st, hinv, hfuel => by
    unfold refillLoop
    have hact0 : st.active = 0 := by
      by_contra hne
      have hpos : 0 < st.active := by omega
      have h0 := hinv.2.2.1 0 hpos
      have hrem_pos : 0 < activeRem st := by
        unfold activeRem
        rw [show st.active = (st.active - 1) + 1 by omega]
        have h1 : st.laneEnd 0 - st.laneStep 0 > 0 := by omega
        have hmem : st.laneEnd 0 - st.laneStep 0 ∈
            (List.range ((st.active - 1) + 1)).map (fun l => st.laneEnd l - st.laneStep l) :=
          List.mem_map.mpr ⟨0, List.mem_range.mpr (by omega), rfl⟩
        have hle := List.le_sum_of_mem hmem
        omega
      unfold totalRem at hfuel; omega
    exact ⟨hinv, hact0⟩
  | fuel + 1, st, hinv, hfuel => by
    unfold refillLoop
    by_cases hact0 : st.active = 0
    · simp only [hact0, ↓reduceIte]
      exact ⟨hinv, trivial⟩
    · simp only [hact0, ↓reduceIte]
      have hinner := permute_to_inner p pk adrs len initVal startStep endStep order st hinv
      obtain ⟨hinv', hrem'⟩ := postLoop_spec p pk adrs len initVal startStep endStep order
        hnodup hord_valid 0 (permuteActiveStep p pk adrs st) hinner
      have htot_perm : totalRem startStep endStep order (permuteActiveStep p pk adrs st) =
          totalRem startStep endStep order st := rfl
      have hact_perm : (permuteActiveStep p pk adrs st).active = st.active := rfl
      rw [htot_perm, hact_perm, Nat.sub_zero] at hrem'
      exact refillLoop_spec p pk adrs len initVal startStep endStep order hnodup hord_valid
        fuel _ hinv' (by omega)

/-- **Headline Theorem (Dynamic Lane-Refill Scheduler Soundness & Termination)**:
    For any batch width `width >= 1`, any `len`, any `startStep ≤ endStep`, and any
    duplicate-free ordering `order` of `{i < len | startStep i < endStep i}`, the
    dynamic lane-refill scheduler terminates with `active = 0` and writes the exact
    FIPS 205 chain endpoint to `out[id]` for every chain `0..len`. -/
theorem refill_engine_spec (width : Nat) (hw : 0 < width)
    (p : Params) (pk : Bytes) (adrs : Adrs)
    (len : Nat) (initVal : Nat → Bytes) (startStep endStep : Nat → Nat)
    (hle : ∀ i < len, startStep i ≤ endStep i)
    (order : List Nat) (hnodup : order.Nodup)
    (hord_iff : ∀ id, id ∈ order ↔ (id < len ∧ startStep id < endStep id)) :
    let fin := runRefill width p pk adrs initVal startStep endStep order
    fin.active = 0 ∧
    ∀ id < len,
      fin.out id = chain p (initVal id) (startStep id) (endStep id - startStep id)
        pk { adrs with word2 := id } := by
  have hord_valid : ∀ id ∈ order, id < len ∧ startStep id < endStep id :=
    fun id h => (hord_iff id).mp h
  have hinit : OuterInv p pk adrs len initVal startStep endStep order
      (initRefill width initVal startStep endStep order) := by
    unfold OuterInv initRefill
    dsimp only
    refine ⟨Nat.min_le_left _ _, ?_, ?_, ?_, ?_, fun _ _ _ => rfl⟩
    · intro h0
      have : min order.length width = 0 := h0
      omega
    · intro l hl
      have hl_ord : l < order.length := Nat.lt_of_lt_of_le hl (Nat.min_le_left _ _)
      have hmem_take : order[l]! ∈ order.take (min order.length width) := by
        rw [getElem!_pos order l hl_ord]
        have heq : order[l]'hl_ord = (order.take (min order.length width))[l]'(by rw [List.length_take]; omega) :=
          (List.getElem_take (xs := order) (i := l) (j := min order.length width)
            (h := by rw [List.length_take]; omega)).symm
        rw [heq]; exact List.getElem_mem _
      have hval := hord_valid order[l]! (List.mem_of_mem_take hmem_take)
      refine ⟨hmem_take, Nat.le_refl _, hval.2, rfl, ?_⟩
      simp [chain]
    · intro l₁ l₂ h1 h2 heq
      have h1' : l₁ < order.length := Nat.lt_of_lt_of_le h1 (Nat.min_le_left _ _)
      have h2' : l₂ < order.length := Nat.lt_of_lt_of_le h2 (Nat.min_le_left _ _)
      rw [getElem!_pos order l₁ h1', getElem!_pos order l₂ h2'] at heq
      have hidx := (List.nodup_iff_injective_getElem.mp hnodup)
        (a₁ := ⟨l₁, h1'⟩) (a₂ := ⟨l₂, h2'⟩) heq
      simpa using hidx
    · intro id hid hnotact
      obtain ⟨j, hj, hjeq⟩ := List.mem_iff_getElem.mp hid
      have hj_lt : j < min order.length width := by rw [List.length_take] at hj; omega
      have hne := hnotact j hj_lt
      simp only [List.getElem_take] at hjeq
      have hlt_ord : j < order.length := Nat.lt_of_lt_of_le hj_lt (Nat.min_le_left _ _)
      rw [getElem!_pos order j hlt_ord] at hne
      exact False.elim (hne hjeq)
  unfold runRefill
  set st0 := initRefill width initVal startStep endStep order
  set fin := refillLoop p pk adrs initVal startStep endStep order
    (totalRem startStep endStep order st0) st0
  obtain ⟨hfin_inv, hfin_act⟩ := refillLoop_spec p pk adrs len initVal startStep endStep order
    hnodup hord_valid (totalRem startStep endStep order st0) st0 hinit (Nat.le_refl _)
  refine ⟨hfin_act, ?_⟩
  intro id hid
  by_cases hlt : startStep id < endStep id
  · have hmem : id ∈ order := (hord_iff id).mpr ⟨hid, hlt⟩
    have hnext_eq : fin.next = order.length := hfin_inv.2.1 hfin_act
    have htake : order.take fin.next = order := by
      rw [hnext_eq, List.take_length]
    apply hfin_inv.2.2.2.2.1 id (by rw [htake]; exact hmem)
    intro l hl
    omega
  · have heq : startStep id = endStep id := Nat.le_antisymm (hle id hid) (Nat.le_of_not_lt hlt)
    have h0 := hfin_inv.2.2.2.2.2 id hid heq
    rw [h0, show endStep id - startStep id = 0 by omega]
    simp [chain]

/-- Model of dynamic lane-refill `shake::batch::sign` (Algorithm 7). -/
def wotsSignRefill (width : Nat) (p : Params) (msg sk pk : Bytes) (adrs : Adrs)
    (order : List Nat) : Bytes :=
  let digits := wotsDigits p msg
  let initVal (i : Nat) := PRF p pk sk { wotsSkAdrs adrs with word2 := i }
  let fin := runRefill width p pk adrs initVal (fun _ => 0) (fun i => digits[i]!) order
  (List.range p.len).flatMap fun i => fin.out i

/-- **Headline Theorem (Dynamic Lane-Refill WOTS+ Signing = FIPS 205 Algorithm 7)**:
    For any `width >= 1` and any duplicate-free ordering `order` of nonzero digits (in
    particular, the output of `sort_descending`), `shake::batch::sign` equals `Spec.wotsSign`. -/
theorem wots_sign_refill_eq (width : Nat) (hw : 0 < width)
    (p : Params) (msg sk pk : Bytes) (adrs : Adrs)
    (order : List Nat) (hnodup : order.Nodup)
    (hord_iff : ∀ id, id ∈ order ↔ (id < p.len ∧ 0 < (wotsDigits p msg)[id]!)) :
    wotsSignRefill width p msg sk pk adrs order = wotsSign p msg sk pk adrs := by
  unfold wotsSignRefill wotsSign
  dsimp only
  have ⟨_, hout⟩ := refill_engine_spec width hw p pk adrs p.len
    (fun i => PRF p pk sk { wotsSkAdrs adrs with word2 := i })
    (fun _ => 0) (fun i => (wotsDigits p msg)[i]!) (fun _ _ => Nat.zero_le _)
    order hnodup hord_iff
  apply List.flatMap_congr
  intro i hi
  simpa using hout i (List.mem_range.mp hi)

/-- Model of dynamic lane-refill `shake::batch::recover` (Algorithm 8). -/
def wotsRecoverRefill (width : Nat) (p : Params) (sig msg pk : Bytes) (adrs : Adrs)
    (order : List Nat) : Bytes :=
  let digits := wotsDigits p msg
  let initVal (i : Nat) := block p sig i
  let fin := runRefill width p pk adrs initVal (fun i => digits[i]!) (fun _ => p.w - 1) order
  T p pk (wotsPkAdrs adrs) ((List.range p.len).flatMap fun i => fin.out i)

/-- **Headline Theorem (Dynamic Lane-Refill WOTS+ Recovery = FIPS 205 Algorithm 8)**:
    For any `width >= 1`, valid digits `≤ p.w - 1`, and any duplicate-free ordering `order`
    of chains with `digits[i] < p.w - 1` (in particular, the output of `sort_descending`
    on `rem_steps`), `shake::batch::recover` equals `Spec.wotsPkFromSig`. -/
theorem wots_recover_refill_eq (width : Nat) (hw : 0 < width)
    (p : Params) (sig msg pk : Bytes) (adrs : Adrs)
    (hdigits : ∀ i < p.len, (wotsDigits p msg)[i]! ≤ p.w - 1)
    (order : List Nat) (hnodup : order.Nodup)
    (hord_iff : ∀ id, id ∈ order ↔ (id < p.len ∧ (wotsDigits p msg)[id]! < p.w - 1)) :
    wotsRecoverRefill width p sig msg pk adrs order = wotsPkFromSig p sig msg pk adrs := by
  unfold wotsRecoverRefill wotsPkFromSig
  dsimp only
  have ⟨_, hout⟩ := refill_engine_spec width hw p pk adrs p.len
    (fun i => block p sig i)
    (fun i => (wotsDigits p msg)[i]!) (fun _ => p.w - 1) hdigits
    order hnodup hord_iff
  congr 1
  apply List.flatMap_congr
  intro i hi
  exact hout i (List.mem_range.mp hi)

end Shakeopt.WotsRefill
