import Armwide.WotsRefill
import Armwide.Encoders
import Armwide.SignOrderProgram
import Mathlib.Data.Fintype.EquivFin

open Aeneas Aeneas.Std Result
namespace slhdsa.Armwide.SignOrder
open WotsRefill

private theorem count_bound (ws : List U32) (d : Nat) :
    countGt ws d + countEq ws ws.length d ≤ ws.length := by
  unfold countGt countEq
  rw [← filter_disjoint_add]
  · exact (List.length_filter_le _ _).trans_eq List.length_range
  · intro j _
    by_cases h : d < ws[j]!.val <;> simp [h] <;> omega

private theorem slot_lt (ws : List U32) (i : Nat) (hi : i < ws.length) : slotOf ws i < ws.length := by
  have h := countEq_strict_mono ws hi ws[i]!.val rfl
  have bound := count_bound ws ws[i]!.val
  unfold slotOf
  omega

private theorem sort_loop0_spec (weights : Slice U32) (hlen : weights.length ≤ 67)
    (hb : ∀ j < weights.length, (weights.val[j]!).val ≤ 15) :
    sha256.arm_wide.sign_order_loop0 ⟨weights, 0⟩ (Array.repeat 16#usize 0#u8) ⦃ counts =>
      ∀ b, b ≤ 15 → (counts.val[b]!).val = countEq weights.val weights.length b ⦄ := by
  unfold sha256.arm_wide.sign_order_loop0
  apply loop.spec_decr_nat
    (measure := fun (p : core.slice.iter.Iter U32 × Array U8 16#usize) => weights.length - p.1.i)
    (inv := fun p => p.1.slice = weights ∧ p.1.i ≤ weights.length ∧
      ∀ b, b ≤ 15 → (p.2.val[b]!).val = countEq weights.val p.1.i b)
  · rintro ⟨it, counts⟩ ⟨hslice, hi, hcnt⟩
    unfold sha256.arm_wide.sign_order_loop0.body
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
      let* ⟨ i, i_post ⟩ ← UScalar.cast.step_spec
      have hi_val : i.val = (weights.val[it.i]).val := by simp [i_post]
      let* ⟨ i1, i1_post ⟩ ← Array.index_usize_spec
      have hi1_val : i1.val = countEq weights.val it.i (weights.val[it.i]).val := by
        have := hcnt (weights.val[it.i]).val hw_le
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
      intro b hb2
      change (a.val[b]!).val = countEq weights.val (it.i + 1) b
      rw [countEq_succ, hw_get]
      by_cases hbw : b = (weights.val[it.i]).val
      · subst hbw
        rw [ite_eq_left rfl, ha_val, List.getElem!_eq_getElem?_getD,
          List.getElem?_set_self (by simp; omega)]
        simp [i2_post, hi1_val]
      · rw [ite_eq_right (Ne.symm hbw), ha_val, List.getElem!_eq_getElem?_getD,
          List.getElem?_set_ne (by omega)]
        simpa [List.getElem!_eq_getElem?_getD] using hcnt b hb2
    · have hdone : core.slice.iter.IteratorSliceIter.next it = ok (none, it) := by
        simp [core.slice.iter.IteratorSliceIter.next, hslice, more, Slice.length] at *
      rw [hdone]; simp only [step_simps]
      have hie : it.i = weights.length := by omega
      simpa [hie] using hcnt
  · refine ⟨rfl, Nat.zero_le _, fun b hb2 => ?_⟩
    simp only [Array.repeat_val, List.getElem!_eq_getElem?_getD, List.getElem?_replicate,
      show b < (16#usize).val by scalar_tac, ↓reduceIte, countEq_zero]
    rfl

private theorem offsets_spec (ws : List U32) (hlen : ws.length ≤ 67)
    (hb : ∀ j < ws.length, ws[j]!.val ≤ 15) (counts : Array U8 16#usize)
    (hist : ∀ d, d ≤ 15 → counts.val[d]!.val = countEq ws ws.length d) :
    sha256.arm_wide.sign_order_loop1 counts (Array.repeat 16#usize 0#usize) 0#usize 15#isize ⦃ offs =>
      ∀ d, d ≤ 15 → offs.val[d]!.val = countGt ws d ⦄ := by
  unfold sha256.arm_wide.sign_order_loop1
  apply loop.spec_decr_nat
    (measure := fun q : Array Usize 16#usize × Usize × Isize => (q.2.2.val+1).toNat)
    (inv := fun q => -1 ≤ q.2.2.val ∧ q.2.2.val ≤ 15 ∧
      (0 ≤ q.2.2.val → q.2.1.val = countGt ws q.2.2.val.toNat) ∧
      ∀ d : Nat, q.2.2.val < (d:Int) → d ≤ 15 → q.1.val[d]!.val = countGt ws d)
  · rintro ⟨offs,total,b⟩ ⟨lo,hi,tot,done⟩
    simp only at lo hi tot done ⊢
    unfold sha256.arm_wide.sign_order_loop1.body
    spec_split
    · have pos : 0 ≤ b.val := by scalar_tac
      have okCast : 0 ≤ b.val ∧ b.val ≤ UScalar.max .Usize := by scalar_tac
      step with IScalar.hcast_inBounds_spec .Usize b okCast as ⟨i,idx⟩
      have ir : i.val = b.val.toNat := by omega
      have ib : i.val < 16 := by omega
      let* ⟨ next, write ⟩ ← Array.update_spec
      step with IScalar.hcast_inBounds_spec .Usize b okCast as ⟨i1,idx1⟩
      have ir1 : i1.val = b.val.toNat := by omega
      have ib1 : i1.val < 16 := by omega
      let* ⟨ k, read ⟩ ← Array.index_usize_spec
      have kv : k.val = countEq ws ws.length b.val.toNat := by
        rw [read, ← getElem!_pos]; erw [ir1,hist _ (by omega)]
      let* ⟨ k', cast ⟩ ← UScalar.cast.step_spec
      have kval : k'.val = k.val := by simp [cast]
      have bound := count_bound ws b.val.toNat
      have ht := tot pos
      let* ⟨ total', add ⟩ ← Usize.add_spec
      let* ⟨ b', sublo, subhi ⟩ ← Isize.sub_spec
      refine ⟨by omega,by omega,?_,?_,by omega⟩
      · intro live
        rw [add, kval, ht, kv, show b'.val.toNat = b.val.toNat - 1 by omega,
          countGt_step ws b.val.toNat (by omega)]
      · intro d hd hd15
        rw [write,Array.set_val_eq]; erw [ir]
        by_cases eq : d=b.val.toNat
        · subst d
          rw [List.getElem!_eq_getElem?_getD,List.getElem?_set_self (by simp; omega)]
          exact ht
        · rw [List.getElem!_eq_getElem?_getD,List.getElem?_set_ne (by omega)]
          simpa [List.getElem!_eq_getElem?_getD] using done d (by omega) hd15
    · simp only [step_simps]
      intro d hd
      exact done d (by scalar_tac) hd
  · simp only [IScalar.ofInt_val_eq]
    exact ⟨by decide,by decide,fun _ => (countGt_15 ws hb).symm,fun d h d15 => by omega⟩

private theorem sort_loop2_spec (weights : Slice U32) (hlen : weights.length ≤ 67)
    (hb : ∀ j < weights.length, (weights.val[j]!).val ≤ 15)
    (order : Array U8 67#usize) (offsets : Array Usize 16#usize)
    (hoff : ∀ k, k ≤ 15 → (offsets.val[k]!).val = countGt weights.val k) :
    sha256.arm_wide.sign_order_loop2 ⟨⟨weights, 0⟩, 0#usize⟩ offsets order ⦃ order' =>
      ∀ c < weights.length,
        (order'.val[slotOf weights.val c]!).val = c ⦄ := by
  unfold sha256.arm_wide.sign_order_loop2
  apply loop.spec_decr_nat
    (measure := fun (p : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter U32) ×
        Array Usize 16#usize × Array U8 67#usize) => weights.length - p.1.iter.i)
    (inv := fun p => p.1.iter.slice = weights ∧ p.1.iter.i ≤ weights.length ∧
      p.1.count.val = p.1.iter.i ∧
      (∀ k, k ≤ 15 → (p.2.1.val[k]!).val = countGt weights.val k + countEq weights.val p.1.iter.i k) ∧
      (∀ c < p.1.iter.i,
        (p.2.2.val[slotOf weights.val c]!).val = c))
  · rintro ⟨it, offs, ord⟩ ⟨hslice, hi, hcnt, hoffs, hord⟩
    unfold sha256.arm_wide.sign_order_loop2.body
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
      let* ⟨ i1, i1_post ⟩ ← UScalar.cast.step_spec
      have hi1_val : i1.val = (weights.val[it.iter.i]).val := by simp [i1_post]
      let* ⟨ pos, pos_post ⟩ ← Array.index_usize_spec
      have hpos_val : pos.val = slotOf weights.val it.iter.i := by
        have ho := hoffs (weights.val[it.iter.i]).val hw_le
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
        have h1 := slot_lt weights.val it.iter.i more
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
      · intro k hk2
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
          simpa [List.getElem!_eq_getElem?_getD] using hoffs k hk2
      · intro c hc
        have hc' : c < it.iter.i + 1 := hc
        rcases Nat.lt_succ_iff_lt_or_eq.mp hc' with hlt | rfl
        · have hne : pos.val ≠ slotOf weights.val c := by
            rw [hpos_val]
            intro heq
            have := slotOf_inj weights.val more (by omega) heq
            omega
          rw [ha_val, List.getElem!_eq_getElem?_getD, List.getElem?_set_ne hne]
          simpa [List.getElem!_eq_getElem?_getD] using hord c hlt
        · rw [← hpos_val, ha_val, List.getElem!_eq_getElem?_getD,
            List.getElem?_set_self (by simp; omega)]
          simpa using hi2_val
    · have hinner : core.slice.iter.IteratorSliceIter.next it.iter = ok (none, it.iter) := by
        simp [core.slice.iter.IteratorSliceIter.next, hslice, more, Slice.length] at *
      have henum : core.iter.adapters.enumerate.IteratorEnumerate.next
          (core.iter.traits.iterator.IteratorSliceIter U32) it = ok (none, it) := by
        simp [core.iter.adapters.enumerate.IteratorEnumerate.next,
          core.iter.traits.iterator.IteratorSliceIter, hinner]
      rw [henum]; simp only [step_simps]
      have hie : it.iter.i = weights.length := by omega
      simpa [hie] using hord
  · refine ⟨rfl, Nat.zero_le _, rfl, fun k hk2 => ?_, fun _ hc => by change _ < 0 at hc; omega⟩
    simp only [countEq_zero, Nat.add_zero]
    exact hoff k hk2

/-- The live signing prefix includes every chain once, including zero digits. -/
theorem sort_spec (ds : Slice U32) (len : ds.length ≤ 67)
    (small : ∀ i < ds.length, ds.val[i]!.val ≤ 15) :
    sha256.arm_wide.sign_order ds ⦃ o =>
      let order := (o.val.take ds.length).map (·.val)
      order.Nodup ∧ ∀ i, i ∈ order ↔ i < ds.length ⦄ := by
  unfold sha256.arm_wide.sign_order
  simp only [SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter,
    core.slice.Slice.iter, core.iter.traits.iterator.Iterator.enumerate.trait_default,
    core.iter.traits.iterator.Iterator.enumerate.default, bind_ok]
  step with sort_loop0_spec ds len small as ⟨cs, hist⟩
  step with offsets_spec ds.val len small cs hist as ⟨offsets, off⟩
  let* ⟨o, placed⟩ ← sort_loop2_spec ds len small (Array.repeat 67#usize 0#u8) offsets off
  let ord := (o.val.take ds.length).map (·.val)
  have size : ord.length = ds.length := by simp [ord,len]
  let f : Fin ds.length → Fin ds.length := fun c => ⟨slotOf ds.val c.val, slot_lt ds.val c c.isLt⟩
  have inj : Function.Injective f := fun i j h => Fin.ext (slotOf_inj ds.val i.isLt j.isLt (congrArg Fin.val h))
  have covers := Finite.injective_iff_surjective.mp inj
  have atSlot (c : Fin ds.length) : ord[(f c).val]! = c.val := by
    have h := placed c c.isLt
    have h1 := (f c).isLt
    have hi : (f c).val < ord.length := by omega
    rw [getElem!_pos ord _ hi]
    simp only [ord,List.getElem_map,List.getElem_take]
    have ol : o.val.length = 67 := by simp
    have bound : slotOf ds.val c < o.val.length := by rw [ol]; exact (slot_lt _ _ c.isLt).trans_le len
    rw [getElem!_pos o.val _ bound] at h
    exact h
  change ord.Nodup ∧ ∀ i, i ∈ ord ↔ i < ds.length
  constructor
  · rw [List.nodup_iff_injective_getElem]
    intro ⟨i,hi⟩ ⟨j,hj⟩ h
    obtain ⟨c,ec⟩ := covers ⟨i, by omega⟩
    obtain ⟨d,ed⟩ := covers ⟨j, by omega⟩
    have ci := atSlot c
    have dj := atSlot d
    simp only [ec,ed,getElem!_pos ord i hi,getElem!_pos ord j hj] at ci dj
    have eq : c = d := Fin.ext (ci.symm.trans (h.trans dj))
    have same := congrArg Fin.val ((ec.symm.trans (congrArg f eq)).trans ed)
    exact Fin.ext same
  · intro i
    constructor
    · intro h
      obtain ⟨j,hj,ej⟩ := List.mem_iff_getElem.mp h
      obtain ⟨c,ec⟩ := covers ⟨j,by omega⟩
      have ci := atSlot c
      rw [ec,getElem!_pos ord _ hj,ej] at ci
      exact ci ▸ c.isLt
    · intro hi
      let c : Fin ds.length := ⟨i,hi⟩
      have h := atSlot c
      have b : (f c).val < ord.length := by rw [size]; exact (f c).isLt
      rw [getElem!_pos ord _ b] at h
      exact List.mem_iff_getElem.mpr ⟨_,b,h⟩

private def prefixDigits (r : Array U32 67#usize) (k : Nat) : Slice U32 :=
  Slice.from (r.val.take k) (by
    rw [List.length_take]
    apply (Nat.min_le_right ..).trans
    have h : r.val.length = 67 := by simp
    rw [h]
    scalar_tac)

/-- The extracted message encoder and inline signing sort drive the four-lane refill model.
The concatenation is in signature order, independently of the bucket execution order. -/
theorem sign_bytes {N : Usize} (p : Spec.Params) (valid : p.Valid) (n : p.n = N.val)
    (m : Array U8 N) (pk sk : Spec.Bytes) (a : Spec.Adrs) :
    (do let digits ← slhdsa.wots.arm.wots_digits_stack m
        let ds := prefixDigits digits p.len
        let sorted ← sha256.arm_wide.sign_order ds
        let order := (sorted.val.take p.len).map (·.val)
        ok ((List.range p.len).flatMap
          (signFusedFull p pk sk a (fun i => ds.val[i]!.val) order)))
    ⦃ out => out = Spec.wotsSign p (bytes m.val) sk pk a ⦄ := by
  have casesN : N.val = 16 ∨ N.val = 24 ∨ N.val = 32 := by have := valid.n_cases; omega
  have len : p.len = 2*N.val+3 := by
    simp only [Spec.Params.len, Spec.Params.len2, Spec.Params.len1, Spec.Params.w, valid.lgw_eq, n]
    rcases casesN with h|h|h <;> rw [h] <;> decide
  have cap : p.len ≤ 67 := by omega
  step with wots_digits_stack_spec p valid n m as ⟨digits, values, bounded⟩
  let ds := prefixDigits digits p.len
  have elems : ds.val = digits.val.take p.len := Slice.from_val ..
  have size : ds.length = p.len := by change ds.val.length = _; simp [elems,cap]
  have small : ∀ i < ds.length, ds.val[i]!.val ≤ 15 := by
    intro i hi
    rw [elems,getElem!_pos _ _ (by simpa [elems] using hi),List.getElem_take]
    have h := bounded i (by omega)
    rw [getElem!_pos digits.val _ (by simp; omega)] at h
    omega
  step with sort_spec ds (by omega) small as ⟨sorted,nd,covers⟩
  change ((sorted.val.take ds.length).map (·.val)).Nodup at nd
  change ∀ i, i ∈ ((sorted.val.take ds.length).map (·.val)) ↔ i < ds.length at covers
  rw [size] at nd covers
  simp only [WP.spec_ok, Spec.wotsSign]
  apply List.flatMap_congr
  intro i hi
  have hi := List.mem_range.mp hi
  have target := sign_fused_scheduler_eq_fips p pk sk a (fun i => ds.val[i]!.val)
    p.len _ (by rwa [← size]) nd covers i hi
  rw [target]
  have veq : nats ds.val = Spec.wotsDigits p (bytes m.val) := by simpa only [elems,len] using values
  have hx := congrArg (fun l : List Nat => l[i]!) veq
  have bound : i < ds.val.length := by change i < ds.length; omega
  change (ds.val.map (·.val))[i]! = _ at hx
  rw [getElem!_pos _ _ (by simpa using bound),List.getElem_map] at hx
  rw [getElem!_pos ds.val _ (by change i < ds.length; omega)]
  rw [hx]

end slhdsa.Armwide.SignOrder
