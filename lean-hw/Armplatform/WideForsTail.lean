import Armplatform.WideFors
open Aeneas Aeneas.Std Result
namespace slhdsa.WideFors
set_option maxHeartbeats 1800000

/-- Every row after the paired prefix takes the FIPS authentication-path step. -/
theorem scalar_tail {N : Usize} (p : params.Params) (hp : PN p N)
    (sig : Slice U8) (pk : Array U8 N) (st : Array U32 8#usize) (st5 : Array U64 8#usize)
    (hs : SeedOk ({ pk_seed := pk, state := st, state512 := st5 } : hash.Seed N))
    (adrs : address.Adrs) (k : Usize) (hk : k.val = p.k.val)
    (vals0 : Array (Array U8 N) 35#usize) (idx0 : Array U32 35#usize)
    (h : Usize) (hh : h.val < p.a.val) (hsig : sig.length = p.k.val * (1 + p.a.val) * N.val)
    (idx : Array U32 35#usize) (vals : Array (Array U8 N) 35#usize) (i : Usize) (hi : i.val ≤ k.val)
    (hdone : ∀ t, t < i.val →
      bytes (vals.val[t]!).val = Spec.H (paramsS p) (bytes pk.val)
        { adrsS adrs with word3 := (idx0.val[t]!).val / 2 }
        (pairMsg (bytes (vals0.val[t]!).val)
          (Spec.block (paramsS p) (bytes sig.val) (t * (p.a.val + 1) + 1 + h.val)) (idx0.val[t]!).val) ∧
      (idx.val[t]!).val = (idx0.val[t]!).val / 2)
    (hrest : ∀ t, i.val ≤ t → vals.val[t]! = vals0.val[t]! ∧ idx.val[t]! = idx0.val[t]!) :
    fors.arm.pk_from_sig_loop3_loop0 ⟨i,k⟩ sig pk st st5 p.a idx vals h adrs ⦃ r =>
      ∀ t, t < k.val →
        bytes (r.2.val[t]!).val = Spec.H (paramsS p) (bytes pk.val)
          { adrsS adrs with word3 := (idx0.val[t]!).val / 2 }
          (pairMsg (bytes (vals0.val[t]!).val)
            (Spec.block (paramsS p) (bytes sig.val) (t * (p.a.val + 1) + 1 + h.val)) (idx0.val[t]!).val) ∧
        (r.1.val[t]!).val = (idx0.val[t]!).val / 2 ⦄ := by
  have hv := hp.valid
  have ha14 : p.a.val ≤ 14 := hv.a_le
  have hk35 : p.k.val ≤ 35 := hv.k_le
  unfold fors.arm.pk_from_sig_loop3_loop0
  apply loop.spec_decr_nat
    (measure := fun (q : core.ops.range.Range Usize × Array U32 35#usize × Array (Array U8 N) 35#usize) => k.val - q.1.start.val)
    (inv := fun q => q.1.end = k ∧ q.1.start.val ≤ k.val ∧ (∀ t, t < q.1.start.val →
      bytes (q.2.2.val[t]!).val = Spec.H (paramsS p) (bytes pk.val)
        { adrsS adrs with word3 := (idx0.val[t]!).val / 2 }
        (pairMsg (bytes (vals0.val[t]!).val)
          (Spec.block (paramsS p) (bytes sig.val) (t * (p.a.val + 1) + 1 + h.val)) (idx0.val[t]!).val) ∧
      (q.2.1.val[t]!).val = (idx0.val[t]!).val / 2) ∧
      (∀ t, q.1.start.val ≤ t → q.2.2.val[t]! = vals0.val[t]! ∧ q.2.1.val[t]! = idx0.val[t]!))
  · rintro ⟨it, idx, vals⟩ ⟨he, h1, h2, h3⟩
    simp only [fors.arm.pk_from_sig_loop3_loop0.body]
    simp only at he h1 h2 h3
    by_cases live : it.start.val < it.end.val
    · have hil : it.start.val < k.val := he ▸ live
      step with core.iter.range.IteratorRange.next_Usize_some_spec it live as ⟨o,nxt,ho,hn,hen⟩
      simp only [ho]
      have hsb := fors_sib_bound p.a.val p.k.val N.val it.start.val h.val sig.length (by omega) hh hsig
      step as ⟨i1, i1_post⟩
      step as ⟨i2, i2_post⟩
      have hi2 : i2.val = p.a.val + 1 := by rw [i2_post, i1_post]; simp
      have hmul : it.start.val * i2.val ≤ 35 * 15 := by rw [hi2]; exact Nat.mul_le_mul (by omega) (by omega)
      step as ⟨i3, i3_post⟩
      step as ⟨i4, i4_post⟩
      step as ⟨i5, i5_post⟩
      have hi5 : i5.val = it.start.val * (p.a.val + 1) + 1 + h.val := by
        rw [i5_post, i4_post, i3_post, hi2]
      step as ⟨sibling, sibling_post⟩
      step*
      have hil' : it.start.val < idx.val.length := by simp; omega
      have hi8 : i6 = idx0.val[it.start.val]! := by
        rw [i6_post, ← getElem!_eq _ _ hil', (h3 _ (le_refl _)).2]
      have hpar : parent.val = (idx0.val[it.start.val]!).val / 2 := by
        rw [parent_post, ← hi8]; simp [Nat.shiftRight_eq_div_pow]
      have hi7 : i7.val = (idx0.val[it.start.val]!).val % 2 := by
        rw [i7_post, ← hi8]; simp [Nat.and_one_is_mod]
      have hadrs : adrsS a_node = { adrsS adrs with word3 := parent.val } := by
        simp [adrsS, a_node_post]
      have hsib : bytes sibling.val = Spec.block (paramsS p) (bytes sig.val) (it.start.val * (p.a.val + 1) + 1 + h.val) := by
        rw [bytes_block (paramsS p) sig.val sibling.val i5.val (by rw [sibling_post, hp.n]), hi5]
      have hvl : it.start.val < vals.val.length := by simp; omega
      have hv0 : vals.val[it.start.val]! = vals0.val[it.start.val]! := (h3 _ (le_refl _)).1
      by_cases hc : i7 = 0#u32
      · simp only [hc, ↓reduceIte]
        have hev : (idx0.val[it.start.val]!).val % 2 = 0 := by rw [← hi7, hc]; rfl
        let* ⟨ v, v_post ⟩ ← Array.index_usize_spec
        let* ⟨ w, w_post ⟩ ← thash_pair_spec (paramsS p) hp.n hp.nok _ hs
        let* ⟨ vals1, vals1_post ⟩ ← Array.update_spec
        step*
        refine ⟨hen.trans he,by scalar_tac, ?_, ?_, by scalar_tac⟩
        · intro t ht
          rw [hn] at ht
          rw [vals1_post, a4_post, Array.set_val_eq, Array.set_val_eq]
          rcases Nat.lt_succ_iff_lt_or_eq.mp ht with ht | ht
          · rw [getElem!_set_ne' _ _ _ _ (by omega), getElem!_set_ne' _ _ _ _ (by omega)]
            exact h2 t ht
          · subst ht
            rw [getElem!_set_self' _ _ _ (by simp; omega), getElem!_set_self' _ _ _ (by simp; omega)]
            refine ⟨?_, hpar⟩
            rw [w_post, hadrs, hpar, v_post, ← getElem!_eq _ _ hvl, hv0, hsib, pairMsg_even _ _ _ hev]
        · intro t ht
          rw [vals1_post, a4_post, Array.set_val_eq, Array.set_val_eq,
            getElem!_set_ne' _ _ _ _ (by scalar_tac), getElem!_set_ne' _ _ _ _ (by scalar_tac)]
          exact h3 t (by scalar_tac)
      · simp only [hc, ↓reduceIte]
        have hod : ¬ (idx0.val[it.start.val]!).val % 2 = 0 := by
          rw [← hi7]; intro h0; apply hc; scalar_tac
        let* ⟨ v, v_post ⟩ ← Array.index_usize_spec
        let* ⟨ w, w_post ⟩ ← thash_pair_spec (paramsS p) hp.n hp.nok _ hs
        let* ⟨ vals1, vals1_post ⟩ ← Array.update_spec
        step*
        refine ⟨hen.trans he,by scalar_tac, ?_, ?_, by scalar_tac⟩
        · intro t ht
          rw [hn] at ht
          rw [vals1_post, a4_post, Array.set_val_eq, Array.set_val_eq]
          rcases Nat.lt_succ_iff_lt_or_eq.mp ht with ht | ht
          · rw [getElem!_set_ne' _ _ _ _ (by omega), getElem!_set_ne' _ _ _ _ (by omega)]
            exact h2 t ht
          · subst ht
            rw [getElem!_set_self' _ _ _ (by simp; omega), getElem!_set_self' _ _ _ (by simp; omega)]
            refine ⟨?_, hpar⟩
            rw [w_post, hadrs, hpar, v_post, ← getElem!_eq _ _ hvl, hv0, hsib, pairMsg_odd _ _ _ hod]
        · intro t ht
          rw [vals1_post, a4_post, Array.set_val_eq, Array.set_val_eq,
            getElem!_set_ne' _ _ _ _ (by scalar_tac), getElem!_set_ne' _ _ _ _ (by scalar_tac)]
          exact h3 t (by scalar_tac)
    · step with core.iter.range.IteratorRange.next_Usize_none_spec it (by omega) as ⟨o,nxt,ho,_⟩
      simp only [ho,step_simps]
      have : it.start.val = k.val := by rw [he] at live; omega
      rw [this] at h2; exact h2
  · exact ⟨rfl,hi, hdone, hrest⟩

end slhdsa.WideFors
