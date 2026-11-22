import Slhdsa.Proofs.Hw.ChainMain
open Aeneas Aeneas.Std Result

/-! The main loop of `chain_all`, and `chain_all`. -/

namespace slhdsa
open Spec.SHA256

set_option linter.unusedSimpArgs false

theorem main_loop_spec (hw : Arm.haveSha2 = true) (state : Array U32 8#usize) (blocks0 : Slice (Array U8 64#usize))
    (start «end» : Slice U32)
    (hs : blocks0.length ≤ start.length) (he : blocks0.length ≤ «end».length)
    (blocks : Slice (Array U8 64#usize)) (slots : Array sha256.hw.Slot 4#usize)
    (first : sha256.hw.First) (n next : Usize)
    (hI : MInv state blocks0 start «end» blocks slots first n.val next.val) :
    sha256.hw.chain_all_loop0 state blocks start «end» slots first n next ⦃ r =>
      r.length = blocks0.length ∧ ∀ i, i < blocks0.length → bytes (r.val[i]!).val =
        runBlock (wv state.val) (bytes (blocks0.val[i]!).val) (start.val[i]!).val («end».val[i]!).val ⦄ := by
  unfold sha256.hw.chain_all_loop0
  apply loop.spec_decr_nat
    (measure := fun (q : Slice (Array U8 64#usize) × Array sha256.hw.Slot 4#usize × sha256.hw.First ×
      Usize × Usize) => Mmeas blocks0.length q.2.2.2.2.val (q.2.1.val.take q.2.2.2.1.val))
    (inv := fun q => MInv state blocks0 start «end» q.1 q.2.1 q.2.2.1 q.2.2.2.1.val q.2.2.2.2.val)
  · rintro ⟨blocks, slots, first, n, next⟩ hI
    simp only [sha256.hw.chain_all_loop0.body]
    simp only at hI
    have hI' := hI
    obtain ⟨hn4, hnext, hlen, hf, hA, hpw, hmem, hfin⟩ := hI'
    split
    · split
      · have hnx : next.val < blocks0.length := by scalar_tac
        step*
        have hi1 : i1.val = (start.val[next.val]!).val := by
          rw [i1_post, getElem!_eq _ _ (by scalar_tac)]
        have hi2 : i2.val = («end».val[next.val]!).val := by
          rw [i2_post, getElem!_eq _ _ (by scalar_tac)]
        split
        · step as ⟨a, ha⟩
          have hab : a = blocks0.val[next.val]! := by
            rw [ha, ← getElem!_eq _ _ (by scalar_tac)]; exact hmem _ hnx (Or.inl (le_refl _))
          step with enter_spec hw state a i1 i2 next first hf as ⟨res, hr1, hr2, hr3, hr4, hr5, hr6⟩
          obtain ⟨sl, f'⟩ := res
          simp only at hr1 hr2 hr3 hr4 hr5 hr6 ⊢
          step*
          rw [hab] at hr2 hr3
          have key := enter_inv state blocks0 start «end» blocks slots first n.val next.val hI
            (by scalar_tac) hnx sl f' hr1 hr2 hr3 (by rw [hr4, hi1]) (by rw [hr5, hi2]) (by rw [hr6])
            (by rw [hr4, hr5]; scalar_tac) n rfl
          rw [next1_post, x_post]
          rw [← ‹_ = slots.set n sl›] at key
          exact key
        · step*
          rw [next1_post]
          exact skip_inv state blocks0 start «end» blocks slots first n.val next.val hI hnx
            (by rw [← hi1, ← hi2]; scalar_tac)
      · split
        · have hn0 : n.val = 0 := by scalar_tac
          simp only [WP.spec_ok]
          rw [hn0] at hI
          exact done_inv state blocks0 start «end» blocks slots first next.val hI (by scalar_tac)
        · have hn1 : 1 ≤ n.val := by scalar_tac
          have hmemA : ∀ i < n.val, slots.val[i]! ∈ slots.val.take n.val :=
            fun i hi => mem_take_n _ _ _ hi (by simp; omega)
          have hpos : ∀ i < n.val, (slots.val[i]!).t.val < (slots.val[i]!).end.val :=
            fun i hi => (hA _ (hmemA i hi)).1.2.2.2.1
          have hs0 : (slots.val[0]'(by simp)).t.val < (slots.val[0]'(by simp)).end.val := by
            rw [← getElem!_eq]; exact hpos 0 hn1
          step*
          have hr0 : r.val = (slots.val[0]!).end.val - (slots.val[0]!).t.val := by
            rw [r_post, s_post, getElem!_eq _ _ (by simp)]
          step with min_loop0_spec slots n r 1#usize hn4 (by simp; omega) hpos
            (by have := hpos 0 hn1; omega)
            (by intro i hi; simp at hi; subst hi; omega) as ⟨r1, hr1a, hr1b⟩
          rw [run_dispatch n state slots r1 hn1 hn4]
          have hov : ∀ l < n.val, (slots.val[l]!).t.val + r1.val ≤ U32.max := by
            intro l hl; have := hr1b l hl; have := hpos l hl; have := u32_lt (slots.val[l]!).end
            scalar_tac
          step with run_spec hw n state slots r1 hn1 hn4 hr1a hov as ⟨slots1, hrun⟩
          have hS := run_take n.val hn4 (vOf (wv state.val) 0) r1.val slots slots1
            (fun l hl => by have := hov l hl; scalar_tac) (fun l hl hln => (hrun l hl).1 hln)
          have hpwS : (slots1.val.take n.val).Pairwise (fun a b => a.lane.val < b.lane.val) := by
            rw [hS, List.pairwise_map]; exact hpw
          have hfinS : ∀ sl ∈ slots1.val.take n.val, keepB sl = false →
              1 ≤ sl.t.val ∧ sl.lane.val < blocks.length := by
            intro sl hsl _
            rw [hS, List.mem_map] at hsl
            obtain ⟨sl0, hsl0, rfl⟩ := hsl
            obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hsl0
            have hi' : i < n.val := by simp at hi; omega
            have hb := hov i hi'
            rw [List.getElem_take, ← getElem!_eq _ _ (by simp; omega)]
            refine ⟨?_, ?_⟩
            · rw [advF_t _ _ _ (by scalar_tac)]; omega
            · show (slots.val[i]!).lane.val < blocks.length
              rw [hlen]; exact (hA _ (hmemA i hi')).1.1
          step with compact_loop1_spec hw n blocks slots1 blocks slots1 0#usize 0#usize hn4 hpwS hfinS
            (by refine ⟨le_refl _, Nat.zero_le _, rfl, by simp, fun _ _ => rfl, by simp, fun _ _ => rfl⟩)
            as ⟨blocks1, slots2, k, hres⟩
          have hrr : ∀ sl ∈ slots.val.take n.val, r1.val ≤ sl.end.val - sl.t.val := by
            intro sl hsl
            obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hsl
            have hi' : i < n.val := by simp at hi; omega
            rw [List.getElem_take, ← getElem!_eq _ _ (by simp; omega)]
            exact hr1b i hi'
          exact run_branch_inv state blocks0 start «end» blocks slots first n.val next.val hI hn1 r1.val
            hr1a hrr slots1 hS blocks1 slots2 k.val hres
    · split
      · exfalso; scalar_tac
      · have hn1 : 1 ≤ n.val := by scalar_tac
        have hmemA : ∀ i < n.val, slots.val[i]! ∈ slots.val.take n.val :=
          fun i hi => mem_take_n _ _ _ hi (by simp; omega)
        have hpos : ∀ i < n.val, (slots.val[i]!).t.val < (slots.val[i]!).end.val :=
          fun i hi => (hA _ (hmemA i hi)).1.2.2.2.1
        have hs0 : (slots.val[0]'(by simp)).t.val < (slots.val[0]'(by simp)).end.val := by
          rw [← getElem!_eq]; exact hpos 0 hn1
        step*
        have hr0 : r.val = (slots.val[0]!).end.val - (slots.val[0]!).t.val := by
          rw [r_post, s_post, getElem!_eq _ _ (by simp)]
        step with min_loop2_spec slots n r 1#usize hn4 (by simp; omega) hpos
          (by have := hpos 0 hn1; omega)
          (by intro i hi; simp at hi; subst hi; omega) as ⟨r1, hr1a, hr1b⟩
        rw [run_dispatch n state slots r1 hn1 hn4]
        have hov : ∀ l < n.val, (slots.val[l]!).t.val + r1.val ≤ U32.max := by
          intro l hl; have := hr1b l hl; have := hpos l hl; have := u32_lt (slots.val[l]!).end
          scalar_tac
        step with run_spec hw n state slots r1 hn1 hn4 hr1a hov as ⟨slots1, hrun⟩
        have hS := run_take n.val hn4 (vOf (wv state.val) 0) r1.val slots slots1
          (fun l hl => by have := hov l hl; scalar_tac) (fun l hl hln => (hrun l hl).1 hln)
        have hpwS : (slots1.val.take n.val).Pairwise (fun a b => a.lane.val < b.lane.val) := by
          rw [hS, List.pairwise_map]; exact hpw
        have hfinS : ∀ sl ∈ slots1.val.take n.val, keepB sl = false →
            1 ≤ sl.t.val ∧ sl.lane.val < blocks.length := by
          intro sl hsl _
          rw [hS, List.mem_map] at hsl
          obtain ⟨sl0, hsl0, rfl⟩ := hsl
          obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hsl0
          have hi' : i < n.val := by simp at hi; omega
          have hb := hov i hi'
          rw [List.getElem_take, ← getElem!_eq _ _ (by simp; omega)]
          refine ⟨?_, ?_⟩
          · rw [advF_t _ _ _ (by scalar_tac)]; omega
          · show (slots.val[i]!).lane.val < blocks.length
            rw [hlen]; exact (hA _ (hmemA i hi')).1.1
        step with compact_loop3_spec hw n blocks slots1 blocks slots1 0#usize 0#usize hn4 hpwS hfinS
          (by refine ⟨le_refl _, Nat.zero_le _, rfl, by simp, fun _ _ => rfl, by simp, fun _ _ => rfl⟩)
          as ⟨blocks1, slots2, k, hres⟩
        have hrr : ∀ sl ∈ slots.val.take n.val, r1.val ≤ sl.end.val - sl.t.val := by
          intro sl hsl
          obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hsl
          have hi' : i < n.val := by simp at hi; omega
          rw [List.getElem_take, ← getElem!_eq _ _ (by simp; omega)]
          exact hr1b i hi'
        exact run_branch_inv state blocks0 start «end» blocks slots first n.val next.val hI hn1 r1.val
          hr1a hrr slots1 hS blocks1 slots2 k.val hres
  · exact hI

end slhdsa
