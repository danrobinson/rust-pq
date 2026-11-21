import Slhdsa.Proofs.Xmss
open Aeneas Aeneas.Std Result

/-! FORS. -/

namespace slhdsa

@[local simp, local scalar_tac_simps] theorem fors_A_eq : params.A = 12#u32 := by simp [global_simps]
@[local simp, local scalar_tac_simps] theorem fors_K_eq : params.K = 14#u32 := by simp [global_simps]
@[local simp] theorem fors_FORS_PRF_eq : address.FORS_PRF = 6#u32 := by simp [global_simps]
@[local simp] theorem fors_FORS_ROOTS_eq : address.FORS_ROOTS = 4#u32 := by simp [global_simps]

@[local step]
theorem fors_extend_from_slice_spec (v : alloc.vec.Vec U8) (s : Slice U8)
    (h : v.length + s.length ≤ Usize.max) :
    alloc.vec.Vec.extend_from_slice core.clone.CloneU8 v s ⦃ r => r.val = v.val ++ s.val ⦄ := by
  unfold alloc.vec.Vec.extend_from_slice
  simp only [h, ↓reduceDIte]
  apply WP.spec_bind (List.clone_spec (l := s.val) (by intros; simp [liftFun1]))
  intro l' hl'
  simp [hl']

@[step]
theorem fors_sk_gen_spec (sk : Array U8 16#usize) (pk : hash.Seed) (hpk : SeedOk pk) (a : address.Adrs) (idx : U32) :
    fors.fors_sk_gen sk pk a idx ⦃ r =>
      bytes r.val = Spec.forsSkGen (bytes sk.val) (bytes pk.pk_seed.val) (adrsS a) idx.val ⦄ := by
  unfold fors.fors_sk_gen
  step*
  rw [r_post]
  simp [Spec.forsSkGen, Spec.PRF, adrsS, Spec.Adrs.setTypeAndClear, Spec.FORS_PRF, *]

/-! The node at a height of at most `BATCH_HEIGHT`, computed in one batch. -/

theorem setSlice0_getElem! {α} [Inhabited α] (l s : List α) (j : Nat) (hj : j < s.length)
    (hs : s.length ≤ l.length) : (l.setSlice! 0 s)[j]! = s[j]! := by
  have hm : min s.length (l.length - 0) = s.length := by omega
  simp only [List.setSlice!, List.take_zero, List.nil_append, hm, Nat.zero_add,
    List.take_of_length_le (le_refl _)]
  rw [List.getElem!_eq_getElem?_getD, List.getElem!_eq_getElem?_getD, List.getElem?_append_left hj]

theorem slice0_getElem! {α} [Inhabited α] (l : List α) (k c : Nat) (h : c < k) :
    (List.slice 0 k l)[c]! = l[c]! := by
  simp [List.slice, List.getElem!_eq_getElem?_getD, h]

theorem fors_batch_loop0_spec (sk : Array U8 16#usize) (i z : U32) (n : Usize) (prf : address.Adrs)
    (hn : n.val ≤ 128) (hb : i.val * 2 ^ z.val + n.val ≤ 2 ^ 32 - 1) (hz : z.val < 32)
    (blocks : Array (Array U8 64#usize) 128#usize) (start «end» : Array U32 128#usize) (j : Usize)
    (hj : j.val ≤ n.val)
    (hinv : ∀ k, k < j.val →
      bytes (blocks.val[k]!).val =
        padFrom 64 ({ adrsS prf with word3 := i.val * 2 ^ z.val + k }.compress ++ bytes sk.val) ∧
      (start.val[k]!).val = i.val * 2 ^ z.val + k ∧ («end».val[k]!).val = i.val * 2 ^ z.val + k + 1) :
    fors.fors_batch_loop0 sk i z n prf blocks start «end» j ⦃ r =>
      ∀ k, k < n.val →
        bytes (r.1.val[k]!).val =
          padFrom 64 ({ adrsS prf with word3 := i.val * 2 ^ z.val + k }.compress ++ bytes sk.val) ∧
        (r.2.1.val[k]!).val = i.val * 2 ^ z.val + k ∧ (r.2.2.val[k]!).val = i.val * 2 ^ z.val + k + 1 ⦄ := by
  unfold fors.fors_batch_loop0
  apply loop.spec_decr_nat
    (measure := fun (p : Array (Array U8 64#usize) 128#usize × Array U32 128#usize ×
      Array U32 128#usize × Usize) => n.val - p.2.2.2.val)
    (inv := fun p => p.2.2.2.val ≤ n.val ∧ ∀ k, k < p.2.2.2.val →
      bytes (p.1.val[k]!).val =
        padFrom 64 ({ adrsS prf with word3 := i.val * 2 ^ z.val + k }.compress ++ bytes sk.val) ∧
      (p.2.1.val[k]!).val = i.val * 2 ^ z.val + k ∧ (p.2.2.1.val[k]!).val = i.val * 2 ^ z.val + k + 1)
  · rintro ⟨blocks, start, «end», j⟩ ⟨h1, h2⟩
    simp only [fors.fors_batch_loop0.body]
    simp only at h1 h2
    have hsh : (i.val <<< z.val) % U32.size = i.val * 2 ^ z.val := by
      rw [Nat.shiftLeft_eq]; exact Nat.mod_eq_of_lt (by simp [U32.size, U32.numBits]; omega)
    step*
    · have hjv : j.val < n.val := by scalar_tac
      have hi2 : i2.val = j.val := by rw [i2_post]; simp; scalar_tac
      have hidx : idx.val = i.val * 2 ^ z.val + j.val := by rw [idx_post, i1_post, hsh, hi2]
      refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      intro k hk
      rw [j1_post] at hk
      rw [a2_post, a3_post, a4_post, Array.set_val_eq, Array.set_val_eq, Array.set_val_eq]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | hk
      · rw [getElem!_set_ne' _ _ _ _ (by omega), getElem!_set_ne' _ _ _ _ (by omega),
          getElem!_set_ne' _ _ _ _ (by omega)]
        exact h2 k hk
      · subst hk
        rw [getElem!_set_self' _ _ _ (by simp; omega), getElem!_set_self' _ _ _ (by simp; omega),
          getElem!_set_self' _ _ _ (by simp; omega)]
        refine ⟨?_, hidx, by rw [i3_post, hidx]⟩
        rw [a1_post, s_post, a_post, Array.val_to_slice]
        simp [adrsS, hidx]
    · have : j.val = n.val := by scalar_tac
      rw [this] at h2; exact h2
  · exact ⟨hj, hinv⟩

theorem fors_batch_loop1_spec (ty : U32) (n : Usize) (hn : n.val ≤ 128)
    (blocks0 blocks : Array (Array U8 64#usize) 128#usize) (j : Usize) (hj : j.val ≤ n.val)
    (hdone : ∀ k, k < j.val → bytes (blocks.val[k]!).val =
      (bytes (blocks0.val[k]!).val).set 9 (BitVec.ofNat 8 ty.val))
    (hrest : ∀ k, j.val ≤ k → blocks.val[k]! = blocks0.val[k]!) :
    fors.fors_batch_loop1 ty n blocks j ⦃ r =>
      ∀ k, k < n.val → bytes (r.val[k]!).val =
        (bytes (blocks0.val[k]!).val).set 9 (BitVec.ofNat 8 ty.val) ⦄ := by
  unfold fors.fors_batch_loop1
  apply loop.spec_decr_nat
    (measure := fun (p : Array (Array U8 64#usize) 128#usize × Usize) => n.val - p.2.val)
    (inv := fun p => p.2.val ≤ n.val ∧
      (∀ k, k < p.2.val → bytes (p.1.val[k]!).val =
        (bytes (blocks0.val[k]!).val).set 9 (BitVec.ofNat 8 ty.val)) ∧
      (∀ k, p.2.val ≤ k → p.1.val[k]! = blocks0.val[k]!))
  · rintro ⟨blocks, j⟩ ⟨h1, h2, h3⟩
    simp only [fors.fors_batch_loop1.body]
    simp only at h1 h2 h3
    step*
    · have hil : j.val < blocks.val.length := by simp; scalar_tac
      refine ⟨by scalar_tac, ?_, ?_, by scalar_tac⟩
      · rw [j1_post, index_mut_back_post, Array.set_val_eq]
        refine forall_set_succ blocks.val j.val a1 (fun k (b : Array U8 64#usize) => bytes b.val =
          (bytes (blocks0.val[k]!).val).set 9 (BitVec.ofNat 8 ty.val)) hil h2 ?_
        rw [a1_post, Array.set_val_eq, bytes_set, i1_post, cast_u8_bv32, a_post,
          ← getElem!_eq _ _ hil, h3 _ (le_refl _)]
        rfl
      · intro k hk
        rw [index_mut_back_post, Array.set_val_eq, getElem!_set_ne' _ _ _ _ (by scalar_tac)]
        exact h3 k (by scalar_tac)
  · exact ⟨hj, hdone, hrest⟩

theorem fors_batch_loop2_spec (n : Usize) (hn : n.val ≤ 128)
    (blocks : Array (Array U8 64#usize) 128#usize) (vals : Array (Array U8 16#usize) 128#usize)
    (j : Usize) (hj : j.val ≤ n.val)
    (hinv : ∀ (k : Nat), k < j.val → bytes (vals.val[k]!).val = blkVal blocks.val[k]!) :
    fors.fors_batch_loop2 n blocks vals j ⦃ r =>
      ∀ (k : Nat), k < n.val → bytes (r.val[k]!).val = blkVal blocks.val[k]! ⦄ := by
  unfold fors.fors_batch_loop2
  apply loop.spec_decr_nat
    (measure := fun (p : Array (Array U8 16#usize) 128#usize × Usize) => n.val - p.2.val)
    (inv := fun p => p.2.val ≤ n.val ∧
      ∀ (k : Nat), k < p.2.val → bytes (p.1.val[k]!).val = blkVal blocks.val[k]!)
  · rintro ⟨vals, j⟩ ⟨h1, h2⟩
    simp only [fors.fors_batch_loop2.body]
    simp only at h1 h2
    step*
    · refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      rw [j1_post, a2_post, Array.set_val_eq]
      refine forall_set_succ vals.val j.val a1 (fun k (b : Array U8 16#usize) =>
        bytes b.val = blkVal blocks.val[k]!) (by simp; scalar_tac) h2 ?_
      rw [a1_post, a_post, ← getElem!_eq _ _ (by simp; scalar_tac)]
      rfl
  · exact ⟨hj, hinv⟩

theorem fors_batch_loop3_loop1_spec (blocks : Array (Array U8 64#usize) 128#usize)
    (cnt : Usize) (hn : cnt.val ≤ 128) (vals : Array (Array U8 16#usize) 128#usize)
    (j : Usize) (hj : j.val ≤ cnt.val)
    (hinv : ∀ (k : Nat), k < j.val → bytes (vals.val[k]!).val = blkVal blocks.val[k]!) :
    fors.fors_batch_loop3_loop1 blocks vals cnt j ⦃ r =>
      ∀ (k : Nat), k < cnt.val → bytes (r.val[k]!).val = blkVal blocks.val[k]! ⦄ := by
  unfold fors.fors_batch_loop3_loop1
  apply loop.spec_decr_nat
    (measure := fun (p : Array (Array U8 16#usize) 128#usize × Usize) => cnt.val - p.2.val)
    (inv := fun p => p.2.val ≤ cnt.val ∧
      ∀ (k : Nat), k < p.2.val → bytes (p.1.val[k]!).val = blkVal blocks.val[k]!)
  · rintro ⟨vals, j⟩ ⟨h1, h2⟩
    simp only [fors.fors_batch_loop3_loop1.body]
    simp only at h1 h2
    step*
    · refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      rw [j1_post, a2_post, Array.set_val_eq]
      refine forall_set_succ vals.val j.val a1 (fun k (b : Array U8 16#usize) =>
        bytes b.val = blkVal blocks.val[k]!) (by simp; scalar_tac) h2 ?_
      rw [a1_post, a_post, ← getElem!_eq _ _ (by simp; scalar_tac)]
      rfl
  · exact ⟨hj, hinv⟩

theorem fors_batch_loop3_loop0_spec (i z i1 : U32) (i2 : U64) (i3 i4 i5 i6 : U32)
    (A0 : address.Adrs) (hA0 : A0 = ⟨i1, i2, i3, i4, i5, i6⟩)
    (vals : Array (Array U8 16#usize) 128#usize) (lvl : U32) (cnt : Usize)
    (hlvl : 1 ≤ lvl.val) (hlz : lvl.val ≤ z.val) (hz : z.val ≤ 7)
    (hcnt : cnt.val = 2 ^ (z.val - lvl.val)) (hi : (i.val + 1) * 2 ^ z.val < 2 ^ 32)
    (blocks : Array (Array U8 64#usize) 128#usize) (start «end» : Array U32 128#usize) (j : Usize)
    (hj : j.val ≤ cnt.val)
    (hinv : ∀ k, k < j.val →
      bytes (blocks.val[k]!).val =
        padFrom 64 ({ adrsS A0 with word2 := lvl.val, word3 := i.val * 2 ^ (z.val - lvl.val) + k }.compress ++
          (bytes (vals.val[2 * k]!).val ++ bytes (vals.val[2 * k + 1]!).val)) ∧
      (start.val[k]!).val = i.val * 2 ^ (z.val - lvl.val) + k ∧
      («end».val[k]!).val = i.val * 2 ^ (z.val - lvl.val) + k + 1) :
    fors.fors_batch_loop3_loop0 i z i1 i2 i3 i4 i5 i6 blocks start «end» vals lvl cnt j ⦃ r =>
      ∀ k, k < cnt.val →
        bytes (r.1.val[k]!).val =
          padFrom 64 ({ adrsS A0 with word2 := lvl.val, word3 := i.val * 2 ^ (z.val - lvl.val) + k }.compress ++
            (bytes (vals.val[2 * k]!).val ++ bytes (vals.val[2 * k + 1]!).val)) ∧
        (r.2.1.val[k]!).val = i.val * 2 ^ (z.val - lvl.val) + k ∧
        (r.2.2.val[k]!).val = i.val * 2 ^ (z.val - lvl.val) + k + 1 ⦄ := by
  have hp1 : 2 ^ (z.val - lvl.val) ≤ 2 ^ z.val := Nat.pow_le_pow_right (by omega) (by omega)
  have hp2 : 2 ^ z.val ≤ 2 ^ 7 := Nat.pow_le_pow_right (by omega) hz
  have hp3 : 2 * 2 ^ (z.val - lvl.val) ≤ 2 ^ z.val := by
    rw [← pow_succ']; exact Nat.pow_le_pow_right (by omega) (by omega)
  have hiz : i.val * 2 ^ (z.val - lvl.val) ≤ i.val * 2 ^ z.val := Nat.mul_le_mul_left _ hp1
  unfold fors.fors_batch_loop3_loop0
  apply loop.spec_decr_nat
    (measure := fun (p : Array (Array U8 64#usize) 128#usize × Array U32 128#usize ×
      Array U32 128#usize × Usize) => cnt.val - p.2.2.2.val)
    (inv := fun p => p.2.2.2.val ≤ cnt.val ∧ ∀ k, k < p.2.2.2.val →
      bytes (p.1.val[k]!).val =
        padFrom 64 ({ adrsS A0 with word2 := lvl.val, word3 := i.val * 2 ^ (z.val - lvl.val) + k }.compress ++
          (bytes (vals.val[2 * k]!).val ++ bytes (vals.val[2 * k + 1]!).val)) ∧
      (p.2.1.val[k]!).val = i.val * 2 ^ (z.val - lvl.val) + k ∧
      (p.2.2.1.val[k]!).val = i.val * 2 ^ (z.val - lvl.val) + k + 1)
  · rintro ⟨blocks, start, «end», j⟩ ⟨h1, h2⟩
    simp only [fors.fors_batch_loop3_loop0.body]
    simp only at h1 h2
    have hsh : (i.val <<< (z.val - lvl.val)) % U32.size = i.val * 2 ^ (z.val - lvl.val) := by
      rw [Nat.shiftLeft_eq]; exact Nat.mod_eq_of_lt (by simp [U32.size, U32.numBits]; nlinarith)
    step*
    · have hjv : j.val < cnt.val := by scalar_tac
      have hi9 : i9.val = j.val := by rw [i9_post]; simp; scalar_tac
      have hidx : idx.val = i.val * 2 ^ (z.val - lvl.val) + j.val := by
        rw [idx_post, i8_post, i7_post, hsh, hi9]
      refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      intro k hk
      rw [j1_post] at hk
      rw [a5_post, a6_post, a7_post, Array.set_val_eq, Array.set_val_eq, Array.set_val_eq]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | hk
      · rw [getElem!_set_ne' _ _ _ _ (by omega), getElem!_set_ne' _ _ _ _ (by omega),
          getElem!_set_ne' _ _ _ _ (by omega)]
        exact h2 k hk
      · subst hk
        rw [getElem!_set_self' _ _ _ (by simp; omega), getElem!_set_self' _ _ _ (by simp; omega),
          getElem!_set_self' _ _ _ (by simp; omega)]
        refine ⟨?_, hidx, by rw [i12_post, hidx]⟩
        rw [a4_post, a2_post, a3_post, ← getElem!_eq _ _ (by simp; scalar_tac),
          ← getElem!_eq _ _ (by simp; scalar_tac), i11_post, i10_post, a1_post, a_post, hA0]
        simp [adrsS, hidx]
    · have : j.val = cnt.val := by scalar_tac
      rw [this] at h2; exact h2
  · exact ⟨hj, hinv⟩

theorem fors_forsNode_succ (sk pk : Spec.Bytes) (A : Spec.Adrs) (x h : Nat) :
    Spec.forsNode sk x (h + 1) pk A =
      Spec.H pk { A with word2 := h + 1, word3 := x }
        (Spec.forsNode sk (2 * x) h pk A ++ Spec.forsNode sk (2 * x + 1) h pk A) := by
  rfl

theorem fors_batch_loop3_spec (sk : Array U8 16#usize) (pk : hash.Seed) (hpk : SeedOk pk)
    (i z i1 : U32) (i2 : U64) (i3 i4 i5 i6 : U32)
    (A0 : address.Adrs) (hA0 : A0 = ⟨i1, i2, i3, i4, i5, i6⟩)
    (hz : z.val ≤ 7) (hi : (i.val + 1) * 2 ^ z.val < 2 ^ 32)
    (blocks : Array (Array U8 64#usize) 128#usize) (start «end» : Array U32 128#usize)
    (vals : Array (Array U8 16#usize) 128#usize) (lvl : U32) (cnt : Usize)
    (hlvl : 1 ≤ lvl.val) (hlz : lvl.val ≤ z.val + 1) (hcnt : cnt.val = 2 ^ z.val / 2 ^ lvl.val)
    (hv : ∀ k, k < 2 ^ z.val / 2 ^ (lvl.val - 1) → bytes (vals.val[k]!).val =
      Spec.forsNode (bytes sk.val) (i.val * 2 ^ (z.val - (lvl.val - 1)) + k) (lvl.val - 1)
        (bytes pk.pk_seed.val) (adrsS A0)) :
    fors.fors_batch_loop3 i z pk.state i1 i2 i3 i4 i5 i6 blocks start «end» vals lvl cnt ⦃ r =>
      bytes (r.val[0]!).val = Spec.forsNode (bytes sk.val) i.val z.val (bytes pk.pk_seed.val) (adrsS A0) ⦄ := by
  unfold fors.fors_batch_loop3
  apply loop.spec_decr_nat
    (measure := fun (p : Array (Array U8 64#usize) 128#usize × Array U32 128#usize ×
      Array U32 128#usize × Array (Array U8 16#usize) 128#usize × U32 × Usize) => z.val + 1 - p.2.2.2.2.1.val)
    (inv := fun p => 1 ≤ p.2.2.2.2.1.val ∧ p.2.2.2.2.1.val ≤ z.val + 1 ∧
      p.2.2.2.2.2.val = 2 ^ z.val / 2 ^ p.2.2.2.2.1.val ∧
      ∀ k, k < 2 ^ z.val / 2 ^ (p.2.2.2.2.1.val - 1) → bytes (p.2.2.2.1.val[k]!).val =
        Spec.forsNode (bytes sk.val) (i.val * 2 ^ (z.val - (p.2.2.2.2.1.val - 1)) + k)
          (p.2.2.2.2.1.val - 1) (bytes pk.pk_seed.val) (adrsS A0))
  · rintro ⟨blocks, start, «end», vals, lvl, cnt⟩ ⟨h1, h2, h3, h4⟩
    simp only [fors.fors_batch_loop3.body]
    simp only at h1 h2 h3 h4
    simp only [step_simps]
    spec_split
    · have hlz' : lvl.val ≤ z.val := by scalar_tac
      have hcnt' : cnt.val = 2 ^ (z.val - lvl.val) := by
        rw [h3, Nat.pow_div hlz' (by omega)]
      have hp2 : 2 ^ z.val ≤ 2 ^ 7 := Nat.pow_le_pow_right (by omega) hz
      have hp1 : 2 ^ (z.val - lvl.val) ≤ 2 ^ z.val := Nat.pow_le_pow_right (by omega) (by omega)
      have hprev : 2 ^ z.val / 2 ^ (lvl.val - 1) = 2 * 2 ^ (z.val - lvl.val) := by
        rw [Nat.pow_div (by omega) (by omega), ← pow_succ']; congr 1; omega
      let* ⟨ blocks1, start1, end1, hQ ⟩ ← fors_batch_loop3_loop0_spec i z i1 i2 i3 i4 i5 i6 A0 hA0
        vals lvl cnt h1 hlz' hz hcnt' hi blocks start «end» 0#usize (by simp) (by simp)
      step*
      have hsl : s.length = cnt.val := by rw [s_post1]; rfl
      let* ⟨ vals1, vals1_post ⟩ ← fors_batch_loop3_loop1_spec (index_mut_back s3) cnt (by scalar_tac)
        vals 0#usize (by simp) (by simp)
      let* ⟨ cnt1, cnt1_post ⟩ ← Usize.div_spec
      let* ⟨ lvl1, lvl1_post ⟩ ← U32.add_spec
      refine ⟨by scalar_tac, by scalar_tac, ?_, ?_, by scalar_tac⟩
      · rw [cnt1_post, lvl1_post, h3, Nat.div_div_eq_div_mul, ← pow_succ]
      · intro k hk
        rw [lvl1_post, show lvl.val + 1 - 1 = lvl.val by omega] at hk ⊢
        have hkc : k < cnt.val := by rw [hcnt']; rwa [Nat.pow_div hlz' (by omega)] at hk
        obtain ⟨hb, hs, he⟩ := hQ k hkc
        have h2k : 2 * k < 2 ^ z.val / 2 ^ (lvl.val - 1) := by rw [hprev]; omega
        have h2k1 : 2 * k + 1 < 2 ^ z.val / 2 ^ (lvl.val - 1) := by rw [hprev]; omega
        have hs3 : s3.val.length = cnt.val := by rw [← hsl]; exact s3_post
        rw [vals1_post k hkc, blkVal, s_post2, setSlice0_getElem! _ _ _ (by omega) (by simp; omega),
          s3_post1 k (by omega), s_post, slice0_getElem! _ _ _ hkc, s1_post, s2_post,
          Array.val_to_slice, Array.val_to_slice, he, hs, runBlock_one, hb]
        have hpkl : (bytes pk.pk_seed.val).length = 16 := by simp
        refine (stepBlock_pair_value _ hpkl _ hpk
          { adrsS A0 with word2 := lvl.val, word3 := i.val * 2 ^ (z.val - lvl.val) + k } _
          (by simp)).trans ?_
        have e := fors_forsNode_succ (bytes sk.val) (bytes pk.pk_seed.val) (adrsS A0)
          (i.val * 2 ^ (z.val - lvl.val) + k) (lvl.val - 1)
        rw [show lvl.val - 1 + 1 = lvl.val by omega] at e
        have e2 : i.val * 2 ^ (z.val - (lvl.val - 1)) = 2 * (i.val * 2 ^ (z.val - lvl.val)) := by
          rw [show z.val - (lvl.val - 1) = (z.val - lvl.val) + 1 by omega, pow_succ]; ring
        rw [e, h4 (2 * k) h2k, h4 (2 * k + 1) h2k1, e2,
          show 2 * (i.val * 2 ^ (z.val - lvl.val) + k) = 2 * (i.val * 2 ^ (z.val - lvl.val)) + 2 * k
            by ring]
        rfl
    · have hlz' : lvl.val = z.val + 1 := by scalar_tac
      have h0 := h4 0 (by rw [hlz', Nat.add_sub_cancel, Nat.div_self (by positivity)]; omega)
      rw [hlz', Nat.add_sub_cancel, Nat.sub_self, pow_zero, Nat.mul_one, Nat.add_zero] at h0
      simp only [step_simps]
      exact h0
  · exact ⟨hlvl, hlz, hcnt, hv⟩

/-- A FORS leaf block: `PRF` in place, the type switched, then `F` in place. -/
theorem fors_leaf_value (pk : Spec.Bytes) (hpk : pk.length = 16) (st : List Spec.SHA256.Word)
    (hst : st = Spec.SHA256.compress Spec.SHA256.H0 (pk ++ List.replicate 48 0#8))
    (P : Spec.Adrs) (m : Spec.Bytes) (hm : m.length = 16) (t ty : Nat) :
    ((stepBlock st ((stepBlock st (padFrom 64 ({ P with word3 := t }.compress ++ m)) t).set 9
      (BitVec.ofNat 8 ty)) t).drop 22).take 16 =
      Spec.thash pk { P with word3 := t, typ := ty } (Spec.thash pk { P with word3 := t } m) := by
  rw [stepBlock_thash pk hpk st hst _ _ hm, block_set_typ _ _ (by rw [thash_length _ hpk]; omega),
    stepBlock_thash pk hpk st hst _ _ (thash_length _ hpk _ _),
    block_value _ _ (by rw [thash_length _ hpk]; omega), List.take_left' (thash_length _ hpk _ _)]

theorem fors_batch_spec (sk : Array U8 16#usize) (i z : U32) (pk : hash.Seed) (hpk : SeedOk pk)
    (a : address.Adrs) (hz : z.val ≤ 7) (h : (i.val + 1) * 2 ^ z.val < 2 ^ 32) :
    fors.fors_batch sk i z pk a ⦃ r =>
      bytes r.val = Spec.forsNode (bytes sk.val) i.val z.val (bytes pk.pk_seed.val) (adrsS a) ⦄ := by
  rename' a => adrs
  unfold fors.fors_batch
  have hp2 : 2 ^ z.val ≤ 2 ^ 7 := Nat.pow_le_pow_right (by omega) hz
  have hpos : 1 ≤ 2 ^ z.val := Nat.one_le_two_pow
  let* ⟨ n, n_post, n_post1 ⟩ ← Usize.ShiftLeft_spec
  · rcases System.Platform.numBits_eq with h | h <;> simp [h] <;> omega
  have hn : n.val = 2 ^ z.val := by
    rw [n_post, Nat.one_shiftLeft]
    exact Nat.mod_eq_of_lt (lt_of_le_of_lt hp2 (by
      rcases System.Platform.numBits_eq with h | h <;> simp [Usize.size, Usize.numBits, h]))
  have hiz : i.val * 2 ^ z.val + 2 ^ z.val = (i.val + 1) * 2 ^ z.val := by ring
  let* ⟨ a, a_post, a_post1 ⟩ ← with_type_spec
  let* ⟨ prf, prf_post ⟩ ← with_keypair_spec
  let* ⟨ blocks1, start1, end1, hL ⟩ ← fors_batch_loop0_spec sk i z n prf (by omega) (by omega)
    (by omega) _ _ _ 0#usize (by simp) (by simp)
  step*
  let* ⟨ blocks3, blocks3_post ⟩ ← fors_batch_loop1_spec adrs.typ n (by omega) (index_mut_back s3)
    (index_mut_back s3) 0#usize (by simp) (by simp) (fun _ _ => rfl)
  step*
  let* ⟨ vals1, vals1_post ⟩ ← fors_batch_loop2_spec n (by omega) (index_mut_back1 s7)
    (Array.repeat 128#usize (Array.repeat 16#usize 0#u8)) 0#usize (by simp) (by simp)
  let* ⟨ cnt, cnt_post ⟩ ← Usize.div_spec
  have hpkl : (bytes pk.pk_seed.val).length = 16 := by simp
  have hsl : s.length = n.val := by rw [s_post1]; rfl
  have hs4l : s4.length = n.val := by rw [s4_post1]; rfl
  have hv : ∀ k, k < 2 ^ z.val / 2 ^ (1 - 1) → bytes (vals1.val[k]!).val =
      Spec.forsNode (bytes sk.val) (i.val * 2 ^ (z.val - (1 - 1)) + k) (1 - 1)
        (bytes pk.pk_seed.val) (adrsS adrs) := by
    intro k hk
    simp only [Nat.sub_self, pow_zero, Nat.div_one, Nat.sub_zero] at hk ⊢
    have hkn : k < n.val := by omega
    obtain ⟨hb, hs, he⟩ := hL k hkn
    have hs3 : s3.val.length = n.val := by rw [← hsl]; exact s3_post
    have hs7 : s7.val.length = n.val := by rw [← hs4l]; exact s7_post
    rw [vals1_post k hkn, blkVal, s4_post2, setSlice0_getElem! _ _ _ (by omega) (by simp; omega),
      s7_post1 k (by omega), s4_post, slice0_getElem! _ _ _ hkn, s5_post, s6_post,
      Array.val_to_slice, Array.val_to_slice, he, hs, runBlock_one, blocks3_post k hkn,
      s_post2, setSlice0_getElem! _ _ _ (by omega) (by simp; omega),
      s3_post1 k (by omega), s_post, slice0_getElem! _ _ _ hkn, s1_post, s2_post,
      Array.val_to_slice, Array.val_to_slice, he, hs, runBlock_one, hb,
      fors_leaf_value _ hpkl _ hpk _ _ (by simp)]
    simp [Spec.forsNode, Spec.F, Spec.forsSkGen, Spec.PRF, prf_post, a_post1, adrsS,
      Spec.Adrs.setTypeAndClear, Spec.FORS_PRF]
  let* ⟨ vals2, vals2_post ⟩ ← fors_batch_loop3_spec sk pk hpk i z adrs.layer adrs.tree adrs.typ
    adrs.keypair adrs.word2 adrs.word3 adrs rfl hz h (index_mut_back1 s7) start1 end1 vals1 1#u32 cnt
    (by simp) (by simp) (by rw [cnt_post, hn]; simp) hv
  let* ⟨ r, r_post ⟩ ← Array.index_usize_spec
  rw [r_post, ← getElem!_eq _ _ (by simp)]
  exact vals2_post

theorem fors_node_spec_aux (sk : Array U8 16#usize) (pk : hash.Seed) (hpk : SeedOk pk) (a : address.Adrs) (n : Nat) :
    ∀ (i z : U32), z.val = n → (i.val + 1) * 2 ^ n < 2 ^ 32 →
    fors.fors_node sk i z pk a ⦃ r =>
      bytes r.val = Spec.forsNode (bytes sk.val) i.val n (bytes pk.pk_seed.val) (adrsS a) ⦄ := by
  induction n with
  | zero =>
    intro i z hz h
    have hz7 : z ≤ fors.BATCH_HEIGHT := by simp only [global_simps]; scalar_tac
    unfold fors.fors_node
    simp only [hz7, ↓reduceIte]
    have := fors_batch_spec sk i z pk hpk a (by omega) (by rw [hz]; simpa using h)
    rw [hz] at this; exact this
  | succ n ih =>
    intro i z hz h
    unfold fors.fors_node
    by_cases hz7 : z ≤ fors.BATCH_HEIGHT
    · simp only [hz7, ↓reduceIte]
      have hz7' : z.val ≤ 7 := by simp only [global_simps] at hz7; scalar_tac
      have := fors_batch_spec sk i z pk hpk a hz7' (by rw [hz]; exact h)
      rw [hz] at this; exact this
    · simp only [hz7, ↓reduceIte]
      have hz0 : 1 ≤ z.val := by simp only [global_simps] at hz7; scalar_tac
      have hpos : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      have h1 : (2 * i.val + 1 + 1) * 2 ^ n < 2 ^ 32 := by
        have : (2 * i.val + 1 + 1) * 2 ^ n = (i.val + 1) * 2 ^ (n + 1) := by ring
        omega
      have h2 : (2 * i.val + 1) * 2 ^ n < 2 ^ 32 := by nlinarith
      have h3 : 2 * i.val + 2 ≤ 2 ^ 32 := by nlinarith
      step
      step
      step with ih i1 i2 (by scalar_tac) (by simp [*]; omega)
      step
      step with ih i3 i2 (by scalar_tac) (by simp [*]; omega)
      step*
      rw [r_post]
      simp [Spec.forsNode, adrsS, *]

@[step]
theorem fors_node_spec (sk : Array U8 16#usize) (i z : U32) (pk : hash.Seed) (hpk : SeedOk pk) (a : address.Adrs)
    (h : (i.val + 1) * 2 ^ z.val < 2 ^ 32) :
    fors.fors_node sk i z pk a ⦃ r =>
      bytes r.val = Spec.forsNode (bytes sk.val) i.val z.val (bytes pk.pk_seed.val) (adrsS a) ⦄ :=
  fors_node_spec_aux sk pk hpk a z.val i z rfl h

theorem fors_xor_one_le (x : Nat) : x ^^^ 1 ≤ x + 1 := by
  rcases Nat.even_or_odd x with h | h
  · rw [Nat.xor_one_of_even h]
  · rw [Nat.xor_one_of_odd h]; omega

theorem fors_inner_arith (i idx j : Nat) (hi : i < 14) (hidx : idx < 2 ^ 12) (hj : j < 12) :
    (i <<< (12 - j)) % 2 ^ 32 = i * 2 ^ (12 - j) ∧
    i * 2 ^ (12 - j) + ((idx / 2 ^ j) ^^^ 1) ≤ 2 ^ 32 - 1 ∧
    (i * 2 ^ (12 - j) + ((idx / 2 ^ j) ^^^ 1) + 1) * 2 ^ j < 2 ^ 32 := by
  have h1 : 2 ^ (12 - j) ≤ 2 ^ 12 := Nat.pow_le_pow_right (by omega) (by omega)
  have h2 : 2 ^ j ≤ 2 ^ 11 := Nat.pow_le_pow_right (by omega) (by omega)
  have h3 : idx / 2 ^ j ≤ idx := Nat.div_le_self _ _
  have h4 := fors_xor_one_le (idx / 2 ^ j)
  have h5 : i * 2 ^ (12 - j) ≤ 13 * 2 ^ 12 := Nat.mul_le_mul (by omega) h1
  refine ⟨?_, by omega, ?_⟩
  · rw [Nat.shiftLeft_eq]; exact Nat.mod_eq_of_lt (by omega)
  · calc (i * 2 ^ (12 - j) + ((idx / 2 ^ j) ^^^ 1) + 1) * 2 ^ j
        ≤ (13 * 2 ^ 12 + 2 ^ 12 + 1) * 2 ^ 11 := Nat.mul_le_mul (by omega) h2
      _ < 2 ^ 32 := by norm_num

/-- The `j`-th authentication-path node of FORS tree `i` (Algorithm 16, lines 6–8). -/
def forsAuth (sk pk : Spec.Bytes) (adrs : Spec.Adrs) (i idx j : Nat) : Spec.Bytes :=
  Spec.forsNode sk (i * 2 ^ (Spec.a - j) + ((idx / 2 ^ j) ^^^ 1)) j pk adrs

theorem fors_sign_inner_spec (sk : Array U8 16#usize) (pk : hash.Seed) (hpk : SeedOk pk) (a : address.Adrs)
    (sig : alloc.vec.Vec U8) (i idx j : U32) (S0 : Spec.Bytes) (L0 : Nat)
    (hi : i.val < 14) (hidx : idx.val < 2 ^ 12) (hj : j.val ≤ 12) (hL : L0 ≤ 100000)
    (hlen : sig.length = L0 + 16 * j.val)
    (hinv : bytes sig.val = S0 ++ (List.range j.val).flatMap
      (forsAuth (bytes sk.val) (bytes pk.pk_seed.val) (adrsS a) i.val idx.val)) :
    fors.fors_sign_loop0_loop0 sk pk a sig i idx j ⦃ r =>
      r.length = L0 + 16 * 12 ∧
      bytes r.val = S0 ++ (List.range 12).flatMap
        (forsAuth (bytes sk.val) (bytes pk.pk_seed.val) (adrsS a) i.val idx.val) ⦄ := by
  unfold fors.fors_sign_loop0_loop0
  apply loop.spec_decr_nat
    (measure := fun (p : alloc.vec.Vec U8 × U32) => 12 - p.2.val)
    (inv := fun p => p.2.val ≤ 12 ∧ p.1.length = L0 + 16 * p.2.val ∧
      bytes p.1.val = S0 ++ (List.range p.2.val).flatMap
        (forsAuth (bytes sk.val) (bytes pk.pk_seed.val) (adrsS a) i.val idx.val))
  · rintro ⟨sig, j⟩ ⟨hj, hlen, hinv⟩
    simp only [fors.fors_sign_loop0_loop0.body]
    simp only at hj hlen hinv
    by_cases hjA : j < params.A
    · simp only [hjA, ↓reduceIte]
      have hjlt : j.val < 12 := by scalar_tac
      obtain ⟨ha1, ha2, ha3⟩ := fors_inner_arith i.val idx.val j.val hi hidx hjlt
      step as ⟨i1, i1_post⟩
      step as ⟨s, s_post⟩
      step as ⟨i2, i2_post⟩
      step as ⟨i3, i3_post⟩
      have hs : s.val = (idx.val / 2 ^ j.val) ^^^ 1 := by
        rw [s_post, UScalar.val_xor, i1_post, Nat.shiftRight_eq_div_pow]; rfl
      have hi3 : i3.val = i.val * 2 ^ (12 - j.val) := by
        rw [i3_post, i2_post]; simpa [U32.size, U32.numBits] using ha1
      step as ⟨i4, i4_post⟩
      have hi4 : i4.val = i.val * 2 ^ (12 - j.val) + ((idx.val / 2 ^ j.val) ^^^ 1) := by
        rw [i4_post, hi3, hs]
      step as ⟨node, node_post⟩
      step*
      refine ⟨by scalar_tac, ?_, ?_, by scalar_tac⟩
      · have : sig1.length = sig.length + 16 := by
          simp [alloc.vec.Vec.length, sig1_post, s1_post]
        scalar_tac
      · rw [sig1_post, bytes_append, hinv, j1_post, List.range_succ, List.flatMap_append]
        simp [forsAuth, s1_post, node_post, hi4, Spec.a]
    · simp only [hjA, ↓reduceIte]
      have hj12 : j.val = 12 := by scalar_tac
      rw [hj12] at hlen hinv
      simp [hlen, hinv]
  · exact ⟨hj, hlen, hinv⟩

/-- The part of a FORS signature for tree `i`: the secret value and its authentication path. -/
def forsSignTree (sk pk : Spec.Bytes) (adrs : Spec.Adrs) (ind : List Nat) (i : Nat) : Spec.Bytes :=
  Spec.forsSkGen sk pk adrs (i * 2 ^ Spec.a + ind[i]!) ++
    (List.range Spec.a).flatMap (forsAuth sk pk adrs i ind[i]!)

theorem forsSign_eq (md sk pk : Spec.Bytes) (adrs : Spec.Adrs) :
    Spec.forsSign md sk pk adrs =
      (List.range 14).flatMap (forsSignTree sk pk adrs (Spec.base2b md 12 14)) := by
  rfl

theorem fors_flatMap_range_succ {β} (f : Nat → List β) (n : Nat) :
    (List.range (n + 1)).flatMap f = (List.range n).flatMap f ++ f n := by
  rw [List.range_succ, List.flatMap_append]; simp

theorem fors_nats_getElem! (l : List U32) (i : Nat) (h : i < l.length) :
    (nats l)[i]! = (l[i]'h).val := by
  simp [nats, h]

theorem fors_sign_loop_spec (sk : Array U8 16#usize) (pk : hash.Seed) (hpk : SeedOk pk) (a : address.Adrs)
    (indices : alloc.vec.Vec U32) (sig : alloc.vec.Vec U8) (i : U32)
    (hlenI : indices.length = 14) (hbd : ∀ d ∈ indices.val, d.val < 2 ^ 12)
    (hi : i.val ≤ 14) (hlen : sig.length = 208 * i.val)
    (hinv : bytes sig.val = (List.range i.val).flatMap
      (forsSignTree (bytes sk.val) (bytes pk.pk_seed.val) (adrsS a) (nats indices.val))) :
    fors.fors_sign_loop0 sk pk a indices sig i ⦃ r =>
      r.length = 2912 ∧
      bytes r.val = (List.range 14).flatMap
        (forsSignTree (bytes sk.val) (bytes pk.pk_seed.val) (adrsS a) (nats indices.val)) ⦄ := by
  unfold fors.fors_sign_loop0
  apply loop.spec_decr_nat
    (measure := fun (p : alloc.vec.Vec U8 × U32) => 14 - p.2.val)
    (inv := fun p => p.2.val ≤ 14 ∧ p.1.length = 208 * p.2.val ∧
      bytes p.1.val = (List.range p.2.val).flatMap
        (forsSignTree (bytes sk.val) (bytes pk.pk_seed.val) (adrsS a) (nats indices.val)))
  · rintro ⟨sig, i⟩ ⟨hi, hlen, hinv⟩
    simp only [fors.fors_sign_loop0.body]
    simp only at hi hlen hinv
    by_cases hiK : i < params.K
    · simp only [hiK, ↓reduceIte]
      have hilt : i.val < 14 := by scalar_tac
      step as ⟨i1, i1_post⟩
      step as ⟨idx, idx_post⟩
      have hi1 : i1.val = i.val := by rw [i1_post]; simp
      have hidx : idx.val < 2 ^ 12 := by rw [idx_post]; exact hbd _ (List.getElem_mem _)
      have hind : (nats indices.val)[i.val]! = idx.val := by
        rw [fors_nats_getElem! _ _ (by scalar_tac)]; simp [idx_post, hi1]
      step as ⟨i2, i2_post⟩
      have hi2 : i2.val = i.val * 2 ^ 12 := by
        rw [i2_post]; simp only [fors_A_eq, U32.size, U32.numBits]
        rw [Nat.shiftLeft_eq]; exact Nat.mod_eq_of_lt (by scalar_tac)
      step as ⟨i3, i3_post⟩
      step as ⟨sk1, sk1_post⟩
      step as ⟨s, s_post⟩
      step as ⟨sig1, sig1_post⟩
      have hl1 : sig1.length = sig.length + 16 := by
        simp [alloc.vec.Vec.length, sig1_post, s_post]
      step with fors_sign_inner_spec sk pk hpk a sig1 i idx 0#u32 (bytes sig1.val) sig1.length hilt hidx
        (by simp) (by scalar_tac) (by simp) (by simp) as ⟨sig2, sig2_len, sig2_post⟩
      step*
      refine ⟨by scalar_tac, by scalar_tac, ?_, by scalar_tac⟩
      rw [sig2_post, sig1_post, bytes_append, hinv, i4_post, fors_flatMap_range_succ _ i.val]
      simp [forsSignTree, hind, s_post, sk1_post, i3_post, hi2, Spec.a]
    · simp only [hiK, ↓reduceIte]
      have hi14 : i.val = 14 := by scalar_tac
      rw [hi14] at hlen hinv
      simp [hlen, hinv]
  · exact ⟨hi, hlen, hinv⟩

@[step]
theorem fors_sign_spec (md : Slice U8) (sk : Array U8 16#usize) (pk : hash.Seed) (hpk : SeedOk pk) (a : address.Adrs) (hmd : md.length = 21) :
    fors.fors_sign md sk pk a ⦃ r =>
      bytes r.val = Spec.forsSign (bytes md.val) (bytes sk.val) (bytes pk.pk_seed.val) (adrsS a) ∧
      r.length = 2912 ⦄ := by
  unfold fors.fors_sign
  step as ⟨i, i_post⟩
  have hi : i.val = 14 := by rw [i_post]; simp
  step with base_2b_spec md params.A i (by simp) (by simp [hi, hmd]) as ⟨indices, hind, hlenI, hbd⟩
  simp only [fors_A_eq, hi] at hind hlenI hbd
  apply WP.spec_mono
  · exact fors_sign_loop_spec sk pk hpk a indices (alloc.vec.Vec.new U8) 0#u32 (by simpa using hlenI)
      (by simpa using hbd) (by simp) (by simp) (by simp)
  · intro r ⟨h1, h2⟩
    refine ⟨?_, h1⟩
    rw [forsSign_eq, h2, hind]; rfl

/-- The root of FORS tree `i` recomputed from a signature (Algorithm 17, lines 3–20). -/
def forsRoot (sig pk : Spec.Bytes) (adrs : Spec.Adrs) (ind : List Nat) (i : Nat) : Spec.Bytes :=
  Spec.climb
    (Spec.F pk { adrs with word2 := 0, word3 := i * 2 ^ Spec.a + ind[i]! }
      (Spec.block sig (i * (Spec.a + 1))))
    ind[i]! (i * 2 ^ Spec.a + ind[i]!)
    ((sig.drop ((i * (Spec.a + 1) + 1) * Spec.n)).take (Spec.a * Spec.n)) Spec.a pk adrs

theorem forsPkFromSig_eq (sig md pk : Spec.Bytes) (adrs : Spec.Adrs) :
    Spec.forsPkFromSig sig md pk adrs =
      Spec.T pk { adrs.setTypeAndClear Spec.FORS_ROOTS with keypair := adrs.keypair }
        ((List.range 14).flatMap (forsRoot sig pk adrs (Spec.base2b md 12 14))) := by
  rfl

/-! `fors_pkFromSig`: the `K` trees climbed together. -/

/-- The leaf index of FORS tree `t`. -/
def forsLeaf (ind : List Nat) (t : Nat) : Nat := t * 2 ^ 12 + ind[t]!

theorem fors_pk_from_sig_loop0_spec (sig : Slice U8) (adrs : address.Adrs)
    (indices : alloc.vec.Vec U32) (hs : sig.length = 2912)
    (hlenI : indices.length = 14) (hbd : ∀ d ∈ indices.val, d.val < 2 ^ 12)
    (blocks : Array (Array U8 64#usize) 14#usize) (idx «end» : Array U32 14#usize) (i : Usize)
    (hi : i.val ≤ 14)
    (hinv : ∀ t, t < i.val →
      bytes (blocks.val[t]!).val = padFrom 64 ({ adrsS adrs with word2 := 0, word3 := forsLeaf (nats indices.val) t }.compress ++ Spec.block (bytes sig.val) (t * 13)) ∧
      (idx.val[t]!).val = forsLeaf (nats indices.val) t ∧
      («end».val[t]!).val = forsLeaf (nats indices.val) t + 1) :
    fors.fors_pk_from_sig_loop0 sig adrs indices blocks idx «end» i ⦃ r =>
      ∀ t, t < 14 →
        bytes (r.1.val[t]!).val = padFrom 64 ({ adrsS adrs with word2 := 0, word3 := forsLeaf (nats indices.val) t }.compress ++ Spec.block (bytes sig.val) (t * 13)) ∧
        (r.2.1.val[t]!).val = forsLeaf (nats indices.val) t ∧
        (r.2.2.val[t]!).val = forsLeaf (nats indices.val) t + 1 ⦄ := by
  unfold fors.fors_pk_from_sig_loop0
  apply loop.spec_decr_nat
    (measure := fun (p : Array (Array U8 64#usize) 14#usize × Array U32 14#usize ×
      Array U32 14#usize × Usize) => 14 - p.2.2.2.val)
    (inv := fun p => p.2.2.2.val ≤ 14 ∧ ∀ t, t < p.2.2.2.val →
      bytes (p.1.val[t]!).val = padFrom 64 ({ adrsS adrs with word2 := 0, word3 := forsLeaf (nats indices.val) t }.compress ++ Spec.block (bytes sig.val) (t * 13)) ∧
      (p.2.1.val[t]!).val = forsLeaf (nats indices.val) t ∧
      (p.2.2.1.val[t]!).val = forsLeaf (nats indices.val) t + 1)
  · rintro ⟨blocks, idx, «end», i⟩ ⟨h1, h2⟩
    simp only [fors.fors_pk_from_sig_loop0.body, fors_A_eq, fors_K_eq]
    simp only at h1 h2
    step as ⟨i1, i1_post⟩
    have hi1 : i1.val = 14 := by rw [i1_post]; simp
    split
    · have hil : i.val < 14 := by scalar_tac
      step as ⟨i2, i2_post⟩
      have hi2 : i2.val = i.val := by rw [i2_post]; simp; scalar_tac
      step as ⟨i3, i3_post, i3_post1⟩
      have hi3 : i3.val = i.val * 2 ^ 12 := by
        rw [i3_post, hi2, Nat.shiftLeft_eq]
        exact Nat.mod_eq_of_lt (by simp [U32.size, U32.numBits]; omega)
      step as ⟨i4, i4_post⟩
      have hi4 : i4.val < 2 ^ 12 := by rw [i4_post]; exact hbd _ (List.getElem_mem _)
      have hind : (nats indices.val)[i.val]! = i4.val := by
        rw [fors_nats_getElem! _ _ (by scalar_tac)]; simp [i4_post]
      have hleafv : i3.val + i4.val = forsLeaf (nats indices.val) i.val := by
        rw [hi3, forsLeaf, hind]
      step*
      have hleaf : leaf.val = forsLeaf (nats indices.val) i.val := by rw [leaf_post, hleafv]
      have hi7 : i7.val = i.val * 13 := by rw [i7_post, i6_post, i5_post]; simp
      refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      intro t ht
      rw [i9_post] at ht
      rw [a3_post, a4_post, a5_post, Array.set_val_eq, Array.set_val_eq, Array.set_val_eq]
      rcases Nat.lt_succ_iff_lt_or_eq.mp ht with ht | ht
      · rw [getElem!_set_ne' _ _ _ _ (by omega), getElem!_set_ne' _ _ _ _ (by omega),
          getElem!_set_ne' _ _ _ _ (by omega)]
        exact h2 t ht
      · subst ht
        rw [getElem!_set_self' _ _ _ (by simp; omega), getElem!_set_self' _ _ _ (by simp; omega),
          getElem!_set_self' _ _ _ (by simp; omega)]
        refine ⟨?_, hleaf, by rw [i8_post, hleaf]⟩
        rw [a2_post, s_post, Array.val_to_slice, sk_post1, hi7, a1_post, a_post]
        simp [adrsS, hleaf]
    · simp only [step_simps]
      have : i.val = 14 := by scalar_tac
      rw [this] at h2; exact h2
  · exact ⟨hi, hinv⟩

theorem fors_pk_from_sig_loop1_spec (blocks : Array (Array U8 64#usize) 14#usize)
    (vals : Array (Array U8 16#usize) 14#usize) (i : Usize) (hi : i.val ≤ 14)
    (hinv : ∀ (t : Nat), t < i.val → bytes (vals.val[t]!).val = blkVal blocks.val[t]!) :
    fors.fors_pk_from_sig_loop1 blocks vals i ⦃ r =>
      ∀ (t : Nat), t < 14 → bytes (r.val[t]!).val = blkVal blocks.val[t]! ⦄ := by
  unfold fors.fors_pk_from_sig_loop1
  apply loop.spec_decr_nat
    (measure := fun (p : Array (Array U8 16#usize) 14#usize × Usize) => 14 - p.2.val)
    (inv := fun p => p.2.val ≤ 14 ∧
      ∀ (t : Nat), t < p.2.val → bytes (p.1.val[t]!).val = blkVal blocks.val[t]!)
  · rintro ⟨vals, i⟩ ⟨h1, h2⟩
    simp only [fors.fors_pk_from_sig_loop1.body, fors_K_eq]
    simp only at h1 h2
    step*
    · refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      rw [i2_post, a2_post, Array.set_val_eq]
      refine forall_set_succ vals.val i.val a1 (fun t (b : Array U8 16#usize) =>
        bytes b.val = blkVal blocks.val[t]!) (by simp; scalar_tac) h2 ?_
      rw [a1_post, a_post, ← getElem!_eq _ _ (by simp; scalar_tac)]
      rfl
  · exact ⟨hi, hinv⟩

theorem fors_pk_from_sig_loop2_loop1_spec (blocks : Array (Array U8 64#usize) 14#usize)
    (vals : Array (Array U8 16#usize) 14#usize) (i : Usize) (hi : i.val ≤ 14)
    (hinv : ∀ (t : Nat), t < i.val → bytes (vals.val[t]!).val = blkVal blocks.val[t]!) :
    fors.fors_pk_from_sig_loop2_loop1 blocks vals i ⦃ r =>
      ∀ (t : Nat), t < 14 → bytes (r.val[t]!).val = blkVal blocks.val[t]! ⦄ := by
  unfold fors.fors_pk_from_sig_loop2_loop1
  apply loop.spec_decr_nat
    (measure := fun (p : Array (Array U8 16#usize) 14#usize × Usize) => 14 - p.2.val)
    (inv := fun p => p.2.val ≤ 14 ∧
      ∀ (t : Nat), t < p.2.val → bytes (p.1.val[t]!).val = blkVal blocks.val[t]!)
  · rintro ⟨vals, i⟩ ⟨h1, h2⟩
    simp only [fors.fors_pk_from_sig_loop2_loop1.body, fors_K_eq]
    simp only at h1 h2
    step*
    · refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      rw [i2_post, a2_post, Array.set_val_eq]
      refine forall_set_succ vals.val i.val a1 (fun t (b : Array U8 16#usize) =>
        bytes b.val = blkVal blocks.val[t]!) (by simp; scalar_tac) h2 ?_
      rw [a1_post, a_post, ← getElem!_eq _ _ (by simp; scalar_tac)]
      rfl
  · exact ⟨hi, hinv⟩

theorem fors_pk_from_sig_loop3_spec (vals : Array (Array U8 16#usize) 14#usize)
    (roots : alloc.vec.Vec U8) (i : Usize) (hi : i.val ≤ 14) (hlen : roots.length = 16 * i.val)
    (hinv : bytes roots.val = (List.range i.val).flatMap (fun (t : Nat) => bytes (vals.val[t]!).val)) :
    fors.fors_pk_from_sig_loop3 vals roots i ⦃ r =>
      bytes r.val = (List.range 14).flatMap (fun (t : Nat) => bytes (vals.val[t]!).val) ∧
      r.length = 224 ⦄ := by
  unfold fors.fors_pk_from_sig_loop3
  apply loop.spec_decr_nat (measure := fun (p : alloc.vec.Vec U8 × Usize) => 14 - p.2.val)
    (inv := fun p => p.2.val ≤ 14 ∧ p.1.length = 16 * p.2.val ∧
      bytes p.1.val = (List.range p.2.val).flatMap (fun (t : Nat) => bytes (vals.val[t]!).val))
  · rintro ⟨roots, i⟩ ⟨h1, h2, h3⟩
    simp only [fors.fors_pk_from_sig_loop3.body, fors_K_eq]
    simp only at h1 h2 h3
    step*
    · refine ⟨by scalar_tac, ?_, ?_, by scalar_tac⟩
      · have : roots1.length = roots.length + 16 := by
          simp [alloc.vec.Vec.length, roots1_post, s_post]
        scalar_tac
      · rw [roots1_post, bytes_append, h3, i2_post, fors_flatMap_range_succ _ i.val]
        simp [s_post, a_post, getElem!_eq _ _ (show i.val < vals.val.length by simp; scalar_tac)]
  · exact ⟨hi, hlen, hinv⟩

/-- The message of an inner FORS node: the node and its sibling, in the order
given by the parity of the node's index. -/
def pairMsg (v sib : Spec.Bytes) (x : Nat) : Spec.Bytes := if x % 2 = 0 then v ++ sib else sib ++ v

theorem pairMsg_even (v sib : Spec.Bytes) (x : Nat) (h : x % 2 = 0) : pairMsg v sib x = v ++ sib := by
  simp [pairMsg, h]

theorem pairMsg_odd (v sib : Spec.Bytes) (x : Nat) (h : ¬ x % 2 = 0) : pairMsg v sib x = sib ++ v := by
  simp [pairMsg, h]

theorem fors_pk_from_sig_loop2_loop0_spec (sig : Slice U8) (adrs : address.Adrs)
    (vals : Array (Array U8 16#usize) 14#usize) (k : U32) (hk : k.val < 12) (hs : sig.length = 2912)
    (idx0 : Array U32 14#usize)
    (blocks : Array (Array U8 64#usize) 14#usize) (idx «end» : Array U32 14#usize) (i : Usize)
    (hi : i.val ≤ 14)
    (hdone : ∀ t, t < i.val →
      bytes (blocks.val[t]!).val = padFrom 64 ({ adrsS adrs with word2 := k.val + 1, word3 := (idx0.val[t]!).val / 2 }.compress ++
        pairMsg (bytes (vals.val[t]!).val) (Spec.block (bytes sig.val) (t * 13 + 1 + k.val)) (idx0.val[t]!).val) ∧
      (idx.val[t]!).val = (idx0.val[t]!).val / 2 ∧ («end».val[t]!).val = (idx0.val[t]!).val / 2 + 1)
    (hrest : ∀ t, i.val ≤ t → idx.val[t]! = idx0.val[t]!) :
    fors.fors_pk_from_sig_loop2_loop0 sig adrs blocks idx «end» vals k i ⦃ r =>
      ∀ t, t < 14 →
        bytes (r.1.val[t]!).val = padFrom 64 ({ adrsS adrs with word2 := k.val + 1, word3 := (idx0.val[t]!).val / 2 }.compress ++
          pairMsg (bytes (vals.val[t]!).val) (Spec.block (bytes sig.val) (t * 13 + 1 + k.val)) (idx0.val[t]!).val) ∧
        (r.2.1.val[t]!).val = (idx0.val[t]!).val / 2 ∧ (r.2.2.val[t]!).val = (idx0.val[t]!).val / 2 + 1 ⦄ := by
  unfold fors.fors_pk_from_sig_loop2_loop0
  apply loop.spec_decr_nat
    (measure := fun (p : Array (Array U8 64#usize) 14#usize × Array U32 14#usize ×
      Array U32 14#usize × Usize) => 14 - p.2.2.2.val)
    (inv := fun p => p.2.2.2.val ≤ 14 ∧ (∀ t, t < p.2.2.2.val →
      bytes (p.1.val[t]!).val = padFrom 64 ({ adrsS adrs with word2 := k.val + 1, word3 := (idx0.val[t]!).val / 2 }.compress ++
        pairMsg (bytes (vals.val[t]!).val) (Spec.block (bytes sig.val) (t * 13 + 1 + k.val)) (idx0.val[t]!).val) ∧
      (p.2.1.val[t]!).val = (idx0.val[t]!).val / 2 ∧ (p.2.2.1.val[t]!).val = (idx0.val[t]!).val / 2 + 1) ∧
      (∀ t, p.2.2.2.val ≤ t → p.2.1.val[t]! = idx0.val[t]!))
  · rintro ⟨blocks, idx, «end», i⟩ ⟨h1, h2, h3⟩
    simp only [fors.fors_pk_from_sig_loop2_loop0.body, fors_A_eq, fors_K_eq]
    simp only at h1 h2 h3
    step as ⟨i1, i1_post⟩
    split
    · have hil : i.val < 14 := by scalar_tac
      step*
      have hi7 : i7.val = i.val * 13 + 1 + k.val := by
        rw [i7_post, i5_post, i4_post, i3_post, i2_post, i6_post]; simp
      have hil' : i.val < idx.val.length := by simp; omega
      have hi8 : i8 = idx0.val[i.val]! := by
        rw [i8_post, ← getElem!_eq _ _ hil', h3 _ (le_refl _)]
      have hpar : parent.val = (idx0.val[i.val]!).val / 2 := by
        rw [parent_post, ← hi8]; simp [Nat.shiftRight_eq_div_pow]
      have hi10 : i10.val = (idx0.val[i.val]!).val % 2 := by
        rw [i10_post, ← hi8]; simp [Nat.and_one_is_mod]
      have hadrs : adrsS a1 = { adrsS adrs with word2 := k.val + 1, word3 := parent.val } := by
        simp [adrsS, a1_post, a_post, i9_post]
      have hsib : bytes sibling.val = Spec.block (bytes sig.val) (i.val * 13 + 1 + k.val) := by
        rw [sibling_post1, hi7]
      have hvl : i.val < vals.val.length := by simp; omega
      by_cases hc : i10 = 0#u32
      · simp only [hc, ↓reduceIte]
        have hev : (idx0.val[i.val]!).val % 2 = 0 := by rw [← hi10, hc]; rfl
        let* ⟨ v, v_post ⟩ ← Array.index_usize_spec
        let* ⟨ pb, pb_post ⟩ ← pair_block_spec
        let* ⟨ b1, b1_post ⟩ ← Array.update_spec
        step*
        refine ⟨by scalar_tac, ?_, ?_, by scalar_tac⟩
        · intro t ht
          rw [i12_post] at ht
          rw [b1_post, a2_post, a3_post, Array.set_val_eq, Array.set_val_eq, Array.set_val_eq]
          rcases Nat.lt_succ_iff_lt_or_eq.mp ht with ht | ht
          · rw [getElem!_set_ne' _ _ _ _ (by omega), getElem!_set_ne' _ _ _ _ (by omega),
              getElem!_set_ne' _ _ _ _ (by omega)]
            exact h2 t ht
          · subst ht
            rw [getElem!_set_self' _ _ _ (by simp; omega), getElem!_set_self' _ _ _ (by simp; omega),
              getElem!_set_self' _ _ _ (by simp; omega)]
            refine ⟨?_, hpar, by rw [i11_post, hpar]⟩
            rw [pb_post, hadrs, hpar, v_post, ← getElem!_eq _ _ hvl, hsib, pairMsg_even _ _ _ hev]
        · intro t ht
          rw [a2_post, Array.set_val_eq, getElem!_set_ne' _ _ _ _ (by scalar_tac)]
          exact h3 t (by scalar_tac)
      · simp only [hc, ↓reduceIte]
        have hod : ¬ (idx0.val[i.val]!).val % 2 = 0 := by
          rw [← hi10]; intro h0; apply hc; scalar_tac
        let* ⟨ v, v_post ⟩ ← Array.index_usize_spec
        let* ⟨ pb, pb_post ⟩ ← pair_block_spec
        let* ⟨ b1, b1_post ⟩ ← Array.update_spec
        step*
        refine ⟨by scalar_tac, ?_, ?_, by scalar_tac⟩
        · intro t ht
          rw [i12_post] at ht
          rw [b1_post, a2_post, a3_post, Array.set_val_eq, Array.set_val_eq, Array.set_val_eq]
          rcases Nat.lt_succ_iff_lt_or_eq.mp ht with ht | ht
          · rw [getElem!_set_ne' _ _ _ _ (by omega), getElem!_set_ne' _ _ _ _ (by omega),
              getElem!_set_ne' _ _ _ _ (by omega)]
            exact h2 t ht
          · subst ht
            rw [getElem!_set_self' _ _ _ (by simp; omega), getElem!_set_self' _ _ _ (by simp; omega),
              getElem!_set_self' _ _ _ (by simp; omega)]
            refine ⟨?_, hpar, by rw [i11_post, hpar]⟩
            rw [pb_post, hadrs, hpar, v_post, ← getElem!_eq _ _ hvl, hsib, pairMsg_odd _ _ _ hod]
        · intro t ht
          rw [a2_post, Array.set_val_eq, getElem!_set_ne' _ _ _ _ (by scalar_tac)]
          exact h3 t (by scalar_tac)
    · simp only [step_simps]
      have : i.val = 14 := by scalar_tac
      rw [this] at h2; exact h2
  · exact ⟨hi, hdone, hrest⟩

/-- One level of `Spec.climb`. -/
def forsClimbStep (leaf : Nat) (auth pk : Spec.Bytes) (adrs : Spec.Adrs)
    (st : Spec.Bytes × Nat) (j : Nat) : Spec.Bytes × Nat :=
  if (leaf / 2 ^ j) % 2 = 0 then
    (Spec.H pk { adrs with word2 := j + 1, word3 := st.2 / 2 } (st.1 ++ Spec.block auth j), st.2 / 2)
  else
    (Spec.H pk { adrs with word2 := j + 1, word3 := (st.2 - 1) / 2 } (Spec.block auth j ++ st.1),
      (st.2 - 1) / 2)

theorem fors_climb_eq (node : Spec.Bytes) (leaf ti : Nat) (auth : Spec.Bytes) (height : Nat)
    (pk : Spec.Bytes) (adrs : Spec.Adrs) :
    Spec.climb node leaf ti auth height pk adrs =
      ((List.range height).foldl (forsClimbStep leaf auth pk adrs) (node, ti)).1 := by
  unfold Spec.climb
  congr 2

/-- The authentication path of FORS tree `t` in a signature. -/
def forsAuthPath (sig : Spec.Bytes) (t : Nat) : Spec.Bytes :=
  (sig.drop ((t * (Spec.a + 1) + 1) * Spec.n)).take (Spec.a * Spec.n)

/-- Tree `t` of `fors_pkFromSig` after climbing `k` levels: the node and its tree index. -/
def forsClimbAt (sig pk : Spec.Bytes) (adrs : Spec.Adrs) (ind : List Nat) (t k : Nat) : Spec.Bytes × Nat :=
  (List.range k).foldl (forsClimbStep ind[t]! (forsAuthPath sig t) pk adrs)
    (Spec.F pk { adrs with word2 := 0, word3 := forsLeaf ind t } (Spec.block sig (t * (Spec.a + 1))),
      forsLeaf ind t)

theorem fors_block_auth (s : Spec.Bytes) (t k : Nat) (hk : k < 12) :
    Spec.block (forsAuthPath s t) k = Spec.block s (t * 13 + 1 + k) := by
  simp only [forsAuthPath, Spec.block, Spec.n, Spec.a, List.drop_take, List.take_take, List.drop_drop]
  have h1 : min 16 (12 * 16 - k * 16) = 16 := by omega
  have h2 : (t * (12 + 1) + 1) * 16 + k * 16 = (t * 13 + 1 + k) * 16 := by ring
  rw [h1, h2]

theorem fors_pk_from_sig_loop2_spec (sig : Slice U8) (pk : hash.Seed) (hpk : SeedOk pk)
    (adrs : address.Adrs) (ind : List Nat) (hs : sig.length = 2912)
    (blocks : Array (Array U8 64#usize) 14#usize) (idx «end» : Array U32 14#usize)
    (vals : Array (Array U8 16#usize) 14#usize) (k : U32) (hk : k.val ≤ 12)
    (hinv : ∀ t, t < 14 →
      bytes (vals.val[t]!).val = (forsClimbAt (bytes sig.val) (bytes pk.pk_seed.val) (adrsS adrs) ind t k.val).1 ∧
      (idx.val[t]!).val = (forsClimbAt (bytes sig.val) (bytes pk.pk_seed.val) (adrsS adrs) ind t k.val).2 ∧
      (idx.val[t]!).val = t * 2 ^ (12 - k.val) + ind[t]! / 2 ^ k.val) :
    fors.fors_pk_from_sig_loop2 sig pk.state adrs blocks idx «end» vals k ⦃ r =>
      ∀ t, t < 14 →
        bytes (r.val[t]!).val = (forsClimbAt (bytes sig.val) (bytes pk.pk_seed.val) (adrsS adrs) ind t 12).1 ⦄ := by
  unfold fors.fors_pk_from_sig_loop2
  apply loop.spec_decr_nat
    (measure := fun (p : Array (Array U8 64#usize) 14#usize × Array U32 14#usize ×
      Array U32 14#usize × Array (Array U8 16#usize) 14#usize × U32) => 12 - p.2.2.2.2.val)
    (inv := fun p => p.2.2.2.2.val ≤ 12 ∧ ∀ t, t < 14 →
      bytes (p.2.2.2.1.val[t]!).val =
        (forsClimbAt (bytes sig.val) (bytes pk.pk_seed.val) (adrsS adrs) ind t p.2.2.2.2.val).1 ∧
      (p.2.1.val[t]!).val = (forsClimbAt (bytes sig.val) (bytes pk.pk_seed.val) (adrsS adrs) ind t p.2.2.2.2.val).2 ∧
      (p.2.1.val[t]!).val = t * 2 ^ (12 - p.2.2.2.2.val) + ind[t]! / 2 ^ p.2.2.2.2.val)
  · rintro ⟨blocks, idx, «end», vals, k⟩ ⟨h1, h2⟩
    simp only [fors.fors_pk_from_sig_loop2.body, fors_A_eq]
    simp only at h1 h2
    simp only [step_simps]
    spec_split
    · have hk12 : k.val < 12 := by scalar_tac
      let* ⟨ blocks1, idx1, end1, hQ ⟩ ← fors_pk_from_sig_loop2_loop0_spec sig adrs vals k hk12 hs idx
        blocks idx «end» 0#usize (by simp) (by simp) (fun _ _ => rfl)
      step*
      have hsl : s.length = 14 := by simp [s_post]
      have hb2 : (to_slice_mut_back s3).val = s3.val := by
        rw [to_slice_mut_back_post]; exact Array.from_slice_val _ _ (by simp [s3_post, s_post])
      let* ⟨ vals1, vals1_post ⟩ ← fors_pk_from_sig_loop2_loop1_spec (to_slice_mut_back s3) vals
        0#usize (by simp) (by simp)
      let* ⟨ k1, k1_post ⟩ ← U32.add_spec
      refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      intro t ht
      obtain ⟨hv, hti, hcl⟩ := h2 t ht
      obtain ⟨hb, hi1, he1⟩ := hQ t ht
      have hpkl : (bytes pk.pk_seed.val).length = 16 := by simp
      have hpw : 2 ^ (12 - k.val) = 2 * 2 ^ (12 - (k.val + 1)) := by
        rw [← pow_succ']; congr 1; omega
      have hidx' : (idx.val[t]!).val = 2 * (t * 2 ^ (12 - (k.val + 1))) + ind[t]! / 2 ^ k.val := by
        rw [hcl, hpw]; ring
      have hmod : (idx.val[t]!).val % 2 = (ind[t]! / 2 ^ k.val) % 2 := by rw [hidx']; omega
      have hdiv : (idx.val[t]!).val / 2 = t * 2 ^ (12 - (k.val + 1)) + ind[t]! / 2 ^ (k.val + 1) := by
        rw [hidx', pow_succ, ← Nat.div_div_eq_div_mul]; omega
      have hval : bytes (vals1.val[t]!).val = Spec.thash (bytes pk.pk_seed.val)
          { adrsS adrs with word2 := k.val + 1, word3 := (idx.val[t]!).val / 2 }
          (pairMsg (bytes (vals.val[t]!).val) (Spec.block (bytes sig.val) (t * 13 + 1 + k.val))
            (idx.val[t]!).val) := by
        rw [vals1_post t ht, blkVal, hb2, s3_post1 t (by omega), s_post, s1_post, s2_post,
          Array.val_to_slice, Array.val_to_slice, hi1, he1, runBlock_one, hb]
        refine stepBlock_pair_value _ hpkl _ hpk _ _ ?_
        unfold pairMsg; split <;> simp [block_length _ _ (show (t * 13 + 1 + k.val + 1) * 16 ≤ (bytes sig.val).length by simp; scalar_tac)]
      have hstep : forsClimbAt (bytes sig.val) (bytes pk.pk_seed.val) (adrsS adrs) ind t (k.val + 1) =
          forsClimbStep ind[t]! (forsAuthPath (bytes sig.val) t) (bytes pk.pk_seed.val) (adrsS adrs)
            (forsClimbAt (bytes sig.val) (bytes pk.pk_seed.val) (adrsS adrs) ind t k.val) k.val := by
        simp only [forsClimbAt, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [k1_post, hstep]
      by_cases hpar : (ind[t]! / 2 ^ k.val) % 2 = 0
      · simp only [forsClimbStep, hpar, ↓reduceIte]
        refine ⟨?_, ?_, ?_⟩
        · rw [hval, pairMsg_even _ _ _ (by omega), hv, ← hti, fors_block_auth _ _ _ hk12]; rfl
        · rw [hi1, hti]
        · rw [hi1, hdiv]
      · simp only [forsClimbStep, hpar, ↓reduceIte]
        have hsub : ((idx.val[t]!).val - 1) / 2 = (idx.val[t]!).val / 2 := by omega
        refine ⟨?_, ?_, ?_⟩
        · rw [hval, pairMsg_odd _ _ _ (by omega), hv, ← hti, hsub, fors_block_auth _ _ _ hk12]; rfl
        · rw [hi1, ← hti, hsub]
        · rw [hi1, hdiv]
    · simp only [step_simps]
      have : k.val = 12 := by scalar_tac
      intro t ht
      rw [← this]; exact (h2 t ht).1
  · exact ⟨hk, hinv⟩

theorem forsRoot_eq (sig pk : Spec.Bytes) (adrs : Spec.Adrs) (ind : List Nat) (t : Nat) :
    forsRoot sig pk adrs ind t = (forsClimbAt sig pk adrs ind t 12).1 := by
  rw [forsRoot, fors_climb_eq]; rfl

@[step]
theorem fors_pk_from_sig_spec (sig md : Slice U8) (pk : hash.Seed) (hpk : SeedOk pk) (a : address.Adrs)
    (hs : sig.length = 2912) (hmd : md.length = 21) :
    fors.fors_pk_from_sig sig md pk a ⦃ r =>
      bytes r.val = Spec.forsPkFromSig (bytes sig.val) (bytes md.val) (bytes pk.pk_seed.val) (adrsS a) ⦄ := by
  unfold fors.fors_pk_from_sig
  step as ⟨i, i_post⟩
  have hi : i.val = 14 := by rw [i_post]; simp
  step with base_2b_spec md params.A i (by simp) (by simp [hi, hmd]) as ⟨indices, hind, hlenI, hbd⟩
  simp only [fors_A_eq, hi] at hind hlenI hbd
  let* ⟨ blocks1, idx1, end1, hL ⟩ ← fors_pk_from_sig_loop0_spec sig a indices hs
    (by simpa using hlenI) (by simpa using hbd) _ _ _ 0#usize (by simp) (by simp)
  let* ⟨ s, back, s_post, back_post ⟩ ← Array.to_slice_mut_spec
  let* ⟨ s1, s1_post ⟩ ← Array.to_slice.step_spec
  let* ⟨ s2, s2_post ⟩ ← Array.to_slice.step_spec
  let* ⟨ s3, s3_len, s3_post ⟩ ← chain_blocks_spec
  have hsl : s.length = 14 := by simp [s_post]
  have hb2 : (back s3).val = s3.val := by
    rw [back_post]; exact Array.from_slice_val _ _ (by simp [s3_len, s_post])
  let* ⟨ vals1, vals1_post ⟩ ← fors_pk_from_sig_loop1_spec (back s3)
    (Array.repeat 14#usize (Array.repeat 16#usize 0#u8)) 0#usize (by simp) (by simp)
  have hpkl : (bytes pk.pk_seed.val).length = 16 := by simp
  have h0 : ∀ t, t < 14 →
      bytes (vals1.val[t]!).val = (forsClimbAt (bytes sig.val) (bytes pk.pk_seed.val) (adrsS a)
        (nats indices.val) t (0#u32).val).1 ∧
      (idx1.val[t]!).val = (forsClimbAt (bytes sig.val) (bytes pk.pk_seed.val) (adrsS a)
        (nats indices.val) t (0#u32).val).2 ∧
      (idx1.val[t]!).val = t * 2 ^ (12 - (0#u32).val) + (nats indices.val)[t]! / 2 ^ (0#u32).val := by
    intro t ht
    obtain ⟨hb, hi1, he1⟩ := hL t ht
    have hbl : (Spec.block (bytes sig.val) (t * 13)).length = 16 :=
      block_length _ _ (by simp; scalar_tac)
    refine ⟨?_, ?_, ?_⟩
    · rw [vals1_post t ht, blkVal, hb2, s3_post t (by omega), s_post, s1_post, s2_post,
        Array.val_to_slice, Array.val_to_slice, hi1, he1, runBlock_one, hb,
        stepBlock_thash _ hpkl _ hpk _ _ hbl, block_value _ _ (by rw [thash_length _ hpkl]; omega),
        List.take_left' (thash_length _ hpkl _ _)]
      rfl
    · rw [hi1]; rfl
    · rw [hi1, forsLeaf]; simp
  let* ⟨ vals2, vals2_post ⟩ ← fors_pk_from_sig_loop2_spec sig pk hpk a (nats indices.val) hs
    (back s3) idx1 end1 vals1 0#u32 (by simp) h0
  let* ⟨ roots, roots_post, roots_len ⟩ ← fors_pk_from_sig_loop3_spec vals2 (alloc.vec.Vec.new U8)
    0#usize (by simp) (by simp) (by simp)
  step as ⟨a0, a0_post, a0_eq⟩
  step as ⟨a1, a1_post⟩
  step with thash_spec pk hpk a1 roots.deref (by simp [alloc.vec.Vec.deref]; scalar_tac) as ⟨r, r_post⟩
  rw [r_post, forsPkFromSig_eq]
  have hd : roots.deref.val = roots.val := by simp [alloc.vec.Vec.deref]
  have hind' : nats indices.val = Spec.base2b (bytes md.val) 12 14 := by simpa using hind
  have hroots : (List.range 14).flatMap (fun (t : Nat) => bytes (vals2.val[t]!).val) =
      (List.range 14).flatMap (forsRoot (bytes sig.val) (bytes pk.pk_seed.val) (adrsS a) (nats indices.val)) :=
    List.flatMap_congr (fun t ht => by rw [vals2_post t (List.mem_range.mp ht), forsRoot_eq])
  rw [hd, roots_post, hroots, hind']
  simp [Spec.T, adrsS, a1_post, a0_eq, Spec.Adrs.setTypeAndClear, Spec.FORS_ROOTS, fors_FORS_ROOTS_eq]

end slhdsa
