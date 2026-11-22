import Slhdsa.Proofs.Xmss
open Aeneas Aeneas.Std Result

/-! FORS (FIPS 205 §8), for any valid parameter set. Batches of up to 128
leaves; for `n = 16` the levels above the leaves are `chain_blocks` steps on
pair blocks, for `n > 16` one SHA-512 block per node. -/

namespace slhdsa

@[local simp] theorem fors_FORS_PRF_eq : address.FORS_PRF = 6#u32 := by simp [global_simps]
@[local simp] theorem fors_FORS_ROOTS_eq : address.FORS_ROOTS = 4#u32 := by simp [global_simps]

@[local step]
theorem fors_extend_from_slice_spec (v : alloc.vec.Vec U8) (s : Slice U8)
    (h : v.length + s.length ≤ Usize.max) :
    alloc.vec.Vec.extend_from_slice core.clone.CloneU8 v s ⦃ r =>
      r.val = v.val ++ s.val ∧ r.length = v.length + s.length ⦄ := by
  unfold alloc.vec.Vec.extend_from_slice
  simp only [h, ↓reduceDIte]
  apply WP.spec_bind (List.clone_spec (l := s.val) (by intros; simp [liftFun1]))
  intro l' hl'
  simp [hl']

@[step]
theorem fors_sk_gen_spec {N : Usize} (p : params.Params) (hp : PN p N) (sk : Array U8 N)
    (seed : hash.Seed N) (hs : SeedOk seed) (a : address.Adrs) (idx : U32) :
    fors.fors_sk_gen sk seed a idx ⦃ r =>
      bytes r.val = Spec.forsSkGen (paramsS p) (bytes sk.val) (bytes seed.pk_seed.val) (adrsS a)
        idx.val ⦄ := by
  unfold fors.fors_sk_gen
  have hN32 := hp.le32
  let* ⟨ a1, a1_post, a1_post1 ⟩ ← with_type_spec
  let* ⟨ a2, a2_post ⟩ ← with_keypair_spec
  let* ⟨ a3, a3_post ⟩ ← with_word3_spec
  let* ⟨ s, s_post ⟩ ← Array.to_slice.step_spec
  let* ⟨ r, r_post ⟩ ← thash_short_spec hp.nok
  rw [r_post, Spec.forsSkGen, PRF_eq, hp.n]
  simp [adrsS, Spec.Adrs.setTypeAndClear, Spec.FORS_PRF, a3_post, a2_post, a1_post1, s_post]

/-! The node at a height of at most `BATCH_HEIGHT`, computed in one batch. -/

theorem fors_batch_loop0_spec {N : Usize} (sk : Array U8 N) (hN : N.val ≤ 32) (i z : U32) (n : Usize) (prf : address.Adrs)
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

theorem fors_batch_loop2_spec {N : Usize} (hN : N.val ≤ 32) (n : Usize) (hn : n.val ≤ 128)
    (blocks : Array (Array U8 64#usize) 128#usize) (vals : Array (Array U8 N) 128#usize)
    (j : Usize) (hj : j.val ≤ n.val)
    (hinv : ∀ (k : Nat), k < j.val → bytes (vals.val[k]!).val = blkVal N.val blocks.val[k]!) :
    fors.fors_batch_loop2 n blocks vals j ⦃ r =>
      ∀ (k : Nat), k < n.val → bytes (r.val[k]!).val = blkVal N.val blocks.val[k]! ⦄ := by
  unfold fors.fors_batch_loop2
  apply loop.spec_decr_nat
    (measure := fun (p : Array (Array U8 N) 128#usize × Usize) => n.val - p.2.val)
    (inv := fun p => p.2.val ≤ n.val ∧
      ∀ (k : Nat), k < p.2.val → bytes (p.1.val[k]!).val = blkVal N.val blocks.val[k]!)
  · rintro ⟨vals, j⟩ ⟨h1, h2⟩
    simp only [fors.fors_batch_loop2.body]
    simp only at h1 h2
    step*
    · refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      rw [j1_post, a2_post, Array.set_val_eq]
      refine forall_set_succ vals.val j.val a1 (fun k (b : Array U8 N) =>
        bytes b.val = blkVal N.val blocks.val[k]!) (by simp; scalar_tac) h2 ?_
      rw [a1_post, a_post, ← getElem!_eq _ _ (by simp; scalar_tac)]
      rfl
  · exact ⟨hj, hinv⟩

theorem fors_batch_loop3_loop1_spec {N : Usize} (hN : N.val ≤ 32) (blocks : Array (Array U8 64#usize) 128#usize)
    (cnt : Usize) (hn : cnt.val ≤ 128) (vals : Array (Array U8 N) 128#usize)
    (j : Usize) (hj : j.val ≤ cnt.val)
    (hinv : ∀ (k : Nat), k < j.val → bytes (vals.val[k]!).val = blkVal N.val blocks.val[k]!) :
    fors.fors_batch_loop3_loop1 blocks vals cnt j ⦃ r =>
      ∀ (k : Nat), k < cnt.val → bytes (r.val[k]!).val = blkVal N.val blocks.val[k]! ⦄ := by
  unfold fors.fors_batch_loop3_loop1
  apply loop.spec_decr_nat
    (measure := fun (p : Array (Array U8 N) 128#usize × Usize) => cnt.val - p.2.val)
    (inv := fun p => p.2.val ≤ cnt.val ∧
      ∀ (k : Nat), k < p.2.val → bytes (p.1.val[k]!).val = blkVal N.val blocks.val[k]!)
  · rintro ⟨vals, j⟩ ⟨h1, h2⟩
    simp only [fors.fors_batch_loop3_loop1.body]
    simp only at h1 h2
    step*
    · refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      rw [j1_post, a2_post, Array.set_val_eq]
      refine forall_set_succ vals.val j.val a1 (fun k (b : Array U8 N) =>
        bytes b.val = blkVal N.val blocks.val[k]!) (by simp; scalar_tac) h2 ?_
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


/-- A level above the leaves for `n > 16`: node `j` of the level, one SHA-512
block from its two children, written in place over the children's array. -/
theorem fors_batch_loop3_loop2_spec {N : Usize} (p : params.Params) (hp : PN p N)
    (i z : U32) (pk : Array U8 N) (st : Array U32 8#usize) (st5 : Array U64 8#usize)
    (hs : SeedOk ({ pk_seed := pk, state := st, state512 := st5 } : hash.Seed N))
    (i1 : U32) (i2 : U64) (i3 i4 i5 i6 : U32)
    (A0 : address.Adrs) (hA0 : A0 = ⟨i1, i2, i3, i4, i5, i6⟩)
    (vals0 : Array (Array U8 N) 128#usize) (lvl : U32) (cnt : Usize)
    (hlvl : 1 ≤ lvl.val) (hlz : lvl.val ≤ z.val) (hz : z.val ≤ 7)
    (hcnt : cnt.val = 2 ^ (z.val - lvl.val)) (hi : (i.val + 1) * 2 ^ z.val < 2 ^ 32)
    (vals : Array (Array U8 N) 128#usize) (j : Usize) (hj : j.val ≤ cnt.val)
    (hdone : ∀ k, k < j.val → bytes (vals.val[k]!).val =
      Spec.H (paramsS p) (bytes pk.val)
        { adrsS A0 with word2 := lvl.val, word3 := i.val * 2 ^ (z.val - lvl.val) + k }
        (bytes (vals0.val[2 * k]!).val ++ bytes (vals0.val[2 * k + 1]!).val))
    (hrest : ∀ k, j.val ≤ k → vals.val[k]! = vals0.val[k]!) :
    fors.fors_batch_loop3_loop2 i z pk st st5 i1 i2 i3 i4 i5 i6 vals lvl cnt j ⦃ r =>
      ∀ k, k < cnt.val → bytes (r.val[k]!).val =
        Spec.H (paramsS p) (bytes pk.val)
          { adrsS A0 with word2 := lvl.val, word3 := i.val * 2 ^ (z.val - lvl.val) + k }
          (bytes (vals0.val[2 * k]!).val ++ bytes (vals0.val[2 * k + 1]!).val) ⦄ := by
  have hp1 : 2 ^ (z.val - lvl.val) ≤ 2 ^ z.val := Nat.pow_le_pow_right (by omega) (by omega)
  have hp2 : 2 ^ z.val ≤ 2 ^ 7 := Nat.pow_le_pow_right (by omega) hz
  have hp3 : 2 * 2 ^ (z.val - lvl.val) ≤ 2 ^ z.val := by
    rw [← pow_succ']; exact Nat.pow_le_pow_right (by omega) (by omega)
  have hiz : i.val * 2 ^ (z.val - lvl.val) ≤ i.val * 2 ^ z.val := Nat.mul_le_mul_left _ hp1
  unfold fors.fors_batch_loop3_loop2
  apply loop.spec_decr_nat
    (measure := fun (q : Array (Array U8 N) 128#usize × Usize) => cnt.val - q.2.val)
    (inv := fun q => q.2.val ≤ cnt.val ∧
      (∀ k, k < q.2.val → bytes (q.1.val[k]!).val =
        Spec.H (paramsS p) (bytes pk.val)
          { adrsS A0 with word2 := lvl.val, word3 := i.val * 2 ^ (z.val - lvl.val) + k }
          (bytes (vals0.val[2 * k]!).val ++ bytes (vals0.val[2 * k + 1]!).val)) ∧
      (∀ k, q.2.val ≤ k → q.1.val[k]! = vals0.val[k]!))
  · rintro ⟨vals, j⟩ ⟨h1, h2, h3⟩
    simp only [fors.fors_batch_loop3_loop2.body]
    simp only at h1 h2 h3
    have hsh : (i.val <<< (z.val - lvl.val)) % U32.size = i.val * 2 ^ (z.val - lvl.val) := by
      rw [Nat.shiftLeft_eq]; exact Nat.mod_eq_of_lt (by simp [U32.size, U32.numBits]; nlinarith)
    split
    · rename_i hlt
      have hjv : j.val < cnt.val := by scalar_tac
      step*
      case P => exact paramsS p
      case hPN => exact hp.n
      case hN => exact hp.nok
      all_goals try exact hs
      step*
      have hi9 : i9.val = j.val := by rw [i9_post]; simp; scalar_tac
      have hidx : idx.val = i.val * 2 ^ (z.val - lvl.val) + j.val := by
        rw [idx_post, i8_post, i7_post, hsh, hi9]
      have hv5 : a5 = vals0.val[2 * j.val]! := by
        rw [a5_post, ← getElem!_eq _ _ (by simp; scalar_tac), i10_post, h3 _ (by omega)]
      have hv6 : a6 = vals0.val[2 * j.val + 1]! := by
        rw [a6_post, ← getElem!_eq _ _ (by simp; scalar_tac), i11_post, i10_post, h3 _ (by omega)]
      refine ⟨by scalar_tac, ?_, ?_, by scalar_tac⟩
      · intro k hk
        rw [j1_post] at hk
        rw [a8_post, Array.set_val_eq]
        rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | hk
        · rw [getElem!_set_ne' _ _ _ _ (by omega)]
          exact h2 k hk
        · subst hk
          rw [getElem!_set_self' _ _ _ (by simp; omega), a7_post, ← hv5, ← hv6, a4_post, a3_post, hA0]
          simp [adrsS, hidx]
      · intro k hk
        rw [a8_post, Array.set_val_eq, getElem!_set_ne' _ _ _ _ (by scalar_tac)]
        exact h3 k (by scalar_tac)
    · simp only [step_simps]
      have : j.val = cnt.val := by scalar_tac
      rw [this] at h2; exact h2
  · exact ⟨hj, hdone, hrest⟩


theorem fors_forsNode_succ (P : Spec.Params) (sk pk : Spec.Bytes) (A : Spec.Adrs) (x h : Nat) :
    Spec.forsNode P sk x (h + 1) pk A =
      Spec.H P pk { A with word2 := h + 1, word3 := x }
        (Spec.forsNode P sk (2 * x) h pk A ++ Spec.forsNode P sk (2 * x + 1) h pk A) := by
  rfl

theorem seed_eta {N : Usize} (seed : hash.Seed N) :
    ({ pk_seed := seed.pk_seed, state := seed.state, state512 := seed.state512 } : hash.Seed N) = seed :=
  rfl

theorem fors_batch_loop3_spec {N : Usize} (p : params.Params) (hp : PN p N) (sk : Array U8 N)
    (seed : hash.Seed N) (hs : SeedOk seed)
    (i z i1 : U32) (i2 : U64) (i3 i4 i5 i6 : U32)
    (A0 : address.Adrs) (hA0 : A0 = ⟨i1, i2, i3, i4, i5, i6⟩)
    (hz : z.val ≤ 7) (hi : (i.val + 1) * 2 ^ z.val < 2 ^ 32)
    (blocks : Array (Array U8 64#usize) 128#usize) (start «end» : Array U32 128#usize)
    (vals : Array (Array U8 N) 128#usize) (lvl : U32) (cnt : Usize)
    (hlvl : 1 ≤ lvl.val) (hlz : lvl.val ≤ z.val + 1) (hcnt : cnt.val = 2 ^ z.val / 2 ^ lvl.val)
    (hv : ∀ k, k < 2 ^ z.val / 2 ^ (lvl.val - 1) → bytes (vals.val[k]!).val =
      Spec.forsNode (paramsS p) (bytes sk.val) (i.val * 2 ^ (z.val - (lvl.val - 1)) + k) (lvl.val - 1)
        (bytes seed.pk_seed.val) (adrsS A0)) :
    fors.fors_batch_loop3 i z seed.pk_seed seed.state seed.state512 i1 i2 i3 i4 i5 i6 blocks start
      «end» vals lvl cnt ⦃ r =>
      bytes (r.val[0]!).val = Spec.forsNode (paramsS p) (bytes sk.val) i.val z.val
        (bytes seed.pk_seed.val) (adrsS A0) ⦄ := by
  unfold fors.fors_batch_loop3
  apply loop.spec_decr_nat
    (measure := fun (q : Array (Array U8 64#usize) 128#usize × Array U32 128#usize ×
      Array U32 128#usize × Array (Array U8 N) 128#usize × U32 × Usize) => z.val + 1 - q.2.2.2.2.1.val)
    (inv := fun q => 1 ≤ q.2.2.2.2.1.val ∧ q.2.2.2.2.1.val ≤ z.val + 1 ∧
      q.2.2.2.2.2.val = 2 ^ z.val / 2 ^ q.2.2.2.2.1.val ∧
      ∀ k, k < 2 ^ z.val / 2 ^ (q.2.2.2.2.1.val - 1) → bytes (q.2.2.2.1.val[k]!).val =
        Spec.forsNode (paramsS p) (bytes sk.val) (i.val * 2 ^ (z.val - (q.2.2.2.2.1.val - 1)) + k)
          (q.2.2.2.2.1.val - 1) (bytes seed.pk_seed.val) (adrsS A0))
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
      have e2 : i.val * 2 ^ (z.val - (lvl.val - 1)) = 2 * (i.val * 2 ^ (z.val - lvl.val)) := by
        rw [show z.val - (lvl.val - 1) = (z.val - lvl.val) + 1 by omega, pow_succ]; ring
      -- the next level from the children, as the specification has it
      have hnext : ∀ k, k < cnt.val →
          Spec.H (paramsS p) (bytes seed.pk_seed.val)
            { adrsS A0 with word2 := lvl.val, word3 := i.val * 2 ^ (z.val - lvl.val) + k }
            (bytes (vals.val[2 * k]!).val ++ bytes (vals.val[2 * k + 1]!).val) =
          Spec.forsNode (paramsS p) (bytes sk.val) (i.val * 2 ^ (z.val - (lvl.val + 1 - 1)) + k)
            (lvl.val + 1 - 1) (bytes seed.pk_seed.val) (adrsS A0) := by
        intro k hkc
        have h2k : 2 * k < 2 ^ z.val / 2 ^ (lvl.val - 1) := by rw [hprev]; omega
        have h2k1 : 2 * k + 1 < 2 ^ z.val / 2 ^ (lvl.val - 1) := by rw [hprev]; omega
        have e := fors_forsNode_succ (paramsS p) (bytes sk.val) (bytes seed.pk_seed.val) (adrsS A0)
          (i.val * 2 ^ (z.val - lvl.val) + k) (lvl.val - 1)
        rw [show lvl.val - 1 + 1 = lvl.val by omega] at e
        rw [show lvl.val + 1 - 1 = lvl.val by omega, e, h4 (2 * k) h2k, h4 (2 * k + 1) h2k1, e2,
          show 2 * (i.val * 2 ^ (z.val - lvl.val) + k) = 2 * (i.val * 2 ^ (z.val - lvl.val)) + 2 * k
            by ring]
        rfl
      split
      · rename_i h16
        subst h16
        let* ⟨ blocks1, start1, end1, hQ ⟩ ← fors_batch_loop3_loop0_spec i z i1 i2 i3 i4 i5 i6 A0 hA0
          vals lvl cnt h1 hlz' hz hcnt' hi blocks start «end» 0#usize (by simp) (by simp)
        step*
        have hsl : s.length = cnt.val := by rw [s_post1]; rfl
        let* ⟨ vals1, vals1_post ⟩ ← fors_batch_loop3_loop1_spec (by decide) (index_mut_back s3) cnt
          (by scalar_tac) vals 0#usize (by simp) (by simp)
        let* ⟨ cnt1, cnt1_post ⟩ ← Usize.div_spec
        let* ⟨ lvl1, lvl1_post ⟩ ← U32.add_spec
        refine ⟨by scalar_tac, by scalar_tac, ?_, ?_, by scalar_tac⟩
        · rw [cnt1_post, lvl1_post, h3, Nat.div_div_eq_div_mul, ← pow_succ]
        · intro k hk
          rw [lvl1_post] at hk ⊢
          rw [show lvl.val + 1 - 1 = lvl.val by omega] at hk
          have hkc : k < cnt.val := by rw [hcnt']; rwa [Nat.pow_div hlz' (by omega)] at hk
          obtain ⟨hb, hs', he⟩ := hQ k hkc
          have hs3 : s3.val.length = cnt.val := by
            have := s3_post; simp only [Slice.length] at this hsl; omega
          rw [vals1_post k hkc, blkVal, s_post2, setSlice0_getElem! _ _ _ (by omega) (by simp; omega),
            s3_post1 k (by simp [Slice.length] at hsl ⊢; omega), s_post,
            slice0_getElem! _ _ _ hkc (by simp; omega), s1_post, s2_post,
            Array.val_to_slice, Array.val_to_slice, he, hs', runBlock_one, hb, ← hnext k hkc]
          have hpkl : (bytes seed.pk_seed.val).length = 16 := by simp
          have hn16 : (paramsS p).n = 16 := by rw [hp.n]; rfl
          rw [H_eq, if_pos hn16, hn16, seed_state seed hs]
          exact stepBlock_pair_value 16 (by decide) _ hpkl
            { adrsS A0 with word2 := lvl.val, word3 := i.val * 2 ^ (z.val - lvl.val) + k } _ (by simp)
      · rename_i h16
        let* ⟨ vals1, vals1_post ⟩ ← fors_batch_loop3_loop2_spec p hp i z seed.pk_seed seed.state
          seed.state512 hs i1 i2 i3 i4 i5 i6 A0 hA0 vals lvl cnt h1 hlz' hz
          hcnt' hi vals 0#usize (by simp) (by simp) (fun _ _ => rfl)
        let* ⟨ cnt1, cnt1_post ⟩ ← Usize.div_spec
        let* ⟨ lvl1, lvl1_post ⟩ ← U32.add_spec
        refine ⟨by scalar_tac, by scalar_tac, ?_, ?_, by scalar_tac⟩
        · rw [cnt1_post, lvl1_post, h3, Nat.div_div_eq_div_mul, ← pow_succ]
        · intro k hk
          rw [lvl1_post] at hk ⊢
          rw [show lvl.val + 1 - 1 = lvl.val by omega] at hk
          have hkc : k < cnt.val := by rw [hcnt']; rwa [Nat.pow_div hlz' (by omega)] at hk
          rw [vals1_post k hkc, hnext k hkc]
    · have hlz' : lvl.val = z.val + 1 := by scalar_tac
      have h0 := h4 0 (by rw [hlz', Nat.add_sub_cancel, Nat.div_self (by positivity)]; omega)
      rw [hlz', Nat.add_sub_cancel, Nat.sub_self, pow_zero, Nat.mul_one, Nat.add_zero] at h0
      simp only [step_simps]
      exact h0
  · exact ⟨hlvl, hlz, hcnt, hv⟩

/-- A FORS leaf block: `PRF` in place, the type switched, then `F` in place. -/
theorem fors_leaf_value (P : Spec.Params) (hn : P.n ≤ 32) (pk : Spec.Bytes) (hpk : pk.length = P.n)
    (A : Spec.Adrs) (m : Spec.Bytes) (hm : m.length = P.n) (t ty : Nat) :
    ((stepBlock P.n (seedState P.n pk) ((stepBlock P.n (seedState P.n pk)
      (padFrom 64 ({ A with word3 := t }.compress ++ m)) t).set 9 (BitVec.ofNat 8 ty)) t).drop 22).take P.n =
      Spec.F P pk { A with word3 := t, typ := ty } (Spec.F P pk { A with word3 := t } m) := by
  have hF : ∀ (B : Spec.Adrs) (x : Spec.Bytes), (Spec.F P pk B x).length = P.n := fun B x => by
    rw [F_eq]; exact th256_length _ hn _ hpk _ _
  rw [stepBlock_thash P hn pk hpk _ _ hm, block_set_typ _ _ (by rw [hF]; omega),
    stepBlock_thash P hn pk hpk _ _ (hF _ _),
    block_value _ _ _ (by rw [hF]; omega), List.take_left' (hF _ _)]

theorem fors_batch_spec {N : Usize} (p : params.Params) (hp : PN p N) (sk : Array U8 N) (i z : U32)
    (seed : hash.Seed N) (hs : SeedOk seed)
    (a : address.Adrs) (hz : z.val ≤ 7) (h : (i.val + 1) * 2 ^ z.val < 2 ^ 32) :
    fors.fors_batch sk i z seed a ⦃ r =>
      bytes r.val = Spec.forsNode (paramsS p) (bytes sk.val) i.val z.val (bytes seed.pk_seed.val)
        (adrsS a) ⦄ := by
  rename' a => adrs
  have hN32 := hp.le32
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
  let* ⟨ blocks1, start1, end1, hL ⟩ ← fors_batch_loop0_spec sk hN32 i z n prf (by omega) (by omega)
    (by omega) _ _ _ 0#usize (by simp) (by simp)
  step*
  let* ⟨ blocks3, blocks3_post ⟩ ← fors_batch_loop1_spec adrs.typ n (by omega) (index_mut_back s3)
    (index_mut_back s3) 0#usize (by simp) (by simp) (fun _ _ => rfl)
  step*
  let* ⟨ vals1, vals1_post ⟩ ← fors_batch_loop2_spec hN32 n (by omega) (index_mut_back1 s7)
    (Array.repeat 128#usize (Array.repeat N 0#u8)) 0#usize (by simp) (by simp)
  let* ⟨ cnt, cnt_post ⟩ ← Usize.div_spec
  have hpkl : (bytes seed.pk_seed.val).length = (paramsS p).n := by rw [hp.n]; simp
  have hsl : s.length = n.val := by rw [s_post1]; rfl
  have hs4l : s4.length = n.val := by rw [s4_post1]; rfl
  have hv : ∀ k, k < 2 ^ z.val / 2 ^ (1 - 1) → bytes (vals1.val[k]!).val =
      Spec.forsNode (paramsS p) (bytes sk.val) (i.val * 2 ^ (z.val - (1 - 1)) + k) (1 - 1)
        (bytes seed.pk_seed.val) (adrsS adrs) := by
    intro k hk
    simp only [Nat.sub_self, pow_zero, Nat.div_one, Nat.sub_zero] at hk ⊢
    have hkn : k < n.val := by omega
    obtain ⟨hb, hs', he⟩ := hL k hkn
    have hs3 : s3.val.length = n.val := by
      have := s3_post; simp only [Slice.length] at this hsl; omega
    have hs7 : s7.val.length = n.val := by
      have := s7_post; simp only [Slice.length] at this hs4l; omega
    have h32 : (paramsS p).n ≤ 32 := by rw [hp.n]; exact hN32
    rw [vals1_post k hkn, blkVal, s4_post2, setSlice0_getElem! _ _ _ (by omega) (by simp; omega),
      s7_post1 k (by simp [Slice.length] at hs4l ⊢; omega), s4_post,
      slice0_getElem! _ _ _ hkn (by simp; omega), s5_post, s6_post,
      Array.val_to_slice, Array.val_to_slice, he, hs', runBlock_one, blocks3_post k hkn,
      s_post2, setSlice0_getElem! _ _ _ (by omega) (by simp; omega),
      s3_post1 k (by simp [Slice.length] at hsl ⊢; omega), s_post,
      slice0_getElem! _ _ _ hkn (by simp; omega), s1_post, s2_post,
      Array.val_to_slice, Array.val_to_slice, he, hs', runBlock_one, hb, ← hp.n, seed_state seed hs,
      hp.n, ← hp.n,
      fors_leaf_value _ h32 _ hpkl _ _ (by rw [hp.n]; simp)]
    simp [Spec.forsNode, Spec.F, Spec.forsSkGen, Spec.PRF, prf_post, a_post1, adrsS,
      Spec.Adrs.setTypeAndClear, Spec.FORS_PRF]
  let* ⟨ vals2, vals2_post ⟩ ← fors_batch_loop3_spec p hp sk seed hs i z adrs.layer adrs.tree adrs.typ
    adrs.keypair adrs.word2 adrs.word3 adrs rfl hz h (index_mut_back1 s7) start1 end1 vals1 1#u32 cnt
    (by simp) (by simp) (by rw [cnt_post, hn]; simp) hv
  let* ⟨ r, r_post ⟩ ← Array.index_usize_spec
  rw [r_post, ← getElem!_eq _ _ (by simp)]
  exact vals2_post

theorem fors_node_spec_aux {N : Usize} (p : params.Params) (hp : PN p N) (sk : Array U8 N)
    (seed : hash.Seed N) (hs : SeedOk seed) (a : address.Adrs) (n : Nat) :
    ∀ (i z : U32), z.val = n → (i.val + 1) * 2 ^ n < 2 ^ 32 →
    fors.fors_node sk i z seed a ⦃ r =>
      bytes r.val = Spec.forsNode (paramsS p) (bytes sk.val) i.val n (bytes seed.pk_seed.val)
        (adrsS a) ⦄ := by
  induction n with
  | zero =>
    intro i z hz h
    have hz7 : z ≤ fors.BATCH_HEIGHT := by simp only [global_simps]; scalar_tac
    unfold fors.fors_node
    simp only [hz7, ↓reduceIte]
    have := fors_batch_spec p hp sk i z seed hs a (by omega) (by rw [hz]; simpa using h)
    rw [hz] at this; exact this
  | succ n ih =>
    intro i z hz h
    unfold fors.fors_node
    by_cases hz7 : z ≤ fors.BATCH_HEIGHT
    · simp only [hz7, ↓reduceIte]
      have hz7' : z.val ≤ 7 := by simp only [global_simps] at hz7; scalar_tac
      have := fors_batch_spec p hp sk i z seed hs a hz7' (by rw [hz]; exact h)
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
      step
      step
      step with hash2_spec p hp as ⟨r, r_post⟩
      rw [r_post]
      simp [Spec.forsNode, adrsS, *]

@[step]
theorem fors_node_spec {N : Usize} (p : params.Params) (hp : PN p N) (sk : Array U8 N) (i z : U32)
    (seed : hash.Seed N) (hs : SeedOk seed) (a : address.Adrs)
    (h : (i.val + 1) * 2 ^ z.val < 2 ^ 32) :
    fors.fors_node sk i z seed a ⦃ r =>
      bytes r.val = Spec.forsNode (paramsS p) (bytes sk.val) i.val z.val (bytes seed.pk_seed.val)
        (adrsS a) ⦄ :=
  fors_node_spec_aux p hp sk seed hs a z.val i z rfl h

theorem fors_xor_one_lt (x m : Nat) (h : x < 2 * m) : x ^^^ 1 < 2 * m := by
  rcases Nat.even_or_odd x with h' | h'
  · rw [Nat.xor_one_of_even h']; obtain ⟨q, hq⟩ := h'; omega
  · rw [Nat.xor_one_of_odd h']; omega

/-- `i · 2^a` fits in 32 bits. -/
theorem fors_shl_arith (a i : Nat) (ha : a ≤ 14) (hi : i < 35) :
    (i <<< a) % 2 ^ 32 = i * 2 ^ a ∧ i * 2 ^ a + 2 ^ a ≤ 35 * 2 ^ 14 := by
  have h1 : 2 ^ a ≤ 2 ^ 14 := Nat.pow_le_pow_right (by omega) ha
  have h2 : (i + 1) * 2 ^ a ≤ 35 * 2 ^ 14 := Nat.mul_le_mul (by omega) h1
  rw [Nat.add_mul, Nat.one_mul] at h2
  refine ⟨?_, h2⟩
  rw [Nat.shiftLeft_eq]
  exact Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.le_add_right _ _) (lt_of_le_of_lt h2 (by norm_num)))

theorem fors_inner_arith (a i idx j : Nat) (ha : a ≤ 14) (hi : i < 35) (hidx : idx < 2 ^ a)
    (hj : j < a) :
    (i <<< (a - j)) % 2 ^ 32 = i * 2 ^ (a - j) ∧
    i * 2 ^ (a - j) + ((idx / 2 ^ j) ^^^ 1) ≤ 2 ^ 32 - 1 ∧
    (i * 2 ^ (a - j) + ((idx / 2 ^ j) ^^^ 1) + 1) * 2 ^ j < 2 ^ 32 := by
  have h1 : 2 ^ (a - j) ≤ 2 ^ 14 := Nat.pow_le_pow_right (by omega) (by omega)
  have hsplit : 2 ^ a = 2 ^ j * 2 ^ (a - j) := by rw [← Nat.pow_add]; congr 1; omega
  have h2 : 2 ^ (a - j) = 2 * 2 ^ (a - j - 1) := by
    rw [← Nat.pow_succ']; congr 1; omega
  have h3 : idx / 2 ^ j < 2 ^ (a - j) := Nat.div_lt_of_lt_mul (by rw [← hsplit]; exact hidx)
  have h4 : (idx / 2 ^ j) ^^^ 1 < 2 ^ (a - j) := by
    rw [h2] at h3 ⊢; exact fors_xor_one_lt _ _ h3
  have h5 : i * 2 ^ (a - j) ≤ 34 * 2 ^ 14 := Nat.mul_le_mul (by omega) h1
  have h6 : i * 2 ^ (a - j) + ((idx / 2 ^ j) ^^^ 1) + 1 ≤ (i + 1) * 2 ^ (a - j) := by
    rw [Nat.add_mul, Nat.one_mul]; omega
  have h7 : 2 ^ a ≤ 2 ^ 14 := Nat.pow_le_pow_right (by omega) ha
  refine ⟨?_, by omega, ?_⟩
  · rw [Nat.shiftLeft_eq]; exact Nat.mod_eq_of_lt (by omega)
  · calc (i * 2 ^ (a - j) + ((idx / 2 ^ j) ^^^ 1) + 1) * 2 ^ j
        ≤ ((i + 1) * 2 ^ (a - j)) * 2 ^ j := Nat.mul_le_mul_right _ h6
      _ = (i + 1) * 2 ^ a := by rw [hsplit]; ring
      _ ≤ 35 * 2 ^ 14 := Nat.mul_le_mul (by omega) h7
      _ < 2 ^ 32 := by norm_num

/-- The `j`-th authentication-path node of FORS tree `i` (Algorithm 16, lines 6–8). -/
def forsAuth (P : Spec.Params) (sk pk : Spec.Bytes) (adrs : Spec.Adrs) (i idx j : Nat) :
    Spec.Bytes :=
  Spec.forsNode P sk (i * 2 ^ (P.a - j) + ((idx / 2 ^ j) ^^^ 1)) j pk adrs

theorem fors_flatMap_range_succ {β} (f : Nat → List β) (n : Nat) :
    (List.range (n + 1)).flatMap f = (List.range n).flatMap f ++ f n := by
  rw [List.range_succ, List.flatMap_append]; simp

theorem fors_sign_inner_spec {N : Usize} (p : params.Params) (hp : PN p N) (sk : Array U8 N)
    (seed : hash.Seed N) (hseed : SeedOk seed) (a : address.Adrs)
    (sig : alloc.vec.Vec U8) (i idx j : U32) (S0 : Spec.Bytes) (L0 : Nat)
    (hi : i.val < p.k.val) (hidx : idx.val < 2 ^ p.a.val) (hj : j.val ≤ p.a.val)
    (hL : L0 ≤ 100000) (hlen : sig.length = L0 + j.val * N.val)
    (hinv : bytes sig.val = S0 ++ (List.range j.val).flatMap
      (forsAuth (paramsS p) (bytes sk.val) (bytes seed.pk_seed.val) (adrsS a) i.val idx.val)) :
    fors.fors_sign_loop0_loop0 sk seed a p.a sig i idx j ⦃ r =>
      r.length = L0 + p.a.val * N.val ∧
      bytes r.val = S0 ++ (List.range p.a.val).flatMap
        (forsAuth (paramsS p) (bytes sk.val) (bytes seed.pk_seed.val) (adrsS a) i.val idx.val) ⦄ := by
  have hn : N.val ≤ 32 := hp.le32
  have hv := hp.valid
  have ha14 : p.a.val ≤ 14 := hv.a_le
  have hk35 : p.k.val ≤ 35 := hv.k_le
  unfold fors.fors_sign_loop0_loop0
  apply loop.spec_decr_nat
    (measure := fun (q : alloc.vec.Vec U8 × U32) => p.a.val - q.2.val)
    (inv := fun q => q.2.val ≤ p.a.val ∧ q.1.length = L0 + q.2.val * N.val ∧
      bytes q.1.val = S0 ++ (List.range q.2.val).flatMap
        (forsAuth (paramsS p) (bytes sk.val) (bytes seed.pk_seed.val) (adrsS a) i.val idx.val))
  · rintro ⟨sig, j⟩ ⟨hj, hlen, hinv⟩
    simp only [fors.fors_sign_loop0_loop0.body]
    simp only at hj hlen hinv
    by_cases hjA : j < p.a
    · simp only [hjA, ↓reduceIte]
      have hjlt : j.val < p.a.val := by scalar_tac
      have hjn : j.val * N.val ≤ 14 * 32 := Nat.mul_le_mul (by omega) hn
      obtain ⟨ha1, ha2, ha3⟩ :=
        fors_inner_arith p.a.val i.val idx.val j.val ha14 (by omega) hidx hjlt
      step as ⟨i1, i1_post⟩
      step as ⟨s, s_post⟩
      step as ⟨i2, i2_post⟩
      step as ⟨i3, i3_post⟩
      have hs : s.val = (idx.val / 2 ^ j.val) ^^^ 1 := by
        rw [s_post, UScalar.val_xor, i1_post, Nat.shiftRight_eq_div_pow]; rfl
      have hi3 : i3.val = i.val * 2 ^ (p.a.val - j.val) := by
        rw [i3_post, i2_post]; simpa [U32.size, U32.numBits] using ha1
      step as ⟨i4, i4_post⟩
      have hi4 : i4.val = i.val * 2 ^ (p.a.val - j.val) + ((idx.val / 2 ^ j.val) ^^^ 1) := by
        rw [i4_post, hi3, hs]
      step with fors_node_spec p hp sk i4 j seed hseed a (by rw [hi4]; exact ha3)
        as ⟨node, node_post⟩
      step as ⟨s1, s1_post⟩
      step as ⟨sig1, sig1_post, sig1_len⟩
      step as ⟨j1, j1_post⟩
      refine ⟨by scalar_tac, ?_, ?_, by scalar_tac⟩
      · rw [sig1_len, hlen, s1_post, j1_post, Nat.add_mul]; simp; omega
      · rw [sig1_post, bytes_append, hinv, j1_post, fors_flatMap_range_succ _ j.val]
        simp [forsAuth, node_post, hi4, s1_post]
    · simp only [hjA, ↓reduceIte]
      have hjeq : j.val = p.a.val := by scalar_tac
      rw [hjeq] at hlen hinv
      simp [hlen, hinv]
  · exact ⟨hj, hlen, hinv⟩

/-- The part of a FORS signature for tree `i`: the secret value and its authentication path. -/
def forsSignTree (P : Spec.Params) (sk pk : Spec.Bytes) (adrs : Spec.Adrs) (ind : List Nat)
    (i : Nat) : Spec.Bytes :=
  Spec.forsSkGen P sk pk adrs (i * 2 ^ P.a + ind[i]!) ++
    (List.range P.a).flatMap (forsAuth P sk pk adrs i ind[i]!)

theorem forsSign_eq (P : Spec.Params) (md sk pk : Spec.Bytes) (adrs : Spec.Adrs) :
    Spec.forsSign P md sk pk adrs =
      (List.range P.k).flatMap (forsSignTree P sk pk adrs (Spec.base2b md P.a P.k)) := by
  rfl

theorem fors_nats_getElem! (l : List U32) (i : Nat) (h : i < l.length) :
    (nats l)[i]! = (l[i]'h).val := by
  simp [nats, h]

theorem fors_sign_loop_spec {N : Usize} (p : params.Params) (hp : PN p N) (sk : Array U8 N)
    (seed : hash.Seed N) (hs : SeedOk seed) (a : address.Adrs)
    (indices : alloc.vec.Vec U32) (sig : alloc.vec.Vec U8) (i : U32)
    (hlenI : indices.length = p.k.val) (hbd : ∀ d ∈ indices.val, d.val < 2 ^ p.a.val)
    (hi : i.val ≤ p.k.val) (hlen : sig.length = i.val * (1 + p.a.val) * N.val)
    (hinv : bytes sig.val = (List.range i.val).flatMap
      (forsSignTree (paramsS p) (bytes sk.val) (bytes seed.pk_seed.val) (adrsS a) (nats indices.val))) :
    fors.fors_sign_loop0 p.k sk seed a p.a indices sig i ⦃ r =>
      r.length = p.k.val * (1 + p.a.val) * N.val ∧
      bytes r.val = (List.range p.k.val).flatMap
        (forsSignTree (paramsS p) (bytes sk.val) (bytes seed.pk_seed.val) (adrsS a) (nats indices.val)) ⦄ := by
  have hn : N.val ≤ 32 := hp.le32
  have hv := hp.valid
  have ha14 : p.a.val ≤ 14 := hv.a_le
  have hk35 : p.k.val ≤ 35 := hv.k_le
  unfold fors.fors_sign_loop0
  apply loop.spec_decr_nat
    (measure := fun (q : alloc.vec.Vec U8 × U32) => p.k.val - q.2.val)
    (inv := fun q => q.2.val ≤ p.k.val ∧ q.1.length = q.2.val * (1 + p.a.val) * N.val ∧
      bytes q.1.val = (List.range q.2.val).flatMap
        (forsSignTree (paramsS p) (bytes sk.val) (bytes seed.pk_seed.val) (adrsS a) (nats indices.val)))
  · rintro ⟨sig, i⟩ ⟨hi, hlen, hinv⟩
    simp only [fors.fors_sign_loop0.body]
    simp only at hi hlen hinv
    by_cases hiK : i < p.k
    · simp only [hiK, ↓reduceIte]
      have hilt : i.val < p.k.val := by scalar_tac
      have hbound : i.val * (1 + p.a.val) * N.val ≤ 35 * 15 * 32 :=
        Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by omega)) hn
      obtain ⟨hs1, hs2⟩ := fors_shl_arith p.a.val i.val ha14 (by omega)
      step as ⟨i1, i1_post⟩
      have hi1 : i1.val = i.val := by rw [i1_post]; simp
      step as ⟨idx, idx_post⟩
      have hidx : idx.val < 2 ^ p.a.val := by rw [idx_post]; exact hbd _ (List.getElem_mem _)
      have hind : (nats indices.val)[i.val]! = idx.val := by
        rw [fors_nats_getElem! _ _ (by scalar_tac)]; simp [idx_post, hi1]
      step as ⟨i2, i2_post⟩
      have hi2 : i2.val = i.val * 2 ^ p.a.val := by
        rw [i2_post]; simpa [U32.size, U32.numBits] using hs1
      step as ⟨i3, i3_post⟩
      step with fors_sk_gen_spec p hp sk seed hs a i3 as ⟨sk1, sk1_post⟩
      step as ⟨s, s_post⟩
      step as ⟨sig1, sig1_post, sig1_len⟩
      have hl1 : sig1.length = sig.length + N.val := by
        rw [sig1_len]; simp [s_post]
      step with fors_sign_inner_spec p hp sk seed hs a sig1 i idx 0#u32 (bytes sig1.val) sig1.length
        hilt hidx (by simp) (by omega) (by simp) (by simp)
        as ⟨sig2, sig2_len, sig2_post⟩
      step as ⟨i4, i4_post⟩
      refine ⟨by scalar_tac, ?_, ?_, by scalar_tac⟩
      · rw [sig2_len, hl1, hlen, i4_post]; ring
      · rw [sig2_post, sig1_post, bytes_append, hinv, i4_post, fors_flatMap_range_succ _ i.val]
        simp [forsSignTree, hind, sk1_post, i3_post, hi2, s_post]
    · simp only [hiK, ↓reduceIte]
      have hieq : i.val = p.k.val := by scalar_tac
      rw [hieq] at hlen hinv
      simp [hlen, hinv]
  · exact ⟨hi, hlen, hinv⟩

@[step]
theorem fors_sign_spec {N : Usize} (p : params.Params) (hp : PN p N) (md : Slice U8)
    (sk : Array U8 N) (seed : hash.Seed N) (hs : SeedOk seed) (a : address.Adrs)
    (hmd : md.length = (p.k.val * p.a.val + 7) / 8) :
    fors.fors_sign p md sk seed a ⦃ r =>
      bytes r.val = Spec.forsSign (paramsS p) (bytes md.val) (bytes sk.val) (bytes seed.pk_seed.val)
        (adrsS a) ∧
      r.length = p.k.val * (1 + p.a.val) * N.val ⦄ := by
  have hv := hp.valid
  have ha1 : 1 ≤ p.a.val := hv.a_pos
  have ha14 : p.a.val ≤ 14 := hv.a_le
  unfold fors.fors_sign
  step as ⟨i, i_post⟩
  have hi : i.val = p.k.val := by rw [i_post]; simp
  step with base_2b_spec md p.a i (by omega) (by rw [hi, hmd]; omega)
    as ⟨indices, hind, hlenI, hbd⟩
  rw [hi] at hind hlenI
  apply WP.spec_mono
  · exact fors_sign_loop_spec p hp sk seed hs a indices (alloc.vec.Vec.new U8) 0#u32
      (by simpa using hlenI) hbd (by simp) (by simp) (by simp)
  · intro r ⟨h1, h2⟩
    refine ⟨?_, h1⟩
    rw [forsSign_eq, h2, hind]; rfl


/-! `fors_pkFromSig`: the `k` trees climbed together. -/

/-- The root of FORS tree `i` recomputed from a signature (Algorithm 17, lines 3–20). -/
def forsRoot (P : Spec.Params) (sig pk : Spec.Bytes) (adrs : Spec.Adrs) (ind : List Nat)
    (i : Nat) : Spec.Bytes :=
  Spec.climb P
    (Spec.F P pk { adrs with word2 := 0, word3 := i * 2 ^ P.a + ind[i]! }
      (Spec.block P sig (i * (P.a + 1))))
    ind[i]! (i * 2 ^ P.a + ind[i]!)
    ((sig.drop ((i * (P.a + 1) + 1) * P.n)).take (P.a * P.n)) P.a pk adrs

theorem forsPkFromSig_eq (P : Spec.Params) (sig md pk : Spec.Bytes) (adrs : Spec.Adrs) :
    Spec.forsPkFromSig P sig md pk adrs =
      Spec.T P pk { adrs.setTypeAndClear Spec.FORS_ROOTS with keypair := adrs.keypair }
        ((List.range P.k).flatMap (forsRoot P sig pk adrs (Spec.base2b md P.a P.k))) := by
  rfl

/-- The leaf index of FORS tree `t`. -/
def forsLeaf (a : Nat) (ind : List Nat) (t : Nat) : Nat := t * 2 ^ a + ind[t]!

theorem cast_u32_usize_val (i : Usize) (h : i.val < 2 ^ 32) : (UScalar.cast .U32 i).val = i.val := by
  simp; scalar_tac

theorem fors_pk_from_sig_loop0_spec {N : Usize} (p : params.Params) (hp : PN p N) (sig : Slice U8)
    (adrs : address.Adrs) (k : Usize) (hk : k.val = p.k.val)
    (indices : alloc.vec.Vec U32) (hs : sig.length = p.k.val * (1 + p.a.val) * N.val)
    (hlenI : indices.length = p.k.val) (hbd : ∀ d ∈ indices.val, d.val < 2 ^ p.a.val)
    (blocks : Array (Array U8 64#usize) 35#usize) (idx «end» : Array U32 35#usize) (i : Usize)
    (hi : i.val ≤ k.val)
    (hinv : ∀ t, t < i.val →
      bytes (blocks.val[t]!).val = padFrom 64 ({ adrsS adrs with word2 := 0, word3 := forsLeaf p.a.val (nats indices.val) t }.compress ++
          Spec.block (paramsS p) (bytes sig.val) (t * (p.a.val + 1))) ∧
      (idx.val[t]!).val = forsLeaf p.a.val (nats indices.val) t ∧
      («end».val[t]!).val = forsLeaf p.a.val (nats indices.val) t + 1) :
    fors.fors_pk_from_sig_loop0 N sig adrs p.a k indices blocks idx «end» i ⦃ r =>
      ∀ t, t < k.val →
        bytes (r.1.val[t]!).val = padFrom 64 ({ adrsS adrs with word2 := 0, word3 := forsLeaf p.a.val (nats indices.val) t }.compress ++
            Spec.block (paramsS p) (bytes sig.val) (t * (p.a.val + 1))) ∧
        (r.2.1.val[t]!).val = forsLeaf p.a.val (nats indices.val) t ∧
        (r.2.2.val[t]!).val = forsLeaf p.a.val (nats indices.val) t + 1 ⦄ := by
  have hv := hp.valid
  have ha14 : p.a.val ≤ 14 := hv.a_le
  have hk35 : p.k.val ≤ 35 := hv.k_le
  have hN32 := hp.le32
  unfold fors.fors_pk_from_sig_loop0
  apply loop.spec_decr_nat
    (measure := fun (q : Array (Array U8 64#usize) 35#usize × Array U32 35#usize ×
      Array U32 35#usize × Usize) => k.val - q.2.2.2.val)
    (inv := fun q => q.2.2.2.val ≤ k.val ∧ ∀ t, t < q.2.2.2.val →
      bytes (q.1.val[t]!).val = padFrom 64 ({ adrsS adrs with word2 := 0, word3 := forsLeaf p.a.val (nats indices.val) t }.compress ++
          Spec.block (paramsS p) (bytes sig.val) (t * (p.a.val + 1))) ∧
      (q.2.1.val[t]!).val = forsLeaf p.a.val (nats indices.val) t ∧
      (q.2.2.1.val[t]!).val = forsLeaf p.a.val (nats indices.val) t + 1)
  · rintro ⟨blocks, idx, «end», i⟩ ⟨h1, h2⟩
    simp only [fors.fors_pk_from_sig_loop0.body]
    simp only at h1 h2
    split
    · rename_i hlt
      have hil : i.val < p.k.val := by scalar_tac
      obtain ⟨hs1, hs2⟩ := fors_shl_arith p.a.val i.val ha14 (by omega)
      have hbl : (i.val * (p.a.val + 1) + 1) * N.val ≤ sig.length := by
        rw [hs]
        have : i.val * (p.a.val + 1) + 1 ≤ p.k.val * (1 + p.a.val) := by
          have := Nat.mul_le_mul_right (p.a.val + 1) (show i.val + 1 ≤ p.k.val by omega)
          rw [Nat.add_mul, Nat.one_mul] at this; rw [Nat.add_comm 1 p.a.val]; omega
        exact Nat.mul_le_mul_right _ this
      step as ⟨i1, i1_post⟩
      have hi1 : i1.val = i.val := by rw [i1_post]; exact cast_u32_usize_val _ (by omega)
      step as ⟨i2, i2_post, i2_post1⟩
      have hi2 : i2.val = i.val * 2 ^ p.a.val := by
        rw [i2_post, hi1]; simpa [U32.size, U32.numBits] using hs1
      step as ⟨i3, i3_post⟩
      have hi3 : i3.val < 2 ^ p.a.val := by rw [i3_post]; exact hbd _ (List.getElem_mem _)
      have hind : (nats indices.val)[i.val]! = i3.val := by
        rw [fors_nats_getElem! _ _ (by scalar_tac)]; simp [i3_post]
      step as ⟨leaf, leaf_post⟩
      step as ⟨i4, i4_post⟩
      step as ⟨i5, i5_post⟩
      have hi45 : i5.val = p.a.val + 1 := by rw [i5_post, i4_post]; simp
      have hmul : i.val * i5.val ≤ 35 * 15 := by rw [hi45]; exact Nat.mul_le_mul (by omega) (by omega)
      step*
      have hleaf : leaf.val = forsLeaf p.a.val (nats indices.val) i.val := by
        rw [leaf_post, hi2, forsLeaf, hind]
      have hi6 : i6.val = i.val * (p.a.val + 1) := by rw [i6_post, hi45]
      refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      intro t ht
      rw [i8_post] at ht
      rw [a4_post, a5_post, a6_post, Array.set_val_eq, Array.set_val_eq, Array.set_val_eq]
      rcases Nat.lt_succ_iff_lt_or_eq.mp ht with ht | ht
      · rw [getElem!_set_ne' _ _ _ _ (by omega), getElem!_set_ne' _ _ _ _ (by omega),
          getElem!_set_ne' _ _ _ _ (by omega)]
        exact h2 t ht
      · subst ht
        rw [getElem!_set_self' _ _ _ (by simp; omega), getElem!_set_self' _ _ _ (by simp; omega),
          getElem!_set_self' _ _ _ (by simp; omega)]
        refine ⟨?_, hleaf, by rw [i7_post, hleaf]⟩
        rw [a3_post, s_post, Array.val_to_slice,
          bytes_block (paramsS p) sig.val sk.val i6.val (by rw [sk_post, hp.n]), hi6, a2_post, a1_post]
        simp [adrsS, hleaf]
    · simp only [step_simps]
      have : i.val = k.val := by scalar_tac
      rw [this] at h2; exact h2
  · exact ⟨hi, hinv⟩

theorem fors_pk_from_sig_loop1_spec {N : Usize} (hN : N.val ≤ 32) (k : Usize) (hk : k.val ≤ 35)
    (blocks : Array (Array U8 64#usize) 35#usize)
    (vals : Array (Array U8 N) 35#usize) (i : Usize) (hi : i.val ≤ k.val)
    (hinv : ∀ (t : Nat), t < i.val → bytes (vals.val[t]!).val = blkVal N.val blocks.val[t]!) :
    fors.fors_pk_from_sig_loop1 k blocks vals i ⦃ r =>
      ∀ (t : Nat), t < k.val → bytes (r.val[t]!).val = blkVal N.val blocks.val[t]! ⦄ := by
  unfold fors.fors_pk_from_sig_loop1
  apply loop.spec_decr_nat
    (measure := fun (q : Array (Array U8 N) 35#usize × Usize) => k.val - q.2.val)
    (inv := fun q => q.2.val ≤ k.val ∧
      ∀ (t : Nat), t < q.2.val → bytes (q.1.val[t]!).val = blkVal N.val blocks.val[t]!)
  · rintro ⟨vals, i⟩ ⟨h1, h2⟩
    simp only [fors.fors_pk_from_sig_loop1.body]
    simp only at h1 h2
    step*
    · refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      rw [i1_post, a2_post, Array.set_val_eq]
      refine forall_set_succ vals.val i.val a1 (fun t (b : Array U8 N) =>
        bytes b.val = blkVal N.val blocks.val[t]!) (by simp; scalar_tac) h2 ?_
      rw [a1_post, a_post, ← getElem!_eq _ _ (by simp; scalar_tac)]
      rfl
  · exact ⟨hi, hinv⟩

theorem fors_pk_from_sig_loop2_loop1_spec {N : Usize} (hN : N.val ≤ 32) (k : Usize) (hk : k.val ≤ 35)
    (blocks : Array (Array U8 64#usize) 35#usize)
    (vals : Array (Array U8 N) 35#usize) (i : Usize) (hi : i.val ≤ k.val)
    (hinv : ∀ (t : Nat), t < i.val → bytes (vals.val[t]!).val = blkVal N.val blocks.val[t]!) :
    fors.fors_pk_from_sig_loop2_loop1 k blocks vals i ⦃ r =>
      ∀ (t : Nat), t < k.val → bytes (r.val[t]!).val = blkVal N.val blocks.val[t]! ⦄ := by
  unfold fors.fors_pk_from_sig_loop2_loop1
  apply loop.spec_decr_nat
    (measure := fun (q : Array (Array U8 N) 35#usize × Usize) => k.val - q.2.val)
    (inv := fun q => q.2.val ≤ k.val ∧
      ∀ (t : Nat), t < q.2.val → bytes (q.1.val[t]!).val = blkVal N.val blocks.val[t]!)
  · rintro ⟨vals, i⟩ ⟨h1, h2⟩
    simp only [fors.fors_pk_from_sig_loop2_loop1.body]
    simp only at h1 h2
    step*
    · refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      rw [i1_post, a2_post, Array.set_val_eq]
      refine forall_set_succ vals.val i.val a1 (fun t (b : Array U8 N) =>
        bytes b.val = blkVal N.val blocks.val[t]!) (by simp; scalar_tac) h2 ?_
      rw [a1_post, a_post, ← getElem!_eq _ _ (by simp; scalar_tac)]
      rfl
  · exact ⟨hi, hinv⟩

theorem fors_pk_from_sig_loop3_spec {N : Usize} (hN : N.val ≤ 32) (k : Usize) (hk : k.val ≤ 35)
    (vals : Array (Array U8 N) 35#usize)
    (roots : alloc.vec.Vec U8) (i : Usize) (hi : i.val ≤ k.val) (hlen : roots.length = N.val * i.val)
    (hinv : bytes roots.val = (List.range i.val).flatMap (fun (t : Nat) => bytes (vals.val[t]!).val)) :
    fors.fors_pk_from_sig_loop3 k vals roots i ⦃ r =>
      bytes r.val = (List.range k.val).flatMap (fun (t : Nat) => bytes (vals.val[t]!).val) ∧
      r.length = N.val * k.val ⦄ := by
  unfold fors.fors_pk_from_sig_loop3
  apply loop.spec_decr_nat (measure := fun (q : alloc.vec.Vec U8 × Usize) => k.val - q.2.val)
    (inv := fun q => q.2.val ≤ k.val ∧ q.1.length = N.val * q.2.val ∧
      bytes q.1.val = (List.range q.2.val).flatMap (fun (t : Nat) => bytes (vals.val[t]!).val))
  · rintro ⟨roots, i⟩ ⟨h1, h2, h3⟩
    simp only [fors.fors_pk_from_sig_loop3.body]
    simp only at h1 h2 h3
    split
    · rename_i hlt
      have hil : i.val < k.val := by scalar_tac
      have hb : N.val * i.val + N.val ≤ 32 * 35 := by
        have := Nat.mul_le_mul hN (show i.val + 1 ≤ 35 by omega); rw [Nat.mul_succ] at this; omega
      step*
      refine ⟨by scalar_tac, ?_, ?_, by scalar_tac⟩
      · rw [roots1_post1, h2, s_post, i1_post, Nat.mul_succ]; simp
      · rw [roots1_post, bytes_append, h3, i1_post, fors_flatMap_range_succ _ i.val]
        simp [s_post, a_post, getElem!_eq _ _ (show i.val < vals.val.length by simp; scalar_tac)]
    · simp only [step_simps]
      have : i.val = k.val := by scalar_tac
      rw [this] at h2 h3
      exact ⟨h3, h2⟩
  · exact ⟨hi, hlen, hinv⟩

/-- The message of an inner FORS node: the node and its sibling, in the order
given by the parity of the node's index. -/
def pairMsg (v sib : Spec.Bytes) (x : Nat) : Spec.Bytes := if x % 2 = 0 then v ++ sib else sib ++ v

theorem pairMsg_even (v sib : Spec.Bytes) (x : Nat) (h : x % 2 = 0) : pairMsg v sib x = v ++ sib := by
  simp [pairMsg, h]

theorem pairMsg_odd (v sib : Spec.Bytes) (x : Nat) (h : ¬ x % 2 = 0) : pairMsg v sib x = sib ++ v := by
  simp [pairMsg, h]

/-- The position of the sibling read for tree `t` at level `h` fits in the signature. -/
theorem fors_sib_bound (a k n t h L : Nat) (ht : t < k) (hh : h < a) (hL : L = k * (1 + a) * n) :
    (t * (a + 1) + 1 + h + 1) * n ≤ L := by
  subst hL
  apply Nat.mul_le_mul_right
  have := Nat.mul_le_mul_right (a + 1) (show t + 1 ≤ k by omega)
  rw [Nat.add_mul, Nat.one_mul] at this; rw [Nat.add_comm 1 a]; omega

set_option maxHeartbeats 2000000 in
theorem fors_pk_from_sig_loop2_loop0_spec (p : params.Params) (hp : PN p 16#usize) (sig : Slice U8)
    (adrs : address.Adrs) (k : Usize) (hk : k.val = p.k.val)
    (vals : Array (Array U8 16#usize) 35#usize) (h : U32) (hh : h.val < p.a.val)
    (hs : sig.length = p.k.val * (1 + p.a.val) * 16)
    (idx0 : Array U32 35#usize)
    (blocks : Array (Array U8 64#usize) 35#usize) (idx «end» : Array U32 35#usize) (i : Usize)
    (hi : i.val ≤ k.val)
    (hdone : ∀ t, t < i.val →
      bytes (blocks.val[t]!).val = padFrom 64 ({ adrsS adrs with word2 := h.val + 1, word3 := (idx0.val[t]!).val / 2 }.compress ++
        pairMsg (bytes (vals.val[t]!).val)
          (Spec.block (paramsS p) (bytes sig.val) (t * (p.a.val + 1) + 1 + h.val)) (idx0.val[t]!).val) ∧
      (idx.val[t]!).val = (idx0.val[t]!).val / 2 ∧ («end».val[t]!).val = (idx0.val[t]!).val / 2 + 1)
    (hrest : ∀ t, i.val ≤ t → idx.val[t]! = idx0.val[t]!) :
    fors.fors_pk_from_sig_loop2_loop0 sig adrs p.a k blocks idx «end» vals h i ⦃ r =>
      ∀ t, t < k.val →
        bytes (r.1.val[t]!).val = padFrom 64 ({ adrsS adrs with word2 := h.val + 1, word3 := (idx0.val[t]!).val / 2 }.compress ++
          pairMsg (bytes (vals.val[t]!).val)
            (Spec.block (paramsS p) (bytes sig.val) (t * (p.a.val + 1) + 1 + h.val)) (idx0.val[t]!).val) ∧
        (r.2.1.val[t]!).val = (idx0.val[t]!).val / 2 ∧ (r.2.2.val[t]!).val = (idx0.val[t]!).val / 2 + 1 ⦄ := by
  have hv := hp.valid
  have ha14 : p.a.val ≤ 14 := hv.a_le
  have hk35 : p.k.val ≤ 35 := hv.k_le
  unfold fors.fors_pk_from_sig_loop2_loop0
  apply loop.spec_decr_nat
    (measure := fun (q : Array (Array U8 64#usize) 35#usize × Array U32 35#usize ×
      Array U32 35#usize × Usize) => k.val - q.2.2.2.val)
    (inv := fun q => q.2.2.2.val ≤ k.val ∧ (∀ t, t < q.2.2.2.val →
      bytes (q.1.val[t]!).val = padFrom 64 ({ adrsS adrs with word2 := h.val + 1, word3 := (idx0.val[t]!).val / 2 }.compress ++
        pairMsg (bytes (vals.val[t]!).val)
          (Spec.block (paramsS p) (bytes sig.val) (t * (p.a.val + 1) + 1 + h.val)) (idx0.val[t]!).val) ∧
      (q.2.1.val[t]!).val = (idx0.val[t]!).val / 2 ∧ (q.2.2.1.val[t]!).val = (idx0.val[t]!).val / 2 + 1) ∧
      (∀ t, q.2.2.2.val ≤ t → q.2.1.val[t]! = idx0.val[t]!))
  · rintro ⟨blocks, idx, «end», i⟩ ⟨h1, h2, h3⟩
    simp only [fors.fors_pk_from_sig_loop2_loop0.body]
    simp only at h1 h2 h3
    split
    · rename_i hlt
      have hil : i.val < k.val := by scalar_tac
      have hsb := fors_sib_bound p.a.val p.k.val 16 i.val h.val sig.length (by omega) hh hs
      step as ⟨i1, i1_post⟩
      step as ⟨i2, i2_post⟩
      have hi2 : i2.val = p.a.val + 1 := by rw [i2_post, i1_post]; simp
      have hmul : i.val * i2.val ≤ 35 * 15 := by rw [hi2]; exact Nat.mul_le_mul (by omega) (by omega)
      step as ⟨i3, i3_post⟩
      step as ⟨i4, i4_post⟩
      step as ⟨i5, i5_post⟩
      have hi5 : i5.val = h.val := by rw [i5_post]; simp
      step as ⟨i6, i6_post⟩
      have hi6 : i6.val = i.val * (p.a.val + 1) + 1 + h.val := by
        rw [i6_post, i4_post, i3_post, hi2, hi5]
      step as ⟨sibling, sibling_post⟩
      step*
      have hil' : i.val < idx.val.length := by simp; omega
      have hi8 : i7 = idx0.val[i.val]! := by
        rw [i7_post, ← getElem!_eq _ _ hil', h3 _ (le_refl _)]
      have hpar : parent.val = (idx0.val[i.val]!).val / 2 := by
        rw [parent_post, ← hi8]; simp [Nat.shiftRight_eq_div_pow]
      have hi9 : i9.val = (idx0.val[i.val]!).val % 2 := by
        rw [i9_post, ← hi8]; simp [Nat.and_one_is_mod]
      have hadrs : adrsS adr = { adrsS adrs with word2 := h.val + 1, word3 := parent.val } := by
        simp [adrsS, adr_post, a1_post, i8_post]
      have hsib : bytes sibling.val = Spec.block (paramsS p) (bytes sig.val) (i.val * (p.a.val + 1) + 1 + h.val) := by
        rw [bytes_block (paramsS p) sig.val sibling.val i6.val (by rw [sibling_post, hp.n]; rfl), hi6]
      have hvl : i.val < vals.val.length := by simp; omega
      by_cases hc : i9 = 0#u32
      · simp only [hc, ↓reduceIte]
        have hev : (idx0.val[i.val]!).val % 2 = 0 := by rw [← hi9, hc]; rfl
        let* ⟨ v, v_post ⟩ ← Array.index_usize_spec
        let* ⟨ pb, pb_post ⟩ ← pair_block_spec
        let* ⟨ b1, b1_post ⟩ ← Array.update_spec
        step*
        refine ⟨by scalar_tac, ?_, ?_, by scalar_tac⟩
        · intro t ht
          rw [i11_post] at ht
          rw [b1_post, a2_post, a3_post, Array.set_val_eq, Array.set_val_eq, Array.set_val_eq]
          rcases Nat.lt_succ_iff_lt_or_eq.mp ht with ht | ht
          · rw [getElem!_set_ne' _ _ _ _ (by omega), getElem!_set_ne' _ _ _ _ (by omega),
              getElem!_set_ne' _ _ _ _ (by omega)]
            exact h2 t ht
          · subst ht
            rw [getElem!_set_self' _ _ _ (by simp; omega), getElem!_set_self' _ _ _ (by simp; omega),
              getElem!_set_self' _ _ _ (by simp; omega)]
            refine ⟨?_, hpar, by rw [i10_post, hpar]⟩
            rw [pb_post, hadrs, hpar, v_post, ← getElem!_eq _ _ hvl, hsib, pairMsg_even _ _ _ hev]
        · intro t ht
          rw [a2_post, Array.set_val_eq, getElem!_set_ne' _ _ _ _ (by scalar_tac)]
          exact h3 t (by scalar_tac)
      · simp only [hc, ↓reduceIte]
        have hod : ¬ (idx0.val[i.val]!).val % 2 = 0 := by
          rw [← hi9]; intro h0; apply hc; scalar_tac
        let* ⟨ v, v_post ⟩ ← Array.index_usize_spec
        let* ⟨ pb, pb_post ⟩ ← pair_block_spec
        let* ⟨ b1, b1_post ⟩ ← Array.update_spec
        step*
        refine ⟨by scalar_tac, ?_, ?_, by scalar_tac⟩
        · intro t ht
          rw [i11_post] at ht
          rw [b1_post, a2_post, a3_post, Array.set_val_eq, Array.set_val_eq, Array.set_val_eq]
          rcases Nat.lt_succ_iff_lt_or_eq.mp ht with ht | ht
          · rw [getElem!_set_ne' _ _ _ _ (by omega), getElem!_set_ne' _ _ _ _ (by omega),
              getElem!_set_ne' _ _ _ _ (by omega)]
            exact h2 t ht
          · subst ht
            rw [getElem!_set_self' _ _ _ (by simp; omega), getElem!_set_self' _ _ _ (by simp; omega),
              getElem!_set_self' _ _ _ (by simp; omega)]
            refine ⟨?_, hpar, by rw [i10_post, hpar]⟩
            rw [pb_post, hadrs, hpar, v_post, ← getElem!_eq _ _ hvl, hsib, pairMsg_odd _ _ _ hod]
        · intro t ht
          rw [a2_post, Array.set_val_eq, getElem!_set_ne' _ _ _ _ (by scalar_tac)]
          exact h3 t (by scalar_tac)
    · simp only [step_simps]
      have : i.val = k.val := by scalar_tac
      rw [this] at h2; exact h2
  · exact ⟨hi, hdone, hrest⟩

set_option maxHeartbeats 2000000 in
/-- A level of the `k` climbs for `n > 16`: one SHA-512 block per tree, in place. -/
theorem fors_pk_from_sig_loop2_loop2_spec {N : Usize} (p : params.Params) (hp : PN p N)
    (sig : Slice U8) (pk : Array U8 N) (st : Array U32 8#usize) (st5 : Array U64 8#usize)
    (hs : SeedOk ({ pk_seed := pk, state := st, state512 := st5 } : hash.Seed N))
    (adrs : address.Adrs) (k : Usize) (hk : k.val = p.k.val)
    (vals0 : Array (Array U8 N) 35#usize) (idx0 : Array U32 35#usize)
    (h : U32) (hh : h.val < p.a.val) (hsig : sig.length = p.k.val * (1 + p.a.val) * N.val)
    (idx : Array U32 35#usize) (vals : Array (Array U8 N) 35#usize) (i : Usize) (hi : i.val ≤ k.val)
    (hdone : ∀ t, t < i.val →
      bytes (vals.val[t]!).val = Spec.H (paramsS p) (bytes pk.val)
        { adrsS adrs with word2 := h.val + 1, word3 := (idx0.val[t]!).val / 2 }
        (pairMsg (bytes (vals0.val[t]!).val)
          (Spec.block (paramsS p) (bytes sig.val) (t * (p.a.val + 1) + 1 + h.val)) (idx0.val[t]!).val) ∧
      (idx.val[t]!).val = (idx0.val[t]!).val / 2)
    (hrest : ∀ t, i.val ≤ t → vals.val[t]! = vals0.val[t]! ∧ idx.val[t]! = idx0.val[t]!) :
    fors.fors_pk_from_sig_loop2_loop2 sig pk st st5 adrs p.a k idx vals h i ⦃ r =>
      ∀ t, t < k.val →
        bytes (r.2.val[t]!).val = Spec.H (paramsS p) (bytes pk.val)
          { adrsS adrs with word2 := h.val + 1, word3 := (idx0.val[t]!).val / 2 }
          (pairMsg (bytes (vals0.val[t]!).val)
            (Spec.block (paramsS p) (bytes sig.val) (t * (p.a.val + 1) + 1 + h.val)) (idx0.val[t]!).val) ∧
        (r.1.val[t]!).val = (idx0.val[t]!).val / 2 ⦄ := by
  have hv := hp.valid
  have ha14 : p.a.val ≤ 14 := hv.a_le
  have hk35 : p.k.val ≤ 35 := hv.k_le
  unfold fors.fors_pk_from_sig_loop2_loop2
  apply loop.spec_decr_nat
    (measure := fun (q : Array U32 35#usize × Array (Array U8 N) 35#usize × Usize) => k.val - q.2.2.val)
    (inv := fun q => q.2.2.val ≤ k.val ∧ (∀ t, t < q.2.2.val →
      bytes (q.2.1.val[t]!).val = Spec.H (paramsS p) (bytes pk.val)
        { adrsS adrs with word2 := h.val + 1, word3 := (idx0.val[t]!).val / 2 }
        (pairMsg (bytes (vals0.val[t]!).val)
          (Spec.block (paramsS p) (bytes sig.val) (t * (p.a.val + 1) + 1 + h.val)) (idx0.val[t]!).val) ∧
      (q.1.val[t]!).val = (idx0.val[t]!).val / 2) ∧
      (∀ t, q.2.2.val ≤ t → q.2.1.val[t]! = vals0.val[t]! ∧ q.1.val[t]! = idx0.val[t]!))
  · rintro ⟨idx, vals, i⟩ ⟨h1, h2, h3⟩
    simp only [fors.fors_pk_from_sig_loop2_loop2.body]
    simp only at h1 h2 h3
    split
    · rename_i hlt
      have hil : i.val < k.val := by scalar_tac
      have hsb := fors_sib_bound p.a.val p.k.val N.val i.val h.val sig.length (by omega) hh hsig
      step as ⟨i1, i1_post⟩
      step as ⟨i2, i2_post⟩
      have hi2 : i2.val = p.a.val + 1 := by rw [i2_post, i1_post]; simp
      have hmul : i.val * i2.val ≤ 35 * 15 := by rw [hi2]; exact Nat.mul_le_mul (by omega) (by omega)
      step as ⟨i3, i3_post⟩
      step as ⟨i4, i4_post⟩
      step as ⟨i5, i5_post⟩
      have hi5 : i5.val = h.val := by rw [i5_post]; simp
      step as ⟨i6, i6_post⟩
      have hi6 : i6.val = i.val * (p.a.val + 1) + 1 + h.val := by
        rw [i6_post, i4_post, i3_post, hi2, hi5]
      step as ⟨sibling, sibling_post⟩
      step*
      have hil' : i.val < idx.val.length := by simp; omega
      have hi8 : i7 = idx0.val[i.val]! := by
        rw [i7_post, ← getElem!_eq _ _ hil', (h3 _ (le_refl _)).2]
      have hpar : parent.val = (idx0.val[i.val]!).val / 2 := by
        rw [parent_post, ← hi8]; simp [Nat.shiftRight_eq_div_pow]
      have hi9 : i9.val = (idx0.val[i.val]!).val % 2 := by
        rw [i9_post, ← hi8]; simp [Nat.and_one_is_mod]
      have hadrs : adrsS adr = { adrsS adrs with word2 := h.val + 1, word3 := parent.val } := by
        simp [adrsS, adr_post, a4_post, i8_post]
      have hsib : bytes sibling.val = Spec.block (paramsS p) (bytes sig.val) (i.val * (p.a.val + 1) + 1 + h.val) := by
        rw [bytes_block (paramsS p) sig.val sibling.val i6.val (by rw [sibling_post, hp.n]), hi6]
      have hvl : i.val < vals.val.length := by simp; omega
      have hv0 : vals.val[i.val]! = vals0.val[i.val]! := (h3 _ (le_refl _)).1
      by_cases hc : i9 = 0#u32
      · simp only [hc, ↓reduceIte]
        have hev : (idx0.val[i.val]!).val % 2 = 0 := by rw [← hi9, hc]; rfl
        let* ⟨ v, v_post ⟩ ← Array.index_usize_spec
        let* ⟨ w, w_post ⟩ ← thash_pair_spec (paramsS p) hp.n hp.nok _ hs
        let* ⟨ vals1, vals1_post ⟩ ← Array.update_spec
        step*
        refine ⟨by scalar_tac, ?_, ?_, by scalar_tac⟩
        · intro t ht
          rw [i10_post] at ht
          rw [vals1_post, a5_post, Array.set_val_eq, Array.set_val_eq]
          rcases Nat.lt_succ_iff_lt_or_eq.mp ht with ht | ht
          · rw [getElem!_set_ne' _ _ _ _ (by omega), getElem!_set_ne' _ _ _ _ (by omega)]
            exact h2 t ht
          · subst ht
            rw [getElem!_set_self' _ _ _ (by simp; omega), getElem!_set_self' _ _ _ (by simp; omega)]
            refine ⟨?_, hpar⟩
            rw [w_post, hadrs, hpar, v_post, ← getElem!_eq _ _ hvl, hv0, hsib, pairMsg_even _ _ _ hev]
        · intro t ht
          rw [vals1_post, a5_post, Array.set_val_eq, Array.set_val_eq,
            getElem!_set_ne' _ _ _ _ (by scalar_tac), getElem!_set_ne' _ _ _ _ (by scalar_tac)]
          exact h3 t (by scalar_tac)
      · simp only [hc, ↓reduceIte]
        have hod : ¬ (idx0.val[i.val]!).val % 2 = 0 := by
          rw [← hi9]; intro h0; apply hc; scalar_tac
        let* ⟨ v, v_post ⟩ ← Array.index_usize_spec
        let* ⟨ w, w_post ⟩ ← thash_pair_spec (paramsS p) hp.n hp.nok _ hs
        let* ⟨ vals1, vals1_post ⟩ ← Array.update_spec
        step*
        refine ⟨by scalar_tac, ?_, ?_, by scalar_tac⟩
        · intro t ht
          rw [i10_post] at ht
          rw [vals1_post, a5_post, Array.set_val_eq, Array.set_val_eq]
          rcases Nat.lt_succ_iff_lt_or_eq.mp ht with ht | ht
          · rw [getElem!_set_ne' _ _ _ _ (by omega), getElem!_set_ne' _ _ _ _ (by omega)]
            exact h2 t ht
          · subst ht
            rw [getElem!_set_self' _ _ _ (by simp; omega), getElem!_set_self' _ _ _ (by simp; omega)]
            refine ⟨?_, hpar⟩
            rw [w_post, hadrs, hpar, v_post, ← getElem!_eq _ _ hvl, hv0, hsib, pairMsg_odd _ _ _ hod]
        · intro t ht
          rw [vals1_post, a5_post, Array.set_val_eq, Array.set_val_eq,
            getElem!_set_ne' _ _ _ _ (by scalar_tac), getElem!_set_ne' _ _ _ _ (by scalar_tac)]
          exact h3 t (by scalar_tac)
    · simp only [step_simps]
      have : i.val = k.val := by scalar_tac
      rw [this] at h2; exact h2
  · exact ⟨hi, hdone, hrest⟩

/-- One level of `Spec.climb`. -/
def forsClimbStep (P : Spec.Params) (leaf : Nat) (auth pk : Spec.Bytes) (adrs : Spec.Adrs)
    (st : Spec.Bytes × Nat) (j : Nat) : Spec.Bytes × Nat :=
  if (leaf / 2 ^ j) % 2 = 0 then
    (Spec.H P pk { adrs with word2 := j + 1, word3 := st.2 / 2 } (st.1 ++ Spec.block P auth j), st.2 / 2)
  else
    (Spec.H P pk { adrs with word2 := j + 1, word3 := (st.2 - 1) / 2 } (Spec.block P auth j ++ st.1),
      (st.2 - 1) / 2)

theorem fors_climb_eq (P : Spec.Params) (node : Spec.Bytes) (leaf ti : Nat) (auth : Spec.Bytes)
    (height : Nat) (pk : Spec.Bytes) (adrs : Spec.Adrs) :
    Spec.climb P node leaf ti auth height pk adrs =
      ((List.range height).foldl (forsClimbStep P leaf auth pk adrs) (node, ti)).1 := by
  unfold Spec.climb
  congr 2

/-- The authentication path of FORS tree `t` in a signature. -/
def forsAuthPath (P : Spec.Params) (sig : Spec.Bytes) (t : Nat) : Spec.Bytes :=
  (sig.drop ((t * (P.a + 1) + 1) * P.n)).take (P.a * P.n)

/-- Tree `t` of `fors_pkFromSig` after climbing `h` levels: the node and its tree index. -/
def forsClimbAt (P : Spec.Params) (sig pk : Spec.Bytes) (adrs : Spec.Adrs) (ind : List Nat)
    (t h : Nat) : Spec.Bytes × Nat :=
  (List.range h).foldl (forsClimbStep P ind[t]! (forsAuthPath P sig t) pk adrs)
    (Spec.F P pk { adrs with word2 := 0, word3 := forsLeaf P.a ind t } (Spec.block P sig (t * (P.a + 1))),
      forsLeaf P.a ind t)

theorem fors_block_auth (P : Spec.Params) (s : Spec.Bytes) (t j : Nat) (hj : j < P.a) :
    Spec.block P (forsAuthPath P s t) j = Spec.block P s (t * (P.a + 1) + 1 + j) := by
  rw [forsAuthPath, block_drop_take P s _ _ _ hj]

theorem forsRoot_eq (P : Spec.Params) (sig pk : Spec.Bytes) (adrs : Spec.Adrs) (ind : List Nat)
    (t : Nat) : forsRoot P sig pk adrs ind t = (forsClimbAt P sig pk adrs ind t P.a).1 := by
  rw [forsRoot, fors_climb_eq]; rfl

theorem fors_pk_from_sig_loop2_spec {N : Usize} (p : params.Params) (hp : PN p N) (sig : Slice U8)
    (seed : hash.Seed N) (hs : SeedOk seed)
    (adrs : address.Adrs) (k : Usize) (hk : k.val = p.k.val) (ind : List Nat)
    (hsig : sig.length = p.k.val * (1 + p.a.val) * N.val)
    (blocks : Array (Array U8 64#usize) 35#usize) (idx «end» : Array U32 35#usize)
    (vals : Array (Array U8 N) 35#usize) (h : U32) (hh : h.val ≤ p.a.val)
    (hinv : ∀ t, t < k.val →
      bytes (vals.val[t]!).val =
        (forsClimbAt (paramsS p) (bytes sig.val) (bytes seed.pk_seed.val) (adrsS adrs) ind t h.val).1 ∧
      (idx.val[t]!).val =
        (forsClimbAt (paramsS p) (bytes sig.val) (bytes seed.pk_seed.val) (adrsS adrs) ind t h.val).2 ∧
      (idx.val[t]!).val = t * 2 ^ (p.a.val - h.val) + ind[t]! / 2 ^ h.val) :
    fors.fors_pk_from_sig_loop2 sig seed.pk_seed seed.state seed.state512 adrs p.a k blocks idx «end»
      vals h ⦃ r =>
      ∀ t, t < k.val →
        bytes (r.val[t]!).val =
          (forsClimbAt (paramsS p) (bytes sig.val) (bytes seed.pk_seed.val) (adrsS adrs) ind t p.a.val).1 ⦄ := by
  have hv := hp.valid
  have ha14 : p.a.val ≤ 14 := hv.a_le
  have hk35 : p.k.val ≤ 35 := hv.k_le
  have hN32 := hp.le32
  unfold fors.fors_pk_from_sig_loop2
  apply loop.spec_decr_nat
    (measure := fun (q : Array (Array U8 64#usize) 35#usize × Array U32 35#usize ×
      Array U32 35#usize × Array (Array U8 N) 35#usize × U32) => p.a.val - q.2.2.2.2.val)
    (inv := fun q => q.2.2.2.2.val ≤ p.a.val ∧ ∀ t, t < k.val →
      bytes (q.2.2.2.1.val[t]!).val =
        (forsClimbAt (paramsS p) (bytes sig.val) (bytes seed.pk_seed.val) (adrsS adrs) ind t q.2.2.2.2.val).1 ∧
      (q.2.1.val[t]!).val =
        (forsClimbAt (paramsS p) (bytes sig.val) (bytes seed.pk_seed.val) (adrsS adrs) ind t q.2.2.2.2.val).2 ∧
      (q.2.1.val[t]!).val = t * 2 ^ (p.a.val - q.2.2.2.2.val) + ind[t]! / 2 ^ q.2.2.2.2.val)
  · rintro ⟨blocks, idx, «end», vals, h⟩ ⟨h1, h2⟩
    simp only [fors.fors_pk_from_sig_loop2.body]
    simp only at h1 h2
    simp only [step_simps]
    spec_split
    · have hha : h.val < p.a.val := by scalar_tac
      -- what one level does to tree `t`, given the new node value
      have hlevel : ∀ t, t < k.val → ∀ (newv : Spec.Bytes),
          newv = Spec.H (paramsS p) (bytes seed.pk_seed.val)
            { adrsS adrs with word2 := h.val + 1, word3 := (idx.val[t]!).val / 2 }
            (pairMsg (bytes (vals.val[t]!).val)
              (Spec.block (paramsS p) (bytes sig.val) (t * (p.a.val + 1) + 1 + h.val)) (idx.val[t]!).val) →
          newv = (forsClimbAt (paramsS p) (bytes sig.val) (bytes seed.pk_seed.val) (adrsS adrs) ind t (h.val + 1)).1 ∧
          (idx.val[t]!).val / 2 =
            (forsClimbAt (paramsS p) (bytes sig.val) (bytes seed.pk_seed.val) (adrsS adrs) ind t (h.val + 1)).2 ∧
          (idx.val[t]!).val / 2 = t * 2 ^ (p.a.val - (h.val + 1)) + ind[t]! / 2 ^ (h.val + 1) := by
        intro t ht newv hnew
        obtain ⟨hv, hti, hcl⟩ := h2 t ht
        have hpw : 2 ^ (p.a.val - h.val) = 2 * 2 ^ (p.a.val - (h.val + 1)) := by
          rw [← pow_succ']; congr 1; omega
        have hidx' : (idx.val[t]!).val = 2 * (t * 2 ^ (p.a.val - (h.val + 1))) + ind[t]! / 2 ^ h.val := by
          rw [hcl, hpw]; ring
        have hmod : (idx.val[t]!).val % 2 = (ind[t]! / 2 ^ h.val) % 2 := by rw [hidx']; omega
        have hdiv : (idx.val[t]!).val / 2 = t * 2 ^ (p.a.val - (h.val + 1)) + ind[t]! / 2 ^ (h.val + 1) := by
          rw [hidx', pow_succ, ← Nat.div_div_eq_div_mul]; omega
        have hstep : forsClimbAt (paramsS p) (bytes sig.val) (bytes seed.pk_seed.val) (adrsS adrs) ind t (h.val + 1) =
            forsClimbStep (paramsS p) ind[t]! (forsAuthPath (paramsS p) (bytes sig.val) t) (bytes seed.pk_seed.val)
              (adrsS adrs)
              (forsClimbAt (paramsS p) (bytes sig.val) (bytes seed.pk_seed.val) (adrsS adrs) ind t h.val) h.val := by
          simp only [forsClimbAt, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
        rw [hstep]
        by_cases hpar : (ind[t]! / 2 ^ h.val) % 2 = 0
        · simp only [forsClimbStep, hpar, ↓reduceIte]
          refine ⟨?_, by rw [hti], hdiv⟩
          rw [hnew, pairMsg_even _ _ _ (by omega), hv, ← hti, fors_block_auth _ _ _ _ hha]; rfl
        · simp only [forsClimbStep, hpar, ↓reduceIte]
          have hsub : ((idx.val[t]!).val - 1) / 2 = (idx.val[t]!).val / 2 := by omega
          refine ⟨?_, by rw [← hti, hsub], hdiv⟩
          rw [hnew, pairMsg_odd _ _ _ (by omega), hv, ← hti, hsub, fors_block_auth _ _ _ _ hha]; rfl
      split
      · rename_i h16
        subst h16
        let* ⟨ blocks1, idx1, end1, hQ ⟩ ← fors_pk_from_sig_loop2_loop0_spec p hp sig adrs k hk vals h hha
          hsig idx blocks idx «end» 0#usize (by simp) (by simp) (fun _ _ => rfl)
        step*
        have hsl : s.length = k.val := by rw [s_post1]; rfl
        have hs3 : s3.val.length = k.val := by
          have := s3_post; simp only [Slice.length] at this hsl; omega
        let* ⟨ vals1, vals1_post ⟩ ← fors_pk_from_sig_loop2_loop1_spec (by decide) k (by omega)
          (index_mut_back s3) vals 0#usize (Nat.zero_le _) (fun t ht => absurd ht (Nat.not_lt_zero t))
        let* ⟨ h1', h1'_post ⟩ ← U32.add_spec
        refine ⟨by rw [h1'_post]; omega, ?_, by rw [h1'_post]; omega⟩
        intro t ht
        obtain ⟨hb, hi1, he1⟩ := hQ t ht
        have hpkl : (bytes seed.pk_seed.val).length = 16 := by simp
        have hn16 : (paramsS p).n = 16 := by rw [hp.n]; rfl
        have hval : bytes (vals1.val[t]!).val = Spec.H (paramsS p) (bytes seed.pk_seed.val)
            { adrsS adrs with word2 := h.val + 1, word3 := (idx.val[t]!).val / 2 }
            (pairMsg (bytes (vals.val[t]!).val)
              (Spec.block (paramsS p) (bytes sig.val) (t * (p.a.val + 1) + 1 + h.val)) (idx.val[t]!).val) := by
          rw [vals1_post t ht, blkVal, s_post2, setSlice0_getElem! _ _ _ (by omega) (by simp; omega),
            s3_post1 t (by simp [Slice.length] at hsl ⊢; omega), s_post,
            slice0_getElem! _ _ _ ht (by simp; omega), s1_post, s2_post,
            Array.val_to_slice, Array.val_to_slice, hi1, he1, runBlock_one, hb, H_eq, if_pos hn16, hn16,
            seed_state seed hs]
          refine stepBlock_pair_value 16 (by decide) _ hpkl _ _ ?_
          have hbl : (Spec.block (paramsS p) (bytes sig.val) (t * (p.a.val + 1) + 1 + h.val)).length = 16 := by
            have hsb := fors_sib_bound p.a.val p.k.val 16 t h.val sig.length (by omega) hha hsig
            have hpn : p.n.val = 16 := by simpa using hn16
            simp [Spec.block, hpn]; simp only [Slice.length] at hsb; omega
          unfold pairMsg; split <;> simp [hbl]
        obtain ⟨e1, e2, e3⟩ := hlevel t ht _ hval
        rw [h1'_post]
        exact ⟨e1, by rw [hi1]; exact e2, by rw [hi1]; exact e3⟩
      · rename_i h16
        have hn16 : N.val ≠ 16 := fun h' => h16 (by scalar_tac)
        let* ⟨ idx1, vals1, hQ ⟩ ← fors_pk_from_sig_loop2_loop2_spec p hp sig seed.pk_seed seed.state
          seed.state512 hs adrs k hk vals idx h hha hsig idx vals 0#usize (by simp) (by simp)
          (fun _ _ => ⟨rfl, rfl⟩)
        let* ⟨ h1', h1'_post ⟩ ← U32.add_spec
        refine ⟨by rw [h1'_post]; omega, ?_, by rw [h1'_post]; omega⟩
        intro t ht
        obtain ⟨hval, hi1⟩ := hQ t ht
        obtain ⟨e1, e2, e3⟩ := hlevel t ht _ hval
        rw [h1'_post]
        exact ⟨e1, by rw [hi1]; exact e2, by rw [hi1]; exact e3⟩
    · simp only [step_simps]
      have : h.val = p.a.val := by scalar_tac
      intro t ht
      rw [← this]; exact (h2 t ht).1
  · exact ⟨hh, hinv⟩

@[step]
theorem fors_pk_from_sig_spec {N : Usize} (p : params.Params) (hp : PN p N) (sig md : Slice U8)
    (seed : hash.Seed N) (hs : SeedOk seed) (a : address.Adrs)
    (hsig : sig.length = p.k.val * (1 + p.a.val) * N.val) (hmd : md.length = (p.k.val * p.a.val + 7) / 8) :
    fors.fors_pk_from_sig p sig md seed a ⦃ r =>
      bytes r.val = Spec.forsPkFromSig (paramsS p) (bytes sig.val) (bytes md.val) (bytes seed.pk_seed.val)
        (adrsS a) ⦄ := by
  have hv := hp.valid
  have ha1 : 1 ≤ p.a.val := hv.a_pos
  have ha14 : p.a.val ≤ 14 := hv.a_le
  have hk35 : p.k.val ≤ 35 := hv.k_le
  have hN32 := hp.le32
  unfold fors.fors_pk_from_sig
  step as ⟨k, k_post⟩
  have hk : k.val = p.k.val := by rw [k_post]; simp
  step with base_2b_spec md p.a k (by omega) (by rw [hk, hmd]; omega) as ⟨indices, hind, hlenI, hbd⟩
  rw [hk] at hind hlenI
  let* ⟨ blocks1, idx1, end1, hL ⟩ ← fors_pk_from_sig_loop0_spec p hp sig a k hk indices hsig
    (by simpa using hlenI) hbd _ _ _ 0#usize (by simp) (by simp)
  step*
  have hsl : s.length = k.val := by rw [s_post1]; rfl
  have hs3 : s3.val.length = k.val := by
    have := s3_post; simp only [Slice.length] at this hsl; omega
  let* ⟨ vals1, vals1_post ⟩ ← fors_pk_from_sig_loop1_spec hN32 k (by omega) (index_mut_back s3)
    (Array.repeat 35#usize (Array.repeat N 0#u8)) 0#usize (by simp) (by simp)
  have hpkl : (bytes seed.pk_seed.val).length = (paramsS p).n := by rw [hp.n]; simp
  have h32 : (paramsS p).n ≤ 32 := by rw [hp.n]; exact hN32
  have h0 : ∀ t, t < k.val →
      bytes (vals1.val[t]!).val = (forsClimbAt (paramsS p) (bytes sig.val) (bytes seed.pk_seed.val)
        (adrsS a) (nats indices.val) t (0#u32).val).1 ∧
      (idx1.val[t]!).val = (forsClimbAt (paramsS p) (bytes sig.val) (bytes seed.pk_seed.val) (adrsS a)
        (nats indices.val) t (0#u32).val).2 ∧
      (idx1.val[t]!).val = t * 2 ^ (p.a.val - (0#u32).val) + (nats indices.val)[t]! / 2 ^ (0#u32).val := by
    intro t ht
    obtain ⟨hb, hi1, he1⟩ := hL t ht
    have hbl : (Spec.block (paramsS p) (bytes sig.val) (t * (p.a.val + 1))).length = (paramsS p).n := by
      have hsb := fors_sib_bound p.a.val p.k.val N.val t 0 sig.length (by omega) (by omega) hsig
      have e : (t * (p.a.val + 1) + 1 + 0 + 1) * N.val = t * (p.a.val + 1) * N.val + 2 * N.val := by ring
      rw [hp.n]; simp [Spec.block, hp.n_eq]; simp only [Slice.length] at hsb; omega
    have hF : ∀ (B : Spec.Adrs) (x : Spec.Bytes), (Spec.F (paramsS p) (bytes seed.pk_seed.val) B x).length =
        (paramsS p).n := fun B x => by rw [F_eq]; exact th256_length _ h32 _ hpkl _ _
    refine ⟨?_, ?_, ?_⟩
    · rw [vals1_post t ht, blkVal, s_post2, setSlice0_getElem! _ _ _ (by omega) (by simp; omega),
        s3_post1 t (by simp [Slice.length] at hsl ⊢; omega), s_post,
        slice0_getElem! _ _ _ ht (by simp; omega), s1_post, s2_post,
        Array.val_to_slice, Array.val_to_slice, hi1, he1, runBlock_one, hb, ← hp.n, seed_state seed hs,
        hp.n, ← hp.n, stepBlock_thash _ h32 _ hpkl _ _ hbl,
        block_value _ _ _ (by rw [hF]; omega), List.take_left' (hF _ _)]
      rfl
    · rw [hi1]; rfl
    · rw [hi1, forsLeaf]; simp
  let* ⟨ vals2, vals2_post ⟩ ← fors_pk_from_sig_loop2_spec p hp sig seed hs a k hk (nats indices.val)
    hsig (index_mut_back s3) idx1 end1 vals1 0#u32 (by simp) h0
  let* ⟨ roots, roots_post, roots_len ⟩ ← fors_pk_from_sig_loop3_spec hN32 k (by omega) vals2
    (alloc.vec.Vec.new U8) 0#usize (by simp) (by simp) (by simp)
  step as ⟨a0, a0_post, a0_eq⟩
  step as ⟨a1, a1_post⟩
  have hrl : roots.length ≤ 4096 := by
    rw [roots_len]; have := Nat.mul_le_mul hN32 (show k.val ≤ 35 by omega); omega
  step with thash_spec (paramsS p) hp.n hp.nok seed hs a1 roots.deref (by simpa using hrl) as ⟨r, r_post⟩
  rw [r_post, forsPkFromSig_eq, T_eq_H, T_eq_H]
  have hd : roots.deref.val = roots.val := by simp [alloc.vec.Vec.deref]
  have hind' : nats indices.val = Spec.base2b (bytes md.val) (paramsS p).a (paramsS p).k := by simpa using hind
  have hroots : (List.range k.val).flatMap (fun (t : Nat) => bytes (vals2.val[t]!).val) =
      (List.range (paramsS p).k).flatMap
        (forsRoot (paramsS p) (bytes sig.val) (bytes seed.pk_seed.val) (adrsS a) (nats indices.val)) := by
    rw [hk]
    exact List.flatMap_congr (fun t ht => by
      rw [vals2_post t (by have := List.mem_range.mp ht; omega), forsRoot_eq]; rfl)
  rw [hd, roots_post, hroots, hind']
  simp [adrsS, a1_post, a0_eq, Spec.Adrs.setTypeAndClear, Spec.FORS_ROOTS, fors_FORS_ROOTS_eq]

theorem fors_pk_gen_loop_spec {N : Usize} (p : params.Params) (hp : PN p N) (sk : Array U8 N)
    (seed : hash.Seed N) (hs : SeedOk seed) (a : address.Adrs) (roots : alloc.vec.Vec U8) (i : U32)
    (hi : i.val ≤ p.k.val) (hlen : roots.length = N.val * i.val)
    (hinv : bytes roots.val = (List.range i.val).flatMap fun t =>
      Spec.forsNode (paramsS p) (bytes sk.val) t p.a.val (bytes seed.pk_seed.val) (adrsS a)) :
    fors.fors_pk_gen_loop p sk seed a roots i ⦃ r =>
      bytes r.val = (List.range p.k.val).flatMap (fun t =>
        Spec.forsNode (paramsS p) (bytes sk.val) t p.a.val (bytes seed.pk_seed.val) (adrsS a)) ∧
      r.length = N.val * p.k.val ⦄ := by
  have hv := hp.valid
  have ha14 : p.a.val ≤ 14 := hv.a_le
  have hk35 : p.k.val ≤ 35 := hv.k_le
  have hN32 := hp.le32
  unfold fors.fors_pk_gen_loop
  apply loop.spec_decr_nat (measure := fun (q : alloc.vec.Vec U8 × U32) => p.k.val - q.2.val)
    (inv := fun q => q.2.val ≤ p.k.val ∧ q.1.length = N.val * q.2.val ∧
      bytes q.1.val = (List.range q.2.val).flatMap fun t =>
        Spec.forsNode (paramsS p) (bytes sk.val) t p.a.val (bytes seed.pk_seed.val) (adrsS a))
  · rintro ⟨roots, i⟩ ⟨h1, h2, h3⟩
    simp only [fors.fors_pk_gen_loop.body]
    simp only at h1 h2 h3
    split
    · rename_i hlt
      have hil : i.val < p.k.val := by scalar_tac
      have hb : N.val * i.val + N.val ≤ 32 * 35 := by
        have := Nat.mul_le_mul hN32 (show i.val + 1 ≤ 35 by omega); rw [Nat.mul_succ] at this; omega
      have hpow : (i.val + 1) * 2 ^ p.a.val < 2 ^ 32 := by
        have h1 : 2 ^ p.a.val ≤ 2 ^ 14 := Nat.pow_le_pow_right (by omega) ha14
        calc (i.val + 1) * 2 ^ p.a.val ≤ 35 * 2 ^ 14 := Nat.mul_le_mul (by omega) h1
          _ < 2 ^ 32 := by norm_num
      step with fors_node_spec p hp sk i p.a seed hs a hpow as ⟨root, root_post⟩
      step*
      refine ⟨by scalar_tac, ?_, ?_, by scalar_tac⟩
      · rw [roots1_post1, h2, s_post, i1_post, Nat.mul_succ]; simp
      · rw [roots1_post, bytes_append, h3, i1_post, fors_flatMap_range_succ _ i.val]
        simp [s_post, root_post]
    · simp only [step_simps]
      have : i.val = p.k.val := by scalar_tac
      rw [this] at h2 h3
      exact ⟨h3, h2⟩
  · exact ⟨hi, hlen, hinv⟩

@[step]
theorem fors_pk_gen_spec {N : Usize} (p : params.Params) (hp : PN p N) (sk : Array U8 N)
    (seed : hash.Seed N) (hs : SeedOk seed) (a : address.Adrs) :
    fors.fors_pk_gen p sk seed a ⦃ r =>
      bytes r.val = Spec.forsPkGen (paramsS p) (bytes sk.val) (bytes seed.pk_seed.val) (adrsS a) ⦄ := by
  have hk35 : p.k.val ≤ 35 := hp.valid.k_le
  have hN32 := hp.le32
  unfold fors.fors_pk_gen
  let* ⟨ roots, roots_post, roots_len ⟩ ← fors_pk_gen_loop_spec p hp sk seed hs a
    (alloc.vec.Vec.new U8) 0#u32 (by simp) (by simp) (by simp)
  step as ⟨a0, a0_post, a0_eq⟩
  step as ⟨a1, a1_post⟩
  have hrl : roots.length ≤ 4096 := by
    rw [roots_len]; have := Nat.mul_le_mul hN32 hk35; omega
  step with thash_spec (paramsS p) hp.n hp.nok seed hs a1 roots.deref (by simpa using hrl) as ⟨r, r_post⟩
  rw [r_post, Spec.forsPkGen]
  have hd : roots.deref.val = roots.val := by simp [alloc.vec.Vec.deref]
  rw [hd, roots_post]
  simp [adrsS, a1_post, a0_eq, Spec.Adrs.setTypeAndClear, Spec.FORS_ROOTS, fors_FORS_ROOTS_eq]

end slhdsa
