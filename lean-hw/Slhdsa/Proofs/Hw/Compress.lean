import Slhdsa.Proofs.Hw.Rounds
open Aeneas Aeneas.Std Result

/-! The hardware compression function, `sha256::hw::compress_block`, computes
the SHA-256 compression function, given the instruction model in `Arm.lean`,
on a processor with the instructions: every statement that runs a wrapper
assumes `hw : Arm.haveSha2 = true` (see `Hw/Wrappers.lean`). -/

namespace slhdsa
open Spec.SHA256

/-! ## The wrappers, as `compress_block` uses them -/

@[step]
theorem load_words_spec (hw : Arm.haveSha2 = true) (w : Slice U32) (at' : Usize) (h : at'.val + 4 ≤ w.length) :
    sha256.hw.arm.load_words w at' ⦃ r => (r : Arm.V) = vOf (wv w.val) at'.val ⦄ := by
  unfold sha256.hw.arm.load_words
  rw [if_pos hw, if_pos (by scalar_tac)]
  simp only [vOf]
  rw [wv_getElem! _ _ (by scalar_tac), wv_getElem! _ _ (by scalar_tac),
    wv_getElem! _ _ (by scalar_tac), wv_getElem! _ _ (by scalar_tac),
    getElem!_eq _ _ (by scalar_tac), getElem!_eq _ _ (by scalar_tac),
    getElem!_eq _ _ (by scalar_tac), getElem!_eq _ _ (by scalar_tac)]
  exact (WP.spec_ok _).mpr rfl

@[step]
theorem load_be_spec (hw : Arm.haveSha2 = true) (b : Slice U8) (at' : Usize) (h : at'.val + 16 ≤ b.length) :
    sha256.hw.arm.load_be b at' ⦃ r => (r : Arm.V) = beV (bytes b.val) at'.val ⦄ := by
  unfold sha256.hw.arm.load_be
  rw [if_pos hw, if_pos (by scalar_tac)]
  simp only [beV, word, Arm.beWord, Nat.add_assoc, Nat.reduceAdd]
  have e : ∀ i, i < 16 → (b.val[at'.val + i]!).bv = (bytes b.val)[at'.val + i]! := by
    intro i hi
    rw [bytes_getElem! _ _ (by scalar_tac), getElem!_eq _ _ (by scalar_tac)]
  rw [e 0 (by omega), e 1 (by omega), e 2 (by omega), e 3 (by omega), e 4 (by omega),
    e 5 (by omega), e 6 (by omega), e 7 (by omega), e 8 (by omega), e 9 (by omega),
    e 10 (by omega), e 11 (by omega), e 12 (by omega), e 13 (by omega), e 14 (by omega),
    e 15 (by omega)]
  exact (WP.spec_ok _).mpr rfl

@[step]
theorem store_words_spec (hw : Arm.haveSha2 = true) (a e : core.core_arch.arm_shared.neon.uint32x4_t) :
    sha256.hw.arm.store_words a e ⦃ r => wv r.val = vwords a ++ vwords e ⦄ := by
  unfold sha256.hw.arm.store_words
  rw [if_pos hw]
  exact (WP.spec_ok _).mpr rfl

@[step]
theorem add_spec (hw : Arm.haveSha2 = true) (a b : core.core_arch.arm_shared.neon.uint32x4_t) :
    sha256.hw.arm.add a b ⦃ r => (r : Arm.V) = Arm.ADD a b ⦄ :=
  (wr_add hw a b) ▸ (WP.spec_ok _).mpr rfl

@[step]
theorem sha256h_spec (hw : Arm.haveSha2 = true) (a b w : core.core_arch.arm_shared.neon.uint32x4_t) :
    sha256.hw.arm.sha256h a b w ⦃ r => (r : Arm.V) = Arm.SHA256H a b w ⦄ :=
  (wr_sha256h hw a b w) ▸ (WP.spec_ok _).mpr rfl

@[step]
theorem sha256h2_spec (hw : Arm.haveSha2 = true) (a b w : core.core_arch.arm_shared.neon.uint32x4_t) :
    sha256.hw.arm.sha256h2 a b w ⦃ r => (r : Arm.V) = Arm.SHA256H2 a b w ⦄ :=
  (wr_sha256h2 hw a b w) ▸ (WP.spec_ok _).mpr rfl

@[step]
theorem sha256su0_spec (hw : Arm.haveSha2 = true) (a b : core.core_arch.arm_shared.neon.uint32x4_t) :
    sha256.hw.arm.sha256su0 a b ⦃ r => (r : Arm.V) = Arm.SHA256SU0 a b ⦄ :=
  (wr_sha256su0 hw a b) ▸ (WP.spec_ok _).mpr rfl

@[step]
theorem sha256su1_spec (hw : Arm.haveSha2 = true) (a b c : core.core_arch.arm_shared.neon.uint32x4_t) :
    sha256.hw.arm.sha256su1 a b c ⦃ r => (r : Arm.V) = Arm.SHA256SU1 a b c ⦄ :=
  (wr_sha256su1 hw a b c) ▸ (WP.spec_ok _).mpr rfl

/-! ## The loop -/

theorem set_val' {α : Type} {n : Usize} (a : Std.Array α n) (i : Usize) (j : Nat)
    (hj : i.val = j) (x : α) : (a.set i x).val = a.val.set j x := by
  subst hj; simp [Array.set_val_eq]

theorem kstep_lt12 (abcd efgh : Arm.V) (ml : List Arm.V) (hl : ml.length = 4) (i : Nat)
    (hi : i < 12) :
    kstep ⟨abcd, efgh, ml⟩ i =
      ⟨Arm.SHA256H abcd efgh (Arm.ADD (ml[i % 4]'(by omega)) (vOf K (4 * i))),
        Arm.SHA256H2 efgh abcd (Arm.ADD (ml[i % 4]'(by omega)) (vOf K (4 * i))),
        ml.set (i % 4) (Arm.SHA256SU1 (Arm.SHA256SU0 (ml[i % 4]'(by omega))
          (ml[(i + 1) % 4]'(by omega))) (ml[(i + 2) % 4]'(by omega)) (ml[(i + 3) % 4]'(by omega)))⟩ := by
  simp only [kstep, hi, ↓reduceIte]
  rw [getElem!_eq _ (i % 4) (by omega), getElem!_eq _ ((i + 1) % 4) (by omega),
    getElem!_eq _ ((i + 2) % 4) (by omega), getElem!_eq _ ((i + 3) % 4) (by omega)]

theorem kstep_ge12 (abcd efgh : Arm.V) (ml : List Arm.V) (hl : ml.length = 4) (i : Nat)
    (hi : ¬ i < 12) :
    kstep ⟨abcd, efgh, ml⟩ i =
      ⟨Arm.SHA256H abcd efgh (Arm.ADD (ml[i % 4]'(by omega)) (vOf K (4 * i))),
        Arm.SHA256H2 efgh abcd (Arm.ADD (ml[i % 4]'(by omega)) (vOf K (4 * i))), ml⟩ := by
  simp only [kstep, hi, ↓reduceIte]
  rw [getElem!_eq _ (i % 4) (by omega)]

theorem compress_block_loop_spec (hw : Arm.haveSha2 = true) (s0 : KState) (abcd efgh : core.core_arch.arm_shared.neon.uint32x4_t)
    (m : Array core.core_arch.arm_shared.neon.uint32x4_t 4#usize) (i : Usize) (hi : i.val ≤ 16)
    (hinv : (⟨abcd, efgh, m.val⟩ : KState) = (List.range i.val).foldl kstep s0) :
    sha256.hw.compress_block_loop abcd efgh m i ⦃ r =>
      (r.1 : Arm.V) = ((List.range 16).foldl kstep s0).abcd ∧
      (r.2 : Arm.V) = ((List.range 16).foldl kstep s0).efgh ⦄ := by
  unfold sha256.hw.compress_block_loop
  apply loop.spec_decr_nat
    (measure := fun (p : core.core_arch.arm_shared.neon.uint32x4_t ×
      core.core_arch.arm_shared.neon.uint32x4_t ×
      Array core.core_arch.arm_shared.neon.uint32x4_t 4#usize × Usize) => 16 - p.2.2.2.val)
    (inv := fun p => p.2.2.2.val ≤ 16 ∧
      (⟨p.1, p.2.1, p.2.2.1.val⟩ : KState) = (List.range p.2.2.2.val).foldl kstep s0)
  · rintro ⟨abcd, efgh, m, i⟩ ⟨hi, hinv⟩
    simp only [sha256.hw.compress_block_loop.body]
    simp only at hi hinv
    step*
    · rename_i h16 h12
      refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      have hK : wv sha256.K.to_slice.val = K := by simpa using K_eq
      rw [i3_post, List.range_succ, List.foldl_append, ← hinv]
      simp only [List.foldl_cons, List.foldl_nil]
      subst a_post uxt7_post uxt4_post uxt2_post uxt3_post uxt5_post uxt6_post abcd1_post
        efgh1_post w_post uxt_post uxt1_post s_post
      simp only [hK, i1_post, i2_post, i4_post, i6_post, i8_post, i3_post,
        i5_post, i7_post]
      refine Eq.trans ?_ (kstep_lt12 abcd efgh m.val m.property i.val (by scalar_tac)).symm
      congr 1
      exact set_val' m i1 _ i1_post _
    · rename_i h16 h12
      refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      have hK : wv sha256.K.to_slice.val = K := by simpa using K_eq
      rw [i3_post, List.range_succ, List.foldl_append, ← hinv]
      simp only [List.foldl_cons, List.foldl_nil]
      subst abcd1_post efgh1_post w_post uxt_post uxt1_post s_post
      simp only [hK, i1_post, i2_post]
      exact (kstep_ge12 abcd efgh m.val m.property i.val (by scalar_tac)).symm
  · exact ⟨hi, hinv⟩

theorem hw_compress_block_spec (hw : Arm.haveSha2 = true) (state : Array U32 8#usize) (block : Array U8 64#usize) :
    sha256.hw.compress_block state block ⦃ r =>
      wv r.val = compress (wv state.val) (bytes block.val) ⦄ := by
  unfold sha256.hw.compress_block
  step*
  step with compress_block_loop_spec hw ⟨abcd0, efgh0, [m0, m1, m2, m3]⟩ as ⟨abcd, efgh, h1, h2⟩
  · rfl
  step*
  rw [r_post]
  subst uxt_post uxt1_post
  rw [h1, h2]
  subst abcd0_post efgh0_post m0_post m1_post m2_post m3_post
  have := kcompress_eq (wv state.val) (by simp) (bytes block.val) (by simp)
  simp only [kcompress] at this
  subst s_post s1_post s2_post s3_post s4_post s5_post
  simp only [Array.val_to_slice]
  exact this

end slhdsa
