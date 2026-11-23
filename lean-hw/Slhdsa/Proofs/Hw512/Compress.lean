import Slhdsa.Proofs.Hw512.Rounds
import Slhdsa.Proofs.Hw512.Wrappers
open Aeneas Aeneas.Std Result

/-! The hardware SHA-512 compression function, `sha512::hw::compress_block`,
computes the SHA-512 compression function, given the instruction model in
`Arm.lean`, on a processor with the instructions: every statement that runs a
wrapper assumes `hw : Arm.haveSha512 = true` (see `Hw512/Wrappers.lean`). -/

namespace slhdsa
namespace H512
open Spec.SHA512 S512

/-! ## The wrappers, as `compress_block` uses them -/

@[step]
theorem load_words_spec (hw : Arm.haveSha512 = true) (w : Slice U64) (at' : Usize)
    (h : at'.val + 2 ≤ w.length) :
    sha512.hw.arm.load_words w at' ⦃ r => (r : Arm.V2) = vOf2 (S512.wv w.val) at'.val ⦄ := by
  unfold sha512.hw.arm.load_words
  rw [ite_eq_left hw, if_pos (by scalar_tac)]
  simp only [vOf2]
  rw [S512.wv_getElem! _ _ (by scalar_tac), S512.wv_getElem! _ _ (by scalar_tac),
    getElem!_eq _ _ (by scalar_tac), getElem!_eq _ _ (by scalar_tac)]
  exact (WP.spec_ok _).mpr rfl

@[step]
theorem load_be_spec (hw : Arm.haveSha512 = true) (b : Slice U8) (at' : Usize)
    (h : at'.val + 16 ≤ b.length) :
    sha512.hw.arm.load_be b at' ⦃ r => (r : Arm.V2) = beV2 (bytes b.val) at'.val ⦄ := by
  unfold sha512.hw.arm.load_be
  rw [ite_eq_left hw, if_pos (by scalar_tac)]
  simp only [beV2, word, Arm.beWord64, Nat.add_assoc, Nat.reduceAdd]
  have e : ∀ i, i < 16 → (b.val[at'.val + i]!).bv = (bytes b.val)[at'.val + i]! := by
    intro i hi
    rw [bytes_getElem! _ _ (by scalar_tac), getElem!_eq _ _ (by scalar_tac)]
  rw [e 0 (by omega), e 1 (by omega), e 2 (by omega), e 3 (by omega), e 4 (by omega),
    e 5 (by omega), e 6 (by omega), e 7 (by omega), e 8 (by omega), e 9 (by omega),
    e 10 (by omega), e 11 (by omega), e 12 (by omega), e 13 (by omega), e 14 (by omega),
    e 15 (by omega)]
  exact (WP.spec_ok _).mpr rfl

@[step]
theorem store_words_spec (hw : Arm.haveSha512 = true) (a b : core.core_arch.arm_shared.neon.uint64x2_t) :
    sha512.hw.arm.store_words a b ⦃ r => S512.wv r.val = vwords2 a ++ vwords2 b ∧ r.val.length = 4 ⦄ := by
  unfold sha512.hw.arm.store_words
  rw [if_pos hw]
  exact (WP.spec_ok _).mpr ⟨rfl, rfl⟩

@[step]
theorem add_spec (hw : Arm.haveSha512 = true) (a b : core.core_arch.arm_shared.neon.uint64x2_t) :
    sha512.hw.arm.add a b ⦃ r => (r : Arm.V2) = Arm.ADD2 a b ⦄ :=
  (wr512_add hw a b) ▸ (WP.spec_ok _).mpr rfl

@[step]
theorem ext1_spec (hw : Arm.haveSha512 = true) (a b : core.core_arch.arm_shared.neon.uint64x2_t) :
    sha512.hw.arm.ext1 a b ⦃ r => (r : Arm.V2) = Arm.EXT1 a b ⦄ :=
  (wr512_ext1 hw a b) ▸ (WP.spec_ok _).mpr rfl

@[step]
theorem sha512h_spec (hw : Arm.haveSha512 = true) (a b c : core.core_arch.arm_shared.neon.uint64x2_t) :
    sha512.hw.arm.sha512h a b c ⦃ r => (r : Arm.V2) = Arm.SHA512H a b c ⦄ :=
  (wr512_sha512h hw a b c) ▸ (WP.spec_ok _).mpr rfl

@[step]
theorem sha512h2_spec (hw : Arm.haveSha512 = true) (a b c : core.core_arch.arm_shared.neon.uint64x2_t) :
    sha512.hw.arm.sha512h2 a b c ⦃ r => (r : Arm.V2) = Arm.SHA512H2 a b c ⦄ :=
  (wr512_sha512h2 hw a b c) ▸ (WP.spec_ok _).mpr rfl

@[step]
theorem sha512su0_spec (hw : Arm.haveSha512 = true) (a b : core.core_arch.arm_shared.neon.uint64x2_t) :
    sha512.hw.arm.sha512su0 a b ⦃ r => (r : Arm.V2) = Arm.SHA512SU0 a b ⦄ :=
  (wr512_sha512su0 hw a b) ▸ (WP.spec_ok _).mpr rfl

@[step]
theorem sha512su1_spec (hw : Arm.haveSha512 = true) (a b c : core.core_arch.arm_shared.neon.uint64x2_t) :
    sha512.hw.arm.sha512su1 a b c ⦃ r => (r : Arm.V2) = Arm.SHA512SU1 a b c ⦄ :=
  (wr512_sha512su1 hw a b c) ▸ (WP.spec_ok _).mpr rfl

/-! ## The loop -/

theorem set_val' {α : Type} {n : Usize} (a : Std.Array α n) (i : Usize) (j : Nat)
    (hj : i.val = j) (x : α) : (a.set i x).val = a.val.set j x := by
  subst hj; simp [Array.set_val_eq]

theorem kstep_lt32 (ab cd ef gh : Arm.V2) (ml : List Arm.V2) (hl : ml.length = 8) (i : Nat)
    (hi : i < 32) :
    kstep ⟨ab, cd, ef, gh, ml⟩ i =
      let wk := Arm.ADD2 (ml[i % 8]'(by omega)) (vOf2 Spec.SHA512.K (2 * i))
      let t := Arm.SHA512H (Arm.ADD2 (Arm.EXT1 wk wk) gh) (Arm.EXT1 ef gh) (Arm.EXT1 cd ef)
      ⟨Arm.SHA512H2 t cd ab, ab, Arm.ADD2 cd t, ef,
        ml.set (i % 8) (Arm.SHA512SU1 (Arm.SHA512SU0 (ml[i % 8]'(by omega))
          (ml[(i + 1) % 8]'(by omega))) (ml[(i + 7) % 8]'(by omega))
          (Arm.EXT1 (ml[(i + 4) % 8]'(by omega)) (ml[(i + 5) % 8]'(by omega))))⟩ := by
  simp only [kstep, hi, ↓reduceIte]
  rw [getElem!_eq _ (i % 8) (by omega), getElem!_eq _ ((i + 1) % 8) (by omega),
    getElem!_eq _ ((i + 7) % 8) (by omega), getElem!_eq _ ((i + 4) % 8) (by omega),
    getElem!_eq _ ((i + 5) % 8) (by omega)]

theorem kstep_ge32 (ab cd ef gh : Arm.V2) (ml : List Arm.V2) (hl : ml.length = 8) (i : Nat)
    (hi : ¬ i < 32) :
    kstep ⟨ab, cd, ef, gh, ml⟩ i =
      let wk := Arm.ADD2 (ml[i % 8]'(by omega)) (vOf2 Spec.SHA512.K (2 * i))
      let t := Arm.SHA512H (Arm.ADD2 (Arm.EXT1 wk wk) gh) (Arm.EXT1 ef gh) (Arm.EXT1 cd ef)
      ⟨Arm.SHA512H2 t cd ab, ab, Arm.ADD2 cd t, ef, ml⟩ := by
  simp only [kstep, hi, ↓reduceIte]
  rw [getElem!_eq _ (i % 8) (by omega)]

abbrev V64 := core.core_arch.arm_shared.neon.uint64x2_t

theorem compress_block_loop_spec (hw : Arm.haveSha512 = true) (s0 : KState)
    (m : Array V64 8#usize) (ab cd ef gh : V64) (i : Usize) (hi : i.val ≤ 40)
    (hinv : (⟨ab, cd, ef, gh, m.val⟩ : KState) = (List.range i.val).foldl kstep s0) :
    sha512.hw.compress_block_loop m ab cd ef gh i ⦃ r =>
      (r.1 : Arm.V2) = ((List.range 40).foldl kstep s0).ab ∧
      (r.2.1 : Arm.V2) = ((List.range 40).foldl kstep s0).cd ∧
      (r.2.2.1 : Arm.V2) = ((List.range 40).foldl kstep s0).ef ∧
      (r.2.2.2 : Arm.V2) = ((List.range 40).foldl kstep s0).gh ⦄ := by
  unfold sha512.hw.compress_block_loop
  apply loop.spec_decr_nat
    (measure := fun (p : Array V64 8#usize × V64 × V64 × V64 × V64 × Usize) => 40 - p.2.2.2.2.2.val)
    (inv := fun p => p.2.2.2.2.2.val ≤ 40 ∧
      (⟨p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.1.val⟩ : KState) =
        (List.range p.2.2.2.2.2.val).foldl kstep s0)
  · rintro ⟨m, ab, cd, ef, gh, i⟩ ⟨hi, hinv⟩
    simp only [sha512.hw.compress_block_loop.body]
    simp only at hi hinv
    step*
    · rename_i h40 h32
      refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      have hK : S512.wv sha512.K.to_slice.val = Spec.SHA512.K := by simpa using S512.K_eq
      rw [i3_post, List.range_succ, List.foldl_append, ← hinv]
      simp only [List.foldl_cons, List.foldl_nil]
      subst a_post uxt12_post uxt7_post uxt5_post uxt6_post uxt8_post uxt9_post uxt10_post
        uxt11_post ab2_post ef2_post t_post sum_post uxt2_post uxt3_post uxt4_post wk_post
        uxt_post uxt1_post s_post
      simp only [hK, i1_post, i2_post, i4_post, i6_post, i8_post, i10_post, i3_post,
        i5_post, i7_post, i9_post]
      refine Eq.trans ?_ (kstep_lt32 ab cd ef gh m.val m.property i.val (by scalar_tac)).symm
      congr 1
      exact set_val' m i1 _ i1_post _
    · rename_i h40 h32
      refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      have hK : S512.wv sha512.K.to_slice.val = Spec.SHA512.K := by simpa using S512.K_eq
      rw [i3_post, List.range_succ, List.foldl_append, ← hinv]
      simp only [List.foldl_cons, List.foldl_nil]
      subst ab2_post ef2_post t_post sum_post uxt2_post uxt3_post uxt4_post wk_post
        uxt_post uxt1_post s_post
      simp only [hK, i1_post, i2_post]
      exact (kstep_ge32 ab cd ef gh m.val m.property i.val (by scalar_tac)).symm
  · exact ⟨hi, hinv⟩

theorem list44 (l m : List U64) (hl : l.length = 4) (hm : m.length = 4) :
    [l[0]'(by omega), l[1]'(by omega), l[2]'(by omega), l[3]'(by omega),
      m[0]'(by omega), m[1]'(by omega), m[2]'(by omega), m[3]'(by omega)] = l ++ m := by
  match l, m, hl, hm with
  | [_, _, _, _], [_, _, _, _], _, _ => rfl

end H512

open Spec.SHA512 S512 H512 in
/-- **The hardware SHA-512 compression function is the SHA-512 compression
function** of FIPS 180-4 on the block, on a processor with the instructions. -/
theorem hw_compress_block512_spec (hw : Arm.haveSha512 = true) (state : Array U64 8#usize)
    (block : Array U8 128#usize) :
    sha512.hw.compress_block state block ⦃ r =>
      S512.wv r.val = Spec.SHA512.compress (S512.wv state.val) (bytes block.val) ⦄ := by
  unfold sha512.hw.compress_block
  step*
  step with H512.compress_block_loop_spec hw ⟨ab0, cd0, ef0, gh0, [uxt, uxt1, uxt2, uxt3, uxt4, uxt5, uxt6, uxt7]⟩
    as ⟨ab, cd, ef, gh, h1, h2, h3, h4⟩
  · rfl
  step*
  show S512.wv [i, i1, i2, i3, i4, i5, i6, i7] = _
  subst i_post i1_post i2_post i3_post i4_post i5_post i6_post i7_post
  rw [list44 _ _ lo_post1 hi_post1, S512.wv, List.map_append, ← S512.wv, ← S512.wv, lo_post, hi_post]
  subst uxt8_post uxt9_post uxt10_post uxt11_post
  rw [h1, h2, h3, h4]
  subst ab0_post cd0_post ef0_post gh0_post uxt_post uxt1_post uxt2_post uxt3_post uxt4_post uxt5_post
    uxt6_post uxt7_post
  subst s_post s1_post s2_post s3_post s4_post s5_post s6_post s7_post s8_post s9_post s10_post s11_post
  have := H512.kcompress_eq (S512.wv state.val) (bytes block.val)
  simp only [H512.kcompress, H512.blockVs] at this
  simp only [Array.val_to_slice]
  rw [← this, List.append_assoc]

end slhdsa
