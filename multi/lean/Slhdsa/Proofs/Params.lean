import Slhdsa.Proofs.Basic
open Aeneas Aeneas.Std Result

/-! Parameter sets: the derived quantities, and the six instances. -/

namespace slhdsa

/-! ## Derived quantities of the specification under `Valid` -/

theorem w_eq (p : params.Params) : (paramsS p).w = 16 := by
  simp [Spec.Params.w]

theorem len1_eq (p : params.Params) (_hv : (paramsS p).Valid) : (paramsS p).len1 = 2 * p.n.val := by
  simp only [Spec.Params.len1, paramsS_n, paramsS_lgw]
  omega

theorem len2_eq (p : params.Params) (hv : (paramsS p).Valid) : (paramsS p).len2 = 3 := by
  have h1 := len1_eq p hv
  have hn := hv.n_cases
  simp only [paramsS_n] at hn
  simp only [Spec.Params.len2, h1, w_eq, paramsS_lgw]
  rcases hn with hn | hn | hn
  · have : Nat.log2 (2 * p.n.val * (16 - 1)) = 8 := by
      rw [hn]; exact (Nat.log2_eq_iff (by norm_num)).2 (by norm_num)
    rw [this]
  · have : Nat.log2 (2 * p.n.val * (16 - 1)) = 9 := by
      rw [hn]; exact (Nat.log2_eq_iff (by norm_num)).2 (by norm_num)
    rw [this]
  · have : Nat.log2 (2 * p.n.val * (16 - 1)) = 9 := by
      rw [hn]; exact (Nat.log2_eq_iff (by norm_num)).2 (by norm_num)
    rw [this]

theorem len_eq (p : params.Params) (hv : (paramsS p).Valid) : (paramsS p).len = 2 * p.n.val + 3 := by
  simp [Spec.Params.len, len1_eq p hv, len2_eq p hv]

/-- `h / d = h'`. -/
theorem h_div_d (p : params.Params) (hv : (paramsS p).Valid) : p.h.val / p.d.val = p.hp.val := by
  have h1 := hv.h_eq
  have h2 := hv.d_ge
  simp only [paramsS_h, paramsS_d, paramsS_hp] at h1 h2
  rw [h1]
  exact Nat.mul_div_cancel_left _ (by omega)

/-- The signature size of Figure 17 is `n` plus the FORS and hypertree parts. -/
theorem sigBytes_eq (p : params.Params) (hv : (paramsS p).Valid) :
    (paramsS p).sigBytes =
      p.n.val + (paramsS p).forsSigBytes + p.d.val * (paramsS p).xmssSigBytes := by
  have h1 := hv.h_eq
  simp only [paramsS_h, paramsS_d, paramsS_hp] at h1
  simp only [Spec.Params.sigBytes, Spec.Params.forsSigBytes, Spec.Params.xmssSigBytes,
    paramsS_n, paramsS_h, paramsS_d, paramsS_hp, paramsS_a, paramsS_k, h1]
  ring

/-- The `Valid` bounds as facts about the machine fields. -/
theorem valid_bounds (p : params.Params) (hv : (paramsS p).Valid) :
    (p.n.val = 16 ∨ p.n.val = 24 ∨ p.n.val = 32) ∧ 2 ≤ p.d.val ∧ p.d.val ≤ 22 ∧
    1 ≤ p.hp.val ∧ p.hp.val ≤ 9 ∧ p.h.val = p.d.val * p.hp.val ∧ p.h.val - p.hp.val ≤ 64 ∧
    1 ≤ p.a.val ∧ p.a.val ≤ 14 ∧ 1 ≤ p.k.val ∧ p.k.val ≤ 35 ∧
    p.hp.val ≤ p.h.val - p.hp.val ∧ p.k.val * p.a.val ≤ 490 ∧
    p.k.val * (1 + p.a.val) ≤ 525 := by
  have h1 := hv.n_cases
  have h2 := hv.d_ge
  have h3 := hv.d_le
  have h4 := hv.hp_pos
  have h5 := hv.hp_le
  have h6 := hv.h_eq
  have h7 := hv.tree_le
  have h8 := hv.a_pos
  have h9 := hv.a_le
  have h10 := hv.k_pos
  have h11 := hv.k_le
  simp only [paramsS_n, paramsS_h, paramsS_d, paramsS_hp, paramsS_a, paramsS_k] at *
  have h12 : 2 * p.hp.val ≤ p.d.val * p.hp.val := Nat.mul_le_mul_right _ h2
  have h13 : p.k.val * p.a.val ≤ 35 * 14 := Nat.mul_le_mul h11 h9
  have h14 : p.k.val * (1 + p.a.val) ≤ 35 * 15 := Nat.mul_le_mul h11 (by omega)
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, ?_, ?_, ?_⟩ <;> omega

/-! ## The Rust accessors -/

@[step]
theorem len1_spec (p : params.Params) (hv : (paramsS p).Valid) :
    params.Params.len1 p ⦃ r => r.val = 2 * p.n.val ∧ r.val = (paramsS p).len1 ⦄ := by
  unfold params.Params.len1
  obtain ⟨hn, -⟩ := valid_bounds p hv
  have hn32 : p.n.val ≤ 32 := by omega
  rw [len1_eq p hv]
  step*

@[step]
theorem len_spec (p : params.Params) (hv : (paramsS p).Valid) :
    params.Params.len p ⦃ r => r.val = 2 * p.n.val + 3 ∧ r.val = (paramsS p).len ⦄ := by
  unfold params.Params.len
  obtain ⟨hn, -⟩ := valid_bounds p hv
  have hn32 : p.n.val ≤ 32 := by omega
  rw [len_eq p hv]
  simp only [global_simps]
  step*

@[step]
theorem md_bytes_spec (p : params.Params) (hv : (paramsS p).Valid) :
    params.Params.md_bytes p ⦃ r => r.val = (p.k.val * p.a.val + 7) / 8 ∧
      r.val = (paramsS p).mdBytes ⦄ := by
  unfold params.Params.md_bytes
  obtain ⟨hn, hd2, hd, hp1, hp, hh, ht, ha1, ha, hk1, hk, hhp, hka, hka1⟩ := valid_bounds p hv
  have hn32 : p.n.val ≤ 32 := by omega
  simp only [Spec.Params.mdBytes, paramsS_k, paramsS_a]
  step*

@[step]
theorem tree_bits_spec (p : params.Params) (hv : (paramsS p).Valid) :
    params.Params.tree_bits p ⦃ r => r.val = p.h.val - p.hp.val ∧
      r.val = p.h.val - p.h.val / p.d.val ∧ 1 ≤ r.val ∧ r.val ≤ 64 ⦄ := by
  unfold params.Params.tree_bits
  obtain ⟨hn, hd2, hd, hp1, hp, hh, ht, ha1, ha, hk1, hk, hhp, hka, hka1⟩ := valid_bounds p hv
  have hn32 : p.n.val ≤ 32 := by omega
  rw [h_div_d p hv]
  step*

@[step]
theorem tree_bytes_spec (p : params.Params) (hv : (paramsS p).Valid) :
    params.Params.tree_bytes p ⦃ r => r.val = (p.h.val - p.hp.val + 7) / 8 ∧
      r.val = (paramsS p).treeBytes ∧ 1 ≤ r.val ∧ r.val ≤ 8 ⦄ := by
  unfold params.Params.tree_bytes
  obtain ⟨hn, hd2, hd, hp1, hp, hh, ht, ha1, ha, hk1, hk, hhp, hka, hka1⟩ := valid_bounds p hv
  have hn32 : p.n.val ≤ 32 := by omega
  simp only [Spec.Params.treeBytes, paramsS_h, paramsS_d, h_div_d p hv]
  step*
  have : (UScalar.cast UScalarTy.Usize i2).val = i2.val := by
    rw [UScalar.cast_val_eq]; apply Nat.mod_eq_of_lt; scalar_tac
  scalar_tac

@[step]
theorem leaf_bytes_spec (p : params.Params) (hv : (paramsS p).Valid) :
    params.Params.leaf_bytes p ⦃ r => r.val = (p.hp.val + 7) / 8 ∧
      r.val = (paramsS p).leafBytes ∧ 1 ≤ r.val ∧ r.val ≤ 2 ⦄ := by
  unfold params.Params.leaf_bytes
  obtain ⟨hn, hd2, hd, hp1, hp, hh, ht, ha1, ha, hk1, hk, hhp, hka, hka1⟩ := valid_bounds p hv
  have hn32 : p.n.val ≤ 32 := by omega
  simp only [Spec.Params.leafBytes, paramsS_h, paramsS_d, h_div_d p hv]
  step*
  have : (UScalar.cast UScalarTy.Usize i1).val = i1.val := by
    rw [UScalar.cast_val_eq]; apply Nat.mod_eq_of_lt; scalar_tac
  scalar_tac

@[step]
theorem xmss_sig_bytes_spec (p : params.Params) (hv : (paramsS p).Valid) :
    params.Params.xmss_sig_bytes p ⦃ r => r.val = (2 * p.n.val + 3 + p.hp.val) * p.n.val ∧
      r.val = (paramsS p).xmssSigBytes ⦄ := by
  unfold params.Params.xmss_sig_bytes
  obtain ⟨hn, hd2, hd, hp1, hp, hh, ht, ha1, ha, hk1, hk, hhp, hka, hka1⟩ := valid_bounds p hv
  have hn32 : p.n.val ≤ 32 := by omega
  simp only [Spec.Params.xmssSigBytes, len_eq p hv, paramsS_hp, paramsS_n]
  let* ⟨ i, i_post, i_post' ⟩ ← len_spec
  have hc : (UScalar.cast UScalarTy.Usize p.hp).val = p.hp.val := by
    rw [UScalar.cast_val_eq]; apply Nat.mod_eq_of_lt; scalar_tac
  let* ⟨ i1, i1_post ⟩ ← UScalar.cast_inBounds_spec
  let* ⟨ i2, i2_post ⟩ ← Usize.add_spec
  have hm : i2.val * p.n.val ≤ 76 * 32 := Nat.mul_le_mul (by scalar_tac) hn32
  let* ⟨ r, r_post ⟩ ← Usize.mul_spec
  simp [r_post, i2_post, i_post, i1_post]

@[step]
theorem fors_sig_bytes_spec (p : params.Params) (hv : (paramsS p).Valid) :
    params.Params.fors_sig_bytes p ⦃ r => r.val = p.k.val * (1 + p.a.val) * p.n.val ∧
      r.val = (paramsS p).forsSigBytes ⦄ := by
  unfold params.Params.fors_sig_bytes
  obtain ⟨hn, hd2, hd, hp1, hp, hh, ht, ha1, ha, hk1, hk, hhp, hka, hka1⟩ := valid_bounds p hv
  have hn32 : p.n.val ≤ 32 := by omega
  simp only [Spec.Params.forsSigBytes, paramsS_a, paramsS_k, paramsS_n]
  let* ⟨ i, i_post ⟩ ← U32.add_spec
  have hi1 : p.k.val * i.val ≤ 525 := by rw [i_post]; exact hka1
  let* ⟨ i1, i1_post ⟩ ← U32.mul_spec
  have hc : (UScalar.cast UScalarTy.Usize i1).val = i1.val := by
    rw [UScalar.cast_val_eq]; apply Nat.mod_eq_of_lt; scalar_tac
  let* ⟨ i2, i2_post ⟩ ← UScalar.cast_inBounds_spec
  have hm : i2.val * p.n.val ≤ 525 * 32 := Nat.mul_le_mul (by scalar_tac) hn32
  let* ⟨ r, r_post ⟩ ← Usize.mul_spec
  simp [r_post, i2_post, i1_post, i_post]

@[step]
theorem sig_bytes_spec (p : params.Params) (hv : (paramsS p).Valid) :
    params.Params.sig_bytes p ⦃ r => r.val = (paramsS p).sigBytes ∧
      r.val = p.n.val + (paramsS p).forsSigBytes + p.d.val * (paramsS p).xmssSigBytes ⦄ := by
  unfold params.Params.sig_bytes
  obtain ⟨hn, hd2, hd, hp1, hp, hh, ht, ha1, ha, hk1, hk, hhp, hka, hka1⟩ := valid_bounds p hv
  have hn32 : p.n.val ≤ 32 := by omega
  rw [sigBytes_eq p hv]
  let* ⟨ i, i_post, i_post' ⟩ ← fors_sig_bytes_spec
  have hi : i.val ≤ 525 * 32 := by
    rw [i_post]; exact Nat.mul_le_mul hka1 (by omega)
  let* ⟨ i1, i1_post ⟩ ← Usize.add_spec
  let* ⟨ i2, i2_post ⟩ ← UScalar.cast_inBounds_spec
  let* ⟨ i3, i3_post, i3_post' ⟩ ← xmss_sig_bytes_spec
  have hi3 : i3.val ≤ 76 * 32 := by
    rw [i3_post]; exact Nat.mul_le_mul (by omega) (by omega)
  have hm : i2.val * i3.val ≤ 22 * (76 * 32) := by
    rw [i2_post]; exact Nat.mul_le_mul hd hi3
  let* ⟨ i4, i4_post ⟩ ← Usize.mul_spec
  let* ⟨ r, r_post ⟩ ← Usize.add_spec
  simp [r_post, i4_post, i1_post, i2_post, ← i_post', ← i3_post']

/-! ## The six parameter sets of the crate are those of Table 2, and valid -/

theorem paramsS_128s : paramsS params.SHA2_128S = Spec.sha2_128s := by
  simp [paramsS, global_simps, Spec.sha2_128s]
theorem paramsS_128f : paramsS params.SHA2_128F = Spec.sha2_128f := by
  simp [paramsS, global_simps, Spec.sha2_128f]
theorem paramsS_192s : paramsS params.SHA2_192S = Spec.sha2_192s := by
  simp [paramsS, global_simps, Spec.sha2_192s]
theorem paramsS_192f : paramsS params.SHA2_192F = Spec.sha2_192f := by
  simp [paramsS, global_simps, Spec.sha2_192f]
theorem paramsS_256s : paramsS params.SHA2_256S = Spec.sha2_256s := by
  simp [paramsS, global_simps, Spec.sha2_256s]
theorem paramsS_256f : paramsS params.SHA2_256F = Spec.sha2_256f := by
  simp [paramsS, global_simps, Spec.sha2_256f]

theorem valid_128s : (paramsS params.SHA2_128S).Valid := paramsS_128s ▸ Spec.sha2_128s_valid
theorem valid_128f : (paramsS params.SHA2_128F).Valid := paramsS_128f ▸ Spec.sha2_128f_valid
theorem valid_192s : (paramsS params.SHA2_192S).Valid := paramsS_192s ▸ Spec.sha2_192s_valid
theorem valid_192f : (paramsS params.SHA2_192F).Valid := paramsS_192f ▸ Spec.sha2_192f_valid
theorem valid_256s : (paramsS params.SHA2_256S).Valid := paramsS_256s ▸ Spec.sha2_256s_valid
theorem valid_256f : (paramsS params.SHA2_256F).Valid := paramsS_256f ▸ Spec.sha2_256f_valid

end slhdsa
