import Integration.SlhDsaForsLifetime

namespace Reduction.ForsLifetime
open ENNReal Finset PQ.QROM

set_option maxRecDepth 10000
set_option maxHeartbeats 1500000

private abbrev targets : ℕ := 2^64
private abbrev addresses : ℕ := 2^68
private def term (i : ℕ) : ℚ :=
  (((targets.descFactorial i : ℚ) / i.factorial) * ((addresses:ℚ)⁻¹)^i) *
      (15/16) * (1-(511/512)^i)^35

/-- The first ten occupancies suffice for this strict inequality. The estimate
uses Bernoulli's lower bound 15/16 for the no-hit probability on remaining trials. -/
theorem iid_fors_256f_floor :
    ((2:ℝ≥0∞)^256)⁻¹ < coverProb (Fin targets)
      (forsCov (I := Fin addresses) (L := Fin 512) (k := 35)) := by
  classical
  rw [coverProb_fors]
  simp only [Fintype.card_fin]
  let exactTerm (i : ℕ) : ℝ≥0∞ :=
    (targets.choose i : ℝ≥0∞)*((addresses:ℝ≥0∞)⁻¹)^i*(1-(addresses:ℝ≥0∞)⁻¹)^(targets-i)*
      (1-(1-(512:ℝ≥0∞)⁻¹)^i)^35
  let small (i : ℕ) : ℝ≥0∞ := (targets.choose i : ℝ≥0∞)*((addresses:ℝ≥0∞)⁻¹)^i*(15/16)*
      (1-(1-(512:ℝ≥0∞)⁻¹)^i)^35
  change _ < ∑ i ∈ range (targets+1), exactTerm i
  have lower (i : ℕ) : small i ≤ exactTerm i := by
    have hb := Num.one_sub_one_sub_pow_le (addresses:ℝ≥0∞)⁻¹ (by norm_num) (targets-i)
    have budget : ((targets-i:ℕ):ℝ≥0∞)*(addresses:ℝ≥0∞)⁻¹ ≤ 1/16 := by
      apply (mul_le_mul' (Nat.cast_le.mpr (Nat.sub_le targets i)) le_rfl).trans
      apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
      norm_num [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_div]
    have h := tsub_le_iff_right.mp (hb.trans budget)
    unfold small exactTerm
    gcongr
    have fin : (1-(addresses:ℝ≥0∞)⁻¹)^(targets-i) ≠ ⊤ := by finiteness
    apply (ENNReal.toReal_le_toReal (by finiteness) fin).mp
    have hr := (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mpr h
    rw [ENNReal.toReal_add (by finiteness) fin] at hr
    norm_num at hr ⊢
    linarith
  have clip := sum_le_sum_of_subset_of_nonneg (f := exactTerm)
    (range_mono (show 10 ≤ targets+1 by decide)) (fun _ _ _ => zero_le)
  apply lt_of_lt_of_le _ ((sum_le_sum fun i _ => lower i).trans clip)
  have real_small (i : ℕ) : (small i).toReal = (term i : ℝ) := by
    have col : (1-(1-(512:ℝ≥0∞)⁻¹)^i).toReal = 1-(511/512:ℝ)^i := by
      rw [ENNReal.toReal_sub_of_le (pow_le_one₀ zero_le tsub_le_self) (by finiteness),ENNReal.toReal_pow,
        ENNReal.toReal_sub_of_le (by norm_num) (by finiteness)]
      norm_num
    have rows : ((targets.choose i : ℕ):ℝ) = (targets.descFactorial i : ℝ)/i.factorial := by
      rw [Nat.descFactorial_eq_factorial_mul_choose,Nat.cast_mul]
      field_simp
    simp (disch := first | finiteness | norm_num | positivity) only [small,term,ENNReal.toReal_mul,col,
      ENNReal.toReal_div,ENNReal.toReal_inv,ENNReal.toReal_ofNat,ENNReal.toReal_natCast,ENNReal.toReal_pow,
      Rat.cast_mul,Rat.cast_div,Rat.cast_natCast,Rat.cast_pow,Rat.cast_sub,Rat.cast_one,
      Rat.cast_inv,Rat.cast_ofNat]
    rw [rows]
  have cert : (2:ℚ)⁻¹^256 < ∑ i ∈ range 10, term i := by decide +kernel
  have hf (i : ℕ) : small i ≠ ⊤ := by
    unfold small
    exact ENNReal.mul_ne_top (by finiteness) (ENNReal.pow_ne_top (ne_top_of_le_ne_top one_ne_top tsub_le_self))
  apply (ENNReal.toReal_lt_toReal (by finiteness) (ENNReal.sum_ne_top.mpr fun i _ => hf i)).mp
  simp only [ENNReal.toReal_inv,ENNReal.toReal_pow,ENNReal.toReal_ofNat,
    ENNReal.toReal_sum (f := small) (fun i _ => hf i),real_small,←inv_pow]
  have hc := Rat.cast_lt (K := ℝ) |>.2 cert
  simpa only [Rat.cast_pow,Rat.cast_inv,Rat.cast_ofNat,Rat.cast_sum] using hc

open QItsr SLHDSA SLHDSA.DigestTransport

private theorem decoded_cover (vp : ValidatedParams) (S : Finset (Bytes vp.params.m)) (u : Bytes vp.params.m)
    (h : forsCov (S.image (coveringDigest vp)) (coveringDigest vp u)) : SetDigest.idxCov vp S u := by
  intro v hv
  simp only [SetDigest.idxOf,forsIndices,List.mem_map,List.mem_range] at hv
  obtain ⟨j,hj,rfl⟩ := hv
  let i : Fin vp.params.k := ⟨j,hj⟩
  obtain ⟨z,hz,leaf,digit⟩ := h i
  obtain ⟨d,hd,rfl⟩ := mem_image.mp hz
  obtain ⟨tree,idx⟩ := (coveringDigest_fst_eq_iff vp d u).mp leaf
  have addr : (splitDigest vp.params d).forsAdrs = (splitDigest vp.params u).forsAdrs := by
    simp only [DigestParts.forsAdrs,tree,idx]
  have dig := congrArg Fin.val digit
  rw [coveringDigest_snd_val,coveringDigest_snd_val] at dig
  refine ⟨d,hd,?_⟩
  simp only [SetDigest.idxOf,forsIndices,List.mem_map,List.mem_range]
  exact ⟨j,hj,Prod.ext addr (congrArg (j*2^vp.params.a+·) dig)⟩

private theorem cover_complement {D : Type} [Fintype D] [DecidableEq D] [Nonempty D] (s : ℕ)
    (cov : Finset D → D → Prop) [∀ v, DecidablePred (cov v)] :
    coverProb (Fin s) cov + coverProb (Fin s) (fun v d => ¬cov v d) = 1 := by
  unfold coverProb
  rw [← sum_add_distrib]
  simp_rw [←mul_add,←add_mul]
  have sizes (d : Fin s → D) :
      #(covered cov (univ.image d)) + #(covered (fun v y => ¬cov v y) (univ.image d)) = Fintype.card D :=
    (card_filter_add_card_filter_not ..).trans card_univ
  simp only [← Nat.cast_add,sizes,natCast_mul_inv_cancel Fintype.card_ne_zero,mul_one,
    sum_const,card_univ,nsmul_eq_mul]

/-- Equal-size decoding fibers preserve the exact coverage probability of
the FIPS byte digest, including its unused bits. -/
theorem digest_coverage_exact (vp : ValidatedParams) (s : ℕ) :
    coverProb (Fin s) (SetDigest.idxCov vp) =
      coverProb (Fin s) (forsCov (I := Fin (2^vp.params.h)) (L := Fin (2^vp.params.a)) (k := vp.params.k)) := by
  apply le_antisymm (SetDigest.coverProb_idxCov_le vp s)
  let dec := coveringDigest vp
  let C := SetDigest.idxCov vp
  let σ := @forsCov (Fin (2^vp.params.h)) (Fin (2^vp.params.a)) vp.params.k
  have hc := cover_complement s C
  have hf := cover_complement s σ
  have flip := coverProb_le_of_fiber (ι := Fin s) dec _ (Nat.two_pow_pos _)
    (card_fiber_coveringDigest vp) (fun v d => ¬C v d) (fun v d => ¬σ v d)
    (fun v d no yes => no (decoded_cover vp v d yes))
  have finite : coverProb (Fin s) (fun v d => ¬ C v d) ≠ ⊤ :=
    ne_top_of_le_ne_top one_ne_top ((le_add_self).trans_eq hc)
  apply ENNReal.le_of_add_le_add_right finite
  exact (add_le_add le_rfl flip).trans_eq (hf.trans hc.symm)

/-- At the 256f parameter set a fresh independent encoded digest has coverage
probability strictly above 2^-256 after 2^64 independent target digests. -/
theorem encoded_256f_floor :
    ((2:ℝ≥0∞)^256)⁻¹ < coverProb (Fin (2^64)) (SetDigest.idxCov MLink.Sha2Set.s256f.vp) := by
  rw [digest_coverage_exact]
  exact iid_fors_256f_floor

end Reduction.ForsLifetime
#print axioms Reduction.ForsLifetime.iid_fors_256f_floor
#print axioms Reduction.ForsLifetime.encoded_256f_floor
