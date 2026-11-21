import Ideal.RustFinalClosed

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal Ideal Ideal.Realize

/-- Forger 1: one compression query at (0, 0), then one signing query on a 1-byte message that
depends on the answer, then outputs (message [1], the signature it got). -/
noncomputable def F1 : ForgerI where
  main _ := do
    let c : St ← (FSpecP (List SLHDSA.Byte)).query (.inr (.inl (Vector.replicate 32 0, Vector.replicate 64 0)))
    let s ← (FSpecP (List SLHDSA.Byte)).query (.inr (.inr [c[0]!]))
    pure ([1], s)

theorem F1_port (pk) : IsQueryBoundP (F1.main pk) (fun i => isPortQ (S := List SLHDSA.Byte) i = true) 1 := by
  simp [F1, IsQueryBoundP, isQueryBound_query_bind_iff, isPortQ]

theorem F1_sign (pk) : IsQueryBoundP (F1.main pk) (fun i => isSignQ (S := List SLHDSA.Byte) i = true) 1 := by
  simp [F1, IsQueryBoundP, isQueryBound_query_bind_iff, isSignQ]

theorem F1_long (pk) : IsQueryBoundP (F1.main pk) (fun i => isLongQ (S := List SLHDSA.Byte) 1 i = true) 0 := by
  simp [F1, IsQueryBoundP, isQueryBound_query_bind_iff, isLongQ]

theorem F1_out (pk) : ∀ z ∈ support (F1.main pk), z.1.length ≤ 1 := by
  intro z hz
  simp [F1] at hz
  obtain ⟨_, _, rfl⟩ := hz
  simp

example (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) :
    sufI F1 (optRandU oR) ($ᵗ (Bytes 16)) ≤
      ((2 : ℝ≥0∞) ^ 70)⁻¹ + ((2 : ℝ≥0∞) ^ 128)⁻¹ + ((2 : ℝ≥0∞) ^ 61)⁻¹ :=
  suf_ideal_closed_2_20 F1 oR F1_port F1_sign F1_long F1_out (by norm_num) (by norm_num) (by norm_num)

example :
    eufI F1 (optRandU fun s _ => pure s) ($ᵗ (Bytes 16)) ≤
      ((2 : ℝ≥0∞) ^ 44)⁻¹ + ((2 : ℝ≥0∞) ^ 43)⁻¹ + ((2 : ℝ≥0∞) ^ 31)⁻¹ :=
  euf_ideal_closed_2_64 F1 _ F1_port F1_sign F1_long F1_out (by norm_num) (by norm_num) (by norm_num)

-- general theorem at F1 (hQ is decidable arithmetic)
example (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) := 
  suf_ideal_closed F1 oR F1_port F1_sign F1_long F1_out (by unfold QcAll; norm_num)

-- sanity: the bounds are tight (the queries are real and are counted)
example (pk) : ¬ IsQueryBoundP (F1.main pk) (fun i => isPortQ (S := List SLHDSA.Byte) i = true) 0 := by
  simp [F1, IsQueryBoundP, isPortQ]
example (pk) : ¬ IsQueryBoundP (F1.main pk) (fun i => isSignQ (S := List SLHDSA.Byte) i = true) 0 := by
  simp [F1, IsQueryBoundP, isSignQ]
-- a forger signing a 2-byte message violates hlong at ℓ = 1
example : ¬ IsQueryBoundP
    ((FSpecP (List SLHDSA.Byte)).query (.inr (.inr [0, 0])) : OracleComp (FSpecP (List SLHDSA.Byte)) _)
    (fun i => isLongQ (S := List SLHDSA.Byte) 1 i = true) 0 := by
  simp [IsQueryBoundP, isLongQ]
