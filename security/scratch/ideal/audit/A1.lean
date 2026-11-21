import Ideal.RustFinalClosed

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal Ideal Ideal.Realize

#print axioms Ideal.suf_ideal_closed
#print axioms Ideal.euf_ideal_closed
#print axioms Ideal.suf_ideal_closed_2_20
#print axioms Ideal.euf_ideal_closed_2_20
#print axioms Ideal.suf_ideal_closed_2_40
#print axioms Ideal.euf_ideal_closed_2_40
#print axioms Ideal.suf_ideal_closed_2_64
#print axioms Ideal.euf_ideal_closed_2_64
#print axioms Ideal.rust_ideal_security_closed

-- which SampleableType instance is used for the table, and what are St / Blk
#synth SampleableType (CF St Blk)
#check (inferInstance : SampleableType (CF St Blk))
#print St
#print Blk
#print Ideal.ForgerI
#print Ideal.sufI
#print Ideal.optRandU

-- Forger 0: outputs a constant, no queries.
def F0 : ForgerI where
  main _ := pure ([], [])

example (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) :
    sufI F0 (optRandU oR) ($ᵗ (Bytes 16)) ≤
      ((2 : ℝ≥0∞) ^ 70)⁻¹ + ((2 : ℝ≥0∞) ^ 128)⁻¹ + ((2 : ℝ≥0∞) ^ 61)⁻¹ :=
  suf_ideal_closed_2_20 F0 oR (qf := 0) (qs := 0) (ℓ := 0)
    (fun _ => by simp [F0, IsQueryBoundP])
    (fun _ => by simp [F0, IsQueryBoundP])
    (fun _ => by simp [F0, IsQueryBoundP])
    (fun _ z hz => by simp [F0] at hz; subst hz; simp)
    (by norm_num) (by norm_num) (by norm_num)
