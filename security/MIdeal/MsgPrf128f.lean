import MIdeal.MsgPrf512

set_option maxRecDepth 8192
namespace MIdeal
open Ideal SLHDSA SLHDSA.Concrete MLink OracleComp OracleSpec ENNReal PRFScheme

/-- For both 128-bit sets the message PRF is the very same truncated HMAC-SHA-256.
The independent SHA-512 table may be fixed arbitrarily. -/
theorem msg_scheme_128f (g : CompressionTables) :
    @Reduction.msgPrf Sha2Set.s128f.vp (tablePrimitives g Sha2Set.s128f.vp.params)
      (inferInstanceAs (SampleableType (Bytes 16))) =
    Reduction.msgPrf Link.vp (primsG (liftC g.1)) := by
  unfold Reduction.msgPrf SLHDSA.msgPrfScheme
  apply congrArg (fun f => (⟨$ᵗ (Bytes 16), f⟩ :
    PRFScheme (Bytes 16) (Bytes 16 × List Byte) (Bytes 16)))
  funext k d
  change @sha2PRFmsgMixed (liftC g.1) (lift512 g.2) 16 k d.1 d.2 = @sha2PRFmsgG (liftC g.1) 16 k d.1 d.2
  simp only [sha2PRFmsgMixed, sha2PRFmsgG, ite_true]

noncomputable def msgReal128f (g512 : CF Chain512 Block512) (A : MsgPrfAdvI) : ℝ≥0∞ :=
  cfAdvantage fun g =>
    (@Reduction.msgPrf Sha2Set.s128f.vp (tablePrimitives (g,g512) Sha2Set.s128f.vp.params)
      (inferInstanceAs (SampleableType (Bytes 16)))).prfRealExperiment (A.inst g)

theorem msg_prf_128f (g512 : CF Chain512 Block512) (A : MsgPrfAdvI) (q qo limit : ℕ)
    (hq : IsQueryBoundP A (fun i => isCompQ i = true) q)
    (ho : IsQueryBoundP A (fun i => isPrfQ i = true) qo) (hm : AllQueriesSatisfy A (msgLenLe limit)) :
    let err := 2*(q:ℝ≥0∞)/2^128 +
      (((q + qo*((limit+24)/64+1)+2)^2 : ℕ) : ℝ≥0∞)/2^256
    msgReal128f g512 A ≤ msgIdealI A + err ∧ msgIdealI A ≤ msgReal128f g512 A + err := by
  have eq : msgReal128f g512 A = msgRealI A := by
    unfold msgReal128f msgRealI
    refine congrArg cfAdvantage (funext fun g => ?_)
    exact congrArg (fun s : PRFScheme (Bytes 16) (Bytes 16 × List Byte) (Bytes 16) =>
      s.prfRealExperiment (A.inst g)) (msg_scheme_128f (g,g512))
  rw [eq]
  exact msgPrf_bound_128s A q qo limit hq ho hm
end MIdeal

#print axioms MIdeal.msg_prf_128f
