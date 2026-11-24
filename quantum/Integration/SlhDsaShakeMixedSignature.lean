import Integration.SlhDsaShakeXofMsgLifetime
import Integration.SlhDsaShakeAdaptiveItsr
import Integration.SlhDsaShakeXofRepeated

namespace Reduction.ShakeXof
open MLink SLHDSA SLHDSA.Security OracleComp OracleSpec PQ.Interactive Quantum ENNReal
set_option maxRecDepth 8192

/-- Both PRF terms in the full signature experiment charge only the
forger's public calls coherently. The other hash games retain their own
reduction counts. The adaptive digest term uses the shared XOF byte table. -/
theorem mixed_signature_queries (S : Sha2Set) (N : ℕ)
    (rand : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node)
    {E : Type} [Fintype E] [DecidableEq E] (F : PortForger (ShakeApi.Input N) (Bytes S.vp.params.m) E)
    (q s : ℕ) (c : Caps) (raw : 3*S.vp.params.n+c.ml ≤ N)
    (fit : ∀ k ∈ [1,2,S.vp.params.len,S.vp.params.k], S.vp.params.n+32+S.vp.params.n*k ≤ N)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hs : ∀ pk, CountBound isSign (F.main pk) s)
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    let bound := repeatedLossWithPrfs S q s (mixedPrfLoss S q (ShakeApi.Sk.budget S 0 s))
      (mixedPrfLoss S q (ShakeApi.Msg.budget S 0 s)) (itsrBound S.vp.params (q+itsrHashes S.vp s) s)
    SetOracle.uniformMean (fun H => qStrongUnforgeableAdvantage (ShakeApi.rawForger S N rand seeds F H)) ≤ bound ∧
    SetOracle.uniformMean (fun H => qUnforgeableAdvantage (ShakeApi.rawForger S N rand seeds F H)) ≤ bound := by
  have singleton := fit 1 (by simp)
  simp only [Nat.mul_one] at singleton
  obtain ⟨strong,ordinary⟩ := signature_with_prfs S N rand seeds F q s _ _ fit hq hs
    (ShakeApi.Sk.Mixed.real_le_ideal S N rand seeds F (by omega) q s hq hs)
    (ShakeApi.Msg.Mixed.real_le_ideal S N rand seeds F c (by omega) q s hq hs hc)
  have cover := ShakeAdaptive.signature_itsr S N rand seeds F q s c raw hq hs hc
  constructor <;> first | apply strong.trans | apply ordinary.trans
  all_goals dsimp only [repeatedLossWithPrfs]; gcongr

end Reduction.ShakeXof
#print axioms Reduction.ShakeXof.mixed_signature_queries
