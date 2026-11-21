import Integration.SlhDsaComposedEnc2Msg
import Integration.SlhDsaBridgeForsDspr

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal PQ.Interactive PQ.QROM Quantum
namespace Reduction
variable {E : Type} [Fintype E] [DecidableEq E] (c : Caps)
  (optRand₀ : Bytes Link.vp.params.n → Bytes Link.vp.params.n → ProbComp (Bytes Link.vp.params.n))
  (pkSeedDist₀ : ProbComp (Bytes Link.vp.params.n))

example (F : PortForger (EncX c) EncY E) (q qs : ℕ) (r : RedCounts)
    (hq : ∀ pk, CountBound isPort (F.main pk) q)
    (hqs : ∀ pk, CountBound isSign (F.main pk) qs)
    (hcap : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk))
    (htl : 35 ≤ c.tl)
    (hb : BridgesRest10 c (optRandOf c optRand₀) (fun _ ↦ pkSeedDist₀)
        (internalΩ c optRand₀ pkSeedDist₀ encΩ F) q qs r)
    (hMfv : ∀ (ω₀ : Ω128 c) (st : Open.ForsP1State Link.vp (primsΩ ω₀))
        (pk : Bytes Link.vp.params.n),
      ∃ Mo : PQ.QROM.HybridModel (EncX c) EncY (ℕ × Bytes Link.vp.params.n) (q + r.tcrFv),
        ∀ (T : Bytes Link.vp.params.n → Bytes 22 → BList (Bytes Link.vp.params.n) c.tl →
            Bytes Link.vp.params.n)
          (Ev : ℕ × Bytes Link.vp.params.n → Prop) [DecidablePred Ev],
          Mo.prob (encΩ { ω₀ with thash := T }) Ev =
            qWeight Ev ((qToTcr (internalΩ c optRand₀ pkSeedDist₀ encΩ F
              { ω₀ with thash := T })).forge st pk) F.ρ₀)
    (hMd : ∀ (ω₀ : Ω128 c) (st : Open.ForsP1State Link.vp (primsΩ ω₀))
        (pk : Bytes Link.vp.params.n),
      ∃ Mo : PQ.QROM.HybridModel (EncX c) EncY (ℕ × Bool) (q + r.dspr),
        Mo.Additive ∧
        PQ.QROM.Rows.RowsBound (fun H E ↦ (Mo.prob H E).toReal) (q + r.dspr) ∧
        ∀ (T : Bytes Link.vp.params.n → Bytes 22 → BList (Bytes Link.vp.params.n) c.tl →
            Bytes Link.vp.params.n)
          (Ev : ℕ × Bool → Prop) [DecidablePred Ev],
          Mo.prob (encΩ { ω₀ with thash := T }) Ev =
            qWeight Ev ((qToDspr (internalΩ c optRand₀ pkSeedDist₀ encΩ F
              { ω₀ with thash := T })).guess st pk) F.ρ₀) :
    avΩ c (fun ω ↦ qStrongUnforgeableAdvantage (F.at (encΩ ω) (algΩ c optRand₀ pkSeedDist₀ ω))) ≤
      composedBoundFinal q qs r.noPrfMsg := by
  exact composed_of_linear_eps (internalΩ c optRand₀ pkSeedDist₀ encΩ F) _ _ _ _ _
    _ _ _ _ _ _ _ _ _ _ _ _
    (fun ω ↦ qPrfIdealPr_le_one' _ (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω).posSemidef
      (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω).trace_eq_one)
    (fun ω ↦ qPrfIdealPr_le_one' _ (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω).posSemidef
      (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω).trace_eq_one)
    (slhdsa_sha2_128s_pure_bytes_suf_cma_linear_quantum_uniform c (optRandOf c optRand₀)
      (fun _ ↦ pkSeedDist₀) fun ω ↦ F.at (encΩ ω) (algΩ c optRand₀ pkSeedDist₀ ω))
    (prf_term_suf c optRand₀ pkSeedDist₀ F q hq
      (QInd.prfMachSuf_withPrf c optRand₀ pkSeedDist₀ F))
    (QMsg.msg_term_suf c optRand₀ pkSeedDist₀ F q hq hcap)
    (hb.itsr.le fun _ ↦ ItsrValue.le)
    (dspr_term c optRand₀ pkSeedDist₀ F (by omega) _ hMd)
    (tcrFv_term c optRand₀ pkSeedDist₀ F (by omega) _ hMfv)
    (hb.tcr1.le fun _ ↦ TcrValue.le) (hb.tcr2.le fun _ ↦ TcrValue.le)
    (hb.tcrLen.le fun _ ↦ TcrValue.le) (hb.tcrK.le fun _ ↦ TcrValue.le)
    (hb.ud.le fun _ _ ↦ UdValue.le) (hb.pre.le fun _ ↦ PreValue.le)
    (hb.tcrT.le fun _ ↦ TcrValue.le)
end Reduction
