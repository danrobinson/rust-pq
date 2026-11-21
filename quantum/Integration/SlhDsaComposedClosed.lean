import Integration.SlhDsaComposedEnc2Msg
import Integration.SlhDsaBridgeTcrClosed
import Integration.SlhDsaBridgeForsClosed
import Integration.SlhDsaBridgeForsClosed2
import Integration.SlhDsaBridgeTcrTClosed
import Integration.SlhDsaBridgeWotsClosed
import Integration.SlhDsaBridgeMachItsr2

/-!
# The composed QROM statement for SLH-DSA-SHA2-128s with the bridge terms closed

NOT part of the default target; compiled like the other `Integration/*.lean` files.

`slhdsa_sha2_128s_pure_bytes_{suf,euf}_cma_qrom_enc_closed`: the `…_qrom_enc2msg` headline
(`Integration/SlhDsaComposedEnc2Msg.lean`) at the counts `r := openCounts128s qs`, conclusion
`… ≤ composedBoundFinal q qs (openCounts128s qs).noPrfMsg` (PRF and PRF_msg charged `q`; every
other term charged `q + (openCounts128s qs).<term>`), with the terms PROVED inside:

| term | proof |
|---|---|
| PRF | `prf_term_suf/euf` + `QInd.prfMachSuf_withPrf/prfMachEuf_withPrf` |
| PRF_msg | `QMsg.msg_term_suf/euf` (uses `hcap`) |
| DSPR (FORS) | `dspr_term_closed_128s` |
| TCR-FV (FORS) | `tcrFv_term_closed_128s` |
| TCR arity 1, 2, len, k | `tcr_terms_closed_128s` |
| PRE (WOTS) | `pre_term` + `wotsPre_hModel` (`pre_term_closed_128s`) |
| UD (WOTS) | `ud_closed` (`SlhDsaBridgeWotsClosed.lean`) |
| TCR (WOTS) | `tcrT_term_closed_128s` |
| ITSR | `itsr_closed` (`SlhDsaBridgeMachItsr2.lean`, uses `hcap`) |

NO bridge or model hypothesis remains: the only hypotheses are on the forger (`hq`, `hqs`,
`hcap`) and the Thash cap `htl : 35 ≤ c.tl`.

Name: `…_qrom_closed` is already taken by the older bridge-conditional theorems of
`Integration/SlhDsaComposedFinal.lean:697/712` (imported transitively), hence `…_qrom_enc_closed`.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal PQ.Interactive PQ.QROM Quantum
open scoped ComplexOrder

set_option linter.unusedSectionVars false

namespace Reduction

section port

variable {E : Type} [Fintype E] [DecidableEq E] (c : Caps)
  (optRand₀ : Bytes Link.vp.params.n → Bytes Link.vp.params.n → ProbComp (Bytes Link.vp.params.n))
  (pkSeedDist₀ : ProbComp (Bytes Link.vp.params.n))

/-- The PRE term, closed, with the count of `openCounts128s qs`. -/
theorem pre_term_closed_128s (F : PortForger (EncX c) EncY E) (hn : 1 ≤ c.tl) (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q)
    (hqs : ∀ pk, CountBound isSign (F.main pk) qs) :
    avΩ c (fun ω ↦ qSM_DT_PRE_Advantage
      (qrPre (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω))) ≤
        epsPre0 (q + (openCounts128s qs).pre) := by
  rw [← qmWotsPreHashes_openCounts128s qs]
  exact pre_term c optRand₀ pkSeedDist₀ F hn _
    (wotsPre_hModel c optRand₀ pkSeedDist₀ F q qs hq hqs)

/-- **Composed theorem, SUF-CMA, at the open counts; all twelve terms proved**: hypotheses on
the forger (`hq`, `hqs`, `hcap`) and `htl : 35 ≤ c.tl` only. -/
theorem slhdsa_sha2_128s_pure_bytes_suf_cma_qrom_enc_closed
    (F : PortForger (EncX c) EncY E) (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q)
    (hqs : ∀ pk, CountBound isSign (F.main pk) qs)
    (hcap : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk))
    (htl : 35 ≤ c.tl) :
    avΩ c (fun ω ↦ qStrongUnforgeableAdvantage (F.at (encΩ ω) (algΩ c optRand₀ pkSeedDist₀ ω))) ≤
      composedBoundFinal q qs (openCounts128s qs).noPrfMsg := by
  obtain ⟨h1, h2, hLen, hK⟩ := tcr_terms_closed_128s c optRand₀ pkSeedDist₀ F q qs htl hq hqs
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
    (itsr_closed c optRand₀ pkSeedDist₀ F q qs hq hqs hcap)
    (dspr_term_closed_128s c optRand₀ pkSeedDist₀ F (by omega) q qs hq hqs)
    (tcrFv_term_closed_128s c optRand₀ pkSeedDist₀ F (by omega) q qs hq hqs)
    h1 h2 hLen hK (ud_closed c optRand₀ pkSeedDist₀ F q qs htl hq hqs)
    (pre_term_closed_128s c optRand₀ pkSeedDist₀ F (by omega) q qs hq hqs)
    (tcrT_term_closed_128s c optRand₀ pkSeedDist₀ F (by omega) q qs hq hqs)

/-- **Composed theorem, EUF-CMA, at the open counts; all twelve terms proved**: hypotheses on
the forger (`hq`, `hqs`, `hcap`) and `htl : 35 ≤ c.tl` only. -/
theorem slhdsa_sha2_128s_pure_bytes_euf_cma_qrom_enc_closed
    (F : PortForger (EncX c) EncY E) (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q)
    (hqs : ∀ pk, CountBound isSign (F.main pk) qs)
    (hcap : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk))
    (htl : 35 ≤ c.tl) :
    avΩ c (fun ω ↦ qUnforgeableAdvantage (F.at (encΩ ω) (algΩ c optRand₀ pkSeedDist₀ ω))) ≤
      composedBoundFinal q qs (openCounts128s qs).noPrfMsg := by
  obtain ⟨h1, h2, hLen, hK⟩ := tcr_terms_closed_128s c optRand₀ pkSeedDist₀ F q qs htl hq hqs
  exact composed_of_linear_eps (internalΩ c optRand₀ pkSeedDist₀ encΩ F) _ _ _ _ _
    _ _ _ _ _ _ _ _ _ _ _ _
    (fun ω ↦ qPrfIdealPr_le_one' _ (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω).posSemidef
      (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω).trace_eq_one)
    (fun ω ↦ qPrfIdealPr_le_one' _ (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω).posSemidef
      (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω).trace_eq_one)
    (slhdsa_sha2_128s_pure_bytes_euf_cma_linear_quantum_uniform c (optRandOf c optRand₀)
      (fun _ ↦ pkSeedDist₀) fun ω ↦ F.at (encΩ ω) (algΩ c optRand₀ pkSeedDist₀ ω))
    (prf_term_euf c optRand₀ pkSeedDist₀ F q hq
      (QInd.prfMachEuf_withPrf c optRand₀ pkSeedDist₀ F))
    (QMsg.msg_term_euf c optRand₀ pkSeedDist₀ F q hq hcap)
    (itsr_closed c optRand₀ pkSeedDist₀ F q qs hq hqs hcap)
    (dspr_term_closed_128s c optRand₀ pkSeedDist₀ F (by omega) q qs hq hqs)
    (tcrFv_term_closed_128s c optRand₀ pkSeedDist₀ F (by omega) q qs hq hqs)
    h1 h2 hLen hK (ud_closed c optRand₀ pkSeedDist₀ F q qs htl hq hqs)
    (pre_term_closed_128s c optRand₀ pkSeedDist₀ F (by omega) q qs hq hqs)
    (tcrT_term_closed_128s c optRand₀ pkSeedDist₀ F (by omega) q qs hq hqs)

end port

end Reduction

#print axioms Reduction.pre_term_closed_128s
#print axioms Reduction.slhdsa_sha2_128s_pure_bytes_suf_cma_qrom_enc_closed
#print axioms Reduction.slhdsa_sha2_128s_pure_bytes_euf_cma_qrom_enc_closed
