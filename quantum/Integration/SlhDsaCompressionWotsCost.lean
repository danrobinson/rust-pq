import Integration.SlhDsaCompressionBudget
import Ideal.Realize.WotsPort

namespace Reduction.Compression
open MLink Ideal SLHDSA SLHDSA.Security OracleComp OracleSpec PQ.Interactive Quantum Resources2 Open Realize.Wots
attribute [local instance] Lazy.openQ Lazy.closedQ
variable (S : Sha2Set) (f : RandFns S.vp.params)
local notation "P₀" => randPrims f

def exceeds (L : ℕ) (t : (Lazy.OSpec P₀ []ₒ).Domain) := signMax S L < openWeight S f []ₒ t
instance (L : ℕ) : DecidablePred (exceeds S f L) := fun _ => Nat.decLt _ _

theorem openProgram_cost (tbl : SecretTable S.vp P₀) {α : Type} (P : OracleComp (Lazy.OSpec P₀ []ₒ) α)
    (q L : ℕ) (hc : IsQueryBoundP P (fun t => Lazy.kind t = .hash) q) (hl : IsQueryBoundP P (exceeds S f L) 0) :
    EvalCost (fun H => simulateQ (qmImpl (hashPort S f H) tbl) P) (q*signMax S L) := by
  apply EvalCost.simulateQ _ (openWeight S f []ₒ)
  · rintro (n|op|addr|hash)
    · exact EvalCost.const _
    · exact PEmpty.elim op
    · exact EvalCost.const _
    · exact hashPort_cost S f hash
  · apply cappedCount _ _ _ _ P q hc hl
    rintro (n|op|addr|hash) h <;> first | rfl | exact (h rfl).elim

theorem okLength_cost (L : ℕ) (pk : S.Node) (key : Bytes 22) (xs : List S.Node) (hx : Realize.OkLen S.vp xs) :
    ¬exceeds S f L (Realize.thIdx P₀ PEmpty pk key xs) := by
  change ¬ signMax S L < thashCalls S xs.length
  rcases hx with h|h|h|h <;> rw [h] <;> unfold signMax keygenMax <;> omega

private theorem msgOK (pk : PublicKeyCore (P₀).core) (msg : List Byte) (R : S.Node) :
    IsQueryBoundP (PublicHash.hmsg (P₀).core R pk.pkSeed pk.pkRoot msg :
      OracleComp (Lazy.OSpec P₀ []ₒ) _) (exceeds S f msg.length) 0 :=
    (isQueryBoundP_query_iff _ _ _).2 fun ht => False.elim ((not_lt_of_ge (le_max_right ..)) ht)

theorem wotsSign_cost (tbl : SecretTable S.vp P₀) (hist : List (WotsGame.Entry P₀))
    (pk : PublicKeyCore (P₀).core) (msg : List Byte) (R : S.Node) :
    EvalCost (fun H => simulateQ (qmImpl (hashPort S f H) tbl) (wotsSignFromHistO hist pk msg R))
      (wotsSignHistHashes S.vp * signMax S msg.length) := by
  apply openProgram_cost
  · exact (wotsSignFromHistO_kindBound .hash hist pk msg R).mono wotsSignHistB_ind_hash
  · exact pw_signFromHist _ (fun _ => Nat.not_lt_zero _) (okLength_cost S f _) hist pk msg R 0 (msgOK S f pk msg R)

theorem wotsAnswer_cap (hist : List (WotsGame.Entry P₀)) (pk : PublicKeyCore (P₀).core)
    (msg : List Byte) (sig : GeneralScheme.SignatureCore S.vp (P₀).core) :
    IsQueryBoundP (wotsAnswerOpen (gspec := []ₒ) hist pk msg sig) (exceeds S f msg.length) 0 :=
  pw_answer _ (fun _ => Nat.not_lt_zero _) (okLength_cost S f _) hist pk msg sig 0 (msgOK S f pk msg sig.randomness)

end Reduction.Compression
#print axioms Reduction.Compression.wotsSign_cost
#print axioms Reduction.Compression.wotsAnswer_cap
