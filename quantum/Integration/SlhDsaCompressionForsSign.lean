import Integration.SlhDsaCompressionKeygen
import Ideal.Realize.ForsCount

namespace Reduction.Compression
open MLink Ideal SLHDSA SLHDSA.Security OracleComp OracleSpec PQ.Interactive PQ.QROM Quantum
open Resources2
attribute [local instance] Lazy.openQ Lazy.closedQ
variable (S : Sha2Set) (f : RandFns S.vp.params)
local notation "P₀" => randPrims f

def signMax (ml : ℕ) := max (max (keygenMax S) (thashCalls S S.vp.params.k)) (hmsgCalls S ml)

theorem forsSign_cost (tbl : SecretTable S.vp P₀) (targets : List (Bytes 22 × S.Node))
    (pk : PublicKeyCore (P₀).core) (ys : List S.Node) (msg : List Byte) (R : S.Node) (s : List ℕ) :
    EvalCost (fun H => (simulateQ (fImpl (hashPort S f H) tbl targets) (fSignOpen pk ys msg R)).run s)
      ((forsSignHashes S.vp + 1) * signMax S msg.length) := by
  let w := forsWeight S f
  let B := signMax S msg.length
  have hm : IsQueryBoundP (PublicHash.hmsg (P₀).core R pk.pkSeed pk.pkRoot msg :
      OracleComp (Lazy.OSpec P₀ (forsG P₀)) _) (fun t => B < w t) 0 :=
    (isQueryBoundP_query_iff _ _ _).2 fun h => False.elim ((not_lt_of_ge (le_max_right ..)) h)
  apply forsOpen_cost
  refine cappedCount w (fun t => Lazy.kind t = .hash) _ (fun t ht => ?_) _ _ ?_ ?_
  · rcases t with n|op|addr|hash <;> first | rfl | exact (ht rfl).elim
  · unfold fSignOpen
    refine Lazy.qb_bind _ ((forsSignOpen_kindBound .hash pk ys msg R).mono ?_) fun sig =>
      Lazy.qb_bind _ (m := 0) (Lazy.query_kindBound .hash _) fun d => isQueryBoundP_pure _ _ _
    simpa [Lazy.ind] using forsSignB_hash (vp := S.vp)
  · unfold fSignOpen
    refine isQueryBoundP_bind_zero _ _ (Realize.Fors.forsSignOpen_le _ pk ys msg R 0
      (fun _ => Nat.not_lt_zero _) (fun _ => Nat.not_lt_zero _) ?_ hm) fun sig =>
      isQueryBoundP_bind_zero _ _ hm fun _ => isQueryBoundP_pure _ _ _
    intro key xs hx
    change ¬ B < thashCalls S xs.length
    rcases hx with h|h|h|h <;> rw [h] <;> unfold B signMax keygenMax <;> omega

end Reduction.Compression
#print axioms Reduction.Compression.forsSign_cost
