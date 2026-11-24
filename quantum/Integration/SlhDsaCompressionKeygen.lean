import Integration.SlhDsaCompressionOpen
import Ideal.Realize.ItsrWalk

namespace Reduction.Compression
open MLink Ideal SLHDSA SLHDSA.Security OracleComp OracleSpec PQ.Interactive PQ.QROM Quantum
variable (S : Sha2Set) (f : RandFns S.vp.params)
local notation "P₀" => randPrims f

def openWeight {ι : Type} (gspec : OracleSpec ι) : (Lazy.OSpec P₀ gspec).Domain → ℕ
  | .inr (.inr (.inr q)) => hashCalls S f q
  | _ => 0

theorem cappedCount {κ α : Type} {sp : OracleSpec κ} (w : κ → ℕ) (pos : κ → Prop)
    [DecidablePred pos] (B : ℕ) (zero : ∀ t, ¬pos t → w t = 0)
    (P : OracleComp sp α) (q : ℕ) (hq : IsQueryBoundP P pos q)
    (hc : IsQueryBoundP P (fun t => B < w t) 0) : WCount w P (q*B) := by
  induction P using OracleComp.inductionOn generalizing q with
  | pure a => exact wCount_pure ..
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hq hc
    have ht : ¬B < w t := hc.1.resolve_right (by decide)
    have hrest (r) := ih r _ (hq.2 r) (by simpa [ht] using hc.2 r)
    rw [wCount_query_bind]
    by_cases hp : pos t
    · have nonzero := hq.1.resolve_left (by simpa using hp)
      cases q with
      | zero => omega
      | succ q =>
        simp only [hp,ite_true,Nat.add_one_sub_one] at hrest
        rw [Nat.succ_mul]
        exact ⟨by omega, fun r => (hrest r).mono (by omega)⟩
    · simp only [hp,ite_false] at hrest
      simpa [zero t hp] using And.intro (Nat.zero_le (q*B)) hrest

def keygenMax := max (thashCalls S 1) (max (thashCalls S 2) (thashCalls S S.vp.params.len))

theorem keygen_cost (tbl : SecretTable S.vp P₀) (pk : S.Node) :
    EvalCost (fun H => simulateQ (qmImpl (hashPort S f H) tbl) (Lazy.openKeygen P₀ []ₒ pk))
      (Lazy.keygenHashes S.vp * keygenMax S) := by
  let w := openWeight S f []ₒ
  have per (t) : EvalCost (fun H => qmImpl (hashPort S f H) tbl t) (w t) := by
    rcases t with n | op | addr | hash
    · exact EvalCost.const _
    · exact PEmpty.elim op
    · exact EvalCost.const _
    · exact hashPort_cost S f hash
  apply EvalCost.simulateQ _ w per
  refine cappedCount w (fun t => Lazy.kind t = .hash) _ (fun t ht => ?_) _ _ ?_ ?_
  · rcases t with n|op|addr|hash <;> first | rfl | exact (ht rfl).elim
  · exact (Lazy.openKeygen_kindBound (prims := P₀) (gspec := []ₒ) .hash pk).mono (by simpa [Lazy.ind] using Lazy.keygenB_hash (vp := S.vp))
  · apply Ideal.Realize.Itsr.npA_openKeygen
    · intro d; exact Nat.not_lt_zero _
    · intro key x; exact not_lt_of_ge (le_max_left ..)
    · intro key l r; exact not_lt_of_ge (le_trans (le_max_left ..) (le_max_right ..))
    · intro b xs hx
      change ¬keygenMax S < thashCalls S xs.length
      rw [hx]
      exact not_lt_of_ge (le_trans (le_max_right ..) (le_max_right ..))

end Reduction.Compression
#print axioms Reduction.Compression.keygen_cost
