import Integration.SlhDsaCompressionClassCandidates
import MIdeal.ThashReader
import MReduction.Resources

namespace Reduction.Compression.ClassCollision
open MLink Ideal Ideal.HP Ideal.Itsr SLHDSA SLHDSA.Security OracleComp OracleSpec PQ.Interactive Resources2
open MIdeal.Sha512 ENNReal Ideal.Prf
attribute [local irreducible] tcrTargets
variable (S : Sha2Set)
local notation "P₀" => randPrims (carrier S)

/-- Run the honest construction with classical SHA-512 reads and record its tweakable-hash calls. -/
def readWalk {α : Type} (a : CF St Blk) (pk : S.Node) (P : OracleComp (thSpec P₀) α)
    (log : CallLog S) : SHAReader (CallLog S) :=
  let impl : QueryImpl (thSpec P₀) (StateT (CallLog S) SHAReader) := fun t => StateT.mk fun l => do
    let y ← readThash S a pk t.1 t.2
    pure (y,l ++ [t])
  Prod.snd <$> ((simulateQ impl P).run log)

theorem readWalk_eval {α : Type} (g : CompressionTables) (hw : S.vp.params.n ≠ 16)
    (pk : S.Node) (P : OracleComp (thSpec P₀) α) (log : CallLog S) :
    simulateQ (ansImpl (spec := hS Chain512 Block512) g.2) (readWalk S g.1 pk P log) =
      pure (((simulateQ (record S pk (oracle g)) P).run log).2) := by
  induction P using OracleComp.inductionOn generalizing log with
  | pure x => rfl
  | query_bind t k ih =>
    unfold readWalk at *
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, StateT.run_mk, bind_assoc, pure_bind, map_bind,
      readThash_eval S g hw] at *
    specialize ih ((tablePrimitives g S.vp.params).Thash pk t.1 t.2) (log ++ [t])
    change _ = pure (((simulateQ (record S pk (oracle g)) (k
      ((tablePrimitives (tablesOf (oracle g)) S.vp.params).Thash pk t.1 t.2))).run (log ++ [t])).2)
    rw [tablesOf_oracle]
    exact (pure_bind _ _).trans ih

theorem readWalk_bound {α : Type} (a : CF St Blk) (hw : S.vp.params.n ≠ 16) (pk : S.Node)
    (P : OracleComp (thSpec P₀) α) (log : CallLog S) (q : ℕ)
    (hq : WCount (fun t => thashCalls S t.2.length) P q) :
    IsQueryBoundP (readWalk S a pk P log) (fun i => i.isRight = true) q := by
  induction P using OracleComp.inductionOn generalizing log q with
  | pure x => simp [readWalk]
  | query_bind t k ih =>
    rw [wCount_query_bind] at hq
    unfold readWalk at *
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, StateT.run_mk, bind_assoc, pure_bind, map_bind]
    have ht : thashCost S t.2.length ≤ thashCalls S t.2.length := by
      by_cases one : t.2.length = 1 <;> simp [thashCost, thashCalls, one, hw]
    exact (isQueryBoundP_bind ((readThash_bound S a pk t.1 t.2).mono ht)
      (fun y _ => ih y _ _ (hq.2 y))).mono (by have := hq.1; omega)

/-- The honest walk exposes a repeated SHA-512 prefix or the reserved IV prefix
with at most the classical birthday probability. The SHA-256 table may be fixed arbitrarily. -/
theorem walk_prefix_bound (a : CF St Blk) (hw : S.vp.params.n ≠ 16)
    (pk : S.Node) (tbl : SecretTable S.vp P₀) :
    prT ($ᵗ (CF Chain512 Block512) >>= fun g =>
      (simulateQ (stImpl (spec := hS Chain512 Block512) g (logU id))
        (readWalk S a pk (structureFree tbl) [])).run [] >>= fun z =>
          pure (badV (trunc S initial) (z.2.map fun c => trunc S (g c)))) ≤
      (((tcrTargets S.vp * walkMax S)^2 : ℕ) : ℝ≥0∞) * ((2:ℝ≥0∞)^(8*S.vp.params.n))⁻¹ :=
  badPrefix_bound S id (fun g t => g t) (fun _ _ _ h => h) _ _
    (readWalk_bound S a hw pk _ [] _ (walk_count S tbl))

/-- On all four wide parameter sets the honest phase alone costs at most 1/256. -/
theorem walk_prefix_budget (hw : S.vp.params.n ≠ 16) :
    256 * (tcrTargets S.vp * walkMax S)^2 ≤ 2^(8*S.vp.params.n) := by
  cases S <;> first
    | exact (hw rfl).elim
    | (rw [MReduction.tcrTargets_192s_val]; decide +kernel)
    | (rw [MReduction.tcrTargets_192f_val]; decide +kernel)
    | (rw [MReduction.tcrTargets_256s_val]; decide +kernel)
    | (rw [MReduction.tcrTargets_256f_val]; decide +kernel)

end Reduction.Compression.ClassCollision
#print axioms Reduction.Compression.ClassCollision.readWalk_eval
#print axioms Reduction.Compression.ClassCollision.walk_prefix_bound
#print axioms Reduction.Compression.ClassCollision.walk_prefix_budget
