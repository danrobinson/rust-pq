import Integration.SlhDsaCompressionSmallItsrCost
import Integration.SlhDsaCompressionHmac256Preimage
import Integration.SlhDsaCompressionLeftPrefix

namespace Reduction.Compression.SmallItsr
open MLink Ideal SLHDSA SLHDSA.Security OracleComp OracleSpec PQ.Interactive Quantum KeyedHash QMsg QItsr ENNReal Classical
open scoped ComplexOrder
variable (S : Sha2Set) (hn : S.vp.params.n = 16) {K : Type} [DecidableEq K] (key : St → K)
variable {E : Type} [Fintype E] [DecidableEq E]
noncomputable local instance (S : Sha2Set) (g : CompressionTables) : SampleableType (tablePrimitives g S.vp.params).Y :=
  inferInstanceAs (SampleableType S.Node)
local notation "Work" => WS Input Output E
variable (r : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node) (F : PortForger Input Output E)

private def collect (g : CompressionTables) (B : ℕ)
    (z : Query S × List (Query S)) :=
  if traceBudget S hn (z.1::z.2) ≤ B then select key (trace S hn g (z.1::z.2)) else none

noncomputable def witnessMachine (L qs : ℕ) (H : Input → Output) :
    Closed Work (Evidence) :=
  collect S hn key (tablesOf H) (extractionBudget L qs) <$>
    close (ITSROracles (itsrProblem S.vp (randPrims (carrier S)))) (MessageHash.machine S (carrier S) r seeds F H) []

theorem witness_cost (c : Caps) (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hs : ∀ pk, CountBound isSign (F.main pk) qs)
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    PUE (spec := unifSpec) cnt0 (witnessMachine S hn key r seeds F c.ml qs)
      (MessageHash.machineBudget S c.ml q qs + (extractionBudget c.ml qs + extractionBudget c.ml qs)) := by
  unfold witnessMachine
  simp only [map_eq_bind_pure_comp,Function.comp_def]
  apply PUE.bind (PUE.close _ (fun t s => EvalCost.const _) (MessageHash.machine_cost S (carrier S) r seeds F c q qs hq hs hc) [])
  intro z
  unfold collect
  split
  · rename_i le
    have h := (select_cost S hn key (z.1::z.2)).mono (Nat.add_le_add le le)
    have cost := h E _ (fun v _ => (pure v : Closed Work _)) 0 (fun v => PUE.pure v 0)
    simpa only [liftU_pure,pure_bind,Nat.zero_add] using cost
  · exact PUE.pure none _

open Classical in
theorem witness_success_of (c : Caps) (qs : ℕ)
    (hs : ∀ pk, CountBound isSign (F.main pk) qs) (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk))
    (g : CompressionTables)
    (selectedWin : ∀ cand ts, ts.length ≤ qs →
      (itsrProblem S.vp (tablePrimitives g S.vp.params)).Wins ts cand →
      accepts key g (select key (trace S hn g (cand::ts)))) :
    qItsrAdvantage (itsrProblem S.vp (randPrims (functions S g))) (qbItsrL (reduced S r seeds F g)) F.ρ₀ ≤
    qWeight (accepts key g) (witnessMachine S hn key r seeds F c.ml qs (oracle g)) F.ρ₀ := by
  classical
  unfold witnessMachine qItsrAdvantage
  rw [qWeight_map,tablesOf_oracle,MessageHash.machine_oracle]
  have eq : ITSROracles (itsrProblem S.vp (randPrims (carrier S))) =
      ITSROracles (itsrProblem S.vp (randPrims (functions S g))) := rfl
  rw [eq]
  apply qWeight_mono_allQ (MessageHash.transcript_support S r seeds F c qs hs hc g)
  intro z cap win
  have h := budget_le S hn c.ml qs z.1 z.2 cap.1 cap.2.1 cap.2.2
  change accepts key g (collect S hn key g _ z)
  rw [collect,ite_eq_left h]
  exact selectedWin z.1 z.2 cap.2.1 (by
    constructor
    · exact win.1
    · kexact win.2)

open Classical in
theorem witness_success (i : Fin S.vp.params.k) (cover : Covers S hn key i) (c : Caps) (qs : ℕ)
    (hs : ∀ pk, CountBound isSign (F.main pk) qs) (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk))
    (g : CompressionTables) :
    qItsrAdvantage (itsrProblem S.vp (randPrims (functions S g))) (qbItsrL (reduced S r seeds F g)) F.ρ₀ ≤
    qWeight (accepts key g) (witnessMachine S hn key r seeds F c.ml qs (oracle g)) F.ρ₀ :=
  witness_success_of S hn key r seeds F c qs hs hc g (fun cand ts _ => selected S hn key i cover g cand ts)

end Reduction.Compression.SmallItsr
#print axioms Reduction.Compression.SmallItsr.witness_success
#print axioms Reduction.Compression.SmallItsr.witness_cost
