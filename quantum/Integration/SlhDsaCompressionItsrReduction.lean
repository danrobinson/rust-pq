import Integration.SlhDsaCompressionItsrMachine
import Integration.SlhDsaCompressionItsrSupport

namespace Reduction.Compression.MessageHash
open MLink Ideal MIdeal.Hmsg SLHDSA SLHDSA.Security OracleComp OracleSpec PQ.Interactive Quantum KeyedHash QMsg QItsr
open scoped ComplexOrder
variable (S : Sha2Set) {E : Type} [Fintype E] [DecidableEq E]
local notation "Work" => WS Input Output E
variable (r : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node) (F : PortForger Input Output E)

def extractionBudget (L qs : ℕ) := (qs+1)*((L+3*S.vp.params.n+16)/128+3)

private theorem budget_le (L qs : ℕ) (cand : Query S) (ts : List (Query S))
    (hc : cand.2.2.2.length ≤ L) (hlen : ts.length ≤ qs) (ht : ∀ x ∈ ts, x.2.2.2.length ≤ L) :
    traceBudget S (cand::ts) ≤ extractionBudget S L qs := by
  let B := (L+3*S.vp.params.n+16)/128+3
  have aux (xs : List (Query S)) (ok : ∀ x ∈ xs, x.2.2.2.length ≤ L) : traceBudget S xs ≤ xs.length*B := by
    induction xs with
    | nil => simp [traceBudget]
    | cons x ys ih =>
      have small := ok x (List.mem_cons_self ..)
      have tail := ih (fun t ht => ok _ (List.mem_cons_of_mem _ ht))
      have one : (ib S x).length + 2 ≤ B := by rw [ib_length]; dsimp [B]; omega
      exact (Nat.add_le_add one tail).trans (by simp only [List.length_cons,Nat.add_mul,Nat.one_mul,Nat.add_comm,Nat.le_refl])
  have h := aux (cand::ts) (by
    intro x hx
    rcases List.mem_cons.mp hx with rfl|h
    · exact hc
    · exact ht _ h)
  exact h.trans (Nat.mul_le_mul_right _ (Nat.succ_le_succ hlen))

private def collect (i : Fin S.vp.params.k) (g : CompressionTables) (B : ℕ)
    (z : Query S × List (Query S)) :=
  if traceBudget S (z.1::z.2) ≤ B then select S i (trace S g z.1 z.2) else none

noncomputable def witnessMachine (i : Fin S.vp.params.k) (L qs : ℕ) (H : Input → Output) :
    Closed Work (Option HmacKey.Evidence) :=
  collect S i (tablesOf H) (extractionBudget S L qs) <$>
    close (ITSROracles (itsrProblem S.vp (randPrims (carrier S)))) (machine S (carrier S) r seeds F H) []

theorem witness_cost (hw : S.vp.params.n ≠ 16) (i : Fin S.vp.params.k) (c : Caps) (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hs : ∀ pk, CountBound isSign (F.main pk) qs)
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    PUE (spec := unifSpec) cnt0 (witnessMachine S r seeds F i c.ml qs)
      (machineBudget S c.ml q qs + (extractionBudget S c.ml qs + extractionBudget S c.ml qs)) := by
  unfold witnessMachine
  simp only [map_eq_bind_pure_comp,Function.comp_def]
  apply PUE.bind (PUE.close _ (fun t s => EvalCost.const _) (machine_cost S (carrier S) r seeds F c q qs hq hs hc) [])
  intro z
  unfold collect
  split
  · rename_i le
    have h := (select_cost S hw z.1 z.2 i).mono (Nat.add_le_add le le)
    have cost := h E _ (fun v _ => (pure v : Closed Work _)) 0 (fun v => PUE.pure v 0)
    simpa only [liftU_pure,pure_bind,Nat.zero_add] using cost
  · exact PUE.pure none _

open Classical in
theorem witness_success (hw : S.vp.params.n ≠ 16) (i : Fin S.vp.params.k) (c : Caps) (qs : ℕ)
    (hs : ∀ pk, CountBound isSign (F.main pk) qs) (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk))
    (g : CompressionTables) :
    qItsrAdvantage (itsrProblem S.vp (randPrims (functions S g))) (qbItsrL (reduced S r seeds F g)) F.ρ₀ ≤
    qWeight (accepts S i g) (witnessMachine S r seeds F i c.ml qs (oracle g)) F.ρ₀ := by
  classical
  unfold witnessMachine qItsrAdvantage
  rw [qWeight_map,tablesOf_oracle,machine_oracle]
  have eq : ITSROracles (itsrProblem S.vp (randPrims (carrier S))) =
      ITSROracles (itsrProblem S.vp (randPrims (functions S g))) := rfl
  rw [eq]
  apply qWeight_mono_allQ (transcript_support S r seeds F c qs hs hc g)
  intro z cap win
  have h := budget_le S c.ml qs z.1 z.2 cap.1 cap.2.1 cap.2.2
  change accepts S i g (collect S i g _ z)
  rw [collect,ite_eq_left h]
  exact selects_hit S hw g z.1 z.2 (by
    constructor
    · exact win.1
    · kexact win.2) i

end Reduction.Compression.MessageHash
#print axioms Reduction.Compression.MessageHash.witness_cost
#print axioms Reduction.Compression.MessageHash.witness_success
