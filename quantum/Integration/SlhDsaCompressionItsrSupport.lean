import Integration.SlhDsaCompressionItsrTransport
import Integration.SlhDsaCompressionItsrSearch

namespace Reduction.Compression.MessageHash
open MLink Ideal SLHDSA SLHDSA.Security OracleComp OracleSpec PQ.Interactive Quantum KeyedHash QMsg QItsr
variable (S : Sha2Set) {E : Type} [Fintype E] [DecidableEq E]
local notation "Work" => WS Input Output E
variable (r : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node) (F : PortForger Input Output E)

private theorem machine_support (c : Caps) (qs : ℕ)
    (hs : ∀ pk, CountBound isSign (F.main pk) qs)
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) (g : CompressionTables) :
    let f := functions S g
    let A := qbItsrL (reduced S r seeds F g)
    AllQueries (QG Work (Gfin (Ptgt (randPrims f) c.ml)))
      (fun z : Query S => z.2.2.2.length ≤ c.ml) A ∧ CountBound (QC Work isR) A qs := by
  intro f A
  have hQ (pk) := mainAt_cap S f F c hc (oracle g) pk
  simp only [mainAt_eq S f F r seeds] at hQ
  have hO := allQ_qItsrOpen (randPrims f) c.ml (reduced S r seeds F g) hQ
  refine ⟨allQ_and (allQ_qLazyRun _ (Ptgt (randPrims f) c.ml) _
    (allQ_mono (fun _ h => h) (fun _ _ => trivial) hO)) (out_qLazyRun _ _ hO),?_⟩
  exact cb_qLazyRun _ _ (cb_qItsrOpen (randPrims f) _ fun pk =>
    cb_qPureBytesToInternal _ (fun pkb => cb_compileQ (oracle g) (F.main pkb) (hs pkb)) pk)

variable {X K Y Ix α : Type} {W : Type} [Fintype W]

private theorem target_support (prob : ITSRProblem K X Y Ix) (P : X → Prop) (good : α → Prop)
    (A : QOC W (unifSpec + ITSRTargetSpec X K) α) (n : ℕ) (ts : List (K × X))
    (ha : AllQueries (QG W (Gfin P)) good A) (hb : CountBound (QC W isR) A n) :
    AllQueries (fun _ => True) (fun z : α × List (K × X) => good z.1 ∧ z.2.length ≤ ts.length+n ∧
      ∀ x ∈ z.2, x ∈ ts ∨ P x.2) (close (ITSROracles prob) A ts) := by
  induction A using OracleComp.inductionOn generalizing n ts with
  | pure a => exact ⟨ha,by simp,fun x hx => Or.inl hx⟩
  | query_bind q k ih =>
    rcases q with j|m|x
    · rw [close_instr_bind]
      exact ⟨trivial,fun i => ih i _ ts (ha.2 i) (hb i)⟩
    · have hf : ForwardsUnif (ITSROracles prob) := forwardsUnif_ofLift_add _
      rw [close_unif_bind _ hf]
      exact ⟨trivial,fun i => ih i _ ts (ha.2 i) (hb i)⟩
    · have hc : 0 < n ∧ ∀ r, CountBound (QC W isR) (k r) (n-1) := hb
      have hx : P x := ha.1
      rw [close_query_bind]
      have step : ((ITSROracles prob) (Sum.inr x)).run ts =
          (fun r => (r,ts ++ [(r,x)])) <$> prob.khf.keygen := by simp [ITSROracles,ITSRTargetOracle]
      rw [step,liftU_map,bind_map_left]
      apply allQ_bind (allQ_true_of (fun _ => trivial) _)
      intro r _
      apply allQ_mono (fun _ h => h) _ (ih r (n-1) (ts++[(r,x)]) (ha.2 r) (hc.2 r))
      intro z hz
      refine ⟨hz.1,?_,?_⟩
      · have le := hz.2.1
        simp only [List.length_append,List.length_cons,List.length_nil] at le
        omega
      · intro y hy
        rcases hz.2.2 y hy with h|h
        · rcases List.mem_append.mp h with h|h
          · exact Or.inl h
          · rw [List.mem_singleton.mp h]; exact Or.inr hx
        · exact Or.inr h

theorem transcript_support (c : Caps) (qs : ℕ)
    (hs : ∀ pk, CountBound isSign (F.main pk) qs)
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) (g : CompressionTables) :
    let prob := itsrProblem S.vp (randPrims (functions S g))
    let A := qbItsrL (reduced S r seeds F g)
    AllQueries (fun _ => True) (fun z : Query S × List (Query S) =>
      z.1.2.2.2.length ≤ c.ml ∧ z.2.length ≤ qs ∧ ∀ x ∈ z.2, x.2.2.2.length ≤ c.ml)
      (close (ITSROracles prob) A []) := by
  intro prob A
  obtain ⟨h₁,h₂⟩ := machine_support S r seeds F c qs hs hc g
  simpa only [List.length_nil,Nat.zero_add,List.not_mem_nil,false_or,Ptgt] using
    target_support prob (Ptgt _ c.ml) _ A qs [] h₁ h₂

end Reduction.Compression.MessageHash
#print axioms Reduction.Compression.MessageHash.transcript_support
