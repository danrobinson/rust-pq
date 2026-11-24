import Integration.SlhDsaSetClosed
import Integration.SlhDsaCompressionSmallClassExtract
import Integration.SlhDsaCompressionClassCandidates
import Integration.SlhDsaCompressionLeftPrefix

namespace Reduction.Compression.SmallClass
open MLink Ideal SLHDSA SLHDSA.Security OracleComp OracleSpec PQ.Interactive PQ.QROM Quantum ENNReal Classical
open Recording.Compile
open SetOracle (uniformMean)
variable (S : Sha2Set) (hn : S.vp.params.n = 16) {E : Type} [Fintype E] [DecidableEq E] {arity : ℕ}
variable (A : (Input → Output) → Closed (WS Input Output E) (ClassCollision.Attempt S arity))

def machine (H : Input → Output) : Closed (WS Input Output E) (Option (Cell × Cell)) :=
  (fun a => extract S hn (tablesOf H) a.seed a.address a.left.val a.right.val) <$> A H

theorem machine_cost (q : ℕ) (hq : PUE (spec := unifSpec) cnt0 A q) :
    PUE (spec := unifSpec) cnt0 (machine S hn A) (q+(1+2*((22+16*arity+8)/64+1))) := by
  unfold machine
  simp only [map_eq_bind_pure_comp,Function.comp_def]
  apply PUE.bind hq
  intro a
  let B := fun (x : Option (Cell × Cell)) (_ : Input → Output) =>
    (pure x : Closed (WS Input Output E) (Option (Cell × Cell)))
  have h := PUE.liftU_bind (extract_cost S hn a.seed a.address a.left.val a.right.val)
    (B := B) (q := 0) (fun x => PUE.pure x 0)
  simpa only [B,liftU_pure,pure_bind,Nat.zero_add,a.left.property] using h

private theorem collision_reduction (g : CompressionTables) (ρ : Matrix (WS Input Output E) (WS Input Output E) ℂ) :
    @qWeight _ _ _ (ClassCollision.Attempt.wins S g) (Classical.decPred _) (A (oracle g)) ρ ≤
      qWeight (fun z => Recording.Compile.LeftPort.wins out16 g (id z)) (machine S hn A (oracle g)) ρ := by
  unfold machine
  rw [qWeight_map,tablesOf_oracle]
  apply qWeight_mono
  intro a ha
  obtain ⟨u,v,hit,ok⟩ := extract_collision S hn g a.seed a.address a.left.val a.right.val
    (a.left.property.trans a.right.property.symm) ha.1 ha.2
  rw [hit]
  exact ok

def budget (L q qs ar : ℕ) :=
  ClassOne.budget S L q qs + tcrTargets S.vp * ClassCollision.walkMax S + (1+2*((22+16*ar+8)/64+1))

include hn in
theorem class_tcr_le (rand : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node)
    (F : PortForger Input Output E) (ar : ℕ) (c : Caps) (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hs : ∀ pk, CountBound isSign (F.main pk) qs)
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    uniformMean (fun g => qSM_DT_TCR_Advantage (qbTcrArM ar (reduced S rand seeds F g))) ≤
      16*((budget S c.ml q qs ar:ℝ≥0∞)+1)^3 / 2^128 := by
  let cand := ClassCollision.signatureCandidates S rand seeds F ar
  let M := machine S hn cand
  have cost : PUE (spec := unifSpec) cnt0 M (budget S c.ml q qs ar) :=
    machine_cost S hn cand _ (ClassCollision.signatureCandidates_cost S rand seeds F ar c q qs hq hs hc)
  apply le_trans _ (Recording.Compile.LeftPort.search out16 128 (fun B => (Recording.Compile.LeftPort.out16_fraction B).le)
    M id _ cost F.ρ₀ F.posSemidef F.trace_eq_one)
  apply Finset.sum_le_sum
  intro g _
  apply mul_le_mul' le_rfl
  change qSM_DT_TCR_Advantage (qbTcrArM ar (reduced S rand seeds F g)) ≤ _
  rw [ClassCollision.candidates_success (arity := ar) (E := E) S seeds g (qbTcrArM ar (reduced S rand seeds F g)),
    ← ClassCollision.signatureCandidates_oracle]
  exact collision_reduction S hn cand g F.ρ₀
end Reduction.Compression.SmallClass
#print axioms Reduction.Compression.SmallClass.class_tcr_le
