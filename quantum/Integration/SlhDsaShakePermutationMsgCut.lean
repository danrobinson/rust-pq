import Integration.SlhDsaShakePermutationMsgBudget
import Integration.SlhDsaShakePermutationMsgInput

namespace Reduction.ShakePermutation.MsgCost
open Classical MLink SLHDSA SLHDSA.Security OracleComp OracleSpec PQ.Interactive Quantum Open QMsg ShakeApi MsgSplit
set_option allowUnsafeReducibility true in
attribute [local reducible] ShakeSecurity.primitives
variable (S : Sha2Set) (N : ℕ)
variable (rand : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node)
variable {E : Type} [Fintype E] [DecidableEq E] (F : PortForger Port Words E)
local notation "Work" => WS Port Words E
local notation "D" => S.Node × List SLHDSA.Byte
local notation "Stages" => FamilyStage Port Words E D S.Node Bool (2^41)

private theorem pullback {I A B : Type} {spec : OracleSpec I} (p : OracleComp spec A) (f : A → B)
    (accept : B → Prop) (h : AllQueries (fun _ => True) accept (f <$> p)) :
    AllQueries (fun _ => True) (fun a => accept (f a)) p := by
  induction p using OracleComp.inductionOn with
  | pure a => exact h
  | query_bind t k ih =>
    rw [map_bind] at h
    exact ⟨trivial,fun i => ih i (h.2 i)⟩

def validStage (limit : ℕ) : Stages → Prop
  | .inl _ => True
  | .inr (d,_) => d.2.length ≤ limit

/-- The measured public prefix and its continuations can be queried against
different public permutations. Every pending message respects the byte
forger's original encoded-length cap. Pointwise specialization gives back
the entire native prefix, including its final quantum state. -/
theorem signature_cut (c : Caps) (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk))
    (cap : N ≤ rawCap S 67 65536) (hq : ∀ pk, CountBound isPort (F.main pk) (2^40))
    (hs : ∀ pk, CountBound isSign (F.main pk) 1) :
    ∃ pre : (Port → Words) → Closed Work Stages, PUE (spec:=unifSpec) cnt0 pre (2^41) ∧
      (∀ H, AllQueries (fun _ => True) (validStage S (E:=E) c.ml) (pre H)) ∧
      ∀ H, before (native S N rand seeds F H) = specialize H <$> pre H := by
  obtain ⟨pre,cost,eq⟩ := family_before (native_pue S N rand seeds F cap hq hs) _ le_rfl
  refine ⟨pre,cost,?_,eq⟩
  intro H
  have lim := native_inputs S (extend (SkCost.table S N H)) rand seeds F H c hc
  change AllQueries _ _ (before (native S N rand seeds F H)) at lim
  rw [eq] at lim
  have h := pullback _ _ _ lim
  apply QMsg.allQ_mono (fun _ h => h) _ h
  intro z hz
  rcases z with a|⟨d,p⟩ <;> exact hz

end Reduction.ShakePermutation.MsgCost
#print axioms Reduction.ShakePermutation.MsgCost.signature_cut
