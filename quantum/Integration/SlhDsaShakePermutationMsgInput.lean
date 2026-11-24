import Integration.SlhDsaShakePermutationMsgPhases

namespace Reduction.ShakePermutation.MsgSplit
open Classical MLink SLHDSA SLHDSA.Security Quantum OracleComp OracleSpec PQ.Interactive QMsg
variable {W D R A : Type} [Fintype W] [Inhabited R]

def valid (good : D → Prop) : Stage W D R A → Prop
  | .inl _ => True
  | .inr (d,_) => good d

theorem before_inputs (p : Source W D R A) (good : D → Prop)
    (cap : AllQueries (QG W (Gfin good)) (fun _ => True) p) :
    AllQueries (fun _ => True) (valid good) (before p) := by
  induction p using OracleComp.inductionOn with
  | pure a => simp only [before,OracleComp.construct_pure]; trivial
  | query_bind i k ih =>
    have shape := (allQ_query_bind _ _ _ _).mp cap
    rcases i with j | (n|d)
    · exact (allQ_query_bind _ _ _ _).mpr ⟨trivial,fun r => ih r (shape.2 r)⟩
    · exact (allQ_query_bind _ _ _ _).mpr ⟨trivial,fun r => ih r (shape.2 r)⟩
    · exact shape.1

set_option allowUnsafeReducibility true in
attribute [local reducible] ShakeSecurity.primitives
variable (S : Sha2Set) (base : ShakeApi.Xof S) (rand : S.Node → S.Node → ProbComp S.Node)
    (seeds : ProbComp S.Node) {E : Type} [Fintype E] [DecidableEq E] (F : PortForger Port Words E)
    (port : Port → Words)
local notation "P₀" => ShakeApi.primitives S base
local notation "P" => qbPrfMsgWL sufCheck (qPureBytesToInternal (ShakeApi.forgerAt S rand seeds F base port))

theorem native_inputs (c : Caps) (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    AllQueries (fun _ => True) (valid (fun d : S.Node × List SLHDSA.Byte => d.2.length ≤ c.ml)) (before P) := by
  apply before_inputs
  exact allQ_qLazyRun (PublicHash.impl P₀) (fun d : S.Node × List SLHDSA.Byte => d.2.length ≤ c.ml) _
    (allQ_qMsgOpenW P₀ c.ml sufCheck _ (allQ_qPureBytesToInternal c.ml _ fun pk =>
      allQ_compileQ c _ (F.main pk) (hc pk)))

end Reduction.ShakePermutation.MsgSplit
#print axioms Reduction.ShakePermutation.MsgSplit.native_inputs
