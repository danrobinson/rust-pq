import Integration.SlhDsaShakePermutationMsgCost
namespace Reduction.ShakePermutation.MsgCost
open MLink SLHDSA SLHDSA.Security OracleComp OracleSpec PQ.Interactive Quantum Open QMsg ShakeApi
set_option allowUnsafeReducibility true in
attribute [local reducible] ShakeSecurity.primitives
variable (S : Sha2Set) (N : ℕ)
variable (rand : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node)
variable {E : Type} [Fintype E] [DecidableEq E] (F : PortForger Port Words E)
set_option maxHeartbeats 1300000 in
theorem machine_oracle (base : Xof S) (H : Port → Words) :
    machine S N base rand seeds F H = qbPrfMsgWL sufCheck (qPureBytesToInternal (forgerAt S rand seeds F (extend (SkCost.table S N H)) H)) := by
  let real := ShakeApi.primitives S (extend (SkCost.table S N H))
  let P := {ShakeApi.primitives S base with Thash := real.Thash, Hmsg := real.Hmsg}
  let c := ShakeApi.codec S base
  let r := fun (k : PublicKeyCore P.core) => rand k.pkSeed k.pkRoot
  let r' := fun (k : PublicKeyCore real.core) => rand k.pkSeed k.pkRoot
  let B := F.at H (pureBytesAlg S.vp P c r seeds)
  have hp : hashPort S N base (SkCost.table S N H) = PublicHash.impl P := by funext t; cases t <;> rfl
  have hm : machine S N base rand seeds F H = qbPrfMsgWL sufCheck (qPureBytesToInternal B) := by
    unfold machine qbPrfMsgWL
    rw [hp]
    congr 1
    unfold openMachine qMsgOpenW
    apply bind_congr
    intro pk
    apply bind_congr
    intro root
    unfold qRunForgerSig
    have main : (qPureBytesToInternal B).main = SkCost.qmForger S F base H := by
      funext pk
      simp only [B,qPureBytesToInternal,qToInternal,qPureBytesToTyped,QForger.wrapForger,
        PortForger.at,qmCSign_eq,qmCRead_eq,pureBytesView]
      rfl
    rw [main]
    apply bind_congr
    intro z
    simp only [liftQ_pure]
    unfold ShakeApi.Msg.verdict
    rw [hp]
    kexact congrArg (fun b : Bool => (pure b : QOC (WS Port Words E)
      (Lazy.OSpec P (Lazy.msgG P)) Bool)) (sufCheckOpen_eq (prims := P) ⟨pk,root⟩ z.1 z.2)
  refine hm.trans ?_
  have tr := QMsg.qbPrfMsgWL_setPrf (prims := P) real.PRF real.PRFmsg c r r' (fun _ => rfl) seeds B
  kexact tr.symm


noncomputable def native (H : Port → Words) : MsgSplit.Source (WS Port Words E) (S.Node × List SLHDSA.Byte) S.Node Bool :=
  qbPrfMsgWL sufCheck (qPureBytesToInternal (forgerAt S rand seeds F (extend (SkCost.table S N H)) H))

theorem native_pue (cap : N ≤ rawCap S 67 65536)
    (hq : ∀ pk, CountBound isPort (F.main pk) (2^40)) (hs : ∀ pk, CountBound isSign (F.main pk) 1) :
    PUE (fun _ => 0) (native S N rand seeds F) (2^41) := by
  let base : Xof S := fun _ => default
  have eq : native S N rand seeds F = machine S N base rand seeds F := by
    funext H
    exact (machine_oracle S N rand seeds F base H).symm
  rw [eq]
  exact (machine_cost S N base rand seeds F cap _ _ hq hs).mono (by cases S <;> decide +kernel)

theorem native_uniform_split (cap : N ≤ rawCap S 67 65536)
    (hq : ∀ pk, CountBound isPort (F.main pk) (2^40)) (hs : ∀ pk, CountBound isSign (F.main pk) 1) :
    ∃ pre : (Port → Words) → Closed (WS Port Words E)
      (MsgSplit.FamilyStage Port Words E (S.Node × List SLHDSA.Byte) S.Node Bool (2^41)),
      PUE (spec:=unifSpec) cnt0 pre (2^41) ∧
      ∀ H f, ansRun f (native S N rand seeds F H) = pre H >>= MsgSplit.callPost H f := by
  obtain ⟨pre,cost,eq⟩ := MsgSplit.uniform_split (native_pue S N rand seeds F cap hq hs) _ le_rfl
  exact ⟨pre,cost,fun H f => eq H f (MsgSplit.native_count S _ F rand seeds H 1 hs)⟩

end Reduction.ShakePermutation.MsgCost
#print axioms Reduction.ShakePermutation.MsgCost.native_uniform_split
