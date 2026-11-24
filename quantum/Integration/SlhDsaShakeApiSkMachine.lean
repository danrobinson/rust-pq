import Integration.SlhDsaShakeApiForger
import Integration.SlhDsaShakeApiSkCost
import Integration.SlhDsaShakeXofPrf
import Integration.SlhDsaCompressionPrfBudget

namespace Reduction.ShakeApi.Sk
open MLink SLHDSA SLHDSA.Security OracleComp OracleSpec PQ.Interactive Quantum Resources2 Open QMsg
open scoped Kronecker
variable (S : Sha2Set) (N : ℕ) (base : Xof S)
local notation "P₀" => primitives S base
variable (rand : S.Node → S.Node → ProbComp S.Node) (answer : S.Node × Adrs → S.Node)
variable {E : Type} [Fintype E] [DecidableEq E] (F : PortForger (Input N) (Bytes S.vp.params.m) E)
local notation "Workspace" => WS (Input N) (Bytes S.vp.params.m) E

noncomputable def signer (pk root sk : S.Node) (H : RawTable S N) :
    QueryImpl (unifSpec + (List SLHDSA.Byte →ₒ GeneralScheme.SignatureCore S.vp (P₀).core))
      (StateT (SigLog S.vp P₀) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (SigLog S.vp P₀) ProbComp) +
    sigSignOracle (vp := S.vp) (prims := P₀) (fun m => simulateQ (handler S N base answer H)
      (openSignP (signRand S rand base) ⟨pk,root⟩ sk m))

private theorem signer_cost (pk root sk : S.Node) (t) (log : SigLog S.vp P₀) :
    EvalCost (fun H => (signer S N base rand answer pk root sk H t).run log)
      (sgnW (Lazy.signHashes S.vp + 1) t) := by
  rcases t with n|m
  · exact EvalCost.const _
  · simp only [signer,QueryImpl.add_apply_inr,sigSignOracle,run_appendLog_apply]
    exact ((sign_cost S N base answer (signRand S rand base) ⟨pk,root⟩ sk m).bind
      fun sig => EvalCost.const (X := Input N) (Y := Bytes S.vp.params.m)
        (pure (sig,log ++ [⟨m,sig⟩]) : ProbComp _)).mono (Nat.le_of_eq (Nat.add_zero _))

noncomputable def answered (pk : S.Node) (H : RawTable S N) : Closed Workspace Bool := do
  let sk ← liftU ($ᵗ S.Node)
  let root ← liftU (simulateQ (handler S N base answer H) (openKeygenP (vp := S.vp) P₀ pk))
  let z ← close (signer S N base rand answer pk root sk H) (qmForger S N F base H ⟨pk,root⟩) []
  liftU (simulateQ (fun t => pure (hashPort S N base H t) : QueryImpl _ ProbComp)
    (sufCheckOpen ⟨pk,root⟩ z.1 z.2))

def budget (q qs : ℕ) := Lazy.keygenHashes S.vp + q + qs * (Lazy.signHashes S.vp + 1) + (1 + verifyHashes S.vp)

theorem answered_cost (pk : S.Node) (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hs : ∀ pk, CountBound isSign (F.main pk) qs) :
    PUE (spec := unifSpec) cnt0 (answered S N base rand answer F pk) (budget S q qs) := by
  unfold answered
  have w (sk root : S.Node) : PUE (spec := unifSpec) cnt0 (fun H =>
      close (signer S N base rand answer pk root sk H) (qmForger S N F base H ⟨pk,root⟩) [] >>= fun z =>
      (liftU (simulateQ (fun t => pure (hashPort S N base H t) : QueryImpl _ ProbComp)
        (sufCheckOpen ⟨pk,root⟩ z.1 z.2)) : Closed Workspace Bool))
      (q + qs*(Lazy.signHashes S.vp+1) + (1+verifyHashes S.vp)) := by
    refine PUE.bind (PUE.close _ (signer_cost S N base rand answer pk root sk)
      (pue_qmForger S N F base q qs _ hq hs ⟨pk,root⟩) _) fun z => ?_
    have h := PUE.liftU_bind (E := E) (q := 0) (B := fun b _ => (pure b : Closed Workspace _))
      (check_cost S N base ⟨pk,root⟩ z.1 z.2) (fun b => PUE.pure b 0)
    simpa only [bind_pure,Nat.zero_add] using h
  have h := PUE.liftU_bind (EvalCost.const (X := Input N) (Y := Bytes S.vp.params.m) ($ᵗ S.Node : ProbComp S.Node))
    fun sk => PUE.liftU_bind (key_cost S N base answer pk) (w sk)
  exact h.mono (by unfold budget; omega)

end Reduction.ShakeApi.Sk
#print axioms Reduction.ShakeApi.Sk.answered_cost
