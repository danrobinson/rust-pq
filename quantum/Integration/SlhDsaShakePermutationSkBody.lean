import Integration.SlhDsaShakePermutationSkCost

namespace Reduction.ShakePermutation.SkCost
open Classical MLink SLHDSA SLHDSA.Security OracleComp OracleSpec PQ.Interactive Quantum Resources2 Open QMsg ShakeApi
open scoped Kronecker
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
variable (S : Sha2Set) (N : ℕ) (base : Xof S)
local notation "P₀" => ShakeApi.primitives S base
variable (rand : S.Node → S.Node → ProbComp S.Node) (answer : S.Node × Adrs → S.Node)
variable {E : Type} [Fintype E] [DecidableEq E] (F : PortForger Port Words E)
local notation "Workspace" => WS Port Words E

noncomputable def qmForger (base : Xof S) (H : Port → Words)
    (pk : PublicKeyCore (ShakeApi.primitives S base).core) :
    QOC (WS Port Words E)
      (unifSpec + (List SLHDSA.Byte →ₒ GeneralScheme.SignatureCore S.vp (ShakeApi.primitives S base).core))
      (List SLHDSA.Byte × GeneralScheme.SignatureCore S.vp (ShakeApi.primitives S base).core) :=
  Guarded.readForgery pureEncode ([], constSig default) <$>
    wrap0 (Guarded.signingImpl pureEncode)
      (qmCRead (decodePureSig S.vp (ShakeApi.primitives S base) (ShakeApi.codec S base))
          (Except.error (External.Error.contextTooLong 0)) <$>
        wrap0 (qmCSign (encodePureSig S.vp (ShakeApi.primitives S base) (ShakeApi.codec S base)))
          (compileQ H (F.main (encodePublicKey (ShakeApi.codec S base) pk))))

theorem pue_qmForger (base : Xof S) (q qs k : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hqs : ∀ pk, CountBound isSign (F.main pk) qs)
    (pk : PublicKeyCore (ShakeApi.primitives S base).core) :
    PUE (sgnW k) (fun H ↦ qmForger S F base H pk) (q + qs * k) := by
  unfold qmForger
  refine PUE.map _ (PUE.wrap0 (cnt := sgnW k) _ ?_ (PUE.map _ (PUE.wrap0 (cnt := sgnW k)
    (cnt' := sgnW k) _ ?_ (PUE.compileQ (sgnW k) _ _
    (wCount_of_countBound isPort isSign _ k ?_ _ q qs (hq _) (hqs _))))))
  · intro t
    rcases t with n | e
    · exact wCount_liftM_query _ _ le_rfl
    · simp only [Guarded.signingImpl]
      split
      · exact trivial
      · exact WCount.map (wCount_liftM_query _ _ le_rfl) _
  · intro t
    rcases t with n | m
    · exact wCount_liftM_query _ _ le_rfl
    · exact WCount.map (wCount_liftM_query _ _ le_rfl) _
  · intro t
    rcases t with j | u | n | m <;> simp [compileW, isPort, isSign]

variable (cap : N ≤ ShakeApi.rawCap S 67 65536)
include cap in
private theorem signer_cost (pk root sk : S.Node) (t) (log : SigLog S.vp P₀) :
    EvalCost (fun H => (ShakeApi.Sk.signer S N base rand answer pk root sk (table S N H) t).run log)
      (sgnW (483*(Lazy.signHashes S.vp + 1)) t) := by
  rcases t with n|m
  · exact EvalCost.const _
  · simp only [ShakeApi.Sk.signer,QueryImpl.add_apply_inr,sigSignOracle,run_appendLog_apply]
    exact ((sign_cost S N base answer (signRand S rand base) ⟨pk,root⟩ sk m cap).bind
      fun sig => EvalCost.const (X := Port) (Y := Words)
        (pure (sig,log ++ [⟨m,sig⟩]) : ProbComp _)).mono (Nat.le_of_eq (Nat.add_zero _))

noncomputable def answered (pk : S.Node) (H : Port → Words) : Closed Workspace Bool := do
  let sk ← liftU ($ᵗ S.Node)
  let root ← liftU (simulateQ (ShakeApi.Sk.handler S N base answer (table S N H)) (openKeygenP (vp := S.vp) P₀ pk))
  let z ← close (ShakeApi.Sk.signer S N base rand answer pk root sk (table S N H)) (qmForger S F base H ⟨pk,root⟩) []
  liftU (simulateQ (fun t => pure (hashPort S N base (table S N H) t) : QueryImpl _ ProbComp)
    (sufCheckOpen ⟨pk,root⟩ z.1 z.2))

def budget (q qs : ℕ) := 483*Lazy.keygenHashes S.vp + q + qs * (483*(Lazy.signHashes S.vp + 1)) + (483*(1 + verifyHashes S.vp))

include cap in
theorem answered_cost (pk : S.Node) (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hs : ∀ pk, CountBound isSign (F.main pk) qs) :
    PUE (spec := unifSpec) cnt0 (answered S N base rand answer F pk) (budget S q qs) := by
  unfold answered
  have w (sk root : S.Node) : PUE (spec := unifSpec) cnt0 (fun H =>
      close (ShakeApi.Sk.signer S N base rand answer pk root sk (table S N H)) (qmForger S F base H ⟨pk,root⟩) [] >>= fun z =>
      (liftU (simulateQ (fun t => pure (hashPort S N base (table S N H) t) : QueryImpl _ ProbComp)
        (sufCheckOpen ⟨pk,root⟩ z.1 z.2)) : Closed Workspace Bool))
      (q + qs*(483*(Lazy.signHashes S.vp+1)) + (483*(1+verifyHashes S.vp))) := by
    refine PUE.bind (PUE.close _ (signer_cost S N base rand answer cap pk root sk)
      (pue_qmForger S F base q qs _ hq hs ⟨pk,root⟩) _) fun z => ?_
    have h := PUE.liftU_bind (E := E) (q := 0) (B := fun b _ => (pure b : Closed Workspace _))
      (check_cost S N base ⟨pk,root⟩ z.1 z.2 cap) (fun b => PUE.pure b 0)
    simpa only [bind_pure,Nat.zero_add] using h
  have h := PUE.liftU_bind (EvalCost.const (X := Port) (Y := Words) ($ᵗ S.Node : ProbComp S.Node))
    fun sk => PUE.liftU_bind (key_cost S N base answer pk cap) (w sk)
  exact h.mono (by unfold budget; omega)


theorem benchmark_budget : budget S (2^40) 1 ≤ 2^41 := by cases S <;> decide +kernel

end Reduction.ShakePermutation.SkCost
#print axioms Reduction.ShakePermutation.SkCost.answered_cost
