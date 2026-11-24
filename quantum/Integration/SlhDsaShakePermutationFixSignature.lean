import Integration.SlhDsaShakePermutationFixCount
import Integration.SlhDsaShakeXofSignature

namespace Reduction.ShakePermutation.Fix.Machine
open Quantum PQ.Interactive OracleSpec OracleComp Classical ENNReal SLHDSA SLHDSA.Security MLink
open scoped ComplexOrder

abbrev Msg := List SLHDSA.Byte × List SLHDSA.Byte
abbrev Sig := Option (List SLHDSA.Byte)
abbrev Signing := unifSpec + (Msg →ₒ Sig)

structure Forger (U : Type) [Fintype U] (T : ℕ) where
  main : List SLHDSA.Byte → Source U T Signing (Msg × Sig)
  initial : Matrix U U ℂ
  pos : initial.PosSemidef
  trace : initial.trace = 1

variable {X Y U : Type} {T : ℕ} [Fintype X] [Fintype Y] [Fintype U]
  [DecidableEq X] [DecidableEq Y] [AddCommGroup Y] [DecidableEq U]
variable (A : Access X Y) (L : ℕ) (base : X) (F : Forger U T)

noncomputable def rawForger : PortForger X Y (Access.Scratch T U) where
  main pk := raw A L base (F.main pk)
  ρ₀ := Workspace.state base F.initial
  posSemidef := Workspace.state_pos base F.initial F.pos
  trace_eq_one := (Workspace.state_trace base F.initial).trans F.trace

noncomputable def idealForger {K : Type} (H : X → Y)
    (scheme : SignatureAlg ProbComp Msg (List SLHDSA.Byte) K Sig) : QForger U scheme where
  main pk := ideal (transform (A.value L H)) (F.main pk)
  ρ₀ := F.initial
  posSemidef := F.pos
  trace_eq_one := F.trace

private theorem post_weight {W α β : Type} [Fintype W] (p : Closed W α) (g : α → ProbComp β)
    (ev : β → Prop) [DecidablePred ev] (M : Matrix W W ℂ) :
    qWeight ev (p >>= fun a => liftU (g a)) M = ∑' a, qWeight (· = a) p M * prob (g a) ev := by
  induction p using OracleComp.inductionOn generalizing M with
  | pure a =>
    simp only [pure_bind,qWeight_pure,ite_mul,zero_mul]
    rw [tsum_eq_single a]
    · rw [ite_eq_left rfl]
      have h := qWeight_liftU_bind ev (g a) (pure : β → Closed W β) pure (ENNReal.ofReal M.trace.re) M
        (fun b => by simp)
      simpa using h
    · intro b hb; simp [Ne.symm hb]
  | query_bind t k ih =>
    rw [bind_assoc]
    rcases t with j | n
    · simp only [qWeight_instr_bind,ih,Finset.sum_mul]
      rw [Summable.tsum_finsetSum (fun _ _ => CompleteLattice.summable)]
    · simp only [qWeight_unif_bind,ih,mul_assoc,Finset.sum_mul,ENNReal.tsum_mul_left]
      rw [Summable.tsum_finsetSum (fun _ _ => CompleteLattice.summable)]

/-- Equality of complete signature games, including key generation, the
logged signing transcript and the final (potentially randomized) verifier. -/
theorem signature_weight {K : Type} (H : X → Y) (scheme : SignatureAlg ProbComp Msg (List SLHDSA.Byte) K Sig)
    (fresh : QueryLog (Msg →ₒ Sig) → Msg → Sig → Bool) :
    qWeight (· = true) (qSigExperiment fresh ((rawForger A L base F).at H scheme))
        (Workspace.state base F.initial) =
      qWeight (· = true) (qSigExperiment fresh (idealForger A L F H scheme)) F.initial := by
  unfold qSigExperiment
  rw [qWeight_liftU_bind_tsum,qWeight_liftU_bind_tsum]
  refine tsum_congr fun ks => congrArg _ ?_
  let finish (r : (Msg × Sig) × QueryLog (Msg →ₒ Sig)) : ProbComp Bool := do
    let v ← scheme.verify ks.1 r.1.1 r.1.2
    pure (fresh r.2 r.1.1 r.1.2 && v)
  have after (W : Type) [Fintype W] (r) :
      (liftU (scheme.verify ks.1 r.1.1 r.1.2) >>= fun v => pure (fresh r.2 r.1.1 r.1.2 && v) : Closed W Bool) =
      liftU (finish r) := by simp [finish]
  simp only [after,post_weight]
  apply tsum_congr
  intro r
  letI : DecidablePred (fun x : (Msg × Sig) × QueryLog (Msg →ₒ Sig) => x = r) :=
    fun x => Classical.propDecidable (x = r)
  exact congrArg (fun z => z * prob (finish r) (· = true))
    (weight A L base H (F.main ks.1) (· = r) (signImpl scheme ks.1 ks.2) [] F.initial)

end Reduction.ShakePermutation.Fix.Machine
#print axioms Reduction.ShakePermutation.Fix.Machine.signature_weight
