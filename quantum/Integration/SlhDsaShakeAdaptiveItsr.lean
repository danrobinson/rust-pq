import Integration.SlhDsaShakeAdaptiveMachine
import Integration.SlhDsaShakeAdaptiveRows

namespace Reduction.ShakeAdaptive
open MLink SLHDSA SLHDSA.Security OracleComp OracleSpec PQ.Interactive PQ.QROM Quantum QMsg QItsr KeyedHash
open scoped ComplexOrder Kronecker ENNReal
set_option maxRecDepth 10000
set_option maxHeartbeats 1800000
set_option allowUnsafeReducibility true in
attribute [local reducible] ShakeApi.primitives ShakeSecurity.primitives
variable (S : Sha2Set) (N : ℕ) {E : Type} [Fintype E] [DecidableEq E]
  (rand : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node)
  (F : PortForger (ShakeApi.Input N) (Bytes S.vp.params.m) E)
local notation "A" => fun H => qPureBytesToInternal (ShakeApi.rawForger S N rand seeds F H)
local notation "P" => fun H => ShakeApi.primitives S (ShakeApi.extend H)

/-- Adaptive target security for the signature reduction with public quantum
access to the same raw XOF used by every hash primitive. -/
theorem signature_itsr (q s : ℕ) (c : Caps) (cap : 3*S.vp.params.n+c.ml ≤ N)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hs : ∀ pk, CountBound isSign (F.main pk) s)
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    SetOracle.uniformMean (fun H => qItsrAdvantage (itsrProblem S.vp (P H)) (qbItsrL (A H)) F.ρ₀) ≤
      itsrBound S.vp.params (q+itsrHashes S.vp s) s := by
  classical
  let emb := embedding S c cap
  rw [ShakeXof.resample emb (le_refl S.vp.params.m)]
  apply PQ.QROM.avg_le
  intro g
  let port := ShakeXof.write emb g (n := S.vp.params.m)
  obtain ⟨L,B,I,ρ,x,hq',eq⟩ := interactive_machine S N rand seeds F q s hq hs
  let Ev : (Fin s → S.Node) → (Row S c → Bytes S.vp.params.m) →
      Option (ShakeSingle.Query S) × List (S.Node × S.Node × List SLHDSA.Byte) → Prop :=
    fun Rs H ot ↦ itsrAWin (SetDigest.idxCov S.vp) Rs H
      (⟨QReg.of Unit,(SetOracle.ocO S c ot.1,ot.2.map (SetOracle.tg S c))⟩ :
        Σ _ : QReg, Row S c × List (S.Node × S.Node × BList SLHDSA.Byte c.ml))
  have key (H : Row S c → Bytes S.vp.params.m) :
      qItsrAdvantage (itsrProblem S.vp (P (port H))) (qbItsrL (A (port H))) F.ρ₀ ≤
        PQ.QROM.avg (fun Rs : Fin s → S.Node ↦ qprob I (port H)
          (IAdv.flat (rndCh Rs) (IAdv.stop (L := L) (spec := qromSpec (ShakeApi.Input N) (Bytes S.vp.params.m))) s [] x)
          ρ (fun p ↦ Ev Rs H p.2)) := by
    have hA := target_support S N rand seeds F c hc (port H)
    have hC := target_count S N rand seeds F s hs (port H)
    unfold qItsrAdvantage
    rw [presample (s := s) (itsrProblem S.vp (P (port H))) rfl _ _ s [] []
      (cb_isT hC) (by simp) _]
    apply PQ.QROM.avg_mono
    intro Rs
    rw [eq (port H) Rs (Ev Rs H)]
    refine qWeight_mono_allQ (close_rndImpl_supp Rs _ _ _ s [] hA hC) (fun z hz hw ↦ ?_) _
    simp only [List.length_nil,List.drop_zero,List.nil_append,Nat.zero_add] at hw hz
    exact win_conv S c cap g H Rs z.1 z.2 hz.1
      (fun y hy ↦ (hz.2.2 y hy).resolve_left (List.not_mem_nil)) hz.2.1 hw
  apply (PQ.QROM.avg_mono key).trans
  rw [PQ.QROM.avg_comm]
  change Pull.itsrPExp port (SetOracle.tg S c) (fun _ ↦ SetOracle.ocO S c) I ρ s x (SetDigest.idxCov S.vp) ≤ _
  exact (Pull.itsrP_adaptive_le emb.injective (ShakeXof.different_at emb g)
    (SetOracle.cover_mono S) hq').trans (SetOracle.digest_bound S _ _)

end Reduction.ShakeAdaptive
#print axioms Reduction.ShakeAdaptive.signature_itsr
