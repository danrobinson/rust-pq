import Integration.SlhDsaShakeApiCost
import Integration.SlhDsaSetItsrMach

namespace Reduction.ShakeApi

open MLink OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal PQ.Interactive PQ.QROM Quantum
open scoped ComplexOrder Kronecker

abbrev signRand (S : Sha2Set) (r : S.Node → S.Node → ProbComp S.Node)
    (base : Xof S) : PublicKeyCore (primitives S base).core → ProbComp S.Node :=
  fun pk => r pk.pkSeed pk.pkRoot

variable (S : Sha2Set) {E : Type} [Fintype E] [DecidableEq E] (N : ℕ)
  (optRand₀ : S.Node → S.Node → ProbComp S.Node) (pkSeedDist₀ : ProbComp S.Node)
  (F : PortForger (Input N) (Bytes S.vp.params.m) E)
noncomputable def qmForger (base : Xof S) (H : Input N → (Bytes S.vp.params.m))
    (pk : PublicKeyCore (primitives S base).core) :
    QOC (WS (Input N) (Bytes S.vp.params.m) E)
      (unifSpec + (List SLHDSA.Byte →ₒ GeneralScheme.SignatureCore S.vp (primitives S base).core))
      (List SLHDSA.Byte × GeneralScheme.SignatureCore S.vp (primitives S base).core) :=
  Guarded.readForgery pureEncode ([], constSig default) <$>
    wrap0 (Guarded.signingImpl pureEncode)
      (qmCRead (decodePureSig S.vp (primitives S base) (codec S base))
          (Except.error (External.Error.contextTooLong 0)) <$>
        wrap0 (qmCSign (encodePureSig S.vp (primitives S base) (codec S base)))
          (compileQ H (F.main (encodePublicKey (codec S base) pk))))

theorem pue_qmForger (base : Xof S) (q qs k : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hqs : ∀ pk, CountBound isSign (F.main pk) qs)
    (pk : PublicKeyCore (primitives S base).core) :
    PUE (sgnW k) (fun H ↦ qmForger S N F base H pk) (q + qs * k) := by
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

theorem internal_main (H : RawTable S N) :
    (qPureBytesToInternal (rawForger S N optRand₀ pkSeedDist₀ F H)).main =
      fun pk ↦ qmForger S N F (extend H) H pk := by
  funext pk
  simp only [rawForger,forgerAt, scheme, qPureBytesToInternal, qToInternal, qPureBytesToTyped, QForger.wrapForger,
    PortForger.at, qmCSign_eq, qmCRead_eq, pureBytesView]
  rfl

end Reduction.ShakeApi
#print axioms Reduction.ShakeApi.internal_main
#print axioms Reduction.ShakeApi.pue_qmForger
