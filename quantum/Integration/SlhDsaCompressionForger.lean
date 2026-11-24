import Integration.SlhDsaCompressionQuantum
import Integration.SlhDsaSetTcrMach
import Integration.SlhDsaBridgeItsrD

namespace Reduction.Compression
open MLink SLHDSA SLHDSA.Security OracleComp OracleSpec QItsr QMsg PQ.Interactive Quantum
variable (S : Sha2Set) (f : RandFns S.vp.params)
local notation "P₀" => randPrims f
variable {E : Type} [Fintype E] [DecidableEq E] (F : PortForger Input Output E)

noncomputable def mainAt (H : Input → Output) (pk : PublicKeyCore (P₀).core) :
    QOC (WS Input Output E) (unifSpec + (List Byte →ₒ GeneralScheme.SignatureCore S.vp (P₀).core))
      (List Byte × GeneralScheme.SignatureCore S.vp (P₀).core) :=
  Guarded.readForgery pureEncode ([], constSig default) <$>
    wrap0 (Guarded.signingImpl pureEncode)
      (qmCRead (decodePureSig S.vp P₀ (SetOracle.codecFor S f))
          (Except.error (External.Error.contextTooLong 0)) <$>
        wrap0 (qmCSign (encodePureSig S.vp P₀ (SetOracle.codecFor S f)))
          (compileQ H (F.main (encodePublicKey (SetOracle.codecFor S f) pk))))

theorem mainAt_eq (rand : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node)
    (H : Input → Output) : mainAt S f F H =
      (qPureBytesToInternal (F.at H (pureBytesAlg S.vp P₀ (SetOracle.codecFor S f)
        (fun pk => rand pk.pkSeed pk.pkRoot) seeds))).main := by
  funext pk
  simp only [qPureBytesToInternal, qToInternal, qPureBytesToTyped, QForger.wrapForger,
    PortForger.at, qmCSign_eq, qmCRead_eq, pureBytesView]
  rfl

theorem mainAt_cap (c : Caps) (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk))
    (H : Input → Output) (pk : PublicKeyCore (P₀).core) :
    AllQueries (QG (WS Input Output E) (Gint c.ml)) (fun z => z.1.length ≤ c.ml)
      (mainAt S f F H pk) := by
  rw [mainAt_eq S f F (fun a _ => pure a) (pure default)]
  exact allQ_and (allQ_qPureBytesToInternal c.ml _
    (fun pkb => allQ_compileQ c H (F.main pkb) (hc pkb)) pk)
    (out_qPureBytesToInternal _ c.ml
      (fun pkb => allQ_out_simulateQ (compileImplQ H) (hc pkb)) pk)

theorem mainAt_pue (q qs k : ℕ) (hq : ∀ pk, CountBound isPort (F.main pk) q)
    (hs : ∀ pk, CountBound isSign (F.main pk) qs) (pk : PublicKeyCore (P₀).core) :
    PUE (sgnW k) (fun H => mainAt S f F H pk) (q + qs*k) := by
  unfold mainAt
  refine PUE.map _ (PUE.wrap0 (cnt := sgnW k) _ ?_ (PUE.map _ (PUE.wrap0 (cnt := sgnW k)
    (cnt' := sgnW k) _ ?_ (PUE.compileQ (sgnW k) _ _
    (wCount_of_countBound isPort isSign _ k ?_ _ q qs (hq _) (hs _))))))
  · rintro (n|mc)
    · exact wCount_liftM_query _ _ le_rfl
    · simp only [Guarded.signingImpl]
      split
      · exact trivial
      · exact WCount.map (wCount_liftM_query _ _ le_rfl) _
  · rintro (n|m)
    · exact wCount_liftM_query _ _ le_rfl
    · exact WCount.map (wCount_liftM_query _ _ le_rfl) _
  · rintro (j|u|n|m) <;> simp [compileW, isPort, isSign]

end Reduction.Compression
#print axioms Reduction.Compression.mainAt_cap
#print axioms Reduction.Compression.mainAt_pue
