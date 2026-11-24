import Integration.SlhDsaCompressionHmacSignature
import Ideal.Transport.AdvItsr

namespace Reduction.Compression.MessageHash
open MLink Ideal SLHDSA SLHDSA.Security OracleComp OracleSpec PQ.Interactive Quantum QInd QMsg Ideal.Transport
variable {W : Type} [Fintype W] {vp : ValidatedParams} {prims : Primitives vp.params}
  (prf : prims.PkSeed → prims.SkSeed → Adrs → prims.Y)
  (pm : prims.SkPrf → prims.Y → List Byte → prims.Y)
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y] [Fintype prims.Y]
  (codec : CoreWireCodec vp.params prims.core)
  (rand : PublicKeyCore prims.core → ProbComp prims.Y)
  (rand' : PublicKeyCore (setPrfC prims.core prf pm) → ProbComp prims.Y)
  (hr : ∀ pk, rand' (trPk _ prf pm pk) = rand pk)
  (seeds : ProbComp prims.PkSeed)
  (B : QForger W (pureBytesAlg vp prims codec rand seeds))

include hr in
omit [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Fintype prims.Y] in
private theorem itsr_open_tr :
    castQ prims prf pm (Lazy.itsrG prims)
      (qmItsrOpen rand' seeds (qPureBytesToInternal (trB prf pm codec rand rand' seeds B)).main) =
    qmItsrOpen rand seeds (qPureBytesToInternal B).main := by
  unfold qmItsrOpen
  rw [castQ_bind]
  refine bind_congr_k (by krfl) fun pk => ?_
  rw [castQ_bind]
  refine bind_congr_k (by krfl) fun root => ?_
  rw [castQ_bind]
  let pk₀ : PublicKeyCore prims.core := ⟨pk,root⟩
  let G := Lazy.itsrG prims
  let sign := logSignOracle rand pk₀ (fun s m r => castO' prims prf pm G (Lazy.itsrRandomizerO pk root s m r))
    (fun m R => castO' prims prf pm G (Lazy.openSign prims G m pk root R))
  let sign' := logSignOracle rand' (trPk _ prf pm pk₀)
    (Lazy.itsrRandomizerO (prims := setPrf prims prf pm) pk root)
    (fun m R => Lazy.openSign (setPrf prims prf pm) G m pk root R)
  have step (m s) : (sign' m).run s = (fun z => (trSig _ prf pm z.1,z.2)) <$> (sign m).run s := by
    simp only [sign,sign',logSignOracle,hr,lazyOpenSign_tr prims prf pm G]
    simp
    krfl
  have h := wrap_qPureBytesToInternal_tr prf pm codec rand rand' seeds id B sign sign' step pk₀ []
  have h' := congrArg (castQ prims prf pm G) h
  let baseSign := logSignOracle rand pk₀ (Lazy.itsrRandomizerO (prims := prims) pk root)
    (fun m R => Lazy.openSign prims G m pk root R)
  let wrapped := wrap ((QueryImpl.ofLift unifSpec (OracleComp (Lazy.OSpec prims G))).liftTarget
      (StateT (G2Log prims) (OracleComp (Lazy.OSpec prims G))) + baseSign)
      ((qPureBytesToInternal B).main pk₀) []
  have e : castQ prims prf pm G (wrap ((QueryImpl.ofLift unifSpec (OracleComp (Lazy.OSpec (setPrf prims prf pm) G))).liftTarget
      (StateT (G2Log prims) (OracleComp (Lazy.OSpec (setPrf prims prf pm) G))) + sign')
      ((qPureBytesToInternal (trB prf pm codec rand rand' seeds B)).main (trPk _ prf pm pk₀)) []) =
    (fun z => ((z.1.1,trSig _ prf pm z.1.2),z.2)) <$> wrapped := h'.trans (by krfl)
  refine (bind_congr_k e fun z => rfl).trans ?_
  rw [bind_map_left]
  apply bind_congr
  intro z
  krfl

include hr in
theorem itsr_tr :
    qbItsrL (qPureBytesToInternal (trB prf pm codec rand rand' seeds B)) =
      qbItsrL (qPureBytesToInternal B) := by
  change qLazyRun (PublicHash.impl (setPrf prims prf pm)) (qmItsrOpen rand' seeds
    (qPureBytesToInternal (trB prf pm codec rand rand' seeds B)).main) =
    qLazyRun (PublicHash.impl prims) (qmItsrOpen rand seeds (qPureBytesToInternal B).main)
  rw [qLazyRun_setPrf prims prf pm (Lazy.itsrG prims)]
  exact congrArg (qLazyRun (PublicHash.impl prims)) (itsr_open_tr prf pm codec rand rand' hr seeds B)

section Shared
variable (S : Sha2Set) (f : RandFns S.vp.params)
    (r : S.Node → S.Node → ProbComp S.Node) (ks : ProbComp S.Node)
    {E : Type} [Fintype E] [DecidableEq E] (F : PortForger Input Output E)

noncomputable def machine (H : Input → Output) :=
  qLazyRun (hashPort S f H) (qmItsrOpen (fun pk => r pk.pkSeed pk.pkRoot) ks (mainAt S f F H))

/-- The signature reduction's native ITSR adversary is realized by one public-port
program before either compression table has been chosen. -/
theorem machine_oracle (g : CompressionTables) :
    machine S (carrier S) r ks F (oracle g) = qbItsrL (reduced S r ks F g) := by
  let real := functions S g
  let ref := {carrier S with thash := real.thash, hmsg := real.hmsg}
  have a : machine S (carrier S) r ks F (oracle g) = machine S ref r ks F (oracle g) := by qm_kernel_rfl
  rw [a]
  have b : hashPort S ref (oracle g) = PublicHash.impl (randPrims ref) := by
    unfold hashPort
    rw [tablesOf_oracle]
    funext t
    cases t <;> rfl
  unfold machine
  rw [b,mainAt_eq S ref F r ks]
  have tr := itsr_tr (prims := randPrims ref) real.prf real.prfMsg (SetOracle.codecFor S ref)
    (fun pk => r pk.pkSeed pk.pkRoot) (fun pk => r pk.pkSeed pk.pkRoot) (fun _ => rfl) ks
    (F.at (oracle g) (pureBytesAlg S.vp (randPrims ref) (SetOracle.codecFor S ref)
      (fun pk => r pk.pkSeed pk.pkRoot) ks))
  kexact tr.symm
end Shared

end Reduction.Compression.MessageHash
#print axioms Reduction.Compression.MessageHash.itsr_tr
#print axioms Reduction.Compression.MessageHash.machine_oracle
