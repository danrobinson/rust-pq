import Ideal.Transport.Sign
import Ideal.Transport.Verify
import Reduction.SufHarness
import Reduction.Suf

/-!
# Common part of the core-invariance lemmas for the reduction adversaries

The byte-level forger wrapper run inside the three harnesses of the reductions (`runForger`,
`runForgerSig`, `runForgerLog`), over `setPrf prims prf pm` and over `prims`.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security

namespace Ideal.Transport

set_option linter.unusedSectionVars false

/-- Two stateful handlers related by a map of states give related runs. -/
theorem simulateQ_run_map_state {ι : Type} {spec : OracleSpec ι} {m : Type → Type} [Monad m]
    [LawfulMonad m] {σ σ' α : Type} (f : σ → σ') (impl : QueryImpl spec (StateT σ m))
    (impl' : QueryImpl spec (StateT σ' m))
    (h : ∀ t s, (impl' t).run (f s) = (fun z => (z.1, f z.2)) <$> (impl t).run s)
    (oa : OracleComp spec α) (s : σ) :
    (simulateQ impl' oa).run (f s) = (fun z => (z.1, f z.2)) <$> (simulateQ impl oa).run s := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure a => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, StateT.run_bind, h, map_bind, bind_map_left, ih,
      OracleQuery.cont_query, id_map, OracleQuery.input_query]

theorem vector_map_injective {α β : Type} {g : α → β} (hg : Function.Injective g) {n : ℕ} :
    Function.Injective (Vector.map g : Vector α n → Vector β n) := by
  intro v w h
  ext i hi
  have := congrArg (fun u : Vector β n => u[i]) h
  simp only [Vector.getElem_map] at this
  exact hg this

section Forger

open Reduction

variable {vp : ValidatedParams} {prims : Primitives vp.params}
  (prf : prims.PkSeed → prims.SkSeed → Adrs → prims.Y)
  (pm : prims.SkPrf → prims.Y → List Byte → prims.Y)
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [Inhabited prims.Y]
variable (codec : CoreWireCodec vp.params prims.core)
  (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
  (optRand' : PublicKeyCore (setPrfC prims.core prf pm) → ProbComp prims.Y)
  (pkSeedDist : ProbComp prims.PkSeed)

/-- The wrapped byte-level forger run against an arbitrary stateful signing handler: the run over
`setPrf prims prf pm` is the run over `prims`, when the two handlers are related by `trSig` on
the answers and a map `f` of the states. -/
theorem simRun_bytesToTyped_tr {ι : Type} {spec : OracleSpec ι} {σ σ' : Type} (f : σ → σ')
    (S : List Byte → OracleComp (unifSpec + (List Byte →ₒ List Byte)) (List Byte × List Byte))
    (impl : QueryImpl (List Byte →ₒ GeneralScheme.SignatureCore vp prims.core)
      (StateT σ (OracleComp (unifSpec + spec))))
    (impl' : QueryImpl (List Byte →ₒ GeneralScheme.SignatureCore vp (setPrfC prims.core prf pm))
      (StateT σ' (OracleComp (unifSpec + spec))))
    (h : ∀ m s, (impl' m).run (f s) = (fun z => (trSig _ prf pm z.1, f z.2)) <$> (impl m).run s)
    (pk : PublicKeyCore prims.core) (s : σ) :
    (simulateQ
        ((QueryImpl.ofLift unifSpec (OracleComp (unifSpec + spec))).liftTarget
            (StateT σ' (OracleComp (unifSpec + spec))) + impl')
        ((bytesToTyped (prims := setPrf prims prf pm) (codec := trCodec _ prf pm codec)
          (optRand := optRand') (pkSeedDist := pkSeedDist) ⟨S⟩).main (trPk _ prf pm pk))).run (f s) =
      (fun z => ((z.1.1, trSig _ prf pm z.1.2), f z.2)) <$>
        (simulateQ
          ((QueryImpl.ofLift unifSpec (OracleComp (unifSpec + spec))).liftTarget
              (StateT σ (OracleComp (unifSpec + spec))) + impl)
          ((bytesToTyped (codec := codec) (optRand := optRand) (pkSeedDist := pkSeedDist)
            ⟨S⟩).main pk)).run s := by
  unfold bytesToTyped Coded.reduce
  dsimp only
  rw [simulateQ_map, simulateQ_map, ← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose,
    funext (readForgery_tr prf pm codec optRand optRand' pkSeedDist)]
  have hpk : (bytesView vp (setPrf prims prf pm) (trCodec _ prf pm codec) optRand'
      pkSeedDist).encPk (trPk _ prf pm pk) = (bytesView vp prims codec optRand pkSeedDist).encPk pk :=
    encodePublicKey_tr _ prf pm codec pk
  rw [hpk, StateT.run_map, StateT.run_map]
  rw [simulateQ_run_map_state f
    (((QueryImpl.ofLift unifSpec (OracleComp (unifSpec + spec))).liftTarget
        (StateT σ (OracleComp (unifSpec + spec))) + impl) ∘ₛ
      Coded.signingImpl (bytesView vp prims codec optRand pkSeedDist)) _ ?_ _ s]
  · simp only [Functor.map_map]
  · intro t s
    rcases t with n | msg
    · simp [QueryImpl.apply_compose, Coded.signingImpl]
    · simp only [QueryImpl.apply_compose, Coded.signingImpl, simulateQ_map]
      simp only [simulateQ_HasQuery_query, QueryImpl.add_apply_inr]
      simp only [StateT.run_map, h, Functor.map_map, bytesView, encodeSignature_tr]

/-- The wrapped byte-level forger run in `ProbComp` against an arbitrary stateful signing handler
(the shape of `g2RunWith`). -/
theorem simRunP_bytesToTyped_tr {σ σ' : Type} (f : σ → σ')
    (S : List Byte → OracleComp (unifSpec + (List Byte →ₒ List Byte)) (List Byte × List Byte))
    (impl : QueryImpl (List Byte →ₒ GeneralScheme.SignatureCore vp prims.core)
      (StateT σ ProbComp))
    (impl' : QueryImpl (List Byte →ₒ GeneralScheme.SignatureCore vp (setPrfC prims.core prf pm))
      (StateT σ' ProbComp))
    (h : ∀ m s, (impl' m).run (f s) = (fun z => (trSig _ prf pm z.1, f z.2)) <$> (impl m).run s)
    (pk : PublicKeyCore prims.core) (s : σ) :
    (simulateQ
        ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT σ' ProbComp) + impl')
        ((bytesToTyped (prims := setPrf prims prf pm) (codec := trCodec _ prf pm codec)
          (optRand := optRand') (pkSeedDist := pkSeedDist) ⟨S⟩).main (trPk _ prf pm pk))).run (f s) =
      (fun z => ((z.1.1, trSig _ prf pm z.1.2), f z.2)) <$>
        (simulateQ
          ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT σ ProbComp) + impl)
          ((bytesToTyped (codec := codec) (optRand := optRand) (pkSeedDist := pkSeedDist)
            ⟨S⟩).main pk)).run s := by
  unfold bytesToTyped Coded.reduce
  dsimp only
  rw [simulateQ_map, simulateQ_map, ← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose,
    funext (readForgery_tr prf pm codec optRand optRand' pkSeedDist)]
  have hpk : (bytesView vp (setPrf prims prf pm) (trCodec _ prf pm codec) optRand'
      pkSeedDist).encPk (trPk _ prf pm pk) = (bytesView vp prims codec optRand pkSeedDist).encPk pk :=
    encodePublicKey_tr _ prf pm codec pk
  rw [hpk, StateT.run_map, StateT.run_map]
  rw [simulateQ_run_map_state f
    (((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT σ ProbComp) + impl) ∘ₛ
      Coded.signingImpl (bytesView vp prims codec optRand pkSeedDist)) _ ?_ _ s]
  · simp only [Functor.map_map]
  · intro t s
    rcases t with n | msg
    · simp [QueryImpl.apply_compose, Coded.signingImpl]
    · simp only [QueryImpl.apply_compose, Coded.signingImpl, simulateQ_map]
      simp only [simulateQ_HasQuery_query, QueryImpl.add_apply_inr]
      simp only [StateT.run_map, h, Functor.map_map, bytesView, encodeSignature_tr]

variable (hopt : ∀ pk, optRand' (trPk _ prf pm pk) = optRand pk)

include hopt in
/-- `g2RunWith` at the wrapped byte-level forger, for an arbitrary signer. -/
theorem g2RunWith_bytesToTyped_tr
    (S : List Byte → OracleComp (unifSpec + (List Byte →ₒ List Byte)) (List Byte × List Byte))
    (pk : PublicKeyCore prims.core)
    (signR : List Byte → prims.Y → GeneralScheme.SignatureCore vp prims.core)
    (signR' : List Byte → prims.Y → GeneralScheme.SignatureCore vp (setPrfC prims.core prf pm))
    (hs : ∀ m R, signR' m R = trSig _ prf pm (signR m R)) :
    g2RunWith (prims := setPrf prims prf pm)
        (bytesToTyped (prims := setPrf prims prf pm) (codec := trCodec _ prf pm codec)
          (optRand := optRand') (pkSeedDist := pkSeedDist) ⟨S⟩) (trPk _ prf pm pk) signR' =
      (fun z => ((z.1.1, trSig _ prf pm z.1.2), z.2)) <$>
        g2RunWith (bytesToTyped (codec := codec) (optRand := optRand)
          (pkSeedDist := pkSeedDist) ⟨S⟩) pk signR := by
  unfold g2RunWith
  refine simRunP_bytesToTyped_tr prf pm codec optRand optRand' pkSeedDist id S _ _ ?_ pk []
  intro m s
  simp only [g2SignOracle, hopt, hs, id]
  simp
  krfl

include hopt in
/-- `runForgerLog` at the wrapped byte-level forger. -/
theorem runForgerLog_bytesToTyped_tr {ι : Type} {spec : OracleSpec ι}
    (S : List Byte → OracleComp (unifSpec + (List Byte →ₒ List Byte)) (List Byte × List Byte))
    (pk : PublicKeyCore prims.core)
    (rnd : G2Log prims → List Byte → prims.Y → OracleComp (unifSpec + spec) prims.Y)
    (signR : List Byte → prims.Y →
      OracleComp (unifSpec + spec) (GeneralScheme.SignatureCore vp prims.core))
    (signR' : List Byte → prims.Y →
      OracleComp (unifSpec + spec) (GeneralScheme.SignatureCore vp (setPrfC prims.core prf pm)))
    (hs : ∀ m R, signR' m R = trSig _ prf pm <$> signR m R) :
    runForgerLog (prims := setPrf prims prf pm)
        (bytesToTyped (prims := setPrf prims prf pm) (codec := trCodec _ prf pm codec)
          (optRand := optRand') (pkSeedDist := pkSeedDist) ⟨S⟩) (trPk _ prf pm pk) rnd signR' =
      (fun z => ((z.1.1, trSig _ prf pm z.1.2), z.2)) <$>
        runForgerLog (bytesToTyped (codec := codec) (optRand := optRand)
          (pkSeedDist := pkSeedDist) ⟨S⟩) pk rnd signR := by
  unfold runForgerLog
  refine simRun_bytesToTyped_tr prf pm codec optRand optRand' pkSeedDist id S _ _ ?_ pk []
  intro m s
  simp only [logSignOracle, hopt, hs, id]
  simp

/-- `runForger` at the wrapped byte-level forger. -/
theorem runForger_bytesToTyped_tr {ι : Type} {spec : OracleSpec ι}
    (S : List Byte → OracleComp (unifSpec + (List Byte →ₒ List Byte)) (List Byte × List Byte))
    (pk : PublicKeyCore prims.core)
    (sign : List Byte → OracleComp (unifSpec + spec) (GeneralScheme.SignatureCore vp prims.core))
    (sign' : List Byte →
      OracleComp (unifSpec + spec) (GeneralScheme.SignatureCore vp (setPrfC prims.core prf pm)))
    (hs : ∀ m, sign' m = trSig _ prf pm <$> sign m) :
    runForger (prims := setPrf prims prf pm)
        (bytesToTyped (prims := setPrf prims prf pm) (codec := trCodec _ prf pm codec)
          (optRand := optRand') (pkSeedDist := pkSeedDist) ⟨S⟩) (trPk _ prf pm pk) sign' =
      (fun z => ((z.1.1, trSig _ prf pm z.1.2), z.2)) <$>
        runForger (bytesToTyped (codec := codec) (optRand := optRand)
          (pkSeedDist := pkSeedDist) ⟨S⟩) pk sign := by
  unfold runForger
  refine simRun_bytesToTyped_tr prf pm codec optRand optRand' pkSeedDist id S _ _ ?_ pk []
  intro m s
  simp only [harnessSignOracle, hs, id]
  simp

/-- The log of returned pairs, transported entry-wise. -/
def trLog (log : SigLog vp prims) : SigLog vp (setPrf prims prf pm) :=
  log.map fun e => ⟨e.1, trSig _ prf pm e.2⟩

/-- `runForgerSig` at the wrapped byte-level forger. -/
theorem runForgerSig_bytesToTyped_tr {ι : Type} {spec : OracleSpec ι}
    (S : List Byte → OracleComp (unifSpec + (List Byte →ₒ List Byte)) (List Byte × List Byte))
    (pk : PublicKeyCore prims.core)
    (sign : List Byte → OracleComp (unifSpec + spec) (GeneralScheme.SignatureCore vp prims.core))
    (sign' : List Byte →
      OracleComp (unifSpec + spec) (GeneralScheme.SignatureCore vp (setPrfC prims.core prf pm)))
    (hs : ∀ m, sign' m = trSig _ prf pm <$> sign m) :
    runForgerSig (prims := setPrf prims prf pm)
        (bytesToTyped (prims := setPrf prims prf pm) (codec := trCodec _ prf pm codec)
          (optRand := optRand') (pkSeedDist := pkSeedDist) ⟨S⟩) (trPk _ prf pm pk) sign' =
      (fun z => ((z.1.1, trSig _ prf pm z.1.2), trLog prf pm z.2)) <$>
        runForgerSig (bytesToTyped (codec := codec) (optRand := optRand)
          (pkSeedDist := pkSeedDist) ⟨S⟩) pk sign := by
  unfold runForgerSig
  refine simRun_bytesToTyped_tr prf pm codec optRand optRand' pkSeedDist (trLog prf pm) S _ _ ?_
    pk []
  intro m s
  simp only [sigSignOracle, run_appendLog_apply, hs]
  simp [trLog]

end Forger

section Checks

open Reduction

variable {vp : ValidatedParams} (prims : Primitives vp.params)
  (prf : prims.PkSeed → prims.SkSeed → Adrs → prims.Y)
  (pm : prims.SkPrf → prims.Y → List Byte → prims.Y)

theorem trSig_injective : Function.Injective (trSig (p := vp.params) prims.core prf pm) := by
  rintro ⟨r, f, h⟩ ⟨r', f', h'⟩ e
  have hr : r = r' := congrArg (·.randomness) e
  have hf : f = f' :=
    vector_map_injective (trFors_injective _ prf pm) (congrArg (·.fors) e)
  have hh : h = h' :=
    vector_map_injective (trXmss_injective _ prf pm) (congrArg (·.hypertree) e)
  subst hr hf hh
  rfl

variable [DecidableEq prims.Y]

/-- The EUF final check. -/
theorem harnessValid_setPrf (pk : PublicKeyCore prims.core) (msgs : List (List Byte))
    (msg : List Byte) (sig : GeneralScheme.SignatureCore vp prims.core) :
    harnessValid (prims := setPrf prims prf pm) (trPk _ prf pm pk) msgs msg (trSig _ prf pm sig) =
      harnessValid (prims := prims) pk msgs msg sig := by
  unfold harnessValid
  rw [verifyInternal_setPrf]

theorem trLog_mem (log : SigLog vp prims) (m : List Byte)
    (s : GeneralScheme.SignatureCore vp prims.core) :
    (⟨m, trSig _ prf pm s⟩ : (_ : List Byte) × GeneralScheme.SignatureCore vp
        (setPrfC prims.core prf pm)) ∈ trLog prf pm log ↔
      (⟨m, s⟩ : (_ : List Byte) × GeneralScheme.SignatureCore vp prims.core) ∈ log := by
  unfold trLog
  rw [List.mem_map]
  constructor
  · rintro ⟨⟨m', s'⟩, hmem, he⟩
    obtain ⟨rfl, hs⟩ := Sigma.mk.inj he
    obtain rfl := trSig_injective prims prf pm (eq_of_heq hs)
    exact hmem
  · intro h
    exact ⟨⟨m, s⟩, h, rfl⟩

/-- The SUF final check. -/
theorem sufCheck_setPrf (pk : PublicKeyCore prims.core)
    (f : List Byte × GeneralScheme.SignatureCore vp prims.core) (log : SigLog vp prims) :
    sufCheck (prims := setPrf prims prf pm) (trPk _ prf pm pk) (f.1, trSig _ prf pm f.2)
        (trLog prf pm log) =
      sufCheck (prims := prims) pk f log := by
  unfold sufCheck SignatureAlg.signingLogContains
  dsimp only
  rw [verifyInternal_setPrf]
  congr 2
  rw [decide_eq_decide]
  exact trLog_mem prims prf pm log f.1 f.2

end Checks

end Ideal.Transport

section AxiomCheck
open Ideal.Transport
#print axioms simRun_bytesToTyped_tr
#print axioms runForgerLog_bytesToTyped_tr
#print axioms runForger_bytesToTyped_tr
#print axioms g2RunWith_bytesToTyped_tr
#print axioms runForgerSig_bytesToTyped_tr
#print axioms harnessValid_setPrf
#print axioms sufCheck_setPrf
end AxiomCheck
