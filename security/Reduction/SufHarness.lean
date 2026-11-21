import Reduction.Harness

/-!
# Harness for games whose final check reads the returned signatures

The EUF-CMA harness `runForger` (`Reduction.Harness`) records only the queried *messages*.  A
strong-unforgeability check needs the returned `(message, signature)` pairs, so the reductions of
the SUF-CMA proof run the forger through `runForgerSig`, which records exactly the log of VCVio's
`SignatureAlg.runWithSigningOracle`.

* `WinCheck` — a final check: a Boolean function of the public key, the forger's output and the
  log of returned pairs.
* `expW alg w A` — the chosen-message experiment against `alg` with final check `w`.
* `run_withLogging_eq_run_appendLog` — VCVio's `WriterT` log equals the `StateT` log of the
  harness (the full-log analogue of `QueryImpl.map_run_withLogging_inputs_eq_run_appendInputLog`).
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal

namespace Reduction

set_option linter.unusedSectionVars false

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y]
variable {optRand : PublicKeyCore prims.core → ProbComp prims.Y}
  {pkSeedDist : ProbComp prims.PkSeed}

/-- The log of returned `(message, signature)` pairs, as VCVio's signing oracle writes it. -/
abbrev SigLog (vp : ValidatedParams) (prims : Primitives vp.params) : Type :=
  QueryLog (List Byte →ₒ GeneralScheme.SignatureCore vp prims.core)

/-- A final check of a chosen-message game: public key, forger's output, returned pairs. -/
abbrev WinCheck (vp : ValidatedParams) (prims : Primitives vp.params) : Type :=
  PublicKeyCore prims.core → List Byte × GeneralScheme.SignatureCore vp prims.core →
    SigLog vp prims → Bool

/-! ## Generic: `WriterT` log = `StateT` log -/

section AppendLog

variable {ι₀ : Type} {spec₀ : OracleSpec.{0, 0} ι₀}
variable {κ : Type} {loggedSpec : OracleSpec.{0, 0} κ}
variable {m₀ : Type → Type} [Monad m₀]

/-- Answer by `so` and append the `(input, output)` pair to a `StateT` log. -/
def appendLog (so : QueryImpl loggedSpec m₀) :
    QueryImpl loggedSpec (StateT (QueryLog loggedSpec) m₀) :=
  fun t => do
    let u ← (monadLift (so t) : StateT (QueryLog loggedSpec) m₀ (loggedSpec.Range t))
    modify (· ++ [⟨t, u⟩])
    return u

theorem run_appendLog_apply [LawfulMonad m₀] (so : QueryImpl loggedSpec m₀)
    (t : loggedSpec.Domain) (log : QueryLog loggedSpec) :
    (appendLog so t).run log = (so t >>= fun u => pure (u, log ++ [⟨t, u⟩])) := by
  simp [appendLog]

/-- A `WriterT` query log can be replayed as a `StateT` log of the same entries. -/
theorem run_withLogging_eq_run_appendLog [LawfulMonad m₀] [HasQuery spec₀ m₀] {α' : Type}
    (so : QueryImpl loggedSpec m₀) (oa : OracleComp (spec₀ + loggedSpec) α')
    (init : QueryLog loggedSpec) :
    ((fun z : α' × QueryLog loggedSpec => (z.1, init ++ z.2)) <$>
        ((simulateQ
          ((HasQuery.toQueryImpl (spec := spec₀) (m := m₀)).liftTarget
              (WriterT (QueryLog loggedSpec) m₀) + QueryImpl.withLogging so) oa).run :
          m₀ (α' × QueryLog loggedSpec))) =
      ((simulateQ
        ((HasQuery.toQueryImpl (spec := spec₀) (m := m₀)).liftTarget
            (StateT (QueryLog loggedSpec) m₀) + appendLog so) oa).run init :
        m₀ (α' × QueryLog loggedSpec)) := by
  induction oa using OracleComp.inductionOn generalizing init with
  | pure x => simp
  | query_bind t oa ih =>
      cases t with
      | inl t' =>
          rw [QueryImpl.simulateQ_add_query_bind_left, QueryImpl.simulateQ_add_query_bind_left]
          simp only [QueryImpl.liftTarget_apply, WriterT.run_bind', WriterT.run_liftM,
            StateT.run_bind, StateT.run_monadLift, monadLift_self, map_bind,
            monad_norm, List.empty_eq]
          exact bind_congr fun u => by
            simpa [Function.comp_apply] using ih u init
      | inr t' =>
          rw [QueryImpl.simulateQ_add_query_bind_right, QueryImpl.simulateQ_add_query_bind_right]
          simp only [WriterT.run_bind', StateT.run_bind, map_bind]
          rw [QueryImpl.run_withLogging_apply, run_appendLog_apply]
          simp only [bind_assoc, pure_bind, Functor.map_map]
          exact bind_congr fun u => by
            have h := ih u (init ++ [⟨t', u⟩])
            simp only [List.append_assoc, List.singleton_append] at h
            simpa using h

end AppendLog

/-! ## The harness -/

/-- The signing oracle of a reduction: answer by `sign`, record the returned pair. -/
def sigSignOracle {ι : Type} {spec : OracleSpec ι}
    (sign : List Byte → OracleComp spec (GeneralScheme.SignatureCore vp prims.core)) :
    QueryImpl (List Byte →ₒ GeneralScheme.SignatureCore vp prims.core)
      (StateT (SigLog vp prims) (OracleComp spec)) :=
  appendLog sign

/-- Run the forger once inside a reduction whose oracle interface is `unifSpec + spec`; returns
the forger's output and the log of returned `(message, signature)` pairs. -/
def runForgerSig {ι : Type} {spec : OracleSpec ι} (A : Forger vp prims optRand pkSeedDist)
    (pk : PublicKeyCore prims.core)
    (sign : List Byte → OracleComp (unifSpec + spec) (GeneralScheme.SignatureCore vp prims.core)) :
    OracleComp (unifSpec + spec)
      ((List Byte × GeneralScheme.SignatureCore vp prims.core) × SigLog vp prims) :=
  (simulateQ
    ((QueryImpl.ofLift unifSpec (OracleComp (unifSpec + spec))).liftTarget
        (StateT (SigLog vp prims) (OracleComp (unifSpec + spec))) +
      sigSignOracle sign) (A.main pk)).run []

/-- The chosen-message experiment against a scheme `alg` (same message, key and signature types
as SLH-DSA) with final check `w`: key generation, one run of the forger against the logging
signing oracle, then `w`. -/
noncomputable def expW {SK : Type}
    (alg : SignatureAlg ProbComp (List Byte) (PublicKeyCore prims.core) SK
      (GeneralScheme.SignatureCore vp prims.core))
    (w : WinCheck vp prims) (A : Forger vp prims optRand pkSeedDist) : ProbComp Bool :=
  alg.keygen >>= fun kp =>
    alg.runWithSigningOracle kp.1 kp.2 (A.main kp.1) >>= fun z => pure (w kp.1 z.1 z.2)

/-- The run of a scheme's logging signing oracle is the `StateT` run of `appendLog`. -/
theorem runWithSigningOracle_eq_appendLog {SK : Type}
    (alg : SignatureAlg ProbComp (List Byte) (PublicKeyCore prims.core) SK
      (GeneralScheme.SignatureCore vp prims.core))
    (pk : PublicKeyCore prims.core) (sk : SK) {α : Type}
    (oa : OracleComp (unifSpec + (List Byte →ₒ GeneralScheme.SignatureCore vp prims.core)) α) :
    alg.runWithSigningOracle pk sk oa =
      (simulateQ
        ((HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
            (StateT (SigLog vp prims) ProbComp) + appendLog (alg.sign pk sk)) oa).run [] := by
  have h := run_withLogging_eq_run_appendLog (spec₀ := unifSpec) (alg.sign pk sk) oa []
  refine Eq.trans ?_ h
  simp [SignatureAlg.runWithSigningOracle, SignatureAlg.signingOracle]
  rfl

end Reduction

#print axioms Reduction.run_withLogging_eq_run_appendLog
#print axioms Reduction.runWithSigningOracle_eq_appendLog
