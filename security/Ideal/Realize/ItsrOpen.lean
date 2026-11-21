import Ideal.Realize.ItsrWalk

/-!
# The open ITSR program with a compression port (ITSR realiser, generic part)

`Reduction.Lazy.itsrOpen A` runs the forger `A` (no compression queries) over the open interface
`Lazy.OSpec prims (Lazy.itsrG prims)` (uniform bits, ITSR target queries, secret reads, hash
queries).  Here the forger has a compression port (`Ideal.Realize.FSpecP`), threaded through the
game slot `gI prims := Lazy.itsrG prims + hS St Blk`:

* `randP`, `portImplI`, `itsrOpenP optRand pkSeedDist mainP` — the open ITSR program of a typed
  port forger `mainP`;
* `portAns g` — answers the port queries by the table `g`, forwards everything else (for any
  secret / hash slots, so it serves both `Lazy.OSpec` and the resource-explicit `Lazy.RSpec … Unit`);
* **fusion** `itsrOpenP_fusion`: `simulateQ (portAns g) (itsrOpenP optRand pkSeedDist mainP)` is
  `Lazy.itsrOpen` at the forger `pk ↦ simulateQ (instImpl g) (mainP pk)`;
* `lazyRes_portAns`: the lazy cache commutes with `portAns g`.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security

namespace Ideal.Realize.Itsr

open Reduction Reduction.Lazy Ideal.Realize

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! ## Answering the port -/

section PortAns

variable {ι κ : Type} {G : OracleSpec ι} {D V : Type} {hspec : OracleSpec κ}

/-- Answer the port queries (`hS St Blk` in the game slot) by `g`; forward every other query. -/
def portAns (g : CF St Blk) :
    QueryImpl (RSpec (G + hS St Blk) D V hspec) (OracleComp (RSpec G D V hspec))
  | .inl n => (liftM ((RSpec G D V hspec).query (.inl n)) : OracleComp (RSpec G D V hspec) _)
  | .inr (.inl (.inl x)) =>
      (liftM ((RSpec G D V hspec).query (.inr (.inl x))) : OracleComp (RSpec G D V hspec) _)
  | .inr (.inl (.inr q)) => pure (g q)
  | .inr (.inr t) =>
      (liftM ((RSpec G D V hspec).query (.inr (.inr t))) : OracleComp (RSpec G D V hspec) _)

theorem portAns_liftM (g : CF St Blk) {β : Type} (ob : ProbComp β) :
    simulateQ (portAns (G := G) (D := D) (V := V) (hspec := hspec) g)
      (liftM ob : OracleComp (RSpec (G + hS St Blk) D V hspec) β) =
      (liftM ob : OracleComp (RSpec G D V hspec) β) := by
  induction ob using OracleComp.inductionOn with
  | pure a => simp
  | query_bind n k ih =>
    rw [liftM_bind, liftM_bind, simulateQ_bind]
    simp only [ih]
    congr 1

end PortAns

/-! ## The open program -/

section Open

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]

attribute [local instance] Lazy.openQ

/-- The game slot of the port program: ITSR target queries and compression queries. -/
abbrev gI (prims : Primitives vp.params) := Lazy.itsrG prims + hS St Blk

/-- The randomizer of the port program (as `Lazy.itsrRandomizerO`). -/
def randP (pkSeed : prims.PkSeed) (root : prims.Y) (log : G2Log prims) (m : List Byte)
    (addrnd : prims.Y) : OracleComp (OSpec prims (gI prims)) prims.Y :=
  match log.find? (fun e => decide (e.1 = m ∧ e.2.1 = addrnd)) with
  | some e => pure e.2.2
  | none => gameQ prims (gI prims) (.inl (pkSeed, root, m))

/-- The handler by which the port program runs the forger: sampling forwarded, a compression
query becomes a port query, a signing query is answered as in `Lazy.itsrOpen`. -/
noncomputable def portImplI (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (pkSeed : prims.PkSeed) (root : prims.Y) :
    QueryImpl (FSpecP (GeneralScheme.SignatureCore vp prims.core))
      (StateT (G2Log prims) (OracleComp (OSpec prims (gI prims))))
  | .inl n => ((QueryImpl.ofLift unifSpec (OracleComp (OSpec prims (gI prims)))).liftTarget
      (StateT (G2Log prims) (OracleComp (OSpec prims (gI prims))))) n
  | .inr (.inl q) => (liftM (gameQ prims (gI prims) (.inr q)) :
      StateT (G2Log prims) (OracleComp (OSpec prims (gI prims))) St)
  | .inr (.inr m) => logSignOracle optRand ⟨pkSeed, root⟩ (randP pkSeed root)
      (fun m R => openSign prims (gI prims) m pkSeed root R) m

/-- **The open ITSR program of a typed port forger.** -/
noncomputable def itsrOpenP (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (pkSeedDist : ProbComp prims.PkSeed) (mainP : PortForgerProg vp prims) :
    OracleComp (OSpec prims (gI prims)) (prims.Y × ItsrIn prims) := do
  let pkSeed ← (liftM pkSeedDist : OracleComp (OSpec prims (gI prims)) prims.PkSeed)
  let root ← openKeygen prims (gI prims) pkSeed
  let z ← (simulateQ (portImplI optRand pkSeed root) (mainP ⟨pkSeed, root⟩)).run []
  return (z.1.2.randomness, (pkSeed, root, z.1.1))

/-- `portAns g` as a hash-preserving monad morphism. -/
noncomputable def portHom (g : CF St Blk) :
    HasQuery.QueryHom (publicHashSpec prims.core) (OracleComp (OSpec prims (gI prims)))
      (OracleComp (OSpec prims (Lazy.itsrG prims))) :=
  { toMonadHom := simulateQ' (portAns g)
    map_query' := fun q => by simp [portAns] }

theorem portAns_secQ (g : CF St Blk) (a : Adrs) :
    simulateQ (portAns g) (secQ prims (gI prims) a) = secQ prims (Lazy.itsrG prims) a := by
  unfold secQ
  rw [simulateQ_spec_query]
  rfl

theorem portAns_openKeygen (g : CF St Blk) (pkSeed : prims.PkSeed) :
    simulateQ (portAns g) (openKeygen prims (gI prims) pkSeed) =
      openKeygen prims (Lazy.itsrG prims) pkSeed :=
  GeneralScheme.keygenInternalWithSecretM_natural (vp := vp) prims.core (portHom g)
    (secQ prims (gI prims)) (secQ prims (Lazy.itsrG prims)) (fun a _ => portAns_secQ g a) pkSeed

theorem portAns_openSign (g : CF St Blk) (msg : List Byte) (pkSeed : prims.PkSeed)
    (root R : prims.Y) :
    simulateQ (portAns g) (openSign prims (gI prims) msg pkSeed root R) =
      openSign prims (Lazy.itsrG prims) msg pkSeed root R :=
  GeneralScheme.signInternalWithSecretRandomizerM_natural (vp := vp) prims.core (portHom g)
    (secQ prims (gI prims)) (secQ prims (Lazy.itsrG prims)) (fun a _ => portAns_secQ g a)
    msg pkSeed root R

theorem portAns_randP (g : CF St Blk) (pkSeed : prims.PkSeed) (root : prims.Y)
    (log : G2Log prims) (m : List Byte) (a : prims.Y) :
    simulateQ (portAns g) (randP pkSeed root log m a) = itsrRandomizerO pkSeed root log m a := by
  unfold randP itsrRandomizerO
  rcases hf : log.find? (fun e => decide (e.1 = m ∧ e.2.1 = a)) with _ | e
  · simp only [hf]
    unfold gameQ
    rw [simulateQ_spec_query]
    rfl
  · simp only [hf, simulateQ_pure]

/-- The step of `logSignOracle`, run. -/
theorem logSignOracle_run {ι : Type} {spec : OracleSpec ι}
    (optRand : PublicKeyCore prims.core → ProbComp prims.Y) (pk : PublicKeyCore prims.core)
    (rnd : G2Log prims → List Byte → prims.Y → OracleComp (unifSpec + spec) prims.Y)
    (sgn : List Byte → prims.Y →
      OracleComp (unifSpec + spec) (GeneralScheme.SignatureCore vp prims.core))
    (m : List Byte) (s : G2Log prims) :
    (logSignOracle optRand pk rnd sgn m).run s =
      (liftM (optRand pk) : OracleComp (unifSpec + spec) prims.Y) >>= fun addrnd =>
        rnd s m addrnd >>= fun R => sgn m R >>= fun sig => pure (sig, s ++ [(m, addrnd, R)]) := by
  simp [logSignOracle]

/-- **Fusion.**  Answering the port of the open ITSR port program by `g` gives
`Lazy.itsrOpen` at the forger program with its port answered by `g`. -/
theorem itsrOpenP_fusion (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (pkSeedDist : ProbComp prims.PkSeed) (g : CF St Blk) (mainP : PortForgerProg vp prims) :
    simulateQ (portAns g) (itsrOpenP optRand pkSeedDist mainP) =
      Lazy.itsrOpen (⟨fun pk => simulateQ (instImpl g) (mainP pk)⟩ :
        Forger vp prims optRand pkSeedDist) := by
  unfold itsrOpenP Lazy.itsrOpen runForgerLog
  simp only [simulateQ_bind, simulateQ_pure, portAns_liftM, portAns_openKeygen]
  refine bind_congr fun pkSeed => bind_congr fun root => ?_
  congr 1
  refine (Ideal.simulateQ_run_simulateQ_eq_of_step (instImpl g) _ _ (portAns g)
    (fun t s => ?_) _ []).symm
  rcases t with n | q | m
  · simp only [portImplI, instImpl, simulateQ_spec_query]
    simp
    show _ = simulateQ (portAns g) (liftM ((OSpec prims (gI prims)).query (.inl n)))
    rw [simulateQ_spec_query]
    rfl
  · simp [portImplI, instImpl, portAns, gameQ]
  · simp only [instImpl, simulateQ_spec_query]
    rw [QueryImpl.add_apply_inr]
    simp only [portImplI]
    rw [logSignOracle_run, logSignOracle_run]
    simp only [simulateQ_bind, simulateQ_pure, portAns_liftM, portAns_randP, portAns_openSign]

/-! ## The lazy cache commutes with `portAns` -/

/-- **The lazy cache commutes with answering the port.** -/
theorem lazyRes_portAns {ι : Type} {G : OracleSpec ι} {D V : Type} [DecidableEq D]
    {κ : Type} {hspec : OracleSpec κ} {α : Type} (g : CF St Blk)
    (P : OracleComp (RSpec (G + hS St Blk) D V hspec) α) :
    lazyRes (simulateQ (portAns g) P) = simulateQ (portAns g) (lazyRes P) := by
  unfold lazyRes
  rw [StateT.run'_eq, StateT.run'_eq, simulateQ_map]
  congr 1
  refine Ideal.simulateQ_run_simulateQ_eq_of_step (portAns g) lazyImplR lazyImplR (portAns g)
    (fun t s => ?_) P []
  rcases t with n | (x | q) | d | h
  · simp [portAns, lazyImplR]
  · simp [portAns, lazyImplR]
  · simp [portAns, lazyImplR]
  · show (simulateQ lazyImplR (liftM ((RSpec G D V hspec).query (.inr (.inr (.inl d)))))).run s = _
    rw [simulateQ_spec_query]
    rcases hc : s.lookup d with _ | v
    · rw [lazyImplR_sec_run_miss d s hc, lazyImplR_sec_run_miss d s hc]
      simp [portAns]
    · rw [lazyImplR_sec_run_hit d s v hc, lazyImplR_sec_run_hit d s v hc]
      simp
  · simp [portAns, lazyImplR]

end Open

end Ideal.Realize.Itsr

#print axioms Ideal.Realize.Itsr.itsrOpenP_fusion
#print axioms Ideal.Realize.Itsr.lazyRes_portAns
