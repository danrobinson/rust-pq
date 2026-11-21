/-
Work package OPEN, items R3 and R7 for the class SM-TCR adversaries `bTcrArM n A`.

Inventory of the second phase `(bTcrArM n A).forge (tbl, L) pk = memoForge n A (tbl, L) pk`
(`Reduction/TcrMemo.lean`): `idealPk` (recomputation of `PK.root`: `Thash`), `g2Run`
(signing simulation `idealSign`: `Thash`, `Hmsg`), `verifyCalls` (`Hmsg`, `Thash`),
`findCollisionM`/`chkM` (`Thash`), `classOut` (index translation).  The existing equation
`Resources2.bTcrArM_forge_open` already puts ALL of these except `classOut` inside the open
program `memoForgeOpen` (`openKeygen`, `openSign`, the `H_msg` query, `verifyFree` through
`collO`), so the only post-processing is `classOut prims n L`.  This file

* (R3) proves `classOut` hash-free (`classOut_withTH`: unchanged under `withTH prims T H`),
  proves the open program hash-free as a term (`tcrMOpen_withTH`, `memoForgeOpen_withTH`), and
  derives the uniform statement `tcrM_phase2_open_uniform`: for ALL `T`, `H` the second phase of
  `bTcrArM n` over `withTH prims T H` is the interpretation, with hash oracle
  `PublicHash.impl (withTH prims T H)`, of ONE open program and ONE post-processing, neither
  depending on `T`, `H`.  So every `Thash`/`Hmsg` evaluation of the second phase is a query;
* (R7) defines the open program `tcrMOpen` and the second phase `tcrMForge` for an ARBITRARY
  forger program `main` (no `Forger` structure, no `pkSeedDist`), the second phase being BY
  DEFINITION the `tblImpl` interpretation of the open program followed by `classOut`, and proves
  it equal to the existing second phase (`tcrM_phase2_open_eq`);
* summary lemmas `tcrM_phase2_open_eq`, `tcrM_phase2_open_hashes(_128s)`.
-/
import Reduction.Open.WithHash
import Reduction.TcrMemo

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal TweakableHash

namespace Reduction
namespace Open

/-- Close a goal `a = b` by `Eq.refl a`, with the definitional equality checked by the KERNEL
only.  (The elaborator's unifier does not unfold stuck `match` auxiliaries whose parameters
differ, here `prims` vs `withTH prims T H`; the kernel does.  No axiom is involved.) -/
elab "tcr_kernel_rfl" : tactic => Lean.Elab.Tactic.withMainContext do
  let g ← Lean.Elab.Tactic.getMainGoal
  let t ← Lean.instantiateMVars (← g.getType)
  let some (_, a, _) := t.eq? | throwError "tcr_kernel_rfl: not an equality"
  let pf ← Lean.Meta.mkEqRefl a
  g.assign pf
  Lean.Elab.Tactic.replaceMainGoal []

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]
variable {optRand : PublicKeyCore prims.core → ProbComp prims.Y}
  {pkSeedDist : ProbComp prims.PkSeed}
variable {ι : Type} {gspec : OracleSpec ι}

attribute [local irreducible] arityTargets tcrTargets

/-- A forger program: the only way a forger enters the second phase. -/
abbrev TcrForgerProg (vp : ValidatedParams) (prims : Primitives vp.params) : Type :=
  PublicKeyCore prims.core →
    OracleComp (unifSpec + (List Byte →ₒ GeneralScheme.SignatureCore vp prims.core))
      (List Byte × GeneralScheme.SignatureCore vp prims.core)

/-! ## R7: the open program and the second phase for an arbitrary forger program -/

/-- **The open second-phase program of `bTcrArM n`, for an arbitrary forger program `main`.**
Written out without the `Forger` structure: key generation (`openKeygen`), ONE run of `main`
against the logging signing oracle with open signing (`openSign`), one `H_msg` query for the
forgery, verification of the forgery with the collision search interleaved (`collO`). -/
noncomputable def tcrMOpen (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (gspec : OracleSpec ι) (main : TcrForgerProg vp prims)
    (L : List (prims.AdrsKey × List prims.Y)) (pkSeed : prims.PkSeed) :
    OracleComp (Lazy.OSpec prims gspec) (ℕ × List prims.Y) := do
  let root ← Lazy.openKeygen prims gspec pkSeed
  let z ← (simulateQ
    ((QueryImpl.ofLift unifSpec (OracleComp (Lazy.OSpec prims gspec))).liftTarget
        (StateT (G2Log prims) (OracleComp (Lazy.OSpec prims gspec))) +
      logSignOracle optRand ⟨pkSeed, root⟩ lazyRandomizerLift
        (fun m R => Lazy.openSign prims gspec m pkSeed root R)) (main ⟨pkSeed, root⟩)).run []
  let dg ← (PublicHash.hmsg prims.core z.1.2.randomness pkSeed root z.1.1 :
    OracleComp (Lazy.OSpec prims gspec) (Bytes vp.params.m))
  let c ← (simulateQ (Resources2.collO (gspec := gspec) pkSeed L)
    (Resources2.verifyFree pkSeed (splitDigest vp.params dg) z.1.2)).run none
  return c.2.getD (0, [])

/-- On a forger, `tcrMOpen` at its program is the existing `memoForgeOpen`. -/
theorem tcrMOpen_eq_memoForgeOpen (A : Forger vp prims optRand pkSeedDist)
    (L : List (prims.AdrsKey × List prims.Y)) (pkSeed : prims.PkSeed) :
    tcrMOpen optRand gspec A.main L pkSeed = Resources2.memoForgeOpen (gspec := gspec) A L pkSeed :=
  rfl

/-- **The second phase of the arity-`n` class adversary for an arbitrary forger program, DEFINED
as the `tblImpl` interpretation of the open program** followed by `classOut`. -/
noncomputable def tcrMForge (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (gspec : OracleSpec ι) (n : ℕ) (main : TcrForgerProg vp prims)
    (s : SecretTable vp prims × List (prims.AdrsKey × List prims.Y)) (pkSeed : prims.PkSeed) :
    OracleComp (unifSpec + gspec) (ℕ × {xs : List prims.Y // xs.length = n}) :=
  simulateQ (Lazy.tblImpl (gspec := gspec) (PublicHash.impl prims) s.1)
      (tcrMOpen optRand gspec main s.2 pkSeed) >>= fun jm => pure (classOut prims n s.2 jm)

/-- The same second phase in closed form (no open program), for an arbitrary forger program:
`memoForge` with the forger entering only through `main`. -/
noncomputable def tcrMForgeClosed (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (n : ℕ) (main : TcrForgerProg vp prims)
    (s : SecretTable vp prims × List (prims.AdrsKey × List prims.Y)) (pkSeed : prims.PkSeed) :
    ProbComp (ℕ × {xs : List prims.Y // xs.length = n}) :=
  memoForge (optRand := optRand) (pkSeedDist := (pure pkSeed : ProbComp prims.PkSeed)) n ⟨main⟩
    s pkSeed

theorem tcrMForgeClosed_forger (n : ℕ) (A : Forger vp prims optRand pkSeedDist)
    (s : SecretTable vp prims × List (prims.AdrsKey × List prims.Y)) (pkSeed : prims.PkSeed) :
    tcrMForgeClosed optRand n A.main s pkSeed = (bTcrArM n A).forge s pkSeed := rfl

/-- **R7, program-generic interpretation lemma**: for every forger program `main` and every
state, the interpretation of the open program followed by `classOut` is the closed second
phase. -/
theorem tcrMForge_eq (n : ℕ) (main : TcrForgerProg vp prims) (tbl : SecretTable vp prims)
    (L : List (prims.AdrsKey × List prims.Y)) (pk : prims.PkSeed) :
    tcrMForge optRand gspec n main (tbl, L) pk =
      (liftM (tcrMForgeClosed optRand n main (tbl, L) pk) : OracleComp (unifSpec + gspec) _) :=
  (Resources2.bTcrArM_forge_open (gspec := gspec) (optRand := optRand)
    (pkSeedDist := (pure pk : ProbComp prims.PkSeed)) n ⟨main⟩ tbl L pk).symm

/-! ## R3: hash-freeness of the post-processing and of the open program -/

/-- **The post-processing `classOut` is hash-free**: it is the same function over
`withTH prims T H` for all `T`, `H`. -/
theorem classOut_withTH (T : prims.PkSeed → prims.AdrsKey → List prims.Y → prims.Y)
    (H : prims.Y → prims.PkSeed → prims.Y → List Byte → Bytes vp.params.m) (n : ℕ)
    (L : List (prims.AdrsKey × List prims.Y)) (jm : ℕ × List prims.Y) :
    classOut (withTH prims T H) n L jm = classOut prims n L jm := by
  tcr_kernel_rfl

/-- **The open program is hash-free as a term**: the program built over `withTH prims T H` is
the program built over `prims`, for all `T`, `H`.  Hence it evaluates `Thash`/`H_msg` only
through its hash-oracle queries. -/
theorem tcrMOpen_withTH (T : prims.PkSeed → prims.AdrsKey → List prims.Y → prims.Y)
    (H : prims.Y → prims.PkSeed → prims.Y → List Byte → Bytes vp.params.m)
    (main : TcrForgerProg vp prims) (L : List (prims.AdrsKey × List prims.Y)) (pkSeed : prims.PkSeed) :
    tcrMOpen (prims := withTH prims T H) optRand gspec main L pkSeed =
      tcrMOpen optRand gspec main L pkSeed := by
  tcr_kernel_rfl

/-- The same for the existing `memoForgeOpen`. -/
theorem memoForgeOpen_withTH (T : prims.PkSeed → prims.AdrsKey → List prims.Y → prims.Y)
    (H : prims.Y → prims.PkSeed → prims.Y → List Byte → Bytes vp.params.m)
    (A : Forger vp prims optRand pkSeedDist) (L : List (prims.AdrsKey × List prims.Y))
    (pkSeed : prims.PkSeed) :
    Resources2.memoForgeOpen (gspec := gspec) (castForger T H A) L pkSeed =
      Resources2.memoForgeOpen (gspec := gspec) A L pkSeed := by
  tcr_kernel_rfl

/-- **R3, uniform form.**  For ALL hash functions `T`, `H`: the second phase of the class
adversary built over `withTH prims T H` (same forger program) is the interpretation — secrets
from `tbl`, hash oracle answered by `T`, `H` — of the ONE open program `tcrMOpen … main L pk`
built over `prims`, followed by the ONE post-processing `classOut prims n L`.  Neither depends
on `T`, `H`; so the hash functions enter the second phase only through the hash oracle. -/
theorem tcrM_phase2_open_uniform (T : prims.PkSeed → prims.AdrsKey → List prims.Y → prims.Y)
    (H : prims.Y → prims.PkSeed → prims.Y → List Byte → Bytes vp.params.m)
    (n : ℕ) (main : TcrForgerProg vp prims) (tbl : SecretTable vp prims)
    (L : List (prims.AdrsKey × List prims.Y)) (pk : prims.PkSeed) :
    (liftM (tcrMForgeClosed (prims := withTH prims T H) optRand n main (tbl, L) pk) :
        OracleComp (unifSpec + gspec) _) =
      simulateQ (Lazy.tblImpl (gspec := gspec) (PublicHash.impl (withTH prims T H)) tbl)
          (tcrMOpen optRand gspec main L pk) >>= fun jm => pure (classOut prims n L jm) :=
  by
  refine ((tcrMForge_eq (prims := withTH prims T H) (optRand := optRand) (gspec := gspec) n main
    tbl L pk).symm).trans ?_
  -- unfold `tcrMForge`; then `tcrMOpen_withTH` and `classOut_withTH`, all definitional
  tcr_kernel_rfl

/-- `tcrM_phase2_open_uniform` for the adversary `bTcrArM n` itself. -/
theorem bTcrArM_phase2_open_uniform (T : prims.PkSeed → prims.AdrsKey → List prims.Y → prims.Y)
    (H : prims.Y → prims.PkSeed → prims.Y → List Byte → Bytes vp.params.m)
    (n : ℕ) (A : Forger vp prims optRand pkSeedDist) (tbl : SecretTable vp prims)
    (L : List (prims.AdrsKey × List prims.Y)) (pk : prims.PkSeed) :
    (liftM ((bTcrArM n (castForger T H A)).forge (tbl, L) pk) :
        OracleComp (unifSpec + gspec) _) =
      simulateQ (Lazy.tblImpl (gspec := gspec) (PublicHash.impl (withTH prims T H)) tbl)
          (tcrMOpen optRand gspec A.main L pk) >>= fun jm => pure (classOut prims n L jm) :=
  tcrM_phase2_open_uniform (optRand := optRand) (gspec := gspec) T H n A.main tbl L pk

/-! ## Summary lemmas for `bTcrArM n A` (all `n`) -/

/-- **Second phase of `bTcrArM n A` = interpretation of the open program** (then the hash-free
`classOut`, `classOut_withTH`), for every state `(tbl, L)` and every game spec `gspec`. -/
theorem tcrM_phase2_open_eq (gspec : OracleSpec ι) (n : ℕ) (A : Forger vp prims optRand pkSeedDist)
    (tbl : SecretTable vp prims) (L : List (prims.AdrsKey × List prims.Y)) (pk : prims.PkSeed) :
    (liftM ((bTcrArM n A).forge (tbl, L) pk) : OracleComp (unifSpec + gspec) _) =
      simulateQ (Lazy.tblImpl (gspec := gspec) (PublicHash.impl prims) tbl)
          (tcrMOpen optRand gspec A.main L pk) >>= fun jm => pure (classOut prims n L jm) :=
  Resources2.bTcrArM_forge_open (gspec := gspec) n A tbl L pk

/-- The same with the right side named: the second phase is `tcrMForge`. -/
theorem tcrM_phase2_eq_tcrMForge (gspec : OracleSpec ι) (n : ℕ)
    (A : Forger vp prims optRand pkSeedDist)
    (s : SecretTable vp prims × List (prims.AdrsKey × List prims.Y)) (pk : prims.PkSeed) :
    (liftM ((bTcrArM n A).forge s pk) : OracleComp (unifSpec + gspec) _) =
      tcrMForge optRand gspec n A.main s pk :=
  tcrM_phase2_open_eq gspec n A s.1 s.2 pk

/-- Queries of kind `K ≠ .unif` of the open program, for an arbitrary forger program with at
most `qs` signing queries. -/
theorem tcrMOpen_kindBound (gspec : OracleSpec ι) (main : TcrForgerProg vp prims) (K : Lazy.Kind)
    (hK : K ≠ .unif) (qs : ℕ)
    (hA : ∀ pk, IsQueryBoundP (main pk) (fun i => i.isRight = true) qs)
    (L : List (prims.AdrsKey × List prims.Y)) (pkSeed : prims.PkSeed) :
    IsQueryBoundP (tcrMOpen optRand gspec main L pkSeed) (fun t => Lazy.kind t = K)
      (Lazy.keygenB vp (Lazy.ind K .sec) (Lazy.ind K .hash) +
        qs * Lazy.signB vp (Lazy.ind K .sec) (Lazy.ind K .hash) +
        (1 + Resources2.verifyHashes vp * 2)) :=
  Resources2.memoForgeOpen_kindBound (gspec := gspec) (optRand := optRand)
    (pkSeedDist := (pure pkSeed : ProbComp prims.PkSeed)) ⟨main⟩ K hK qs hA L pkSeed

/-- **Hash queries of the open second-phase program** (arbitrary forger program with at most
`qs` signing queries): `≤ keygenHashes + qs·signHashes + (1 + verifyHashes·2)`. -/
theorem tcrM_phase2_open_hashes (gspec : OracleSpec ι) (main : TcrForgerProg vp prims) (qs : ℕ)
    (hA : ∀ pk, IsQueryBoundP (main pk) (fun i => i.isRight = true) qs)
    (L : List (prims.AdrsKey × List prims.Y)) (pkSeed : prims.PkSeed) :
    IsQueryBoundP (tcrMOpen optRand gspec main L pkSeed) (fun t => Lazy.kind t = .hash)
      (Lazy.keygenHashes vp + qs * Lazy.signHashes vp + (1 + Resources2.verifyHashes vp * 2)) :=
  Resources2.memoForgeOpen_hashes (gspec := gspec) (optRand := optRand)
    (pkSeedDist := (pure pkSeed : ProbComp prims.PkSeed)) ⟨main⟩ qs hA L pkSeed

/-- Secret-table reads of the open second-phase program. -/
theorem tcrM_phase2_open_reads (gspec : OracleSpec ι) (main : TcrForgerProg vp prims) (qs : ℕ)
    (hA : ∀ pk, IsQueryBoundP (main pk) (fun i => i.isRight = true) qs)
    (L : List (prims.AdrsKey × List prims.Y)) (pkSeed : prims.PkSeed) :
    IsQueryBoundP (tcrMOpen optRand gspec main L pkSeed) (fun t => Lazy.kind t = .sec)
      (Lazy.keygenB vp 1 0 + qs * Lazy.signB vp 1 0 + (1 + Resources2.verifyHashes vp * 2)) :=
  Resources2.memoForgeOpen_reads (gspec := gspec) (optRand := optRand)
    (pkSeedDist := (pure pkSeed : ProbComp prims.PkSeed)) ⟨main⟩ qs hA L pkSeed

/-- **SLH-DSA-SHA2-128s**: `≤ 269824 + qs·2007385 + 7857` hash queries. -/
theorem tcrM_phase2_open_hashes_128s {ι : Type} (gspec : OracleSpec ι)
    (optRand : PublicKeyCore Link.prims.core → ProbComp Link.prims.Y)
    (main : TcrForgerProg Link.vp Link.prims) (qs : ℕ)
    (hA : ∀ pk, IsQueryBoundP (main pk) (fun i => i.isRight = true) qs)
    (L : List (Link.prims.AdrsKey × List Link.prims.Y)) (pkSeed : Link.prims.PkSeed) :
    IsQueryBoundP (tcrMOpen optRand gspec main L pkSeed) (fun t => Lazy.kind t = .hash)
      (269824 + qs * 2007385 + 7857) :=
  Resources2.memoForgeOpen_hashes_128s (gspec := gspec) optRand
    (pure pkSeed : ProbComp Link.prims.PkSeed) ⟨main⟩ qs hA L pkSeed

end Open

#print axioms Open.tcrMOpen
#print axioms Open.tcrMOpen_eq_memoForgeOpen
#print axioms Open.tcrMForge_eq
#print axioms Open.classOut_withTH
#print axioms Open.tcrMOpen_withTH
#print axioms Open.memoForgeOpen_withTH
#print axioms Open.tcrM_phase2_open_uniform
#print axioms Open.bTcrArM_phase2_open_uniform
#print axioms Open.tcrM_phase2_open_eq
#print axioms Open.tcrM_phase2_eq_tcrMForge
#print axioms Open.tcrM_phase2_open_hashes
#print axioms Open.tcrM_phase2_open_reads
#print axioms Open.tcrM_phase2_open_hashes_128s

end Reduction
