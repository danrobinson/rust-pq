import Integration.SlhDsaAllCounts
import Integration.SlhDsaAllTight

/-!
# The reduction certificate: the machines ARE the reduction code around the forger (integration)

NOT part of the default target; checked by `scripts/check-integration.sh`.

## Why this is the meaningful resource statement (audit F5)

The model has no cost notion, classical code is uncounted and embeds into quantum machines, and a
classical program may even carry a density matrix.  So neither "there exist quantum machines with
these advantages" nor a bound on the quantum operations along each path says by itself that the
machines on the right-hand sides of the headlines are the *reductions* run on the *forger*.

What does say it is syntactic.  A sampler `s : Sampler W` is an arbitrary rule for drawing the
outcome of each instrument node (given the instrument and the tracked state); `toProbCompWith s`
replaces every instrument node of a machine by the classical code `s` and leaves every other node
— all classical control, all oracle queries — untouched, and `Q.toClassicalWith s` is the forger
`Q` with its instrument nodes replaced in this way.  `ReductionCertificate Q` states, for EVERY
sampler `s` and for every machine `qb Q` of the final headlines:

    toProbCompWith s (qb Q) Q.ρ₀ = b (Q.toClassicalWith s)          (single-phase machines)
    (qb Q).toClassicalWith s      = b (Q.toClassicalWith s)          (two-phase machines)

where `b` is the classical reduction adversary of `security/Reduction` — an equality of PROGRAMS,
not of distributions.  Since `s` is arbitrary and is used as an opaque block at the positions of
the instrument nodes, the equation determines the machine up to what it does at instrument nodes:
whatever the forger does at its instrument nodes, the machine `qb Q` does the reduction's
classical code `b` around it, with the forger's instrument nodes at the forger's positions, fed
with the forger's tracked state, and its control flow continuing with the outcome drawn.  In
particular the machine cannot run the forger twice, cannot continue "as if a different outcome
had occurred", and cannot replace the forger by a classical simulation: each of these would
change the right-hand side for some sampler (e.g. for the uniform sampler `unifSamp`, under which
`toProbCompWith` is a relabelling of the control tree — `classicalQueryBound_iff_unif` — or for a
sampler that is constant on one instrument and not on another).

The limit theorems use the certificate at the rational samplers `sampN n`; the classical
resource counts use it at `unifSamp`; `qfinal_resources_final.classical` states the classical
counts at every sampler.

## What `instrTraces ⊆` adds

The trace inclusions (`QuantumResourcesFinal`, `quantum_resources_final`) are a sampler-free fact
about the machine terms themselves: along every path, the sequence of instrument indices is that
of a path of a single run of the forger.  They bound number, identity and order of the quantum
operations per path directly (no classicalisation involved), but they do not determine the
control flow between them; the certificate does.  The initial states agree by definition
(`ρ₀ := Q.ρ₀`, field `rho` of `QuantumResourcesFinal`).

## Scope

`ReductionCertificate Q` covers, for an internal typed quantum forger `Q`: the EUF and SUF PRF
distinguishers, the ITSR adversary, the FORS-leaf adversaries, the class adversaries in both
variants (`qbTcrArM n` of the final headlines, `qbTcrArST n` of the tight-cap headlines), the
unsplit `qbTcrS`, the chain adversaries `qrUd`, `qrPre`, `qrTcr`, `qrTcrT`, and the open machines
of `SlhDsaAllCounts.lean` on which the post-seed hash evaluations are counted.  The interface
translations are certified by `wrapper_certificate_*`, and
`reduction_certificate_{pure,bytes,pure_bytes}` combine both for the forgers of the external and
byte-level headlines.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal PQ.Interactive
open scoped ComplexOrder

namespace Reduction

open TweakableHash Resources2

set_option linter.unusedSectionVars false

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]
  [Fintype prims.Y]
variable {codec : CoreWireCodec vp.params prims.core}
variable {optRand : PublicKeyCore prims.core → ProbComp prims.Y}
  {pkSeedDist : ProbComp prims.PkSeed}
variable {W : Type} [Fintype W]

attribute [local irreducible] arityTargets tcrTargets

/-- What `Q.toClassicalWith s` is: the forger's program with every instrument node replaced by
the sampler. -/
theorem toClassicalWith_main (s : Sampler W)
    (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) (pk : PublicKeyCore prims.core) :
    (Q.toClassicalWith s).main pk = toProbCompWith s (Q.main pk) Q.ρ₀ := rfl

/-- **The reduction certificate.**  For every sampler `s`, the `s`-classicalisation of each
machine of the final headlines is, as a program, the classical reduction adversary of
`security/Reduction` applied to the `s`-classicalisation of the forger.  See the file header. -/
structure ReductionCertificate (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) :
    Prop where
  /-- PRF distinguisher (EUF). -/
  prf : ∀ s : Sampler W, toProbCompWith s (qbPrfC Q) Q.ρ₀ = bPrfC (Q.toClassicalWith s)
  /-- PRF distinguisher (SUF). -/
  prfSuf : ∀ s : Sampler W,
    toProbCompWith s (qbPrfWC sufCheck Q) Q.ρ₀ = bPrfWC sufCheck (Q.toClassicalWith s)
  /-- `PRF_msg` distinguisher (EUF). -/
  msg : ∀ s : Sampler W, toProbCompWith s (qbPrfMsgL Q) Q.ρ₀ = Lazy.bPrfMsgL (Q.toClassicalWith s)
  /-- `PRF_msg` distinguisher (SUF). -/
  msgSuf : ∀ s : Sampler W,
    toProbCompWith s (qbPrfMsgWL sufCheck Q) Q.ρ₀ = Lazy.bPrfMsgWL sufCheck (Q.toClassicalWith s)
  /-- ITSR adversary. -/
  itsr : ∀ s : Sampler W,
    toProbCompWith s (qbItsrL Q) Q.ρ₀ = (Lazy.bItsrL (Q.toClassicalWith s)).main
  /-- SM-DSPR(F) adversary at the FORS leaves. -/
  dspr : ∀ s : Sampler W,
    (qToDspr Q).toClassicalWith s = toDspr (Lazy.bOpenPreS (Q.toClassicalWith s))
  /-- SM-TCR(F) adversary at the FORS leaves. -/
  tcrF : ∀ s : Sampler W,
    (qToTcr Q).toClassicalWith s = toTcr (Lazy.bOpenPreS (Q.toClassicalWith s))
  /-- Memoising class adversaries (final headlines), every arity. -/
  tcrArM : ∀ (s : Sampler W) (n : ℕ),
    (qbTcrArM n Q).toClassicalWith s = bTcrArM n (Q.toClassicalWith s)
  /-- Tight-cap class adversaries (tight headlines), every arity. -/
  tcrArST : ∀ (s : Sampler W) (n : ℕ),
    (qbTcrArST n Q).toClassicalWith s = bTcrArST n (Q.toClassicalWith s)
  /-- Unsplit SM-TCR(`Thash`) adversary (first headline). -/
  tcrS : ∀ s : Sampler W, (qbTcrS Q).toClassicalWith s = Lazy.bTcrS (Q.toClassicalWith s)
  /-- SM-UD(F) adversary. -/
  ud : ∀ s : Sampler W,
    (qrUd Q).toClassicalWith s = rUd pkSeedDist (Lazy.bWotsS (Q.toClassicalWith s))
  /-- SM-PRE(F) adversary. -/
  pre : ∀ s : Sampler W,
    (qrPre Q).toClassicalWith s = rPre pkSeedDist (Lazy.bWotsS (Q.toClassicalWith s))
  /-- SM-TCR(F) chain adversary. -/
  tcrW : ∀ s : Sampler W,
    (qrTcr Q).toClassicalWith s = rTcr pkSeedDist (Lazy.bWotsS (Q.toClassicalWith s))
  /-- SM-TCR(F) chain adversary, tight cap. -/
  tcrWT : ∀ s : Sampler W,
    (qrTcrT Q).toClassicalWith s = rTcrT pkSeedDist (Lazy.bWotsS (Q.toClassicalWith s))
  /-- Open machine of the FORS second phases. -/
  openFors : ∀ (s : Sampler W) pk ys,
    toProbCompWith s (qFindOpenFull Q pk ys) Q.ρ₀ = findOpenFull (Q.toClassicalWith s) pk ys
  /-- Open machine of the class second phases. -/
  openMemo : ∀ (s : Sampler W) {ι : Type} (gspec : OracleSpec ι) L pk,
    toProbCompWith s (qMemoForgeOpen (gspec := gspec) Q L pk) Q.ρ₀ =
      memoForgeOpen (Q.toClassicalWith s) L pk
  /-- Open machine of the chain second phases. -/
  openWots : ∀ (s : Sampler W) {ι : Type} (gspec : OracleSpec ι) tbl hist root pk {β : Type}
      (tail : ℕ × prims.Y × WotsSig vp.params prims.core → OracleComp (Lazy.OSpec prims gspec) β),
    toProbCompWith s (qWotsPhase2O Q tbl hist root pk tail) Q.ρ₀ =
      wotsPhase2O (Q.toClassicalWith s) tbl hist root pk tail

/-- **Every machine of the final headlines is the reduction's classical code around the
forger's program, for every way of sampling the forger's instruments.**  No hypothesis. -/
theorem reduction_certificate (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) :
    ReductionCertificate Q where
  prf := fun s ↦ toProbCompWith_qbPrfC s Q
  prfSuf := fun s ↦ toProbCompWith_qbPrfWC s sufCheck Q
  msg := fun s ↦ toProbCompWith_qbPrfMsgL s Q
  msgSuf := fun s ↦ toProbCompWith_qbPrfMsgWL s sufCheck Q
  itsr := fun s ↦ toProbCompWith_qbItsrL s Q
  dspr := fun s ↦ toClassicalWith_qToDspr s Q
  tcrF := fun s ↦ toClassicalWith_qToTcr s Q
  tcrArM := fun s n ↦ toClassicalWith_qbTcrArM s n Q
  tcrArST := fun s n ↦ toClassicalWith_qbTcrArST s n Q
  tcrS := fun s ↦ toClassicalWith_qbTcrS s Q
  ud := fun s ↦ toClassicalWith_qrUd s Q
  pre := fun s ↦ toClassicalWith_qrPre s Q
  tcrW := fun s ↦ toClassicalWith_qrTcr s Q
  tcrWT := fun s ↦ toClassicalWith_qrTcrT s Q
  openFors := fun s pk ys ↦ toProbCompWith_qFindOpenFull s Q pk ys
  openMemo := fun s _ _ L pk ↦ toProbCompWith_qMemoForgeOpen s Q L pk
  openWots := fun s _ _ tbl hist root pk _ tail ↦
    toProbCompWith_qWotsPhase2O s Q tbl hist root pk tail

/-! ## The interface translations -/

/-- The context-string wrapper around a quantum forger is the classical wrapper `toInternal`
around its program, for every sampler. -/
theorem wrapper_certificate_pure (Q : QForger W (externalAlg vp prims optRand pkSeedDist)) :
    ∀ s : Sampler W, (qToInternal Q).toClassicalWith s = toInternal (Q.toClassicalWith s) :=
  fun s ↦ toClassicalWith_qToInternal s Q

/-- The byte-level wrapper around a quantum forger is the classical wrapper `bytesToTyped`
around its program, for every sampler. -/
theorem wrapper_certificate_bytes (Q : QForger W (bytesAlg vp prims codec optRand pkSeedDist)) :
    ∀ s : Sampler W, (qBytesToTyped Q).toClassicalWith s = bytesToTyped (Q.toClassicalWith s) :=
  fun s ↦ toClassicalWith_qBytesToTyped s Q

/-- The byte-level context-string wrapper around a quantum forger is the classical wrapper
`toInternal ∘ pureBytesToTyped` around its program, for every sampler. -/
theorem wrapper_certificate_pure_bytes
    (Q : QForger W (pureBytesAlg vp prims codec optRand pkSeedDist)) :
    ∀ s : Sampler W, (qPureBytesToInternal Q).toClassicalWith s =
      toInternal (pureBytesToTyped (Q.toClassicalWith s)) :=
  fun s ↦ toClassicalWith_qPureBytesToInternal s Q

/-- Certificate for the machines of the external (context-string) headlines. -/
theorem reduction_certificate_pure (Q : QForger W (externalAlg vp prims optRand pkSeedDist)) :
    ReductionCertificate (qToInternal Q) ∧
      ∀ s : Sampler W, (qToInternal Q).toClassicalWith s = toInternal (Q.toClassicalWith s) :=
  ⟨reduction_certificate _, wrapper_certificate_pure Q⟩

/-- Certificate for the machines of the byte-level headlines. -/
theorem reduction_certificate_bytes
    (Q : QForger W (bytesAlg vp prims codec optRand pkSeedDist)) :
    ReductionCertificate (qBytesToTyped Q) ∧
      ∀ s : Sampler W, (qBytesToTyped Q).toClassicalWith s = bytesToTyped (Q.toClassicalWith s) :=
  ⟨reduction_certificate _, wrapper_certificate_bytes Q⟩

/-- Certificate for the machines of the byte-level context-string headlines. -/
theorem reduction_certificate_pure_bytes
    (Q : QForger W (pureBytesAlg vp prims codec optRand pkSeedDist)) :
    ReductionCertificate (qPureBytesToInternal Q) ∧
      ∀ s : Sampler W, (qPureBytesToInternal Q).toClassicalWith s =
        toInternal (pureBytesToTyped (Q.toClassicalWith s)) :=
  ⟨reduction_certificate _, wrapper_certificate_pure_bytes Q⟩

/-- **Certificate, trace inclusions and classical counts together** (internal typed forger with
at most `qs` classical signing queries per run). -/
theorem reduction_certificate_resources (hS : Structural vp prims)
    (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) (qs : ℕ)
    (hQ : ∀ pk, ClassicalQueryBound (Q.main pk) (fun i => i.isRight = true) qs) :
    ReductionCertificate Q ∧ QuantumResourcesFinal Q ∧
      QFinalResourcesFinal Q qs (Resources2.directCounts vp qs) (finalMemoP2 vp qs) :=
  ⟨reduction_certificate Q, quantum_resources_final Q, qfinal_resources_final hS Q qs hQ⟩

end Reduction

#print axioms Reduction.reduction_certificate
#print axioms Reduction.reduction_certificate_pure
#print axioms Reduction.reduction_certificate_bytes
#print axioms Reduction.reduction_certificate_pure_bytes
#print axioms Reduction.reduction_certificate_resources
