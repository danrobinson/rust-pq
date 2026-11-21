# GEN — interface for `quantum/` (forgers over a general sampling spec)

Status: PROVED (typed/byte-level, internal/external, EUF/SUF, linear and absolute-value). Files:
`security/Reduction/Gen/*.lean`; full report `security/status/GEN.md`.

## Types
- `ds : OracleSpec.{0,0} κ` arbitrary with `[OracleSpec.AnswerMeasure ds] [∀ d, Fintype (ds.Range d)]`.
  For quantum: `ds := PQ.Interactive.distSpec` (its instances are in `Strategy.lean`).
- `Reduction.Gen.gSpec ds = ds + unifSpec` (abbrev; at `distSpec` this is `privSpec`).
- `Reduction.Gen.liftR ds`, `Reduction.Gen.liftAlg ds sigAlg`: the SAME definitions as quantum's
  `liftR`, `liftSig` (`liftSig sigAlg = liftAlg distSpec sigAlg := rfl`, checked).
- Forger: VCVio's `SignatureAlg.UnforgeableAdversary (liftAlg ds alg)` /
  `StrongUnforgeableAdversary (liftAlg ds alg)`, `alg ∈ {internalAlg, externalAlg, bytesAlg, pureBytesAlg}`
  (abbrevs `GForger`, `GStrongForger`, `GExtForger`, `GBytesForger`, `GPureBytesForger`, …).
  So `Q.toStrategy : UnforgeableAdversary (liftSig sigAlg)` is accepted as is.
- Advantage: `eufAdvG ds A = 𝒟[SignatureAlg.unforgeableExperiment A] {true}` (`eufAdvG_def`, `rfl`),
  `sufAdvG ds S = 𝒟[SignatureAlg.strongUnforgeableExperiment S] {true}` — exactly the quantity of
  `qUnforgeableAdvantage_eq_strategy`.

## Theorems to apply (`Reduction/Gen/Final.lean`, namespace `Reduction.Gen`)
```lean
theorem slhdsa_euf_cmaG (hS : Structural vp prims) (A : GForger ds vp prims optRand pkSeedDist) :
    eufAdvG ds A ≤ betaEufG ds optRand pkSeedDist A.main
theorem slhdsa_euf_cma_linearG (hS) (A : GForger ds vp prims optRand pkSeedDist) :
    eufAdvG ds A + linIdealEufG ds optRand pkSeedDist A.main ≤ linRealEufG ds optRand pkSeedDist A.main
-- likewise slhdsa_suf_cmaG / _linearG (GStrongForger, sufAdvG, betaSufG, linIdealSufG/linRealSufG),
-- slhdsa_pure_{euf,suf}_cma(_linear)G, slhdsa_bytes_{euf,suf}_cma(_linear)G,
-- slhdsa_pure_bytes_{euf,suf}_cma(_linear)G  (right sides at (toInternalG ds A).main, (bytesToTypedG ds A).main, …)
```
`betaEufG ds optRand pkSeedDist F` = the twelve advantages, in WRAPPER games (adversaries over
`ds + unifSpec`), of `bPrfCG F`, `bPrfMsgLG F`, `bItsrLG F`, `toDsprG F`, `toTcrG F`,
`bTcrArMG n F` (n = 1, 2, len, k), `rUdG F`, `rPreG F`, `rTcrTG F` (each: the classical reduction
code around ONE run of the forger family `F`).

## Composition (type-checked in `security/scratch/Gen/QuantumCompose.lean`)
```lean
theorem slhdsa_euf_cma_quantum_viaG (hS : Structural vp prims)
    (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) :
    qUnforgeableAdvantage Q ≤ betaEufG distSpec optRand pkSeedDist Q.toStrategy.main :=
  qUnforgeableAdvantage_le_of_forall_strategy Q
    (fun A ↦ betaEufG distSpec optRand pkSeedDist A.main) (fun A ↦ slhdsa_euf_cmaG distSpec hS A)
```
compile with `LEAN_PATH="$(lake env printenv LEAN_PATH):$PWD/../quantum/.lake/build/lib/lean" lean scratch/Gen/QuantumCompose.lean`
from `security/`. Axioms: propext, Classical.choice, Quot.sound.

## What quantum would still need on its side
- a SUF analogue of `qUnforgeableAdvantage_le_of_forall_strategy` (only EUF exists in `Strategy.lean`);
- right-hand sides as QUANTUM machines: `toStrategy` analogues of `Wrap.lean`/`Games.lean`
  (the right side above is a classical-strategy quantity over `distSpec + unifSpec`).
- Restriction on our side: `ds` must have finite answer types (true for `distSpec`).
