# OPEN-O4 — R3 and R7 for the class SM-TCR adversaries `bTcrArM n A`

File: `Reduction/Open/Tcr.lean` (imports `Reduction.Open.WithHash`, `Reduction.TcrMemo`; namespace `Reduction.Open`;
compiles in ~5 s, no error; olean written). No sorry/axiom/native_decide; nothing existing edited.

## Inventory (R3): hash evaluations of the second phase `memoForge n A (tbl, L) pk`
| place | evaluates | status |
|---|---|---|
| `idealPk` (recompute PK.root); `g2Run`/`idealSign` (signing) | `Thash` | queries (`openKeygen`; `openSign`) |
| digest of the forgery inside `verifyCalls` | `Hmsg` | one query (`PublicHash.hmsg`) |
| `verifyCalls` (FORS pk, hypertree root) | `Thash` | queries (`verifyFree` through `collO`) |
| `findCollisionM` / `chkM` (collision test, lookup in `L`) | `Thash` (≤ 2 per call) | queries (`collO`) |
| `classOut prims n L` (index translation) | nothing | proved hash-free: `classOut_withTH` |
`Resources2.bTcrArM_forge_open` already had everything but `classOut` inside `memoForgeOpen`: NO extension of
the open program, NO new bound. New: hash-freeness (post-processing AND open program) is a theorem.

## Definitions (verbatim)
```lean
abbrev ForgerProg (vp : ValidatedParams) (prims : Primitives vp.params) : Type :=
  PublicKeyCore prims.core → OracleComp (unifSpec + (List Byte →ₒ GeneralScheme.SignatureCore vp prims.core))
      (List Byte × GeneralScheme.SignatureCore vp prims.core)
noncomputable def tcrMOpen (optRand : PublicKeyCore prims.core → ProbComp prims.Y) (gspec : OracleSpec ι)
    (main : ForgerProg vp prims) (L : List (prims.AdrsKey × List prims.Y)) (pkSeed : prims.PkSeed) :
    OracleComp (Lazy.OSpec prims gspec) (ℕ × List prims.Y)      -- body of memoForgeOpen written out, no `Forger`
noncomputable def tcrMForge optRand gspec (n : ℕ) (main : ForgerProg vp prims)
    (s : SecretTable vp prims × List (prims.AdrsKey × List prims.Y)) (pkSeed : prims.PkSeed) :
    OracleComp (unifSpec + gspec) (ℕ × {xs : List prims.Y // xs.length = n}) :=
  simulateQ (Lazy.tblImpl (gspec := gspec) (PublicHash.impl prims) s.1) (tcrMOpen optRand gspec main s.2 pkSeed)
    >>= fun jm => pure (classOut prims n s.2 jm)
noncomputable def tcrMForgeClosed optRand (n : ℕ) (main : ForgerProg vp prims) s pkSeed :
    ProbComp (ℕ × {xs : List prims.Y // xs.length = n}) := memoForge (pkSeedDist := pure pkSeed) n ⟨main⟩ s pkSeed
```
`Forger` is a one-field structure (`main`), so `⟨main⟩` is an arbitrary program; `pkSeedDist` is phantom.

## Theorems (verbatim statements; `T`, `H` range over all `Thash`/`Hmsg`-typed functions)
```lean
-- rfl: tcrMOpen_eq_memoForgeOpen : tcrMOpen optRand gspec A.main L pkSeed = Resources2.memoForgeOpen A L pkSeed
-- rfl: tcrMForgeClosed_forger : tcrMForgeClosed optRand n A.main s pkSeed = (bTcrArM n A).forge s pkSeed
theorem tcrMForge_eq (n) (main : ForgerProg vp prims) tbl L pk :                       -- R7, generic in the program
    tcrMForge optRand gspec n main (tbl, L) pk = (liftM (tcrMForgeClosed optRand n main (tbl, L) pk) : OracleComp (unifSpec + gspec) _)
theorem classOut_withTH T H n L jm : classOut (withTH prims T H) n L jm = classOut prims n L jm          -- R3
theorem tcrMOpen_withTH T H main L pkSeed : tcrMOpen (prims := withTH prims T H) optRand gspec main L pkSeed = tcrMOpen optRand gspec main L pkSeed
theorem memoForgeOpen_withTH T H (A) L pkSeed : Resources2.memoForgeOpen (castForger T H A) L pkSeed = Resources2.memoForgeOpen A L pkSeed
theorem tcrM_phase2_open_uniform T H n main tbl L pk :                                 -- R3, main statement
    (liftM (tcrMForgeClosed (prims := withTH prims T H) optRand n main (tbl, L) pk) : OracleComp (unifSpec + gspec) _) =
      simulateQ (Lazy.tblImpl (gspec := gspec) (PublicHash.impl (withTH prims T H)) tbl)
          (tcrMOpen optRand gspec main L pk) >>= fun jm => pure (classOut prims n L jm)
theorem bTcrArM_phase2_open_uniform T H n (A) tbl L pk : liftM ((bTcrArM n (castForger T H A)).forge (tbl, L) pk) = <same at A.main>
theorem tcrM_phase2_open_eq (gspec : OracleSpec ι) (n : ℕ) (A : Forger vp prims optRand pkSeedDist)
    (tbl : SecretTable vp prims) (L : List (prims.AdrsKey × List prims.Y)) (pk : prims.PkSeed) :
    (liftM ((bTcrArM n A).forge (tbl, L) pk) : OracleComp (unifSpec + gspec) _) =
      simulateQ (Lazy.tblImpl (gspec := gspec) (PublicHash.impl prims) tbl)
          (tcrMOpen optRand gspec A.main L pk) >>= fun jm => pure (classOut prims n L jm)
theorem tcrM_phase2_open_hashes (gspec : OracleSpec ι) (main : ForgerProg vp prims) (qs : ℕ)
    (hA : ∀ pk, IsQueryBoundP (main pk) (fun i => i.isRight = true) qs)
    (L : List (prims.AdrsKey × List prims.Y)) (pkSeed : prims.PkSeed) :
    IsQueryBoundP (tcrMOpen optRand gspec main L pkSeed) (fun t => Lazy.kind t = .hash)
      (Lazy.keygenHashes vp + qs * Lazy.signHashes vp + (1 + Resources2.verifyHashes vp * 2))
theorem tcrM_phase2_open_hashes_128s gspec optRand (main : ForgerProg Link.vp Link.prims) qs hA L pkSeed : IsQueryBoundP (tcrMOpen optRand gspec main L pkSeed) (fun t => Lazy.kind t = .hash) (269824 + qs * 2007385 + 7857)
```
Also `tcrM_phase2_eq_tcrMForge` (`liftM ((bTcrArM n A).forge s pk) = tcrMForge optRand gspec n A.main s pk`),
`tcrMOpen_kindBound` (any kind `K ≠ .unif`), `tcrM_phase2_open_reads` (secret reads).
Bundle fields: `tcrM_phase2_open_eq gspec n A`, `tcrM_phase2_open_hashes gspec A.main qs hA` (∀ `n`, `tbl`, `L`,
`pk`; headline `n = 1, 2, len, k` are instances; the open program does not depend on `n`, only `classOut` does).
`tcrM_phase2_open_uniform` reads: ONE open program and ONE post-processing (over `prims`) give the second phase
for every `(T, H)` answering the hash oracle; `Thash`/`Hmsg` enter only through (counted) hash queries.
## Deviations / caveats
1. Equations live in `OracleComp (unifSpec + gspec)` with `liftM` on the closed side (as in the existing
   `bTcrArM_forge_open`), for every `gspec`; no `ProbComp`-level equation.
2. Only `withTH` (`Thash`, `Hmsg`); invariance under `withHash` (also `PRF`, `PRFmsg`; types change) NOT stated.
3. Proof method of the three `_withTH` lemmas and the last step of `tcrM_phase2_open_uniform`: a local
   tactic `tcr_kernel_rfl` (defined at the top of the file) that supplies `Eq.refl` and leaves the
   definitional check to the KERNEL. Reason: the elaborator's `rfl` does not unfold stuck `match`
   auxiliaries (`classOut`, `collO`, `lazyRandomizer`) whose `prims` parameter differs. No axiom; a false
   equation is rejected by the kernel (tested: `2 + 2 = 5`).
4. R7: both options given (program-generic lemmas over `ForgerProg`; `tcrMForge` DEFINED as the
   interpretation); `bTcrArM` itself not redefined. Reduction/Gen already has the general-sampling analogue
   (`memoForgeOpenG`, `bTcrArMG_forge_open`, `memoForgeOpenG_hashes`); no `withTH` lemma for it. R4 not here.

Axioms: `#print axioms` for all 13 names above (file end): each `[propext, Classical.choice, Quot.sound]`.
