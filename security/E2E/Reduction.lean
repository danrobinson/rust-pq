import E2E.Main
import Reduction.Instance128s

/-!
# End to end, standard model: the Rust code and the EUF-CMA reduction

`E2E.end_to_end` relates the Rust functions to the scheme
`internalAlg Link.vp Link.prims optRand pkSeedDist` (FIPS 205 Algorithms 18–20 at
SLH-DSA-SHA2-128s).  `Reduction.slhdsa_sha2_128s_euf_cma` bounds the EUF-CMA advantage of every
forger against *that same term* by standard-model advantages against the SHA-2-based functions of
`Link.prims`.  `E2E.standard_model_security` states both in one theorem; the two libraries use the
same `vp` and `prims` (`Link.vp`, `Link.prims`), checked by `scheme_eq` below (`rfl`).
-/

namespace E2E

open Aeneas Aeneas.Std Result
open SLHDSA SLHDSA.Concrete SLHDSA.Security OracleComp OracleSpec SignatureAlg ENNReal
open Link (vp prims)
open Reduction (bPrf bPrfMsg bItsr bOpenPre bTcr bWots rUd rPre rTcr)

/-- The scheme of the Rust link (`EndToEnd`) and the scheme attacked in the reduction
(`Reduction.Forger Link.vp Link.prims …`) are the same term. -/
theorem scheme_eq (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (pkSeedDist : ProbComp prims.PkSeed) :
    Reduction.realAlg Link.vp Link.prims optRand pkSeedDist =
      internalAlg vp prims optRand pkSeedDist := rfl

/-- **The Rust code and standard-model EUF-CMA security, in one statement.**

Fix how `opt_rand` and `PK.seed` are sampled (`optRand`, `pkSeedDist`; arbitrary — deterministic
and hedged signing are both covered).  Let `S = internalAlg vp prims optRand pkSeedDist`: FIPS 205
Algorithms 18–20 (`slh_keygen_internal`, `slh_sign_internal`, `slh_verify_internal`) at
SLH-DSA-SHA2-128s, with `SK.seed`, `SK.prf` uniform.

1. `EndToEnd optRand pkSeedDist`: the Rust `slh_keygen_internal`, `slh_sign_internal`,
   `slh_verify_internal` (Aeneas translation) never panic and compute the deterministic cores of
   `S.keygen`, `S.sign`, `S.verify` on the FIPS byte encodings (see `EndToEnd` for the exact
   items, including the older random-oracle SUF-CMA bound, which is independent of item 2).
2. For **every** chosen-message forger `A` against `S` (no bound on its queries or running time),
   its EUF-CMA advantage is at most the sum of eight advantages, each of a choice-free adversary
   (`Reduction.bPrf A`, …; black-box, straight-line, each running `A` once) in a standard-model
   game on a function of `prims`, i.e. of SHA-256 as used by FIPS 205 §11.2.1:
   * PRF security of `prims.PRF` keyed by `SK.seed`, and of `prims.PRFmsg` (HMAC-SHA-256) keyed
     by `SK.prf`;
   * interleaved target-subset resilience (ITSR) of `prims.Hmsg` keyed by the randomizer;
   * for the tweakable hash `prims.Thash` under the seed distribution `pkSeedDist`:
     single-function multi-target opening-preimage resistance (SM-DT-OpenPRE) of `F` at the
     `2^h·k·2^a` FORS leaves; target-collision resistance (SM-TCR) of `Thash` over all hash
     calls of the key structure; and undetectability (SM-UD, with coefficient `w - 2 = 14`),
     preimage resistance (SM-PRE) and SM-TCR of `F` on the WOTS+ chains.

**What this does not say.**

* The eight advantages are *not* bounded here.  That they are small for SHA-256-based functions
  is an unproven cryptographic assumption (as for any hash-based scheme); the theorem only says
  that a forger yields an adversary against one of these named properties.
* **No running-time claim.**  The reductions are choice-free definitions with proved
  query/target caps (`Reduction.slhdsa_euf_cma_resources`, `standard_model_resources`), but five
  of them sample and carry an eager table of all `2^256`-indexed secret values, so as written
  they are not feasible; the caps of the SM games are exponential in `h` (at 128s
  `openPreTargets = 14·2^75 ≈ 2^78.81`, `tcrTargets ≈ 2^79.81`, `wotsChainTargets ≈ 2^68.13`,
  `wotsStepTargets ≈ 2^72.13`).
* **Superseded** by `E2E.standard_model_security_split` (`E2E/FinalSplit.lean`) and
  `E2E.standard_model_security_final` (`E2E/Final.lean`): there the PRF game is
  on the secret-key address domain (the game `Reduction.skPrf` used here is false at SHA2-128s,
  `Reduction.skPrf_broken_128s`, which makes the first summand below useless), no adversary
  samples the eager table, the FORS term is `SM-DSPR + 3·SM-TCR`, and SUF-CMA is covered.
* EUF-CMA only (a forgery is on a message never submitted to the signing oracle); strong
  unforgeability (SUF-CMA) is not covered by item 2 (it is by `E2E/Final.lean`,
  `E2E/FinalSplit.lean`).  Single key.
* Internal algorithms only: the messages are the internal messages `M'`.  The external
  interfaces `slh_sign`/`slh_verify` (FIPS 205 Algorithms 22/24, `M' = 0 ‖ |ctx| ‖ ctx ‖ M`) are
  not the scheme of item 2; their security theorems are in `E2E/External.lean`, `E2E/Final.lean`,
  `E2E/FinalSplit.lean`.  For the pre-hash variants no security theorem is proved anywhere.
  (`E2E.rust_sign`/`E2E.rust_verify` show the Rust pure interface computes exactly that
  wrapper around the internal algorithms.)
* The Rust-level items are functional statements under the `Room` message-length bound; the Rust
  code computes only the deterministic cores, so sampling `SK.seed`, `SK.prf` uniformly, and
  `PK.seed`, `opt_rand` according to `pkSeedDist`, `optRand`, is the caller's obligation.  For
  the assumptions of item 2 to be plausible `pkSeedDist` must be (close to) uniform.
* Side channels, the Rust compiler and the Aeneas extraction are outside the statement. -/
theorem standard_model_security (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (pkSeedDist : ProbComp prims.PkSeed) :
    EndToEnd optRand pkSeedDist ∧
    ∀ A : SignatureAlg.UnforgeableAdversary (internalAlg vp prims optRand pkSeedDist),
      SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤
        (Reduction.skPrf vp prims).prfAdvantage (bPrf A) +
        (Reduction.msgPrf vp prims).prfAdvantage (bPrfMsg A) +
        KeyedHash.ITSRAdvantage (bItsr A) +
        TweakableHash.SM_DT_OpenPRE_SourceFinalValidity.advantage (bOpenPre A) +
        TweakableHash.SM_DT_TCR_Advantage (bTcr A) +
        ((vp.params.w - 2 : ℕ) : ℝ≥0∞) *
          TweakableHash.SM_DT_UD_Advantage (rUd pkSeedDist (bWots A)) +
        TweakableHash.SM_DT_PRE_Advantage (rPre pkSeedDist (bWots A)) +
        TweakableHash.SM_DT_TCR_Advantage (rTcr pkSeedDist (bWots A)) :=
  ⟨end_to_end optRand pkSeedDist,
    fun A => Reduction.slhdsa_sha2_128s_euf_cma optRand pkSeedDist A⟩

/-- The coefficient of the undetectability term is `14`. -/
theorem w_sub_two : vp.params.w - 2 = 14 := by decide

/-- **Resources of the `qs`-dependent reductions** at SLH-DSA-SHA2-128s.  If the forger makes at
most `qs` signing queries then `bPrf A` makes at most `2^h'·len + qs·(k·2^a + d·2^h'·len)`
queries to its PRF oracle, and `bPrfMsg A`, `bItsr A` at most `qs` queries to their `PRF_msg`
oracle / ITSR target oracle.  The target counts of the other reductions do not depend on `qs`
and are the caps of their games.  No running-time statement. -/
theorem standard_model_resources (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (pkSeedDist : ProbComp prims.PkSeed)
    (A : SignatureAlg.UnforgeableAdversary (internalAlg vp prims optRand pkSeedDist)) (qs : ℕ)
    (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs) :
    IsQueryBoundP (bPrf A) (fun i => i.isRight = true)
        (2 ^ vp.params.hp * vp.params.len + qs * Reduction.signReads vp) ∧
      IsQueryBoundP (bPrfMsg A) (fun i => i.isRight = true) qs ∧
      IsQueryBoundP (bItsr A).main (fun i => i.isRight = true) qs :=
  (Reduction.slhdsa_euf_cma_resources Reduction.structural_128s A qs hA).2

end E2E

#print axioms E2E.scheme_eq
#print axioms E2E.standard_model_security
#print axioms E2E.standard_model_resources
