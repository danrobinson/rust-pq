import HashSig.SLHDSA.Security.RomConformance
import HashSig.SLHDSA.Security.SecretTraces
import HashSig.SLHDSA.Security.WotsWitnesses
import HashSig.SLHDSA.Security.TargetCounts
import HashSig.SLHDSA.Security.ReachableTargets
import HashSig.SLHDSA.Security.KeyDiscipline
import VCVio.CryptoFoundations.PRF
import VCVio.CryptoFoundations.HardnessAssumptions.KeyedHash.ITSR
import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTTCR
import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTPRE
import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTUD
import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTOpenPREFinalValidity

/-!
# Standard-model reduction for SLH-DSA: primitive families and named games

This file fixes, once and for all, the *hash-function games* that appear on the right-hand side of
the final theorem (`Reduction.Main`).  Every game is a VCVio game instantiated at the scheme's own
functions `prims.PRF`, `prims.PRFmsg`, `prims.Hmsg`, `prims.Thash`; nothing is idealised.

Paper references: HK22 = Hülsing–Kudinov, ePrint 2022/346; BDHMS = Barbosa et al., ePrint 2024/910
(EasyCrypt artefact `proofs/*.ec`).

| here | VCVio game | paper |
|---|---|---|
| `skPrf` + `PRFScheme.prfAdvantage` | `VCVio.CryptoFoundations.PRF` | HK22 §2 (PRF), EC `SKG_PRF` |
| `msgPrf` + `prfAdvantage` | same | EC `MKG_PRF` |
| `itsrProblem` + `ITSRAdvantage` | `KeyedHash.ITSR` | HK22 Def. 9 (ITSR), EC `MCO_ITSR` |
| `tcrProblem` + `SM_DT_TCR_Advantage` | `TweakableHash.SMDTTCR` | HK22 Def. 2/7 (SM-TCR), EC `SM_DT_TCR_C` |
| `forsOpenPreProblem` + `…OpenPRE….advantage` | `SMDTOpenPREFinalValidity` | BDHMS Fig. 10/11, EC `FP_OpenPRE` |
| `wotsUdProblem` + `SM_DT_UD_Advantage` | `TweakableHash.SMDTUD` | HK22 Def. 4/7 (SM-UD), EC `FC_UD` |
| `wotsPreProblem` + `SM_DT_PRE_Advantage` | `TweakableHash.SMDTPRE` | HK22 Def. 3/7 (SM-PRE), EC `FC_PRE` |
| `wotsTcrProblem` + `SM_DT_TCR_Advantage` | `TweakableHash.SMDTTCR` | EC `FC_TCR` |

Deviations from the paper, all documented at the definitions:
* one SM-TCR game on the *whole* variable-arity `Thash` (message type `List Y`) replaces the
  paper's separate SM-TCR games for FORS `H`, FORS `T_k`, WOTS `T_len`, XMSS `H` (phase 1 only:
  split into per-function games on `F`, `H`, `T_len`, `T_k` in `Reduction/HeadlineSplit.lean`);
* the public seed is drawn from the scheme's `pkSeedDist` (not necessarily uniform);
* FORS leaves use SM-DT-OpenPRE directly (BDHMS's intermediate notion); the further reduction
  OpenPRE ≤ 3·TCR + DSPR is proved in `Reduction/ForsTight.lean` (phase 2) and used in
  `Reduction/Headline.lean`;
* all SM target caps are whole-structure counts (`2^h·k·2^a`, `#inst·len`, `#inst·len·w`,
  `tcrTargets`), exponential in `h`; an adversary that uses its cap is not feasible.  See
  `Reduction/Resources.lean` (caps equal to the proved usage: `Reduction/TightCaps.lean`);
* the PRF game `skPrf` below has the oracle domain all of `Adrs`; it is false for the SHA-2
  bundle (`skPrf_broken_128s`).  The final theorems use `skPrfC` (`Reduction/PrfDomain.lean`).
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security

namespace Reduction

variable (vp : ValidatedParams) (prims : Primitives vp.params)

/-! ## Standing assumptions on the carrier types -/

/-- Structural (non-cryptographic) side conditions on the primitive bundle used throughout.
* `byteLaws`: the node encoding is injective (needed for the WOTS+ checksum argument);
* `keyInj`: the address encoding is injective on in-range addresses (needed for distinct tweaks);
* `bounds`: the parameter set's address fields fit the FIPS 205 widths. -/
structure Structural : Prop where
  byteLaws : prims.core.ByteLaws
  keyInj : CorePrimitives.KeyInjective vp prims.core
  bounds : CanonicalAddressBounds vp.params

/-! ## Tweakable-hash families -/

/-- The whole public collection `Thash` as ONE tweakable hash with message type `List Y`
(`F`, `H`, `T_len`, `T_k` are its restrictions to lists of length `1`, `2`, `len`, `k`).
Seed distribution: the scheme's own `pkSeedDist`. -/
def thashList (pkSeedDist : ProbComp prims.PkSeed) :
    TweakableHash prims.PkSeed prims.AdrsKey (List prims.Y) prims.Y where
  seedGen := pkSeedDist
  eval := prims.Thash

/-- `F = Thash` at arity one. -/
def fHash (pkSeedDist : ProbComp prims.PkSeed) :
    TweakableHash prims.PkSeed prims.AdrsKey prims.Y prims.Y where
  seedGen := pkSeedDist
  eval := fun pk t x => prims.Thash pk t [x]

/-- The collection handed to reductions while the seed is hidden: the whole `Thash`. -/
def thashColl : TweakableHashCollection Unit prims.PkSeed prims.AdrsKey prims.Y where
  Msg := fun _ => List prims.Y
  eval := fun _ => prims.Thash

/-! ## PRFs -/

/-- `PRF(PK.seed, SK.seed, ADRS)` keyed by `SK.seed`; the input is `(PK.seed, ADRS)`. -/
def skPrf [SampleableType prims.SkSeed] :
    PRFScheme prims.SkSeed (prims.PkSeed × Adrs) prims.Y where
  keygen := $ᵗ prims.SkSeed
  eval := fun k d => prims.PRF d.1 k d.2

/-- `PRF_msg(SK.prf, opt_rand, M)` keyed by `SK.prf` (VCVio's `msgPrfScheme`). -/
abbrev msgPrf [SampleableType prims.SkPrf] :
    PRFScheme prims.SkPrf (prims.Y × List Byte) prims.Y :=
  SLHDSA.msgPrfScheme prims

/-! ## ITSR for `H_msg` -/

/-- The FORS leaves a digest opens: `(FORS instance address, global leaf index)` for each of the
`k` trees. -/
def forsIndices (parts : DigestParts vp.params) : List (Adrs × ℕ) :=
  (List.range vp.params.k).map fun i =>
    (parts.forsAdrs, i * 2 ^ vp.params.a + forsIdx vp.params parts.md.toList i)

/-- `H_msg` keyed by the randomizer `R` (uniform), on inputs `(PK.seed, PK.root, M)`. -/
def hmsgFamily [SampleableType prims.Y] :
    CollisionResistance.KeyedHashFamily prims.Y (prims.PkSeed × prims.Y × List Byte)
      (Bytes vp.params.m) where
  keygen := $ᵗ prims.Y
  hash := fun R x => prims.Hmsg R x.1 x.2.1 x.2.2

/-- ITSR (HK22 Def. 9) for `H_msg`, with the FORS index map of FIPS 205. -/
def itsrProblem [SampleableType prims.Y] :
    KeyedHash.ITSRProblem prims.Y (prims.PkSeed × prims.Y × List Byte) (Bytes vp.params.m)
      (Adrs × ℕ) where
  khf := hmsgFamily vp prims
  indices := fun d => forsIndices vp (splitDigest vp.params d)

/-! ## Target counts -/

/-- Number of targets of the top-level SM-TCR game: every tweakable-hash call of the honest
structure (the union ledger `constructionAddresses`); closed form `Resources.tcrTargets_eq`,
`≈ 2^79.81` at 128s. -/
def tcrTargets : ℕ := (constructionAddresses vp).length

/-- FORS leaves: `2^h · k · 2^a`. -/
def openPreTargets : ℕ := targetCount vp.params .forsF

/-- One target per WOTS+ chain: `#instances · len`. -/
def wotsChainTargets : ℕ := targetCount vp.params .wotsFPre

/-- Cap of SM-TCR on `F`: `#instances · len · w` (the literature's cap; the chains have only
`#instances · len · (w − 1)` steps, which is what `rTcr` issues at most,
`Resources.rTcr_targets_le`). -/
def wotsStepTargets : ℕ := targetCount vp.params .wotsFTcr

/-! ## The named problems -/

/-- Top-level SM-TCR on `Thash` (stand-alone = no collection oracle: every hash evaluation the
adversary needs before the seed is revealed must be a target). -/
def tcrProblem (pkSeedDist : ProbComp prims.PkSeed) :
    TweakableHash.SM_DT_TCR_Problem Empty prims.PkSeed prims.AdrsKey (List prims.Y) prims.Y :=
  .standalone (thashList vp prims pkSeedDist) (tcrTargets vp)

/-- SM-DT-OpenPRE on `F` for the FORS leaves, uniform hidden inputs. -/
def forsOpenPreProblem [SampleableType prims.Y] (pkSeedDist : ProbComp prims.PkSeed) :
    TweakableHash.SM_DT_OpenPRE_SourceFinalValidity.Problem Empty prims.PkSeed prims.AdrsKey
      prims.Y prims.Y :=
  .standalone (fHash vp prims pkSeedDist) ($ᵗ prims.Y) (openPreTargets vp)

/-- SM-UD on `F` for the WOTS+ chains, with `Thash` as collection. -/
def wotsUdProblem [SampleableType prims.Y] (pkSeedDist : ProbComp prims.PkSeed) :
    TweakableHash.SM_DT_UD_Problem Unit prims.PkSeed prims.AdrsKey prims.Y prims.Y prims.Y where
  th := fHash vp prims pkSeedDist
  emb := id
  emb_injective := Function.injective_id
  inputGen := $ᵗ prims.Y
  outputGen := $ᵗ prims.Y
  thColl := thashColl vp prims
  numTargets := wotsChainTargets vp

/-- SM-PRE on `F` for the WOTS+ chains, with `Thash` as collection. -/
def wotsPreProblem (pkSeedDist : ProbComp prims.PkSeed) :
    TweakableHash.SM_DT_PRE_Problem Unit prims.PkSeed prims.AdrsKey prims.Y prims.Y prims.Y where
  th := fHash vp prims pkSeedDist
  emb := id
  emb_injective := Function.injective_id
  thColl := thashColl vp prims
  numTargets := wotsChainTargets vp

/-- SM-TCR on `F` for the WOTS+ chain steps, with `Thash` as collection. -/
def wotsTcrProblem (pkSeedDist : ProbComp prims.PkSeed) :
    TweakableHash.SM_DT_TCR_Problem Unit prims.PkSeed prims.AdrsKey prims.Y prims.Y where
  th := fHash vp prims pkSeedDist
  thColl := thashColl vp prims
  numTargets := wotsStepTargets vp

end Reduction
