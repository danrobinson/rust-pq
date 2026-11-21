/-
# Work package OPEN, item R6: one bundle for the adversaries of the linear headline

For EACH adversary of the linear headline (EUF and SUF; `status/FINAL3.md` §2, `status/W7.md`)
and a forger `A` with at most `qs` signing queries, `Open.FinalResourcesOpen A qs` collects

* the open program (every `Thash`/`H_msg` evaluation, and for the PRF distinguishers every
  `PRF_msg` evaluation, is an oracle query);
* the equation of the adversary (or of its second phase) with the interpretation of the open
  program;
* the per-run bound on the hash queries of the open program, in `qs`;
* where delivered: the open program / the first phase is the same term when `Thash`, `H_msg` are
  replaced by arbitrary functions (`Open.withTH`, `Open.castForger`).

| adversary | open program | equation | hash count |
|---|---|---|---|
| `bPrfC A` / `bPrfWC sufCheck A` | `bPrfCOpen A` / `bPrfWCOpen sufCheckOpen A` | `closeImpl` | `keygenHashes + qs·signHashes + (1 + verifyHashes)` |
| `Lazy.bPrfMsgL A` / `Lazy.bPrfMsgWL sufCheck A` | `msgOpenV A` / `msgOpenWV sufCheckO A` | `lazyRun` | the same |
| `Lazy.bItsrL A` | `Lazy.itsrOpen A` | `lazyRun` (`rfl`) | `keygenHashes + qs·signHashes` |
| `toDspr`/`toTcr (Lazy.bOpenPreS A)` | `forsFindOpen optRand A.main pk ys` | `forsRun`, then `forsDsprPost`/`forsTcrPost` | `keygenHashes + qs·forsSignHashes + (1 + qs + k)` |
| `bTcrArM n A` (all `n`; headline `1, 2, len, k`) | `tcrMOpen optRand gspec A.main L pk` | `tblImpl`, then `classOut` | `keygenHashes + qs·signHashes + (1 + 2·verifyHashes)` |
| `rUd`/`rPre`/`rTcrT pkSeedDist (Lazy.bWotsS A)` | `wotsUdOpenAll`/`wotsPreOpenAll`/`wotsTcrOpenAll` | `tblImpl` | `qs·wotsSignHistHashes + (wotsAnswerHashes + wotsWin/Pre/TcrHashes)` |

All fields quote the delivered lemmas of `Reduction/Open/*.lean` unchanged; the only new proof is
the closed form of the hash/secret counts of `Lazy.itsrOpen` (from `Lazy.itsrOpen_kindBound`).
No `Structural` hypothesis is needed.

**IMPORT PRECONDITION (open at hand-over).**  The delivered package files cannot all be imported
together: four constants are declared twice — `Reduction.Open.hashEmb` (`HSpec`, `MsgV`),
`Reduction.Open.emb` (`MsgV`, `TcrStoreCover`), `Reduction.Open.ForgerProg` (`Fors`, `Tcr`),
`Reduction.Open.tcrPhase1` (`Phase1Tcr`, `Phase1Wots`).  This file therefore does NOT compile
against the tree as delivered (`import … failed, environment already contains …`).  It compiles
with no error or warning, and all `#print axioms` below give `[propext, Classical.choice,
Quot.sound]`, once the renaming patch `status/OPEN-rename.patch` is applied (in `MsgV.lean`:
`hashEmb → hashEmbR`, `emb → embR`; in `Tcr.lean`: `ForgerProg → TcrForgerProg`; in
`Phase1Wots.lean`: `tcrPhase1 → wotsTcrPhase1`) — checked against patched copies outside the
tree.  This file names none of the four constants, so any other renaming works as well.

Not in the bundle (see `status/OPEN.md`): the collection
and sample counts of `WotsCounts*.lean`, the wrappers (`Wrappers.lean`), the `withHash` forms of
the first phases, the answer-storing variant (`TcrStore*.lean`).
-/
import Reduction.Open.HSpec
import Reduction.Open.Prf
import Reduction.Open.MsgV
import Reduction.Open.Fors
import Reduction.Open.Tcr
import Reduction.Open.Wots
import Reduction.Open.WotsCounts
import Reduction.Open.WotsCountsSM
import Reduction.Open.WotsCountsSamples
import Reduction.Open.Phase1Fors
import Reduction.Open.Phase1Tcr
import Reduction.Open.Phase1Wots
import Reduction.Open.Wrappers
import Reduction.Open.TcrStore
import Reduction.Open.TcrStoreHeadline
import Reduction.Open.TcrStoreCount
import Reduction.Open.TcrStoreCover
import Reduction.Open.WithHash
import Reduction.ResourcesFinal

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal TweakableHash

namespace Reduction
namespace Open

open Resources2

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

section

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]
variable {optRand : PublicKeyCore prims.core → ProbComp prims.Y}
  {pkSeedDist : ProbComp prims.PkSeed}

attribute [local irreducible] arityTargets tcrTargets

/-! ## Closed-form counts of `Lazy.itsrOpen` (the lemmas of `ItsrLazy.lean` are stated for
`lazyRes (itsrOpen A)`; these are the same bounds for the open program itself) -/

theorem itsrOpen_hashes (A : Forger vp prims optRand pkSeedDist) (qs : ℕ)
    (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs) :
    IsQueryBoundP (Lazy.itsrOpen A) (fun t => Lazy.kind t = .hash)
      (Lazy.keygenHashes vp + qs * Lazy.signHashes vp) :=
  (Lazy.itsrOpen_kindBound A .hash (by decide) qs hA).mono
    (Nat.add_le_add Lazy.keygenB_hash (Nat.mul_le_mul_left _ (by
      simpa [Lazy.ind] using Lazy.signB_hash (vp := vp))))

theorem itsrOpen_game (A : Forger vp prims optRand pkSeedDist) (qs : ℕ)
    (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs) :
    IsQueryBoundP (Lazy.itsrOpen A) (fun t => Lazy.kind t = .game) qs :=
  (Lazy.itsrOpen_kindBound A .game (by decide) qs hA).mono
    (by simp [Lazy.ind, Lazy.keygenB_game, Lazy.signB_game])

theorem itsrOpen_sec (A : Forger vp prims optRand pkSeedDist) (qs : ℕ)
    (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs) :
    IsQueryBoundP (Lazy.itsrOpen A) (fun t => Lazy.kind t = .sec)
      (2 ^ vp.params.hp * vp.params.len + qs * signReads vp) :=
  (Lazy.itsrOpen_kindBound A .sec (by decide) qs hA).mono
    (Nat.add_le_add Lazy.keygenB_sec (Nat.mul_le_mul_left _ (by
      simpa [Lazy.ind] using Lazy.signB_sec (vp := vp))))

/-! ## The bundle -/

/-- **R6: open programs, equations and hash-query counts of all adversaries of the linear
headline**, for a forger `A` with at most `qs` signing queries.  See the file header. -/
structure FinalResourcesOpen (A : Forger vp prims optRand pkSeedDist) (qs : ℕ) : Prop where
  -- ### PRF distinguishers `bPrfC A` (EUF), `bPrfWC sufCheck A` (SUF)
  prf_euf_eq : simulateQ (closeImpl prims (prims.PkSeed × SkAdrs vp)) (bPrfCOpen A) = bPrfC A
  prf_suf_eq : simulateQ (closeImpl prims (prims.PkSeed × SkAdrs vp))
      (bPrfWCOpen sufCheckOpen A) = bPrfWC sufCheck A
  prf_euf_hashes : IsQueryBoundP (bPrfCOpen A) (fun t => hkind t = .hash)
    (Lazy.keygenHashes vp + qs * Lazy.signHashes vp + (1 + Resources2.verifyHashes vp))
  prf_euf_prfmsg : IsQueryBoundP (bPrfCOpen A) (fun t => hkind t = .prfmsg) qs
  prf_euf_game : IsQueryBoundP (bPrfCOpen A) (fun t => hkind t = .game)
    (2 ^ vp.params.hp * vp.params.len + qs * signReads vp)
  prf_suf_hashes : IsQueryBoundP (bPrfWCOpen sufCheckOpen A) (fun t => hkind t = .hash)
    (Lazy.keygenHashes vp + qs * Lazy.signHashes vp + (1 + Resources2.verifyHashes vp))
  prf_suf_prfmsg : IsQueryBoundP (bPrfWCOpen sufCheckOpen A) (fun t => hkind t = .prfmsg) qs
  prf_suf_game : IsQueryBoundP (bPrfWCOpen sufCheckOpen A) (fun t => hkind t = .game)
    (2 ^ vp.params.hp * vp.params.len + qs * signReads vp)
  -- ### `PRF_msg` distinguishers `Lazy.bPrfMsgL A` (EUF), `Lazy.bPrfMsgWL sufCheck A` (SUF)
  msg_euf_eq : Lazy.lazyRun (PublicHash.impl prims) (msgOpenV A) = Lazy.bPrfMsgL A
  msg_suf_eq : Lazy.lazyRun (PublicHash.impl prims) (msgOpenWV sufCheckO A) =
    Lazy.bPrfMsgWL sufCheck A
  msg_euf_hashes : IsQueryBoundP (msgOpenV A) (fun t => Lazy.kind t = .hash)
    (Lazy.keygenHashes vp + qs * Lazy.signHashes vp + (1 + Resources2.verifyHashes vp))
  msg_euf_game : IsQueryBoundP (msgOpenV A) (fun t => Lazy.kind t = .game) qs
  msg_euf_sec : IsQueryBoundP (msgOpenV A) (fun t => Lazy.kind t = .sec)
    (2 ^ vp.params.hp * vp.params.len + qs * signReads vp)
  msg_suf_hashes : IsQueryBoundP (msgOpenWV sufCheckO A) (fun t => Lazy.kind t = .hash)
    (Lazy.keygenHashes vp + qs * Lazy.signHashes vp + (1 + Resources2.verifyHashes vp))
  msg_suf_game : IsQueryBoundP (msgOpenWV sufCheckO A) (fun t => Lazy.kind t = .game) qs
  msg_suf_sec : IsQueryBoundP (msgOpenWV sufCheckO A) (fun t => Lazy.kind t = .sec)
    (2 ^ vp.params.hp * vp.params.len + qs * signReads vp)
  /-- For every `T`, `H`: the distinguisher over `withTH prims T H` is the ONE open program
  (over `prims`) with hash queries answered by `T`, `H`. -/
  msg_euf_uniform : ∀ (T : prims.PkSeed → prims.AdrsKey → List prims.Y → prims.Y)
      (H : prims.Y → prims.PkSeed → prims.Y → List Byte → Bytes vp.params.m),
    Lazy.bPrfMsgL (prims := withTH prims T H) (castForger T H A) =
      Lazy.lazyRun (PublicHash.impl (withTH prims T H)) (msgOpenV (prims := prims) A)
  msg_suf_uniform : ∀ (T : prims.PkSeed → prims.AdrsKey → List prims.Y → prims.Y)
      (H : prims.Y → prims.PkSeed → prims.Y → List Byte → Bytes vp.params.m),
    Lazy.bPrfMsgWL (prims := withTH prims T H) sufCheck (castForger T H A) =
      Lazy.lazyRun (PublicHash.impl (withTH prims T H)) (msgOpenWV (prims := prims) sufCheckO A)
  -- ### ITSR adversary `Lazy.bItsrL A` (no final check)
  itsr_eq : (Lazy.bItsrL A).main = Lazy.lazyRun (PublicHash.impl prims) (Lazy.itsrOpen A)
  itsr_hashes : IsQueryBoundP (Lazy.itsrOpen A) (fun t => Lazy.kind t = .hash)
    (Lazy.keygenHashes vp + qs * Lazy.signHashes vp)
  itsr_game : IsQueryBoundP (Lazy.itsrOpen A) (fun t => Lazy.kind t = .game) qs
  itsr_sec : IsQueryBoundP (Lazy.itsrOpen A) (fun t => Lazy.kind t = .sec)
    (2 ^ vp.params.hp * vp.params.len + qs * signReads vp)
  itsr_uniform : ∀ (T : prims.PkSeed → prims.AdrsKey → List prims.Y → prims.Y)
      (H : prims.Y → prims.PkSeed → prims.Y → List Byte → Bytes vp.params.m),
    (Lazy.bItsrL (prims := withTH prims T H) (castForger T H A)).main =
      Lazy.lazyRun (PublicHash.impl (withTH prims T H)) (Lazy.itsrOpen (prims := prims) A)
  -- ### FORS adversaries `toDspr (Lazy.bOpenPreS A)`, `toTcr (Lazy.bOpenPreS A)`
  fors_dspr_eq : ∀ (tbl : SecretTable vp prims) (tg : List (prims.AdrsKey × prims.Y))
      (ys : List prims.Y) (pk : prims.PkSeed),
    (toDspr (Lazy.bOpenPreS A)).guess (tbl, tg, ys) pk =
      forsRun (PublicHash.impl prims) tbl tg (forsFindOpen optRand A.main pk ys) >>=
        fun z => pure (forsDsprPost tg z)
  fors_tcr_eq : ∀ (tbl : SecretTable vp prims) (tg : List (prims.AdrsKey × prims.Y))
      (ys : List prims.Y) (pk : prims.PkSeed),
    (toTcr (Lazy.bOpenPreS A)).forge (tbl, tg, ys) pk =
      forsRun (PublicHash.impl prims) tbl tg (forsFindOpen optRand A.main pk ys) >>=
        fun z => pure (forsTcrPost z)
  /-- One open program for both; its hash queries. -/
  fors_hashes : ∀ (pk : prims.PkSeed) (ys : List prims.Y),
    IsQueryBoundP (forsFindOpen optRand A.main pk ys) (fun t => Lazy.kind t = .hash)
      (Lazy.keygenHashes vp + qs * forsSignHashes vp + (1 + qs + vp.params.k))
  /-- The open program is the same term for every `Thash`/`H_msg`. -/
  fors_open_hashfree : ∀ (T : prims.PkSeed → prims.AdrsKey → List prims.Y → prims.Y)
      (H : prims.Y → prims.PkSeed → prims.Y → List Byte → Bytes vp.params.m)
      (pk : prims.PkSeed) (ys : List prims.Y),
    forsFindOpen (prims := withTH prims T H) optRand A.main pk ys =
      forsFindOpen (prims := prims) optRand A.main pk ys
  /-- First phases do no hashing of their own. -/
  fors_dspr_phase1 : ∀ (T : prims.PkSeed → prims.AdrsKey → List prims.Y → prims.Y)
      (H : prims.Y → prims.PkSeed → prims.Y → List Byte → Bytes vp.params.m),
    ((toDspr (Lazy.bOpenPreS (castForger T H A))).choose :
        OracleComp (ForsP1Spec prims) (ForsP1State vp prims)) =
      (toDspr (Lazy.bOpenPreS A)).choose
  fors_tcr_phase1 : ∀ (T : prims.PkSeed → prims.AdrsKey → List prims.Y → prims.Y)
      (H : prims.Y → prims.PkSeed → prims.Y → List Byte → Bytes vp.params.m),
    ((toTcr (Lazy.bOpenPreS (castForger T H A))).choose :
        OracleComp (ForsP1Spec prims) (ForsP1State vp prims)) =
      (toTcr (Lazy.bOpenPreS A)).choose
  -- ### Class SM-TCR adversaries `bTcrArM n A` (every `n`; the headline uses `1, 2, len, k`)
  tcr_eq : ∀ {ι : Type} (gspec : OracleSpec ι) (n : ℕ) (tbl : SecretTable vp prims)
      (L : List (prims.AdrsKey × List prims.Y)) (pk : prims.PkSeed),
    (liftM ((bTcrArM n A).forge (tbl, L) pk) : OracleComp (unifSpec + gspec) _) =
      simulateQ (Lazy.tblImpl (gspec := gspec) (PublicHash.impl prims) tbl)
          (tcrMOpen optRand gspec A.main L pk) >>= fun jm => pure (classOut prims n L jm)
  tcr_hashes : ∀ {ι : Type} (gspec : OracleSpec ι) (L : List (prims.AdrsKey × List prims.Y))
      (pk : prims.PkSeed),
    IsQueryBoundP (tcrMOpen optRand gspec A.main L pk) (fun t => Lazy.kind t = .hash)
      (Lazy.keygenHashes vp + qs * Lazy.signHashes vp + (1 + Resources2.verifyHashes vp * 2))
  /-- For every `T`, `H`: ONE open program and ONE post-processing (over `prims`). -/
  tcr_uniform : ∀ {ι : Type} (gspec : OracleSpec ι)
      (T : prims.PkSeed → prims.AdrsKey → List prims.Y → prims.Y)
      (H : prims.Y → prims.PkSeed → prims.Y → List Byte → Bytes vp.params.m)
      (n : ℕ) (tbl : SecretTable vp prims) (L : List (prims.AdrsKey × List prims.Y))
      (pk : prims.PkSeed),
    (liftM ((bTcrArM n (castForger T H A)).forge (tbl, L) pk) :
        OracleComp (unifSpec + gspec) _) =
      simulateQ (Lazy.tblImpl (gspec := gspec) (PublicHash.impl (withTH prims T H)) tbl)
          (tcrMOpen optRand gspec A.main L pk) >>= fun jm => pure (classOut prims n L jm)
  /-- First phase: no hashing of its own (its collection-oracle queries are the game's). -/
  tcr_phase1 : ∀ (T : prims.PkSeed → prims.AdrsKey → List prims.Y → prims.Y)
      (H : prims.Y → prims.PkSeed → prims.Y → List Byte → Bytes vp.params.m) (n : ℕ),
    ((bTcrArM n (castForger T H A)).choose :
        OracleComp (TcrP1Spec prims n) (TcrP1State vp prims)) =
      (bTcrArM n A).choose
  -- ### WOTS adversaries `rUd`, `rPre`, `rTcrT` at `Lazy.bWotsS A`
  wots_ud_eq : ∀ {ι : Type} (gspec : OracleSpec ι) (tbl : SecretTable vp prims)
      (hist hist2 : List (WotsGame.Entry prims)) (root : prims.Y) (pk : prims.PkSeed),
    (liftM ((rUd pkSeedDist (Lazy.bWotsS A)).distinguish ((tbl, hist, root), hist2) pk) :
        OracleComp (unifSpec + gspec) Bool) =
      simulateQ (Lazy.tblImpl (gspec := gspec) (PublicHash.impl prims) tbl)
        (wotsUdOpenAll A hist hist2 root pk)
  wots_pre_eq : ∀ {ι : Type} (gspec : OracleSpec ι) (tbl : SecretTable vp prims)
      (hist hist2 : List (WotsGame.Entry prims)) (root : prims.Y) (pk : prims.PkSeed),
    (liftM ((rPre pkSeedDist (Lazy.bWotsS A)).invert ((tbl, hist, root), hist2) pk) :
        OracleComp (unifSpec + gspec) (ℕ × prims.Y)) =
      simulateQ (Lazy.tblImpl (gspec := gspec) (PublicHash.impl prims) tbl)
        (wotsPreOpenAll A hist hist2 root pk)
  wots_tcr_eq : ∀ {ι : Type} (gspec : OracleSpec ι) (tbl : SecretTable vp prims)
      (hist hist2 : List (WotsGame.Entry prims)) (root : prims.Y) (pk : prims.PkSeed),
    (liftM ((rTcrT (vp := vp) pkSeedDist (Lazy.bWotsS A)).forge ((tbl, hist, root), hist2) pk) :
        OracleComp (unifSpec + gspec) (ℕ × prims.Y)) =
      simulateQ (Lazy.tblImpl (gspec := gspec) (PublicHash.impl prims) tbl)
        (wotsTcrOpenAll A hist hist2 root pk)
  wots_ud_hashes : ∀ {ι : Type} (gspec : OracleSpec ι)
      (hist hist2 : List (WotsGame.Entry prims)) (root : prims.Y) (pk : prims.PkSeed),
    IsQueryBoundP (wotsUdOpenAll (gspec := gspec) A hist hist2 root pk)
      (fun t => Lazy.kind t = .hash)
      (qs * wotsSignHistHashes vp + (wotsAnswerHashes vp + wotsWinHashes vp))
  wots_pre_hashes : ∀ {ι : Type} (gspec : OracleSpec ι)
      (hist hist2 : List (WotsGame.Entry prims)) (root : prims.Y) (pk : prims.PkSeed),
    IsQueryBoundP (wotsPreOpenAll (gspec := gspec) A hist hist2 root pk)
      (fun t => Lazy.kind t = .hash)
      (qs * wotsSignHistHashes vp + (wotsAnswerHashes vp + wotsPreHashes vp))
  wots_tcr_hashes : ∀ {ι : Type} (gspec : OracleSpec ι)
      (hist hist2 : List (WotsGame.Entry prims)) (root : prims.Y) (pk : prims.PkSeed),
    IsQueryBoundP (wotsTcrOpenAll (gspec := gspec) A hist hist2 root pk)
      (fun t => Lazy.kind t = .hash)
      (qs * wotsSignHistHashes vp + (wotsAnswerHashes vp + wotsTcrHashes vp))
  /-- The open programs are the same terms for every `Thash`/`H_msg`. -/
  wots_ud_open_hashfree : ∀ {ι : Type} (gspec : OracleSpec ι)
      (T : prims.PkSeed → prims.AdrsKey → List prims.Y → prims.Y)
      (H : prims.Y → prims.PkSeed → prims.Y → List Byte → Bytes vp.params.m)
      (hist hist2 : List (WotsGame.Entry prims)) (root : prims.Y) (pk : prims.PkSeed),
    wotsUdOpenAll (prims := withTH prims T H) (gspec := gspec) (castForger T H A) hist hist2
        root pk = wotsUdOpenAll (gspec := gspec) A hist hist2 root pk
  wots_pre_open_hashfree : ∀ {ι : Type} (gspec : OracleSpec ι)
      (T : prims.PkSeed → prims.AdrsKey → List prims.Y → prims.Y)
      (H : prims.Y → prims.PkSeed → prims.Y → List Byte → Bytes vp.params.m)
      (hist hist2 : List (WotsGame.Entry prims)) (root : prims.Y) (pk : prims.PkSeed),
    wotsPreOpenAll (prims := withTH prims T H) (gspec := gspec) (castForger T H A) hist hist2
        root pk = wotsPreOpenAll (gspec := gspec) A hist hist2 root pk
  wots_tcr_open_hashfree : ∀ {ι : Type} (gspec : OracleSpec ι)
      (T : prims.PkSeed → prims.AdrsKey → List prims.Y → prims.Y)
      (H : prims.Y → prims.PkSeed → prims.Y → List Byte → Bytes vp.params.m)
      (hist hist2 : List (WotsGame.Entry prims)) (root : prims.Y) (pk : prims.PkSeed),
    wotsTcrOpenAll (prims := withTH prims T H) (gspec := gspec) (castForger T H A) hist hist2
        root pk = wotsTcrOpenAll (gspec := gspec) A hist hist2 root pk
  /-- First phases do no hashing of their own (collection/challenge queries are the game's). -/
  wots_ud_phase1 : ∀ (T : prims.PkSeed → prims.AdrsKey → List prims.Y → prims.Y)
      (H : prims.Y → prims.PkSeed → prims.Y → List Byte → Bytes vp.params.m),
    @Eq (OracleComp (udSpecC prims.AdrsKey prims.Y) (RState vp prims))
      (rUd (prims := withTH prims T H) pkSeedDist (Lazy.bWotsS (castForger T H A))).pick
      (rUd pkSeedDist (Lazy.bWotsS A)).pick
  wots_pre_phase1 : ∀ (T : prims.PkSeed → prims.AdrsKey → List prims.Y → prims.Y)
      (H : prims.Y → prims.PkSeed → prims.Y → List Byte → Bytes vp.params.m),
    @Eq (OracleComp (preSpecC prims.AdrsKey prims.Y) (RState vp prims))
      (rPre (prims := withTH prims T H) pkSeedDist (Lazy.bWotsS (castForger T H A))).choose
      (rPre pkSeedDist (Lazy.bWotsS A)).choose
  wots_tcr_phase1 : ∀ (T : prims.PkSeed → prims.AdrsKey → List prims.Y → prims.Y)
      (H : prims.Y → prims.PkSeed → prims.Y → List Byte → Bytes vp.params.m),
    @Eq (OracleComp (tcrSpecC prims.AdrsKey prims.Y) (RState vp prims))
      (rTcrT (vp := vp) (prims := withTH prims T H) pkSeedDist
        (Lazy.bWotsS (castForger T H A))).choose
      (rTcrT (vp := vp) pkSeedDist (Lazy.bWotsS A)).choose

/-- **R6: the resource theorem for the open programs of the adversaries of the linear
headline.**  No hypothesis besides the bound on the forger's signing queries. -/
theorem final_resources_final_open
    (A : Forger vp prims optRand pkSeedDist) (qs : ℕ)
    (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs) :
    FinalResourcesOpen A qs where
  prf_euf_eq := bPrfCOpen_close A
  prf_suf_eq := bPrfWCOpen_close_suf A
  prf_euf_hashes := bPrfCOpen_hashes A qs hA
  prf_euf_prfmsg := bPrfCOpen_prfmsg A qs hA
  prf_euf_game := bPrfCOpen_game A qs hA
  prf_suf_hashes := bPrfWCOpen_suf_hashes A qs hA
  prf_suf_prfmsg := bPrfWCOpen_suf_prfmsg A qs hA
  prf_suf_game := bPrfWCOpen_suf_game A qs hA
  msg_euf_eq := lazyRun_msgOpenV A
  msg_suf_eq := lazyRun_msgOpenWV_sufCheck A
  msg_euf_hashes := msgOpenV_hashes A qs hA
  msg_euf_game := msgOpenV_game A qs hA
  msg_euf_sec := msgOpenV_sec A qs hA
  msg_suf_hashes := msgOpenWV_suf_hashes A qs hA
  msg_suf_game := msgOpenWV_suf_game A qs hA
  msg_suf_sec := msgOpenWV_suf_sec A qs hA
  msg_euf_uniform := fun T H => bPrfMsgL_castForger T H A
  msg_suf_uniform := fun T H => bPrfMsgWL_castForger T H A
  itsr_eq := rfl
  itsr_hashes := itsrOpen_hashes A qs hA
  itsr_game := itsrOpen_game A qs hA
  itsr_sec := itsrOpen_sec A qs hA
  itsr_uniform := fun T H => bItsrL_castForger_main T H A
  fors_dspr_eq := fun tbl tg ys pk => forsDspr_phase2_open_eq A tbl tg ys pk
  fors_tcr_eq := fun tbl tg ys pk => forsTcr_phase2_open_eq A tbl tg ys pk
  fors_hashes := fun pk ys => forsTcr_phase2_open_hashes A qs hA pk ys
  fors_open_hashfree := fun T H pk ys => forsFindOpen_withTH T H A.main pk ys
  fors_dspr_phase1 := fun T H => forsDspr_phase1_hashfree T H A
  fors_tcr_phase1 := fun T H => forsTcr_phase1_hashfree T H A
  tcr_eq := fun gspec n tbl L pk => tcrM_phase2_open_eq gspec n A tbl L pk
  tcr_hashes := fun gspec L pk => tcrM_phase2_open_hashes gspec A.main qs hA L pk
  tcr_uniform := fun gspec T H n tbl L pk => bTcrArM_phase2_open_uniform T H n A tbl L pk
  tcr_phase1 := fun T H n => tcrM_phase1_hashfree T H n A
  wots_ud_eq := fun gspec tbl hist hist2 root pk => wotsUd_phase2_open_eq A tbl hist hist2 root pk
  wots_pre_eq := fun gspec tbl hist hist2 root pk =>
    wotsPre_phase2_open_eq A tbl hist hist2 root pk
  wots_tcr_eq := fun gspec tbl hist hist2 root pk =>
    wotsTcrT_phase2_open_eq A tbl hist hist2 root pk
  wots_ud_hashes := fun gspec hist hist2 root pk =>
    wotsUd_phase2_open_hashes A qs hA hist hist2 root pk
  wots_pre_hashes := fun gspec hist hist2 root pk =>
    wotsPre_phase2_open_hashes A qs hA hist hist2 root pk
  wots_tcr_hashes := fun gspec hist hist2 root pk =>
    wotsTcrT_phase2_open_hashes A qs hA hist hist2 root pk
  wots_ud_open_hashfree := fun gspec T H hist hist2 root pk =>
    wotsUdOpenAll_hashfree T H A hist hist2 root pk
  wots_pre_open_hashfree := fun gspec T H hist hist2 root pk =>
    wotsPreOpenAll_hashfree T H A hist hist2 root pk
  wots_tcr_open_hashfree := fun gspec T H hist hist2 root pk =>
    wotsTcrOpenAll_hashfree T H A hist hist2 root pk
  wots_ud_phase1 := fun T H => wotsUd_phase1_hashfree T H A
  wots_pre_phase1 := fun T H => wotsPre_phase1_hashfree T H A
  wots_tcr_phase1 := fun T H => wotsTcrT_phase1_hashfree T H A

/-- The bundle for an external (pure-interface) forger: `toInternal A` makes at most `qs`
signing queries and the bundle holds for it (`toInternal` adds no hash query:
`Open.toInternal_main`, `Open.toInternal_open`). -/
theorem final_resources_final_open_external
    (A : ExtForger vp prims optRand pkSeedDist) (qs : ℕ)
    (hq : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs) :
    (∀ pk, IsQueryBoundP ((toInternal A).main pk) (fun i => i.isRight = true) qs) ∧
      FinalResourcesOpen (toInternal A) qs :=
  ⟨toInternal_queryBound A qs hq,
    final_resources_final_open _ qs (toInternal_queryBound A qs hq)⟩

/-- The bundle for a byte-level forger (`bytesToTyped` adds no hash query:
`Open.bytesToTyped_main`, `Open.bytesToTyped_open`). -/
theorem final_resources_final_open_bytes {codec : CoreWireCodec vp.params prims.core}
    (A : BytesForger vp prims codec optRand pkSeedDist) (qs : ℕ)
    (hq : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs) :
    (∀ pk, IsQueryBoundP ((bytesToTyped A).main pk) (fun i => i.isRight = true) qs) ∧
      FinalResourcesOpen (bytesToTyped A) qs :=
  ⟨bytesToTyped_queryBound A qs hq,
    final_resources_final_open _ qs (bytesToTyped_queryBound A qs hq)⟩

end

/-! ## SLH-DSA-SHA2-128s -/

/-- The hash-query bounds of the open programs at SLH-DSA-SHA2-128s, as numerals. -/
structure FinalResourcesOpen128s
    {optRand : PublicKeyCore Link.prims.core → ProbComp Link.prims.Y}
    {pkSeedDist : ProbComp Link.prims.PkSeed}
    (A : Forger Link.vp Link.prims optRand pkSeedDist) (qs : ℕ) : Prop where
  prf_euf : IsQueryBoundP (bPrfCOpen A) (fun t => hkind t = .hash) (269824 + qs * 2007385 + 3929)
  prf_suf : IsQueryBoundP (bPrfWCOpen sufCheckOpen A) (fun t => hkind t = .hash)
    (269824 + qs * 2007385 + 3929)
  msg_euf : IsQueryBoundP (msgOpenV A) (fun t => Lazy.kind t = .hash)
    (269824 + qs * 2007385 + 3929)
  msg_suf : IsQueryBoundP (msgOpenWV sufCheckO A) (fun t => Lazy.kind t = .hash)
    (269824 + qs * 2007385 + 3929)
  itsr : IsQueryBoundP (Lazy.itsrOpen A) (fun t => Lazy.kind t = .hash) (269824 + qs * 2007385)
  fors : ∀ (pk : Link.prims.PkSeed) (ys : List Link.prims.Y),
    IsQueryBoundP (forsFindOpen optRand A.main pk ys) (fun t => Lazy.kind t = .hash)
      (269839 + qs * 1950028)
  tcr : ∀ {ι : Type} (gspec : OracleSpec ι) (L : List (Link.prims.AdrsKey × List Link.prims.Y))
      (pk : Link.prims.PkSeed),
    IsQueryBoundP (tcrMOpen optRand gspec A.main L pk) (fun t => Lazy.kind t = .hash)
      (269824 + qs * 2007385 + 7857)
  wots_ud : ∀ {ι : Type} (gspec : OracleSpec ι) (hist hist2 : List (WotsGame.Entry Link.prims))
      (root : Link.prims.Y) (pk : Link.prims.PkSeed),
    IsQueryBoundP (wotsUdOpenAll (gspec := gspec) A hist hist2 root pk)
      (fun t => Lazy.kind t = .hash) (qs * 121857 + 130239)
  wots_pre : ∀ {ι : Type} (gspec : OracleSpec ι) (hist hist2 : List (WotsGame.Entry Link.prims))
      (root : Link.prims.Y) (pk : Link.prims.PkSeed),
    IsQueryBoundP (wotsPreOpenAll (gspec := gspec) A hist hist2 root pk)
      (fun t => Lazy.kind t = .hash) (qs * 121857 + 130274)
  wots_tcr : ∀ {ι : Type} (gspec : OracleSpec ι) (hist hist2 : List (WotsGame.Entry Link.prims))
      (root : Link.prims.Y) (pk : Link.prims.PkSeed),
    IsQueryBoundP (wotsTcrOpenAll (gspec := gspec) A hist hist2 root pk)
      (fun t => Lazy.kind t = .hash) (qs * 121857 + 146514)

/-- **R6 at SLH-DSA-SHA2-128s**: the bundle, and the hash-query bounds as numerals. -/
theorem final_resources_final_open_128s
    (optRand : PublicKeyCore Link.prims.core → ProbComp Link.prims.Y)
    (pkSeedDist : ProbComp Link.prims.PkSeed)
    (A : Forger Link.vp Link.prims optRand pkSeedDist) (qs : ℕ)
    (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs) :
    FinalResourcesOpen A qs ∧ FinalResourcesOpen128s A qs := by
  refine ⟨final_resources_final_open A qs hA, ?_⟩
  have hi := itsrOpen_hashes A qs hA
  rw [keygenHashes_128s, signHashes_128s] at hi
  exact
    { prf_euf := bPrfCOpen_hashes_128s optRand pkSeedDist A qs hA
      prf_suf := bPrfWCOpen_suf_hashes_128s optRand pkSeedDist A qs hA
      msg_euf := (msgOpenV_hashes_128s A qs hA).1
      msg_suf := (msgOpenV_hashes_128s A qs hA).2.2.1
      itsr := hi
      fors := fun pk ys => forsTcr_phase2_open_hashes_128s optRand pkSeedDist A qs hA pk ys
      tcr := fun gspec L pk => tcrM_phase2_open_hashes_128s gspec optRand A.main qs hA L pk
      wots_ud := fun gspec hist hist2 root pk =>
        wotsUd_phase2_open_hashes_128s optRand pkSeedDist A qs hA hist hist2 root pk
      wots_pre := fun gspec hist hist2 root pk =>
        wotsPre_phase2_open_hashes_128s optRand pkSeedDist A qs hA hist hist2 root pk
      wots_tcr := fun gspec hist hist2 root pk =>
        wotsTcrT_phase2_open_hashes_128s optRand pkSeedDist A qs hA hist hist2 root pk }

#print axioms itsrOpen_hashes
#print axioms final_resources_final_open
#print axioms final_resources_final_open_external
#print axioms final_resources_final_open_bytes
#print axioms final_resources_final_open_128s

end Open
end Reduction
