import Integration.SlhDsaComposedFinal
import Reduction.Open.Bundle

/-!
# The counts `openCounts128s` are the hash-query bounds of the open reduction programs

NOT part of the default target; checked by `scripts/check-integration.sh`.

`openCounts128s_sound`: for every classical forger `A` against SLH-DSA-SHA2-128s (`Link.prims`)
with at most `qs` signing queries, each open program of the reduction
(`security/Reduction/Open/`) makes at most `(openCounts128s qs).<term>` hash-kind queries.  This
is `Reduction.Open.final_resources_final_open_128s` restated with the fields of `openCounts128s`,
so the numerals of `openCounts128s` are no longer independent copies.

Scope: the statement is about the CLASSICAL open programs at the SHA-2 primitives `Link.prims`.
It is not yet used to bound the oracle calls of the quantum reduction machines at the random
primitives (stage 2(b)).
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security

namespace Reduction

open Reduction.Open in
theorem openCounts128s_sound
    (optRand : PublicKeyCore Link.prims.core → ProbComp Link.prims.Y)
    (pkSeedDist : ProbComp Link.prims.PkSeed)
    (A : Forger Link.vp Link.prims optRand pkSeedDist) (qs : ℕ)
    (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs) :
    IsQueryBoundP (bPrfCOpen A) (fun t => hkind t = .hash) (openCounts128s qs).prf ∧
    IsQueryBoundP (bPrfWCOpen sufCheckOpen A) (fun t => hkind t = .hash) (openCounts128s qs).prf ∧
    IsQueryBoundP (msgOpenV A) (fun t => Lazy.kind t = .hash) (openCounts128s qs).msg ∧
    IsQueryBoundP (msgOpenWV sufCheckO A) (fun t => Lazy.kind t = .hash) (openCounts128s qs).msg ∧
    IsQueryBoundP (Lazy.itsrOpen A) (fun t => Lazy.kind t = .hash) (openCounts128s qs).itsr ∧
    (∀ (pk : Link.prims.PkSeed) (ys : List Link.prims.Y),
      IsQueryBoundP (forsFindOpen optRand A.main pk ys) (fun t => Lazy.kind t = .hash)
        (openCounts128s qs).dspr) ∧
    (∀ {ι : Type} (gspec : OracleSpec ι) (L : List (Link.prims.AdrsKey × List Link.prims.Y))
        (pk : Link.prims.PkSeed),
      IsQueryBoundP (tcrMOpen optRand gspec A.main L pk) (fun t => Lazy.kind t = .hash)
        (openCounts128s qs).tcr1) ∧
    (∀ {ι : Type} (gspec : OracleSpec ι) (hist hist2 : List (WotsGame.Entry Link.prims))
        (root : Link.prims.Y) (pk : Link.prims.PkSeed),
      IsQueryBoundP (wotsUdOpenAll (gspec := gspec) A hist hist2 root pk)
        (fun t => Lazy.kind t = .hash) (openCounts128s qs).ud) ∧
    (∀ {ι : Type} (gspec : OracleSpec ι) (hist hist2 : List (WotsGame.Entry Link.prims))
        (root : Link.prims.Y) (pk : Link.prims.PkSeed),
      IsQueryBoundP (wotsPreOpenAll (gspec := gspec) A hist hist2 root pk)
        (fun t => Lazy.kind t = .hash) (openCounts128s qs).pre) ∧
    (∀ {ι : Type} (gspec : OracleSpec ι) (hist hist2 : List (WotsGame.Entry Link.prims))
        (root : Link.prims.Y) (pk : Link.prims.PkSeed),
      IsQueryBoundP (wotsTcrOpenAll (gspec := gspec) A hist hist2 root pk)
        (fun t => Lazy.kind t = .hash) (openCounts128s qs).tcrT) := by
  obtain ⟨-, h⟩ := final_resources_final_open_128s optRand pkSeedDist A qs hA
  exact ⟨h.prf_euf, h.prf_suf, h.msg_euf, h.msg_suf, h.itsr, h.fors, h.tcr, h.wots_ud,
    h.wots_pre, h.wots_tcr⟩

/-- The FORS counts (`dspr`, `tcrFv`) and the class-TCR counts coincide. -/
theorem openCounts128s_eq (qs : ℕ) :
    (openCounts128s qs).tcrFv = (openCounts128s qs).dspr ∧
    (openCounts128s qs).tcr2 = (openCounts128s qs).tcr1 ∧
    (openCounts128s qs).tcrLen = (openCounts128s qs).tcr1 ∧
    (openCounts128s qs).tcrK = (openCounts128s qs).tcr1 := ⟨rfl, rfl, rfl, rfl⟩

end Reduction

#print axioms Reduction.openCounts128s_sound
