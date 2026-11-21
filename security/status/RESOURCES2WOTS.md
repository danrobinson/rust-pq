# Resources2Wots — own hash evaluations of phase 2 of rUd / rPre / rTcr at bWotsS A

File: `Reduction/Resources2Wots.lean` (namespace `Reduction.Resources2`, all names prefixed `wots`).
Checks with `lake env lean Reduction/Resources2Wots.lean`; no sorry; axioms ⊆ propext, Classical.choice,
Quot.sound; olean written. No existing file edited.

Notation: `tI tbl := Lazy.tblImpl (PublicHash.impl prims) tbl`, `M := OracleComp (Lazy.OSpec prims gspec)`
(any `gspec`), `hA : ∀ pk, IsQueryBoundP (A.main pk) (·.isRight = true) qs`.

## Proved
- `wotsSignFromHistO hist pk msg R : M Sig`; `wotsSignFromHistO_tbl : simulateQ (tI tbl) (wotsSignFromHistO hist pk msg R) = pure (signFromHist tbl hist pk msg R)` (H_msg is an `hmsg` query).
- `wots_runForgerLog_pure_eq_liftM_g2RunWith : runForgerLog (spec := spec) A pk lazyRandomizerLift (fun m R => pure (signR m R)) = liftM (g2RunWith A pk signR)` (generic `spec`, `signR`); `wots_runForgerLog_tbl` (generic-`gspec` copy of `Lazy.runForgerLog_tbl`).
- `wotsForgeOpen A hist root pkSeed := runForgerLog A ⟨pkSeed, root⟩ lazyRandomizerLift (wotsSignFromHistO hist ⟨pkSeed, root⟩)`; `wotsForgeOpen_tbl : simulateQ (tI tbl) (wotsForgeOpen …) = liftM (g2RunWith A ⟨pkSeed, root⟩ (signFromHist tbl hist ⟨pkSeed, root⟩))`.
- `wotsForgeOpen_kindBound` (any kind ≠ unif, budget `qs * wotsSignHistB vp (ind K .sec) (ind K .hash)`),
  `wotsForgeOpen_hashes` (`.hash ≤ qs * wotsSignHistHashes vp`), `wotsForgeOpen_reads` (`.sec ≤ qs * (k * 2^a)`), `wotsForgeOpen_game` (`.game ≤ 0`).
  `wotsSignHistHashes vp = 1 + k*(2^a*2) + d*(2^h'*2)`; `wotsSignHistHashes_128s : … = 121857`.
- Tails as open programs with `_tbl` (= `pure` of pure tail) and `_kindBound`: `wotsWinO` (`WotsGame.win`), `wotsPreAnswerO` (`preAnswer`), `wotsTcrAnswerO` (`tcrAnswer`); closed forms `wotsWinHashes = len*(w-1)` (525), `wotsPreHashes = len*((w-1)+1)` (560), `wotsTcrHashes = len*((w-1)*(2*(w-1)+2))` (16800); `_128s` lemmas.
- `rfl` shapes: `wots_rUd_distinguish_eq`, `wots_rPre_invert_eq`, `wots_rTcr_forge_eq` (generic `W`), `wots_bWotsWith_forge_eq`.
- `wotsPhase2O A tbl hist root pk tail := wotsForgeOpen … >>= fun r => tail (wotsAnswer tbl hist ⟨pk, root⟩ r.1.1 r.1.2)`; `wotsPhase2O_tbl`, `wotsPhase2O_kindBound`, `wotsPhase2O_game`.
- `wots_bWotsWith_forge_open`, `wots_bWotsS_forge_open : liftM ((bWotsS A).forge (tbl, hist, root) pk) = simulateQ (tI tbl) (wotsForgeOpen A hist root pk >>= fun r => pure (wotsAnswer …))`.
- `wots_r{Ud,Pre,Tcr}_phase2_eq` (sampler `my`) and `wots_r{Ud,Pre,Tcr}_bWotsS_phase2_eq`:
  `liftM ((rX pkSeedDist (bWotsS A)).phase2 ((tbl, hist, root), hist2) pk) = simulateQ (tI tbl) (wotsPhase2O A tbl hist root pk (tailO pk hist2 …))`.
- `wots_r{Ud,Pre,Tcr}_phase2_hashes`: `.hash ≤ qs * wotsSignHistHashes vp + wots{Win,Pre,Tcr}Hashes vp`.

## Not counted formally (argued only; see module doc)
- `wotsAnswer` stays pure inside `wotsPhase2O`: ≤ 1 + wotsSignHistHashes + 2(k(1+a)+1) + 2d(len(w-1)+1+h') with memoised layer messages (129714 at 128s); literally as written the last term ×(d+1).
- uniform-bit queries and the forger's own computation.
