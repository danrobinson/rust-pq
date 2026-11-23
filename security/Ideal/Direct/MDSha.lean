import Ideal.Direct.MDCore
import Ideal.Direct.Entry

/-!
# H1: the real SUF/EUF programs as walk programs (`status/DIRECT.md` §11)

`Entry.progS` (resp. `progE`), the table-independent compression program of the SUF (EUF)
experiment, is EXACTLY the walk program `XS` (`XE`) of `Direct/MDCore.lean` with its walks
answered by compression chains (`MD.cellsR IV128`):
```
progS S oR pkSeedDist = simulateQ (MD.cellsR IV128) (XS S oR pkSeedDist)      -- h1_suf
progE S oR pkSeedDist = simulateQ (MD.cellsR IV128) (XE S oR pkSeedDist)      -- h1_euf
```
`XS` is the open SUF program `PprfS` (the realisers' port program) with its PRF key `k` drawn
first, coins and port queries forwarded, and every hash evaluation issued as walk queries:
`Thash(pk, a, xs)` = `out16` of the walk `sb128 pk :: tblocks a xs`; `H_msg(R, pk, root, M)` =
`dig30` of the walk `oblocksH R pk s` with `s` the walk `iblocksH R pk root M`; `PRF_msg(k, r, M)`
= `out16` of the walk `[okey k, oblock s]` with `s` the walk `ikey k :: iblocks r M`; the PRF
oracle `(pk, a)` = `out16` of the walk `[sb128 pk, blk128 a k]`.

With `MD.md_core` this gives the real game as the deferred game of `XS` plus `2·Pr[Bad]`
(`suf_real_le_deferred`).
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security

namespace Ideal.Direct.Rom

open Ideal.Realize Ideal.Realize.Prf
open Ideal.Realize.Msg (Rd cEmb)

set_option linter.unusedSectionVars false

/-- The walk-program interface at SHA-256. -/
abbrev OS := MD.OSp St Blk

/-- A walk query. -/
def wQ (bs : List Blk) : OracleComp OS St := (liftM (OS.query (.inr bs)) : OracleComp OS St)

/-- `Thash` and `H_msg` as walks. -/
def hashW : QueryImpl (publicHashSpec core₀) (OracleComp OS)
  | .thash pk a xs => out16 <$> wQ (sb128 pk :: (tblocks a xs).1 :: (tblocks a xs).2)
  | .hmsg R pk root M => do
      let s ← wQ (iblocksH R pk root M)
      let s' ← wQ (oblocksH R pk s)
      pure (dig30 s')

/-- `PRF_msg` (HMAC) as walks. -/
def prfW (k r : Bytes 16) (M : List UInt8) : OracleComp OS (Bytes 16) := do
  let s ← wQ (ikey k :: iblocks r M)
  let s' ← wQ [okey k, oblock s]
  pure (out16 s')

/-- The hash interface with `PRF_msg`, as walks. -/
def hashPW : QueryImpl (Reduction.Open.HSpec Rd) (OracleComp OS)
  | .inl q => hashW q
  | .inr t => prfW t.1 t.2.1 t.2.2

/-- **The walk interpretation of a port program at the PRF key `k`.** -/
def chainW (k : Bytes 16) : QueryImpl (QSpec Rd Dsk) (OracleComp OS)
  | .inl n => (liftM (OS.query (.inl (.inl n))) : OracleComp OS _)
  | .inr (.inl (.inl q)) => (liftM (OS.query (.inl (.inr q))) : OracleComp OS _)
  | .inr (.inl (.inr d)) => (out16 <$> wQ [sb128 d.1, blk128 d.2 k] : OracleComp OS (Bytes 16))
  | .inr (.inr q) => hashPW q

/-- The walk program of a port program: draw the PRF key, interpret. -/
noncomputable def walkProg (P : OracleComp (QSpec Rd Dsk) Bool) : OracleComp OS Bool := do
  let k ← (liftM ($ᵗ (Bytes 16) : ProbComp (Bytes 16)) : OracleComp OS (Bytes 16))
  simulateQ (chainW k) P

/-- **The SUF walk program.** -/
noncomputable def XS (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    (pkSeedDist : ProbComp (Bytes 16)) : OracleComp OS Bool :=
  walkProg (PprfS S oR pkSeedDist)

/-- **The EUF walk program.** -/
noncomputable def XE (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    (pkSeedDist : ProbComp (Bytes 16)) : OracleComp OS Bool :=
  walkProg (PprfE S oR pkSeedDist)

/-! ## Walks are the realisers' compression chains -/

theorem foldQ_eq_walkR : ∀ (c : St) (bs : List Blk), foldQ c bs = MD.walkR c bs
  | c, [] => by simp [foldQ, MD.walkR]
  | c, b :: bs => by
    have h : foldQ c (b :: bs) = cq (c, b) >>= fun c' => foldQ c' bs := by
      simp [foldQ, List.foldlM_cons]
    rw [h, MD.walkR]
    exact bind_congr fun c' ↦ foldQ_eq_walkR c' bs

theorem cellsR_wQ (bs : List Blk) :
    simulateQ (MD.cellsR IV128) (wQ bs) = MD.walkR IV128 bs := by
  unfold wQ
  rw [simulateQ_spec_query]
  rfl

theorem cellsR_liftM {α : Type} (oa : ProbComp α) :
    simulateQ (MD.cellsR IV128) (liftM oa : OracleComp OS α) =
      (liftM oa : OracleComp CSpec α) := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp
  | query_bind n k ih =>
    rw [liftM_bind, liftM_bind, simulateQ_bind]
    simp only [ih]
    have : simulateQ (MD.cellsR IV128)
        (liftM (liftM (unifSpec.query n) : ProbComp _) : OracleComp OS _) =
        (liftM (liftM (unifSpec.query n) : ProbComp _) : OracleComp CSpec _) := by
      show simulateQ (MD.cellsR IV128) (liftM (OS.query (.inl (.inl n)))) = _
      rw [simulateQ_spec_query]
      rfl
    rw [this]

theorem hashW_eq (q : (publicHashSpec core₀).Domain) :
    simulateQ (MD.cellsR IV128) (hashW q) = hashC q := by
  rcases q with ⟨pk, a, xs⟩ | ⟨R, pk, root, M⟩
  · show simulateQ (MD.cellsR IV128) (out16 <$> wQ _) = _
    simp [hashC, thashC, foldQ_eq_walkR, MD.walkR.eq_2, cellsR_wQ, MD.cR, cq]
  · simp only [hashW, hashC, hmsgC, simulateQ_bind, cellsR_wQ, foldQ_eq_walkR]
    refine bind_congr fun s ↦ bind_congr fun s' ↦ ?_
    rfl

theorem prfW_eq (k r : Bytes 16) (M : List UInt8) :
    simulateQ (MD.cellsR IV128) (prfW k r M) = prfMsgC k r M := by
  simp only [prfW, prfMsgC, simulateQ_bind, simulateQ_pure, cellsR_wQ, MD.walkR,
    ← foldQ_eq_walkR, bind_assoc, pure_bind]
  rfl

theorem prfOI_cEmb (k : Bytes 16) {α : Type} (Y : OracleComp CSpec α) :
    simulateQ (prfOI k) (simulateQ (cEmb (X := Dsk →ₒ Bytes 16)) Y) = Y := by
  rw [← QueryImpl.simulateQ_compose]
  conv_rhs => rw [← simulateQ_id' Y]
  congr 1
  funext t
  rcases t with n | q
  · simp [cEmb, prfOI]
  · simp [cEmb, prfOI]

/-- **H1 (generic form).**  The realisers' closed compression program of any port program is its
walk program answered by compression chains. -/
theorem progOf_chainA_eq (P : OracleComp (QSpec Rd Dsk) Bool) :
    progOf (chainA P) = simulateQ (MD.cellsR IV128) (walkProg P) := by
  unfold progOf chainA walkProg
  rw [simulateQ_bind, cellsR_liftM]
  refine bind_congr fun k ↦ ?_
  rw [← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose]
  congr 1
  funext t
  rcases t with n | (q | d) | (q | t)
  · simp [chainP, chainW, prfOI]
    rfl
  · simp [chainP, chainW, prfOI]
    rfl
  · show simulateQ (prfOI k)
        (liftM ((unifSpec + (hS St Blk + (Dsk →ₒ Bytes 16))).query (.inr (.inr d)))) =
      simulateQ (MD.cellsR IV128) (out16 <$> wQ [sb128 d.1, blk128 d.2 k])
    rw [simulateQ_spec_query, map_eq_bind_pure_comp, simulateQ_bind, cellsR_wQ]
    simp [prfOI, MD.walkR.eq_2, MD.walkR.eq_1, MD.cR]
  · simp only [QueryImpl.apply_compose, chainP, chainW, hashPW, hashPC]
    rw [prfOI_cEmb, hashW_eq]
  · simp only [QueryImpl.apply_compose, chainP, chainW, hashPW, hashPC]
    exact (prfOI_cEmb k _).trans (prfW_eq _ _ _).symm

/-- **H1 (SUF).** -/
theorem h1_suf (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    (pkSeedDist : ProbComp (Bytes 16)) :
    progS S oR pkSeedDist = simulateQ (MD.cellsR IV128) (XS S oR pkSeedDist) :=
  progOf_chainA_eq _

/-- **H1 (EUF).** -/
theorem h1_euf (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    (pkSeedDist : ProbComp (Bytes 16)) :
    progE S oR pkSeedDist = simulateQ (MD.cellsR IV128) (XE S oR pkSeedDist) :=
  progOf_chainA_eq _

end Ideal.Direct.Rom

#print axioms Ideal.Direct.Rom.h1_suf
#print axioms Ideal.Direct.Rom.h1_euf
