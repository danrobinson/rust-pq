import MIdeal.Wots128fFirst

/-! Running any of the three SHA2-128f WOTS second phases against the sampled
SHA-256 table implements the corresponding byte-forger reduction. The program
may be constructed using an arbitrary reference SHA-256 table. -/

namespace MIdeal.Wots128f
open Ideal Ideal.Realize MLink SLHDSA SLHDSA.Security OracleComp OracleSpec Reduction Reduction.Open Ideal.Transport TweakableHash ENNReal
open Ideal.Realize.Wots Reduction.Resources2 Reduction.Lazy
open Class128f (vp P)
attribute [local irreducible] wotsChainTargets wotsStepTargets wotsStepTargetsT Lazy.structSecIdx Lazy.sparseTable wotsInsts
noncomputable local instance (g : CompressionTables) : SampleableType (P g).Y := sampY128
local instance (g : CompressionTables) : SampleableType (P g).SkSeed := inferInstanceAs (SampleableType (Bytes 16))
local instance (g : CompressionTables) : SampleableType (P g).SkPrf := inferInstanceAs (SampleableType (Bytes 16))
local instance (g : CompressionTables) : Inhabited (P g).Y := inferInstanceAs (Inhabited (Bytes 16))
local instance (g : CompressionTables) : DecidableEq (P g).Y := inferInstanceAs (DecidableEq (Bytes 16))
local instance (g : CompressionTables) : DecidableEq (P g).PkSeed := inferInstanceAs (DecidableEq (Bytes 16))
local instance (g : CompressionTables) : DecidableEq (P g).AdrsKey := inferInstanceAs (DecidableEq (Bytes 22))
local instance (g : CompressionTables) : Fintype (P g).Y := inferInstanceAs (Fintype (Bytes 16))

variable (rand : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) (A : PureCompression.Forger)
private def th (g : CompressionTables) : Bytes 16 → Bytes 22 → List (Bytes 16) → Bytes 16 := (P g).Thash
private def hm (g : CompressionTables) : Bytes 16 → Bytes 16 → Bytes 16 → List Byte → Bytes 34 := (P g).Hmsg
private def prf (g : CompressionTables) : Bytes 16 → Bytes 16 → Adrs → Bytes 16 := (P g).PRF
private def pm (g : CompressionTables) : Bytes 16 → Bytes 16 → List Byte → Bytes 16 := (P g).PRFmsg
private def publicAnswers {p : Params} (base : Primitives p)
    (T : base.PkSeed → base.AdrsKey → List base.Y → base.Y)
    (H : base.Y → base.PkSeed → base.Y → List Byte → Bytes p.m) :
    QueryImpl (publicHashSpec base.core) Id
  | .thash pk a xs => T pk a xs
  | .hmsg r pk root msg => H r pk root msg

private theorem reader_transport {v : ValidatedParams} (base : Primitives v.params)
    (T : base.PkSeed → base.AdrsKey → List base.Y → base.Y)
    (H : base.Y → base.PkSeed → base.Y → List Byte → Bytes v.params.m)
    (tbl : SecIdx → base.Y) (g : CF St Blk)
    (read : QueryImpl (Lazy.OSpec base (hS St Blk)) (OracleComp CSpec))
    (he : ∀ t, simulateQ (instImpl₀ g) (read t) =
      simulateQ (instImpl₀ g) (Lazy.tblImpl (gspec := hS St Blk) (publicAnswers base T H) tbl t)) :
    ∀ t, simulateQ (instImpl₀ g) (read t) =
      simulateQ (instImpl₀ g) (Lazy.tblImpl (gspec := hS St Blk) (PublicHash.impl (withTH base T H)) tbl t) := by
  have e : @Eq (QueryImpl (publicHashSpec base.core) Id)
      (PublicHash.impl (withTH base T H)) (publicAnswers base T H) := by
    funext q
    cases q <;> rfl
  rw [e]
  exact he

private theorem reader (m g : CompressionTables) (tbl : SecIdx → Bytes 16) (t : (Lazy.OSpec (P m) (hS St Blk)).Domain) :
    simulateQ (instImpl₀ g.1) (Class128f.handler m tbl t) =
      simulateQ (instImpl₀ g.1) (Lazy.tblImpl (gspec := hS St Blk) (publicAnswers (P m) (th g) (hm g)) tbl t) := by
  rcases t with n|q|d|t
  · rfl
  · rfl
  · rfl
  · cases t with
    | thash pk a xs =>
      change simulateQ (instImpl₀ g.1) (thashC pk a xs) = pure (f := ProbComp) ((P g).Thash pk a xs)
      exact (thashC_inst g.1 pk a xs).trans (congrArg (fun y => pure (f := ProbComp) y)
        ((thG_shape g.1 pk a xs).trans (Hash128f.shape g pk a xs).symm))
    | hmsg r pk root msg => exact Class128f.hmsg_at g r pk root msg

set_option maxHeartbeats 1200000 in
theorem ud_fixed (ref : CF St Blk) (g : CompressionTables) (seeds : ProbComp (Bytes 16)) (st : PhaseState) (pk : Bytes 16) :
    simulateQ (instImpl₀ g.1) (udPhase rand A (ref,g.2) st pk) =
      (rUd (prims := P g) seeds (Lazy.bWotsS (reduced rand A seeds g))).distinguish st pk := by
  obtain ⟨⟨tbl,hist,root⟩,hist2⟩ := st
  let m : CompressionTables := (ref,g.2)
  have h := ud_open (v := vp) (P m) (th g) (hm g) rand seeds (PureCompression.codec Sha2Set.s128f m)
    (A.at512 g.2).toI.main g.1 (prf g) (pm g) tbl (Class128f.handler m tbl)
    (reader_transport (v := vp) (P m) (th g) (hm g) tbl g.1 (Class128f.handler m tbl) (reader m g tbl)) hist hist2 root pk
  dsimp only [udPhase,reduced,PureCompression.typed,PureCompression.internalBytes,PureCompression.codec,
    trCodec,setPrf,setPrfC,withTH,m,th,hm,prf,pm,P,tablePrimitives,sha2PrimitivesMixed] at h ⊢
  kexact h

set_option maxHeartbeats 1200000 in
theorem pre_fixed (ref : CF St Blk) (g : CompressionTables) (seeds : ProbComp (Bytes 16)) (st : PhaseState) (pk : Bytes 16) :
    simulateQ (instImpl₀ g.1) (prePhase rand A (ref,g.2) st pk) =
      (rPre (prims := P g) seeds (Lazy.bWotsS (reduced rand A seeds g))).invert st pk := by
  obtain ⟨⟨tbl,hist,root⟩,hist2⟩ := st
  let m : CompressionTables := (ref,g.2)
  have h := pre_open (v := vp) (P m) (th g) (hm g) rand seeds (PureCompression.codec Sha2Set.s128f m)
    (A.at512 g.2).toI.main g.1 (prf g) (pm g) tbl (Class128f.handler m tbl)
    (reader_transport (v := vp) (P m) (th g) (hm g) tbl g.1 (Class128f.handler m tbl) (reader m g tbl)) hist hist2 root pk
  dsimp only [prePhase,reduced,PureCompression.typed,PureCompression.internalBytes,PureCompression.codec,
    trCodec,setPrf,setPrfC,withTH,m,th,hm,prf,pm,P,tablePrimitives,sha2PrimitivesMixed] at h ⊢
  kexact h

set_option maxHeartbeats 1200000 in
theorem tcr_fixed (ref : CF St Blk) (g : CompressionTables) (seeds : ProbComp (Bytes 16)) (st : PhaseState) (pk : Bytes 16) :
    simulateQ (instImpl₀ g.1) (tcrPhase rand A (ref,g.2) st pk) =
      (rTcrT (prims := P g) seeds (Lazy.bWotsS (reduced rand A seeds g))).forge st pk := by
  obtain ⟨⟨tbl,hist,root⟩,hist2⟩ := st
  let m : CompressionTables := (ref,g.2)
  have h := tcr_open (v := vp) (P m) (th g) (hm g) rand seeds (PureCompression.codec Sha2Set.s128f m)
    (A.at512 g.2).toI.main g.1 (prf g) (pm g) tbl (Class128f.handler m tbl)
    (reader_transport (v := vp) (P m) (th g) (hm g) tbl g.1 (Class128f.handler m tbl) (reader m g tbl)) hist hist2 root pk
  dsimp only [tcrPhase,reduced,PureCompression.typed,PureCompression.internalBytes,PureCompression.codec,
    trCodec,setPrf,setPrfC,withTH,m,th,hm,prf,pm,P,tablePrimitives,sha2PrimitivesMixed] at h ⊢
  kexact h

end MIdeal.Wots128f
#print axioms MIdeal.Wots128f.ud_fixed

#print axioms MIdeal.Wots128f.pre_fixed
#print axioms MIdeal.Wots128f.tcr_fixed
