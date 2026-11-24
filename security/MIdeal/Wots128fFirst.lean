import MIdeal.Wots128fPhase

/-! The SHA2-128f WOTS games choose all their targets before public compression
queries begin. Each chooser has the same distribution and the same oracle program
at every pair of SHA-256 and SHA-512 tables. -/

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
noncomputable abbrev reduced (seeds : ProbComp (Bytes 16)) (g : CompressionTables) :=
  bytesToTyped (PureCompression.internalBytes Sha2Set.s128f rand seeds A g).toUnforgeableAdversary

section First
variable (seeds : ProbComp (Bytes 16)) (ref : CompressionTables)

noncomputable def udChoose (m : CompressionTables) : OracleComp (udSpecC (Bytes 22) (Bytes 16)) PhaseState :=
  (rUd seeds (Lazy.bWotsS (reduced rand A seeds m))).pick

noncomputable def udAdv : UdAdv (Hash128f.chainFamily seeds) where
  State := PhaseState
  pick := simulateQ embImpl (udChoose rand A seeds ref)
  distinguish := udPhase rand A ref

theorem ud_choose_at (g : CompressionTables) : udChoose rand A seeds g = udChoose rand A seeds ref := by
  let f : HashFns (P ref) := ⟨th g,hm g,prf g,pm g⟩
  let B' := bytesToTyped (vp := vp) (prims := withHash (P ref) f) (codec := trCodec _ (prf g) (pm g) (PureCompression.codec Sha2Set.s128f ref))
    (optRand := fun k => rand k.pkSeed k.pkRoot) (pkSeedDist := seeds)
    ⟨fun pk => simulateQ (instImpl g.1) ((A.at512 g.2).toI.main pk)⟩
  have h := wotsUd_phase1_hashfree_all (vp := vp) (prims := P ref) (pkSeedDist := seeds) f B' (reduced rand A seeds ref)
  dsimp only [udChoose,reduced,PureCompression.internalBytes,PureCompression.codec,withHash,
    trCodec,setPrfC,B',f,th,hm,prf,pm,P,tablePrimitives,sha2PrimitivesMixed] at h ⊢
  kexact h

noncomputable def preChoose (m : CompressionTables) : OracleComp (preSpecC (Bytes 22) (Bytes 16)) PhaseState :=
  (rPre seeds (Lazy.bWotsS (reduced rand A seeds m))).choose

noncomputable def preAdv : PreAdv (Hash128f.chainFamily seeds) (Bytes 16) where
  State := PhaseState
  choose := simulateQ embImpl (preChoose rand A seeds ref)
  invert := prePhase rand A ref

theorem pre_choose_at (g : CompressionTables) : preChoose rand A seeds g = preChoose rand A seeds ref := by
  let f : HashFns (P ref) := ⟨th g,hm g,prf g,pm g⟩
  let B' := bytesToTyped (vp := vp) (prims := withHash (P ref) f) (codec := trCodec _ (prf g) (pm g) (PureCompression.codec Sha2Set.s128f ref))
    (optRand := fun k => rand k.pkSeed k.pkRoot) (pkSeedDist := seeds)
    ⟨fun pk => simulateQ (instImpl g.1) ((A.at512 g.2).toI.main pk)⟩
  have h := wotsPre_phase1_hashfree_all (vp := vp) (prims := P ref) (pkSeedDist := seeds) f B' (reduced rand A seeds ref)
  dsimp only [preChoose,reduced,PureCompression.internalBytes,PureCompression.codec,withHash,
    trCodec,setPrfC,B',f,th,hm,prf,pm,P,tablePrimitives,sha2PrimitivesMixed] at h ⊢
  kexact h

noncomputable def tcrChoose (m : CompressionTables) : OracleComp (tcrSpecC (Bytes 22) (Bytes 16)) PhaseState :=
  (rTcrT seeds (Lazy.bWotsS (reduced rand A seeds m))).choose

noncomputable def tcrAdv : TcrAdv (Hash128f.FWots128T seeds) where
  State := PhaseState
  choose := simulateQ embImpl (tcrChoose rand A seeds ref)
  forge := tcrPhase rand A ref

theorem tcr_choose_at (g : CompressionTables) : tcrChoose rand A seeds g = tcrChoose rand A seeds ref := by
  let f : HashFns (P ref) := ⟨th g,hm g,prf g,pm g⟩
  let B' := bytesToTyped (vp := vp) (prims := withHash (P ref) f) (codec := trCodec _ (prf g) (pm g) (PureCompression.codec Sha2Set.s128f ref))
    (optRand := fun k => rand k.pkSeed k.pkRoot) (pkSeedDist := seeds)
    ⟨fun pk => simulateQ (instImpl g.1) ((A.at512 g.2).toI.main pk)⟩
  have h := wotsTcrT_phase1_hashfree_all (vp := vp) (prims := P ref) (pkSeedDist := seeds) f B' (reduced rand A seeds ref)
  dsimp only [tcrChoose,reduced,PureCompression.internalBytes,PureCompression.codec,withHash,
    trCodec,setPrfC,B',f,th,hm,prf,pm,P,tablePrimitives,sha2PrimitivesMixed] at h ⊢
  kexact h

end First
end MIdeal.Wots128f

#print axioms MIdeal.Wots128f.ud_choose_at
#print axioms MIdeal.Wots128f.pre_choose_at
#print axioms MIdeal.Wots128f.tcr_choose_at
