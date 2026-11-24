import MIdeal.Fors128fPhase
namespace MIdeal.Fors128f
open Ideal Ideal.Realize MLink SLHDSA SLHDSA.Security OracleComp OracleSpec Reduction Reduction.Open Ideal.Transport TweakableHash ENNReal
open Ideal.Realize.Fors Reduction.Resources2 Reduction.Lazy
open Class128f (vp P)
attribute [local irreducible] wotsChainTargets wotsStepTargets wotsStepTargetsT Lazy.structSecIdx Lazy.sparseTable wotsInsts
noncomputable local instance fixedY (g : CompressionTables) : SampleableType (P g).Y := sampY128
local instance fixedSk (g : CompressionTables) : SampleableType (P g).SkSeed := inferInstanceAs (SampleableType (Bytes 16))
local instance fixedPrf (g : CompressionTables) : SampleableType (P g).SkPrf := inferInstanceAs (SampleableType (Bytes 16))
local instance fixedInh (g : CompressionTables) : Inhabited (P g).Y := inferInstanceAs (Inhabited (Bytes 16))
local instance fixedEqY (g : CompressionTables) : DecidableEq (P g).Y := inferInstanceAs (DecidableEq (Bytes 16))
local instance fixedEqPk (g : CompressionTables) : DecidableEq (P g).PkSeed := inferInstanceAs (DecidableEq (Bytes 16))
local instance fixedEqAd (g : CompressionTables) : DecidableEq (P g).AdrsKey := inferInstanceAs (DecidableEq (Bytes 22))
local instance fixedFinite (g : CompressionTables) : Fintype (P g).Y := inferInstanceAs (Fintype (Bytes 16))

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


private theorem with_read {v : ValidatedParams} (base : Primitives v.params)
    (T : base.PkSeed → base.AdrsKey → List base.Y → base.Y)
    (H : base.Y → base.PkSeed → base.Y → List Byte → Bytes v.params.m)
    (ans : QueryImpl (publicHashSpec base.core) (OracleComp CSpec)) (c : CF St Blk)
    (he : ∀ t, simulateQ (instImpl₀ c) (ans t) = pure (f := ProbComp) (α := (publicHashSpec base.core).Range t) (publicAnswers base T H t)) :
    ∀ t, simulateQ (instImpl₀ c) (ans t) = pure (f := ProbComp) (α := (publicHashSpec base.core).Range t) (PublicHash.impl (withTH base T H) t) := by
  intro t
  cases t <;> exact he _

private theorem read_at (m g : CompressionTables) (t : (publicHashSpec (P m).core).Domain) :
    simulateQ (instImpl₀ g.1) (Class128f.hashImpl m t) =
      pure (f := ProbComp) (α := (publicHashSpec (P m).core).Range t) (publicAnswers (P m) (th g) (hm g) t) := by
  cases t with
  | thash pk a xs =>
    exact (thashC_inst g.1 pk a xs).trans (congrArg (fun y => pure (f := ProbComp) y)
      ((thG_shape g.1 pk a xs).trans (Hash128f.shape g pk a xs).symm))
  | hmsg r pk root msg => exact Class128f.hmsg_at g r pk root msg

abbrev State := (SecIdx → Bytes 16) × List (Bytes 22 × Bytes 16) × List (Bytes 16)
noncomputable irreducible_def choose (m : CompressionTables) : OracleComp (ForsP1Spec (P m)) State :=
  forsPhase1 vp (P m)
variable (seeds : ProbComp (Bytes 16)) (ref : CF St Blk) (g : CompressionTables)

noncomputable def dsprAdv (m : CompressionTables) : DsprAdv (Fors.family Sha2Set.s128f seeds) where
  State := State
  choose := simulateQ embImpl (choose m)
  guess st pk := phase2C (P m) (Class128f.hashImpl m) (fun tg z => forsDsprPost tg z) (fun k => rand k.pkSeed k.pkRoot)
    (PureCompression.typed Sha2Set.s128f A m m.2) st.1 st.2.1 st.2.2 pk

private noncomputable abbrev dsprCanon (f : Bytes 16 → Bytes 16 → Adrs → Bytes 16) (p : Bytes 16 → Bytes 16 → List Byte → Bytes 16)
    (st : State) (pk : Bytes 16) :=
  let m : CompressionTables := (ref,g.2)
  dspr_run (v := vp) (P m) (Class128f.hashImpl m) (th g) (hm g) rand seeds (PureCompression.codec Sha2Set.s128f m)
    (A.at512 g.2).toI.main g.1 f p st.1 st.2.1 st.2.2 pk
    (with_read (P m) (th g) (hm g) _ g.1 (read_at m g))

private noncomputable def selected {α : Type} (x : α) : {y : α // y = x} := Classical.choice ⟨⟨x,rfl⟩⟩

set_option maxHeartbeats 450000 in
theorem dspr_fixed (st : State) (pk : Bytes 16) :
    (toDspr (Lazy.bOpenPreS (Wots128f.reduced rand A seeds g))).guess st pk =
      simulateQ (instImpl₀ g.1) ((dsprAdv rand A seeds (ref,g.2)).guess st pk) := by
  have h := dsprCanon rand A seeds ref g (selected (prf g)).val (selected (pm g)).val st pk
  rw [(selected (prf g)).property,(selected (pm g)).property] at h
  dsimp only [dsprAdv,Wots128f.reduced,PureCompression.typed,PureCompression.internalBytes,PureCompression.codec,
    SignatureAlg.StrongUnforgeableAdversary.toUnforgeableAdversary,trCodec,setPrf,setPrfC,withTH,
    th,hm,prf,pm,P,tablePrimitives,sha2PrimitivesMixed,vp] at h ⊢
  kexact h

private noncomputable abbrev dsprFirst (f : Bytes 16 → Bytes 16 → Adrs → Bytes 16) (p : Bytes 16 → Bytes 16 → List Byte → Bytes 16) :=
  let m : CompressionTables := (ref,g.2)
  dspr_choose (v := vp) (P m) (th g) (hm g) rand seeds (PureCompression.codec Sha2Set.s128f m)
    (A.at512 g.2).toI.main g.1 f p

theorem dspr_choose_fixed :
    (toDspr (Lazy.bOpenPreS (Wots128f.reduced rand A seeds g))).choose = choose (ref,g.2) := by
  rw [choose_def]
  have h := dsprFirst rand A seeds ref g (selected (prf g)).val (selected (pm g)).val
  rw [(selected (prf g)).property,(selected (pm g)).property] at h
  dsimp only [Wots128f.reduced,PureCompression.internalBytes,PureCompression.codec,
    SignatureAlg.StrongUnforgeableAdversary.toUnforgeableAdversary,trCodec,setPrf,setPrfC,withTH,
    th,hm,prf,pm,P,tablePrimitives,sha2PrimitivesMixed,vp] at h ⊢
  kexact h

noncomputable def tcrAdv (m : CompressionTables) : FvAdv (Fors.family Sha2Set.s128f seeds) where
  State := State
  choose := simulateQ embImpl (choose m)
  forge st pk := phase2C (P m) (Class128f.hashImpl m) (fun _ z => forsTcrPost z) (fun k => rand k.pkSeed k.pkRoot)
    (PureCompression.typed Sha2Set.s128f A m m.2) st.1 st.2.1 st.2.2 pk

private noncomputable abbrev tcrCanon (f : Bytes 16 → Bytes 16 → Adrs → Bytes 16) (p : Bytes 16 → Bytes 16 → List Byte → Bytes 16)
    (st : State) (pk : Bytes 16) :=
  let m : CompressionTables := (ref,g.2)
  tcr_run (v := vp) (P m) (Class128f.hashImpl m) (th g) (hm g) rand seeds (PureCompression.codec Sha2Set.s128f m)
    (A.at512 g.2).toI.main g.1 f p st.1 st.2.1 st.2.2 pk
    (with_read (P m) (th g) (hm g) _ g.1 (read_at m g))


set_option maxHeartbeats 450000 in
theorem tcr_fixed (st : State) (pk : Bytes 16) :
    (toTcr (Lazy.bOpenPreS (Wots128f.reduced rand A seeds g))).forge st pk =
      simulateQ (instImpl₀ g.1) ((tcrAdv rand A seeds (ref,g.2)).forge st pk) := by
  have h := tcrCanon rand A seeds ref g (selected (prf g)).val (selected (pm g)).val st pk
  rw [(selected (prf g)).property,(selected (pm g)).property] at h
  dsimp only [tcrAdv,Wots128f.reduced,PureCompression.typed,PureCompression.internalBytes,PureCompression.codec,
    SignatureAlg.StrongUnforgeableAdversary.toUnforgeableAdversary,trCodec,setPrf,setPrfC,withTH,
    th,hm,prf,pm,P,tablePrimitives,sha2PrimitivesMixed,vp] at h ⊢
  kexact h

private noncomputable abbrev tcrFirst (f : Bytes 16 → Bytes 16 → Adrs → Bytes 16) (p : Bytes 16 → Bytes 16 → List Byte → Bytes 16) :=
  let m : CompressionTables := (ref,g.2)
  tcr_choose (v := vp) (P m) (th g) (hm g) rand seeds (PureCompression.codec Sha2Set.s128f m)
    (A.at512 g.2).toI.main g.1 f p

theorem tcr_choose_fixed :
    (toTcr (Lazy.bOpenPreS (Wots128f.reduced rand A seeds g))).choose = choose (ref,g.2) := by
  rw [choose_def]
  have h := tcrFirst rand A seeds ref g (selected (prf g)).val (selected (pm g)).val
  rw [(selected (prf g)).property,(selected (pm g)).property] at h
  dsimp only [Wots128f.reduced,PureCompression.internalBytes,PureCompression.codec,
    SignatureAlg.StrongUnforgeableAdversary.toUnforgeableAdversary,trCodec,setPrf,setPrfC,withTH,
    th,hm,prf,pm,P,tablePrimitives,sha2PrimitivesMixed,vp] at h ⊢
  kexact h
end MIdeal.Fors128f
#print axioms MIdeal.Fors128f.dspr_fixed
#print axioms MIdeal.Fors128f.tcr_fixed
