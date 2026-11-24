import MIdeal.Class128fFixed
import MIdeal.Itsr128fBound
import Ideal.Realize.ItsrReal
import Ideal.Realize.ItsrBound
import Ideal.Realize.MsgHarness

/-! The SHA2-128f ITSR byte-forger reduction as a program that makes public
compression queries. Its instantiation agrees with the original experiment for
each SHA-256 table and each fixed SHA-512 table. -/

namespace MIdeal.Itsr128f
open Ideal Ideal.Realize MLink SLHDSA SLHDSA.Security OracleComp OracleSpec Reduction Reduction.Open
open Ideal.Realize.Itsr Reduction.Lazy Ideal.Transport KeyedHash
open Class128f (vp P)

noncomputable def handler {ι κ : Type} {G : OracleSpec ι} {H : OracleSpec κ}
    {V : Type} [SampleableType V] (hash : QueryImpl H (OracleComp CSpec)) :
    QueryImpl (RSpec (G + hS St Blk) Unit V H) (OracleComp (unifSpec + (hS St Blk + G)))
  | .inl n => (unifSpec + (hS St Blk + G)).query (.inl n)
  | .inr (.inl (.inl x)) => (unifSpec + (hS St Blk + G)).query (.inr (.inr x))
  | .inr (.inl (.inr c)) => (unifSpec + (hS St Blk + G)).query (.inr (.inl c))
  | .inr (.inr (.inl _)) => liftM ($ᵗ V : ProbComp V)
  | .inr (.inr (.inr h)) => simulateQ Msg.cEmb (hash h)

theorem run_at {ι κ : Type} {G : OracleSpec ι} {H : OracleSpec κ}
    {D V α : Type} [DecidableEq D] [SampleableType V] (g : CF St Blk)
    (ans : QueryImpl H Id) (hash : QueryImpl H (OracleComp CSpec))
    (correct : ∀ t, simulateQ (instImpl₀ g) (hash t) = pure (f := ProbComp) (α := H.Range t) (ans t))
    (prog : OracleComp (RSpec (G + hS St Blk) D V H) α) :
    lazyRun ans (simulateQ (portAns g) prog) =
      simulateQ (instImpl g) (simulateQ (handler hash) (lazyRes prog)) := by
  rw [lazyRun,lazyRes_portAns]
  refine simulateQ_comm_of_step _ _ _ _ (fun t => ?_) _
  rcases t with n | (x|c) | d | h
  · simp only [portAns,handler,simulateQ_spec_query]; rfl
  · simp only [portAns,handler,simulateQ_spec_query]; rfl
  · simp only [portAns,handler,simulateQ_pure,simulateQ_spec_query]; rfl
  · simp only [portAns,handler,simulateQ_spec_query,Msg.instImpl_liftM]; rfl
  · simp only [portAns,handler,simulateQ_spec_query,Msg.instImpl_cEmb,correct,liftM_pure]
    rfl

section Transport
variable {v : ValidatedParams} (base : Primitives v.params)
  [SampleableType base.SkSeed] [SampleableType base.SkPrf] [SampleableType base.Y]
  [DecidableEq base.Y] [DecidableEq base.PkSeed] [DecidableEq base.AdrsKey] [Inhabited base.Y]
  (T : base.PkSeed → base.AdrsKey → List base.Y → base.Y)
  (H : base.Y → base.PkSeed → base.Y → List Byte → Bytes v.params.m)
  (r : base.PkSeed → base.Y → ProbComp base.Y) (seeds : ProbComp base.PkSeed)
  (codec : CoreWireCodec v.params base.core)
  (mb : List Byte → OracleComp (FSpecP (List Byte)) (List Byte × List Byte))
  (g : CF St Blk) (prf : base.PkSeed → base.SkSeed → Adrs → base.Y)
  (pm : base.SkPrf → base.Y → List Byte → base.Y)
  (hash : QueryImpl (publicHashSpec base.core) (OracleComp CSpec))

private def answers : QueryImpl (publicHashSpec base.core) Id
  | .thash pk a xs => T pk a xs
  | .hmsg a b c m => H a b c m

set_option quotPrecheck false in
local notation "B" => bytesToTyped (vp := v) (prims := setPrf (withTH base T H) prf pm)
    (codec := trCodec _ prf pm codec) (optRand := fun k => r k.pkSeed k.pkRoot)
    (pkSeedDist := seeds) ⟨fun pk => simulateQ (instImpl g) (mb pk)⟩

theorem open_at (he : ∀ t, simulateQ (instImpl₀ g) (hash t) =
    pure (f := ProbComp) (α := (publicHashSpec base.core).Range t) (answers base T H t)) :
    (bItsrL (prims := setPrf (withTH base T H) prf pm) B).main =
      simulateQ (instImpl g) (simulateQ (handler hash) (lazyRes (itsrOpenP (vp := v)
        (prims := base) (fun k => r k.pkSeed k.pkRoot) seeds (typedP codec mb)))) := by
  let W := withTH base T H
  let rb := fun (k : PublicKeyCore base.core) => r k.pkSeed k.pkRoot
  let rs := fun (k : PublicKeyCore (setPrfC base.core prf pm)) => r k.pkSeed k.pkRoot
  let b := bytesToTyped (vp := v) (prims := W) (codec := codec) (optRand := rb)
    (pkSeedDist := seeds) ⟨fun pk => simulateQ (instImpl g) (mb pk)⟩
  have tr := bItsrL_main_setPrf W prf pm codec rb rs (fun _ => rfl) seeds (fun pk => simulateQ (instImpl g) (mb pk))
  refine tr.trans ?_
  have fb : b = (⟨fun pk => simulateQ (instImpl g) (typedP (prims := W) codec mb pk)⟩ : Forger v W rb seeds) :=
    congrArg _ (funext (typedP_inst (prims := W) codec rb seeds g mb)).symm
  have hf := itsrOpenP_fusion (prims := W) rb seeds g (typedP (prims := W) codec mb)
  change lazyRun (PublicHash.impl W) (itsrOpen b) = _
  rw [fb,←hf]
  have hh : ∀ t, simulateQ (instImpl₀ g) (hash t) = pure (f := ProbComp)
      (α := (publicHashSpec base.core).Range t) (PublicHash.impl W t) := by
    intro t
    cases t <;> apply he
  kexact run_at g (PublicHash.impl W) hash hh (itsrOpenP (prims := W) rb seeds (typedP (prims := W) codec mb))
end Transport
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
variable (seeds : ProbComp (Bytes 16))

abbrev TargetSpec := ITSRTargetSpec Hmsg.Fast128.Msg Hmsg.Fast128.Key
abbrev Spec := unifSpec + (hS St Blk + TargetSpec)
abbrev USpec (m : CompressionTables) := RSpec (gI (P m)) Unit (Bytes 16) (publicHashSpec (P m).core)

noncomputable def program (m : CompressionTables) : OracleComp Spec Hmsg.Fast128.Input :=
  simulateQ (handler (Class128f.hashImpl m)) (lazyRes (itsrOpenP (vp := vp) (prims := P m)
    (fun k => rand k.pkSeed k.pkRoot) seeds (PureCompression.typed Sha2Set.s128f A m m.2)))

noncomputable abbrev reduced (g : CompressionTables) :=
  bytesToTyped (PureCompression.internalBytes Sha2Set.s128f rand seeds A g).toUnforgeableAdversary

private theorem read_at (m g : CompressionTables) (t : (publicHashSpec (P m).core).Domain) :
    simulateQ (instImpl₀ g.1) (Class128f.hashImpl m t) =
      pure (f := ProbComp) (α := (publicHashSpec (P m).core).Range t) (answers (P m) (th g) (hm g) t) := by
  cases t with
  | thash pk a xs =>
    exact (thashC_inst g.1 pk a xs).trans (congrArg (fun y => pure (f := ProbComp) y)
      ((thG_shape g.1 pk a xs).trans (Hash128f.shape g pk a xs).symm))
  | hmsg r pk root msg => exact Class128f.hmsg_at g r pk root msg

theorem main_fixed (ref : CF St Blk) (g : CompressionTables) :
    (bItsrL (prims := P g) (reduced rand A seeds g)).main =
      simulateQ (instImpl g.1) (program rand A seeds (ref,g.2)) := by
  let m : CompressionTables := (ref,g.2)
  have h := open_at (v := vp) (P m) (th g) (hm g) rand seeds (PureCompression.codec Sha2Set.s128f m)
    (A.at512 g.2).toI.main g.1 (prf g) (pm g) (Class128f.hashImpl m) (read_at m g)
  dsimp only [program,reduced,PureCompression.typed,PureCompression.internalBytes,PureCompression.codec,
    trCodec,setPrf,setPrfC,withTH,m,th,hm,prf,pm,P,tablePrimitives,sha2PrimitivesMixed] at h ⊢
  kexact h

theorem experiment (ref : CF St Blk) (g : CompressionTables) :
    ITSRExperiment (bItsrL (prims := P g) (reduced rand A seeds g)) =
      ITSRExperiment (Ideal.Itsr.ItsrAdvI.inst (program rand A seeds (ref,g.2)) (itsrProblem vp (P g)) g.1) := by
  have e := congrArg (ITSRAdversary.mk (prob := itsrProblem vp (P g))) (main_fixed rand A seeds ref g)
  kexact congrArg ITSRExperiment e
end MIdeal.Itsr128f
#print axioms MIdeal.Itsr128f.open_at
#print axioms MIdeal.Itsr128f.main_fixed
#print axioms MIdeal.Itsr128f.experiment
