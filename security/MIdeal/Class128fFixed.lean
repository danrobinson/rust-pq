import MIdeal.Class128f
/-! The class-TCR second phase is fixed before sampling the SHA-256 table. Its
choice of reference table affects only the types of the open program. The public
SHA-512 table may be fixed first. -/
namespace MIdeal.Class128f
open Ideal Ideal.Realize MLink SLHDSA SLHDSA.Security OracleComp OracleSpec Reduction Reduction.Open Ideal.Transport

section
variable {v : ValidatedParams} (base : Primitives v.params)
  (T : base.PkSeed → base.AdrsKey → List base.Y → base.Y)
  (H : base.Y → base.PkSeed → base.Y → List Byte → Bytes v.params.m)
  (rand : base.PkSeed → base.Y → ProbComp base.Y) (seeds : ProbComp base.PkSeed)
  (codec : CoreWireCodec v.params base.core)
  (mb : List Byte → OracleComp (FSpecP (List Byte)) (List Byte × List Byte))

private def answers : QueryImpl (publicHashSpec base.core) Id
  | .thash pk a xs => T pk a xs
  | .hmsg r pk root m => H r pk root m

private def runHandler (c : QueryImpl (publicHashSpec base.core) (OracleComp CSpec)) (tbl : SecretTable v base) :
    QueryImpl (Lazy.OSpec base (hS St Blk)) (OracleComp CSpec)
  | .inl n => CSpec.query (.inl n)
  | .inr (.inl q) => Realize.cq q
  | .inr (.inr (.inl d)) => pure (tbl d)
  | .inr (.inr (.inr h)) => c h

private theorem runHandler_at (g : CF St Blk) (c : QueryImpl (publicHashSpec base.core) (OracleComp CSpec))
    (hc : ∀ t, simulateQ (instImpl₀ g) (c t) =
      pure (f := ProbComp) (α := (publicHashSpec base.core).Range t) (answers base T H t))
    (tbl : SecretTable v base) {α : Type} (oa : OracleComp (Lazy.OSpec base (hS St Blk)) α) :
    simulateQ (instImpl₀ g) (simulateQ (runHandler base c tbl) oa) =
      simulateQ (instImpl₀ g) (simulateQ (Lazy.tblImpl (gspec := hS St Blk) (PublicHash.impl (withTH base T H)) tbl) oa) := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind,simulateQ_spec_query,ih]
    congr 1
    rcases t with n | q | d | h
    · rfl
    · rfl
    · rfl
    · cases h <;> exact (hc _).trans (by simp [Lazy.tblImpl,answers,PublicHash.impl,withTH])

variable [SampleableType base.SkSeed] [SampleableType base.SkPrf] [SampleableType base.Y]
  [DecidableEq base.Y] [DecidableEq base.PkSeed] [DecidableEq base.AdrsKey] [Inhabited base.Y]

set_option maxHeartbeats 1200000 in
private theorem openClass_at (g : CF St Blk) (c : QueryImpl (publicHashSpec base.core) (OracleComp CSpec))
    (hc : ∀ t, simulateQ (instImpl₀ g) (c t) =
      pure (f := ProbComp) (α := (publicHashSpec base.core).Range t) (answers base T H t))
    (prf : base.PkSeed → base.SkSeed → Adrs → base.Y) (pm : base.SkPrf → base.Y → List Byte → base.Y)
    (arity : ℕ) (tbl : SecretTable v base) (rows : List (base.AdrsKey × List base.Y)) (pk : base.PkSeed) :
    simulateQ (instImpl₀ g) (simulateQ (runHandler base c tbl)
      (tcrMOpenP (vp := v) (prims := base) (fun k => rand k.pkSeed k.pkRoot) (typedP codec mb) rows pk) >>= fun jm =>
      pure (classOut base arity rows jm)) =
      (bTcrArM arity (bytesToTyped (vp := v) (prims := setPrf (withTH base T H) prf pm)
        (codec := trCodec _ prf pm codec) (optRand := fun k => rand k.pkSeed k.pkRoot) (pkSeedDist := seeds)
        ⟨fun pk => simulateQ (instImpl g) (mb pk)⟩)).forge (tbl,rows) pk := by
  let r := fun (k : PublicKeyCore base.core) => rand k.pkSeed k.pkRoot
  let r' := fun (k : PublicKeyCore (setPrfC base.core prf pm)) => rand k.pkSeed k.pkRoot
  have hr (pk : PublicKeyCore base.core) : r' (trPk _ prf pm pk) = r pk := rfl
  let B := bytesToTyped (vp := v) (prims := withTH base T H) (codec := codec) (optRand := r)
    (pkSeedDist := seeds) ⟨fun pk => simulateQ (instImpl g) (mb pk)⟩
  rw [bTcrArM_forge_setPrf (withTH base T H) prf pm arity B _
    (fun tbl pk => g2Run_bytesToTyped_tr (prims := withTH base T H) prf pm codec r r' hr seeds
      (fun pk => simulateQ (instImpl g) (mb pk)) tbl pk)]
  have h := congrArg (simulateQ (instImpl₀ g)) (tcrM_phase2_open_eq (hS St Blk) arity B tbl rows pk)
  rw [instImpl₀_liftM] at h
  rw [h,simulateQ_bind,simulateQ_bind,runHandler_at base T H g c hc,
    ← QueryImpl.simulateQ_compose,← QueryImpl.simulateQ_compose]
  rw [tcrMOpenP_fusion (vp := v) (prims := base) r
    (instImpl₀ g ∘ₛ Lazy.tblImpl (gspec := hS St Blk) (PublicHash.impl (withTH base T H)) tbl)
    g (fun _ => rfl) (typedP codec mb) rows pk]
  have main : (fun pk => simulateQ (instImpl g) (typedP codec mb pk)) = B.main :=
    funext (typedP_inst (prims := base) codec r seeds g mb)
  rw [main,tcrMOpen_withTH (prims := base) T H]
  simp only [classOut_withTH (prims := base) T H]
end
local instance (g : CompressionTables) : SampleableType (P g).Y := inferInstanceAs (SampleableType (Bytes 16))
local instance (g : CompressionTables) : SampleableType (P g).SkSeed := inferInstanceAs (SampleableType (Bytes 16))
local instance (g : CompressionTables) : SampleableType (P g).SkPrf := inferInstanceAs (SampleableType (Bytes 16))
local instance (g : CompressionTables) : Inhabited (P g).Y := inferInstanceAs (Inhabited (Bytes 16))
local instance (g : CompressionTables) : DecidableEq (P g).Y := inferInstanceAs (DecidableEq (Bytes 16))
local instance (g : CompressionTables) : DecidableEq (P g).PkSeed := inferInstanceAs (DecidableEq (Bytes 16))
local instance (g : CompressionTables) : DecidableEq (P g).AdrsKey := inferInstanceAs (DecidableEq (Bytes 22))
local instance (g : CompressionTables) : Fintype (P g).Y := inferInstanceAs (Fintype (Bytes 16))

variable (rand : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) (A : PureCompression.Forger)
open Ideal.Transport

private def th (g : CompressionTables) : Bytes 16 → Bytes 22 → List (Bytes 16) → Bytes 16 := (P g).Thash
private def hm (g : CompressionTables) : Bytes 16 → Bytes 16 → Bytes 16 → List Byte → Bytes 34 := (P g).Hmsg
private def prf (g : CompressionTables) : Bytes 16 → Bytes 16 → Adrs → Bytes 16 := (P g).PRF
private def pm (g : CompressionTables) : Bytes 16 → Bytes 16 → List Byte → Bytes 16 := (P g).PRFmsg

private theorem read_at (ref : CF St Blk) (g : CompressionTables) (t : (publicHashSpec (P (ref,g.2)).core).Domain) :
    simulateQ (instImpl₀ g.1) (hashImpl (ref,g.2) t) =
      pure (f := ProbComp) (α := (publicHashSpec (P (ref,g.2)).core).Range t)
        (answers (P (ref,g.2)) (th g) (hm g) t) := by
  cases t with
  | thash pk a xs =>
    exact (thashC_inst g.1 pk a xs).trans (congrArg (fun y => pure (f := ProbComp) y)
      ((thG_shape g.1 pk a xs).trans (Hash128f.shape g pk a xs).symm))
  | hmsg r pk root m => exact hmsg_at g r pk root m

set_option maxHeartbeats 1200000 in
theorem forge_fixed (ref : CF St Blk) (g : CompressionTables) (seeds : ProbComp (Bytes 16)) (arity : ℕ)
    (tbl : SecIdx → Bytes 16) (rows : List (Bytes 22 × List (Bytes 16))) (pk : Bytes 16) :
    simulateQ (instImpl₀ g.1) (forge rand A (ref,g.2) arity tbl rows pk) =
      (bTcrArM arity (bytesToTyped (PureCompression.internalBytes Sha2Set.s128f rand seeds A g).toUnforgeableAdversary)).forge (tbl,rows) pk := by
  let model : CompressionTables := (ref,g.2)
  have h := openClass_at (v := vp) (P model) (th g) (hm g)
    rand seeds (PureCompression.codec Sha2Set.s128f model)
    (A.at512 g.2).toI.main g.1 (hashImpl model) (read_at ref g)
    (prf g) (pm g) arity tbl rows pk
  dsimp only [forge, handler, runHandler, PureCompression.typed, PureCompression.internalBytes,
    PureCompression.codec, trCodec, setPrf, setPrfC, withTH, model,
    th, hm, prf, pm, P, tablePrimitives, sha2PrimitivesMixed] at h ⊢
  kexact h
end MIdeal.Class128f
#print axioms MIdeal.Class128f.forge_fixed
