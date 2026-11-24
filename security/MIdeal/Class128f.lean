import MIdeal.PureCompression
import MIdeal.Itsr128f
import MIdeal.Hash128f
import Ideal.Realize.TcrCount

namespace MIdeal.Class128f
open Ideal Ideal.Realize MLink SLHDSA SLHDSA.Security OracleComp OracleSpec Reduction
open MIdeal.Hmsg

attribute [local irreducible] Reduction.arityTargets Reduction.tcrTargets Reduction.Lazy.sparseTable Reduction.Lazy.structSecIdx

abbrev vp := Sha2Set.s128f.vp
abbrev P (g : CompressionTables) := tablePrimitives g vp.params

/-- Evaluate the 34-byte digest through the public SHA-256 port. The two MGF1
counters share their first compression block. -/
def hmsg (r pk root : Bytes 16) (m : List Byte) : OracleComp CSpec (Bytes 34) := do
  let s ← foldQ IV128 (iblocksH r pk root m)
  let row ← Realize.cq (IV128,counterPrefix r pk s)
  let a ← Realize.cq (row,counterFinal 0)
  let b ← Realize.cq (row,counterFinal 1)
  pure (digest128f (a,b))

theorem hmsg_at (g : CompressionTables) (r pk root : Bytes 16) (m : List Byte) :
    simulateQ (instImpl₀ g.1) (hmsg r pk root m) = pure ((P g).Hmsg r pk root m) := by
  simp only [hmsg,simulateQ_bind,foldQ_inst,cq_inst,pure_bind,simulateQ_pure,hmsg_128f_cells]
  rfl

theorem hmsg_count (r pk root : Bytes 16) (m : List Byte) :
    IsQueryBoundP (hmsg r pk root m) (fun i => i.isRight = true) ((m.length+56)/64+4) := by
  unfold hmsg
  apply (isQueryBoundP_bind (foldQ_bound _ _) fun s _ => isQueryBoundP_bind (cq_bound _) fun row _ =>
    isQueryBoundP_bind (cq_bound _) fun a _ => isQueryBoundP_bind (m := 0) (cq_bound _) fun b _ => isQueryBoundP_pure _ _ _).mono
  rw [iblocksH_length]

def hashImpl (model : CompressionTables) : QueryImpl (publicHashSpec (P model).core) (OracleComp CSpec)
  | .thash pk a xs => thashC pk a xs
  | .hmsg r pk root m => hmsg r pk root m

theorem hash_at (g : CompressionTables) (t : (publicHashSpec (P g).core).Domain) :
    simulateQ (instImpl₀ g.1) (hashImpl g t) = pure (f := ProbComp) (α := (publicHashSpec (P g).core).Range t)
      (PublicHash.impl (P g) t) := by
  cases t with
  | thash pk a xs =>
    exact (thashC_inst g.1 pk a xs).trans (congrArg (fun y => pure (f := ProbComp) y)
      ((thG_shape g.1 pk a xs).trans (Hash128f.shape g pk a xs).symm))
  | hmsg r pk root m => exact hmsg_at g r pk root m

def stepCost (model : CompressionTables) : (publicHashSpec (P model).core).Domain → ℕ
  | .thash _ _ xs => thashCost xs.length
  | .hmsg _ _ _ m => (m.length+56)/64+4

theorem hash_count (model : CompressionTables) (t : (publicHashSpec (P model).core).Domain) :
    IsQueryBoundP (hashImpl model t) (fun i => i.isRight = true) (stepCost model t) := by
  cases t with
  | thash pk a xs => exact thashC_bound pk a xs
  | hmsg r pk root m => exact hmsg_count r pk root m

open Ideal.Realize Reduction.Open
open PureCompression (Forger)

local instance (g : CompressionTables) : SampleableType (P g).Y := inferInstanceAs (SampleableType (Bytes 16))
local instance (g : CompressionTables) : SampleableType (P g).SkSeed := inferInstanceAs (SampleableType (Bytes 16))
local instance (g : CompressionTables) : SampleableType (P g).SkPrf := inferInstanceAs (SampleableType (Bytes 16))
local instance (g : CompressionTables) : Inhabited (P g).Y := inferInstanceAs (Inhabited (Bytes 16))
local instance (g : CompressionTables) : DecidableEq (P g).Y := inferInstanceAs (DecidableEq (Bytes 16))
local instance (g : CompressionTables) : DecidableEq (P g).PkSeed := inferInstanceAs (DecidableEq (Bytes 16))
local instance (g : CompressionTables) : DecidableEq (P g).AdrsKey := inferInstanceAs (DecidableEq (Bytes 22))
local instance (g : CompressionTables) : Fintype (P g).Y := inferInstanceAs (Fintype (Bytes 16))

def handler (g : CompressionTables) (tbl : SecretTable vp (P g)) :
    QueryImpl (Lazy.OSpec (P g) (hS St Blk)) (OracleComp CSpec)
  | .inl n => CSpec.query (.inl n)
  | .inr (.inl q) => Realize.cq q
  | .inr (.inr (.inl d)) => pure (tbl d)
  | .inr (.inr (.inr h)) => hashImpl g h

theorem handler_at (g : CompressionTables) (tbl : SecretTable vp (P g)) {α : Type}
    (oa : OracleComp (Lazy.OSpec (P g) (hS St Blk)) α) :
    simulateQ (instImpl₀ g.1) (simulateQ (handler g tbl) oa) =
      simulateQ (instImpl₀ g.1) (simulateQ (Lazy.tblImpl (gspec := hS St Blk) (PublicHash.impl (P g)) tbl) oa) := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind,simulateQ_spec_query,ih]
    congr 1
    rcases t with n | q | d | h
    · rfl
    · rfl
    · rfl
    · simp [handler,Lazy.tblImpl,hash_at]

variable (rand : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) (A : Forger)

noncomputable def forge (model : CompressionTables) (arity : ℕ) (tbl : SecretTable vp (P model))
    (L : List (Bytes 22 × List (Bytes 16))) (pk : Bytes 16) :=
  simulateQ (handler model tbl)
    (tcrMOpenP (vp := vp) (prims := P model) (fun k => rand k.pkSeed k.pkRoot)
      (PureCompression.typed Sha2Set.s128f A model model.2) L pk) >>= fun jm =>
    pure (classOut (P model) arity L jm)

theorem forge_at (g : CompressionTables) (seeds : ProbComp (Bytes 16)) (arity : ℕ)
    (tbl : SecretTable vp (P g)) (L : List (Bytes 22 × List (Bytes 16))) (pk : Bytes 16) :
    simulateQ (instImpl₀ g.1) (forge rand A g arity tbl L pk) =
      (bTcrArM arity (bytesToTyped (PureCompression.internalBytes Sha2Set.s128f rand seeds A g).toUnforgeableAdversary)).forge (tbl,L) pk := by
  let B := bytesToTyped (PureCompression.internalBytes Sha2Set.s128f rand seeds A g).toUnforgeableAdversary
  let r := fun (k : PublicKeyCore (P g).core) => rand k.pkSeed k.pkRoot
  have h := congrArg (simulateQ (instImpl₀ g.1)) (tcrM_phase2_open_eq (hS St Blk) arity B tbl L pk)
  rw [instImpl₀_liftM] at h
  rw [h]
  unfold forge
  rw [simulateQ_bind,simulateQ_bind,handler_at,← QueryImpl.simulateQ_compose,← QueryImpl.simulateQ_compose]
  have hf := tcrMOpenP_fusion (vp := vp) (prims := P g) r
    (instImpl₀ g.1 ∘ₛ Lazy.tblImpl (gspec := hS St Blk) (PublicHash.impl (P g)) tbl) g.1
    (fun _ => rfl) (PureCompression.typed Sha2Set.s128f A g g.2) L pk
  rw [hf,show (fun pk => simulateQ (instImpl g.1) (PureCompression.typed Sha2Set.s128f A g g.2 pk)) = B.main from
    funext (PureCompression.typed_at Sha2Set.s128f rand seeds A g)]
  rfl

private theorem step_bound (g : CompressionTables) (B ℓ : ℕ) (tbl : SecretTable vp (P g))
    (t : (Lazy.OSpec (vp := vp) (P g) (hS St Blk)).Domain) (ht : ¬ isBadIdx B ℓ t = true) :
    IsQueryBoundP (handler g tbl t) (fun i => i.isRight = true)
      ((if Lazy.kind t = .game then 1 else 0) + (if Tcr.isThIdx t = true then thashCost B else 0) +
        (if isHmsgIdx t = true then (ℓ+56)/64+4 else 0)) := by
  rcases t with n | q | d | h
  · exact (isQueryBoundP_query_iff _ _ _).2 fun h => by simp at h
  · exact cq_bound _
  · exact isQueryBoundP_pure _ _ _
  · cases h with
    | thash pk a xs =>
      have hx : xs.length ≤ B := by simpa only [isBadIdx,decide_eq_true_eq,not_lt] using ht
      simp only [Lazy.kind,Tcr.isThIdx,isHmsgIdx,ite_true,Bool.false_eq_true,ite_false,reduceCtorEq]
      exact ((thashC_bound pk a xs).mono (thashCost_mono hx)).mono (by omega)
    | hmsg r pk root m =>
      have hm : m.length ≤ ℓ := by simpa only [isBadIdx,decide_eq_true_eq,not_lt] using ht
      apply (hmsg_count r pk root m).mono
      simp [Lazy.kind,Tcr.isThIdx,isHmsgIdx]
      omega

def forgeBudget (q qs L : ℕ) :=
  q + (Lazy.keygenHashes vp + qs * Lazy.signHashes vp + (1 + Resources2.verifyHashes vp * 2)) *
    thashCost vp.params.len + (qs + 1) * ((L+257+56)/64+4)

theorem forge_count (g : CompressionTables) (arity : ℕ) (tbl : SecretTable vp (P g))
    (rows : List (Bytes 22 × List (Bytes 16))) (pk : Bytes 16) (q qs L : ℕ)
    (hq : ∀ pk, IsQueryBoundP (A.main pk) (fun i => PureCompression.retained isPortQP i = true) q)
    (hs : ∀ pk, IsQueryBoundP (A.main pk) (fun i => PureCompression.retained isSignQP i = true) qs)
    (hl : ∀ pk, IsQueryBoundP (A.main pk) (fun i => PureCompression.retained (isLongQP L) i = true) 0)
    (ho : ∀ pk z, z ∈ support (A.main pk) → z.1.1.length ≤ L)
    (hr : ∀ x ∈ rows, x.2.length ≤ vp.params.len) :
    IsQueryBoundP (forge rand A g arity tbl rows pk) (fun i => i.isRight = true) (forgeBudget q qs L) := by
  let f := PureCompression.typed Sha2Set.s128f A g g.2
  let r := fun (k : PublicKeyCore (P g).core) => rand k.pkSeed k.pkRoot
  have hB : ∀ xs : List (Bytes 16), OkLen vp xs → xs.length ≤ vp.params.len := by
    intro xs hx
    rcases hx with h|h|h|h <;> rw [h] <;> decide
  have cost := qb_simulateQ_classes (p₀ := fun t => isBadIdx vp.params.len (L+257) t = true)
    (p₁ := fun t => Lazy.kind t = .game) (p₂ := fun t => Tcr.isThIdx t = true)
    (p₃ := fun t => isHmsgIdx t = true) 1 (thashCost vp.params.len) ((L+257+56)/64+4)
    (step_bound g _ _ tbl)
    (tcrMOpenP_bad r f rows pk _ _ hB hr (PureCompression.typed_long _ A _ _ hl) (PureCompression.typed_out _ A _ _ ho))
    (tcrMOpenP_port r f rows pk q (PureCompression.typed_port _ A _ _ hq))
    (IsQueryBoundP.of_imp Tcr.isThIdx_kind (tcrMOpenP_hashes r f rows pk qs (PureCompression.typed_sign _ A _ _ hs)))
    (tcrMOpenP_hmsg r f rows pk qs (PureCompression.typed_sign _ A _ _ hs))
  unfold forge
  exact (isQueryBoundP_bind (m := 0) cost fun _ _ => isQueryBoundP_pure _ _ _).mono (by simp [forgeBudget])

end MIdeal.Class128f

#print axioms MIdeal.Class128f.hash_at
#print axioms MIdeal.Class128f.hash_count
#print axioms MIdeal.Class128f.forge_at
#print axioms MIdeal.Class128f.forge_count
