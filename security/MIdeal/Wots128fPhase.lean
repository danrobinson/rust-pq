import MIdeal.Class128fFixed
import MIdeal.Wots128f
import Ideal.Realize.WotsRealizers

/-! The SHA2-128f WOTS reduction exposes its signing, hash and external compression
queries. These programs bound the second phase of each of the three WOTS games.
The open-program equalities permit a fixed reference table for defining the program
and a separately sampled table for answering its compression queries. -/

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
abbrev State := (SecIdx → Bytes 16) × (List (Adrs × Bytes 16 × Vector (Bytes 16) vp.params.len × Vector (Bytes 16) vp.params.len) × Bytes 16)
abbrev PhaseState := State × List (Adrs × Bytes 16 × Vector (Bytes 16) vp.params.len × Vector (Bytes 16) vp.params.len)

noncomputable def udPhase (m : CompressionTables) (st : PhaseState) (pk : Bytes 16) : OracleComp CSpec Bool :=
  simulateQ (Class128f.handler m st.1.1) (wUdP (vp := vp) (prims := P m)
    (fun k => rand k.pkSeed k.pkRoot) (PureCompression.typed Sha2Set.s128f A m m.2)
    st.1.2.1 st.2 st.1.2.2 pk)

noncomputable def prePhase (m : CompressionTables) (st : PhaseState) (pk : Bytes 16) : OracleComp CSpec (ℕ × Bytes 16) :=
  simulateQ (Class128f.handler m st.1.1) (wPreP (vp := vp) (prims := P m)
    (fun k => rand k.pkSeed k.pkRoot) (PureCompression.typed Sha2Set.s128f A m m.2)
    st.1.2.1 st.2 st.1.2.2 pk)

noncomputable def tcrPhase (m : CompressionTables) (st : PhaseState) (pk : Bytes 16) : OracleComp CSpec (ℕ × Bytes 16) :=
  simulateQ (Class128f.handler m st.1.1) (wTcrP (vp := vp) (prims := P m)
    (fun k => rand k.pkSeed k.pkRoot) (PureCompression.typed Sha2Set.s128f A m m.2)
    st.1.2.1 st.2 st.1.2.2 pk)

private theorem run_bound (m : CompressionTables) (tbl : SecIdx → Bytes 16) {α : Type}
    (prog : OracleComp (Lazy.OSpec (P m) (hS St Blk)) α) (ℓ ports hashes messages : ℕ)
    (h0 : IsQueryBoundP prog (fun t => isBadIdx vp.params.len ℓ t = true) 0)
    (h1 : IsQueryBoundP prog (fun t => Lazy.kind t = .game) ports)
    (h2 : IsQueryBoundP prog (fun t => Lazy.kind t = .hash) hashes)
    (h3 : IsQueryBoundP prog (fun t => isHmsgIdx t = true) messages) :
    IsQueryBoundP (simulateQ (Class128f.handler m tbl) prog) (fun i => i.isRight = true)
      (ports + hashes * thashCost vp.params.len + messages*((ℓ+56)/64+4)) := by
  refine (qb_simulateQ_classes (p₂ := fun t => Tcr.isThIdx t = true) 1 (thashCost vp.params.len) ((ℓ+56)/64+4)
    (fun t ht => ?_) h0 h1 (IsQueryBoundP.of_imp Tcr.isThIdx_kind h2) h3).mono (by simp)
  rcases t with n | q | d | t
  · exact (isQueryBoundP_query_iff _ _ _).2 fun h => by simp at h
  · exact cq_bound _
  · exact isQueryBoundP_pure _ _ _
  · cases t with
    | thash pk a xs =>
      have len : xs.length ≤ vp.params.len := by simpa only [isBadIdx,decide_eq_true_eq,not_lt] using ht
      apply (Class128f.hash_count m (.thash pk a xs)).mono
      simpa only [Class128f.stepCost,Lazy.kind,Tcr.isThIdx,isHmsgIdx,ite_true,Bool.false_eq_true,
        ite_false,reduceCtorEq,Nat.zero_add,Nat.add_zero] using thashCost_mono len
    | hmsg r pk root msg =>
      have len : msg.length ≤ ℓ := by simpa only [isBadIdx,decide_eq_true_eq,not_lt] using ht
      apply (Class128f.hash_count m (.hmsg r pk root msg)).mono
      simp only [Class128f.stepCost,Lazy.kind,Tcr.isThIdx,isHmsgIdx,ite_true,Bool.false_eq_true,
        ite_false,reduceCtorEq,Nat.zero_add,Nat.add_zero]
      omega

def phaseBudget (answer q qs L : ℕ) :=
  q + (qs*wotsSignHistHashes vp + (wotsAnswerHashes vp + answer)) * thashCost vp.params.len +
    (qs+2)*((L+257+56)/64+4)

variable (m : CompressionTables) (q qs L : ℕ)
    (hq : ∀ pk, IsQueryBoundP (A.main pk) (fun i => PureCompression.retained isPortQP i = true) q)
    (hs : ∀ pk, IsQueryBoundP (A.main pk) (fun i => PureCompression.retained isSignQP i = true) qs)
    (hl : ∀ pk, IsQueryBoundP (A.main pk) (fun i => PureCompression.retained (isLongQP L) i = true) 0)
    (ho : ∀ pk z, z ∈ support (A.main pk) → z.1.1.length ≤ L)

private theorem okLen {xs : List (Bytes 16)} (h : OkLen vp xs) : xs.length ≤ vp.params.len := by
  rcases h with h|h|h|h <;> rw [h] <;> decide

include hq hs hl ho in
theorem ud_count (st : PhaseState) (pk : Bytes 16) :
    IsQueryBoundP (udPhase rand A m st pk) (fun i => i.isRight = true) (phaseBudget (wotsWinHashes vp) q qs L) := by
  let r := fun (k : PublicKeyCore (P m).core) => rand k.pkSeed k.pkRoot
  let f := PureCompression.typed Sha2Set.s128f A m m.2
  apply run_bound
  · exact wUdP_bad r f _ _ _ _ _ _ (fun _ => okLen)
      (PureCompression.typed_long _ A m _ hl _) (PureCompression.typed_out _ A m _ ho _)
  · exact wUdP_port r f _ _ _ _ (PureCompression.typed_port _ A m _ hq _)
  · exact wUdP_hashes r f _ _ _ _ (PureCompression.typed_sign _ A m _ hs _)
  · exact wUdP_hmsg r f _ _ _ _ (PureCompression.typed_sign _ A m _ hs _)

include hq hs hl ho in
theorem pre_count (st : PhaseState) (pk : Bytes 16) :
    IsQueryBoundP (prePhase rand A m st pk) (fun i => i.isRight = true) (phaseBudget (wotsPreHashes vp) q qs L) := by
  let r := fun (k : PublicKeyCore (P m).core) => rand k.pkSeed k.pkRoot
  let f := PureCompression.typed Sha2Set.s128f A m m.2
  apply run_bound
  · exact wPreP_bad r f _ _ _ _ _ _ (fun _ => okLen)
      (PureCompression.typed_long _ A m _ hl _) (PureCompression.typed_out _ A m _ ho _)
  · exact wPreP_port r f _ _ _ _ (PureCompression.typed_port _ A m _ hq _)
  · exact wPreP_hashes r f _ _ _ _ (PureCompression.typed_sign _ A m _ hs _)
  · exact wPreP_hmsg r f _ _ _ _ (PureCompression.typed_sign _ A m _ hs _)

include hq hs hl ho in
theorem tcr_count (st : PhaseState) (pk : Bytes 16) :
    IsQueryBoundP (tcrPhase rand A m st pk) (fun i => i.isRight = true) (phaseBudget (wotsTcrHashes vp) q qs L) := by
  let r := fun (k : PublicKeyCore (P m).core) => rand k.pkSeed k.pkRoot
  let f := PureCompression.typed Sha2Set.s128f A m m.2
  apply run_bound
  · exact wTcrP_bad r f _ _ _ _ _ _ (fun _ => okLen)
      (PureCompression.typed_long _ A m _ hl _) (PureCompression.typed_out _ A m _ ho _)
  · exact wTcrP_port r f _ _ _ _ (PureCompression.typed_port _ A m _ hq _)
  · exact wTcrP_hashes r f _ _ _ _ (PureCompression.typed_sign _ A m _ hs _)
  · exact wTcrP_hmsg r f _ _ _ _ (PureCompression.typed_sign _ A m _ hs _)

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
  (tbl : SecretTable v base)
  (read : QueryImpl (Lazy.OSpec base (hS St Blk)) (OracleComp CSpec))
  (he : ∀ t, simulateQ (instImpl₀ g) (read t) =
    simulateQ (instImpl₀ g) (Lazy.tblImpl (gspec := hS St Blk) (PublicHash.impl (withTH base T H)) tbl t))
  (hist hist2 : List (WotsGame.Entry base)) (root : base.Y) (pk : base.PkSeed)
set_option quotPrecheck false in
local notation "B" => bytesToTyped (vp := v) (prims := setPrf (withTH base T H) prf pm)
    (codec := trCodec _ prf pm codec) (optRand := fun k => r k.pkSeed k.pkRoot)
    (pkSeedDist := seeds) ⟨fun pk => simulateQ (instImpl g) (mb pk)⟩

include he in
set_option maxHeartbeats 1200000 in
theorem ud_open :
    simulateQ (instImpl₀ g) (simulateQ read (wUdP (vp := v) (prims := base) (fun k => r k.pkSeed k.pkRoot)
      (typedP codec mb) hist hist2 root pk)) =
      (rUd (prims := setPrf (withTH base T H) prf pm) seeds (Lazy.bWotsS B)).distinguish ((tbl,hist,root),hist2) pk := by
  let W := withTH base T H
  let rb := fun (k : PublicKeyCore base.core) => r k.pkSeed k.pkRoot
  let rs := fun (k : PublicKeyCore (setPrfC base.core prf pm)) => r k.pkSeed k.pkRoot
  let b := bytesToTyped (vp := v) (prims := W) (codec := codec) (optRand := rb)
    (pkSeedDist := seeds) ⟨fun pk => simulateQ (instImpl g) (mb pk)⟩
  have tr := rUd_distinguish_setPrf W prf pm codec rb rs (fun _ => rfl) seeds
      (fun pk => simulateQ (instImpl g) (mb pk)) ((tbl,hist,root),hist2) pk
  refine Eq.trans ?_ tr.symm
  have op := congrArg (simulateQ (instImpl₀ g)) (wotsUd_phase2_open_eq (gspec := hS St Blk)
    b tbl hist hist2 root pk)
  rw [instImpl₀_liftM] at op
  refine Eq.trans ?_ op.symm
  rw [Wots.simulateQ_comp,Wots.simulateQ_comp,funext he]
  let φ := fun t => simulateQ (instImpl₀ g) (Lazy.tblImpl (gspec := hS St Blk) (PublicHash.impl W) tbl t)
  have hf := wUdP_fusion (vp := v) (prims := W) rb seeds φ g (fun _ => rfl)
    (typedP (vp := v) (prims := W) codec mb) hist hist2 root pk
  have same : instForger (prims := W) rb seeds g (typedP codec mb) = b := by
    unfold instForger
    exact congrArg _ (funext (typedP_inst (prims := W) codec rb seeds g mb))
  rw [same] at hf
  kexact hf

include he in
set_option maxHeartbeats 1200000 in
theorem pre_open :
    simulateQ (instImpl₀ g) (simulateQ read (wPreP (vp := v) (prims := base) (fun k => r k.pkSeed k.pkRoot)
      (typedP codec mb) hist hist2 root pk)) =
      (rPre (prims := setPrf (withTH base T H) prf pm) seeds (Lazy.bWotsS B)).invert ((tbl,hist,root),hist2) pk := by
  let W := withTH base T H
  let rb := fun (k : PublicKeyCore base.core) => r k.pkSeed k.pkRoot
  let rs := fun (k : PublicKeyCore (setPrfC base.core prf pm)) => r k.pkSeed k.pkRoot
  let b := bytesToTyped (vp := v) (prims := W) (codec := codec) (optRand := rb)
    (pkSeedDist := seeds) ⟨fun pk => simulateQ (instImpl g) (mb pk)⟩
  have tr := rPre_invert_setPrf W prf pm codec rb rs (fun _ => rfl) seeds
      (fun pk => simulateQ (instImpl g) (mb pk)) ((tbl,hist,root),hist2) pk
  refine Eq.trans ?_ tr.symm
  have op := congrArg (simulateQ (instImpl₀ g)) (wotsPre_phase2_open_eq (gspec := hS St Blk)
    b tbl hist hist2 root pk)
  rw [instImpl₀_liftM] at op
  refine Eq.trans ?_ op.symm
  rw [Wots.simulateQ_comp,Wots.simulateQ_comp,funext he]
  let φ := fun t => simulateQ (instImpl₀ g) (Lazy.tblImpl (gspec := hS St Blk) (PublicHash.impl W) tbl t)
  have hf := wPreP_fusion (vp := v) (prims := W) rb seeds φ g (fun _ => rfl)
    (typedP (vp := v) (prims := W) codec mb) hist hist2 root pk
  have same : instForger (prims := W) rb seeds g (typedP codec mb) = b := by
    unfold instForger
    exact congrArg _ (funext (typedP_inst (prims := W) codec rb seeds g mb))
  rw [same] at hf
  kexact hf

include he in
set_option maxHeartbeats 1200000 in
theorem tcr_open :
    simulateQ (instImpl₀ g) (simulateQ read (wTcrP (vp := v) (prims := base) (fun k => r k.pkSeed k.pkRoot)
      (typedP codec mb) hist hist2 root pk)) =
      (rTcrT (prims := setPrf (withTH base T H) prf pm) seeds (Lazy.bWotsS B)).forge ((tbl,hist,root),hist2) pk := by
  let W := withTH base T H
  let rb := fun (k : PublicKeyCore base.core) => r k.pkSeed k.pkRoot
  let rs := fun (k : PublicKeyCore (setPrfC base.core prf pm)) => r k.pkSeed k.pkRoot
  let b := bytesToTyped (vp := v) (prims := W) (codec := codec) (optRand := rb)
    (pkSeedDist := seeds) ⟨fun pk => simulateQ (instImpl g) (mb pk)⟩
  have tr := rTcrT_forge_setPrf W prf pm codec rb rs (fun _ => rfl) seeds
      (fun pk => simulateQ (instImpl g) (mb pk)) ((tbl,hist,root),hist2) pk
  refine Eq.trans ?_ tr.symm
  have op := congrArg (simulateQ (instImpl₀ g)) (wotsTcrT_phase2_open_eq (gspec := hS St Blk)
    b tbl hist hist2 root pk)
  rw [instImpl₀_liftM] at op
  refine Eq.trans ?_ op.symm
  rw [Wots.simulateQ_comp,Wots.simulateQ_comp,funext he]
  let φ := fun t => simulateQ (instImpl₀ g) (Lazy.tblImpl (gspec := hS St Blk) (PublicHash.impl W) tbl t)
  have hf := wTcrP_fusion (vp := v) (prims := W) rb seeds φ g (fun _ => rfl)
    (typedP (vp := v) (prims := W) codec mb) hist hist2 root pk
  have same : instForger (prims := W) rb seeds g (typedP codec mb) = b := by
    unfold instForger
    exact congrArg _ (funext (typedP_inst (prims := W) codec rb seeds g mb))
  rw [same] at hf
  kexact hf
end Transport
end MIdeal.Wots128f
#print axioms MIdeal.Wots128f.ud_count
#print axioms MIdeal.Wots128f.ud_open
#print axioms MIdeal.Wots128f.pre_count
#print axioms MIdeal.Wots128f.pre_open
#print axioms MIdeal.Wots128f.tcr_count
#print axioms MIdeal.Wots128f.tcr_open
