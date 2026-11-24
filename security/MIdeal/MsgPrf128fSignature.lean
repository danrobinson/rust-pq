import MIdeal.Wots128fBound
import MIdeal.MsgPrf128f
import Ideal.Realize.MsgReal

/-! SHA2-128f message-PRF bounds for the byte-level SUF and EUF distinguishers.
The open programs realize the actual reductions for each pair of tables, and the
HMAC bound is applied after charging their compression and PRF queries. -/

namespace MIdeal.Msg128f
open Ideal Ideal.Realize MLink SLHDSA SLHDSA.Security OracleComp OracleSpec Reduction Reduction.Open
open Ideal.Realize.Msg Reduction.Lazy Ideal.Transport ENNReal
open Class128f (vp P)
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

private noncomputable def raw {v : ValidatedParams} (base : Primitives v.params)
    [SampleableType base.Y] [DecidableEq base.Y] [DecidableEq base.PkSeed] [DecidableEq base.AdrsKey]
    (strong : Bool) (rand : PublicKeyCore base.core → ProbComp base.Y)
    (seeds : ProbComp base.PkSeed) (f : PortForgerProg v base) : OracleComp (OP base) Bool :=
  if strong then msgOpenWVP rand seeds sufCheckO f else msgOpenVP rand seeds f

private noncomputable def actual {v : ValidatedParams} (base : Primitives v.params)
    [SampleableType base.SkSeed] [SampleableType base.SkPrf] [SampleableType base.Y]
    [DecidableEq base.Y] [DecidableEq base.PkSeed] [DecidableEq base.AdrsKey] [Inhabited base.Y]
    {rand : PublicKeyCore base.core → ProbComp base.Y} {seeds : ProbComp base.PkSeed}
    (strong : Bool) (f : Forger v base rand seeds) : MsgPrfAdv base :=
  if strong then bPrfMsgWL sufCheck f else bPrfMsgL f

theorem open_at (strong : Bool) (he : ∀ t, simulateQ (instImpl₀ g) (hash t) =
    pure (f := ProbComp) (α := (publicHashSpec base.core).Range t) (answers base T H t)) :
    actual (setPrf (withTH base T H) prf pm) strong B =
      simulateQ (instImpl g) (simulateQ (interpC (G := msgG base) hash) (lazyRes
        (raw base strong (fun k => r k.pkSeed k.pkRoot) seeds (typedC codec default mb)))) := by
  let W := withTH base T H
  let rb := fun (k : PublicKeyCore base.core) => r k.pkSeed k.pkRoot
  let rs := fun (k : PublicKeyCore (setPrfC base.core prf pm)) => r k.pkSeed k.pkRoot
  let b := bytesToTyped (vp := v) (prims := W) (codec := codec) (optRand := rb)
    (pkSeedDist := seeds) ⟨fun pk => simulateQ (instImpl g) (mb pk)⟩
  have fb := bytesToTyped_inst (prims := W) (optRand := rb) (pkSeedDist := seeds) codec g mb
  have hh : ∀ t, simulateQ (instImpl₀ g) (hash t) = pure (f := ProbComp)
      (α := (publicHashSpec base.core).Range t) (PublicHash.impl W t) := by
    intro t
    cases t <;> apply he
  have final := lazyRun_portR (G := msgG base) g (PublicHash.impl W) hash hh
    (raw base strong rb seeds (typedC codec default mb))
  refine Eq.trans ?_ final
  cases strong with
  | false =>
    have tr := bPrfMsgL_setPrf W prf pm codec rb rs (fun _ => rfl) seeds (fun pk => simulateQ (instImpl g) (mb pk))
    refine tr.trans ?_
    have openEq := (lazyRun_msgOpenV (prims := W) b).symm
    refine openEq.trans ?_
    dsimp only [b]
    rw [fb,← msgOpenVP_fusion (prims := W) rb seeds g (typedC codec default mb)]
    kexact congrArg (fun o => lazyRun (PublicHash.impl W) (simulateQ (portR g) o))
      (msgOpenVP_withTH (prims := base) rb seeds T H (typedC codec default mb))
  | true =>
    have tr := bPrfMsgWL_setPrf W prf pm codec rb rs (fun _ => rfl) seeds (fun pk => simulateQ (instImpl g) (mb pk))
    refine tr.trans ?_
    have openEq := (lazyRun_msgOpenWV_sufCheck (prims := W) b).symm
    refine openEq.trans ?_
    dsimp only [b]
    rw [fb,← msgOpenWVP_fusion (prims := W) rb seeds g sufCheckO (typedC codec default mb)]
    kexact congrArg (fun o => lazyRun (PublicHash.impl W) (simulateQ (portR g) o))
      (msgOpenWVP_withTH (prims := base) rb seeds T H (typedC codec default mb))
end Transport
attribute [local irreducible] wotsChainTargets wotsStepTargets wotsStepTargetsT Lazy.structSecIdx Lazy.sparseTable wotsInsts
noncomputable local instance modelY (g : CompressionTables) : SampleableType (P g).Y := sampY128
local instance modelSk (g : CompressionTables) : SampleableType (P g).SkSeed := inferInstanceAs (SampleableType (Bytes 16))
local instance modelPrf (g : CompressionTables) : SampleableType (P g).SkPrf := inferInstanceAs (SampleableType (Bytes 16))
local instance modelInh (g : CompressionTables) : Inhabited (P g).Y := inferInstanceAs (Inhabited (Bytes 16))
local instance modelEqY (g : CompressionTables) : DecidableEq (P g).Y := inferInstanceAs (DecidableEq (Bytes 16))
local instance modelEqPk (g : CompressionTables) : DecidableEq (P g).PkSeed := inferInstanceAs (DecidableEq (Bytes 16))
local instance modelEqAd (g : CompressionTables) : DecidableEq (P g).AdrsKey := inferInstanceAs (DecidableEq (Bytes 22))
local instance modelFinite (g : CompressionTables) : Fintype (P g).Y := inferInstanceAs (Fintype (Bytes 16))

variable (rand : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) (A : PureCompression.Forger)
private def th (g : CompressionTables) : Bytes 16 → Bytes 22 → List (Bytes 16) → Bytes 16 := (P g).Thash
private def hm (g : CompressionTables) : Bytes 16 → Bytes 16 → Bytes 16 → List Byte → Bytes 34 := (P g).Hmsg
private def prf (g : CompressionTables) : Bytes 16 → Bytes 16 → Adrs → Bytes 16 := (P g).PRF
private def pm (g : CompressionTables) : Bytes 16 → Bytes 16 → List Byte → Bytes 16 := (P g).PRFmsg
variable (seeds : ProbComp (Bytes 16))
noncomputable def program (strong : Bool) (m : CompressionTables) : MsgPrfAdvI :=
  simulateQ (interpC (G := msgG (P m)) (Class128f.hashImpl m)) (lazyRes (raw (P m) strong
    (fun k => rand k.pkSeed k.pkRoot) seeds (typedC (PureCompression.codec Sha2Set.s128f m) default (A.at512 m.2).toI.main)))

noncomputable abbrev adversary (strong : Bool) (g : CompressionTables) :=
  actual (P g) strong (Wots128f.reduced rand A seeds g)

private theorem read_at (m g : CompressionTables) (t : (publicHashSpec (P m).core).Domain) :
    simulateQ (instImpl₀ g.1) (Class128f.hashImpl m t) =
      pure (f := ProbComp) (α := (publicHashSpec (P m).core).Range t) (answers (P m) (th g) (hm g) t) := by
  cases t with
  | thash pk a xs =>
    exact (thashC_inst g.1 pk a xs).trans (congrArg (fun y => pure (f := ProbComp) y)
      ((thG_shape g.1 pk a xs).trans (Hash128f.shape g pk a xs).symm))
  | hmsg r pk root msg => exact Class128f.hmsg_at g r pk root msg

private noncomputable abbrev canonical (strong : Bool) (ref : CF St Blk) (g : CompressionTables)
    (f : Bytes 16 → Bytes 16 → Adrs → Bytes 16) (p : Bytes 16 → Bytes 16 → List Byte → Bytes 16) :=
  let m : CompressionTables := (ref,g.2)
  open_at (v := vp) (P m) (th g) (hm g) rand seeds (PureCompression.codec Sha2Set.s128f m)
    (A.at512 g.2).toI.main g.1 f p (Class128f.hashImpl m) strong (read_at m g)

/-- Keep the closed SHA-256 functions opaque while the kernel checks the open
program, then rewrite by the defining equality. -/
private noncomputable def selected {α : Type} (x : α) : {y : α // y = x} :=
  Classical.choice ⟨⟨x,rfl⟩⟩

set_option maxHeartbeats 450000 in
theorem main_fixed (strong : Bool) (ref : CF St Blk) (g : CompressionTables) :
    adversary rand A seeds strong g = (program rand A seeds strong (ref,g.2)).inst g.1 := by
  let m : CompressionTables := (ref,g.2)
  have h := canonical rand A seeds strong ref g (selected (prf g)).val (selected (pm g)).val
  rw [(selected (prf g)).property,(selected (pm g)).property] at h
  dsimp only [program,PrfAdvI.inst,adversary,Wots128f.reduced,PureCompression.typed,PureCompression.internalBytes,PureCompression.codec,
    SignatureAlg.StrongUnforgeableAdversary.toUnforgeableAdversary,
    trCodec,setPrf,setPrfC,withTH,m,th,hm,prf,pm,P,tablePrimitives,sha2PrimitivesMixed,
    vp,msgG,modelY,modelSk,modelPrf,modelInh,modelEqY,modelEqPk,modelEqAd,modelFinite] at h ⊢
  kexact h
variable (m : CompressionTables)
abbrev hashCount (qs : ℕ) := keygenHashes vp + qs * signHashes vp + (1 + Resources2.verifyHashes vp)
def budget (q qs L : ℕ) := q * 1 + hashCount qs * thashCost vp.params.len + (qs + 1) * ((L+257+56)/64+4)

private noncomputable def interp (m : CompressionTables) (o : OracleComp (OP (P m)) Bool) : MsgPrfAdvI :=
  simulateQ (interpC (G := msgG (P m)) (Class128f.hashImpl m)) (lazyRes o)

variable (o : OracleComp (OP (P m)) Bool) (q qs L : ℕ)
private theorem interp_comp (hport : IsQueryBoundP o pPort q) (hth : IsQueryBoundP o pTh (hashCount qs))
    (hhm : IsQueryBoundP o pHm (qs + 1)) (hbad : IsQueryBoundP o (pBad vp.params.len (L+257)) 0) :
    IsQueryBoundP (interp m o) (fun i => isCompQ i = true) (budget q qs L) := by
  unfold interp
  refine qb_simulateQ_classes (p₀ := pBad vp.params.len (L+257)) (p₁ := pPort) (p₂ := pTh) (p₃ := pHm)
    1 (thashCost vp.params.len) (((L+257+56)/64+4)) (fun t ht => ?_)
    (lazyRes_bound_liftP _ _ o 0 hbad) (lazyRes_bound_liftP _ _ o _ hport)
    (lazyRes_bound_liftP _ _ o _ hth) (lazyRes_bound_liftP _ _ o _ hhm)
  rcases t with n | (q | d) | (u | h)
  · exact (isQueryBoundP_query_iff _ _ _).2 fun h => by simp [isCompQ] at h
  · exact (isQueryBoundP_query_iff _ _ _).2 fun _ => by simp [liftP]
  · exact (isQueryBoundP_query_iff _ _ _).2 fun h => by simp [isCompQ] at h
  · exact (liftM_zero (X := hS St Blk + msgG (P m)) ($ᵗ (P m).Y) (fun i => isCompQ i = true)
      fun n => by simp [isCompQ]).mono (Nat.zero_le _)
  · rcases h with ⟨pk, a, xs⟩ | ⟨R, pk, root, M⟩
    · have hx : xs.length ≤ vp.params.len := by
        simp only [pBad, liftP, longH, decide_eq_true_eq, not_lt] at ht
        exact ht
      refine (cEmb_bound (X := msgG (P m)) _ _ (thashC_bound pk a xs) (fun i => isCompQ i = true)
        (fun _ => rfl) (fun _ => by simp [isCompQ])).mono ?_
      simp only [liftP, isTh, isHm, ite_true, ite_false]
      exact (Nat.add_zero _).le.trans (thashCost_mono hx)
    · have hM : M.length ≤ (L+257) := by
        simp only [pBad, liftP, longH, decide_eq_true_eq, not_lt] at ht
        exact ht
      refine (cEmb_bound (X := msgG (P m)) _ _ (Class128f.hmsg_count R pk root M) (fun i => isCompQ i = true)
        (fun _ => rfl) (fun _ => by simp [isCompQ])).mono ?_
      simp only [liftP,isTh,isHm,ite_true,ite_false,Nat.zero_add]
      omega

/-- `PRF_msg` oracle queries of `interpC (Class128f.hashImpl m) (lazyRes o)`. -/
private theorem interp_prf (hmsg : IsQueryBoundP o pMsg qs) :
    IsQueryBoundP (interp m o) (fun i => isPrfQ i = true) qs := by
  unfold interp
  refine IsQueryBoundP.simulateQ_of_step (lazyRes_bound_liftP _ _ o _ hmsg) (fun t ht => ?_)
    (fun t ht => ?_)
  · rcases t with n | (q | d) | (u | h)
    · simp [liftP] at ht
    · simp [liftP] at ht
    · exact (isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos
    · simp [liftP] at ht
    · simp [liftP] at ht
  · rcases t with n | (q | d) | (u | h)
    · exact (isQueryBoundP_query_iff _ _ _).2 fun h => by simp [isPrfQ] at h
    · exact (isQueryBoundP_query_iff _ _ _).2 fun h => by simp [isPrfQ] at h
    · simp [liftP] at ht
    · exact liftM_zero (X := hS St Blk + msgG (P m)) ($ᵗ (P m).Y) (fun i => isPrfQ i = true)
        fun n => by simp [isPrfQ]
    · exact isQueryBoundP_simulateQ_zero _ fun t => by
        rcases t with n | c
        · exact (isQueryBoundP_query_iff _ _ _).2 fun h => by simp [isPrfQ] at h
        · exact (isQueryBoundP_query_iff _ _ _).2 fun h => by simp [isPrfQ] at h

private theorem interp_len (hbad : IsQueryBoundP o (pBad vp.params.len (L+257)) 0) :
    AllQueriesSatisfy (interp m o) (msgLenLe (L+257)) := by
  refine (isQueryBoundP_zero_iff _ (msgLenLe (L+257))).1
    (IsQueryBoundP.of_imp (p' := fun t => longQ (L+257) t = true) (fun t ht => ?_) ?_)
  · rcases t with n | q | d
    · simp [msgLenLe] at ht
    · simp [msgLenLe] at ht
    · simp only [msgLenLe, not_le] at ht
      simpa [longQ] using ht
  unfold interp
  have hq0 : ∀ n, ¬ longQ (Y := (P m).Y) (L+257) (.inl n) = true := fun n => by simp [longQ]
  have hq1 : ∀ c, ¬ longQ (Y := (P m).Y) (L+257) (.inr (.inl c)) = true := fun c => by simp [longQ]
  refine IsQueryBoundP.simulateQ_of_step (q := fun t => longQ (L+257) t = true) (impl := interpC (G := msgG (P m)) (Class128f.hashImpl m))
    (lazyRes_bound_liftP _ _ o 0 hbad) (fun t ht => ?_) (fun t ht => ?_)
  · rcases t with n | (q | d) | (u | h)
    · simp [liftP] at ht
    · simp [liftP, longG] at ht
    · exact (isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos
    · simp [liftP] at ht
    · exact (cEmb_zero (Xs := msgG (P m)) _ (fun t => longQ (Y := (P m).Y) (L+257) t = true) hq0 hq1).mono
        (Nat.zero_le _)
  · rcases t with n | (q | d) | (u | h)
    · exact (isQueryBoundP_query_iff _ _ _).2 fun h => absurd h (hq0 n)
    · exact (isQueryBoundP_query_iff _ _ _).2 fun h => absurd h (hq1 q)
    · have hd : d.2.length ≤ (L+257) := by
        simp only [liftP, longG, decide_eq_true_eq, not_lt] at ht
        exact ht
      exact (isQueryBoundP_query_iff _ _ _).2 fun h => by simp [longQ] at h; omega
    · exact liftM_zero (X := hS St Blk + msgG (P m)) ($ᵗ (P m).Y) (fun t => longQ (Y := (P m).Y) (L+257) t = true) hq0
    · exact cEmb_zero (Xs := msgG (P m)) _ (fun t => longQ (Y := (P m).Y) (L+257) t = true) hq0 hq1

private theorem ok_len (xs : List (P m).Y) (h : OkLen vp xs) : xs.length ≤ vp.params.len := by
  rcases h with h|h|h|h <;> rw [h] <;> decide

variable (strong : Bool)
    (hq : ∀ pk, IsQueryBoundP (A.main pk) (fun i => PureCompression.retained isPortQP i = true) q)
    (hs : ∀ pk, IsQueryBoundP (A.main pk) (fun i => PureCompression.retained isSignQP i = true) qs)
    (hl : ∀ pk, IsQueryBoundP (A.main pk) (fun i => PureCompression.retained (isLongQP L) i = true) 0)
    (ho : ∀ pk z, z ∈ support (A.main pk) → z.1.1.length ≤ L)

include hq hs hl ho in
theorem counts :
    IsQueryBoundP (program rand A seeds strong m) (fun i => isCompQ i = true) (budget q qs L) ∧
    IsQueryBoundP (program rand A seeds strong m) (fun i => isPrfQ i = true) qs ∧
    AllQueriesSatisfy (program rand A seeds strong m) (msgLenLe (L+257)) := by
  let f := PureCompression.typed Sha2Set.s128f A m m.2
  let r := fun (k : PublicKeyCore (P m).core) => rand k.pkSeed k.pkRoot
  have bounds : PortBounds f q qs (L+257) :=
    ⟨PureCompression.typed_port _ A m _ hq, PureCompression.typed_sign _ A m _ hs,
      PureCompression.typed_long _ A m _ hl, PureCompression.typed_out _ A m _ ho⟩
  unfold program
  rw [← typedP_eq_typedC (prims := P m)]
  cases strong with
  | false =>
    let o := msgOpenVP (prims := P m) r seeds f
    have hp := msgOpenVP_port r seeds bounds
    have hm := msgOpenVP_msg r seeds bounds
    have hh := msgOpenVP_hash r seeds bounds
    have hd := msgOpenVP_hm r seeds bounds
    have hb := msgOpenVP_bad r seeds bounds vp.params.len (ok_len m)
    exact ⟨interp_comp m o q qs L hp (IsQueryBoundP.of_imp pTh_imp hh) hd hb,
      interp_prf m o qs hm, interp_len m o L hb⟩
  | true =>
    let o := msgOpenWVP (prims := P m) r seeds sufCheckO f
    have hp := msgOpenWVP_port r seeds bounds
    have hm := msgOpenWVP_msg r seeds bounds
    have hh := msgOpenWVP_hash r seeds bounds
    have hd := msgOpenWVP_hm r seeds bounds
    have hb := msgOpenWVP_bad r seeds bounds vp.params.len (ok_len m)
    exact ⟨interp_comp m o q qs L hp (IsQueryBoundP.of_imp pTh_imp hh) hd hb,
      interp_prf m o qs hm, interp_len m o L hb⟩
noncomputable def loss (q qs L : ℕ) : ℝ≥0∞ :=
  let Q := budget q qs L
  2*(Q:ℝ≥0∞)/2^128 + (((Q + qs*((L+257+24)/64+1)+2)^2 : ℕ) : ℝ≥0∞)/2^256

include hq hs hl ho in
theorem term :
    PureCompression.average (fun g => msgRealPr (prims := P g) (adversary rand A seeds strong g)) ≤
      PureCompression.average (fun g => msgIdealPr (prims := P g) (adversary rand A seeds strong g)) + loss q qs L := by
  let I (other : CF Chain512 Block512) := cfAvg fun c =>
    msgIdealPr (prims := P (c,other)) (adversary rand A seeds strong (c,other))
  have bound (other : CF Chain512 Block512) :
      (cfAvg fun c => msgRealPr (prims := P (c,other)) (adversary rand A seeds strong (c,other))) ≤
        I other + loss q qs L := by
    let ref : CompressionTables := (default,other)
    let D := program rand A seeds strong ref
    have real (c : CF St Blk) := congrArg evalDist (congrArg
      (fun a : MsgPrfAdv (P (c,other)) => (msgPrf vp (P (c,other))).prfRealExperiment a)
      (main_fixed rand A seeds strong ref.1 (c,other)))
    have ideal (c : CF St Blk) := congrArg evalDist (congrArg
      (fun a : MsgPrfAdv (P (c,other)) => PRFScheme.prfIdealExperiment a)
      (main_fixed rand A seeds strong ref.1 (c,other)))
    have re := cfAvg_of_evalDist_eq real
    have ie := cfAvg_of_evalDist_eq ideal
    obtain ⟨hc,hp,hl'⟩ := counts rand A seeds ref q qs L strong hq hs hl ho
    have hh := (msg_prf_128f other D (budget q qs L) qs (L+257) hc hp hl').1
    apply re.le.trans
    apply le_trans ?_ (add_le_add ie.symm.le (le_refl (loss q qs L)))
    dsimp only [loss,ref,D,msgIdealI,msgReal128f] at hh ⊢
    kexact hh
  apply (cfAvg_mono bound).trans
  rw [cfAvg_add]
  apply add_le_add le_rfl
  let _ : MeasurableSpace (CF Chain512 Block512) := ⊤
  unfold cfAvg
  rw [MeasureTheory.lintegral_const]
  exact mul_le_of_le_one_right' (evalDist_apply_univ_le_one _)

end MIdeal.Msg128f
#print axioms MIdeal.Msg128f.open_at
#print axioms MIdeal.Msg128f.main_fixed
#print axioms MIdeal.Msg128f.counts

#print axioms MIdeal.Msg128f.term
