import MIdeal.Wots128fBound
import MIdeal.MsgPrf128f
import MIdeal.SkPrf
import Ideal.Realize.PrfReal
import Ideal.Realize.MsgReal

/-! The restricted secret-address PRF distinguisher obtained from a SHA2-128f byte forger, for both EUF-CMA and SUF-CMA. -/
namespace MIdeal.Secret128f
open Ideal Ideal.Realize MLink SLHDSA SLHDSA.Security OracleComp OracleSpec Reduction Reduction.Open
open Ideal.Realize.Msg Reduction.Lazy Ideal.Transport ENNReal
open Class128f (vp P)
open Ideal.Realize.Prf
section Handler
variable {p : Params} (base : Primitives p) (D : Type)
def closing (ans : QueryImpl (HSpec base) Id) : QueryImpl (PSpec base D) (OracleComp (unifSpec + (D →ₒ base.Y)))
  | .inl n => liftM (liftM (unifSpec.query n) : ProbComp _)
  | .inr (.inl d) => PRFScheme.functionQuery d
  | .inr (.inr x) => pure (ans x)

def handler (hash : QueryImpl (HSpec base) (OracleComp CSpec)) :
    QueryImpl (Ideal.Realize.Prf.QSpec base D) (OracleComp (unifSpec + (hS St Blk + (D →ₒ base.Y))))
  | .inl n => (unifSpec + (hS St Blk + (D →ₒ base.Y))).query (.inl n)
  | .inr (.inl (.inl q)) => (unifSpec + (hS St Blk + (D →ₒ base.Y))).query (.inr (.inl q))
  | .inr (.inl (.inr d)) => (unifSpec + (hS St Blk + (D →ₒ base.Y))).query (.inr (.inr d))
  | .inr (.inr q) => simulateQ cEmb (hash q)

theorem run_at {α : Type} (g : CF St Blk) (ans : QueryImpl (HSpec base) Id)
    (hash : QueryImpl (HSpec base) (OracleComp CSpec))
    (he : ∀ t, simulateQ (instImpl₀ g) (hash t) = pure (f := ProbComp) (α := (HSpec base).Range t) (ans t))
    (o : OracleComp (Ideal.Realize.Prf.QSpec base D) α) :
    simulateQ (closing base D ans) (simulateQ (portP (prims := base) (D := D) g) o) =
      simulateQ (instImpl g) (simulateQ (handler base D hash) o) := by
  refine simulateQ_comm_of_step _ _ _ _ (fun t => ?_) o
  rcases t with n | (q|d) | t
  · simp only [portP,handler,simulateQ_spec_query]; rfl
  · simp only [portP,handler,simulateQ_pure,simulateQ_spec_query]; rfl
  · simp only [portP,handler,simulateQ_spec_query]; rfl
  · simp only [portP,handler,simulateQ_spec_query,instImpl_cEmb,he,liftM_pure]
    rfl
end Handler

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
  (hash : QueryImpl (HSpec base) (OracleComp CSpec))

private def answers : QueryImpl (publicHashSpec base.core) Id
  | .thash pk a xs => T pk a xs
  | .hmsg a b c m => H a b c m

set_option quotPrecheck false in
local notation "B" => bytesToTyped (vp := v) (prims := setPrf (withTH base T H) prf pm)
    (codec := trCodec _ prf pm codec) (optRand := fun k => r k.pkSeed k.pkRoot)
    (pkSeedDist := seeds) ⟨fun pk => simulateQ (instImpl g) (mb pk)⟩

private def answersH : QueryImpl (HSpec base) Id
  | .inl q => answers base T H q
  | .inr a => pm a.1 a.2.1 a.2.2

private noncomputable def raw {v : ValidatedParams} (base : Primitives v.params)
    [SampleableType base.SkPrf] [Inhabited base.Y] [DecidableEq base.Y] [DecidableEq base.PkSeed]
    (strong : Bool) (rand : PublicKeyCore base.core → ProbComp base.Y)
    (seeds : ProbComp base.PkSeed) (f : PortForgerProg v base) :=
  if strong then bPrfWCOpenP rand seeds sufCheckOpen f else bPrfCOpenP rand seeds f

private noncomputable def actual {v : ValidatedParams} (base : Primitives v.params)
    [SampleableType base.SkSeed] [SampleableType base.SkPrf] [SampleableType base.Y]
    [DecidableEq base.Y] [DecidableEq base.PkSeed] [DecidableEq base.AdrsKey] [Inhabited base.Y]
    {rand : PublicKeyCore base.core → ProbComp base.Y} {seeds : ProbComp base.PkSeed}
    (strong : Bool) (f : Forger v base rand seeds) : PRFScheme.PRFAdversary (base.PkSeed × SkAdrs v) base.Y :=
  if strong then bPrfWC sufCheck f else bPrfC f

theorem open_at (strong : Bool) (he : ∀ t, simulateQ (instImpl₀ g) (hash t) =
    pure (f := ProbComp) (α := (HSpec base).Range t) (answersH base T H pm t)) :
    actual (setPrf (withTH base T H) prf pm) strong B =
      simulateQ (instImpl g) (simulateQ (handler base (base.PkSeed × SkAdrs v) hash)
        (raw base strong (fun k => r k.pkSeed k.pkRoot) seeds (typedC codec default mb))) := by
  let W := withTH base T H
  let V := setPrf W prf pm
  let rb := fun (k : PublicKeyCore base.core) => r k.pkSeed k.pkRoot
  let rs := fun (k : PublicKeyCore (setPrfC base.core prf pm)) => r k.pkSeed k.pkRoot
  let D := base.PkSeed × SkAdrs v
  have fb := bytesToTyped_inst (prims := W) (optRand := rb) (pkSeedDist := seeds) codec g mb
  have final := run_at base D g (answersH base T H pm) hash he
    (raw base strong rb seeds (typedC codec default mb))
  refine Eq.trans ?_ final
  have close (X : OracleComp (PSpec W D) Bool) :
      simulateQ (closeImpl V D) (castP' W prf pm D X) = simulateQ (closing base D (answersH base T H pm)) X := by
    krfl
  cases strong with
  | false =>
    refine (bPrfCOpen_close (prims := V) B).symm.trans ?_
    have e := bPrfCOpen_setPrf W prf pm rb rs (fun _ => rfl) codec seeds
      (fun pk => simulateQ (instImpl g) (mb pk))
    have tr := congrArg (fun x => simulateQ (closeImpl V D) (castP' W prf pm D x)) e
    refine (?_ : _ = _).trans (tr.trans ?_)
    · krfl
    refine (close _).trans ?_
    rw [fb, ← bPrfCOpenP_fusion (prims := W) rb seeds g (typedC codec default mb)]
    kexact congrArg (fun o => simulateQ (closing base D (answersH base T H pm)) (simulateQ (portP g) o))
      (bPrfCOpenP_withTH (prims := base) (optRand := rb) (pkSeedDist := seeds) T H (typedC codec default mb))
  | true =>
    refine (bPrfWCOpen_close_suf (prims := V) B).symm.trans ?_
    have e := bPrfWCOpen_setPrf W prf pm rb rs (fun _ => rfl) codec seeds
      (fun pk => simulateQ (instImpl g) (mb pk))
    have tr := congrArg (fun x => simulateQ (closeImpl V D) (castP' W prf pm D x)) e
    refine (?_ : _ = _).trans (tr.trans ?_)
    · krfl
    refine (close _).trans ?_
    rw [bytesToTypedS_inst (prims := W) (optRand := rb) (pkSeedDist := seeds) codec g mb, ← bPrfWCOpenP_fusion (prims := W) rb seeds g sufCheckOpen (typedC codec default mb)]
    kexact congrArg (fun o => simulateQ (closing base D (answersH base T H pm)) (simulateQ (portP g) o))
      (bPrfWCOpenP_withTH (prims := base) (optRand := rb) (pkSeedDist := seeds) T H (typedC codec default mb))
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
private def hashProgram (m : CompressionTables) : QueryImpl (HSpec (P m)) (OracleComp CSpec)
  | .inl q => Class128f.hashImpl m q
  | .inr t => prfMsgC t.1 t.2.1 t.2.2

noncomputable def program (strong : Bool) (m : CompressionTables) : PrfAdvI St Blk (Bytes 16) (SkAdrs vp) (Bytes 16) :=
  simulateQ (handler (P m) (Bytes 16 × SkAdrs vp) (hashProgram m)) (raw (P m) strong
    (fun k => rand k.pkSeed k.pkRoot) seeds (typedC (PureCompression.codec Sha2Set.s128f m) default (A.at512 m.2).toI.main))

noncomputable abbrev adversary (strong : Bool) (g : CompressionTables) :=
  actual (P g) strong (Wots128f.reduced rand A seeds g)

private theorem read_public (m g : CompressionTables) (t : (publicHashSpec (P m).core).Domain) :
    simulateQ (instImpl₀ g.1) (Class128f.hashImpl m t) =
      pure (f := ProbComp) (α := (publicHashSpec (P m).core).Range t) (answers (P m) (th g) (hm g) t) := by
  cases t with
  | thash pk a xs =>
    exact (thashC_inst g.1 pk a xs).trans (congrArg (fun y => pure (f := ProbComp) y)
      ((thG_shape g.1 pk a xs).trans (Hash128f.shape g pk a xs).symm))
  | hmsg r pk root msg => exact Class128f.hmsg_at g r pk root msg

private theorem read_at (m g : CompressionTables) (t : (HSpec (P m)).Domain) :
    simulateQ (instImpl₀ g.1) (hashProgram m t) =
      pure (f := ProbComp) (α := (HSpec (P m)).Range t) (answersH (P m) (th g) (hm g) (pm g) t) := by
  rcases t with t | ⟨k,r,msg⟩
  · exact read_public m g t
  · refine (prfMsgC_inst g.1 k r msg).trans (congrArg (fun y => pure (f := ProbComp) y) ?_)
    exact (congrArg (fun (s : PRFScheme (Bytes 16) (Bytes 16 × List Byte) (Bytes 16)) => s.eval k (r,msg))
      (msg_scheme_128f g)).symm

private noncomputable abbrev canonical (strong : Bool) (ref : CF St Blk) (g : CompressionTables)
    (f : Bytes 16 → Bytes 16 → Adrs → Bytes 16) (p : Bytes 16 → Bytes 16 → List Byte → Bytes 16) (ep : p = pm g) :=
  let m : CompressionTables := (ref,g.2)
  open_at (v := vp) (P m) (th g) (hm g) rand seeds (PureCompression.codec Sha2Set.s128f m)
    (A.at512 g.2).toI.main g.1 f p (hashProgram m) strong (by rw [ep]; exact read_at m g)

/-- Keep the closed SHA-256 functions opaque while the kernel checks the open
program, then rewrite by the defining equality. -/
private noncomputable def selected {α : Type} (x : α) : {y : α // y = x} :=
  Classical.choice ⟨⟨x,rfl⟩⟩

set_option maxHeartbeats 450000 in
theorem main_fixed (strong : Bool) (ref : CF St Blk) (g : CompressionTables) :
    adversary rand A seeds strong g = (program rand A seeds strong (ref,g.2)).inst g.1 := by
  let m : CompressionTables := (ref,g.2)
  have h := canonical rand A seeds strong ref g (selected (prf g)).val (selected (pm g)).val (selected (pm g)).property
  rw [(selected (prf g)).property,(selected (pm g)).property] at h
  dsimp only [program,PrfAdvI.inst,adversary,Wots128f.reduced,PureCompression.typed,PureCompression.internalBytes,PureCompression.codec,
    SignatureAlg.StrongUnforgeableAdversary.toUnforgeableAdversary,
    trCodec,setPrf,setPrfC,withTH,m,th,hm,prf,pm,P,tablePrimitives,sha2PrimitivesMixed,
    vp,modelY,modelSk,modelPrf,modelInh,modelEqY,modelEqPk,modelEqAd,modelFinite] at h ⊢
  kexact h
variable (m : CompressionTables)
abbrev hashCount (qs : ℕ) := keygenHashes vp + qs * signHashes vp + (1 + Resources2.verifyHashes vp)
def budget (q qs L : ℕ) := q * 1 + hashCount qs * thashCost vp.params.len + (qs + 1) * ((L+257+56)/64+4) + qs * prfMsgCost (L+257)
def addressBudget (qs : ℕ) := 2 ^ vp.params.hp * vp.params.len + qs * signReads vp
private abbrev Addr := Bytes 16 × SkAdrs vp
variable (o : OracleComp (Ideal.Realize.Prf.QSpec (P m) Addr) Bool) {qf qs L : ℕ}

theorem chain_comp (hport : IsQueryBoundP o qPort qf) (hth : IsQueryBoundP o qTh (hashCount qs))
    (hhm : IsQueryBoundP o qHm (qs + 1)) (hpm : IsQueryBoundP o qPm qs)
    (hbad : IsQueryBoundP o (qBad vp.params.len (L+257)) 0) :
    IsQueryBoundP (simulateQ (handler (P m) Addr (hashProgram m)) o) (fun i => isCompQ i = true) (budget qf qs L) := by
  refine qb_simulateQ_classes4 (p₀ := qBad vp.params.len (L+257)) (p₁ := qPort) (p₂ := qTh) (p₃ := qHm)
    (p₄ := qPm) 1 (thashCost vp.params.len) (((L+257+56)/64+4)) (prfMsgCost (L+257)) (fun t ht => ?_)
    hbad hport hth hhm hpm
  rcases t with n | (q | d) | (h | ⟨k, r, M⟩)
  · exact (isQueryBoundP_query_iff _ _ _).2 fun h => by simp [isCompQ] at h
  · exact (isQueryBoundP_query_iff _ _ _).2 fun _ => by simp [liftQ]
  · exact (isQueryBoundP_query_iff _ _ _).2 fun h => by simp [isCompQ] at h
  · rcases h with ⟨pk, a, xs⟩ | ⟨R, pk, root, M⟩
    · have hx : xs.length ≤ vp.params.len := by
        simp only [liftQ, longH, decide_eq_true_eq, not_lt] at ht
        exact ht
      refine (cEmb_bound (X := Addr →ₒ Bytes 16) _ _ (thashC_bound pk a xs)
        (fun i => isCompQ i = true) (fun _ => rfl) (fun _ => by simp [isCompQ])).mono ?_
      simp only [liftQ, isTh, isHm, ite_true, ite_false]
      exact (Nat.add_zero _).le.trans ((Nat.add_zero _).le.trans (thashCost_mono hx))
    · have hM : M.length ≤ (L+257) := by
        simp only [liftQ, longH, decide_eq_true_eq, not_lt] at ht
        exact ht
      refine (cEmb_bound (X := Addr →ₒ Bytes 16) _ _ (Class128f.hmsg_count R pk root M)
        (fun i => isCompQ i = true) (fun _ => rfl) (fun _ => by simp [isCompQ])).mono ?_
      simp only [liftQ, isTh, isHm, ite_true, ite_false, Nat.zero_add, Nat.add_zero]; omega
  · have hM : M.length ≤ (L+257) := by
      simp only [liftQ, not_lt] at ht
      exact ht
    refine (cEmb_bound (X := Addr →ₒ Bytes 16) _ _ (prfMsgC_bound k r M)
      (fun i => isCompQ i = true) (fun _ => rfl) (fun _ => by simp [isCompQ])).mono ?_
    simpa [liftQ] using prfMsgCost_mono hM

theorem chain_prf (hgame : IsQueryBoundP o qGame (addressBudget qs)) :
    IsQueryBoundP (simulateQ (handler (P m) Addr (hashProgram m)) o) (fun i => isPrfQ i = true) (addressBudget qs) := by
  refine IsQueryBoundP.simulateQ_of_step hgame (fun t ht => ?_) (fun t ht => ?_)
  · rcases t with n | (q | d) | (h | m)
    · simp [liftQ] at ht
    · simp [liftQ] at ht
    · exact (isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos
    · simp [liftQ] at ht
    · simp [liftQ] at ht
  · rcases t with n | (q | d) | (h | m)
    · exact (isQueryBoundP_query_iff _ _ _).2 fun h => by simp [isPrfQ] at h
    · exact (isQueryBoundP_query_iff _ _ _).2 fun h => by simp [isPrfQ] at h
    · simp [liftQ] at ht
    · exact cEmb_zero (Xs := Addr →ₒ Bytes 16) _ (fun i => isPrfQ i = true)
        (fun n => by simp [isPrfQ]) (fun c => by simp [isPrfQ])
    · exact cEmb_zero (Xs := Addr →ₒ Bytes 16) _ (fun i => isPrfQ i = true)
        (fun n => by simp [isPrfQ]) (fun c => by simp [isPrfQ])

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
    IsQueryBoundP (program rand A seeds strong m) (fun i => isPrfQ i = true) (addressBudget qs) := by
  let f := PureCompression.typed Sha2Set.s128f A m m.2
  let r := fun (k : PublicKeyCore (P m).core) => rand k.pkSeed k.pkRoot
  have bounds : PortBounds f q qs (L+257) :=
    ⟨PureCompression.typed_port _ A m _ hq, PureCompression.typed_sign _ A m _ hs,
      PureCompression.typed_long _ A m _ hl, PureCompression.typed_out _ A m _ ho⟩
  unfold program
  rw [← typedP_eq_typedC (prims := P m)]
  cases strong with
  | false =>
    let o := bPrfCOpenP (prims := P m) r seeds f
    have hp := bPrfCOpenP_port r seeds bounds
    have hm := bPrfCOpenP_game r seeds bounds
    have hh := bPrfCOpenP_hash r seeds bounds
    have hpm := bPrfCOpenP_pm r seeds bounds
    have hd := bPrfCOpenP_hm r seeds bounds
    have hb := bPrfCOpenP_bad r seeds bounds vp.params.len (ok_len m)
    exact ⟨chain_comp m o hp (IsQueryBoundP.of_imp qTh_imp hh) hd hpm hb, chain_prf m o hm⟩
  | true =>
    let o := bPrfWCOpenP (prims := P m) r seeds sufCheckOpen f
    have hp := bPrfWCOpenP_port r seeds bounds
    have hm := bPrfWCOpenP_game r seeds bounds
    have hh := bPrfWCOpenP_hash r seeds bounds
    have hpm := bPrfWCOpenP_pm r seeds bounds
    have hd := bPrfWCOpenP_hm r seeds bounds
    have hb := bPrfWCOpenP_bad r seeds bounds vp.params.len (ok_len m)
    exact ⟨chain_comp m o hp (IsQueryBoundP.of_imp qTh_imp hh) hd hpm hb, chain_prf m o hm⟩
noncomputable def loss (q qs L : ℕ) : ℝ≥0∞ :=
  let Q := budget q qs L
  (Q:ℝ≥0∞)/2^128 + (((Q + addressBudget qs)^2 : ℕ) : ℝ≥0∞)/2^256

set_option maxRecDepth 8192 in
private theorem mixed_scheme (v : ValidatedParams) (c : CompressFn) (d : Compress512Fn) (sample : SampleableType (Bytes v.params.n)) :
    @skPrfC v (sha2PrimitivesMixed c d v.params) sample =
      @skPrfC v (sha2PrimitivesG c v.params) sample := by
  dsimp only [skPrfC, sha2PrimitivesMixed, sha2PrimitivesG]

include hq hs hl ho in
theorem term :
    PureCompression.average (fun g => prfRealPr (vp := vp) (prims := P g) (adversary rand A seeds strong g)) ≤
      PureCompression.average (fun g => prfIdealPr (vp := vp) (prims := P g) (adversary rand A seeds strong g)) + loss q qs L := by
  let I (other : CF Chain512 Block512) := cfAvg fun c =>
    prfIdealPr (vp := vp) (prims := P (c,other)) (adversary rand A seeds strong (c,other))
  have bound (other : CF Chain512 Block512) :
      (cfAvg fun c => prfRealPr (vp := vp) (prims := P (c,other)) (adversary rand A seeds strong (c,other))) ≤
        I other + loss q qs L := by
    let ref : CompressionTables := (default,other)
    let D := program rand A seeds strong ref
    have real (c : CF St Blk) := congrArg evalDist (congrArg
      (fun a : PRFScheme.PRFAdversary Addr (Bytes 16) => (skPrfC vp (P (c,other))).prfRealExperiment a)
      (main_fixed rand A seeds strong ref.1 (c,other)))
    have ideal (c : CF St Blk) := congrArg evalDist (congrArg
      (fun a : PRFScheme.PRFAdversary Addr (Bytes 16) => PRFScheme.prfIdealExperiment a)
      (main_fixed rand A seeds strong ref.1 (c,other)))
    have re := cfAvg_of_evalDist_eq real
    have ie := cfAvg_of_evalDist_eq ideal
    obtain ⟨hc,hp⟩ := counts rand A seeds ref strong hq hs hl ho
    have hh := SkPrf.bound Sha2Set.s128f D (budget q qs L) (addressBudget qs) hc hp
    apply re.le.trans
    apply le_trans ?_ (add_le_add ie.symm.le (le_refl (loss q qs L)))
    unfold SkPrf.advantage at hh
    let X (c : CF St Blk) := (skPrfC vp (sha2PrimitivesG (liftC c) vp.params)).prfRealExperiment (D.inst c)
    let Y (c : CF St Blk) := PRFScheme.prfIdealExperiment (D.inst c)
    have ex (c : CF St Blk) := congrArg (fun f : PRFScheme (Bytes 16) Addr (Bytes 16) => f.prfRealExperiment (D.inst c)) (mixed_scheme vp (liftC c) (lift512 other) (inferInstanceAs (SampleableType (Bytes 16))))
    refine (congrArg cfAdvantage (funext ex)).le.trans ?_
    exact (cfAdvantage_le_add_boolDist X Y).trans (add_le_add le_rfl hh)
  apply (cfAvg_mono bound).trans
  rw [cfAvg_add]
  apply add_le_add le_rfl
  let _ : MeasurableSpace (CF Chain512 Block512) := ⊤
  unfold cfAvg
  rw [MeasureTheory.lintegral_const]
  exact mul_le_of_le_one_right' (evalDist_apply_univ_le_one _)

end MIdeal.Secret128f
#print axioms MIdeal.Secret128f.open_at
#print axioms MIdeal.Secret128f.main_fixed
#print axioms MIdeal.Secret128f.counts
#print axioms MIdeal.Secret128f.term
