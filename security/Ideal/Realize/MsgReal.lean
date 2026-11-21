import Ideal.Realize.MsgCount
import Ideal.Transport.AdvMsg
import Ideal.ComposeFinal

/-!
# The `PRF_msg` realisers (SUF and EUF)

For an ideal-model forger `S`, a table-independent `opt_rand` sampler `oR` and any seed
distribution, ONE ideal-model `PRF_msg` distinguisher `AmsgS S oR pkSeedDist` (resp. `AmsgE`)
whose instantiation at every table `g` IS the Reduction's lazy `PRF_msg` distinguisher
`Lazy.bPrfMsgWL sufCheck (S.typedS (optRandU oR) pkSeedDist g)` (resp.
`Lazy.bPrfMsgL (S.typedE …)`):

* `AmsgS = interpC hashC (lazyRes P)`, `P` the port program `msgOpenWVP` over the reference
  bundle `Rd = R₀ dT dH` at the forger `typedC codec₀ default S.main`;
* `bPrfMsgWL_eq_inst`, `bPrfMsgL_eq_inst`: the equations (closed `setPrf` transport
  `Ideal.Transport.bPrfMsgWL_setPrf_S`, `Reduction.Open.lazyRun_msgOpenWV_sufCheck`, port fusion
  `msgOpenWVP_fusion`, `Thash`/`H_msg` independence `msgOpenWVP_withTH`, chains `lazyRun_portR`);
* counts: compression queries `≤ qMsg qf qs ℓ = qf + Hn·thashCost len + (qs+1)·hmsgCost ℓ`
  (`Hn` the hash count of `Reduction.Open.msgOpenWV_suf_hashes`), `PRF_msg` queries `≤ qs`, on
  messages of at most `ℓ` bytes;
* `realizesMsgSuf`, `realizesMsgEuf`: the two `RealizesMsg` structures;
* `qMsg_128s`, `qMsg_le`: closed forms.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security

namespace Ideal.Realize.Msg

open Reduction Reduction.Lazy Reduction.Open Ideal.Transport

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! ## The reference objects -/

/-- The wire codec over `core₀`. -/
def codec₀ : CoreWireCodec Link.vp.params core₀ where
  pkSeed := WireCodec.bytes Link.vp.params.n
  skSeed := WireCodec.bytes Link.vp.params.n
  skPrf := WireCodec.bytes Link.vp.params.n
  y := WireCodec.bytes Link.vp.params.n
  y_toBytes := fun _ => rfl

/-- `optRandU oR` over `core₀`. -/
def optRand₀ (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) (pk : PublicKeyCore core₀) :
    ProbComp core₀.Y := oR pk.pkSeed pk.pkRoot

/-- The reference bundle (dummy hash functions; never evaluated). -/
abbrev Rd : Primitives Link.vp.params := R₀ dT dH

/-- The typed port forger of `S`, over `core₀`. -/
noncomputable def mainC (S : ForgerI) : PortForgerProg Link.vp Rd :=
  typedC codec₀ default S.main

/-- The SUF port program. -/
noncomputable def PmsgS (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    (pkSeedDist : ProbComp (Bytes 16)) : OracleComp (OP Rd) Bool :=
  msgOpenWVP (prims := Rd) (optRand₀ oR) pkSeedDist sufCheckO (mainC S)

/-- The EUF port program. -/
noncomputable def PmsgE (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    (pkSeedDist : ProbComp (Bytes 16)) : OracleComp (OP Rd) Bool :=
  msgOpenVP (prims := Rd) (optRand₀ oR) pkSeedDist (mainC S)

/-- The ideal-model distinguisher of a port program: lazy cache, hash queries as compression
chains (`hashC`). -/
noncomputable def interpA (P : OracleComp (OP Rd) Bool) : MsgPrfAdvI :=
  simulateQ (interpC (G := msgG Rd) hashC) (lazyRes P)

/-- **The ideal-model `PRF_msg` distinguisher (SUF).** -/
noncomputable def AmsgS (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    (pkSeedDist : ProbComp (Bytes 16)) : MsgPrfAdvI :=
  interpA (PmsgS S oR pkSeedDist)

/-- **The ideal-model `PRF_msg` distinguisher (EUF).** -/
noncomputable def AmsgE (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    (pkSeedDist : ProbComp (Bytes 16)) : MsgPrfAdvI :=
  interpA (PmsgE S oR pkSeedDist)

/-! ## The equations -/

/-- **SUF: the Reduction's lazy `PRF_msg` distinguisher at every table is `AmsgS` there.** -/
theorem bPrfMsgWL_eq_inst (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    (pkSeedDist : ProbComp (Bytes 16)) (g : CF St Blk) :
    Lazy.bPrfMsgWL sufCheck (S.typedS (optRandU oR) pkSeedDist g) =
      (AmsgS S oR pkSeedDist).inst g := by
  have h1 := bPrfMsgWL_setPrf_S (R₀ (thG g) (hmG g)) (prfG g) (pmG g) codec₀ (optRand₀ oR)
    (optRandU oR g) (fun _ => rfl) pkSeedDist (fun pk => simulateQ (instImpl g) (S.main pk))
  refine h1.trans ?_
  have h2 := (lazyRun_msgOpenWV_sufCheck (prims := R₀ (thG g) (hmG g))
    (bytesToTypedS (vp := Link.vp) (prims := R₀ (thG g) (hmG g)) (codec := codec₀)
      (optRand := optRand₀ oR) (pkSeedDist := pkSeedDist)
      ⟨fun pk => simulateQ (instImpl g) (S.main pk)⟩).toUnforgeableAdversary).symm
  refine h2.trans ?_
  have h3 := bytesToTypedS_inst (prims := R₀ (thG g) (hmG g)) (optRand := optRand₀ oR)
    (pkSeedDist := pkSeedDist) codec₀ g S.main
  rw [h3]
  have h4 := msgOpenWVP_fusion (prims := R₀ (thG g) (hmG g)) (optRand₀ oR) pkSeedDist g sufCheckO
    (typedC codec₀ default S.main)
  rw [← h4]
  have h5 : msgOpenWVP (prims := R₀ (thG g) (hmG g)) (optRand₀ oR) pkSeedDist sufCheckO
      (typedC codec₀ default S.main) = PmsgS S oR pkSeedDist :=
    msgOpenWVP_withTH (prims := Rd) (optRand₀ oR) pkSeedDist (thG g) (hmG g) (mainC S)
  rw [h5]
  exact lazyRun_portR (G := msgG Rd) g (PublicHash.impl (R₀ (thG g) (hmG g))) hashC
    (fun q => by rw [impl_R₀]; exact hashC_inst g q) (PmsgS S oR pkSeedDist)

/-- **EUF: the Reduction's lazy `PRF_msg` distinguisher at every table is `AmsgE` there.** -/
theorem bPrfMsgL_eq_inst (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    (pkSeedDist : ProbComp (Bytes 16)) (g : CF St Blk) :
    Lazy.bPrfMsgL (S.typedE (optRandU oR) pkSeedDist g) = (AmsgE S oR pkSeedDist).inst g := by
  have h1 := bPrfMsgL_setPrf (R₀ (thG g) (hmG g)) (prfG g) (pmG g) codec₀ (optRand₀ oR)
    (optRandU oR g) (fun _ => rfl) pkSeedDist (fun pk => simulateQ (instImpl g) (S.main pk))
  refine h1.trans ?_
  have h2 := (lazyRun_msgOpenV (prims := R₀ (thG g) (hmG g))
    (bytesToTyped (vp := Link.vp) (prims := R₀ (thG g) (hmG g)) (codec := codec₀)
      (optRand := optRand₀ oR) (pkSeedDist := pkSeedDist)
      ⟨fun pk => simulateQ (instImpl g) (S.main pk)⟩)).symm
  refine h2.trans ?_
  have h3 := bytesToTyped_inst (prims := R₀ (thG g) (hmG g)) (optRand := optRand₀ oR)
    (pkSeedDist := pkSeedDist) codec₀ g S.main
  rw [h3]
  have h4 := msgOpenVP_fusion (prims := R₀ (thG g) (hmG g)) (optRand₀ oR) pkSeedDist g
    (typedC codec₀ default S.main)
  rw [← h4]
  have h5 : msgOpenVP (prims := R₀ (thG g) (hmG g)) (optRand₀ oR) pkSeedDist
      (typedC codec₀ default S.main) = PmsgE S oR pkSeedDist :=
    msgOpenVP_withTH (prims := Rd) (optRand₀ oR) pkSeedDist (thG g) (hmG g) (mainC S)
  rw [h5]
  exact lazyRun_portR (G := msgG Rd) g (PublicHash.impl (R₀ (thG g) (hmG g))) hashC
    (fun q => by rw [impl_R₀]; exact hashC_inst g q) (PmsgE S oR pkSeedDist)

/-! ## Counts -/

/-- The largest number of values of a `Thash` call of SLH-DSA-SHA2-128s (`len`). -/
abbrev thB : ℕ := Link.vp.params.len

theorem okLen_le (xs : List Rd.Y) (h : OkLen Link.vp xs) : xs.length ≤ thB := by
  rcases h with h | h | h | h <;> rw [h] <;> decide

/-- The hash count of the open `PRF_msg` distinguishers (`Reduction.Open.msgOpenWV_suf_hashes`). -/
abbrev hashN (qs : ℕ) : ℕ :=
  keygenHashes Link.vp + qs * signHashes Link.vp + (1 + Resources2.verifyHashes Link.vp)

/-- **The compression-query count of the `PRF_msg` realisers**: the forger's own queries, the
`Thash` chains and the `H_msg` chains. -/
def qMsg (qf qs ℓ : ℕ) : ℕ := qf * 1 + hashN qs * thashCost thB + (qs + 1) * hmsgCost ℓ

theorem liftM_zero {ι : Type} {X : OracleSpec ι} {α : Type} (ob : ProbComp α)
    (q : ℕ ⊕ ι → Prop) [DecidablePred q] (h0 : ∀ n, ¬ q (.inl n)) :
    IsQueryBoundP (liftM ob : OracleComp (unifSpec + X) α) q 0 := by
  induction ob using OracleComp.inductionOn with
  | pure a => exact isQueryBoundP_pure _ _ _
  | query_bind n k ih =>
    rw [liftM_bind]
    exact isQueryBoundP_bind_zero _ _
      ((isQueryBoundP_query_iff (spec := unifSpec + X) _ (.inl n) 0).2 fun h => absurd h (h0 n)) ih

section Counts

variable (P : OracleComp (OP Rd) Bool) {qf qs ℓ : ℕ}

instance (mlen : ℕ) : DecidablePred (msgLenLe mlen) := fun t => by
  rcases t with n | q | d <;> simp only [msgLenLe] <;> infer_instance

/-- Compression queries of `interpC hashC (lazyRes P)`. -/
theorem interp_comp (hport : IsQueryBoundP P pPort qf) (hth : IsQueryBoundP P pTh (hashN qs))
    (hhm : IsQueryBoundP P pHm (qs + 1)) (hbad : IsQueryBoundP P (pBad thB ℓ) 0) :
    IsQueryBoundP (interpA P) (fun i => isCompQ i = true) (qMsg qf qs ℓ) := by
  unfold interpA
  refine qb_simulateQ_classes (p₀ := pBad thB ℓ) (p₁ := pPort) (p₂ := pTh) (p₃ := pHm)
    1 (thashCost thB) (hmsgCost ℓ) (fun t ht => ?_)
    (lazyRes_bound_liftP _ _ P 0 hbad) (lazyRes_bound_liftP _ _ P _ hport)
    (lazyRes_bound_liftP _ _ P _ hth) (lazyRes_bound_liftP _ _ P _ hhm)
  rcases t with n | (q | d) | (u | h)
  · exact (isQueryBoundP_query_iff _ _ _).2 fun h => by simp [isCompQ] at h
  · exact (isQueryBoundP_query_iff _ _ _).2 fun _ => by simp [liftP]
  · exact (isQueryBoundP_query_iff _ _ _).2 fun h => by simp [isCompQ] at h
  · exact (liftM_zero (X := hS St Blk + msgG Rd) ($ᵗ Rd.Y) (fun i => isCompQ i = true)
      fun n => by simp [isCompQ]).mono (Nat.zero_le _)
  · rcases h with ⟨pk, a, xs⟩ | ⟨R, pk, root, M⟩
    · have hx : xs.length ≤ thB := by
        simp only [pBad, liftP, longH, decide_eq_true_eq, not_lt] at ht
        exact ht
      refine (cEmb_bound (X := msgG Rd) _ _ (thashC_bound pk a xs) (fun i => isCompQ i = true)
        (fun _ => rfl) (fun _ => by simp [isCompQ])).mono ?_
      simp only [liftP, isTh, isHm, ite_true, ite_false]
      exact (Nat.add_zero _).le.trans (thashCost_mono hx)
    · have hM : M.length ≤ ℓ := by
        simp only [pBad, liftP, longH, decide_eq_true_eq, not_lt] at ht
        exact ht
      refine (cEmb_bound (X := msgG Rd) _ _ (hmsgC_bound R pk root M) (fun i => isCompQ i = true)
        (fun _ => rfl) (fun _ => by simp [isCompQ])).mono ?_
      simpa [liftP, isTh, isHm] using hmsgCost_mono hM

/-- `PRF_msg` oracle queries of `interpC hashC (lazyRes P)`. -/
theorem interp_prf (hmsg : IsQueryBoundP P pMsg qs) :
    IsQueryBoundP (interpA P) (fun i => isPrfQ i = true) qs := by
  unfold interpA
  refine IsQueryBoundP.simulateQ_of_step (lazyRes_bound_liftP _ _ P _ hmsg) (fun t ht => ?_)
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
    · exact liftM_zero (X := hS St Blk + msgG Rd) ($ᵗ Rd.Y) (fun i => isPrfQ i = true)
        fun n => by simp [isPrfQ]
    · exact isQueryBoundP_simulateQ_zero _ fun t => by
        rcases t with n | c
        · exact (isQueryBoundP_query_iff _ _ _).2 fun h => by simp [isPrfQ] at h
        · exact (isQueryBoundP_query_iff _ _ _).2 fun h => by simp [isPrfQ] at h

theorem cEmb_zero {ι α : Type} {Xs : OracleSpec ι} (X : OracleComp CSpec α)
    (q : ℕ ⊕ ((St × Blk) ⊕ ι) → Prop) [DecidablePred q]
    (h0 : ∀ n, ¬ q (.inl n)) (h1 : ∀ c, ¬ q (.inr (.inl c))) :
    IsQueryBoundP (simulateQ (cEmb (X := Xs)) X) q 0 :=
  isQueryBoundP_simulateQ_zero _ fun t => by
    rcases t with n | c
    · exact (isQueryBoundP_query_iff _ _ _).2 fun h => absurd h (h0 n)
    · exact (isQueryBoundP_query_iff _ _ _).2 fun h => absurd h (h1 c)

/-- A `PRF_msg` oracle query on a message of more than `ℓ` bytes. -/
def longQ {Y : Type} (ℓ : ℕ) : ℕ ⊕ ((St × Blk) ⊕ (Y × List Byte)) → Bool
  | .inr (.inr d) => decide (ℓ < d.2.length)
  | _ => false

/-- The messages of the `PRF_msg` oracle queries of `interpC hashC (lazyRes P)`. -/
theorem interp_len (hbad : IsQueryBoundP P (pBad thB ℓ) 0) :
    AllQueriesSatisfy (interpA P) (msgLenLe ℓ) := by
  refine (isQueryBoundP_zero_iff _ (msgLenLe ℓ)).1
    (IsQueryBoundP.of_imp (p' := fun t => longQ ℓ t = true) (fun t ht => ?_) ?_)
  · rcases t with n | q | d
    · simp [msgLenLe] at ht
    · simp [msgLenLe] at ht
    · simp only [msgLenLe, not_le] at ht
      simpa [longQ] using ht
  unfold interpA
  have hq0 : ∀ n, ¬ longQ (Y := Rd.Y) ℓ (.inl n) = true := fun n => by simp [longQ]
  have hq1 : ∀ c, ¬ longQ (Y := Rd.Y) ℓ (.inr (.inl c)) = true := fun c => by simp [longQ]
  refine IsQueryBoundP.simulateQ_of_step (q := fun t => longQ ℓ t = true) (impl := interpC (G := msgG Rd) hashC)
    (lazyRes_bound_liftP _ _ P 0 hbad) (fun t ht => ?_) (fun t ht => ?_)
  · rcases t with n | (q | d) | (u | h)
    · simp [liftP] at ht
    · simp [liftP, longG] at ht
    · exact (isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos
    · simp [liftP] at ht
    · exact (cEmb_zero (Xs := msgG Rd) _ (fun t => longQ (Y := Rd.Y) ℓ t = true) hq0 hq1).mono
        (Nat.zero_le _)
  · rcases t with n | (q | d) | (u | h)
    · exact (isQueryBoundP_query_iff _ _ _).2 fun h => absurd h (hq0 n)
    · exact (isQueryBoundP_query_iff _ _ _).2 fun h => absurd h (hq1 q)
    · have hd : d.2.length ≤ ℓ := by
        simp only [liftP, longG, decide_eq_true_eq, not_lt] at ht
        exact ht
      exact (isQueryBoundP_query_iff _ _ _).2 fun h => by simp [longQ] at h; omega
    · exact liftM_zero (X := hS St Blk + msgG Rd) ($ᵗ Rd.Y) (fun t => longQ (Y := Rd.Y) ℓ t = true) hq0
    · exact cEmb_zero (Xs := msgG Rd) _ (fun t => longQ (Y := Rd.Y) ℓ t = true) hq0 hq1

end Counts

/-! ## The realisers -/

/-- A family that IS the instantiation of an ideal-model `PRF_msg` distinguisher is realised by
it (the analogue of `Ideal.RealizesPrf.ofEq`). -/
def realizesMsg_ofEq {B : ∀ g : CF St Blk, Reduction.MsgPrfAdv (primsG (liftC g))}
    {q qO mlen : ℕ} (A : MsgPrfAdvI) (h : ∀ g, B g = A.inst g)
    (hq : IsQueryBoundP A (fun i => isCompQ i = true) q)
    (hO : IsQueryBoundP A (fun i => isPrfQ i = true) qO)
    (hM : AllQueriesSatisfy A (msgLenLe mlen)) : RealizesMsg B q qO mlen :=
  ⟨A, fun g => by rw [h g], fun g => by rw [h g], hq, hO, hM⟩

section Realizers

variable (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
  (pkSeedDist : ProbComp (Bytes 16)) {qf qs ℓ : ℕ}
  (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List Byte) i = true) qf)
  (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List Byte) i = true) qs)
  (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQ (S := List Byte) ℓ i = true) 0)
  (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ)

include hqf hqs hlong hout

theorem mainC_bounds : PortBounds (prims := Rd) (mainC S) qf qs ℓ := by
  unfold mainC
  exact portBounds_typedC (prims := Rd) codec₀ S.main qf qs ℓ hqf hqs hlong hout

/-- **The `PRF_msg` realiser of the SUF-CMA composition.** -/
noncomputable def realizesMsgSuf :
    RealizesMsg (fun g => Reduction.Lazy.bPrfMsgWL Reduction.sufCheck
      (S.typedS (optRandU oR) pkSeedDist g)) (qMsg qf qs ℓ) qs ℓ :=
  have hF := mainC_bounds S hqf hqs hlong hout
  realizesMsg_ofEq (AmsgS S oR pkSeedDist) (bPrfMsgWL_eq_inst S oR pkSeedDist)
    (interp_comp _ (msgOpenWVP_port _ _ hF)
      (IsQueryBoundP.of_imp pTh_imp (msgOpenWVP_hash _ _ hF)) (msgOpenWVP_hm _ _ hF)
      (msgOpenWVP_bad _ _ hF thB okLen_le))
    (interp_prf _ (msgOpenWVP_msg _ _ hF))
    (interp_len _ (msgOpenWVP_bad _ _ hF thB okLen_le))

/-- **The `PRF_msg` realiser of the EUF-CMA composition.** -/
noncomputable def realizesMsgEuf :
    RealizesMsg (fun g => Reduction.Lazy.bPrfMsgL (S.typedE (optRandU oR) pkSeedDist g))
      (qMsg qf qs ℓ) qs ℓ :=
  have hF := mainC_bounds S hqf hqs hlong hout
  realizesMsg_ofEq (AmsgE S oR pkSeedDist) (bPrfMsgL_eq_inst S oR pkSeedDist)
    (interp_comp _ (msgOpenVP_port _ _ hF)
      (IsQueryBoundP.of_imp pTh_imp (msgOpenVP_hash _ _ hF)) (msgOpenVP_hm _ _ hF)
      (msgOpenVP_bad _ _ hF thB okLen_le))
    (interp_prf _ (msgOpenVP_msg _ _ hF))
    (interp_len _ (msgOpenVP_bad _ _ hF thB okLen_le))

end Realizers

/-! ## Closed forms -/

theorem thashCost_thB : thashCost thB = 11 := by decide

theorem hashN_128s (qs : ℕ) : hashN qs = 269824 + qs * 2007385 + 3929 := by
  unfold hashN
  rw [keygenHashes_128s, signHashes_128s, Resources2.verifyHashes_128s]

/-- `qMsg` at SHA2-128s. -/
theorem qMsg_128s (qf qs ℓ : ℕ) :
    qMsg qf qs ℓ = qf + (269824 + qs * 2007385 + 3929) * 11 + (qs + 1) * ((ℓ + 56) / 64 + 3) := by
  unfold qMsg
  rw [hashN_128s, thashCost_thB]
  unfold hmsgCost
  ring

/-- **Simple upper bound** on the compression queries of the `PRF_msg` realisers. -/
theorem qMsg_le (qf qs ℓ : ℕ) : qMsg qf qs ℓ ≤ qf + (qs + 1) * (2 ^ 25 + 2 * ℓ) := by
  rw [qMsg_128s]
  have h1 : (ℓ + 56) / 64 ≤ ℓ + 1 := by omega
  nlinarith [Nat.zero_le qs, Nat.zero_le ℓ]

end Ideal.Realize.Msg

#print axioms Ideal.Realize.Msg.bPrfMsgWL_eq_inst
#print axioms Ideal.Realize.Msg.bPrfMsgL_eq_inst
#print axioms Ideal.Realize.Msg.interp_comp
#print axioms Ideal.Realize.Msg.interp_prf
#print axioms Ideal.Realize.Msg.interp_len
#print axioms Ideal.Realize.Msg.realizesMsgSuf
#print axioms Ideal.Realize.Msg.realizesMsgEuf
#print axioms Ideal.Realize.Msg.qMsg_128s
#print axioms Ideal.Realize.Msg.qMsg_le
