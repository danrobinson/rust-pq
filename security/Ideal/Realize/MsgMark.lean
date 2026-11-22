import Ideal.Realize.PrfMark
import Ideal.Games.MsgPrfFine

/-!
# HMAC-key-block-shaped compression queries of the `PRF_msg` realisers

`Ideal.msgPrf_bound_128s_marked` (below) charges `2·2^-128` only to compression queries whose
block is an inner or outer HMAC key block `ikey k`, `okey k` (`MsgPrf.markK ikey okey`).  The
realisers `AmsgS`, `AmsgE` of `MsgReal.lean` make at most

`qMsgM qf qs ℓ = qf + 11·nLong qs + (qs+1)·hmsgCost ℓ`

such queries (`interp_mark`, `AmsgS_mark`, `AmsgE_mark`): the forger's own queries, every block
of the `T_len`/`T_k` evaluations and of the `H_msg` evaluations.  The `F`, `H` (and `PRF`)
evaluations of the reduction contribute none: bytes `16..63` of an HMAC key block are `0x36`
resp. `0x5c`, while byte `16` of a seed block is `0` and byte `22 + 16·n` of the first block of
`Thash(pk, a, xs)` with `n = |xs| ≤ 2` is the padding byte `0x80`.
-/

open OracleComp OracleSpec ENNReal SLHDSA SLHDSA.Security

namespace Ideal

/-! ## Blocks -/

theorem ikey_toList_get (k : Bytes 16) (j : ℕ) (h1 : 16 ≤ j) (h2 : j < 64) :
    (ikey k).toList[j]? = some 0x36 := by
  rw [ikey_toList, key0L, List.map_append, List.getElem?_append_right (by simpa using h1)]
  rw [List.getElem?_map]
  simp only [List.length_map, Vector.length_toList, List.getElem?_replicate]
  split_ifs with h
  · rfl
  · omega

theorem okey_toList_get (k : Bytes 16) (j : ℕ) (h1 : 16 ≤ j) (h2 : j < 64) :
    (okey k).toList[j]? = some 0x5c := by
  rw [okey_toList, key0L, List.map_append, List.getElem?_append_right (by simpa using h1)]
  rw [List.getElem?_map]
  simp only [List.length_map, Vector.length_toList, List.getElem?_replicate]
  split_ifs with h
  · rfl
  · omega

theorem blk_toList_get (B : Blk) (j : ℕ) (h : j < 64) : B.toList[j]? = some B[j] := by
  rw [List.getElem?_eq_getElem (by simpa using h)]
  simp

/-- A block with byte `j ∈ [16, 64)` different from `0x36` and `0x5c` is no HMAC key block. -/
theorem not_keyBlk_of_byte (B : Blk) (j : ℕ) (h1 : 16 ≤ j) (h2 : j < 64)
    (h36 : B[j] ≠ 0x36) (h5c : B[j] ≠ 0x5c) : ¬ ∃ k, B = ikey k ∨ B = okey k := by
  rintro ⟨k, h | h⟩
  · have e := ikey_toList_get k j h1 h2
    rw [← h, blk_toList_get B j h2] at e
    exact h36 (Option.some.inj e)
  · have e := okey_toList_get k j h1 h2
    rw [← h, blk_toList_get B j h2] at e
    exact h5c (Option.some.inj e)

theorem sb128_get16 (pk : Bytes 16) : (sb128 pk)[16] = 0 := by
  have h : (sb128 pk).toList[16]? = some 0 := by
    rw [sb128_toList, List.getElem?_append_right (by simp)]
    simp
  rw [blk_toList_get _ 16 (by norm_num)] at h
  exact Option.some.inj h

theorem tblocks_fst_pad (a : Bytes 22) (xs : List (Bytes 16)) (h : xs.length ≤ 2) :
    (tblocks a xs).1[22 + 16 * xs.length]'(by omega) = 0x80 := by
  rw [tblocks_fst_eq]
  simp only [Vector.getElem_ofFn, tbytes]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
  simp [tailL]

theorem sb128_not_keyBlk (pk : Bytes 16) : ¬ ∃ k, sb128 pk = ikey k ∨ sb128 pk = okey k :=
  not_keyBlk_of_byte _ 16 (by norm_num) (by norm_num) (by rw [sb128_get16]; decide)
    (by rw [sb128_get16]; decide)

theorem tblocks_not_keyBlk (a : Bytes 22) (xs : List (Bytes 16)) (h : xs.length ≤ 2) :
    ¬ ∃ k, (tblocks a xs).1 = ikey k ∨ (tblocks a xs).1 = okey k :=
  not_keyBlk_of_byte _ (22 + 16 * xs.length) (by omega) (by omega)
    (by rw [tblocks_fst_pad a xs h]; decide) (by rw [tblocks_fst_pad a xs h]; decide)

/-- **`PRF_msg` is a PRF at SLH-DSA-SHA2-128s, marked form.**  As `msgPrf_bound_128s`, with the
`2^-128` term charged only to the `qM` compression queries at HMAC key blocks. -/
theorem msgPrf_bound_128s_marked (A : MsgPrfAdvI) (qM q qO mlen : ℕ)
    (hqM : IsQueryBoundP A (MsgPrf.markK ikey okey) qM)
    (hq : IsQueryBoundP A (fun i => isCompQ i = true) q)
    (hO : IsQueryBoundP A (fun i => isPrfQ i = true) qO)
    (hM : AllQueriesSatisfy A (msgLenLe mlen)) :
    msgRealI A ≤ msgIdealI A + (2 * (qM : ℝ≥0∞) / 2 ^ 128 +
        (((q + qO * ((mlen + 24) / 64 + 1) + 2) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256) := by
  have hL : AllQueriesSatisfy A (ibLenLe ib128 ((mlen + 24) / 64)) :=
    AllQueriesSatisfy.mono hM fun t ht => ibLenLe_of_msgLenLe mlen t ht
  have h := prT_mac_two_sided_marked IV128 ikey okey ikey_injective okey_injective
    (fun k => ikey_ne_okey k k) ib128 ib128_injective oblock oblock_injective out16 prEvent_out16
    A qM q qO ((mlen + 24) / 64) hqM hq hO hL
  have hε : 2 * (qM : ℝ≥0∞) * (Fintype.card (Bytes 16) : ℝ≥0∞)⁻¹ +
        ((3 * q + qO * (1 + 3 * ((mlen + 24) / 64)) + 3 +
          (q + qO * (1 + (mlen + 24) / 64)) ^ 2 : ℕ) : ℝ≥0∞) * (Fintype.card St : ℝ≥0∞)⁻¹ ≤
      2 * (qM : ℝ≥0∞) / 2 ^ 128 +
        (((q + qO * ((mlen + 24) / 64 + 1) + 2) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
    have e1 : ((256 ^ 16 : ℕ) : ℝ≥0∞) = 2 ^ 128 := by
      rw [show (256 : ℕ) = 2 ^ 8 from rfl, ← pow_mul]; norm_num
    have e2 : ((2 ^ 256 : ℕ) : ℝ≥0∞) = 2 ^ 256 := by norm_num
    rw [card_bytes 16, card_St, div_eq_mul_inv, div_eq_mul_inv, e1, e2]
    refine add_le_add le_rfl (mul_le_mul_left (Nat.cast_le.mpr ?_) _)
    generalize (mlen + 24) / 64 = L
    have h1 : qO * (1 + 3 * L) ≤ 3 * (qO * (1 + L)) := by nlinarith
    have h2 : (q + qO * (L + 1) + 2) ^ 2 =
        (q + qO * (1 + L)) ^ 2 + 4 * (q + qO * (1 + L)) + 4 := by ring
    rw [h2]
    omega
  rw [msgRealI_eq, msgIdealI_eq]
  exact h.1.trans (add_le_add le_rfl hε)

end Ideal

namespace Ideal.Realize.Msg

open Reduction Reduction.Lazy Reduction.Open
open Ideal.Realize.Prf (longTh qb_recover verifyM_long keygenLong_128s signLongB signLongB_128s
  verifyLong_128s)

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- A compression query (`CSpec` index) at an HMAC key block. -/
def markKC : ℕ ⊕ (St × Blk) → Prop
  | .inr q => ∃ k, q.2 = ikey k ∨ q.2 = okey k
  | .inl _ => False

noncomputable instance : DecidablePred markKC := fun _ => Classical.propDecidable _

/-- A short `Thash` evaluation makes no compression query at an HMAC key block. -/
theorem thashC_markK (pk : Bytes 16) (key : Bytes 22) (xs : List (Bytes 16)) (h : xs.length ≤ 2) :
    IsQueryBoundP (thashC pk key xs) markKC 0 := by
  unfold thashC
  have htail : (tblocks key xs).2 = [] := by
    have := tblocks_snd_length key xs
    exact List.eq_nil_of_length_eq_zero (by omega)
  refine isQueryBoundP_bind_zero _ _
    ((isQueryBoundP_query_iff _ _ _).2 fun h' => absurd h' (sb128_not_keyBlk pk)) fun cv => ?_
  refine isQueryBoundP_bind_zero _ _
    ((isQueryBoundP_query_iff _ _ _).2 fun h' => absurd h' (tblocks_not_keyBlk key xs h)) fun c => ?_
  rw [htail]
  simp [foldQ]

/-- Embedded `CSpec` programs: marked queries are those of the program. -/
theorem cEmb_markK {α : Type} (oa : OracleComp CSpec α) (n : ℕ) (h : IsQueryBoundP oa markKC n) :
    IsQueryBoundP (simulateQ (cEmb (X := msgG Rd)) oa) (MsgPrf.markK ikey okey) n := by
  refine IsQueryBoundP.simulateQ_of_step h (fun t ht => ?_) (fun t ht => ?_)
  · rcases t with m | c
    · exact (isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos
    · exact (isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos
  · rcases t with m | c
    · exact (isQueryBoundP_query_iff _ _ _).2 fun h' => h'.elim
    · exact (isQueryBoundP_query_iff _ _ _).2 fun h' => absurd h' ht

theorem cEmb_markKR {α : Type} (oa : OracleComp CSpec α) (n : ℕ)
    (h : IsQueryBoundP oa (fun i => i.isRight = true) n) :
    IsQueryBoundP (simulateQ (cEmb (X := msgG Rd)) oa) (MsgPrf.markK ikey okey) n :=
  cEmb_markK oa n (IsQueryBoundP.of_imp (p := markKC) (fun t ht => by
    rcases t with m | q
    · exact ht.elim
    · rfl) h)

section Classes

variable {A D P K Y : Type}

/-- Long `Thash` queries. -/
abbrev pLong : ℕ ⊕ ((A ⊕ (Y × List Byte)) ⊕ (D ⊕ PublicHashQuery P K Y)) → Prop :=
  liftP (fun _ => False) (fun q => longTh q = true)

end Classes

section Counts

variable (P : OracleComp (OP Rd) Bool) {qf qs ℓ nL : ℕ}

/-- **HMAC-key-block-shaped compression queries of `interpA P`.** -/
theorem interp_mark (hport : IsQueryBoundP P pPort qf) (hlong : IsQueryBoundP P pLong nL)
    (hhm : IsQueryBoundP P pHm (qs + 1)) (hbad : IsQueryBoundP P (pBad thB ℓ) 0) :
    IsQueryBoundP (interpA P) (MsgPrf.markK ikey okey)
      (qf * 1 + nL * thashCost thB + (qs + 1) * hmsgCost ℓ) := by
  unfold interpA
  refine qb_simulateQ_classes (p₀ := pBad thB ℓ) (p₁ := pPort) (p₂ := pLong) (p₃ := pHm)
    1 (thashCost thB) (hmsgCost ℓ) (fun t ht => ?_)
    (lazyRes_bound_liftP _ _ P 0 hbad) (lazyRes_bound_liftP _ _ P _ hport)
    (lazyRes_bound_liftP _ _ P _ hlong) (lazyRes_bound_liftP _ _ P _ hhm)
  rcases t with n | (q | d) | (u | h)
  · exact (isQueryBoundP_query_iff _ _ _).2 fun h => h.elim
  · exact (isQueryBoundP_query_iff _ _ _).2 fun _ => by simp [liftP]
  · exact (isQueryBoundP_query_iff _ _ _).2 fun h => h.elim
  · exact (liftM_zero (X := hS St Blk + msgG Rd) ($ᵗ Rd.Y) (MsgPrf.markK ikey okey)
      fun n h => h).mono (Nat.zero_le _)
  · rcases h with ⟨pk, a, xs⟩ | ⟨R, pk, root, M⟩
    · have hx : xs.length ≤ thB := by
        simp only [pBad, liftP, longH, decide_eq_true_eq, not_lt] at ht
        exact ht
      by_cases hl : 2 < List.length (α := Bytes 16) xs
      · refine (cEmb_markKR _ _ (thashC_bound pk a xs)).mono ?_
        simp only [liftP, longTh, isHm, show 2 < List.length (α := Rd.Y) xs from hl, decide_true,
          ite_true, ite_false, Bool.false_eq_true, add_zero, zero_add]
        exact thashCost_mono hx
      · exact (cEmb_markK _ _ (thashC_markK pk a xs (by omega))).mono (Nat.zero_le _)
    · have hM : M.length ≤ ℓ := by
        simp only [pBad, liftP, longH, decide_eq_true_eq, not_lt] at ht
        exact ht
      refine (cEmb_markKR _ _ (hmsgC_bound R pk root M)).mono ?_
      simpa [liftP, longTh, isHm] using hmsgCost_mono hM

end Counts

/-! ## Long `Thash` queries of the port programs -/

section Programs

attribute [local instance] Reduction.Lazy.openQ

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]

variable (p : OIdx prims → Prop) [DecidablePred p]

theorem openKeygen_w (pkSeed : prims.PkSeed) (hsec : ∀ d, ¬ p (.inr (.inr (.inl d))))
    (h1 : ∀ key xs, xs.length ≤ 2 → ¬ p (.inr (.inr (.inr (.thash pkSeed key xs))))) :
    IsQueryBoundP (openKeygen prims (GP prims) pkSeed) p
      (Lazy.merkleB (Lazy.wotsB vp 0 0 + 1) 0 vp.params.hp) :=
  Lazy.qb_xmssNode p prims.core 0 1 0 0
    (hash := PublicHash.f prims.core pkSeed) (compress := PublicHash.tl prims.core pkSeed)
    (nodeHash := PublicHash.h prims.core pkSeed) (secret := secQ prims (GP prims))
    (fun _ _ => (isQueryBoundP_query_iff _ _ _).2 fun h => absurd h (h1 _ _ (by simp)))
    (fun _ _ => (isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos)
    (fun _ _ _ => (isQueryBoundP_query_iff _ _ _).2 fun h => absurd h (h1 _ _ (by simp)))
    (fun _ => (isQueryBoundP_query_iff _ _ _).2 fun h => absurd h (hsec _)) _ _ _

theorem openSign_w (msg : List Byte) (pkSeed : prims.PkSeed) (pkRoot R : prims.Y)
    (hsec : ∀ d, ¬ p (.inr (.inr (.inl d))))
    (h1 : ∀ key xs, xs.length ≤ 2 → ¬ p (.inr (.inr (.inr (.thash pkSeed key xs)))))
    (hm : ∀ R pkSeed root M, ¬ p (.inr (.inr (.inr (.hmsg R pkSeed root M))))) :
    IsQueryBoundP (Lazy.openSign prims (GP prims) msg pkSeed pkRoot R) p (signLongB vp) := by
  have hf : ∀ (a : Adrs) (y : prims.core.Y), IsQueryBoundP (PublicHash.f prims.core pkSeed a y :
      OracleComp (OSpec prims (GP prims)) prims.Y) p 0 :=
    fun _ _ => (isQueryBoundP_query_iff _ _ _).2 fun h => absurd h (h1 _ _ (by simp))
  have htl : ∀ (a : Adrs) (ys : List prims.core.Y),
      IsQueryBoundP (PublicHash.tl prims.core pkSeed a ys :
      OracleComp (OSpec prims (GP prims)) prims.Y) p 1 :=
    fun _ _ => (isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos
  have hh : ∀ (a : Adrs) (l r : prims.core.Y),
      IsQueryBoundP (PublicHash.h prims.core pkSeed a l r :
      OracleComp (OSpec prims (GP prims)) prims.Y) p 0 :=
    fun _ _ _ => (isQueryBoundP_query_iff _ _ _).2 fun h => absurd h (h1 _ _ (by simp))
  have hs : ∀ a : Adrs, IsQueryBoundP (secQ prims (GP prims) a) p 0 :=
    fun _ => (isQueryBoundP_query_iff _ _ _).2 fun h => absurd h (hsec _)
  have hm' : IsQueryBoundP (PublicHash.hmsg prims.core R pkSeed pkRoot msg :
      OracleComp (OSpec prims (GP prims)) _) p 0 :=
    (isQueryBoundP_query_iff _ _ _).2 fun h => absurd h (hm _ _ _ _)
  unfold Lazy.openSign GeneralScheme.signInternalWithSecretRandomizerM
  exact (Lazy.qb_bind p hm' fun digest =>
    Lazy.qb_bind p (Lazy.qb_forsSign p prims.core 0 0 0 hf hh hs _ _) fun forsSig =>
      Lazy.qb_bind p (Lazy.qb_forsPk p prims.core 0 1 0 hf htl hh forsSig _ _) fun forsPk =>
        Lazy.qb_bind p (m := 0) (Lazy.qb_signFromPos p prims.core 0 1 0 0 hf htl hh hs _ _ _ _ _)
          fun htSig => isQueryBoundP_pure _ _ _).mono (by unfold signLongB; omega)

end Programs

section Instances

variable (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) (pkSeedDist : ProbComp (Bytes 16))
  (S : ForgerI) {qf qs ℓ : ℕ}

theorem hu_pl : ∀ n : ℕ, ¬ (pLong : OIdx Rd → Prop) (.inl n) := by
  intro n; simp [liftP]

theorem keygen_pl (pkSeed : Rd.PkSeed) :
    IsQueryBoundP (openKeygen Rd (GP Rd) pkSeed) (pLong : OIdx Rd → Prop) 512 :=
  (openKeygen_w _ pkSeed (fun d => by simp [liftP])
    (fun key xs hx => by simp [liftP, longTh]; omega)).mono keygenLong_128s.le

theorem sign_pl (pk : PublicKeyCore Rd.core) (m : List Byte) :
    IsQueryBoundP (msgSignOP (optRand₀ oR) pk m) (pLong : OIdx Rd → Prop) 3585 :=
  (msgSignOP_bound (optRand₀ oR) pLong hu_pl pk m 0 3585
    (fun a => (gameQ_bound _ _).mono (by simp [liftP]))
    (fun R => (openSign_w _ m _ _ R (fun d => by simp [liftP])
      (fun key xs hx => by simp [liftP, longTh]; omega)
      (fun R pkSeed root M => by simp [liftP, longTh])).mono signLongB_128s.le)).mono (by omega)

theorem verify_pl (pk : PublicKeyCore Rd.core) (msg : List Byte)
    (sig : GeneralScheme.SignatureCore Link.vp Rd.core) :
    IsQueryBoundP (GeneralScheme.verifyInternalM Link.vp Rd.core msg sig pk :
      OracleComp (publicHashSpec Rd.core) Bool) (fun q => longTh q = true) 8 :=
  (verifyM_long Rd.core _ msg sig pk (fun key xs hx => by simp [longTh]; omega)
    (fun R pkSeed root M => by simp [longTh])).mono verifyLong_128s.le

/-- **Long `Thash` queries of the SUF port program.** -/
theorem PmsgS_long (hF : PortBounds (mainC S) qf qs ℓ) :
    IsQueryBoundP (PmsgS S oR pkSeedDist) pLong (512 + (qf * 0 + qs * 3585) + 8) := by
  unfold PmsgS
  exact msgOpenWVP_bound (prims := Rd) (optRand₀ oR) pkSeedDist pLong sufCheckO (mainC S) qf qs ℓ 512 3585 0 8 hF
    hu_pl keygen_pl (fun pk m _ => sign_pl oR pk m)
    (fun q => (gameQ_bound _ _).mono (by simp [liftP]))
    (fun pk f log _ => embR_bound _ _ _ 8 (by
      unfold sufCheckO
      rw [isQueryBoundP_map_iff]
      exact verify_pl pk f.1 f.2))

/-- **Long `Thash` queries of the EUF port program.** -/
theorem PmsgE_long (hF : PortBounds (mainC S) qf qs ℓ) :
    IsQueryBoundP (PmsgE S oR pkSeedDist) pLong (512 + (qf * 0 + qs * 3585) + 8) := by
  unfold PmsgE
  exact msgOpenVP_bound (prims := Rd) (optRand₀ oR) pkSeedDist pLong (mainC S) qf qs ℓ 512 3585 0 8 hF
    hu_pl keygen_pl (fun pk m _ => sign_pl oR pk m)
    (fun q => (gameQ_bound _ _).mono (by simp [liftP]))
    (fun pk msgs msg sig _ => embR_bound _ _ _ 8 (by
      unfold eufCheckO
      rw [isQueryBoundP_map_iff]
      exact verify_pl pk msg sig))

end Instances

/-! ## The realisers -/

/-- **HMAC-key-block-shaped compression queries of the `PRF_msg` realisers.** -/
def qMsgM (qf qs ℓ : ℕ) : ℕ :=
  qf * 1 + (512 + (qf * 0 + qs * 3585) + 8) * thashCost thB + (qs + 1) * hmsgCost ℓ

section Realizers

variable (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
  (pkSeedDist : ProbComp (Bytes 16)) {qf qs ℓ : ℕ}
  (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List Byte) i = true) qf)
  (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List Byte) i = true) qs)
  (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQ (S := List Byte) ℓ i = true) 0)
  (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ)

include hqf hqs hlong hout

theorem AmsgS_mark :
    IsQueryBoundP (AmsgS S oR pkSeedDist) (MsgPrf.markK ikey okey) (qMsgM qf qs ℓ) :=
  have hF := mainC_bounds S hqf hqs hlong hout
  interp_mark _ (msgOpenWVP_port _ _ hF) (PmsgS_long oR pkSeedDist S hF) (msgOpenWVP_hm _ _ hF)
    (msgOpenWVP_bad _ _ hF thB okLen_le)

theorem AmsgE_mark :
    IsQueryBoundP (AmsgE S oR pkSeedDist) (MsgPrf.markK ikey okey) (qMsgM qf qs ℓ) :=
  have hF := mainC_bounds S hqf hqs hlong hout
  interp_mark _ (msgOpenVP_port _ _ hF) (PmsgE_long oR pkSeedDist S hF) (msgOpenVP_hm _ _ hF)
    (msgOpenVP_bad _ _ hF thB okLen_le)

theorem realizesMsgSuf_mark :
    IsQueryBoundP (realizesMsgSuf S oR pkSeedDist hqf hqs hlong hout).A (MsgPrf.markK ikey okey)
      (qMsgM qf qs ℓ) :=
  AmsgS_mark S oR pkSeedDist hqf hqs hlong hout

theorem realizesMsgEuf_mark :
    IsQueryBoundP (realizesMsgEuf S oR pkSeedDist hqf hqs hlong hout).A (MsgPrf.markK ikey okey)
      (qMsgM qf qs ℓ) :=
  AmsgE_mark S oR pkSeedDist hqf hqs hlong hout

end Realizers

/-- Closed form of `qMsgM`. -/
theorem qMsgM_le (qf qs ℓ : ℕ) : qMsgM qf qs ℓ ≤ qf + (qs + 1) * (39438 + (ℓ + 56) / 64) := by
  unfold qMsgM hmsgCost
  rw [thashCost_thB]
  generalize (ℓ + 56) / 64 = x
  ring_nf
  omega

end Ideal.Realize.Msg

#print axioms Ideal.msgPrf_bound_128s_marked
#print axioms Ideal.Realize.Msg.interp_mark
#print axioms Ideal.Realize.Msg.PmsgS_long
#print axioms Ideal.Realize.Msg.AmsgS_mark
#print axioms Ideal.Realize.Msg.AmsgE_mark
#print axioms Ideal.Realize.Msg.qMsgM_le
