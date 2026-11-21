import MLink.Climb

/-!
# WOTS+ (FIPS 205 §5): `Spec` = VCVio, all six SHA-2 parameter sets
-/

namespace MLink

open SLHDSA

/-- A `WOTS_HASH`-typed base address (key pair set) inside the SHA-2 address domain. -/
def WotsDom (a : SLHDSA.Adrs) : Prop :=
  a.type = 0 ∧ a.layer < 256 ∧ a.tree < 2 ^ 64 ∧ a.word1 < 2 ^ 32

variable (S : Sha2Set)

/-! ### Numeric facts used below (all six sets, by evaluation) -/

/-- `len ∈ {35, 51, 67}`: never `1`, so `T_len` is never VCVio's singleton (`F`) case. -/
theorem Sha2Set.len_ne_one (S : Sha2Set) : S.vp.params.len ≠ 1 := by cases S <;> decide
theorem Sha2Set.len_lt (S : Sha2Set) : S.vp.params.len < 2 ^ 32 := by cases S <;> decide
/-- The `len1 = 2n` message digits use exactly the `8n` bits of a node. -/
theorem Sha2Set.len1_mul_lgw (S : Sha2Set) : S.spec.len1 * S.spec.lgw = 8 * S.vp.params.n := by
  cases S <;> rfl
theorem Sha2Set.spec_w (S : Sha2Set) : S.spec.w = 16 := by cases S <;> rfl
theorem Sha2Set.spec_len (S : Sha2Set) : S.spec.len = 2 * S.spec.n + 3 := by cases S <;> decide

/-- Algorithm 5, `chain`, when every visited hash address is in the domain. -/
theorem chain_eq (pk : S.Node) (a : SLHDSA.Adrs) (x : S.Node) (i s : ℕ)
    (h : ∀ j, i ≤ j → j < i + s → Dom (a.setHashAddress j)) :
    nd (SLHDSA.chain S.prims pk a x i s) = Spec.chain S.spec (nd x) i s (nd pk) (adr a) := by
  induction s with
  | zero => rfl
  | succ s ih =>
    have e : SLHDSA.chain S.prims pk a x i (s + 1) =
        S.prims.F pk (a.setHashAddress (i + s)) (SLHDSA.chain S.prims pk a x i s) :=
      SLHDSA.chain_succ S.prims pk a x i s
    refine (congrArg nd e).trans ?_
    have h1 := F_eq S pk (a.setHashAddress (i + s)) (h _ (by omega) (by omega))
      (SLHDSA.chain S.prims pk a x i s)
    rw [ih (fun j h1 h2 => h j h1 (by omega))] at h1
    rw [h1]
    simp [Spec.chain, List.range_succ, adr, Adrs.setHashAddress]

/-- `Spec.chain` overwrites word 3 of its address before every use. -/
theorem specChain_word3 (p : Spec.Params) (x : Spec.Bytes) (i s : ℕ) (pk : Spec.Bytes)
    (a : Spec.Adrs) (v : ℕ) :
    Spec.chain p x i s pk { a with word3 := v } = Spec.chain p x i s pk a := rfl

/-- The spec's checksum fold is the complementary checksum. -/
theorem checksum_foldl (w : ℕ) (ds : List ℕ) (c : ℕ) :
    ds.foldl (fun c x => c + (w - 1 - x)) c = c + (ds.map (fun d => w - 1 - d)).sum := by
  induction ds generalizing c with
  | nil => simp
  | cons d ds ih => simp [ih]; omega

/-- The `len = 2n + 3` base-16 digits (message and checksum) of Algorithm 7 lines 1–7. -/
theorem wotsDigits_eq (msg : S.Node) :
    chainLengthsCore S.prims.core msg = Spec.wotsDigits S.spec (nd msg) := by
  have hm : SLHDSA.base2b msg.toList S.spec.lgw S.spec.len1 =
      Spec.base2b (nd msg) S.spec.lgw S.spec.len1 :=
    base2b_eq msg.toList _ _ (by rw [S.len1_mul_lgw]; simp)
  have hc : ∀ v, SLHDSA.base2b (SLHDSA.toByte v ((S.spec.len2 * S.spec.lgw + 7) / 8))
        S.spec.lgw S.spec.len2 =
      Spec.base2b (Spec.toByte v ((S.spec.len2 * S.spec.lgw + 7) / 8)) S.spec.lgw S.spec.len2 := by
    intro v
    rw [base2b_eq _ _ _ (by rw [toByte_length]; omega), toByte_eq]
  have hy : (S.prims.core.yToBytes msg).toList = msg.toList := rfl
  unfold chainLengthsCore wotsMsgDigitsCore WotsEncoding.fullDigits WotsEncoding.checksumDigits
    WotsEncoding.checksumBytes WotsEncoding.shiftedChecksumValue WotsChecksum.wotsChecksumValue
    VCVio.Algorithms.ComplementaryChecksum.value WotsEncoding.checksumByteLength
    WotsEncoding.checksumShift WotsEncoding.checksumBitLength
  rw [S.lgw_eq, S.len1_eq, S.len2_eq, S.w_eq, hy, hc, hm]
  have h0 := checksum_foldl S.spec.w (Spec.base2b (nd msg) S.spec.lgw S.spec.len1) 0
  simp only [Nat.zero_add] at h0
  rw [← h0]
  rfl

theorem wotsDigits_length (msg : S.Node) :
    (Spec.wotsDigits S.spec (nd msg)).length = S.vp.params.len := by
  rw [← wotsDigits_eq]; exact chainLengthsCore_length S.prims.core msg

theorem chainSteps_eq (msg : S.Node) (i : ℕ) :
    chainStepsCore S.prims.core msg i = (Spec.wotsDigits S.spec (nd msg))[i]! := by
  unfold chainStepsCore
  rw [wotsDigits_eq]
  simp [List.getD_eq_getElem?_getD]

theorem chainSteps_lt (msg : S.Node) (i : ℕ) : chainStepsCore S.prims.core msg i < 16 := by
  have := chainStepsCore_lt S.prims.core msg i
  rwa [S.w_sixteen] at this

theorem wotsChain_dom (a : SLHDSA.Adrs) (ha : WotsDom a) (i j : ℕ) (hi : i < 2 ^ 32)
    (hj : j < 2 ^ 32) : Dom ((wotsChainAdrs a i).setHashAddress j) := by
  obtain ⟨ht, hl, htr, hw⟩ := ha
  refine ⟨?_, ?_, ?_⟩
  · simp only [wotsChainAdrs, Adrs.setTypeAndClear, Adrs.setKeyPairAddress,
      Adrs.setChainAddress, Adrs.setHashAddress, Adrs.getKeyPairAddress,
      Adrs.isCanonical, Adrs.Fits, AddrType.toCode, AddrType.ofCode]
    simp only [Bool.and_eq_true]
    refine ⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩ <;>
      first | rfl | (apply decide_eq_true; omega) | simp
  · simp only [wotsChainAdrs, Adrs.setTypeAndClear, Adrs.setKeyPairAddress,
      Adrs.setChainAddress, Adrs.setHashAddress, Adrs.Fits]
    apply decide_eq_true; omega
  · simp only [wotsChainAdrs, Adrs.setTypeAndClear, Adrs.setKeyPairAddress,
      Adrs.setChainAddress, Adrs.setHashAddress, Adrs.Fits]
    apply decide_eq_true; omega

theorem wotsPk_dom (a : SLHDSA.Adrs) (ha : WotsDom a) : Dom (wotsPkAdrs a) := by
  obtain ⟨ht, hl, htr, hw⟩ := ha
  refine ⟨?_, ?_, ?_⟩
  · simp only [wotsPkAdrs, Adrs.setTypeAndClear, Adrs.setKeyPairAddress,
      Adrs.getKeyPairAddress, Adrs.isCanonical, Adrs.Fits, AddrType.toCode, AddrType.ofCode]
    simp only [Bool.and_eq_true]
    refine ⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩ <;>
      first | rfl | (apply decide_eq_true; omega)
  · simp only [wotsPkAdrs, Adrs.setTypeAndClear, Adrs.setKeyPairAddress, Adrs.Fits]
    apply decide_eq_true; omega
  · simp only [wotsPkAdrs, Adrs.setTypeAndClear, Adrs.setKeyPairAddress, Adrs.Fits]
    apply decide_eq_true; omega

/-- Algorithm 8, `wots_pkFromSig`. -/
theorem wotsPkFromSig_eq (sig : WotsSig S.vp.params S.prims.core) (msg pk : S.Node)
    (a : SLHDSA.Adrs) (ha : WotsDom a) :
    nd (SLHDSA.wotsPkFromSig S.prims sig msg pk a) =
      Spec.wotsPkFromSig S.spec (nds sig.toList) (nd msg) (nd pk) (adr a) := by
  have e : SLHDSA.wotsPkFromSig S.prims sig msg pk a =
      S.prims.Tl pk (wotsPkAdrs a) (Vector.ofFn fun i : Fin S.vp.params.len =>
        SLHDSA.chain S.prims pk (wotsChainAdrs a i.val) sig[i.val]
          (chainStepsCore S.prims.core msg i.val)
          (S.vp.params.w - 1 - chainStepsCore S.prims.core msg i.val)).toList := by
    have e1 := wotsPkFromSig_eq_tl S.prims sig msg pk a
    have e2 := wotsPkFromSigTops_eq_ofFn S.prims sig msg pk a
    exact e1.trans (congrArg (fun v => S.prims.Tl pk (wotsPkAdrs a) v.toList) e2)
  refine (congrArg nd e).trans ?_
  refine (Tl_eq S pk _ (wotsPk_dom a ha) _
    (fun h => S.len_ne_one (Vector.length_toList.symm.trans h))).trans ?_
  have key : nds (Vector.ofFn fun i : Fin S.vp.params.len =>
        SLHDSA.chain S.prims pk (wotsChainAdrs a i.val) sig[i.val]
          (chainStepsCore S.prims.core msg i.val)
          (S.vp.params.w - 1 - chainStepsCore S.prims.core msg i.val)).toList =
      (List.range S.vp.params.len).flatMap fun i =>
        Spec.chain S.spec (Spec.block S.spec (nds sig.toList) i)
          (Spec.wotsDigits S.spec (nd msg))[i]!
          (S.spec.w - 1 - (Spec.wotsDigits S.spec (nd msg))[i]!) (nd pk)
          { adr a with word2 := i } := by
    refine nds_ofFn _ _ ?_
    intro i
    have hi' : i.val < S.vp.params.len := i.isLt
    have hlt := chainSteps_lt S msg i.val
    have hw := S.w_sixteen
    have hc := chain_eq S pk (wotsChainAdrs a i.val) sig[i.val]
      (chainStepsCore S.prims.core msg i.val)
      (S.vp.params.w - 1 - chainStepsCore S.prims.core msg i.val)
      (fun j _ hj => wotsChain_dom a ha i.val j (lt_trans hi' S.len_lt) (by omega))
    refine hc.trans ?_
    rw [chainSteps_eq]
    have hb : Spec.block S.spec (nds sig.toList) i.val = nd sig[i.val] := by
      have hl : sig.toList.length = S.vp.params.len := Vector.length_toList
      have hb' := block_nds S sig.toList i.val (lt_of_lt_of_eq hi' hl.symm)
      rw [hb']
      congr 1
    rw [hb]
    have hadr2 : adr (wotsChainAdrs a i.val) =
        { ({ adr a with word2 := i.val } : Spec.Adrs) with word3 := 0 } := by
      simp [adr, wotsChainAdrs, Adrs.setTypeAndClear, Adrs.setKeyPairAddress,
        Adrs.setChainAddress, Adrs.getKeyPairAddress, AddrType.toCode, ha.1]
    rw [hadr2, specChain_word3, S.w_eq]
  refine (congrArg (Spec.T S.spec (nd pk) (Spec.wotsPkAdrs (adr a))) key).trans ?_
  unfold Spec.wotsPkFromSig
  rw [← S.len_eq]

end MLink

#print axioms MLink.chain_eq
#print axioms MLink.wotsDigits_eq
#print axioms MLink.wotsPkFromSig_eq
