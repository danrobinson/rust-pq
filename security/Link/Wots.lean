import Link.Hash

/-!
# WOTS+ (FIPS 205 §5): `Spec` = VCVio
-/

namespace Link

open SLHDSA

/-- A `WOTS_HASH`-typed base address (key pair set) inside the SHA-2 address domain. -/
def WotsDom (a : SLHDSA.Adrs) : Prop :=
  a.type = 0 ∧ a.layer < 256 ∧ a.tree < 2 ^ 64 ∧ a.word1 < 2 ^ 32

/-- Algorithm 5, `chain`, when every visited hash address is in the domain. -/
theorem chain_eq (pk : Node) (a : SLHDSA.Adrs) (x : Node) (i s : ℕ)
    (h : ∀ j, i ≤ j → j < i + s → Dom (a.setHashAddress j)) :
    nd (SLHDSA.chain prims pk a x i s) = Spec.chain (nd x) i s (nd pk) (adr a) := by
  induction s with
  | zero => rfl
  | succ s ih =>
    have e : SLHDSA.chain prims pk a x i (s + 1) =
        prims.F pk (a.setHashAddress (i + s)) (SLHDSA.chain prims pk a x i s) :=
      SLHDSA.chain_succ prims pk a x i s
    refine (congrArg nd e).trans ?_
    have h1 := F_eq pk (a.setHashAddress (i + s)) (h _ (by omega) (by omega))
      (SLHDSA.chain prims pk a x i s)
    rw [ih (fun j h1 h2 => h j h1 (by omega))] at h1
    rw [h1]
    simp [Spec.chain, List.range_succ, adr, Adrs.setHashAddress]

/-- `Spec.chain` overwrites word 3 of its address before every use. -/
private theorem specChain_word3 (x : Spec.Bytes) (i s : ℕ) (pk : Spec.Bytes) (a : Spec.Adrs) (v : ℕ) :
    Spec.chain x i s pk { a with word3 := v } = Spec.chain x i s pk a := rfl

/-- The spec's checksum fold is the complementary checksum. -/
private theorem checksum_foldl (ds : List ℕ) (c : ℕ) :
    ds.foldl (fun c x => c + (16 - 1 - x)) c = c + (ds.map (fun d => 16 - 1 - d)).sum := by
  induction ds generalizing c with
  | nil => simp
  | cons d ds ih => simp [ih]; omega

/-- The `len = 35` base-16 digits (message and checksum) of Algorithm 7 lines 1–7. -/
theorem wotsDigits_eq (msg : Node) :
    chainLengthsCore prims.core msg = Spec.wotsDigits (nd msg) := by
  have hm : SLHDSA.base2b msg.toList 4 32 = Spec.base2b (nd msg) 4 32 :=
    base2b_eq msg.toList 4 32 (by simp)
  have hc : ∀ v, SLHDSA.base2b (SLHDSA.toByte v 2) 4 3 = Spec.base2b (Spec.toByte v 2) 4 3 := by
    intro v
    rw [base2b_eq _ 4 3 (by simp), toByte_eq]
  have hlgw : vp.params.lgw = 4 := rfl
  have hlen1 : vp.params.len1 = 32 := rfl
  have hlen2 : vp.params.len2 = 3 := rfl
  have hw : vp.params.w = 16 := rfl
  have hbl : WotsEncoding.checksumByteLength vp.params = 2 := rfl
  have hsh : WotsEncoding.checksumShift vp.params = 4 := rfl
  have hy : (prims.core.yToBytes msg).toList = msg.toList := rfl
  unfold chainLengthsCore wotsMsgDigitsCore WotsEncoding.fullDigits WotsEncoding.checksumDigits
    WotsEncoding.checksumBytes WotsEncoding.shiftedChecksumValue WotsChecksum.wotsChecksumValue
    VCVio.Algorithms.ComplementaryChecksum.value
  rw [hlgw, hlen1, hlen2, hw, hbl, hsh, hy, hc, hm]
  have h0 := checksum_foldl (Spec.base2b (nd msg) 4 32) 0
  simp only [Nat.zero_add] at h0
  rw [← h0]
  rfl

private theorem wotsDigits_length (msg : Node) : (Spec.wotsDigits (nd msg)).length = 35 := by
  rw [← wotsDigits_eq]; exact chainLengthsCore_length prims.core msg

private theorem chainSteps_eq (msg : Node) (i : ℕ) :
    chainStepsCore prims.core msg i = (Spec.wotsDigits (nd msg))[i]! := by
  unfold chainStepsCore
  rw [wotsDigits_eq]
  simp [List.getD_eq_getElem?_getD]

private theorem chainSteps_lt (msg : Node) (i : ℕ) : chainStepsCore prims.core msg i < 16 :=
  chainStepsCore_lt prims.core msg i

/-- The `j`-th block of a concatenation of nodes. -/
private theorem block_nds' (ys : List Node) (j : ℕ) (hj : j < ys.length) :
    Spec.block (nds ys) j = nd ys[j] := by
  induction ys generalizing j with
  | nil => simp at hj
  | cons y ys ih =>
    cases j with
    | zero => simp [Spec.block, nds, Spec.n]
    | succ j =>
      have := ih j (by simpa using hj)
      simp only [Spec.block, nds, Spec.n] at this ⊢
      rw [List.flatMap_cons, Nat.succ_mul, Nat.add_comm (j * 16) 16, ← List.drop_drop,
        List.drop_left' (nd_length y)]
      exact this

private theorem wotsChain_dom (a : SLHDSA.Adrs) (ha : WotsDom a) (i j : ℕ) (hi : i < 35) (hj : j < 16) :
    Dom ((wotsChainAdrs a i).setHashAddress j) := by
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

private theorem wotsPk_dom (a : SLHDSA.Adrs) (ha : WotsDom a) : Dom (wotsPkAdrs a) := by
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

private theorem nds_ofFn (f : Fin 35 → Node) :
    nds (Vector.ofFn f).toList =
      (List.range 35).flatMap fun i => if h : i < 35 then nd (f ⟨i, h⟩) else [] := by
  simp only [nds, Vector.toList_ofFn, List.ofFn_eq_map, List.flatMap_map]
  rw [← List.map_coe_finRange_eq_range (n := 35), List.flatMap_map]
  congr 1
  funext i
  simp

/-- Algorithm 8, `wots_pkFromSig`. -/
theorem wotsPkFromSig_eq (sig : WotsSig vp.params prims.core) (msg pk : Node)
    (a : SLHDSA.Adrs) (ha : WotsDom a) :
    nd (SLHDSA.wotsPkFromSig prims sig msg pk a) =
      Spec.wotsPkFromSig (nds sig.toList) (nd msg) (nd pk) (adr a) := by
  have e : SLHDSA.wotsPkFromSig prims sig msg pk a =
      prims.Tl pk (wotsPkAdrs a) (Vector.ofFn fun i : Fin 35 =>
        SLHDSA.chain prims pk (wotsChainAdrs a i.val) sig[i.val]
          (chainStepsCore prims.core msg i.val)
          (16 - 1 - chainStepsCore prims.core msg i.val)).toList := by
    have e1 := wotsPkFromSig_eq_tl prims sig msg pk a
    have e2 := wotsPkFromSigTops_eq_ofFn prims sig msg pk a
    exact e1.trans (congrArg (fun v => prims.Tl pk (wotsPkAdrs a) v.toList) e2)
  refine (congrArg nd e).trans ?_
  refine (Tl_eq pk _ (wotsPk_dom a ha) _).trans ?_
  have key : nds (Vector.ofFn fun i : Fin 35 =>
        SLHDSA.chain prims pk (wotsChainAdrs a i.val) sig[i.val]
          (chainStepsCore prims.core msg i.val)
          (16 - 1 - chainStepsCore prims.core msg i.val)).toList =
      (List.range Spec.len).flatMap fun i =>
        Spec.chain (Spec.block (nds sig.toList) i) (Spec.wotsDigits (nd msg))[i]!
          (Spec.w - 1 - (Spec.wotsDigits (nd msg))[i]!) (nd pk) { adr a with word2 := i } := by
    refine (nds_ofFn _).trans ?_
    apply List.flatMap_congr
    intro i hi
    have hi' : i < 35 := List.mem_range.mp hi
    rw [dif_pos hi']
    have hlt := chainSteps_lt msg i
    have hc := chain_eq pk (wotsChainAdrs a i) sig[i] (chainStepsCore prims.core msg i)
      (16 - 1 - chainStepsCore prims.core msg i)
      (fun j _ hj => wotsChain_dom a ha i j hi' (by omega))
    refine hc.trans ?_
    rw [chainSteps_eq]
    have hb : Spec.block (nds sig.toList) i = nd sig[i] := by
      have hl : sig.toList.length = 35 := Vector.length_toList
      have hb' := block_nds' sig.toList i (lt_of_lt_of_eq hi' hl.symm)
      rw [hb']
      congr 1
    rw [hb]
    have hadr2 : adr (wotsChainAdrs a i) =
        { ({ adr a with word2 := i } : Spec.Adrs) with word3 := 0 } := by
      simp [adr, wotsChainAdrs, Adrs.setTypeAndClear, Adrs.setKeyPairAddress,
        Adrs.setChainAddress, Adrs.getKeyPairAddress, AddrType.toCode, ha.1]
    rw [hadr2, specChain_word3]
    rfl
  exact congrArg (Spec.T (nd pk) (Spec.wotsPkAdrs (adr a))) key

end Link

#print axioms Link.chain_eq
#print axioms Link.wotsDigits_eq
#print axioms Link.wotsPkFromSig_eq
