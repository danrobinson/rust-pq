import Link.Keygen
import Mathlib.Data.Nat.Bitwise

/-!
# Signing components (FIPS 205 Algorithms 7, 10, 16): `Spec` = VCVio
-/

namespace Link

open SLHDSA SLHDSA.Concrete

/-! ### Generic helpers -/

private theorem sibling_eq_xor_one (i : ℕ) : PerfectMerkleTree.sibling i = i ^^^ 1 := by
  unfold PerfectMerkleTree.sibling
  by_cases h : i % 2 = 0
  · rw [ite_eq_left h]
    exact (Nat.xor_one_of_even (by simpa [Nat.even_iff] using h)).symm
  · rw [ite_eq_right h]
    exact (Nat.xor_one_of_odd (by simpa [Nat.odd_iff] using h)).symm

/-- The flat reading of an intrinsic authentication path, entry by entry (FIPS `xor 1` form). -/
private theorem nds_authPath (leaf : ℕ → Node) (nodeHash : ℕ → ℕ → Node → Node → Node)
    (idx z : ℕ) (g : ℕ → Spec.Bytes)
    (h : ∀ j, j < z →
      nd (PerfectMerkleTree.merkleRoot leaf nodeHash j ((idx / 2 ^ j) ^^^ 1)) = g j) :
    nds (PerfectMerkleTree.intrinsicAuthPath leaf nodeHash idx z).toList =
      (List.range z).flatMap g := by
  induction z with
  | zero => rfl
  | succ z ih =>
    have hz := h z (Nat.lt_succ_self z)
    rw [← sibling_eq_xor_one] at hz
    rw [PerfectMerkleTree.intrinsicAuthPath, Vector.toList_push, List.range_succ,
      List.flatMap_append, nds, List.flatMap_append, ← nds, ih (fun j hj => h j (by omega))]
    simp [hz]

private theorem flatMap_ofFn {α : Type} {n : ℕ} (f : Fin n → α) (F : α → Spec.Bytes)
    (g : ℕ → Spec.Bytes) (h : ∀ i : Fin n, F (f i) = g i.val) :
    (Vector.ofFn f).toList.flatMap F = (List.range n).flatMap g := by
  rw [Vector.toList_ofFn, List.ofFn_eq_map, ← List.map_coe_finRange_eq_range,
    List.flatMap_map, List.flatMap_map]
  congr 1
  funext i
  exact h i

private theorem xor_one_lt (x m : ℕ) (h : x < 2 ^ (m + 1)) : x ^^^ 1 < 2 ^ (m + 1) := by
  rw [← sibling_eq_xor_one]
  unfold PerfectMerkleTree.sibling
  rw [pow_succ] at h ⊢
  split <;> omega

private theorem fors_sib (i f j : ℕ) (hj : j < 12) :
    ((i * 2 ^ 12 + f) / 2 ^ j) ^^^ 1 = i * 2 ^ (12 - j) + ((f / 2 ^ j) ^^^ 1) := by
  have h1 : i * 2 ^ 12 + f = f + 2 ^ j * (2 * (i * 2 ^ (11 - j))) := by
    have : (2:ℕ) ^ 12 = 2 ^ j * (2 * 2 ^ (11 - j)) := by
      rw [← pow_succ', ← pow_add]; congr 1; omega
    rw [this]; ring
  have h2 : i * 2 ^ (12 - j) = 2 * (i * 2 ^ (11 - j)) := by
    have : 12 - j = (11 - j) + 1 := by omega
    rw [this, pow_succ]; ring
  rw [h1, Nat.add_mul_div_left _ _ (by positivity), h2,
    ← sibling_eq_xor_one, ← sibling_eq_xor_one]
  generalize i * 2 ^ (11 - j) = e
  generalize f / 2 ^ j = x
  unfold PerfectMerkleTree.sibling
  split <;> split <;> omega

/-! ### WOTS+ signing -/

private theorem specChain_word3' (x : Spec.Bytes) (i s : ℕ) (pk : Spec.Bytes) (a : Spec.Adrs)
    (v : ℕ) : Spec.chain x i s pk { a with word3 := v } = Spec.chain x i s pk a := rfl

private theorem chainSteps_eq' (msg : Node) (i : ℕ) :
    chainStepsCore prims.core msg i = (Spec.wotsDigits (nd msg))[i]! := by
  unfold chainStepsCore
  rw [wotsDigits_eq]
  simp [List.getD_eq_getElem?_getD]

private theorem wotsChain_dom' (a : SLHDSA.Adrs) (ha : WotsDom a) (i j : ℕ) (hi : i < 35)
    (hj : j < 16) : Dom ((wotsChainAdrs a i).setHashAddress j) := by
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

private theorem wotsSk_dom (a : SLHDSA.Adrs) (ha : WotsDom a) (i : ℕ) (hi : i < 35) :
    Dom (wotsSkAdrs a i) := by
  obtain ⟨ht, hl, htr, hw⟩ := ha
  refine ⟨?_, ?_, ?_⟩
  · simp only [wotsSkAdrs, Adrs.setTypeAndClear, Adrs.setKeyPairAddress,
      Adrs.setChainAddress, Adrs.getKeyPairAddress,
      Adrs.isCanonical, Adrs.Fits, AddrType.toCode, AddrType.ofCode]
    simp only [Bool.and_eq_true]
    refine ⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩ <;>
      first | rfl | (apply decide_eq_true; omega)
  · simp only [wotsSkAdrs, Adrs.setTypeAndClear, Adrs.setKeyPairAddress,
      Adrs.setChainAddress, Adrs.Fits]
    apply decide_eq_true; omega
  · simp only [wotsSkAdrs, Adrs.setTypeAndClear, Adrs.setKeyPairAddress,
      Adrs.setChainAddress, Adrs.Fits]
    apply decide_eq_true; omega

/-- Algorithm 7, `wots_sign`. -/
theorem wotsSign_eq (msg sk pk : Node) (a : SLHDSA.Adrs) (ha : WotsDom a) :
    nds (SLHDSA.wotsSign prims msg sk pk a).toList =
      Spec.wotsSign (nd msg) (nd sk) (nd pk) (adr a) := by
  refine (congrArg (fun v => nds v.toList) (wotsSign_eq_ofFn prims msg sk pk a)).trans ?_
  unfold Spec.wotsSign
  refine nds_ofFn (n := 35) _ _ fun i => ?_
  have hi : i.val < 35 := i.isLt
  have hlt : chainStepsCore prims.core msg i.val < 16 := chainStepsCore_lt prims.core msg i.val
  refine (chain_eq pk (wotsChainAdrs a i.val) _ 0 _
    (fun j _ hj => wotsChain_dom' a ha i.val j hi (by omega))).trans ?_
  have hprf : nd (prims.PRF pk sk (wotsSkAdrs a i.val)) =
      Spec.PRF (nd pk) (nd sk) { Spec.wotsSkAdrs (adr a) with word2 := i.val } :=
    (PRF_eq pk sk (wotsSkAdrs a i.val) (wotsSk_dom a ha i.val hi)).trans (by
      congr 1)
  have hadr2 : adr (wotsChainAdrs a i.val) =
      { ({ adr a with word2 := i.val } : Spec.Adrs) with word3 := 0 } := by
    simp [adr, wotsChainAdrs, Adrs.setTypeAndClear, Adrs.setKeyPairAddress,
      Adrs.setChainAddress, Adrs.getKeyPairAddress, AddrType.toCode, ha.1]
  rw [chainSteps_eq', hadr2, specChain_word3']
  exact congrArg (fun x => Spec.chain x 0 _ (nd pk) _) hprf

/-! ### XMSS signing -/

/-- Algorithm 10, `xmss_sign`. -/
theorem xmssSign_eq (msg sk pk : Node) (a : SLHDSA.Adrs) (ha : BaseDom a) (idx : ℕ)
    (hidx : idx < 2 ^ 9) :
    xmssBytes (SLHDSA.xmssSign prims msg sk pk a idx) =
      Spec.xmssSign (nd msg) (nd sk) idx (nd pk) (adr a) := by
  refine (congrArg xmssBytes (xmssSign_eq_pair prims msg sk pk a idx)).trans ?_
  unfold xmssBytes Spec.xmssSign
  refine congrArg₂ (· ++ ·) ?_ ?_
  · exact wotsSign_eq msg sk pk (wotsLeafAdrs a idx) ⟨rfl, ha.1, ha.2, by
      show idx < 2 ^ 32
      omega⟩
  · refine nds_authPath _ _ idx 9 _ fun j hj => ?_
    have hb : (idx / 2 ^ j) ^^^ 1 < 2 ^ (9 - j) := by
      have e : 9 - j = (8 - j) + 1 := by omega
      rw [e]
      apply xor_one_lt
      rw [← e, Nat.div_lt_iff_lt_mul (by positivity), ← pow_add]
      have : 9 - j + j = 9 := by omega
      rw [this]; exact hidx
    exact (congrArg nd (xmssNode_eq_merkleRoot prims sk pk a j _).symm).trans
      (xmssNode_eq sk pk a ha j _ (by omega) hb)

/-! ### FORS signing -/

private theorem forsSk_dom (a : SLHDSA.Adrs) (ha : ForsDom a) (t : ℕ) (ht : t < 2 ^ 32) :
    Dom (forsSkAdrs a t) := by
  obtain ⟨h3, hl, htr, hw⟩ := ha
  refine ⟨?_, ?_, ?_⟩
  · simp [forsSkAdrs, Adrs.setTypeAndClear, Adrs.setKeyPairAddress,
      Adrs.setTreeIndex, Adrs.getKeyPairAddress,
      Adrs.isCanonical, Adrs.Fits, AddrType.toCode, AddrType.ofCode]
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩ <;> apply decide_eq_true <;> omega
  · show Adrs.Fits 1 a.layer = true
    simpa [Adrs.Fits] using hl
  · show Adrs.Fits 8 a.tree = true
    simpa [Adrs.Fits] using htr

/-- Algorithm 14, `fors_skGen`. -/
theorem forsSkGen_eq (sk pk : Node) (a : SLHDSA.Adrs) (ha : ForsDom a) (t : ℕ)
    (ht : t < 2 ^ 32) :
    nd (forsSkGenCore prims.core sk pk a t) = Spec.forsSkGen (nd sk) (nd pk) (adr a) t :=
  (PRF_eq pk sk (forsSkAdrs a t) (forsSk_dom a ha t ht)).trans (by
    unfold Spec.forsSkGen
    congr 1)

/-- Algorithm 15, `fors_node`, for a node of the `k = 14` FORS trees of height `a = 12`:
VCVio's FORS subtree root at `(height z, global index t)`. -/
theorem forsNode_eq (sk pk : Node) (a : SLHDSA.Adrs) (ha : ForsDom a) (z t : ℕ) (hz : z ≤ 12)
    (ht : t < 14 * 2 ^ (12 - z)) :
    nd (PerfectMerkleTree.merkleRoot (forsLeaf prims sk pk a) (forsNodeHash prims pk a) z t) =
      Spec.forsNode (nd sk) t z (nd pk) (adr a) := by
  induction z generalizing t with
  | zero =>
    have ht' : t < 2 ^ 32 := by simp at ht; omega
    refine (congrArg nd (forsLeaf_eq_f prims sk pk a t)).trans ?_
    refine (F_eq pk _ (forsNode_dom a ha 0 t (by norm_num) ht') _).trans ?_
    rw [adr_forsNode a ha.1]
    exact congrArg (Spec.F (nd pk) _) (forsSkGen_eq sk pk a ha t ht')
  | succ z ih =>
    have hp : 2 ^ (12 - z) = 2 * 2 ^ (12 - (z + 1)) := by
      have : 12 - z = (12 - (z + 1)) + 1 := by omega
      rw [this, pow_succ]; omega
    have hle : 2 ^ (12 - (z + 1)) ≤ 2 ^ 12 := Nat.pow_le_pow_right (by omega) (by omega)
    have ht' : t < 2 ^ 32 := by omega
    have e : PerfectMerkleTree.merkleRoot (forsLeaf prims sk pk a) (forsNodeHash prims pk a)
          (z + 1) t =
        prims.H pk (forsNodeAdrs a (z + 1) t)
          (PerfectMerkleTree.merkleRoot (forsLeaf prims sk pk a) (forsNodeHash prims pk a)
            z (2 * t))
          (PerfectMerkleTree.merkleRoot (forsLeaf prims sk pk a) (forsNodeHash prims pk a)
            z (2 * t + 1)) :=
      (PerfectMerkleTree.merkleRoot_succ _ _ z t).trans (forsNodeHash_eq_h prims pk a (z + 1) t _ _)
    refine (congrArg nd e).trans ?_
    refine (H_eq pk _ (forsNode_dom a ha _ _ (by omega) ht') _ _).trans ?_
    rw [adr_forsNode a ha.1]
    exact congrArg₂ (fun l r => Spec.H (nd pk) _ (l ++ r))
      (ih (2 * t) (by omega) (by omega)) (ih (2 * t + 1) (by omega) (by omega))

/-- Algorithm 16, `fors_sign`, on a 21-byte message digest part. -/
theorem forsSign_eq (md : List UInt8) (hmd : md.length = 21) (sk pk : Node) (a : SLHDSA.Adrs)
    (ha : ForsDom a) :
    forsBytes (SLHDSA.forsSign prims md sk pk a) =
      Spec.forsSign (sp md) (nd sk) (nd pk) (adr a) := by
  refine (congrArg forsBytes (forsSign_eq_ofFn prims md sk pk a)).trans ?_
  unfold forsBytes Spec.forsSign
  refine flatMap_ofFn (n := 14) _ _ _ fun i => ?_
  have hi : i.val < 14 := i.isLt
  have hf : forsIdx vp.params md i.val < 2 ^ 12 := forsIdx_lt vp.params md i.val
  dsimp only
  rw [← forsIdx_eq md hmd]
  refine congrArg₂ (· ++ ·) ?_ ?_
  · exact forsSkGen_eq sk pk a ha (i.val * 2 ^ 12 + forsIdx vp.params md i.val) (by omega)
  · refine nds_authPath _ _ (i.val * 2 ^ 12 + forsIdx vp.params md i.val) 12 _ fun j hj => ?_
    refine (congrArg (fun t => nd (PerfectMerkleTree.merkleRoot (forsLeaf prims sk pk a)
      (forsNodeHash prims pk a) j t)) (fors_sib i.val (forsIdx vp.params md i.val) j hj)).trans ?_
    refine forsNode_eq sk pk a ha j
      (i.val * 2 ^ (12 - j) + ((forsIdx vp.params md i.val / 2 ^ j) ^^^ 1)) (by omega) ?_
    have hb : (forsIdx vp.params md i.val / 2 ^ j) ^^^ 1 < 2 ^ (12 - j) := by
      have e : 12 - j = (11 - j) + 1 := by omega
      rw [e]
      apply xor_one_lt
      rw [← e, Nat.div_lt_iff_lt_mul (by positivity), ← pow_add]
      have : 12 - j + j = 12 := by omega
      rw [this]; exact hf
    have : i.val * 2 ^ (12 - j) ≤ 13 * 2 ^ (12 - j) := Nat.mul_le_mul_right _ (by omega)
    omega

end Link

#print axioms Link.wotsSign_eq
#print axioms Link.xmssSign_eq
#print axioms Link.forsSign_eq
#print axioms Link.forsNode_eq
