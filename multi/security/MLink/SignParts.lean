import MLink.Keygen
import Mathlib.Data.Nat.Bitwise

/-!
# Signing components (FIPS 205 Algorithms 7, 10, 14–16): `Spec` = VCVio, all six SHA-2 sets
-/

namespace MLink

open SLHDSA SLHDSA.Concrete

variable (S : Sha2Set)

/-! ### Generic helpers -/

theorem sibling_eq_xor_one (i : ℕ) : PerfectMerkleTree.sibling i = i ^^^ 1 := by
  unfold PerfectMerkleTree.sibling
  by_cases h : i % 2 = 0
  · rw [ite_eq_left h]
    exact (Nat.xor_one_of_even (by simpa [Nat.even_iff] using h)).symm
  · rw [ite_eq_right h]
    exact (Nat.xor_one_of_odd (by simpa [Nat.odd_iff] using h)).symm

/-- The flat reading of an intrinsic authentication path, entry by entry (FIPS `xor 1` form). -/
theorem nds_authPath {n : ℕ} (leaf : ℕ → Bytes n) (nodeHash : ℕ → ℕ → Bytes n → Bytes n → Bytes n)
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

theorem flatMap_ofFn {α : Type} {n : ℕ} (f : Fin n → α) (F : α → Spec.Bytes)
    (g : ℕ → Spec.Bytes) (h : ∀ i : Fin n, F (f i) = g i.val) :
    (Vector.ofFn f).toList.flatMap F = (List.range n).flatMap g := by
  rw [Vector.toList_ofFn, List.ofFn_eq_map, ← List.map_coe_finRange_eq_range,
    List.flatMap_map, List.flatMap_map]
  congr 1
  funext i
  exact h i

theorem xor_one_lt (x m : ℕ) (h : x < 2 ^ (m + 1)) : x ^^^ 1 < 2 ^ (m + 1) := by
  rw [← sibling_eq_xor_one]
  unfold PerfectMerkleTree.sibling
  rw [pow_succ] at h ⊢
  split <;> omega

/-- The sibling at height `j` of an index below `2^a` stays below `2^(a − j)`. -/
theorem sib_lt (a idx j : ℕ) (hj : j < a) (hidx : idx < 2 ^ a) :
    (idx / 2 ^ j) ^^^ 1 < 2 ^ (a - j) := by
  have e : a - j = (a - 1 - j) + 1 := by omega
  rw [e]
  apply xor_one_lt
  rw [← e, Nat.div_lt_iff_lt_mul (by positivity), ← pow_add]
  have : a - j + j = a := by omega
  rw [this]; exact hidx

/-- The sibling of the global FORS node `(i·2^a + f) / 2^j` in the spec's per-tree form. -/
theorem fors_sib (a i f j : ℕ) (hj : j < a) :
    ((i * 2 ^ a + f) / 2 ^ j) ^^^ 1 = i * 2 ^ (a - j) + ((f / 2 ^ j) ^^^ 1) := by
  have h1 : i * 2 ^ a + f = f + 2 ^ j * (2 * (i * 2 ^ (a - 1 - j))) := by
    have : (2:ℕ) ^ a = 2 ^ j * (2 * 2 ^ (a - 1 - j)) := by
      rw [← pow_succ', ← pow_add]; congr 1; omega
    rw [this]; ring
  have h2 : i * 2 ^ (a - j) = 2 * (i * 2 ^ (a - 1 - j)) := by
    have : a - j = (a - 1 - j) + 1 := by omega
    rw [this, pow_succ]; ring
  rw [h1, Nat.add_mul_div_left _ _ (by positivity), h2,
    ← sibling_eq_xor_one, ← sibling_eq_xor_one]
  generalize i * 2 ^ (a - 1 - j) = e
  generalize f / 2 ^ j = x
  unfold PerfectMerkleTree.sibling
  split <;> split <;> omega

/-! ### WOTS+ signing -/

/-- Algorithm 7, `wots_sign`. -/
theorem wotsSign_eq (msg sk pk : S.Node) (a : SLHDSA.Adrs) (ha : WotsDom a) :
    nds (SLHDSA.wotsSign S.prims msg sk pk a).toList =
      Spec.wotsSign S.spec (nd msg) (nd sk) (nd pk) (adr a) := by
  refine (congrArg (fun v => nds v.toList) (wotsSign_eq_ofFn S.prims msg sk pk a)).trans ?_
  unfold Spec.wotsSign
  rw [← S.len_eq]
  refine nds_ofFn _ _ fun i => ?_
  have hi : i.val < S.vp.params.len := i.isLt
  have hi32 : i.val < 2 ^ 32 := lt_trans hi S.len_lt
  have hlt : chainStepsCore S.prims.core msg i.val < 16 := chainSteps_lt S msg i.val
  refine (chain_eq S pk (wotsChainAdrs a i.val) _ 0 _
    (fun j _ hj => wotsChain_dom a ha i.val j hi32 (by omega))).trans ?_
  have hprf := PRF_eq S pk sk (wotsSkAdrs a i.val) (wotsSk_dom a ha i.val hi32)
  rw [adr_wotsSk] at hprf
  rw [chainSteps_eq, adr_wotsChain a ha.1, specChain_word3, hprf]

/-! ### XMSS signing -/

/-- Algorithm 10, `xmss_sign`. -/
theorem xmssSign_eq (msg sk pk : S.Node) (a : SLHDSA.Adrs) (ha : BaseDom a) (idx : ℕ)
    (hidx : idx < 2 ^ S.vp.params.hp) :
    xmssBytes S (SLHDSA.xmssSign S.prims msg sk pk a idx) =
      Spec.xmssSign S.spec (nd msg) (nd sk) idx (nd pk) (adr a) := by
  refine (congrArg (xmssBytes S) (xmssSign_eq_pair S.prims msg sk pk a idx)).trans ?_
  unfold xmssBytes Spec.xmssSign
  have hidx32 : idx < 2 ^ 32 :=
    lt_of_lt_of_le hidx (Nat.pow_le_pow_right (by norm_num) (le_trans S.hp_le (by norm_num)))
  refine congrArg₂ (· ++ ·) ?_ ?_
  · exact wotsSign_eq S msg sk pk (wotsLeafAdrs a idx) ⟨rfl, ha.1, ha.2, hidx32⟩
  · rw [← S.hp_eq]
    refine nds_authPath _ _ idx S.vp.params.hp _ fun j hj => ?_
    exact (congrArg nd (xmssNode_eq_merkleRoot S.prims sk pk a j _).symm).trans
      (xmssNode_eq S sk pk a ha j _ (by omega) (sib_lt _ idx j hj hidx))

/-! ### FORS signing -/

theorem forsSk_dom (a : SLHDSA.Adrs) (ha : ForsDom a) (t : ℕ) (ht : t < 2 ^ 32) :
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
theorem forsSkGen_eq (sk pk : S.Node) (a : SLHDSA.Adrs) (ha : ForsDom a) (t : ℕ)
    (ht : t < 2 ^ 32) :
    nd (forsSkGenCore S.prims.core sk pk a t) =
      Spec.forsSkGen S.spec (nd sk) (nd pk) (adr a) t :=
  (PRF_eq S pk sk (forsSkAdrs a t) (forsSk_dom a ha t ht)).trans (by
    unfold Spec.forsSkGen
    congr 1)

/-- Algorithm 15, `fors_node`, for a node of the `k` FORS trees of height `a`:
VCVio's FORS subtree root at `(height z, global index t)`. -/
theorem forsNode_eq (sk pk : S.Node) (a : SLHDSA.Adrs) (ha : ForsDom a) (z t : ℕ)
    (hz : z ≤ S.vp.params.a) (ht : t < S.vp.params.k * 2 ^ (S.vp.params.a - z)) :
    nd (PerfectMerkleTree.merkleRoot (forsLeaf S.prims sk pk a) (forsNodeHash S.prims pk a) z t) =
      Spec.forsNode S.spec (nd sk) t z (nd pk) (adr a) := by
  have hb : ∀ (z t : ℕ), t < S.vp.params.k * 2 ^ (S.vp.params.a - z) → t < 2 ^ 32 := by
    intro z t ht
    have h1 : S.vp.params.k * 2 ^ (S.vp.params.a - z) ≤ S.vp.params.k * 2 ^ S.vp.params.a :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (Nat.sub_le _ _))
    have h2 := S.fors_leaves_le
    omega
  induction z generalizing t with
  | zero =>
    have ht' : t < 2 ^ 32 := hb 0 t ht
    refine (congrArg nd (forsLeaf_eq_f S.prims sk pk a t)).trans ?_
    refine (F_eq S pk _ (forsNode_dom a ha 0 t (by norm_num) ht') _).trans ?_
    rw [adr_forsNode a ha.1]
    exact congrArg (Spec.F S.spec (nd pk) _) (forsSkGen_eq S sk pk a ha t ht')
  | succ z ih =>
    have hp : S.vp.params.k * 2 ^ (S.vp.params.a - z) =
        2 * (S.vp.params.k * 2 ^ (S.vp.params.a - (z + 1))) := by
      have : S.vp.params.a - z = (S.vp.params.a - (z + 1)) + 1 := by omega
      rw [this, pow_succ]; ring
    have ht' : t < 2 ^ 32 := hb _ t ht
    have hz32 : z + 1 < 2 ^ 32 := by have := S.a_le; omega
    have e : PerfectMerkleTree.merkleRoot (forsLeaf S.prims sk pk a) (forsNodeHash S.prims pk a)
          (z + 1) t =
        S.prims.H pk (forsNodeAdrs a (z + 1) t)
          (PerfectMerkleTree.merkleRoot (forsLeaf S.prims sk pk a) (forsNodeHash S.prims pk a)
            z (2 * t))
          (PerfectMerkleTree.merkleRoot (forsLeaf S.prims sk pk a) (forsNodeHash S.prims pk a)
            z (2 * t + 1)) :=
      (PerfectMerkleTree.merkleRoot_succ _ _ z t).trans
        (forsNodeHash_eq_h S.prims pk a (z + 1) t _ _)
    refine (congrArg nd e).trans ?_
    refine (H_eq S pk _ (forsNode_dom a ha _ _ hz32 ht') _ _).trans ?_
    rw [adr_forsNode a ha.1]
    exact congrArg₂ (fun l r => Spec.H S.spec (nd pk) _ (l ++ r))
      (ih (2 * t) (by omega) (by rw [hp]; omega))
      (ih (2 * t + 1) (by omega) (by rw [hp]; omega))

/-- Algorithm 16, `fors_sign`, on a `⌈k·a/8⌉`-byte message digest part. -/
theorem forsSign_eq (md : List UInt8) (hmd : md.length = S.vp.params.digestBytes)
    (sk pk : S.Node) (a : SLHDSA.Adrs) (ha : ForsDom a) :
    forsBytes S (SLHDSA.forsSign S.prims md sk pk a) =
      Spec.forsSign S.spec (sp md) (nd sk) (nd pk) (adr a) := by
  refine (congrArg (forsBytes S) (forsSign_eq_ofFn S.prims md sk pk a)).trans ?_
  unfold forsBytes
  refine Eq.trans (flatMap_ofFn _ _ (fun i =>
      Spec.forsSkGen S.spec (nd sk) (nd pk) (adr a)
          (i * 2 ^ S.spec.a + (Spec.base2b (sp md) S.spec.a S.spec.k)[i]!) ++
        (List.range S.spec.a).flatMap fun j =>
          Spec.forsNode S.spec (nd sk)
            (i * 2 ^ (S.spec.a - j) + (((Spec.base2b (sp md) S.spec.a S.spec.k)[i]! / 2 ^ j) ^^^ 1))
            j (nd pk) (adr a)) fun i => ?_) (by rw [S.k_eq]; rfl)
  have hi : i.val < S.vp.params.k := i.isLt
  have hf : forsIdx S.vp.params md i.val < 2 ^ S.vp.params.a := forsIdx_lt S.vp.params md i.val
  have hleaf := forsLeaf_lt S md i.val hi
  dsimp only
  rw [← forsIdx_eq S md hmd, ← S.a_eq]
  refine congrArg₂ (· ++ ·) ?_ ?_
  · exact forsSkGen_eq S sk pk a ha _ hleaf
  · refine nds_authPath _ _ (i.val * 2 ^ S.vp.params.a + forsIdx S.vp.params md i.val)
      S.vp.params.a _ fun j hj => ?_
    refine (congrArg (fun t => nd (PerfectMerkleTree.merkleRoot (forsLeaf S.prims sk pk a)
      (forsNodeHash S.prims pk a) j t))
      (fors_sib S.vp.params.a i.val (forsIdx S.vp.params md i.val) j hj)).trans ?_
    refine forsNode_eq S sk pk a ha j
      (i.val * 2 ^ (S.vp.params.a - j) + ((forsIdx S.vp.params md i.val / 2 ^ j) ^^^ 1))
      (by omega) ?_
    have hb := sib_lt S.vp.params.a (forsIdx S.vp.params md i.val) j hj hf
    have h1 : (i.val + 1) * 2 ^ (S.vp.params.a - j) ≤ S.vp.params.k * 2 ^ (S.vp.params.a - j) :=
      Nat.mul_le_mul_right _ hi
    rw [Nat.succ_mul] at h1
    omega

end MLink

#print axioms MLink.wotsSign_eq
#print axioms MLink.xmssSign_eq
#print axioms MLink.forsSign_eq
#print axioms MLink.forsNode_eq
