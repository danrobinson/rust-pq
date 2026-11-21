import MLink.Climb

/-!
# FORS public key from signature (FIPS 205 Algorithm 17): `Spec` = VCVio, all six SHA-2 sets
-/

namespace MLink

open SLHDSA

/-- A `FORS_TREE`-typed base address (key pair set) inside the SHA-2 address domain. -/
def ForsDom (a : SLHDSA.Adrs) : Prop :=
  a.type = 3 ∧ a.layer < 256 ∧ a.tree < 2 ^ 64 ∧ a.word1 < 2 ^ 32

variable (S : Sha2Set)

/-! ### Numeric facts used below (all six sets, by evaluation) -/

/-- `a ∈ {12, 6, 14, 8, 14, 9}`. -/
theorem Sha2Set.a_le (S : Sha2Set) : S.vp.params.a ≤ 14 := by cases S <;> decide
/-- `k ∈ {14, 33, 17, 33, 22, 35}`: never `1`, so `T_k` is never VCVio's singleton (`F`) case. -/
theorem Sha2Set.k_ne_one (S : Sha2Set) : S.vp.params.k ≠ 1 := by cases S <;> decide
/-- Every FORS leaf index `i·2^a + idx` (`i < k`, `idx < 2^a`) fits one 32-bit address word. -/
theorem Sha2Set.fors_leaves_le (S : Sha2Set) : S.vp.params.k * 2 ^ S.vp.params.a ≤ 2 ^ 32 := by
  cases S <;> decide
/-- The `k` base-`2^a` FORS indices fit in the `⌈k·a/8⌉` digest bytes (with spare bits when `k·a`
is not a multiple of 8: 128f, 192s, 256s, 256f). -/
theorem Sha2Set.ka_le (S : Sha2Set) : S.vp.params.k * S.vp.params.a ≤ 8 * S.vp.params.digestBytes := by
  cases S <;> decide

theorem fors_flatMap_drop_mul {α β : Type} (g : α → List β) (c : ℕ) (hg : ∀ t, (g t).length = c)
    (l : List α) (i : ℕ) : (l.flatMap g).drop (i * c) = (l.drop i).flatMap g := by
  induction i generalizing l with
  | zero => simp
  | succ i ih =>
    cases l with
    | nil => simp
    | cons x xs =>
      rw [List.flatMap_cons, List.drop_succ_cons, ← ih xs, Nat.succ_mul, Nat.add_comm,
        ← List.drop_drop, List.drop_left' (hg x)]

theorem forsTree_length (t : ForsTreeSigCore S.vp.params S.prims.core) :
    (nd t.sk ++ nds t.auth.toList).length = (S.vp.params.a + 1) * S.vp.params.n := by
  have h1 : (nd t.sk).length = S.vp.params.n := nd_length _
  have h2 : (nds t.auth.toList).length = S.vp.params.n * S.vp.params.a :=
    (nds_length _).trans (congrArg (S.vp.params.n * ·) (Vector.length_toList))
  rw [List.length_append, h1, h2]; ring

theorem forsBytes_drop (sig : ForsSigCore S.vp.params S.prims.core) (i : ℕ)
    (hi : i < S.vp.params.k) :
    (forsBytes S sig).drop (i * ((S.vp.params.a + 1) * S.vp.params.n)) =
      nd sig[i].sk ++ (nds sig[i].auth.toList ++
        (sig.toList.drop (i + 1)).flatMap fun t => nd t.sk ++ nds t.auth.toList) := by
  unfold forsBytes
  rw [fors_flatMap_drop_mul _ _ (forsTree_length S)]
  have hl : i < sig.toList.length := by rw [Vector.length_toList]; exact hi
  rw [List.drop_eq_getElem_cons hl, List.flatMap_cons, List.append_assoc]
  rfl

theorem fors_block (sig : ForsSigCore S.vp.params S.prims.core) (i : ℕ) (hi : i < S.vp.params.k) :
    Spec.block S.spec (forsBytes S sig) (i * (S.spec.a + 1)) = nd sig[i].sk := by
  have : i * (S.spec.a + 1) * S.spec.n = i * ((S.vp.params.a + 1) * S.vp.params.n) := by
    rw [S.a_eq, S.n_eq]; ring
  rw [Spec.block, this, forsBytes_drop S sig i hi, ← S.n_eq]
  exact List.take_left' (nd_length _)

theorem fors_auth (sig : ForsSigCore S.vp.params S.prims.core) (i : ℕ) (hi : i < S.vp.params.k) :
    ((forsBytes S sig).drop ((i * (S.spec.a + 1) + 1) * S.spec.n)).take (S.spec.a * S.spec.n) =
      nds sig[i].auth.toList := by
  have : (i * (S.spec.a + 1) + 1) * S.spec.n =
      i * ((S.vp.params.a + 1) * S.vp.params.n) + S.vp.params.n := by
    rw [S.a_eq, S.n_eq]; ring
  rw [this, ← List.drop_drop, forsBytes_drop S sig i hi]
  have h1 : (nd sig[i].sk).length = S.vp.params.n := nd_length _
  rw [List.drop_left' h1]
  have h2 : (nds sig[i].auth.toList).length = S.spec.a * S.spec.n :=
    ((nds_length _).trans (congrArg (S.vp.params.n * ·) Vector.length_toList)).trans
      (by rw [S.a_eq, S.n_eq, Nat.mul_comm])
  rw [List.take_left' h2]

theorem fors_parity (a i idx j : ℕ) (hj : j < a) :
    (idx / 2 ^ j) % 2 = ((i * 2 ^ a + idx) / 2 ^ j) % 2 := by
  have : i * 2 ^ a + idx = idx + 2 ^ j * (2 * (i * 2 ^ (a - 1 - j))) := by
    have : (2:ℕ) ^ a = 2 ^ j * (2 * 2 ^ (a - 1 - j)) := by
      rw [← pow_succ', ← pow_add]; congr 1; omega
    rw [this]; ring
  rw [this, Nat.add_mul_div_left _ _ (by positivity)]
  omega

theorem forsNode_dom (a : SLHDSA.Adrs) (ha : ForsDom a) (z t : ℕ) (hz : z < 2 ^ 32)
    (ht : t < 2 ^ 32) : Dom (forsNodeAdrs a z t) := by
  obtain ⟨h3, hl, htr, hw⟩ := ha
  refine ⟨?_, ?_, ?_⟩
  · simp [forsNodeAdrs, Adrs.setTypeAndClear, Adrs.setKeyPairAddress,
      Adrs.setTreeHeight, Adrs.setTreeIndex, Adrs.getKeyPairAddress,
      Adrs.isCanonical, Adrs.Fits, AddrType.toCode, AddrType.ofCode]
    refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩ <;> apply decide_eq_true <;> omega
  · show Adrs.Fits 1 a.layer = true
    simpa [Adrs.Fits] using hl
  · show Adrs.Fits 8 a.tree = true
    simpa [Adrs.Fits] using htr

theorem forsPk_dom (a : SLHDSA.Adrs) (ha : ForsDom a) : Dom (forsPkAdrs a) := by
  obtain ⟨h3, hl, htr, hw⟩ := ha
  refine ⟨?_, ?_, ?_⟩
  · simp [forsPkAdrs, Adrs.setTypeAndClear, Adrs.setKeyPairAddress, Adrs.getKeyPairAddress,
      Adrs.isCanonical, Adrs.Fits, AddrType.toCode, AddrType.ofCode]
    refine ⟨⟨?_, ?_⟩, ?_⟩ <;> apply decide_eq_true <;> omega
  · show Adrs.Fits 1 a.layer = true
    simpa [Adrs.Fits] using hl
  · show Adrs.Fits 8 a.tree = true
    simpa [Adrs.Fits] using htr

theorem adr_forsNode (a : SLHDSA.Adrs) (h3 : a.type = 3) (z t : ℕ) :
    adr (forsNodeAdrs a z t) = { adr a with word2 := z, word3 := t } := by
  simp [adr, forsNodeAdrs, Adrs.setTypeAndClear, Adrs.setKeyPairAddress,
      Adrs.setTreeHeight, Adrs.setTreeIndex, Adrs.getKeyPairAddress, AddrType.toCode, h3]

/-- The `i`-th FORS index, on a `⌈k·a/8⌉`-byte message digest part. -/
theorem forsIdx_eq (md : List UInt8) (hmd : md.length = S.vp.params.digestBytes) (i : ℕ) :
    forsIdx S.vp.params md i = (Spec.base2b (sp md) S.spec.a S.spec.k)[i]! := by
  have : SLHDSA.base2b md S.vp.params.a S.vp.params.k =
      Spec.base2b (sp md) S.vp.params.a S.vp.params.k :=
    base2b_eq md _ _ (by rw [hmd]; exact S.ka_le)
  unfold forsIdx
  rw [this, S.a_eq, S.k_eq]
  simp [List.getD_eq_getElem?_getD]

/-- A FORS leaf index fits one 32-bit address word. -/
theorem forsLeaf_lt (md : List UInt8) (i : ℕ) (hi : i < S.vp.params.k) :
    i * 2 ^ S.vp.params.a + forsIdx S.vp.params md i < 2 ^ 32 := by
  have h1 := forsIdx_lt S.vp.params md i
  have h2 : (i + 1) * 2 ^ S.vp.params.a ≤ S.vp.params.k * 2 ^ S.vp.params.a :=
    Nat.mul_le_mul_right _ hi
  have h3 := S.fors_leaves_le
  rw [Nat.succ_mul] at h2
  omega

/-- Algorithm 17, `fors_pkFromSig`, on a `⌈k·a/8⌉`-byte message digest part. -/
theorem forsPkFromSig_eq (sig : ForsSigCore S.vp.params S.prims.core) (md : List UInt8)
    (hmd : md.length = S.vp.params.digestBytes) (pk : S.Node) (a : SLHDSA.Adrs)
    (ha : ForsDom a) :
    nd (SLHDSA.forsPkFromSig S.prims sig md pk a) =
      Spec.forsPkFromSig S.spec (forsBytes S sig) (sp md) (nd pk) (adr a) := by
  refine (congrArg nd (forsPkFromSig_eq_tl S.prims sig md pk a)).trans ?_
  refine (Tl_eq S pk _ (forsPk_dom a ha) _
    (fun h => S.k_ne_one (Vector.length_toList.symm.trans h))).trans ?_
  have key : nds (Vector.ofFn (fun i : Fin S.vp.params.k =>
        let idx := i.val * 2 ^ S.vp.params.a + forsIdx S.vp.params md i.val
        PerfectMerkleTree.climb (forsNodeHash S.prims pk a) idx
          (S.prims.F pk (forsNodeAdrs a 0 idx) (sig[i.val]).sk)
          (sig[i.val]).auth.toList)).toList =
      (List.range S.vp.params.k).flatMap fun i =>
        Spec.climb S.spec
          (Spec.F S.spec (nd pk)
            { adr a with word2 := 0,
                         word3 := i * 2 ^ S.spec.a +
                           (Spec.base2b (sp md) S.spec.a S.spec.k)[i]! }
            (Spec.block S.spec (forsBytes S sig) (i * (S.spec.a + 1))))
          (Spec.base2b (sp md) S.spec.a S.spec.k)[i]!
          (i * 2 ^ S.spec.a + (Spec.base2b (sp md) S.spec.a S.spec.k)[i]!)
          (((forsBytes S sig).drop ((i * (S.spec.a + 1) + 1) * S.spec.n)).take
            (S.spec.a * S.spec.n))
          S.spec.a (nd pk) (adr a) := by
    refine nds_ofFn _ _ fun i => ?_
    have hi : i.val < S.vp.params.k := i.isLt
    have hidx := forsIdx_lt S.vp.params md i.val
    have hleaf := forsLeaf_lt S md i.val hi
    have hlen : (sig[i.val]).auth.toList.length = S.vp.params.a := Vector.length_toList
    have hale := S.a_le
    have hF : nd (S.prims.F pk
          (forsNodeAdrs a 0 (i.val * 2 ^ S.vp.params.a + forsIdx S.vp.params md i.val))
          (sig[i.val]).sk) =
        Spec.F S.spec (nd pk)
          { adr a with word2 := 0,
                       word3 := (i.val * 2 ^ S.vp.params.a + (forsIdx S.vp.params md i.val)) }
          (nd (sig[i.val]).sk) :=
      (F_eq S pk _ (forsNode_dom a ha _ _ (by norm_num) hleaf) _).trans
        (by rw [adr_forsNode a ha.1])
    have key := climb_eq S (forsNodeHash S.prims pk a) pk (adr a) (forsIdx S.vp.params md i.val)
      (i.val * 2 ^ S.vp.params.a + forsIdx S.vp.params md i.val)
      (S.prims.F pk (forsNodeAdrs a 0 (i.val * 2 ^ S.vp.params.a + forsIdx S.vp.params md i.val))
        (sig[i.val]).sk)
      (sig[i.val]).auth.toList
      (fun z hz1 hz2 l r => by
        have hz : z ≤ S.vp.params.a := hlen ▸ hz2
        have : (i.val * 2 ^ S.vp.params.a + forsIdx S.vp.params md i.val) / 2 ^ z ≤ _ :=
          Nat.div_le_self _ _
        exact ((congrArg nd (forsNodeHash_eq_h S.prims pk a z _ l r)).trans
          (H_eq S pk _ (forsNode_dom a ha _ _ (by omega) (by omega)) l r)).trans
            (by rw [adr_forsNode a ha.1]))
      (fun j hj => fors_parity _ _ _ _ (hlen ▸ hj))
    dsimp only
    rw [fors_block S sig i hi, fors_auth S sig i hi, ← forsIdx_eq S md hmd, ← S.a_eq]
    refine key.trans ?_
    rw [hF]
    exact congrArg (fun h => Spec.climb S.spec _ _ _ _ h _ _) hlen
  refine (congrArg (Spec.T S.spec (nd pk) (adr (forsPkAdrs a))) key).trans ?_
  unfold Spec.forsPkFromSig
  rw [S.k_eq]
  rfl

end MLink

#print axioms MLink.forsPkFromSig_eq
