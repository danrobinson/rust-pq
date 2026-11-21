import Link.Climb

/-!
# FORS public key from signature (FIPS 205 Algorithm 17): `Spec` = VCVio
-/

namespace Link

open SLHDSA

/-- A `FORS_TREE`-typed base address (key pair set) inside the SHA-2 address domain. -/
def ForsDom (a : SLHDSA.Adrs) : Prop :=
  a.type = 3 ∧ a.layer < 256 ∧ a.tree < 2 ^ 64 ∧ a.word1 < 2 ^ 32

theorem nds_length (l : List Node) : (nds l).length = 16 * l.length := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [nds] at ih ⊢; omega

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

theorem forsBytes_drop (sig : ForsSigCore vp.params prims.core) (i : ℕ) (hi : i < vp.params.k) :
    (forsBytes sig).drop (i * 208) =
      nd sig[i].sk ++ (nds sig[i].auth.toList ++
        (sig.toList.drop (i + 1)).flatMap fun t => nd t.sk ++ nds t.auth.toList) := by
  unfold forsBytes
  rw [fors_flatMap_drop_mul _ 208 (fun t => by
    have h1 : (nd t.sk).length = 16 := nd_length _
    have h2 : (nds t.auth.toList).length = 16 * 12 := (nds_length _).trans (congrArg (16 * ·) (Vector.length_toList))
    rw [List.length_append, h1, h2])]
  have hl : i < sig.toList.length := by rw [Vector.length_toList]; exact hi
  rw [List.drop_eq_getElem_cons hl, List.flatMap_cons, List.append_assoc]
  rfl

theorem fors_block (sig : ForsSigCore vp.params prims.core) (i : ℕ) (hi : i < vp.params.k) :
    Spec.block (forsBytes sig) (i * (Spec.a + 1)) = nd sig[i].sk := by
  have : i * (Spec.a + 1) * Spec.n = i * 208 := by simp [Spec.a, Spec.n]; omega
  rw [Spec.block, this, forsBytes_drop sig i hi]
  exact List.take_left' (nd_length _)

theorem fors_auth (sig : ForsSigCore vp.params prims.core) (i : ℕ) (hi : i < vp.params.k) :
    ((forsBytes sig).drop ((i * (Spec.a + 1) + 1) * Spec.n)).take (Spec.a * Spec.n) =
      nds sig[i].auth.toList := by
  have : (i * (Spec.a + 1) + 1) * Spec.n = i * 208 + 16 := by simp [Spec.a, Spec.n]; omega
  rw [this, ← List.drop_drop, forsBytes_drop sig i hi]
  have h1 : (nd sig[i].sk).length = 16 := nd_length _
  rw [List.drop_left' h1]
  have h2 : (nds sig[i].auth.toList).length = Spec.a * Spec.n :=
    (nds_length _).trans (congrArg (16 * ·) (Vector.length_toList))
  rw [List.take_left' h2]

theorem nds_ofFn {n : ℕ} (f : Fin n → Node) (g : ℕ → Spec.Bytes)
    (h : ∀ i : Fin n, nd (f i) = g i.val) :
    nds (Vector.ofFn f).toList = (List.range n).flatMap g := by
  rw [Vector.toList_ofFn, List.ofFn_eq_map, ← List.map_coe_finRange_eq_range, nds,
    List.flatMap_map, List.flatMap_map]
  congr 1
  funext i
  exact h i

theorem fors_parity (i idx j : ℕ) (hj : j < 12) :
    (idx / 2 ^ j) % 2 = ((i * 2 ^ 12 + idx) / 2 ^ j) % 2 := by
  have : i * 2 ^ 12 + idx = idx + 2 ^ j * (2 * (i * 2 ^ (11 - j))) := by
    have : (2:ℕ) ^ 12 = 2 ^ j * (2 * 2 ^ (11 - j)) := by
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

theorem forsIdx_eq (md : List UInt8) (hmd : md.length = 21) (i : ℕ) :
    forsIdx vp.params md i = (Spec.base2b (sp md) Spec.a Spec.k)[i]! := by
  have : SLHDSA.base2b md 12 14 = Spec.base2b (sp md) 12 14 := base2b_eq md 12 14 (by omega)
  unfold forsIdx
  show (SLHDSA.base2b md 12 14).getD i 0 = (Spec.base2b (sp md) 12 14)[i]!
  rw [this]
  simp [List.getD_eq_getElem?_getD]

/-- Algorithm 17, `fors_pkFromSig`, on a 21-byte message digest part. -/
theorem forsPkFromSig_eq (sig : ForsSigCore vp.params prims.core) (md : List UInt8)
    (hmd : md.length = 21) (pk : Node) (a : SLHDSA.Adrs) (ha : ForsDom a) :
    nd (SLHDSA.forsPkFromSig prims sig md pk a) =
      Spec.forsPkFromSig (forsBytes sig) (sp md) (nd pk) (adr a) := by
  refine (congrArg nd (forsPkFromSig_eq_tl prims sig md pk a)).trans ?_
  refine (Tl_eq pk _ (forsPk_dom a ha) _).trans ?_
  unfold Spec.forsPkFromSig
  have hk : Spec.k = 14 := rfl
  have hfb : ∀ i : ℕ, forsIdx vp.params md i < 2 ^ 12 := fun i => forsIdx_lt vp.params md i
  congr 1
  refine nds_ofFn (n := 14) _ _ fun i => ?_
  have hi : i.val < vp.params.k := i.isLt
  have hi' : i.val < 14 := i.isLt
  have hidx := hfb i.val
  have hlen : (sig[i.val]).auth.toList.length = 12 := Vector.length_toList
  have hF : nd (prims.F pk (forsNodeAdrs a 0 (i.val * 2 ^ 12 + forsIdx vp.params md i.val))
      (sig[i.val]).sk) = Spec.F (nd pk) { adr a with word2 := 0, word3 := (i.val * 2 ^ 12 + (forsIdx vp.params md i.val)) } (nd (sig[i.val]).sk) :=
    (F_eq pk _ (forsNode_dom a ha _ _ (by norm_num) (by omega)) _).trans
      (by rw [adr_forsNode a ha.1])
  have key := climb_eq (forsNodeHash prims pk a) pk (adr a) (forsIdx vp.params md i.val)
    (i.val * 2 ^ 12 + forsIdx vp.params md i.val)
    (prims.F pk (forsNodeAdrs a 0 (i.val * 2 ^ 12 + forsIdx vp.params md i.val)) (sig[i.val]).sk)
    (sig[i.val]).auth.toList
    (fun z hz1 hz2 l r => by
      have hz : z ≤ 12 := hlen ▸ hz2
      have : (i.val * 2 ^ 12 + forsIdx vp.params md i.val) / 2 ^ z ≤ _ := Nat.div_le_self _ _
      exact ((congrArg nd (forsNodeHash_eq_h prims pk a z _ l r)).trans
        (H_eq pk _ (forsNode_dom a ha _ _ (by omega) (by omega)) l r)).trans
          (by rw [adr_forsNode a ha.1]))
    (fun j hj => fors_parity _ _ _ (hlen ▸ hj))
  dsimp only
  rw [fors_block sig i hi, fors_auth sig i hi, ← forsIdx_eq md hmd]
  refine key.trans ?_
  rw [hF]
  exact congrArg (fun h => Spec.climb _ _ _ _ h _ _) hlen

end Link

#print axioms Link.forsPkFromSig_eq
