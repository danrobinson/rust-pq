import Link.Hash

/-!
# Merkle authentication-path climb: `Spec.climb` = VCVio's `PerfectMerkleTree.climb`
-/

namespace Link

open SLHDSA BinaryTree AddressedMerkleTree

/-- The engine's putative root on a perfect tree, for a path given leaf-level first and extended
by one sibling at the top. -/
private theorem putative_snoc {Y : Type} (hash : ℕ → ℕ → Y → Y → Y) (idx : ℕ) (node : Y) :
    ∀ (z t : ℕ) (auth : List Y) (s : Y) (l : SkeletonLeafIndex (Skeleton.perfect (z + 1)))
      (_ : l = SkeletonLeafIndex.ofNat (z + 1) idx) (_ : t = idx / 2 ^ (z + 1))
      (proof : List.Vector Y l.depth) (_ : proof.toList = (auth ++ [s]).reverse)
      (l' : SkeletonLeafIndex (Skeleton.perfect z)) (_ : l' = SkeletonLeafIndex.ofNat z idx)
      (proof' : List.Vector Y l'.depth) (_ : proof'.toList = auth.reverse),
      getPutativeRootAddressedWithHash (PerfectMerkleTree.nodeHashAt hash (z + 1) t) l node proof =
        if idx / 2 ^ z % 2 = 0 then
          hash (z + 1) t
            (getPutativeRootAddressedWithHash
              (PerfectMerkleTree.nodeHashAt hash z (idx / 2 ^ z)) l' node proof') s
        else
          hash (z + 1) t s
            (getPutativeRootAddressedWithHash
              (PerfectMerkleTree.nodeHashAt hash z (idx / 2 ^ z)) l' node proof') := by
  intro z t auth s l hl ht proof hproof l' hl' proof' hproof'
  have hdiv : idx / 2 ^ (z + 1) = idx / 2 ^ z / 2 := by
    rw [Nat.pow_succ, Nat.div_div_eq_div_mul]
  unfold SkeletonLeafIndex.ofNat at hl
  by_cases hbit : idx / 2 ^ z % 2 = 0
  · rw [ite_eq_left hbit] at hl ⊢
    subst hl hl'
    have h2 : 2 * t = idx / 2 ^ z := by omega
    have hhead : proof.head = s := by
      obtain ⟨pl, hp⟩ := proof
      cases pl with
      | nil => simp [List.Vector.toList] at hproof
      | cons a pl =>
        have h : a = s ∧ pl = auth.reverse := by simpa [List.Vector.toList] using hproof
        simpa [List.Vector.head] using h.1
    have htail : proof.tail.toList = auth.reverse := by
      obtain ⟨pl, hp⟩ := proof
      cases pl with
      | nil => simp [List.Vector.toList] at hproof
      | cons a pl =>
        have h : a = s ∧ pl = auth.reverse := by simpa [List.Vector.toList] using hproof
        simpa [List.Vector.tail, List.Vector.toList] using h.2
    simp only [getPutativeRootAddressedWithHash]
    rw [hhead]
    have hp : proof.tail = proof' := by
      apply Subtype.ext
      exact htail.trans hproof'.symm
    rw [hp]
    show hash (z + 1) t (getPutativeRootAddressedWithHash
      (PerfectMerkleTree.nodeHashAt hash z (2 * t)) _ node proof') s = _
    rw [h2]
  · rw [ite_eq_right hbit] at hl ⊢
    subst hl hl'
    have h2 : 2 * t + 1 = idx / 2 ^ z := by omega
    have hhead : proof.head = s := by
      obtain ⟨pl, hp⟩ := proof
      cases pl with
      | nil => simp [List.Vector.toList] at hproof
      | cons a pl =>
        have h : a = s ∧ pl = auth.reverse := by simpa [List.Vector.toList] using hproof
        simpa [List.Vector.head] using h.1
    have htail : proof.tail.toList = auth.reverse := by
      obtain ⟨pl, hp⟩ := proof
      cases pl with
      | nil => simp [List.Vector.toList] at hproof
      | cons a pl =>
        have h : a = s ∧ pl = auth.reverse := by simpa [List.Vector.toList] using hproof
        simpa [List.Vector.tail, List.Vector.toList] using h.2
    simp only [getPutativeRootAddressedWithHash]
    rw [hhead]
    have hp : proof.tail = proof' := by
      apply Subtype.ext
      exact htail.trans hproof'.symm
    rw [hp]
    show hash (z + 1) t s (getPutativeRootAddressedWithHash
      (PerfectMerkleTree.nodeHashAt hash z (2 * t + 1)) _ node proof') = _
    rw [h2]

private theorem climb_nil {Y : Type} (hash : ℕ → ℕ → Y → Y → Y) (idx : ℕ) (node : Y) :
    PerfectMerkleTree.climb hash idx node [] = node := rfl

/-- One step of VCVio's climb: extending the path by a sibling at the top. -/
private theorem climb_snoc {Y : Type} (hash : ℕ → ℕ → Y → Y → Y) (idx : ℕ) (node : Y)
    (auth : List Y) (s : Y) :
    PerfectMerkleTree.climb hash idx node (auth ++ [s]) =
      if idx / 2 ^ auth.length % 2 = 0 then
        hash (auth.length + 1) (idx / 2 ^ (auth.length + 1))
          (PerfectMerkleTree.climb hash idx node auth) s
      else
        hash (auth.length + 1) (idx / 2 ^ (auth.length + 1)) s
          (PerfectMerkleTree.climb hash idx node auth) := by
  rw [PerfectMerkleTree.climb_eq hash idx node (auth ++ [s]) (z := auth.length + 1) (by simp)]
  exact putative_snoc hash idx node auth.length _ auth s _ rfl rfl _ rfl _ rfl _ rfl

/-- The `j`-th block of a concatenation of nodes. -/
private theorem block_nds (ys : List Node) (j : ℕ) (hj : j < ys.length) :
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

/-- Climbing an authentication path. `hash z t` is VCVio's node hash at height `z`, index `t`;
it must agree with the spec's `H` at the addresses the climb visits. `idx` (the spec's bit
selector) and `tidx` (the address index) must have the same low `auth.length` bits. -/
theorem climb_eq (hash : ℕ → ℕ → Node → Node → Node) (pk : Node) (a : Spec.Adrs)
    (idx tidx : ℕ) (node : Node) (auth : List Node)
    (hH : ∀ z, 1 ≤ z → z ≤ auth.length → ∀ l r : Node,
      nd (hash z (tidx / 2 ^ z) l r) =
        Spec.H (nd pk) { a with word2 := z, word3 := tidx / 2 ^ z } (nd l ++ nd r))
    (hpar : ∀ j < auth.length, (idx / 2 ^ j) % 2 = (tidx / 2 ^ j) % 2) :
    nd (PerfectMerkleTree.climb hash tidx node auth) =
      Spec.climb (nd node) idx tidx (nds auth) auth.length (nd pk) a := by
  unfold Spec.climb
  suffices h : ∀ k, k ≤ auth.length →
      (List.range k).foldl (fun (st : Spec.Bytes × Nat) j =>
        let (node, ti) := st
        if (idx / 2 ^ j) % 2 = 0 then
          let ti := ti / 2
          (Spec.H (nd pk) { a with word2 := j + 1, word3 := ti } (node ++ Spec.block (nds auth) j),
            ti)
        else
          let ti := (ti - 1) / 2
          (Spec.H (nd pk) { a with word2 := j + 1, word3 := ti } (Spec.block (nds auth) j ++ node),
            ti)) (nd node, tidx) =
        (nd (PerfectMerkleTree.climb hash tidx node (auth.take k)), tidx / 2 ^ k) by
    have := h auth.length le_rfl
    rw [List.take_length] at this
    rw [this]
  intro k
  induction k with
  | zero => intro _; simp [climb_nil]
  | succ k ih =>
    intro hk
    have hk' : k < auth.length := hk
    rw [List.range_succ, List.foldl_append, ih (by omega)]
    have htake : auth.take (k + 1) = auth.take k ++ [auth[k]] := by
      rw [List.take_succ_eq_append_getElem hk']
    have hlen : (auth.take k).length = k := by simp; omega
    have hdiv : tidx / 2 ^ (k + 1) = tidx / 2 ^ k / 2 := by
      rw [Nat.pow_succ, Nat.div_div_eq_div_mul]
    rw [htake, climb_snoc, hlen, List.foldl_cons, List.foldl_nil, block_nds _ _ hk']
    have hp := hpar k hk'
    have hHk := hH (k + 1) (by omega) hk
    by_cases hbit : idx / 2 ^ k % 2 = 0
    · have hbit' : tidx / 2 ^ k % 2 = 0 := by omega
      simp only [hbit, hbit', ite_true]
      rw [hHk, hdiv]
    · have hbit' : ¬ tidx / 2 ^ k % 2 = 0 := by omega
      simp only [hbit, hbit', ite_false]
      rw [hHk, hdiv]
      have : (tidx / 2 ^ k - 1) / 2 = tidx / 2 ^ k / 2 := by
        generalize tidx / 2 ^ k = x at hbit'
        omega
      rw [this]

end Link

#print axioms Link.climb_eq
