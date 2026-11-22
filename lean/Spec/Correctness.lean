import Spec.Checked
import Mathlib.Data.Nat.Bitwise

/-!
# Correctness of the scheme, at the level of the specification

Signatures made with a key verify under it (WOTS+, XMSS, FORS, hypertree
and SLH-DSA), and the properties of the checked signer of `Spec/Checked.lean`.
-/

namespace Spec

/-! ## Lengths -/

theorem compress_length (st : List SHA256.Word) (b : Bytes) : (SHA256.compress st b).length = 8 := by
  simp only [SHA256.compress]
  generalize List.foldl (SHA256.round _) _ _ = r
  obtain ⟨_, _, _, _, _, _, _, _⟩ := r
  rfl

theorem sha256_length (m : Bytes) : (sha256 m).length = 32 := by
  have h : ∀ (l : List Nat) (st : List SHA256.Word), st.length = 8 →
      (l.foldl (fun st k => SHA256.compress st (SHA256.blockAt (SHA256.pad m) k)) st).length = 8 := by
    intro l
    induction l with
    | nil => intro st h; simpa using h
    | cons x xs ih => intro st _; exact ih _ (compress_length _ _)
  simp only [sha256, SHA256.sha256, List.length_flatMap]
  have h8 := h (List.range ((SHA256.pad m).length / 64)) SHA256.H0 rfl
  generalize (List.foldl _ SHA256.H0 _) = st at h8 ⊢
  have : ∀ w : SHA256.Word, (toByte w.toNat 4).length = 4 := by intro w; simp [toByte]
  simp [this, List.map_const', h8]

@[simp] theorem thash_length (p : Bytes) (x : Adrs) (m : Bytes) : (thash p x m).length = 16 := by
  simp [thash, sha256_length, n]

@[simp] theorem F_length (p : Bytes) (x : Adrs) (m : Bytes) : (F p x m).length = 16 := thash_length _ _ _
@[simp] theorem H_length (p : Bytes) (x : Adrs) (m : Bytes) : (H p x m).length = 16 := thash_length _ _ _
@[simp] theorem T_length (p : Bytes) (x : Adrs) (m : Bytes) : (T p x m).length = 16 := thash_length _ _ _
@[simp] theorem PRF_length (p s : Bytes) (x : Adrs) : (PRF p s x).length = 16 := thash_length _ _ _

theorem chain_length (x : Bytes) (hx : x.length = 16) (i s : Nat) (p : Bytes) (adrs : Adrs) :
    (chain x i s p adrs).length = 16 := by
  unfold chain
  generalize List.range s = l
  induction l generalizing x with
  | nil => simpa using hx
  | cons y ys ih => exact ih _ (F_length _ _ _)

/-! ## Concatenations of equal-length pieces -/

theorem flatMap_congr' {α β} {l : List α} {f g : α → List β} (h : ∀ x ∈ l, f x = g x) :
    l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons]
    rw [h x (by simp), ih (fun y hy => h y (by simp [hy]))]

theorem length_flatMap_const (f : Nat → Bytes) (L : Nat) (hf : ∀ j, (f j).length = L) (k : Nat) :
    ((List.range k).flatMap f).length = k * L := by
  induction k with
  | zero => simp
  | succ k ih => simp [List.range_succ, ih, hf, Nat.succ_mul]

/-- The `i`-th piece of a concatenation of `k` pieces of length `L`, and the
part of it from `o`. -/
theorem flatMap_piece (f : Nat → Bytes) (L : Nat) (hf : ∀ j, (f j).length = L) (k i o t : Nat)
    (hi : i < k) (hot : o + t ≤ L) :
    (((List.range k).flatMap f).drop (i * L + o)).take t = ((f i).drop o).take t := by
  induction k with
  | zero => omega
  | succ k ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
    · rw [← ih h]
      have hl := length_flatMap_const f L hf k
      have hle : i * L + o + t ≤ k * L := by
        have : (i + 1) * L ≤ k * L := Nat.mul_le_mul_right _ h
        rw [Nat.add_mul] at this; omega
      rw [List.drop_append_of_le_length (by omega)]
      rw [List.take_append_of_le_length (by rw [List.length_drop, hl]; omega)]
    · subst h
      rw [List.drop_append, length_flatMap_const f L hf, show i * L + o - i * L = o by omega,
        List.drop_eq_nil_of_le (by rw [length_flatMap_const f L hf]; omega), List.nil_append]

theorem block_flatMap (f : Nat → Bytes) (hf : ∀ j, (f j).length = n) (k i : Nat) (hi : i < k) :
    block ((List.range k).flatMap f) i = f i := by
  have := flatMap_piece f n hf k i 0 n hi (by omega)
  simp only [Nat.add_zero, List.drop_zero] at this
  rw [block, this, List.take_of_length_le (by rw [hf])]

/-! ## WOTS+ -/

theorem base2bGo_length (x : Bytes) (b : Nat) :
    ∀ out inp bits total, (base2bGo x b out inp bits total).length = out := by
  intro out
  induction out with
  | zero => intros; rfl
  | succ o ih => intros; simp [base2bGo, ih]

theorem base2bGo_lt (x : Bytes) (b : Nat) :
    ∀ out inp bits total, ∀ v ∈ base2bGo x b out inp bits total, v < 2 ^ b := by
  intro out
  induction out with
  | zero => intro _ _ _ v hv; simp [base2bGo] at hv
  | succ o ih =>
    intro inp bits total v hv
    simp only [base2bGo, List.mem_cons] at hv
    rcases hv with hv | hv
    · rw [hv]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
    · exact ih _ _ _ _ hv

theorem base2b_length (x : Bytes) (b o : Nat) : (base2b x b o).length = o := base2bGo_length _ _ _ _ _ _

theorem base2b_lt (x : Bytes) (b o : Nat) : ∀ v ∈ base2b x b o, v < 2 ^ b := base2bGo_lt _ _ _ _ _ _

theorem base2b_getElem!_lt (x : Bytes) (b o i : Nat) (hi : i < o) : (base2b x b o)[i]! < 2 ^ b := by
  have hl : i < (base2b x b o).length := by rw [base2b_length]; exact hi
  simp only [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hl, Option.getD_some]
  exact base2b_lt x b o _ (List.getElem_mem hl)

theorem wotsDigits_lt (msg : Bytes) (i : Nat) (hi : i < len) : (wotsDigits msg)[i]! < w := by
  have key : ∀ c : Bytes, (base2b msg lgw len1 ++ base2b c lgw len2)[i]! < w := by
    intro c
    have h1 := base2b_length msg lgw len1
    by_cases h : i < len1
    · rw [List.getElem!_eq_getElem?_getD, List.getElem?_append_left (by rw [h1]; exact h),
        ← List.getElem!_eq_getElem?_getD]
      exact base2b_getElem!_lt _ _ _ _ h
    · rw [List.getElem!_eq_getElem?_getD, List.getElem?_append_right (by rw [h1]; omega),
        ← List.getElem!_eq_getElem?_getD, h1]
      exact base2b_getElem!_lt _ _ _ _ (by simp [len, len1, len2] at hi h ⊢; omega)
  exact key _


theorem chain_add (x : Bytes) (s t : Nat) (p : Bytes) (adrs : Adrs) :
    chain (chain x 0 s p adrs) s t p adrs = chain x 0 (s + t) p adrs := by
  simp only [chain, List.range_add, List.foldl_append, List.foldl_map, Nat.zero_add]

/-- WOTS+ is correct: the public key recomputed from a signature of `M` is
the public key. -/
theorem wots_correct (M sk p : Bytes) (adrs : Adrs) :
    wotsPkFromSig (wotsSign M sk p adrs) M p adrs = wotsPkGen sk p adrs := by
  unfold wotsPkFromSig wotsPkGen wotsSign
  refine congrArg (T p (wotsPkAdrs adrs)) ?_
  apply flatMap_congr'
  intro i hi
  rw [List.mem_range] at hi
  rw [block_flatMap _ (fun j => chain_length _ (PRF_length _ _ _) _ _ _ _) _ _ hi, chain_add]
  have := wotsDigits_lt M i hi
  congr 1
  simp only [w] at this ⊢
  omega

/-! ## Authentication paths -/

theorem xor_one_eq (t : Nat) : t ^^^ 1 = if t % 2 = 0 then t + 1 else t - 1 := by
  split
  · exact Nat.xor_one_of_even (Nat.even_iff.mpr ‹_›)
  · rw [Nat.xor_one_of_odd (Nat.odd_iff.mpr (by omega))]

/-- Climbing an authentication path made of the siblings of a tree's nodes
reaches the node above: for any tree whose inner nodes hash their children
as `xmssNode` and `forsNode` do. `ti` is the leaf's index in the tree's
numbering, `idx` a number with the same low bits. -/
theorem climb_node (node : Nat → Nat → Bytes) (p : Bytes) (adrs : Adrs)
    (hnode : ∀ i z, node i (z + 1) =
      H p { adrs with word2 := z + 1, word3 := i } (node (2 * i) z ++ node (2 * i + 1) z))
    (idx ti height : Nat) (auth : Bytes)
    (hbit : ∀ j < height, (idx / 2 ^ j) % 2 = (ti / 2 ^ j) % 2)
    (hauth : ∀ j < height, block auth j = node ((ti / 2 ^ j) ^^^ 1) j) :
    climb (node ti 0) idx ti auth height p adrs = node (ti / 2 ^ height) height := by
  unfold climb
  suffices h : ∀ c, c ≤ height → (List.range c).foldl (fun (st : Bytes × Nat) j =>
      let (node, ti) := st
      if (idx / 2 ^ j) % 2 = 0 then
        let ti := ti / 2
        (H p { adrs with word2 := j + 1, word3 := ti } (node ++ block auth j), ti)
      else
        let ti := (ti - 1) / 2
        (H p { adrs with word2 := j + 1, word3 := ti } (block auth j ++ node), ti))
      (node ti 0, ti) = (node (ti / 2 ^ c) c, ti / 2 ^ c) by
    rw [h height (le_refl _)]
  intro c
  induction c with
  | zero => intro _; simp
  | succ c ih =>
    intro hc
    rw [List.range_succ, List.foldl_append, ih (by omega)]
    simp only [List.foldl_cons, List.foldl_nil]
    have hb := hbit c (by omega)
    have ha := hauth c (by omega)
    have hdiv : ti / 2 ^ (c + 1) = ti / 2 ^ c / 2 := by
      rw [Nat.pow_succ, Nat.div_div_eq_div_mul]
    rw [hdiv, hnode]
    generalize ti / 2 ^ c = t at hb ha
    rw [ha, xor_one_eq]
    split
    · rename_i h0
      have : t % 2 = 0 := by omega
      simp only [this, ite_true]
      have e : 2 * (t / 2) = t := by omega
      rw [e]
    · rename_i h0
      have : ¬ t % 2 = 0 := by omega
      simp only [this, ite_false]
      have e1 : 2 * (t / 2) = t - 1 := by omega
      have e3 : (t - 1) / 2 = t / 2 := by omega
      rw [e1, e3, show t - 1 + 1 = t by omega]

/-! ## XMSS -/

theorem wotsPkGen_length (sk p : Bytes) (adrs : Adrs) : (wotsPkGen sk p adrs).length = 16 := by
  simp [wotsPkGen]

theorem wotsSign_length (M sk p : Bytes) (adrs : Adrs) :
    (wotsSign M sk p adrs).length = len * n :=
  length_flatMap_const _ _ (fun _ => chain_length _ (PRF_length _ _ _) _ _ _ _) _

theorem xmssNode_length (sk : Bytes) (i z : Nat) (p : Bytes) (adrs : Adrs) :
    (xmssNode sk i z p adrs).length = 16 := by
  cases z <;> simp [xmssNode, wotsPkGen_length]

theorem xmssNode_succ (sk : Bytes) (i z : Nat) (p : Bytes) (adrs : Adrs) :
    xmssNode sk i (z + 1) p adrs =
      H p { adrs.setTypeAndClear TREE with word2 := z + 1, word3 := i }
        (xmssNode sk (2 * i) z p adrs ++ xmssNode sk (2 * i + 1) z p adrs) := by
  simp [xmssNode]

/-- XMSS is correct: the root recomputed from a signature of `M` at leaf
`idx` is the root of the tree. -/
theorem xmss_correct (M sk p : Bytes) (idx : Nat) (adrs : Adrs) (hidx : idx < 2 ^ hp) :
    xmssPkFromSig idx (xmssSign M sk idx p adrs) M p adrs = xmssNode sk 0 hp p adrs := by
  unfold xmssPkFromSig xmssSign
  simp only []
  have hW := wotsSign_length M sk p { adrs.setTypeAndClear WOTS_HASH with keypair := idx }
  have hA : ((List.range hp).flatMap fun j => xmssNode sk ((idx / 2 ^ j) ^^^ 1) j p adrs).length =
      hp * n := length_flatMap_const _ _ (fun _ => xmssNode_length _ _ _ _ _) _
  rw [List.take_left' hW, List.drop_left' hW, List.take_of_length_le (by rw [hA]), wots_correct]
  have h0 : wotsPkGen sk p { adrs.setTypeAndClear WOTS_HASH with keypair := idx } =
      xmssNode sk idx 0 p adrs := by simp [xmssNode]
  rw [h0, climb_node (fun i z => xmssNode sk i z p adrs) p (adrs.setTypeAndClear TREE)
    (fun i z => xmssNode_succ sk i z p adrs) idx idx hp _ (fun _ _ => rfl)
    (fun j hj => block_flatMap _ (fun _ => xmssNode_length _ _ _ _ _) _ _ hj)]
  rw [Nat.div_eq_of_lt hidx]

/-! ## FORS -/

theorem forsNode_length (sk : Bytes) (i z : Nat) (p : Bytes) (adrs : Adrs) :
    (forsNode sk i z p adrs).length = 16 := by
  cases z <;> simp [forsNode]

theorem forsNode_succ (sk : Bytes) (i z : Nat) (p : Bytes) (adrs : Adrs) :
    forsNode sk i (z + 1) p adrs =
      H p { adrs with word2 := z + 1, word3 := i }
        (forsNode sk (2 * i) z p adrs ++ forsNode sk (2 * i + 1) z p adrs) := by
  simp [forsNode]

theorem div_split (i idx j a : Nat) (hj : j < a) :
    (i * 2 ^ a + idx) / 2 ^ j = i * 2 ^ (a - j) + idx / 2 ^ j ∧ (i * 2 ^ (a - j)) % 2 = 0 := by
  have hp : 2 ^ a = 2 ^ (a - j) * 2 ^ j := by rw [← Nat.pow_add]; congr 1; omega
  refine ⟨?_, ?_⟩
  · rw [hp, ← Nat.mul_assoc, Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _), Nat.add_comm]
  · have : 2 ^ (a - j) = 2 * 2 ^ (a - j - 1) := by
      rw [← Nat.pow_succ']; congr 1; omega
    rw [this]; simp [Nat.mul_mod]

/-- The pieces of a FORS signature: tree `i`'s secret leaf value and
authentication path. -/
def forsPiece (sk p : Bytes) (adrs : Adrs) (indices : List Nat) (i : Nat) : Bytes :=
  forsSkGen sk p adrs (i * 2 ^ a + indices[i]!) ++
    (List.range a).flatMap fun j =>
      forsNode sk (i * 2 ^ (a - j) + ((indices[i]! / 2 ^ j) ^^^ 1)) j p adrs

theorem forsPiece_length (sk p : Bytes) (adrs : Adrs) (indices : List Nat) (i : Nat) :
    (forsPiece sk p adrs indices i).length = (a + 1) * n := by
  simp only [forsPiece, List.length_append, forsSkGen, PRF_length,
    length_flatMap_const _ _ (fun _ => forsNode_length _ _ _ _ _)]
  simp [a, n]

theorem fors_tree_correct (sk p : Bytes) (adrs : Adrs) (indices : List Nat) (i : Nat) (hi : i < k)
    (hidx : indices[i]! < 2 ^ a) :
    climb (F p { adrs with word2 := 0, word3 := i * 2 ^ a + indices[i]! }
        (block ((List.range k).flatMap (forsPiece sk p adrs indices)) (i * (a + 1))))
      indices[i]! (i * 2 ^ a + indices[i]!)
      ((((List.range k).flatMap (forsPiece sk p adrs indices)).drop ((i * (a + 1) + 1) * n)).take (a * n))
      a p adrs = forsNode sk i a p adrs := by
  have hL := forsPiece_length sk p adrs indices
  have h1 : block ((List.range k).flatMap (forsPiece sk p adrs indices)) (i * (a + 1)) =
      forsSkGen sk p adrs (i * 2 ^ a + indices[i]!) := by
    rw [block, show i * (a + 1) * n = i * ((a + 1) * n) + 0 by rw [Nat.mul_assoc]; rfl,
      flatMap_piece _ _ hL _ _ _ _ hi (by simp [a, n]), List.drop_zero, forsPiece,
      List.take_left' (by simp [forsSkGen, n])]
  have hA : ((List.range a).flatMap fun j =>
      forsNode sk (i * 2 ^ (a - j) + ((indices[i]! / 2 ^ j) ^^^ 1)) j p adrs).length = a * n :=
    length_flatMap_const _ _ (fun _ => forsNode_length _ _ _ _ _) _
  have h2 : (((List.range k).flatMap (forsPiece sk p adrs indices)).drop ((i * (a + 1) + 1) * n)).take
      (a * n) = (List.range a).flatMap fun j =>
        forsNode sk (i * 2 ^ (a - j) + ((indices[i]! / 2 ^ j) ^^^ 1)) j p adrs := by
    rw [show (i * (a + 1) + 1) * n = i * ((a + 1) * n) + n by simp [Nat.add_mul, Nat.mul_assoc],
      flatMap_piece _ _ hL _ _ _ _ hi (by simp [a, n]), forsPiece,
      List.drop_left' (by simp [forsSkGen, n]), List.take_of_length_le (by rw [hA])]
  have h0 : F p { adrs with word2 := 0, word3 := i * 2 ^ a + indices[i]! }
      (forsSkGen sk p adrs (i * 2 ^ a + indices[i]!)) = forsNode sk (i * 2 ^ a + indices[i]!) 0 p adrs := by
    simp [forsNode]
  rw [h1, h2, h0, climb_node (fun i z => forsNode sk i z p adrs) p adrs
    (fun i z => forsNode_succ sk i z p adrs)]
  · congr 1
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hidx]
    simp
  · intro j hj
    obtain ⟨e, he⟩ := div_split i indices[i]! j a hj
    rw [e]
    generalize i * 2 ^ (a - j) = E at he ⊢
    generalize indices[i]! / 2 ^ j = q
    omega
  · intro j hj
    obtain ⟨e, he⟩ := div_split i indices[i]! j a hj
    rw [block_flatMap _ (fun _ => forsNode_length _ _ _ _ _) _ _ hj, e]
    congr 1
    generalize i * 2 ^ (a - j) = E at he ⊢
    generalize indices[i]! / 2 ^ j = q
    rw [xor_one_eq, xor_one_eq]
    split <;> split <;> omega

/-- FORS is correct: the public key recomputed from a signature of `md` is
the public key computed from the secret seed. -/
theorem fors_correct (md sk p : Bytes) (adrs : Adrs) :
    forsPkFromSig (forsSign md sk p adrs) md p adrs = forsPkGen sk p adrs := by
  unfold forsPkFromSig forsPkGen forsSign
  refine congrArg (T p _) ?_
  apply flatMap_congr'
  intro i hi
  rw [List.mem_range] at hi
  exact fors_tree_correct sk p adrs (base2b md a k) i hi (base2b_getElem!_lt _ _ _ _ hi)

/-! ## Hypertree -/

/-- One layer of `htSign`: state `(sig, root, tree, leaf)`. -/
def htLayer (skSeed pkSeed : Bytes) (st : Bytes × Bytes × Nat × Nat) (j : Nat) :
    Bytes × Bytes × Nat × Nat :=
  let (sig, root, tree, leaf) := st
  let adrs := { Adrs.zero with layer := j, tree := tree }
  let s := xmssSign root skSeed leaf pkSeed adrs
  (sig ++ s, xmssPkFromSig leaf s root pkSeed adrs, tree >>> hp, tree % 2 ^ hp)

/-- One layer of `htVerify`: state `(node, tree, leaf)`. -/
def htVerifyLayer (sig pkSeed : Bytes) (st : Bytes × Nat × Nat) (j : Nat) : Bytes × Nat × Nat :=
  let (node, tree, leaf) := st
  let adrs := { Adrs.zero with layer := j, tree := tree }
  let s := (sig.drop (j * xmssSigBytes)).take xmssSigBytes
  (xmssPkFromSig leaf s node pkSeed adrs, tree >>> hp, tree % 2 ^ hp)

theorem htSign_eq (m sk p : Bytes) (t l : Nat) :
    htSign m sk p t l = ((List.range d).foldl (htLayer sk p) ([], m, t, l)).1 := rfl

theorem htVerify_eq (m sig p : Bytes) (t l : Nat) (root : Bytes) :
    htVerify m sig p t l root = (((List.range d).foldl (htVerifyLayer sig p) (m, t, l)).1 == root) := rfl

/-- The root that `htSign` reaches: the last root it computes. -/
def htRoot (m sk p : Bytes) (t l : Nat) : Bytes := ((List.range d).foldl (htLayer sk p) ([], m, t, l)).2.1

theorem xmssSign_length (M sk : Bytes) (idx : Nat) (p : Bytes) (adrs : Adrs) :
    (xmssSign M sk idx p adrs).length = xmssSigBytes := by
  simp only [xmssSign, List.length_append, wotsSign_length,
    length_flatMap_const _ _ (fun _ => xmssNode_length _ _ _ _ _)]
  simp [xmssSigBytes, Nat.add_mul, n]

theorem htLayer_grows (sk p : Bytes) :
    ∀ (l : List Nat) (st : Bytes × Bytes × Nat × Nat), ∃ rest, (l.foldl (htLayer sk p) st).1 = st.1 ++ rest := by
  intro l
  induction l with
  | nil => intro st; exact ⟨[], by simp⟩
  | cons j js ih =>
    intro st
    obtain ⟨rest, h⟩ := ih (htLayer sk p st j)
    refine ⟨(xmssSign st.2.1 sk st.2.2.2 p { Adrs.zero with layer := j, tree := st.2.2.1 }) ++ rest, ?_⟩
    rw [List.foldl_cons, h]
    obtain ⟨_, _, _, _⟩ := st
    simp [htLayer]

theorem htLayer_length (sk p m : Bytes) (t l : Nat) :
    ∀ c, ((List.range c).foldl (htLayer sk p) ([], m, t, l)).1.length = c * xmssSigBytes := by
  intro c
  induction c with
  | zero => rfl
  | succ c ih =>
    rw [List.range_succ, List.foldl_append]
    revert ih
    generalize List.foldl (htLayer sk p) ([], m, t, l) (List.range c) = st
    obtain ⟨_, _, _, _⟩ := st
    intro ih
    simp [htLayer, xmssSign_length, ih, Nat.add_mul]

/-- Verification retraces signing: `htVerify` of what `htSign` returns
compares the root `htSign` reached. Holds for every key. -/
theorem htVerify_htSign (m sk p : Bytes) (t l : Nat) (root : Bytes) :
    htVerify m (htSign m sk p t l) p t l root = (htRoot m sk p t l == root) := by
  rw [htVerify_eq, htRoot]
  generalize hfull : htSign m sk p t l = full
  suffices h : ∀ c, c ≤ d → (List.range c).foldl (htVerifyLayer full p) (m, t, l) =
      (((List.range c).foldl (htLayer sk p) ([], m, t, l)).2.1,
        ((List.range c).foldl (htLayer sk p) ([], m, t, l)).2.2.1,
        ((List.range c).foldl (htLayer sk p) ([], m, t, l)).2.2.2) by
    rw [h d (le_refl _)]
  intro c
  induction c with
  | zero => intro _; rfl
  | succ c ih =>
    intro hc
    -- the full signature extends the first `c + 1` layers
    have hpre : ∃ rest, full = ((List.range (c + 1)).foldl (htLayer sk p) ([], m, t, l)).1 ++ rest := by
      rw [← hfull, htSign_eq, show d = (c + 1) + (d - (c + 1)) by omega, List.range_add,
        List.foldl_append]
      obtain ⟨rest, h⟩ := htLayer_grows sk p (List.map (fun x => c + 1 + x) (List.range (d - (c + 1))))
        ((List.range (c + 1)).foldl (htLayer sk p) ([], m, t, l))
      exact ⟨rest, h⟩
    have hlen := htLayer_length sk p m t l c
    rw [List.range_succ, List.foldl_append] at hpre
    rw [List.range_succ, List.foldl_append, List.foldl_append, ih (by omega)]
    obtain ⟨rest, hrest⟩ := hpre
    revert hrest hlen
    generalize List.foldl (htLayer sk p) ([], m, t, l) (List.range c) = st
    obtain ⟨sig, root, tree, leaf⟩ := st
    intro hlen hrest
    simp only [List.foldl_cons, List.foldl_nil, htLayer, htVerifyLayer] at hrest hlen ⊢
    have hs : (full.drop (c * xmssSigBytes)).take xmssSigBytes =
        xmssSign root sk leaf p { Adrs.zero with layer := c, tree := tree } := by
      rw [hrest, ← hlen, List.append_assoc, List.drop_left,
        List.take_left' (xmssSign_length _ _ _ _ _)]
    rw [hs]

/-! The checked hypertree signer, against `htSign`. -/

/-- The checked state agrees with `htSign`'s state while `ok` holds. -/
def HtRel (C : Bytes × Bytes × Bytes × Bool × Nat × Nat) (S : Bytes × Bytes × Nat × Nat) : Prop :=
  C.2.2.2.2.1 = S.2.2.1 ∧ C.2.2.2.2.2 = S.2.2.2 ∧
    (C.2.2.2.1 = true → C.1 = S.1 ∧ C.2.1 = S.2.1 ∧ C.2.2.1 = S.2.1)

theorem htRel_foldl (sk p root : Bytes) :
    ∀ (l : List Nat) C S, HtRel C S →
      HtRel (l.foldl (htCheckedStep sk p root) C) (l.foldl (htLayer sk p) S) := by
  intro l
  induction l with
  | nil => intro C S h; exact h
  | cons j js ih =>
    intro C S h
    apply ih
    obtain ⟨sig, mA, mB, ok, tree, leaf⟩ := C
    obtain ⟨sig', root', tree', leaf'⟩ := S
    obtain ⟨h1, h2, h3⟩ := h
    simp only at h1 h2 h3
    subst h1 h2
    refine ⟨rfl, rfl, ?_⟩
    intro hok
    simp only [htCheckedStep, Bool.and_eq_true, beq_iff_eq] at hok
    obtain ⟨e1, e2, e3⟩ := h3 hok.1
    subst e1 e2 e3
    simp only [htCheckedStep, htLayer]
    simp [hok.2]

theorem htChecked_last (sk p root : Bytes) (C : Bytes × Bytes × Bytes × Bool × Nat × Nat) :
    ((List.range d).foldl (htCheckedStep sk p root) C).2.2.1 = root := by
  rw [show d = 6 + 1 from rfl, List.range_succ, List.foldl_append]
  generalize List.foldl (htCheckedStep sk p root) C (List.range 6) = st
  obtain ⟨_, _, _, _, _, _⟩ := st
  simp [htCheckedStep, d]

/-- When the checked hypertree signer reports agreement, its signature is
`htSign`'s, and the root `htSign` reaches is the given `PK.root`. -/
theorem htSignChecked_sound (mA mB sk p : Bytes) (t l : Nat) (root : Bytes)
    (h : (htSignChecked mA mB sk p t l root).2 = true) :
    (htSignChecked mA mB sk p t l root).1 = htSign mA sk p t l ∧ htRoot mA sk p t l = root := by
  have hrel := htRel_foldl sk p root (List.range d) ([], mA, mB, mA == mB, t, l) ([], mA, t, l)
    (by unfold HtRel; simp; exact fun h => h.symm)
  have hlast := htChecked_last sk p root ([], mA, mB, mA == mB, t, l)
  unfold htSignChecked at h ⊢
  rw [htSign_eq, htRoot]
  revert h hrel hlast
  generalize List.foldl (htCheckedStep sk p root) ([], mA, mB, mA == mB, t, l) (List.range d) = C
  obtain ⟨_, _, _, _, _, _⟩ := C
  intro h hrel hlast
  simp only at h hlast ⊢
  obtain ⟨_, _, h3⟩ := hrel
  obtain ⟨e1, _, e3⟩ := h3 h
  exact ⟨e1, e3.symm.trans hlast⟩

/-- For a well-formed key the checked hypertree signer reports agreement. -/
theorem htSignChecked_complete (m sk p : Bytes) (t l : Nat) (root : Bytes)
    (ht : t < 2 ^ (h - h / d)) (hl : l < 2 ^ hp)
    (hroot : root = xmssNode sk 0 hp p { Adrs.zero with layer := d - 1 }) :
    (htSignChecked m m sk p t l root).2 = true := by
  suffices H : ∀ c, c ≤ d → ((List.range c).foldl (htCheckedStep sk p root) ([], m, m, m == m, t, l)).2.2.2.1 = true ∧
      ((List.range c).foldl (htCheckedStep sk p root) ([], m, m, m == m, t, l)).2.1 =
        ((List.range c).foldl (htCheckedStep sk p root) ([], m, m, m == m, t, l)).2.2.1 ∧
      ((List.range c).foldl (htCheckedStep sk p root) ([], m, m, m == m, t, l)).2.2.2.2.1 = t >>> (hp * c) ∧
      ((List.range c).foldl (htCheckedStep sk p root) ([], m, m, m == m, t, l)).2.2.2.2.2 < 2 ^ hp by
    have := (H d (le_refl _)).1
    unfold htSignChecked
    revert this
    generalize List.foldl (htCheckedStep sk p root) ([], m, m, m == m, t, l) (List.range d) = C
    obtain ⟨_, _, _, _, _, _⟩ := C
    exact id
  intro c
  induction c with
  | zero => intro _; simp [hl]
  | succ c ih =>
    intro hc
    rw [List.range_succ, List.foldl_append]
    have ih := ih (by omega)
    revert ih
    generalize List.foldl (htCheckedStep sk p root) ([], m, m, m == m, t, l) (List.range c) = C
    obtain ⟨sig, mA, mB, ok, tree, leaf⟩ := C
    rintro ⟨h1, h2, h3, h4⟩
    simp only at h1 h2 h3 h4
    subst h1 h2 h3
    simp only [List.foldl_cons, List.foldl_nil, htCheckedStep]
    rw [xmss_correct _ _ _ _ _ h4]
    refine ⟨?_, ?_, ?_, Nat.mod_lt _ (Nat.two_pow_pos _)⟩
    · split
      · simp
      · have hc6 : c = 6 := by simp [d] at hc ‹_›; omega
        subst hc6
        have h0 : t >>> (hp * 6) = 0 := by
          rw [Nat.shiftRight_eq_div_pow]
          exact Nat.div_eq_of_lt (by simpa [h, d, hp] using ht)
        rw [h0, hroot]
        simp [d, Adrs.zero]
    · split
      · rfl
      · have hc6 : c = 6 := by simp [d] at hc ‹_›; omega
        subst hc6
        have h0 : t >>> (hp * 6) = 0 := by
          rw [Nat.shiftRight_eq_div_pow]
          exact Nat.div_eq_of_lt (by simpa [h, d, hp] using ht)
        rw [h0, hroot]
        simp [d, Adrs.zero]
    · rw [Nat.mul_succ, Nat.shiftRight_add]

/-! ## SLH-DSA -/

theorem PRFmsg_length (k r m : Bytes) : (PRFmsg k r m).length = n := by
  simp [PRFmsg, hmacSha256, sha256_length, n]

theorem forsSign_eq (md sk p : Bytes) (adrs : Adrs) :
    forsSign md sk p adrs = (List.range k).flatMap (forsPiece sk p adrs (base2b md a k)) := rfl

theorem forsSign_length (md sk p : Bytes) (adrs : Adrs) : (forsSign md sk p adrs).length = forsSigBytes := by
  rw [forsSign_eq, length_flatMap_const _ _ (forsPiece_length sk p adrs _)]
  rfl

theorem htSign_length (m sk p : Bytes) (t l : Nat) : (htSign m sk p t l).length = d * xmssSigBytes := by
  rw [htSign_eq]; exact htLayer_length sk p m t l d

theorem block_skPk (sk : Bytes) (i : Nat) : block (skPk sk) i = block sk (i + 2) := by
  simp [block, skPk, List.drop_drop, Nat.add_mul, Nat.add_comm]

/-- Verification of a signature assembled as Algorithm 19 assembles it, under
the public key held in the private key: it compares the root that `htSign`
reached with `PK.root`. Holds for every private key. -/
theorem slhVerify_parts (msg sk r : Bytes) (hr : r.length = n) :
    slhVerifyInternal msg
      (r ++ forsSign ((Hmsg r (block sk 2) (block sk 3) msg).take mdBytes) (block sk 0) (block sk 2)
          { { Adrs.zero with tree := digestTree (Hmsg r (block sk 2) (block sk 3) msg) }.setTypeAndClear
              FORS_TREE with keypair := digestLeaf (Hmsg r (block sk 2) (block sk 3) msg) } ++
        htSign (forsPkFromSig
            (forsSign ((Hmsg r (block sk 2) (block sk 3) msg).take mdBytes) (block sk 0) (block sk 2)
              { { Adrs.zero with tree := digestTree (Hmsg r (block sk 2) (block sk 3) msg) }.setTypeAndClear
                  FORS_TREE with keypair := digestLeaf (Hmsg r (block sk 2) (block sk 3) msg) })
            ((Hmsg r (block sk 2) (block sk 3) msg).take mdBytes) (block sk 2)
            { { Adrs.zero with tree := digestTree (Hmsg r (block sk 2) (block sk 3) msg) }.setTypeAndClear
                FORS_TREE with keypair := digestLeaf (Hmsg r (block sk 2) (block sk 3) msg) })
          (block sk 0) (block sk 2) (digestTree (Hmsg r (block sk 2) (block sk 3) msg))
          (digestLeaf (Hmsg r (block sk 2) (block sk 3) msg)))
      (skPk sk) =
    (htRoot (forsPkFromSig
            (forsSign ((Hmsg r (block sk 2) (block sk 3) msg).take mdBytes) (block sk 0) (block sk 2)
              { { Adrs.zero with tree := digestTree (Hmsg r (block sk 2) (block sk 3) msg) }.setTypeAndClear
                  FORS_TREE with keypair := digestLeaf (Hmsg r (block sk 2) (block sk 3) msg) })
            ((Hmsg r (block sk 2) (block sk 3) msg).take mdBytes) (block sk 2)
            { { Adrs.zero with tree := digestTree (Hmsg r (block sk 2) (block sk 3) msg) }.setTypeAndClear
                FORS_TREE with keypair := digestLeaf (Hmsg r (block sk 2) (block sk 3) msg) })
          (block sk 0) (block sk 2) (digestTree (Hmsg r (block sk 2) (block sk 3) msg))
          (digestLeaf (Hmsg r (block sk 2) (block sk 3) msg)) == block sk 3) := by
  generalize hD : Hmsg r (block sk 2) (block sk 3) msg = D
  generalize hF : forsSign (D.take mdBytes) (block sk 0) (block sk 2)
    { { Adrs.zero with tree := digestTree D }.setTypeAndClear FORS_TREE with keypair := digestLeaf D } = sF
  have hFl : sF.length = forsSigBytes := by rw [← hF]; exact forsSign_length _ _ _ _
  generalize hS : htSign _ (block sk 0) (block sk 2) (digestTree D) (digestLeaf D) = sH
  have hSl : sH.length = d * xmssSigBytes := by rw [← hS]; exact htSign_length _ _ _ _ _
  unfold slhVerifyInternal
  have hlen : (r ++ sF ++ sH).length = sigBytes := by
    simp only [List.length_append, hr, hFl, hSl]; rfl
  simp only [hlen, ne_eq, not_true_eq_false, ↓reduceIte, block_skPk]
  have e1 : (r ++ sF ++ sH).take n = r := by
    rw [List.append_assoc, List.take_left' hr]
  have e2 : ((r ++ sF ++ sH).drop n).take forsSigBytes = sF := by
    rw [List.append_assoc, List.drop_left' hr, List.take_left' hFl]
  have e3 : (r ++ sF ++ sH).drop (n + forsSigBytes) = sH := by
    rw [List.append_assoc, ← List.drop_drop, List.drop_left' hr, List.drop_left' hFl]
  simp only [show (0 + 2 : Nat) = 2 from rfl, show (1 + 2 : Nat) = 3 from rfl, e1, e2, e3, hD]
  rw [← hS, htVerify_htSign]

theorem slhSignInternal_eq (msg sk addrnd : Bytes) :
    slhSignInternal msg sk addrnd =
      (PRFmsg (block sk 1) addrnd msg) ++
      forsSign ((Hmsg (PRFmsg (block sk 1) addrnd msg) (block sk 2) (block sk 3) msg).take mdBytes)
        (block sk 0) (block sk 2)
        { { Adrs.zero with tree := digestTree (Hmsg (PRFmsg (block sk 1) addrnd msg) (block sk 2) (block sk 3) msg) }.setTypeAndClear
            FORS_TREE with keypair := digestLeaf (Hmsg (PRFmsg (block sk 1) addrnd msg) (block sk 2) (block sk 3) msg) } ++
      htSign (forsPkFromSig
          (forsSign ((Hmsg (PRFmsg (block sk 1) addrnd msg) (block sk 2) (block sk 3) msg).take mdBytes)
            (block sk 0) (block sk 2)
            { { Adrs.zero with tree := digestTree (Hmsg (PRFmsg (block sk 1) addrnd msg) (block sk 2) (block sk 3) msg) }.setTypeAndClear
                FORS_TREE with keypair := digestLeaf (Hmsg (PRFmsg (block sk 1) addrnd msg) (block sk 2) (block sk 3) msg) })
          ((Hmsg (PRFmsg (block sk 1) addrnd msg) (block sk 2) (block sk 3) msg).take mdBytes) (block sk 2)
          { { Adrs.zero with tree := digestTree (Hmsg (PRFmsg (block sk 1) addrnd msg) (block sk 2) (block sk 3) msg) }.setTypeAndClear
              FORS_TREE with keypair := digestLeaf (Hmsg (PRFmsg (block sk 1) addrnd msg) (block sk 2) (block sk 3) msg) })
        (block sk 0) (block sk 2) (digestTree (Hmsg (PRFmsg (block sk 1) addrnd msg) (block sk 2) (block sk 3) msg))
        (digestLeaf (Hmsg (PRFmsg (block sk 1) addrnd msg) (block sk 2) (block sk 3) msg)) := rfl

/-- Whenever the checked signer returns a signature, it is the signature of
Algorithm 19, and it verifies under the public key held in `sk`. For every
`sk`, well formed or not. -/
theorem slhSignInternalChecked_sound (msg sk addrnd sig : Bytes)
    (h : slhSignInternalChecked msg sk addrnd = some sig) :
    sig = slhSignInternal msg sk addrnd ∧ slhVerifyInternal msg sig (skPk sk) = true := by
  unfold slhSignInternalChecked at h
  simp only [] at h
  generalize hc : htSignChecked _ _ _ _ _ _ _ = c at h
  obtain ⟨sigHt, ok⟩ := c
  cases ok
  · simp at h
  · simp only [ite_true, Option.some.injEq] at h
    have hs := htSignChecked_sound _ _ _ _ _ _ _ (by rw [hc])
    rw [hc] at hs
    obtain ⟨e1, e2⟩ := hs
    subst h
    simp only at e1
    rw [e1]
    refine ⟨rfl, ?_⟩
    rw [slhVerify_parts _ _ _ (PRFmsg_length _ _ _), e2]
    simp

theorem digestTree_lt (D : Bytes) : digestTree D < 2 ^ (h - h / d) := Nat.mod_lt _ (Nat.two_pow_pos _)

theorem digestLeaf_lt (D : Bytes) : digestLeaf D < 2 ^ hp := Nat.mod_lt _ (Nat.two_pow_pos _)

/-- For a well-formed key the checked signer always returns a signature. -/
theorem slhSignInternalChecked_complete (msg sk addrnd : Bytes) (hk : KeyOk sk) :
    ∃ sig, slhSignInternalChecked msg sk addrnd = some sig := by
  unfold slhSignInternalChecked
  simp only []
  rw [fors_correct]
  have hcomp : ∀ m D, htSignChecked m m (block sk 0) (block sk 2) (digestTree D) (digestLeaf D) (block sk 3) =
      ((htSignChecked m m (block sk 0) (block sk 2) (digestTree D) (digestLeaf D) (block sk 3)).1, true) := by
    intro m D
    rw [← htSignChecked_complete m _ _ _ _ _ (digestTree_lt D) (digestLeaf_lt D) hk]
  rw [hcomp]
  exact ⟨_, rfl⟩

/-- Completeness of Algorithms 19 and 20: under a well-formed key, a
signature verifies under the public key held in the key. -/
theorem slh_complete_internal (msg sk addrnd : Bytes) (hk : KeyOk sk) :
    slhVerifyInternal msg (slhSignInternal msg sk addrnd) (skPk sk) = true := by
  obtain ⟨sig, h⟩ := slhSignInternalChecked_complete msg sk addrnd hk
  obtain ⟨e, v⟩ := slhSignInternalChecked_sound msg sk addrnd sig h
  rw [← e]; exact v

/-- The checked signer with a context string, as `slhSignInternalChecked_sound`. -/
theorem slhSignChecked_sound (msg ctx sk addrnd sig : Bytes)
    (h : slhSignChecked msg ctx sk addrnd = some sig) :
    slhSign msg ctx sk addrnd = some sig ∧ slhVerify msg sig ctx (skPk sk) = true := by
  unfold slhSignChecked at h
  split at h
  · simp at h
  · rename_i hc
    obtain ⟨e, v⟩ := slhSignInternalChecked_sound _ _ _ _ h
    refine ⟨?_, ?_⟩
    · simp [slhSign, hc, e]
    · simp [slhVerify, hc, v]

theorem slhSignChecked_complete (msg ctx sk addrnd : Bytes) (hc : ctx.length ≤ 255) (hk : KeyOk sk) :
    ∃ sig, slhSignChecked msg ctx sk addrnd = some sig := by
  unfold slhSignChecked
  simp only [show ¬ ctx.length > 255 by omega, ↓reduceIte]
  exact slhSignInternalChecked_complete _ _ _ hk

/-- Completeness of Algorithms 22 and 24. -/
theorem slh_complete (msg ctx sk addrnd : Bytes) (hc : ctx.length ≤ 255) (hk : KeyOk sk) :
    ∃ sig, slhSign msg ctx sk addrnd = some sig ∧ slhVerify msg sig ctx (skPk sk) = true := by
  obtain ⟨sig, h⟩ := slhSignChecked_complete msg ctx sk addrnd hc hk
  exact ⟨sig, slhSignChecked_sound _ _ _ _ _ h⟩

/-- Key generation (Algorithm 18) produces well-formed keys, and the public
key is the one the private key holds. -/
theorem keygen_keyOk (skSeed skPrf pkSeed : Bytes)
    (h1 : skSeed.length = n) (h2 : skPrf.length = n) (h3 : pkSeed.length = n) :
    KeyOk (slhKeygenInternal skSeed skPrf pkSeed).1 ∧
      (slhKeygenInternal skSeed skPrf pkSeed).2 = skPk (slhKeygenInternal skSeed skPrf pkSeed).1 := by
  have hr := xmssNode_length skSeed 0 hp pkSeed { Adrs.zero with layer := d - 1 }
  have b0 : ∀ x rest : Bytes, x.length = n → block (x ++ rest) 0 = x := by
    intro x rest hx; simp [block, List.take_left' hx]
  have bs : ∀ x rest : Bytes, x.length = n → ∀ i, block (x ++ rest) (i + 1) = block rest i := by
    intro x rest hx i
    simp only [block, Nat.add_mul, Nat.one_mul, Nat.add_comm _ n, ← List.drop_drop, List.drop_left' hx]
  simp only [slhKeygenInternal, List.append_assoc]
  refine ⟨?_, ?_⟩
  · simp only [KeyOk]
    rw [b0 _ _ h1, bs _ _ h1 1, bs _ _ h2 0, b0 _ _ h3, bs _ _ h1 2, bs _ _ h2 1, bs _ _ h3 0]
    simp [block, List.take_of_length_le, hr, n]
  · simp only [skPk, show 2 * n = n + n from by omega, ← List.drop_drop, List.drop_left' h1,
      List.drop_left' h2]

end Spec
