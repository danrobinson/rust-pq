import Spec.Keys
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.Ring

/-!
# Correctness of the scheme, at the level of the specification

For every valid parameter set (`Params.Valid`, which holds for the six sets of
Table 2): signatures made with a key verify under it (WOTS+, XMSS, FORS,
hypertree and SLH-DSA), and key generation produces well-formed keys
(`Spec/Keys.lean`).
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

theorem compress512_length (st : List SHA512.Word) (b : Bytes) : (SHA512.compress st b).length = 8 := by
  simp only [SHA512.compress]
  generalize List.foldl (SHA512.round _) _ _ = r
  obtain ⟨_, _, _, _, _, _, _, _⟩ := r
  rfl

theorem sha512_length (m : Bytes) : (sha512 m).length = 64 := by
  have h : ∀ (l : List Nat) (st : List SHA512.Word), st.length = 8 →
      (l.foldl (fun st k => SHA512.compress st (SHA512.blockAt (SHA512.pad m) k)) st).length = 8 := by
    intro l
    induction l with
    | nil => intro st h; simpa using h
    | cons x xs ih => intro st _; exact ih _ (compress512_length _ _)
  simp only [sha512, SHA512.sha512, List.length_flatMap]
  have h8 := h (List.range ((SHA512.pad m).length / 128)) SHA512.H0 rfl
  generalize (List.foldl _ SHA512.H0 _) = st at h8 ⊢
  have : ∀ w : SHA512.Word, (toByte w.toNat 8).length = 8 := by intro w; simp [toByte]
  simp [this, List.map_const', h8]

theorem Params.Valid.n_le {p : Params} (hv : p.Valid) : p.n ≤ 32 := by
  have := hv.n_cases; omega

theorem F_length (p : Params) (hv : p.Valid) (pk : Bytes) (x : Adrs) (m : Bytes) :
    (F p pk x m).length = p.n := by
  cases hf : p.family <;> simp [F, hf, sha256_length, hv.n_le]
theorem PRF_length (p : Params) (hv : p.Valid) (pk s : Bytes) (x : Adrs) :
    (PRF p pk s x).length = p.n := by
  cases hf : p.family <;> simp [PRF, hf, sha256_length, hv.n_le]
theorem H_length (p : Params) (hv : p.Valid) (pk : Bytes) (x : Adrs) (m : Bytes) :
    (H p pk x m).length = p.n := by
  have := hv.n_le
  cases hf : p.family <;> simp only [H, hf, shake256_length]
  split <;> simp [sha256_length, sha512_length] <;> omega
theorem T_length (p : Params) (hv : p.Valid) (pk : Bytes) (x : Adrs) (m : Bytes) :
    (T p pk x m).length = p.n := H_length p hv pk x m

theorem chain_length (p : Params) (hv : p.Valid) (x : Bytes) (hx : x.length = p.n) (i s : Nat)
    (pk : Bytes) (adrs : Adrs) : (chain p x i s pk adrs).length = p.n := by
  unfold chain
  generalize List.range s = l
  induction l generalizing x with
  | nil => simpa using hx
  | cons y ys ih => exact ih _ (F_length _ hv _ _ _)

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

theorem block_flatMap (p : Params) (f : Nat → Bytes) (hf : ∀ j, (f j).length = p.n) (k i : Nat)
    (hi : i < k) : block p ((List.range k).flatMap f) i = f i := by
  have := flatMap_piece f p.n hf k i 0 p.n hi (by omega)
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

theorem wotsDigits_lt (p : Params) (msg : Bytes) (i : Nat) (hi : i < p.len) :
    (wotsDigits p msg)[i]! < p.w := by
  have key : ∀ c : Bytes, (base2b msg p.lgw p.len1 ++ base2b c p.lgw p.len2)[i]! < p.w := by
    intro c
    have h1 := base2b_length msg p.lgw p.len1
    by_cases h : i < p.len1
    · rw [List.getElem!_eq_getElem?_getD, List.getElem?_append_left (by rw [h1]; exact h),
        ← List.getElem!_eq_getElem?_getD]
      exact base2b_getElem!_lt _ _ _ _ h
    · rw [List.getElem!_eq_getElem?_getD, List.getElem?_append_right (by rw [h1]; omega),
        ← List.getElem!_eq_getElem?_getD, h1]
      exact base2b_getElem!_lt _ _ _ _ (by simp [Params.len] at hi h ⊢; omega)
  exact key _

theorem chain_add (p : Params) (x : Bytes) (s t : Nat) (pk : Bytes) (adrs : Adrs) :
    chain p (chain p x 0 s pk adrs) s t pk adrs = chain p x 0 (s + t) pk adrs := by
  simp only [chain, List.range_add, List.foldl_append, List.foldl_map, Nat.zero_add]

/-- WOTS+ is correct: the public key recomputed from a signature of `M` is
the public key. -/
theorem wots_correct (p : Params) (hv : p.Valid) (M sk pk : Bytes) (adrs : Adrs) :
    wotsPkFromSig p (wotsSign p M sk pk adrs) M pk adrs = wotsPkGen p sk pk adrs := by
  unfold wotsPkFromSig wotsPkGen wotsSign
  refine congrArg (T p pk (wotsPkAdrs adrs)) ?_
  apply flatMap_congr'
  intro i hi
  rw [List.mem_range] at hi
  rw [block_flatMap p _ (fun j => chain_length p hv _ (PRF_length p hv _ _ _) _ _ _ _) _ _ hi, chain_add]
  have := wotsDigits_lt p M i hi
  congr 1
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
theorem climb_node (P : Params) (node : Nat → Nat → Bytes) (p : Bytes) (adrs : Adrs)
    (hnode : ∀ i z, node i (z + 1) =
      H P p { adrs with word2 := z + 1, word3 := i } (node (2 * i) z ++ node (2 * i + 1) z))
    (idx ti height : Nat) (auth : Bytes)
    (hbit : ∀ j < height, (idx / 2 ^ j) % 2 = (ti / 2 ^ j) % 2)
    (hauth : ∀ j < height, block P auth j = node ((ti / 2 ^ j) ^^^ 1) j) :
    climb P (node ti 0) idx ti auth height p adrs = node (ti / 2 ^ height) height := by
  unfold climb
  suffices h : ∀ c, c ≤ height → (List.range c).foldl (fun (st : Bytes × Nat) j =>
      let (node, ti) := st
      if (idx / 2 ^ j) % 2 = 0 then
        let ti := ti / 2
        (H P p { adrs with word2 := j + 1, word3 := ti } (node ++ block P auth j), ti)
      else
        let ti := (ti - 1) / 2
        (H P p { adrs with word2 := j + 1, word3 := ti } (block P auth j ++ node), ti))
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

theorem wotsPkGen_length (p : Params) (hv : p.Valid) (sk pk : Bytes) (adrs : Adrs) :
    (wotsPkGen p sk pk adrs).length = p.n := by
  simp [wotsPkGen, T_length p hv]

theorem wotsSign_length (p : Params) (hv : p.Valid) (M sk pk : Bytes) (adrs : Adrs) :
    (wotsSign p M sk pk adrs).length = p.len * p.n :=
  length_flatMap_const _ _ (fun _ => chain_length p hv _ (PRF_length p hv _ _ _) _ _ _ _) _

theorem xmssNode_length (p : Params) (hv : p.Valid) (sk : Bytes) (i z : Nat) (pk : Bytes) (adrs : Adrs) :
    (xmssNode p sk i z pk adrs).length = p.n := by
  cases z <;> simp [xmssNode, wotsPkGen_length p hv, H_length p hv]

theorem xmssNode_succ (p : Params) (sk : Bytes) (i z : Nat) (pk : Bytes) (adrs : Adrs) :
    xmssNode p sk i (z + 1) pk adrs =
      H p pk { adrs.setTypeAndClear TREE with word2 := z + 1, word3 := i }
        (xmssNode p sk (2 * i) z pk adrs ++ xmssNode p sk (2 * i + 1) z pk adrs) := by
  simp [xmssNode]

/-- XMSS is correct: the root recomputed from a signature of `M` at leaf
`idx` is the root of the tree. -/
theorem xmss_correct (p : Params) (hv : p.Valid) (M sk pk : Bytes) (idx : Nat) (adrs : Adrs)
    (hidx : idx < 2 ^ p.hp) :
    xmssPkFromSig p idx (xmssSign p M sk idx pk adrs) M pk adrs = xmssNode p sk 0 p.hp pk adrs := by
  unfold xmssPkFromSig xmssSign
  simp only []
  have hW := wotsSign_length p hv M sk pk { adrs.setTypeAndClear WOTS_HASH with keypair := idx }
  have hA : ((List.range p.hp).flatMap fun j => xmssNode p sk ((idx / 2 ^ j) ^^^ 1) j pk adrs).length =
      p.hp * p.n := length_flatMap_const _ _ (fun _ => xmssNode_length p hv _ _ _ _ _) _
  rw [List.take_left' hW, List.drop_left' hW, List.take_of_length_le (by rw [hA]), wots_correct p hv]
  have h0 : wotsPkGen p sk pk { adrs.setTypeAndClear WOTS_HASH with keypair := idx } =
      xmssNode p sk idx 0 pk adrs := by simp [xmssNode]
  rw [h0, climb_node p (fun i z => xmssNode p sk i z pk adrs) pk (adrs.setTypeAndClear TREE)
    (fun i z => xmssNode_succ p sk i z pk adrs) idx idx p.hp _ (fun _ _ => rfl)
    (fun j hj => block_flatMap p _ (fun _ => xmssNode_length p hv _ _ _ _ _) _ _ hj)]
  rw [Nat.div_eq_of_lt hidx]

/-! ## FORS -/

theorem forsNode_length (p : Params) (hv : p.Valid) (sk : Bytes) (i z : Nat) (pk : Bytes) (adrs : Adrs) :
    (forsNode p sk i z pk adrs).length = p.n := by
  cases z <;> simp [forsNode, F_length p hv, H_length p hv]

theorem forsNode_succ (p : Params) (sk : Bytes) (i z : Nat) (pk : Bytes) (adrs : Adrs) :
    forsNode p sk i (z + 1) pk adrs =
      H p pk { adrs with word2 := z + 1, word3 := i }
        (forsNode p sk (2 * i) z pk adrs ++ forsNode p sk (2 * i + 1) z pk adrs) := by
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
def forsPiece (p : Params) (sk pk : Bytes) (adrs : Adrs) (indices : List Nat) (i : Nat) : Bytes :=
  forsSkGen p sk pk adrs (i * 2 ^ p.a + indices[i]!) ++
    (List.range p.a).flatMap fun j =>
      forsNode p sk (i * 2 ^ (p.a - j) + ((indices[i]! / 2 ^ j) ^^^ 1)) j pk adrs

theorem forsPiece_length (p : Params) (hv : p.Valid) (sk pk : Bytes) (adrs : Adrs) (indices : List Nat)
    (i : Nat) : (forsPiece p sk pk adrs indices i).length = (p.a + 1) * p.n := by
  simp only [forsPiece, List.length_append, forsSkGen, PRF_length p hv,
    length_flatMap_const _ _ (fun _ => forsNode_length p hv _ _ _ _ _)]
  rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]

theorem fors_tree_correct (p : Params) (hv : p.Valid) (sk pk : Bytes) (adrs : Adrs) (indices : List Nat)
    (i : Nat) (hi : i < p.k) (hidx : indices[i]! < 2 ^ p.a) :
    climb p (F p pk { adrs with word2 := 0, word3 := i * 2 ^ p.a + indices[i]! }
        (block p ((List.range p.k).flatMap (forsPiece p sk pk adrs indices)) (i * (p.a + 1))))
      indices[i]! (i * 2 ^ p.a + indices[i]!)
      ((((List.range p.k).flatMap (forsPiece p sk pk adrs indices)).drop ((i * (p.a + 1) + 1) * p.n)).take
        (p.a * p.n))
      p.a pk adrs = forsNode p sk i p.a pk adrs := by
  have hL := forsPiece_length p hv sk pk adrs indices
  have hn := hv.n_le
  have h1 : block p ((List.range p.k).flatMap (forsPiece p sk pk adrs indices)) (i * (p.a + 1)) =
      forsSkGen p sk pk adrs (i * 2 ^ p.a + indices[i]!) := by
    rw [block, show i * (p.a + 1) * p.n = i * ((p.a + 1) * p.n) + 0 by rw [Nat.mul_assoc]; rfl,
      flatMap_piece _ _ hL _ _ _ _ hi (by rw [Nat.add_mul]; omega), List.drop_zero, forsPiece,
      List.take_left' (by simp [forsSkGen, PRF_length p hv])]
  have hA : ((List.range p.a).flatMap fun j =>
      forsNode p sk (i * 2 ^ (p.a - j) + ((indices[i]! / 2 ^ j) ^^^ 1)) j pk adrs).length = p.a * p.n :=
    length_flatMap_const _ _ (fun _ => forsNode_length p hv _ _ _ _ _) _
  have h2 : (((List.range p.k).flatMap (forsPiece p sk pk adrs indices)).drop ((i * (p.a + 1) + 1) * p.n)).take
      (p.a * p.n) = (List.range p.a).flatMap fun j =>
        forsNode p sk (i * 2 ^ (p.a - j) + ((indices[i]! / 2 ^ j) ^^^ 1)) j pk adrs := by
    rw [show (i * (p.a + 1) + 1) * p.n = i * ((p.a + 1) * p.n) + p.n by simp [Nat.add_mul, Nat.mul_assoc],
      flatMap_piece _ _ hL _ _ _ _ hi (by rw [Nat.add_mul]; omega), forsPiece,
      List.drop_left' (by simp [forsSkGen, PRF_length p hv]), List.take_of_length_le (by rw [hA])]
  have h0 : F p pk { adrs with word2 := 0, word3 := i * 2 ^ p.a + indices[i]! }
      (forsSkGen p sk pk adrs (i * 2 ^ p.a + indices[i]!)) =
        forsNode p sk (i * 2 ^ p.a + indices[i]!) 0 pk adrs := by
    simp [forsNode]
  rw [h1, h2, h0, climb_node p (fun i z => forsNode p sk i z pk adrs) pk adrs
    (fun i z => forsNode_succ p sk i z pk adrs)]
  · congr 1
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hidx]
    simp
  · intro j hj
    obtain ⟨e, he⟩ := div_split i indices[i]! j p.a hj
    rw [e]
    generalize i * 2 ^ (p.a - j) = E at he ⊢
    generalize indices[i]! / 2 ^ j = q
    omega
  · intro j hj
    obtain ⟨e, he⟩ := div_split i indices[i]! j p.a hj
    rw [block_flatMap p _ (fun _ => forsNode_length p hv _ _ _ _ _) _ _ hj, e]
    congr 1
    generalize i * 2 ^ (p.a - j) = E at he ⊢
    generalize indices[i]! / 2 ^ j = q
    rw [xor_one_eq, xor_one_eq]
    split <;> split <;> omega

/-- FORS is correct: the public key recomputed from a signature of `md` is
the public key computed from the secret seed (the roots of the `k` trees,
compressed as in Algorithm 17, line 21). -/
theorem fors_correct (p : Params) (hv : p.Valid) (md sk pk : Bytes) (adrs : Adrs) :
    forsPkFromSig p (forsSign p md sk pk adrs) md pk adrs =
      T p pk { adrs.setTypeAndClear FORS_ROOTS with keypair := adrs.keypair }
        ((List.range p.k).flatMap fun i => forsNode p sk i p.a pk adrs) := by
  unfold forsPkFromSig forsSign
  refine congrArg (T p pk _) ?_
  apply flatMap_congr'
  intro i hi
  rw [List.mem_range] at hi
  exact fors_tree_correct p hv sk pk adrs (base2b md p.a p.k) i hi (base2b_getElem!_lt _ _ _ _ hi)

/-! ## Hypertree -/

/-- One layer of `htSign`: state `(sig, root, tree, leaf)`. -/
def htLayer (p : Params) (skSeed pkSeed : Bytes) (st : Bytes × Bytes × Nat × Nat) (j : Nat) :
    Bytes × Bytes × Nat × Nat :=
  let (sig, root, tree, leaf) := st
  let adrs := { Adrs.zero with layer := j, tree := tree }
  let s := xmssSign p root skSeed leaf pkSeed adrs
  (sig ++ s, xmssPkFromSig p leaf s root pkSeed adrs, tree >>> p.hp, tree % 2 ^ p.hp)

/-- One layer of `htVerify`: state `(node, tree, leaf)`. -/
def htVerifyLayer (p : Params) (sig pkSeed : Bytes) (st : Bytes × Nat × Nat) (j : Nat) :
    Bytes × Nat × Nat :=
  let (node, tree, leaf) := st
  let adrs := { Adrs.zero with layer := j, tree := tree }
  let s := (sig.drop (j * p.xmssSigBytes)).take p.xmssSigBytes
  (xmssPkFromSig p leaf s node pkSeed adrs, tree >>> p.hp, tree % 2 ^ p.hp)

theorem htSign_eq (p : Params) (m sk pk : Bytes) (t l : Nat) :
    htSign p m sk pk t l = ((List.range p.d).foldl (htLayer p sk pk) ([], m, t, l)).1 := rfl

theorem htVerify_eq (p : Params) (m sig pk : Bytes) (t l : Nat) (root : Bytes) :
    htVerify p m sig pk t l root =
      (((List.range p.d).foldl (htVerifyLayer p sig pk) (m, t, l)).1 == root) := rfl

/-- The root that `htSign` reaches: the last root it computes. -/
def htRoot (p : Params) (m sk pk : Bytes) (t l : Nat) : Bytes :=
  ((List.range p.d).foldl (htLayer p sk pk) ([], m, t, l)).2.1

theorem xmssSign_length (p : Params) (hv : p.Valid) (M sk : Bytes) (idx : Nat) (pk : Bytes) (adrs : Adrs) :
    (xmssSign p M sk idx pk adrs).length = p.xmssSigBytes := by
  simp only [xmssSign, List.length_append, wotsSign_length p hv,
    length_flatMap_const _ _ (fun _ => xmssNode_length p hv _ _ _ _ _)]
  simp [Params.xmssSigBytes, Nat.add_mul]

theorem htLayer_grows (p : Params) (sk pk : Bytes) :
    ∀ (l : List Nat) (st : Bytes × Bytes × Nat × Nat), ∃ rest,
      (l.foldl (htLayer p sk pk) st).1 = st.1 ++ rest := by
  intro l
  induction l with
  | nil => intro st; exact ⟨[], by simp⟩
  | cons j js ih =>
    intro st
    obtain ⟨rest, h⟩ := ih (htLayer p sk pk st j)
    refine ⟨(xmssSign p st.2.1 sk st.2.2.2 pk { Adrs.zero with layer := j, tree := st.2.2.1 }) ++ rest, ?_⟩
    rw [List.foldl_cons, h]
    obtain ⟨_, _, _, _⟩ := st
    simp [htLayer]

theorem htLayer_length (p : Params) (hv : p.Valid) (sk pk m : Bytes) (t l : Nat) :
    ∀ c, ((List.range c).foldl (htLayer p sk pk) ([], m, t, l)).1.length = c * p.xmssSigBytes := by
  intro c
  induction c with
  | zero => simp
  | succ c ih =>
    rw [List.range_succ, List.foldl_append]
    revert ih
    generalize List.foldl (htLayer p sk pk) ([], m, t, l) (List.range c) = st
    obtain ⟨_, _, _, _⟩ := st
    intro ih
    simp [htLayer, xmssSign_length p hv, ih, Nat.add_mul]

/-- Verification retraces signing: `htVerify` of what `htSign` returns
compares the root `htSign` reached. Holds for every key. -/
theorem htVerify_htSign (p : Params) (hv : p.Valid) (m sk pk : Bytes) (t l : Nat) (root : Bytes) :
    htVerify p m (htSign p m sk pk t l) pk t l root = (htRoot p m sk pk t l == root) := by
  rw [htVerify_eq, htRoot]
  generalize hfull : htSign p m sk pk t l = full
  suffices h : ∀ c, c ≤ p.d → (List.range c).foldl (htVerifyLayer p full pk) (m, t, l) =
      (((List.range c).foldl (htLayer p sk pk) ([], m, t, l)).2.1,
        ((List.range c).foldl (htLayer p sk pk) ([], m, t, l)).2.2.1,
        ((List.range c).foldl (htLayer p sk pk) ([], m, t, l)).2.2.2) by
    rw [h p.d (le_refl _)]
  intro c
  induction c with
  | zero => intro _; rfl
  | succ c ih =>
    intro hc
    have hpre : ∃ rest, full = ((List.range (c + 1)).foldl (htLayer p sk pk) ([], m, t, l)).1 ++ rest := by
      rw [← hfull, htSign_eq, show p.d = (c + 1) + (p.d - (c + 1)) by omega, List.range_add,
        List.foldl_append]
      obtain ⟨rest, h⟩ := htLayer_grows p sk pk
        (List.map (fun x => c + 1 + x) (List.range (p.d - (c + 1))))
        ((List.range (c + 1)).foldl (htLayer p sk pk) ([], m, t, l))
      exact ⟨rest, h⟩
    have hlen := htLayer_length p hv sk pk m t l c
    rw [List.range_succ, List.foldl_append] at hpre
    rw [List.range_succ, List.foldl_append, List.foldl_append, ih (by omega)]
    obtain ⟨rest, hrest⟩ := hpre
    revert hrest hlen
    generalize List.foldl (htLayer p sk pk) ([], m, t, l) (List.range c) = st
    obtain ⟨sig, root, tree, leaf⟩ := st
    intro hlen hrest
    simp only [List.foldl_cons, List.foldl_nil, htLayer, htVerifyLayer] at hrest hlen ⊢
    have hs : (full.drop (c * p.xmssSigBytes)).take p.xmssSigBytes =
        xmssSign p root sk leaf pk { Adrs.zero with layer := c, tree := tree } := by
      rw [hrest, ← hlen, List.append_assoc, List.drop_left,
        List.take_left' (xmssSign_length p hv _ _ _ _ _)]
    rw [hs]

theorem h_div_d (p : Params) (hv : p.Valid) : p.h / p.d = p.hp := by
  rw [hv.h_eq]; exact Nat.mul_div_cancel_left _ (by have := hv.d_ge; omega)

/-- For a well-formed key, the root that `htSign` reaches is `PK.root`: each
layer's root is the root of the XMSS tree it signs with, and the top tree is
tree 0 of layer `d − 1`. -/
theorem htRoot_keyOk (p : Params) (hv : p.Valid) (m sk pk : Bytes) (t l : Nat) (root : Bytes)
    (ht : t < 2 ^ (p.h - p.h / p.d)) (hl : l < 2 ^ p.hp)
    (hroot : root = xmssNode p sk 0 p.hp pk { Adrs.zero with layer := p.d - 1 }) :
    htRoot p m sk pk t l = root := by
  have hd := hv.d_ge
  have ht' : t < 2 ^ (p.hp * (p.d - 1)) := by
    rw [h_div_d p hv, hv.h_eq] at ht
    have : p.d * p.hp - p.hp = p.hp * (p.d - 1) := by
      rw [Nat.mul_sub, Nat.mul_one, Nat.mul_comm]
    rwa [this] at ht
  have h0 : t >>> (p.hp * (p.d - 1)) = 0 := by
    rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_eq_of_lt ht'
  suffices H : ∀ c, c ≤ p.d →
      ((List.range c).foldl (htLayer p sk pk) ([], m, t, l)).2.2.1 = t >>> (p.hp * c) ∧
      ((List.range c).foldl (htLayer p sk pk) ([], m, t, l)).2.2.2 < 2 ^ p.hp ∧
      (0 < c → ((List.range c).foldl (htLayer p sk pk) ([], m, t, l)).2.1 =
        xmssNode p sk 0 p.hp pk { Adrs.zero with layer := c - 1, tree := t >>> (p.hp * (c - 1)) }) by
    unfold htRoot
    rw [(H p.d (le_refl _)).2.2 (by omega), h0, hroot]
    simp [Adrs.zero]
  intro c
  induction c with
  | zero => intro _; simp [hl]
  | succ c ih =>
    intro hc
    rw [List.range_succ, List.foldl_append]
    have ih := ih (by omega)
    revert ih
    generalize List.foldl (htLayer p sk pk) ([], m, t, l) (List.range c) = S
    obtain ⟨sig, r, tree, leaf⟩ := S
    rintro ⟨h1, h2, -⟩
    simp only at h1 h2
    subst h1
    simp only [List.foldl_cons, List.foldl_nil, htLayer]
    rw [xmss_correct p hv _ _ _ _ _ h2]
    refine ⟨?_, Nat.mod_lt _ (Nat.two_pow_pos _), fun _ => ?_⟩
    · rw [Nat.mul_succ, Nat.shiftRight_add]
    · simp

/-! ## SLH-DSA -/

theorem PRFmsg_length (p : Params) (hv : p.Valid) (k r m : Bytes) : (PRFmsg p k r m).length = p.n := by
  have := hv.n_le
  cases hf : p.family <;> simp only [PRFmsg, hf, shake256_length]
  split <;> simp [hmacSha256, hmacSha512, sha256_length, sha512_length] <;> omega

theorem forsSign_eq (p : Params) (md sk pk : Bytes) (adrs : Adrs) :
    forsSign p md sk pk adrs =
      (List.range p.k).flatMap (forsPiece p sk pk adrs (base2b md p.a p.k)) := rfl

theorem forsSign_length (p : Params) (hv : p.Valid) (md sk pk : Bytes) (adrs : Adrs) :
    (forsSign p md sk pk adrs).length = p.forsSigBytes := by
  rw [forsSign_eq, length_flatMap_const _ _ (forsPiece_length p hv sk pk adrs _)]
  simp [Params.forsSigBytes, Nat.add_comm, Nat.mul_assoc]

theorem htSign_length (p : Params) (hv : p.Valid) (m sk pk : Bytes) (t l : Nat) :
    (htSign p m sk pk t l).length = p.d * p.xmssSigBytes := by
  rw [htSign_eq]; exact htLayer_length p hv sk pk m t l p.d

theorem block_skPk (p : Params) (sk : Bytes) (i : Nat) : block p (skPk p sk) i = block p sk (i + 2) := by
  simp [block, skPk, List.drop_drop, Nat.add_mul, Nat.add_comm]

theorem sigBytes_parts (p : Params) (hv : p.Valid) :
    p.n + p.forsSigBytes + p.d * p.xmssSigBytes = p.sigBytes := by
  simp only [Params.sigBytes, Params.forsSigBytes, Params.xmssSigBytes, hv.h_eq]
  ring

/-- Verification of a signature assembled as Algorithm 19 assembles it, under
the public key held in the private key: it compares the root that `htSign`
reached with `PK.root`. Holds for every private key. -/
theorem slhVerify_parts (p : Params) (hv : p.Valid) (msg sk r : Bytes) (hr : r.length = p.n) :
    slhVerifyInternal p msg
      (r ++ forsSign p ((Hmsg p r (block p sk 2) (block p sk 3) msg).take p.mdBytes) (block p sk 0) (block p sk 2)
          { { Adrs.zero with tree := digestTree p (Hmsg p r (block p sk 2) (block p sk 3) msg) }.setTypeAndClear
              FORS_TREE with keypair := digestLeaf p (Hmsg p r (block p sk 2) (block p sk 3) msg) } ++
        htSign p (forsPkFromSig p
            (forsSign p ((Hmsg p r (block p sk 2) (block p sk 3) msg).take p.mdBytes) (block p sk 0) (block p sk 2)
              { { Adrs.zero with tree := digestTree p (Hmsg p r (block p sk 2) (block p sk 3) msg) }.setTypeAndClear
                  FORS_TREE with keypair := digestLeaf p (Hmsg p r (block p sk 2) (block p sk 3) msg) })
            ((Hmsg p r (block p sk 2) (block p sk 3) msg).take p.mdBytes) (block p sk 2)
            { { Adrs.zero with tree := digestTree p (Hmsg p r (block p sk 2) (block p sk 3) msg) }.setTypeAndClear
                FORS_TREE with keypair := digestLeaf p (Hmsg p r (block p sk 2) (block p sk 3) msg) })
          (block p sk 0) (block p sk 2) (digestTree p (Hmsg p r (block p sk 2) (block p sk 3) msg))
          (digestLeaf p (Hmsg p r (block p sk 2) (block p sk 3) msg)))
      (skPk p sk) =
    (htRoot p (forsPkFromSig p
            (forsSign p ((Hmsg p r (block p sk 2) (block p sk 3) msg).take p.mdBytes) (block p sk 0) (block p sk 2)
              { { Adrs.zero with tree := digestTree p (Hmsg p r (block p sk 2) (block p sk 3) msg) }.setTypeAndClear
                  FORS_TREE with keypair := digestLeaf p (Hmsg p r (block p sk 2) (block p sk 3) msg) })
            ((Hmsg p r (block p sk 2) (block p sk 3) msg).take p.mdBytes) (block p sk 2)
            { { Adrs.zero with tree := digestTree p (Hmsg p r (block p sk 2) (block p sk 3) msg) }.setTypeAndClear
                FORS_TREE with keypair := digestLeaf p (Hmsg p r (block p sk 2) (block p sk 3) msg) })
          (block p sk 0) (block p sk 2) (digestTree p (Hmsg p r (block p sk 2) (block p sk 3) msg))
          (digestLeaf p (Hmsg p r (block p sk 2) (block p sk 3) msg)) == block p sk 3) := by
  generalize hD : Hmsg p r (block p sk 2) (block p sk 3) msg = D
  generalize hF : forsSign p (D.take p.mdBytes) (block p sk 0) (block p sk 2)
    { { Adrs.zero with tree := digestTree p D }.setTypeAndClear FORS_TREE with keypair := digestLeaf p D } = sF
  have hFl : sF.length = p.forsSigBytes := by rw [← hF]; exact forsSign_length p hv _ _ _ _
  generalize hS : htSign p _ (block p sk 0) (block p sk 2) (digestTree p D) (digestLeaf p D) = sH
  have hSl : sH.length = p.d * p.xmssSigBytes := by rw [← hS]; exact htSign_length p hv _ _ _ _ _
  unfold slhVerifyInternal
  have hlen : (r ++ sF ++ sH).length = p.sigBytes := by
    simp only [List.length_append, hr, hFl, hSl]; exact sigBytes_parts p hv
  simp only [hlen, ne_eq, not_true_eq_false, ↓reduceIte, block_skPk]
  have e1 : (r ++ sF ++ sH).take p.n = r := by
    rw [List.append_assoc, List.take_left' hr]
  have e2 : ((r ++ sF ++ sH).drop p.n).take p.forsSigBytes = sF := by
    rw [List.append_assoc, List.drop_left' hr, List.take_left' hFl]
  have e3 : (r ++ sF ++ sH).drop (p.n + p.forsSigBytes) = sH := by
    rw [List.append_assoc, ← List.drop_drop, List.drop_left' hr, List.drop_left' hFl]
  simp only [show (0 + 2 : Nat) = 2 from rfl, show (1 + 2 : Nat) = 3 from rfl, e1, e2, e3, hD]
  rw [← hS, htVerify_htSign p hv]

theorem digestTree_lt (p : Params) (D : Bytes) : digestTree p D < 2 ^ (p.h - p.h / p.d) :=
  Nat.mod_lt _ (Nat.two_pow_pos _)

theorem digestLeaf_lt (p : Params) (hv : p.Valid) (D : Bytes) : digestLeaf p D < 2 ^ p.hp := by
  rw [← h_div_d p hv]; exact Nat.mod_lt _ (Nat.two_pow_pos _)

/-- A signature of Algorithm 19 has the length of Table 2, for every key and message. -/
theorem slhSignInternal_length (p : Params) (hv : p.Valid) (msg sk addrnd : Bytes) :
    (slhSignInternal p msg sk addrnd).length = p.sigBytes := by
  unfold slhSignInternal
  simp only [List.length_append, PRFmsg_length p hv, forsSign_length p hv, htSign_length p hv]
  exact sigBytes_parts p hv

/-- Completeness of Algorithms 19 and 20: under a well-formed key, a
signature verifies under the public key held in the key. -/
theorem slh_complete_internal (p : Params) (hv : p.Valid) (msg sk addrnd : Bytes) (hk : KeyOk p sk) :
    slhVerifyInternal p msg (slhSignInternal p msg sk addrnd) (skPk p sk) = true := by
  unfold slhSignInternal
  simp only []
  rw [slhVerify_parts p hv _ _ _ (PRFmsg_length p hv _ _ _),
    htRoot_keyOk p hv _ _ _ _ _ _ (digestTree_lt p _) (digestLeaf_lt p hv _) hk]
  simp

/-- Completeness of Algorithms 22 and 24. -/
theorem slh_complete (p : Params) (hv : p.Valid) (msg ctx sk addrnd : Bytes) (hc : ctx.length ≤ 255)
    (hk : KeyOk p sk) :
    ∃ sig, slhSign p msg ctx sk addrnd = some sig ∧ slhVerify p msg sig ctx (skPk p sk) = true := by
  refine ⟨slhSignInternal p (withContext msg ctx) sk addrnd, ?_, ?_⟩
  · simp [slhSign, show ¬ ctx.length > 255 by omega]
  · simp only [slhVerify, show ¬ ctx.length > 255 by omega, ↓reduceIte]
    exact slh_complete_internal p hv _ _ _ hk

/-- Key generation (Algorithm 18) produces well-formed keys, and the public
key is the one the private key holds. -/
theorem keygen_keyOk (p : Params) (hv : p.Valid) (skSeed skPrf pkSeed : Bytes)
    (h1 : skSeed.length = p.n) (h2 : skPrf.length = p.n) (h3 : pkSeed.length = p.n) :
    KeyOk p (slhKeygenInternal p skSeed skPrf pkSeed).1 ∧
      (slhKeygenInternal p skSeed skPrf pkSeed).2 = skPk p (slhKeygenInternal p skSeed skPrf pkSeed).1 := by
  have hr := xmssNode_length p hv skSeed 0 p.hp pkSeed { Adrs.zero with layer := p.d - 1 }
  have b0 : ∀ x rest : Bytes, x.length = p.n → block p (x ++ rest) 0 = x := by
    intro x rest hx; simp [block, List.take_left' hx]
  have bs : ∀ x rest : Bytes, x.length = p.n → ∀ i, block p (x ++ rest) (i + 1) = block p rest i := by
    intro x rest hx i
    simp only [block, Nat.add_mul, Nat.one_mul, Nat.add_comm _ p.n, ← List.drop_drop, List.drop_left' hx]
  simp only [slhKeygenInternal, List.append_assoc]
  refine ⟨?_, ?_⟩
  · simp only [KeyOk]
    rw [b0 _ _ h1, bs _ _ h1 1, bs _ _ h2 0, b0 _ _ h3, bs _ _ h1 2, bs _ _ h2 1, bs _ _ h3 0]
    simp [block, List.take_of_length_le, hr]
  · simp only [skPk, show 2 * p.n = p.n + p.n from by omega, ← List.drop_drop, List.drop_left' h1,
      List.drop_left' h2]

end Spec
