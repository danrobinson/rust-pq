import Slhdsa.Proofs.Xmss
open Aeneas Aeneas.Std Result

/-! FORS (FIPS 205 §8). -/

namespace slhdsa

@[local simp] theorem fors_FORS_PRF_eq : address.FORS_PRF = 6#u32 := by simp [global_simps]
@[local simp] theorem fors_FORS_ROOTS_eq : address.FORS_ROOTS = 4#u32 := by simp [global_simps]

@[local step]
theorem fors_extend_from_slice_spec (v : alloc.vec.Vec U8) (s : Slice U8)
    (h : v.length + s.length ≤ Usize.max) :
    alloc.vec.Vec.extend_from_slice core.clone.CloneU8 v s ⦃ r =>
      r.val = v.val ++ s.val ∧ r.length = v.length + s.length ⦄ := by
  unfold alloc.vec.Vec.extend_from_slice
  simp only [h, ↓reduceDIte]
  apply WP.spec_bind (List.clone_spec (l := s.val) (by intros; simp [liftFun1]))
  intro l' hl'
  simp [hl']

@[step]
theorem fors_sk_gen_spec (p : params.Params) (sk pk : Slice U8) (a : address.Adrs) (idx : U32)
    (hv : (paramsS p).Valid) (hsk : sk.length = p.n.val) (hpk : pk.length = p.n.val) :
    fors.fors_sk_gen p sk pk a idx ⦃ r =>
      bytes r.val = Spec.forsSkGen (paramsS p) (bytes sk.val) (bytes pk.val) (adrsS a) idx.val ∧
      r.length = p.n.val ⦄ := by
  have hn : p.n.val ≤ 32 := by
    rcases hv.n_cases with h | h | h <;> simp only [paramsS_n] at h <;> omega
  unfold fors.fors_sk_gen
  step as ⟨a0, a0_post, a0_eq⟩
  step as ⟨a1, a1_post⟩
  step as ⟨a2, a2_post⟩
  step with thash_f_spec p pk a2 sk hv hpk (by scalar_tac) as ⟨r, r_post, r_len⟩
  refine ⟨?_, r_len⟩
  rw [r_post, Spec.forsSkGen, PRF_eq_F]
  simp [adrsS, Spec.Adrs.setTypeAndClear, Spec.FORS_PRF, a2_post, a1_post, a0_eq]

theorem fors_node_spec_aux (p : params.Params) (sk pk : Slice U8) (a : address.Adrs)
    (hv : (paramsS p).Valid) (hsk : sk.length = p.n.val) (hpk : pk.length = p.n.val) (n : Nat) :
    ∀ (i z : U32), z.val = n → (i.val + 1) * 2 ^ n ≤ 2 ^ 32 →
    fors.fors_node p sk i z pk a ⦃ r =>
      bytes r.val = Spec.forsNode (paramsS p) (bytes sk.val) i.val n (bytes pk.val) (adrsS a) ∧
      r.length = p.n.val ⦄ := by
  have hn : p.n.val ≤ 32 := by
    rcases hv.n_cases with h | h | h <;> simp only [paramsS_n] at h <;> omega
  induction n with
  | zero =>
    intro i z hz h
    have hz0 : z = 0#u32 := by scalar_tac
    unfold fors.fors_node
    simp only [hz0, ↓reduceIte]
    step with fors_sk_gen_spec p sk pk a i hv hsk hpk as ⟨s, s_post, s_len⟩
    step as ⟨a0, a0_post⟩
    step as ⟨a1, a1_post⟩
    step with thash_f_spec p pk a1 (alloc.vec.Vec.deref s) hv hpk (by simp; scalar_tac)
      as ⟨r, r_post, r_len⟩
    refine ⟨?_, r_len⟩
    rw [r_post]
    simp [Spec.forsNode, adrsS, s_post, a1_post, a0_post]
  | succ n ih =>
    intro i z hz h
    have hz0 : ¬ z = 0#u32 := by scalar_tac
    have hpos : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have h1 : (2 * i.val + 1 + 1) * 2 ^ n ≤ 2 ^ 32 := by
      have : (2 * i.val + 1 + 1) * 2 ^ n = (i.val + 1) * 2 ^ (n + 1) := by ring
      omega
    have h2 : (2 * i.val + 1) * 2 ^ n ≤ 2 ^ 32 := by nlinarith
    have h3 : 2 * i.val + 2 ≤ 2 ^ 32 := by nlinarith
    unfold fors.fors_node
    simp only [hz0, ↓reduceIte]
    step as ⟨i1, i1_post⟩
    step as ⟨i2, i2_post⟩
    step with ih i1 i2 (by scalar_tac) (by simp [*]; omega) as ⟨l, l_post, l_len⟩
    step as ⟨i3, i3_post⟩
    step with ih i3 i2 (by scalar_tac) (by simp [*]; omega) as ⟨r', r'_post, r'_len⟩
    step as ⟨a0, a0_post⟩
    step as ⟨a1, a1_post⟩
    step with hash2_spec p pk a1 (alloc.vec.Vec.deref l) (alloc.vec.Vec.deref r') hv hpk
      (by simpa using l_len) (by simpa using r'_len) as ⟨r, r_post, r_len⟩
    refine ⟨?_, r_len⟩
    rw [r_post]
    simp [Spec.forsNode, adrsS, l_post, r'_post, a1_post, a0_post, i1_post, i3_post, hz]

@[step]
theorem fors_node_spec (p : params.Params) (sk : Slice U8) (i z : U32) (pk : Slice U8)
    (a : address.Adrs) (hv : (paramsS p).Valid) (hsk : sk.length = p.n.val)
    (hpk : pk.length = p.n.val) (h : (i.val + 1) * 2 ^ z.val ≤ 2 ^ 32) :
    fors.fors_node p sk i z pk a ⦃ r =>
      bytes r.val = Spec.forsNode (paramsS p) (bytes sk.val) i.val z.val (bytes pk.val) (adrsS a) ∧
      r.length = p.n.val ⦄ :=
  fors_node_spec_aux p sk pk a hv hsk hpk z.val i z rfl h

theorem fors_xor_one_lt (x m : Nat) (h : x < 2 * m) : x ^^^ 1 < 2 * m := by
  rcases Nat.even_or_odd x with h' | h'
  · rw [Nat.xor_one_of_even h']; obtain ⟨q, hq⟩ := h'; omega
  · rw [Nat.xor_one_of_odd h']; omega

/-- `i · 2^a` fits in 32 bits. -/
theorem fors_shl_arith (a i : Nat) (ha : a ≤ 14) (hi : i < 35) :
    (i <<< a) % 2 ^ 32 = i * 2 ^ a ∧ i * 2 ^ a + 2 ^ a ≤ 35 * 2 ^ 14 := by
  have h1 : 2 ^ a ≤ 2 ^ 14 := Nat.pow_le_pow_right (by omega) ha
  have h2 : (i + 1) * 2 ^ a ≤ 35 * 2 ^ 14 := Nat.mul_le_mul (by omega) h1
  rw [Nat.add_mul, Nat.one_mul] at h2
  refine ⟨?_, h2⟩
  rw [Nat.shiftLeft_eq]
  exact Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.le_add_right _ _) (lt_of_le_of_lt h2 (by norm_num)))

theorem fors_inner_arith (a i idx j : Nat) (ha : a ≤ 14) (hi : i < 35) (hidx : idx < 2 ^ a)
    (hj : j < a) :
    (i <<< (a - j)) % 2 ^ 32 = i * 2 ^ (a - j) ∧
    i * 2 ^ (a - j) + ((idx / 2 ^ j) ^^^ 1) ≤ 2 ^ 32 - 1 ∧
    (i * 2 ^ (a - j) + ((idx / 2 ^ j) ^^^ 1) + 1) * 2 ^ j ≤ 2 ^ 32 := by
  have h1 : 2 ^ (a - j) ≤ 2 ^ 14 := Nat.pow_le_pow_right (by omega) (by omega)
  have hsplit : 2 ^ a = 2 ^ j * 2 ^ (a - j) := by rw [← Nat.pow_add]; congr 1; omega
  have h2 : 2 ^ (a - j) = 2 * 2 ^ (a - j - 1) := by
    rw [← Nat.pow_succ']; congr 1; omega
  have h3 : idx / 2 ^ j < 2 ^ (a - j) := Nat.div_lt_of_lt_mul (by rw [← hsplit]; exact hidx)
  have h4 : (idx / 2 ^ j) ^^^ 1 < 2 ^ (a - j) := by
    rw [h2] at h3 ⊢; exact fors_xor_one_lt _ _ h3
  have h5 : i * 2 ^ (a - j) ≤ 34 * 2 ^ 14 := Nat.mul_le_mul (by omega) h1
  have h6 : i * 2 ^ (a - j) + ((idx / 2 ^ j) ^^^ 1) + 1 ≤ (i + 1) * 2 ^ (a - j) := by
    rw [Nat.add_mul, Nat.one_mul]; omega
  have h7 : 2 ^ a ≤ 2 ^ 14 := Nat.pow_le_pow_right (by omega) ha
  refine ⟨?_, by omega, ?_⟩
  · rw [Nat.shiftLeft_eq]; exact Nat.mod_eq_of_lt (by omega)
  · calc (i * 2 ^ (a - j) + ((idx / 2 ^ j) ^^^ 1) + 1) * 2 ^ j
        ≤ ((i + 1) * 2 ^ (a - j)) * 2 ^ j := Nat.mul_le_mul_right _ h6
      _ = (i + 1) * 2 ^ a := by rw [hsplit]; ring
      _ ≤ 35 * 2 ^ 14 := Nat.mul_le_mul (by omega) h7
      _ ≤ 2 ^ 32 := by norm_num

/-- The `j`-th authentication-path node of FORS tree `i` (Algorithm 16, lines 6–8). -/
def forsAuth (P : Spec.Params) (sk pk : Spec.Bytes) (adrs : Spec.Adrs) (i idx j : Nat) :
    Spec.Bytes :=
  Spec.forsNode P sk (i * 2 ^ (P.a - j) + ((idx / 2 ^ j) ^^^ 1)) j pk adrs

theorem fors_flatMap_range_succ {β} (f : Nat → List β) (n : Nat) :
    (List.range (n + 1)).flatMap f = (List.range n).flatMap f ++ f n := by
  rw [List.range_succ, List.flatMap_append]; simp

theorem fors_sign_inner_spec (p : params.Params) (sk pk : Slice U8) (a : address.Adrs)
    (sig : alloc.vec.Vec U8) (i idx j : U32) (S0 : Spec.Bytes) (L0 : Nat)
    (hv : (paramsS p).Valid) (hsk : sk.length = p.n.val) (hpk : pk.length = p.n.val)
    (hi : i.val < p.k.val) (hidx : idx.val < 2 ^ p.a.val) (hj : j.val ≤ p.a.val)
    (hL : L0 ≤ 100000) (hlen : sig.length = L0 + j.val * p.n.val)
    (hinv : bytes sig.val = S0 ++ (List.range j.val).flatMap
      (forsAuth (paramsS p) (bytes sk.val) (bytes pk.val) (adrsS a) i.val idx.val)) :
    fors.fors_sign_loop0_loop0 p.n p.h p.d p.hp p.a p.k p.m sk pk a p.a sig i idx j ⦃ r =>
      r.length = L0 + p.a.val * p.n.val ∧
      bytes r.val = S0 ++ (List.range p.a.val).flatMap
        (forsAuth (paramsS p) (bytes sk.val) (bytes pk.val) (adrsS a) i.val idx.val) ⦄ := by
  have hn : p.n.val ≤ 32 := by
    rcases hv.n_cases with h | h | h <;> simp only [paramsS_n] at h <;> omega
  have ha14 : p.a.val ≤ 14 := hv.a_le
  have hk35 : p.k.val ≤ 35 := hv.k_le
  unfold fors.fors_sign_loop0_loop0
  apply loop.spec_decr_nat
    (measure := fun (q : alloc.vec.Vec U8 × U32) => p.a.val - q.2.val)
    (inv := fun q => q.2.val ≤ p.a.val ∧ q.1.length = L0 + q.2.val * p.n.val ∧
      bytes q.1.val = S0 ++ (List.range q.2.val).flatMap
        (forsAuth (paramsS p) (bytes sk.val) (bytes pk.val) (adrsS a) i.val idx.val))
  · rintro ⟨sig, j⟩ ⟨hj, hlen, hinv⟩
    simp only [fors.fors_sign_loop0_loop0.body]
    simp only at hj hlen hinv
    by_cases hjA : j < p.a
    · simp only [hjA, ↓reduceIte]
      have hjlt : j.val < p.a.val := by scalar_tac
      have hjn : j.val * p.n.val ≤ 14 * 32 := Nat.mul_le_mul (by omega) hn
      obtain ⟨ha1, ha2, ha3⟩ :=
        fors_inner_arith p.a.val i.val idx.val j.val ha14 (by omega) hidx hjlt
      step as ⟨i1, i1_post⟩
      step as ⟨s, s_post⟩
      step as ⟨i2, i2_post⟩
      step as ⟨i3, i3_post⟩
      have hs : s.val = (idx.val / 2 ^ j.val) ^^^ 1 := by
        rw [s_post, UScalar.val_xor, i1_post, Nat.shiftRight_eq_div_pow]; rfl
      have hi3 : i3.val = i.val * 2 ^ (p.a.val - j.val) := by
        rw [i3_post, i2_post]; simpa [U32.size, U32.numBits] using ha1
      step as ⟨i4, i4_post⟩
      have hi4 : i4.val = i.val * 2 ^ (p.a.val - j.val) + ((idx.val / 2 ^ j.val) ^^^ 1) := by
        rw [i4_post, hi3, hs]
      step with fors_node_spec p sk i4 j pk a hv hsk hpk (by rw [hi4]; exact ha3)
        as ⟨node, node_post, node_len⟩
      step as ⟨sig1, sig1_post, sig1_len⟩
      step as ⟨j1, j1_post⟩
      refine ⟨by scalar_tac, ?_, ?_, by scalar_tac⟩
      · simp only [vec_deref_length] at sig1_len
        rw [sig1_len, hlen, node_len, j1_post, Nat.add_mul]; omega
      · rw [sig1_post, bytes_append, hinv, j1_post, fors_flatMap_range_succ _ j.val]
        simp [forsAuth, node_post, hi4]
    · simp only [hjA, ↓reduceIte]
      have hjeq : j.val = p.a.val := by scalar_tac
      rw [hjeq] at hlen hinv
      simp [hlen, hinv]
  · exact ⟨hj, hlen, hinv⟩

/-- The part of a FORS signature for tree `i`: the secret value and its authentication path. -/
def forsSignTree (P : Spec.Params) (sk pk : Spec.Bytes) (adrs : Spec.Adrs) (ind : List Nat)
    (i : Nat) : Spec.Bytes :=
  Spec.forsSkGen P sk pk adrs (i * 2 ^ P.a + ind[i]!) ++
    (List.range P.a).flatMap (forsAuth P sk pk adrs i ind[i]!)

theorem forsSign_eq (P : Spec.Params) (md sk pk : Spec.Bytes) (adrs : Spec.Adrs) :
    Spec.forsSign P md sk pk adrs =
      (List.range P.k).flatMap (forsSignTree P sk pk adrs (Spec.base2b md P.a P.k)) := by
  rfl

theorem fors_nats_getElem! (l : List U32) (i : Nat) (h : i < l.length) :
    (nats l)[i]! = (l[i]'h).val := by
  simp [nats, h]

theorem fors_sign_loop_spec (p : params.Params) (sk pk : Slice U8) (a : address.Adrs)
    (indices : alloc.vec.Vec U32) (sig : alloc.vec.Vec U8) (i : U32)
    (hv : (paramsS p).Valid) (hsk : sk.length = p.n.val) (hpk : pk.length = p.n.val)
    (hlenI : indices.length = p.k.val) (hbd : ∀ d ∈ indices.val, d.val < 2 ^ p.a.val)
    (hi : i.val ≤ p.k.val) (hlen : sig.length = i.val * (1 + p.a.val) * p.n.val)
    (hinv : bytes sig.val = (List.range i.val).flatMap
      (forsSignTree (paramsS p) (bytes sk.val) (bytes pk.val) (adrsS a) (nats indices.val))) :
    fors.fors_sign_loop0 p.n p.h p.d p.hp p.a p.k p.m sk pk a p.a indices sig i ⦃ r =>
      r.length = p.k.val * (1 + p.a.val) * p.n.val ∧
      bytes r.val = (List.range p.k.val).flatMap
        (forsSignTree (paramsS p) (bytes sk.val) (bytes pk.val) (adrsS a) (nats indices.val)) ⦄ := by
  have hn : p.n.val ≤ 32 := by
    rcases hv.n_cases with h | h | h <;> simp only [paramsS_n] at h <;> omega
  have ha14 : p.a.val ≤ 14 := hv.a_le
  have hk35 : p.k.val ≤ 35 := hv.k_le
  unfold fors.fors_sign_loop0
  apply loop.spec_decr_nat
    (measure := fun (q : alloc.vec.Vec U8 × U32) => p.k.val - q.2.val)
    (inv := fun q => q.2.val ≤ p.k.val ∧ q.1.length = q.2.val * (1 + p.a.val) * p.n.val ∧
      bytes q.1.val = (List.range q.2.val).flatMap
        (forsSignTree (paramsS p) (bytes sk.val) (bytes pk.val) (adrsS a) (nats indices.val)))
  · rintro ⟨sig, i⟩ ⟨hi, hlen, hinv⟩
    simp only [fors.fors_sign_loop0.body]
    simp only at hi hlen hinv
    by_cases hiK : i < p.k
    · simp only [hiK, ↓reduceIte]
      have hilt : i.val < p.k.val := by scalar_tac
      have hbound : i.val * (1 + p.a.val) * p.n.val ≤ 35 * 15 * 32 :=
        Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by omega)) hn
      obtain ⟨hs1, hs2⟩ := fors_shl_arith p.a.val i.val ha14 (by omega)
      step as ⟨i1, i1_post⟩
      have hi1 : i1.val = i.val := by rw [i1_post]; simp
      step as ⟨idx, idx_post⟩
      have hidx : idx.val < 2 ^ p.a.val := by rw [idx_post]; exact hbd _ (List.getElem_mem _)
      have hind : (nats indices.val)[i.val]! = idx.val := by
        rw [fors_nats_getElem! _ _ (by scalar_tac)]; simp [idx_post, hi1]
      step as ⟨i2, i2_post⟩
      have hi2 : i2.val = i.val * 2 ^ p.a.val := by
        rw [i2_post]; simpa [U32.size, U32.numBits] using hs1
      step as ⟨i3, i3_post⟩
      step with fors_sk_gen_spec p sk pk a i3 hv hsk hpk as ⟨sk1, sk1_post, sk1_len⟩
      step as ⟨sig1, sig1_post, sig1_len⟩
      have hl1 : sig1.length = sig.length + p.n.val := by
        rw [sig1_len]; simp [sk1_len]
      step with fors_sign_inner_spec p sk pk a sig1 i idx 0#u32 (bytes sig1.val) sig1.length
        hv hsk hpk hilt hidx (by simp) (by omega) (by simp) (by simp)
        as ⟨sig2, sig2_len, sig2_post⟩
      step as ⟨i4, i4_post⟩
      refine ⟨by scalar_tac, ?_, ?_, by scalar_tac⟩
      · rw [sig2_len, hl1, hlen, i4_post]; ring
      · rw [sig2_post, sig1_post, bytes_append, hinv, i4_post, fors_flatMap_range_succ _ i.val]
        simp [forsSignTree, hind, sk1_post, i3_post, hi2]
    · simp only [hiK, ↓reduceIte]
      have hieq : i.val = p.k.val := by scalar_tac
      rw [hieq] at hlen hinv
      simp [hlen, hinv]
  · exact ⟨hi, hlen, hinv⟩

@[step]
theorem fors_sign_spec (p : params.Params) (md sk pk : Slice U8) (a : address.Adrs)
    (hv : (paramsS p).Valid) (hmd : md.length = (p.k.val * p.a.val + 7) / 8)
    (hsk : sk.length = p.n.val) (hpk : pk.length = p.n.val) :
    fors.fors_sign p md sk pk a ⦃ r =>
      bytes r.val = Spec.forsSign (paramsS p) (bytes md.val) (bytes sk.val) (bytes pk.val)
        (adrsS a) ∧
      r.length = p.k.val * (1 + p.a.val) * p.n.val ⦄ := by
  have ha1 : 1 ≤ p.a.val := hv.a_pos
  have ha14 : p.a.val ≤ 14 := hv.a_le
  unfold fors.fors_sign
  step as ⟨i, i_post⟩
  have hi : i.val = p.k.val := by rw [i_post]; simp
  step with base_2b_spec md p.a i (by omega) (by rw [hi, hmd]; omega)
    as ⟨indices, hind, hlenI, hbd⟩
  rw [hi] at hind hlenI
  apply WP.spec_mono
  · exact fors_sign_loop_spec p sk pk a indices (alloc.vec.Vec.new U8) 0#u32 hv hsk hpk
      (by simpa using hlenI) hbd (by simp) (by simp) (by simp)
  · intro r ⟨h1, h2⟩
    refine ⟨?_, h1⟩
    rw [forsSign_eq, h2, hind]; rfl

/-- The root of FORS tree `i` recomputed from a signature (Algorithm 17, lines 3–20). -/
def forsRoot (P : Spec.Params) (sig pk : Spec.Bytes) (adrs : Spec.Adrs) (ind : List Nat)
    (i : Nat) : Spec.Bytes :=
  Spec.climb P
    (Spec.F P pk { adrs with word2 := 0, word3 := i * 2 ^ P.a + ind[i]! }
      (Spec.block P sig (i * (P.a + 1))))
    ind[i]! (i * 2 ^ P.a + ind[i]!)
    ((sig.drop ((i * (P.a + 1) + 1) * P.n)).take (P.a * P.n)) P.a pk adrs

theorem forsPkFromSig_eq (P : Spec.Params) (sig md pk : Spec.Bytes) (adrs : Spec.Adrs) :
    Spec.forsPkFromSig P sig md pk adrs =
      Spec.T P pk { adrs.setTypeAndClear Spec.FORS_ROOTS with keypair := adrs.keypair }
        ((List.range P.k).flatMap (forsRoot P sig pk adrs (Spec.base2b md P.a P.k))) := by
  rfl

theorem fors_pk_from_sig_loop_spec (p : params.Params) (sig pk : Slice U8) (a : address.Adrs)
    (indices : alloc.vec.Vec U32) (roots : alloc.vec.Vec U8) (i : U32)
    (hv : (paramsS p).Valid) (hs : sig.length = p.k.val * (1 + p.a.val) * p.n.val)
    (hpk : pk.length = p.n.val)
    (hlenI : indices.length = p.k.val) (hbd : ∀ d ∈ indices.val, d.val < 2 ^ p.a.val)
    (hi : i.val ≤ p.k.val) (hlen : roots.length = i.val * p.n.val)
    (hinv : bytes roots.val = (List.range i.val).flatMap
      (forsRoot (paramsS p) (bytes sig.val) (bytes pk.val) (adrsS a) (nats indices.val))) :
    fors.fors_pk_from_sig_loop p.n p.h p.d p.hp p.a p.k p.m sig pk a p.a indices roots i ⦃ r =>
      r.length = p.k.val * p.n.val ∧
      bytes r.val = (List.range p.k.val).flatMap
        (forsRoot (paramsS p) (bytes sig.val) (bytes pk.val) (adrsS a) (nats indices.val)) ⦄ := by
  have hn : p.n.val ≤ 32 := by
    rcases hv.n_cases with h | h | h <;> simp only [paramsS_n] at h <;> omega
  have ha14 : p.a.val ≤ 14 := hv.a_le
  have hk35 : p.k.val ≤ 35 := hv.k_le
  unfold fors.fors_pk_from_sig_loop
  apply loop.spec_decr_nat
    (measure := fun (q : alloc.vec.Vec U8 × U32) => p.k.val - q.2.val)
    (inv := fun q => q.2.val ≤ p.k.val ∧ q.1.length = q.2.val * p.n.val ∧
      bytes q.1.val = (List.range q.2.val).flatMap
        (forsRoot (paramsS p) (bytes sig.val) (bytes pk.val) (adrsS a) (nats indices.val)))
  · rintro ⟨roots, i⟩ ⟨hi, hlen, hinv⟩
    simp only [fors.fors_pk_from_sig_loop.body]
    simp only at hi hlen hinv
    by_cases hiK : i < p.k
    · simp only [hiK, ↓reduceIte]
      have hilt : i.val < p.k.val := by scalar_tac
      have hin : i.val * p.n.val ≤ 35 * 32 := Nat.mul_le_mul (by omega) hn
      have hmul : i.val * (p.a.val + 1) ≤ 34 * 15 := Nat.mul_le_mul (by omega) (by omega)
      obtain ⟨hs1, hs2⟩ := fors_shl_arith p.a.val i.val ha14 (by omega)
      have hblocks : (i.val * (p.a.val + 1) + 1 + p.a.val) * p.n.val ≤ sig.length := by
        rw [hs]
        apply Nat.mul_le_mul_right
        calc i.val * (p.a.val + 1) + 1 + p.a.val = (i.val + 1) * (1 + p.a.val) := by ring
          _ ≤ p.k.val * (1 + p.a.val) := Nat.mul_le_mul_right _ (by omega)
      step as ⟨i1, i1_post⟩
      step as ⟨i2, i2_post⟩
      step as ⟨first, first_post⟩
      have hfirst : first.val = i.val * (p.a.val + 1) := by
        rw [first_post]; simp [i2_post, i1_post]
      step as ⟨i3, i3_post⟩
      have hi3 : i3.val = i.val * 2 ^ p.a.val := by
        rw [i3_post]; simpa [U32.size, U32.numBits] using hs1
      step as ⟨i4, i4_post⟩
      have hi4 : i4.val = i.val := by rw [i4_post]; simp
      step as ⟨i5, i5_post⟩
      have hidx : i5.val < 2 ^ p.a.val := by rw [i5_post]; exact hbd _ (List.getElem_mem _)
      have hind : (nats indices.val)[i.val]! = i5.val := by
        rw [fors_nats_getElem! _ _ (by scalar_tac)]; simp [i5_post, hi4]
      step as ⟨leaf, leaf_post⟩
      step with block_spec sig p.n first (by
        rw [hfirst]
        exact le_trans (Nat.mul_le_mul_right _ (by omega)) hblocks) as ⟨sk, sk_post, sk_len⟩
      step as ⟨a0, a0_post⟩
      step as ⟨a1, a1_post⟩
      step with thash_f_spec p pk a1 (alloc.vec.Vec.deref sk) hv hpk (by simp; scalar_tac)
        as ⟨node, node_post, node_len⟩
      step as ⟨i6, i6_post⟩
      step with climb_spec p node leaf sig i6 p.a pk a i.val i5.val hv node_len hpk
        (by rw [i6_post, hfirst]; exact hblocks) (by omega)
        (by rw [leaf_post, hi3]) hidx as ⟨root, root_post, root_len⟩
      step as ⟨roots1, roots1_post, roots1_len⟩
      step as ⟨i7, i7_post⟩
      refine ⟨by scalar_tac, ?_, ?_, by scalar_tac⟩
      · simp only [vec_deref_length] at roots1_len
        rw [roots1_len, hlen, root_len, i7_post, Nat.add_mul]; omega
      · have hsk : bytes sk.val = Spec.block (paramsS p) (bytes sig.val) first.val :=
          bytes_block p sig.val sk.val first.val sk_post
        rw [roots1_post, bytes_append, hinv, i7_post, fors_flatMap_range_succ _ i.val]
        simp [forsRoot, hind, root_post, node_post, hsk, a1_post, a0_post,
          adrsS, leaf_post, hi3, i6_post, hfirst]
    · simp only [hiK, ↓reduceIte]
      have hieq : i.val = p.k.val := by scalar_tac
      rw [hieq] at hlen hinv
      simp [hlen, hinv]
  · exact ⟨hi, hlen, hinv⟩

@[step]
theorem fors_pk_from_sig_spec (p : params.Params) (sig md pk : Slice U8) (a : address.Adrs)
    (hv : (paramsS p).Valid) (hs : sig.length = p.k.val * (1 + p.a.val) * p.n.val)
    (hmd : md.length = (p.k.val * p.a.val + 7) / 8) (hpk : pk.length = p.n.val) :
    fors.fors_pk_from_sig p sig md pk a ⦃ r =>
      bytes r.val = Spec.forsPkFromSig (paramsS p) (bytes sig.val) (bytes md.val) (bytes pk.val)
        (adrsS a) ∧
      r.length = p.n.val ⦄ := by
  have hn : p.n.val ≤ 32 := by
    rcases hv.n_cases with h | h | h <;> simp only [paramsS_n] at h <;> omega
  have ha1 : 1 ≤ p.a.val := hv.a_pos
  have ha14 : p.a.val ≤ 14 := hv.a_le
  have hk35 : p.k.val ≤ 35 := hv.k_le
  unfold fors.fors_pk_from_sig
  step as ⟨i, i_post⟩
  have hi : i.val = p.k.val := by rw [i_post]; simp
  step with base_2b_spec md p.a i (by omega) (by rw [hi, hmd]; omega)
    as ⟨indices, hind, hlenI, hbd⟩
  rw [hi] at hind hlenI
  step with fors_pk_from_sig_loop_spec p sig pk a indices (alloc.vec.Vec.new U8) 0#u32 hv hs hpk
    (by simpa using hlenI) hbd (by simp) (by simp) (by simp) as ⟨roots, hrl, hroots⟩
  have hrb : roots.length ≤ 35 * 32 := by rw [hrl]; exact Nat.mul_le_mul hk35 hn
  step as ⟨a0, a0_post, a0_eq⟩
  step as ⟨a1, a1_post⟩
  step with thash_h_spec p pk a1 (alloc.vec.Vec.deref roots) hv hpk (by simp; scalar_tac)
    as ⟨r, r_post, r_len⟩
  refine ⟨?_, r_len⟩
  rw [r_post, forsPkFromSig_eq, T_eq_H, vec_deref_val, hroots, hind]
  simp [adrsS, a1_post, a0_eq, Spec.Adrs.setTypeAndClear, Spec.FORS_ROOTS]

end slhdsa
