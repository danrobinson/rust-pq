import Slhdsa.Proofs.Xmss
open Aeneas Aeneas.Std Result

/-! FORS. -/

namespace slhdsa

@[local simp, local scalar_tac_simps] theorem fors_A_eq : params.A = 12#u32 := by simp [global_simps]
@[local simp, local scalar_tac_simps] theorem fors_K_eq : params.K = 14#u32 := by simp [global_simps]
@[local simp] theorem fors_FORS_PRF_eq : address.FORS_PRF = 6#u32 := by simp [global_simps]
@[local simp] theorem fors_FORS_ROOTS_eq : address.FORS_ROOTS = 4#u32 := by simp [global_simps]

@[local step]
theorem fors_extend_from_slice_spec (v : alloc.vec.Vec U8) (s : Slice U8)
    (h : v.length + s.length ≤ Usize.max) :
    alloc.vec.Vec.extend_from_slice core.clone.CloneU8 v s ⦃ r => r.val = v.val ++ s.val ⦄ := by
  unfold alloc.vec.Vec.extend_from_slice
  simp only [h, ↓reduceDIte]
  apply WP.spec_bind (List.clone_spec (l := s.val) (by intros; simp [liftFun1]))
  intro l' hl'
  simp [hl']

@[step]
theorem fors_sk_gen_spec (sk pk : Array U8 16#usize) (a : address.Adrs) (idx : U32) :
    fors.fors_sk_gen sk pk a idx ⦃ r =>
      bytes r.val = Spec.forsSkGen (bytes sk.val) (bytes pk.val) (adrsS a) idx.val ⦄ := by
  unfold fors.fors_sk_gen
  step*
  rw [r_post]
  simp [Spec.forsSkGen, Spec.PRF, adrsS, Spec.Adrs.setTypeAndClear, Spec.FORS_PRF, *]

theorem fors_node_spec_aux (sk pk : Array U8 16#usize) (a : address.Adrs) (n : Nat) :
    ∀ (i z : U32), z.val = n → (i.val + 1) * 2 ^ n ≤ 2 ^ 32 →
    fors.fors_node sk i z pk a ⦃ r =>
      bytes r.val = Spec.forsNode (bytes sk.val) i.val n (bytes pk.val) (adrsS a) ⦄ := by
  induction n with
  | zero =>
    intro i z hz h
    have hz0 : z = 0#u32 := by scalar_tac
    unfold fors.fors_node
    simp only [hz0, ↓reduceIte]
    step*
    rw [r_post]
    simp [Spec.forsNode, Spec.F, adrsS, *]
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
    step
    step
    step with ih i1 i2 (by scalar_tac) (by simp [*]; omega)
    step
    step with ih i3 i2 (by scalar_tac) (by simp [*]; omega)
    step*
    rw [r_post]
    simp [Spec.forsNode, adrsS, *]

@[step]
theorem fors_node_spec (sk : Array U8 16#usize) (i z : U32) (pk : Array U8 16#usize) (a : address.Adrs)
    (h : (i.val + 1) * 2 ^ z.val ≤ 2 ^ 32) :
    fors.fors_node sk i z pk a ⦃ r =>
      bytes r.val = Spec.forsNode (bytes sk.val) i.val z.val (bytes pk.val) (adrsS a) ⦄ :=
  fors_node_spec_aux sk pk a z.val i z rfl h

theorem fors_xor_one_le (x : Nat) : x ^^^ 1 ≤ x + 1 := by
  rcases Nat.even_or_odd x with h | h
  · rw [Nat.xor_one_of_even h]
  · rw [Nat.xor_one_of_odd h]; omega

theorem fors_inner_arith (i idx j : Nat) (hi : i < 14) (hidx : idx < 2 ^ 12) (hj : j < 12) :
    (i <<< (12 - j)) % 2 ^ 32 = i * 2 ^ (12 - j) ∧
    i * 2 ^ (12 - j) + ((idx / 2 ^ j) ^^^ 1) ≤ 2 ^ 32 - 1 ∧
    (i * 2 ^ (12 - j) + ((idx / 2 ^ j) ^^^ 1) + 1) * 2 ^ j ≤ 2 ^ 32 := by
  have h1 : 2 ^ (12 - j) ≤ 2 ^ 12 := Nat.pow_le_pow_right (by omega) (by omega)
  have h2 : 2 ^ j ≤ 2 ^ 11 := Nat.pow_le_pow_right (by omega) (by omega)
  have h3 : idx / 2 ^ j ≤ idx := Nat.div_le_self _ _
  have h4 := fors_xor_one_le (idx / 2 ^ j)
  have h5 : i * 2 ^ (12 - j) ≤ 13 * 2 ^ 12 := Nat.mul_le_mul (by omega) h1
  refine ⟨?_, by omega, ?_⟩
  · rw [Nat.shiftLeft_eq]; exact Nat.mod_eq_of_lt (by omega)
  · calc (i * 2 ^ (12 - j) + ((idx / 2 ^ j) ^^^ 1) + 1) * 2 ^ j
        ≤ (13 * 2 ^ 12 + 2 ^ 12 + 1) * 2 ^ 11 := Nat.mul_le_mul (by omega) h2
      _ ≤ 2 ^ 32 := by norm_num

/-- The `j`-th authentication-path node of FORS tree `i` (Algorithm 16, lines 6–8). -/
def forsAuth (sk pk : Spec.Bytes) (adrs : Spec.Adrs) (i idx j : Nat) : Spec.Bytes :=
  Spec.forsNode sk (i * 2 ^ (Spec.a - j) + ((idx / 2 ^ j) ^^^ 1)) j pk adrs

theorem fors_sign_inner_spec (sk pk : Array U8 16#usize) (a : address.Adrs)
    (sig : alloc.vec.Vec U8) (i idx j : U32) (S0 : Spec.Bytes) (L0 : Nat)
    (hi : i.val < 14) (hidx : idx.val < 2 ^ 12) (hj : j.val ≤ 12) (hL : L0 ≤ 100000)
    (hlen : sig.length = L0 + 16 * j.val)
    (hinv : bytes sig.val = S0 ++ (List.range j.val).flatMap
      (forsAuth (bytes sk.val) (bytes pk.val) (adrsS a) i.val idx.val)) :
    fors.fors_sign_loop0_loop0 sk pk a sig i idx j ⦃ r =>
      r.length = L0 + 16 * 12 ∧
      bytes r.val = S0 ++ (List.range 12).flatMap
        (forsAuth (bytes sk.val) (bytes pk.val) (adrsS a) i.val idx.val) ⦄ := by
  unfold fors.fors_sign_loop0_loop0
  apply loop.spec_decr_nat
    (measure := fun (p : alloc.vec.Vec U8 × U32) => 12 - p.2.val)
    (inv := fun p => p.2.val ≤ 12 ∧ p.1.length = L0 + 16 * p.2.val ∧
      bytes p.1.val = S0 ++ (List.range p.2.val).flatMap
        (forsAuth (bytes sk.val) (bytes pk.val) (adrsS a) i.val idx.val))
  · rintro ⟨sig, j⟩ ⟨hj, hlen, hinv⟩
    simp only [fors.fors_sign_loop0_loop0.body]
    simp only at hj hlen hinv
    by_cases hjA : j < params.A
    · simp only [hjA, ↓reduceIte]
      have hjlt : j.val < 12 := by scalar_tac
      obtain ⟨ha1, ha2, ha3⟩ := fors_inner_arith i.val idx.val j.val hi hidx hjlt
      step as ⟨i1, i1_post⟩
      step as ⟨s, s_post⟩
      step as ⟨i2, i2_post⟩
      step as ⟨i3, i3_post⟩
      have hs : s.val = (idx.val / 2 ^ j.val) ^^^ 1 := by
        rw [s_post, UScalar.val_xor, i1_post, Nat.shiftRight_eq_div_pow]; rfl
      have hi3 : i3.val = i.val * 2 ^ (12 - j.val) := by
        rw [i3_post, i2_post]; simpa [U32.size, U32.numBits] using ha1
      step as ⟨i4, i4_post⟩
      have hi4 : i4.val = i.val * 2 ^ (12 - j.val) + ((idx.val / 2 ^ j.val) ^^^ 1) := by
        rw [i4_post, hi3, hs]
      step as ⟨node, node_post⟩
      step*
      refine ⟨by scalar_tac, ?_, ?_, by scalar_tac⟩
      · have : sig1.length = sig.length + 16 := by
          simp [alloc.vec.Vec.length, sig1_post, s1_post]
        scalar_tac
      · rw [sig1_post, bytes_append, hinv, j1_post, List.range_succ, List.flatMap_append]
        simp [forsAuth, s1_post, node_post, hi4, Spec.a]
    · simp only [hjA, ↓reduceIte]
      have hj12 : j.val = 12 := by scalar_tac
      rw [hj12] at hlen hinv
      simp [hlen, hinv]
  · exact ⟨hj, hlen, hinv⟩

/-- The part of a FORS signature for tree `i`: the secret value and its authentication path. -/
def forsSignTree (sk pk : Spec.Bytes) (adrs : Spec.Adrs) (ind : List Nat) (i : Nat) : Spec.Bytes :=
  Spec.forsSkGen sk pk adrs (i * 2 ^ Spec.a + ind[i]!) ++
    (List.range Spec.a).flatMap (forsAuth sk pk adrs i ind[i]!)

theorem forsSign_eq (md sk pk : Spec.Bytes) (adrs : Spec.Adrs) :
    Spec.forsSign md sk pk adrs =
      (List.range 14).flatMap (forsSignTree sk pk adrs (Spec.base2b md 12 14)) := by
  rfl

theorem fors_flatMap_range_succ {β} (f : Nat → List β) (n : Nat) :
    (List.range (n + 1)).flatMap f = (List.range n).flatMap f ++ f n := by
  rw [List.range_succ, List.flatMap_append]; simp

theorem fors_nats_getElem! (l : List U32) (i : Nat) (h : i < l.length) :
    (nats l)[i]! = (l[i]'h).val := by
  simp [nats, h]

theorem fors_sign_loop_spec (sk pk : Array U8 16#usize) (a : address.Adrs)
    (indices : alloc.vec.Vec U32) (sig : alloc.vec.Vec U8) (i : U32)
    (hlenI : indices.length = 14) (hbd : ∀ d ∈ indices.val, d.val < 2 ^ 12)
    (hi : i.val ≤ 14) (hlen : sig.length = 208 * i.val)
    (hinv : bytes sig.val = (List.range i.val).flatMap
      (forsSignTree (bytes sk.val) (bytes pk.val) (adrsS a) (nats indices.val))) :
    fors.fors_sign_loop0 sk pk a indices sig i ⦃ r =>
      r.length = 2912 ∧
      bytes r.val = (List.range 14).flatMap
        (forsSignTree (bytes sk.val) (bytes pk.val) (adrsS a) (nats indices.val)) ⦄ := by
  unfold fors.fors_sign_loop0
  apply loop.spec_decr_nat
    (measure := fun (p : alloc.vec.Vec U8 × U32) => 14 - p.2.val)
    (inv := fun p => p.2.val ≤ 14 ∧ p.1.length = 208 * p.2.val ∧
      bytes p.1.val = (List.range p.2.val).flatMap
        (forsSignTree (bytes sk.val) (bytes pk.val) (adrsS a) (nats indices.val)))
  · rintro ⟨sig, i⟩ ⟨hi, hlen, hinv⟩
    simp only [fors.fors_sign_loop0.body]
    simp only at hi hlen hinv
    by_cases hiK : i < params.K
    · simp only [hiK, ↓reduceIte]
      have hilt : i.val < 14 := by scalar_tac
      step as ⟨i1, i1_post⟩
      step as ⟨idx, idx_post⟩
      have hi1 : i1.val = i.val := by rw [i1_post]; simp
      have hidx : idx.val < 2 ^ 12 := by rw [idx_post]; exact hbd _ (List.getElem_mem _)
      have hind : (nats indices.val)[i.val]! = idx.val := by
        rw [fors_nats_getElem! _ _ (by scalar_tac)]; simp [idx_post, hi1]
      step as ⟨i2, i2_post⟩
      have hi2 : i2.val = i.val * 2 ^ 12 := by
        rw [i2_post]; simp only [fors_A_eq, U32.size, U32.numBits]
        rw [Nat.shiftLeft_eq]; exact Nat.mod_eq_of_lt (by scalar_tac)
      step as ⟨i3, i3_post⟩
      step as ⟨sk1, sk1_post⟩
      step as ⟨s, s_post⟩
      step as ⟨sig1, sig1_post⟩
      have hl1 : sig1.length = sig.length + 16 := by
        simp [alloc.vec.Vec.length, sig1_post, s_post]
      step with fors_sign_inner_spec sk pk a sig1 i idx 0#u32 (bytes sig1.val) sig1.length hilt hidx
        (by simp) (by scalar_tac) (by simp) (by simp) as ⟨sig2, sig2_len, sig2_post⟩
      step*
      refine ⟨by scalar_tac, by scalar_tac, ?_, by scalar_tac⟩
      rw [sig2_post, sig1_post, bytes_append, hinv, i4_post, fors_flatMap_range_succ _ i.val]
      simp [forsSignTree, hind, s_post, sk1_post, i3_post, hi2, Spec.a]
    · simp only [hiK, ↓reduceIte]
      have hi14 : i.val = 14 := by scalar_tac
      rw [hi14] at hlen hinv
      simp [hlen, hinv]
  · exact ⟨hi, hlen, hinv⟩

@[step]
theorem fors_sign_spec (md : Slice U8) (sk pk : Array U8 16#usize) (a : address.Adrs) (hmd : md.length = 21) :
    fors.fors_sign md sk pk a ⦃ r =>
      bytes r.val = Spec.forsSign (bytes md.val) (bytes sk.val) (bytes pk.val) (adrsS a) ∧
      r.length = 2912 ⦄ := by
  unfold fors.fors_sign
  step as ⟨i, i_post⟩
  have hi : i.val = 14 := by rw [i_post]; simp
  step with base_2b_spec md params.A i (by simp) (by simp [hi, hmd]) as ⟨indices, hind, hlenI, hbd⟩
  simp only [fors_A_eq, hi] at hind hlenI hbd
  apply WP.spec_mono
  · exact fors_sign_loop_spec sk pk a indices (alloc.vec.Vec.new U8) 0#u32 (by simpa using hlenI)
      (by simpa using hbd) (by simp) (by simp) (by simp)
  · intro r ⟨h1, h2⟩
    refine ⟨?_, h1⟩
    rw [forsSign_eq, h2, hind]; rfl

/-- The root of FORS tree `i` recomputed from a signature (Algorithm 17, lines 3–20). -/
def forsRoot (sig pk : Spec.Bytes) (adrs : Spec.Adrs) (ind : List Nat) (i : Nat) : Spec.Bytes :=
  Spec.climb
    (Spec.F pk { adrs with word2 := 0, word3 := i * 2 ^ Spec.a + ind[i]! }
      (Spec.block sig (i * (Spec.a + 1))))
    ind[i]! (i * 2 ^ Spec.a + ind[i]!)
    ((sig.drop ((i * (Spec.a + 1) + 1) * Spec.n)).take (Spec.a * Spec.n)) Spec.a pk adrs

theorem forsPkFromSig_eq (sig md pk : Spec.Bytes) (adrs : Spec.Adrs) :
    Spec.forsPkFromSig sig md pk adrs =
      Spec.T pk { adrs.setTypeAndClear Spec.FORS_ROOTS with keypair := adrs.keypair }
        ((List.range 14).flatMap (forsRoot sig pk adrs (Spec.base2b md 12 14))) := by
  rfl

theorem fors_pk_from_sig_loop_spec (sig : Slice U8) (pk : Array U8 16#usize) (a : address.Adrs)
    (indices : alloc.vec.Vec U32) (roots : alloc.vec.Vec U8) (i : U32)
    (hs : sig.length = 2912)
    (hlenI : indices.length = 14) (hbd : ∀ d ∈ indices.val, d.val < 2 ^ 12)
    (hi : i.val ≤ 14) (hlen : roots.length = 16 * i.val)
    (hinv : bytes roots.val = (List.range i.val).flatMap
      (forsRoot (bytes sig.val) (bytes pk.val) (adrsS a) (nats indices.val))) :
    fors.fors_pk_from_sig_loop sig pk a indices roots i ⦃ r =>
      r.length = 224 ∧
      bytes r.val = (List.range 14).flatMap
        (forsRoot (bytes sig.val) (bytes pk.val) (adrsS a) (nats indices.val)) ⦄ := by
  unfold fors.fors_pk_from_sig_loop
  apply loop.spec_decr_nat
    (measure := fun (p : alloc.vec.Vec U8 × U32) => 14 - p.2.val)
    (inv := fun p => p.2.val ≤ 14 ∧ p.1.length = 16 * p.2.val ∧
      bytes p.1.val = (List.range p.2.val).flatMap
        (forsRoot (bytes sig.val) (bytes pk.val) (adrsS a) (nats indices.val)))
  · rintro ⟨roots, i⟩ ⟨hi, hlen, hinv⟩
    simp only [fors.fors_pk_from_sig_loop.body]
    simp only at hi hlen hinv
    by_cases hiK : i < params.K
    · simp only [hiK, ↓reduceIte]
      have hilt : i.val < 14 := by scalar_tac
      step as ⟨i1, i1_post⟩
      step as ⟨i2, i2_post⟩
      step as ⟨first, first_post⟩
      have hfirst : first.val = i.val * 13 := by rw [first_post]; simp [i2_post, i1_post]
      step as ⟨i3, i3_post⟩
      have hi3 : i3.val = i.val * 2 ^ 12 := by
        rw [i3_post]; simp only [fors_A_eq, U32.size, U32.numBits]
        rw [Nat.shiftLeft_eq]; exact Nat.mod_eq_of_lt (by scalar_tac)
      step as ⟨i4, i4_post⟩
      have hi4 : i4.val = i.val := by rw [i4_post]; simp
      step as ⟨i5, i5_post⟩
      have hidx : i5.val < 2 ^ 12 := by rw [i5_post]; exact hbd _ (List.getElem_mem _)
      have hind : (nats indices.val)[i.val]! = i5.val := by
        rw [fors_nats_getElem! _ _ (by scalar_tac)]; simp [i5_post, hi4]
      step as ⟨leaf, leaf_post⟩
      step as ⟨sk, sk_post, sk_post1⟩
      step as ⟨a0, a0_post⟩
      step as ⟨a1, a1_post⟩
      step as ⟨s, s_post⟩
      step as ⟨node, node_post⟩
      step as ⟨i6, i6_post⟩
      step with climb_spec node leaf sig i6 params.A pk a i.val i5.val (by scalar_tac) (by simp)
        (by simp [leaf_post, hi3]) (by simpa using hidx) as ⟨root, root_post⟩
      step*
      refine ⟨by scalar_tac, ?_, ?_, by scalar_tac⟩
      · have : roots1.length = roots.length + 16 := by
          simp [alloc.vec.Vec.length, roots1_post, s1_post]
        scalar_tac
      · rw [roots1_post, bytes_append, hinv, i7_post, fors_flatMap_range_succ _ i.val]
        simp [forsRoot, hind, s1_post, root_post, node_post, s_post, sk_post1, a1_post, a0_post,
          adrsS, leaf_post, hi3, i6_post, hfirst, Spec.a, Spec.n, Spec.F]
    · simp only [hiK, ↓reduceIte]
      have hi14 : i.val = 14 := by scalar_tac
      rw [hi14] at hlen hinv
      simp [hlen, hinv]
  · exact ⟨hi, hlen, hinv⟩

@[step]
theorem fors_pk_from_sig_spec (sig md : Slice U8) (pk : Array U8 16#usize) (a : address.Adrs)
    (hs : sig.length = 2912) (hmd : md.length = 21) :
    fors.fors_pk_from_sig sig md pk a ⦃ r =>
      bytes r.val = Spec.forsPkFromSig (bytes sig.val) (bytes md.val) (bytes pk.val) (adrsS a) ⦄ := by
  unfold fors.fors_pk_from_sig
  step as ⟨i, i_post⟩
  have hi : i.val = 14 := by rw [i_post]; simp
  step with base_2b_spec md params.A i (by simp) (by simp [hi, hmd]) as ⟨indices, hind, hlenI, hbd⟩
  simp only [fors_A_eq, hi] at hind hlenI hbd
  step with fors_pk_from_sig_loop_spec sig pk a indices (alloc.vec.Vec.new U8) 0#u32 hs
    (by simpa using hlenI) (by simpa using hbd) (by simp) (by simp) (by simp) as ⟨roots, hrl, hroots⟩
  step as ⟨a0, a0_post, a0_eq⟩
  step as ⟨a1, a1_post⟩
  step with thash_spec pk a1 roots.deref (by simp [alloc.vec.Vec.deref]; scalar_tac) as ⟨r, r_post⟩
  rw [r_post, forsPkFromSig_eq]
  have hd : roots.deref.val = roots.val := by simp [alloc.vec.Vec.deref]
  rw [hd, hroots, hind]
  simp [Spec.T, adrsS, a1_post, a0_eq, Spec.Adrs.setTypeAndClear, Spec.FORS_ROOTS]

end slhdsa
