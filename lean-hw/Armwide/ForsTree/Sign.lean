import Armwide.ForsTree.EntryProgram
open Aeneas Aeneas.Std Result
namespace slhdsa.ArmForsTree.Entry
open Armwide.Public.Dispatcher (Cpu)
open Armwide.Keygen (Features)
variable [cpu : Cpu] [features : Features]
attribute [local step] slhdsa.fors_extend_from_slice_spec

theorem fors_batch_spec {N : Usize} (p : params.Params) (hp : PN p N) (sk : Array U8 N) (i z : U32)
    (seed : hash.Seed N) (hs : SeedOk seed)
    (a : address.Adrs) (tree : (adrsS a).typ = Spec.FORS_TREE) (hz : z.val ≤ 7) (h : (i.val + 1) * 2 ^ z.val < 2 ^ 32) :
    fors.fors_batch sk i z seed a ⦃ r =>
      bytes r.val = Spec.forsNode (paramsS p) (bytes sk.val) i.val z.val (bytes seed.pk_seed.val)
        (adrsS a) ⦄ := by
  unfold fors.fors_batch
  rcases hp.nok with w|w|w <;> simp only [w,bind_ok,ite_true,sha256.arm_wide.available,
    Armwide.Public.Dispatcher.sha256.arm_wide.available] <;> cases cpu.wide
  all_goals first
    | exact AppleInternal.slhdsa.fors_batch_spec p hp sk i z seed hs a hz h
    | exact subtree_fips p hp seed hs features.sha512 sk i z a tree hz (by omega)

theorem fors_node_spec_aux {N : Usize} (p : params.Params) (hp : PN p N) (sk : Array U8 N)
    (seed : hash.Seed N) (hs : SeedOk seed) (a : address.Adrs) (tree : (adrsS a).typ = Spec.FORS_TREE) (n : Nat) :
    ∀ (i z : U32), z.val = n → (i.val + 1) * 2 ^ n < 2 ^ 32 →
    fors.fors_node sk i z seed a ⦃ r =>
      bytes r.val = Spec.forsNode (paramsS p) (bytes sk.val) i.val n (bytes seed.pk_seed.val)
        (adrsS a) ⦄ := by
  induction n with
  | zero =>
    intro i z hz h
    have hz7 : z ≤ fors.BATCH_HEIGHT := by simp only [global_simps]; scalar_tac
    unfold fors.fors_node
    simp only [hz7, ↓reduceIte]
    have := fors_batch_spec p hp sk i z seed hs a tree (by omega) (by rw [hz]; simpa using h)
    rw [hz] at this; exact this
  | succ n ih =>
    intro i z hz h
    unfold fors.fors_node
    by_cases hz7 : z ≤ fors.BATCH_HEIGHT
    · simp only [hz7, ↓reduceIte]
      have hz7' : z.val ≤ 7 := by simp only [global_simps] at hz7; scalar_tac
      have := fors_batch_spec p hp sk i z seed hs a tree hz7' (by rw [hz]; exact h)
      rw [hz] at this; exact this
    · simp only [hz7, ↓reduceIte]
      have hz0 : 1 ≤ z.val := by simp only [global_simps] at hz7; scalar_tac
      have hpos : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      have h1 : (2 * i.val + 1 + 1) * 2 ^ n < 2 ^ 32 := by
        have : (2 * i.val + 1 + 1) * 2 ^ n = (i.val + 1) * 2 ^ (n + 1) := by ring
        omega
      have h2 : (2 * i.val + 1) * 2 ^ n < 2 ^ 32 := by nlinarith
      have h3 : 2 * i.val + 2 ≤ 2 ^ 32 := by nlinarith
      step
      step
      step with ih i1 i2 (by scalar_tac) (by simp [*]; omega)
      step
      step with ih i3 i2 (by scalar_tac) (by simp [*]; omega)
      step
      step
      step with hash2_spec p hp as ⟨r, r_post⟩
      rw [r_post]
      simp [Spec.forsNode, adrsS, *]

@[step]
theorem fors_node_spec {N : Usize} (p : params.Params) (hp : PN p N) (sk : Array U8 N) (i z : U32)
    (seed : hash.Seed N) (hs : SeedOk seed) (a : address.Adrs) (tree : (adrsS a).typ = Spec.FORS_TREE)
    (h : (i.val + 1) * 2 ^ z.val < 2 ^ 32) :
    fors.fors_node sk i z seed a ⦃ r =>
      bytes r.val = Spec.forsNode (paramsS p) (bytes sk.val) i.val z.val (bytes seed.pk_seed.val)
        (adrsS a) ⦄ :=
  fors_node_spec_aux p hp sk seed hs a tree z.val i z rfl h

theorem fors_sign_inner_spec {N : Usize} (p : params.Params) (hp : PN p N) (sk : Array U8 N)
    (seed : hash.Seed N) (hseed : SeedOk seed) (a : address.Adrs) (tree : (adrsS a).typ = Spec.FORS_TREE)
    (sig : alloc.vec.Vec U8) (i idx j : U32) (S0 : Spec.Bytes) (L0 : Nat)
    (hi : i.val < p.k.val) (hidx : idx.val < 2 ^ p.a.val) (hj : j.val ≤ p.a.val)
    (hL : L0 ≤ 100000) (hlen : sig.length = L0 + j.val * N.val)
    (hinv : bytes sig.val = S0 ++ (List.range j.val).flatMap
      (forsAuth (paramsS p) (bytes sk.val) (bytes seed.pk_seed.val) (adrsS a) i.val idx.val)) :
    fors.fors_sign_loop0_loop0 sk seed a p.a sig i idx j ⦃ r =>
      r.length = L0 + p.a.val * N.val ∧
      bytes r.val = S0 ++ (List.range p.a.val).flatMap
        (forsAuth (paramsS p) (bytes sk.val) (bytes seed.pk_seed.val) (adrsS a) i.val idx.val) ⦄ := by
  have hn : N.val ≤ 32 := hp.le32
  have hv := hp.valid
  have ha14 : p.a.val ≤ 14 := hv.a_le
  have hk35 : p.k.val ≤ 35 := hv.k_le
  unfold fors.fors_sign_loop0_loop0
  apply loop.spec_decr_nat
    (measure := fun (q : alloc.vec.Vec U8 × U32) => p.a.val - q.2.val)
    (inv := fun q => q.2.val ≤ p.a.val ∧ q.1.length = L0 + q.2.val * N.val ∧
      bytes q.1.val = S0 ++ (List.range q.2.val).flatMap
        (forsAuth (paramsS p) (bytes sk.val) (bytes seed.pk_seed.val) (adrsS a) i.val idx.val))
  · rintro ⟨sig, j⟩ ⟨hj, hlen, hinv⟩
    simp only [fors.fors_sign_loop0_loop0.body]
    simp only at hj hlen hinv
    by_cases hjA : j < p.a
    · simp only [hjA, ↓reduceIte]
      have hjlt : j.val < p.a.val := by scalar_tac
      have hjn : j.val * N.val ≤ 14 * 32 := Nat.mul_le_mul (by omega) hn
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
      step with fors_node_spec p hp sk i4 j seed hseed a tree (by rw [hi4]; exact ha3)
        as ⟨node, node_post⟩
      step as ⟨s1, s1_post⟩
      step as ⟨sig1, sig1_post, sig1_len⟩
      step as ⟨j1, j1_post⟩
      refine ⟨by scalar_tac, ?_, ?_, by scalar_tac⟩
      · rw [sig1_len, hlen, s1_post, j1_post, Nat.add_mul]; simp; omega
      · rw [sig1_post, bytes_append, hinv, j1_post, fors_flatMap_range_succ _ j.val]
        simp [forsAuth, node_post, hi4, s1_post]
    · simp only [hjA, ↓reduceIte]
      have hjeq : j.val = p.a.val := by scalar_tac
      rw [hjeq] at hlen hinv
      simp [hlen, hinv]
  · exact ⟨hj, hlen, hinv⟩

theorem fors_sign_loop_spec {N : Usize} (p : params.Params) (hp : PN p N) (sk : Array U8 N)
    (seed : hash.Seed N) (hs : SeedOk seed) (a : address.Adrs) (tree : (adrsS a).typ = Spec.FORS_TREE)
    (indices : alloc.vec.Vec U32) (sig : alloc.vec.Vec U8) (i : U32)
    (hlenI : indices.length = p.k.val) (hbd : ∀ d ∈ indices.val, d.val < 2 ^ p.a.val)
    (hi : i.val ≤ p.k.val) (hlen : sig.length = i.val * (1 + p.a.val) * N.val)
    (hinv : bytes sig.val = (List.range i.val).flatMap
      (forsSignTree (paramsS p) (bytes sk.val) (bytes seed.pk_seed.val) (adrsS a) (nats indices.val))) :
    fors.fors_sign_loop0 p.k sk seed a p.a indices sig i ⦃ r =>
      r.length = p.k.val * (1 + p.a.val) * N.val ∧
      bytes r.val = (List.range p.k.val).flatMap
        (forsSignTree (paramsS p) (bytes sk.val) (bytes seed.pk_seed.val) (adrsS a) (nats indices.val)) ⦄ := by
  have hn : N.val ≤ 32 := hp.le32
  have hv := hp.valid
  have ha14 : p.a.val ≤ 14 := hv.a_le
  have hk35 : p.k.val ≤ 35 := hv.k_le
  unfold fors.fors_sign_loop0
  apply loop.spec_decr_nat
    (measure := fun (q : alloc.vec.Vec U8 × U32) => p.k.val - q.2.val)
    (inv := fun q => q.2.val ≤ p.k.val ∧ q.1.length = q.2.val * (1 + p.a.val) * N.val ∧
      bytes q.1.val = (List.range q.2.val).flatMap
        (forsSignTree (paramsS p) (bytes sk.val) (bytes seed.pk_seed.val) (adrsS a) (nats indices.val)))
  · rintro ⟨sig, i⟩ ⟨hi, hlen, hinv⟩
    simp only [fors.fors_sign_loop0.body]
    simp only at hi hlen hinv
    by_cases hiK : i < p.k
    · simp only [hiK, ↓reduceIte]
      have hilt : i.val < p.k.val := by scalar_tac
      have hbound : i.val * (1 + p.a.val) * N.val ≤ 35 * 15 * 32 :=
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
      step with fors_sk_gen_spec p hp sk seed hs a i3 as ⟨sk1, sk1_post⟩
      step as ⟨s, s_post⟩
      step as ⟨sig1, sig1_post, sig1_len⟩
      have hl1 : sig1.length = sig.length + N.val := by
        rw [sig1_len]; simp [s_post]
      step with fors_sign_inner_spec p hp sk seed hs a tree sig1 i idx 0#u32 (bytes sig1.val) sig1.length
        hilt hidx (by simp) (by omega) (by simp) (by simp)
        as ⟨sig2, sig2_len, sig2_post⟩
      step as ⟨i4, i4_post⟩
      refine ⟨by scalar_tac, ?_, ?_, by scalar_tac⟩
      · rw [sig2_len, hl1, hlen, i4_post]; ring
      · rw [sig2_post, sig1_post, bytes_append, hinv, i4_post, fors_flatMap_range_succ _ i.val]
        simp [forsSignTree, hind, sk1_post, i3_post, hi2, s_post]
    · simp only [hiK, ↓reduceIte]
      have hieq : i.val = p.k.val := by scalar_tac
      rw [hieq] at hlen hinv
      simp [hlen, hinv]
  · exact ⟨hi, hlen, hinv⟩

@[step]
theorem fors_sign_spec {N : Usize} (p : params.Params) (hp : PN p N) (md : Slice U8)
    (sk : Array U8 N) (seed : hash.Seed N) (hs : SeedOk seed) (a : address.Adrs) (tree : (adrsS a).typ = Spec.FORS_TREE)
    (hmd : md.length = (p.k.val * p.a.val + 7) / 8) :
    fors.fors_sign p md sk seed a ⦃ r =>
      bytes r.val = Spec.forsSign (paramsS p) (bytes md.val) (bytes sk.val) (bytes seed.pk_seed.val)
        (adrsS a) ∧
      r.length = p.k.val * (1 + p.a.val) * N.val ⦄ := by
  have hv := hp.valid
  have ha1 : 1 ≤ p.a.val := hv.a_pos
  have ha14 : p.a.val ≤ 14 := hv.a_le
  unfold fors.fors_sign
  step as ⟨i, i_post⟩
  have hi : i.val = p.k.val := by rw [i_post]; simp
  step with base_2b_spec md p.a i (by omega) (by rw [hi, hmd]; omega)
    as ⟨indices, hind, hlenI, hbd⟩
  rw [hi] at hind hlenI
  apply WP.spec_mono
  · exact fors_sign_loop_spec p hp sk seed hs a tree indices (alloc.vec.Vec.new U8) 0#u32
      (by simpa using hlenI) hbd (by simp) (by simp) (by simp)
  · intro r ⟨h1, h2⟩
    refine ⟨?_, h1⟩
    rw [forsSign_eq, h2, hind]; rfl

end slhdsa.ArmForsTree.Entry
