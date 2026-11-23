import Slhdsa.Proofs.Fors
import Slhdsa.Proofs.ShakeXmss

open Aeneas Aeneas.Std Result
namespace slhdsa.Shake
attribute [local step] fors_extend_from_slice_spec
attribute [local simp] fors_FORS_PRF_eq fors_FORS_ROOTS_eq

@[step]
theorem fors_sk_gen_spec {N : Usize} (p : _root_.slhdsa.params.Params) (hp : PN p N) (sk : Array U8 N)
    (seed : Array U8 N) (a : address.Adrs) (idx : U32) :
    shake.fors.fors_sk_gen sk seed a idx ⦃ r =>
      bytes r.val = Spec.forsSkGen (params p) (bytes sk.val) (bytes seed.val) (adrsS a)
        idx.val ⦄ := by
  unfold shake.fors.fors_sk_gen
  have hN32 := hp.le32
  let* ⟨ a1, a1_post, a1_post1 ⟩ ← with_type_spec
  let* ⟨ a2, a2_post ⟩ ← with_keypair_spec
  let* ⟨ a3, a3_post ⟩ ← with_word3_spec
  let* ⟨r, hr⟩ ← thash_spec
  simpa only [Spec.forsSkGen, Spec.PRF, params, hp.n_eq, paramsS_n, a3_post, a2_post, a1_post1,
    adrsS, Spec.Adrs.setTypeAndClear, Spec.FORS_PRF, fors_FORS_PRF_eq, show (6#u32).val = 6 by decide, show (0#u32).val = 0 by decide] using hr

theorem fors_node_spec_aux {N : Usize} (p : _root_.slhdsa.params.Params) (hp : PN p N) (sk : Array U8 N)
    (seed : Array U8 N) (a : address.Adrs) (n : Nat) :
    ∀ (i z : U32), z.val = n → (i.val + 1) * 2 ^ n < 2 ^ 32 →
    shake.fors.fors_node sk i z seed a ⦃ r =>
      bytes r.val = Spec.forsNode (params p) (bytes sk.val) i.val n (bytes seed.val)
        (adrsS a) ⦄ := by
  induction n with
  | zero =>
    intro i z hz h
    have hz0 : z = 0#u32 := by scalar_tac
    unfold shake.fors.fors_node
    step as ⟨addr, ha⟩
    step as ⟨addr1, ha1⟩
    simp only [hz0, ↓reduceIte]
    let* ⟨v, hv⟩ ← fors_sk_gen_spec p hp
    let* ⟨r, hr⟩ ← thash_spec
    simpa only [Spec.forsNode, Spec.F, params, paramsS_n, hp.n_eq, ha, ha1, hz0, adrsS, hv, show (0#u32).val = 0 by decide] using hr
  | succ n ih =>
    intro i z hz h
    have nz : z ≠ 0#u32 := by scalar_tac
    unfold shake.fors.fors_node
    step as ⟨addr, ha⟩
    step as ⟨addr1, ha1⟩
    simp only [nz, ↓reduceIte]
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
    step with pair_spec as ⟨r, hr⟩
    simpa only [Spec.forsNode, Spec.H, params, hp.n_eq, paramsS_n, adrsS, ha1, ha, hz, *] using hr

@[step]
theorem fors_node_spec {N : Usize} (p : _root_.slhdsa.params.Params) (hp : PN p N) (sk : Array U8 N) (i z : U32)
    (seed : Array U8 N) (a : address.Adrs)
    (h : (i.val + 1) * 2 ^ z.val < 2 ^ 32) :
    shake.fors.fors_node sk i z seed a ⦃ r =>
      bytes r.val = Spec.forsNode (params p) (bytes sk.val) i.val z.val (bytes seed.val)
        (adrsS a) ⦄ :=
  fors_node_spec_aux p hp sk seed a z.val i z rfl h

theorem fors_sign_inner_spec {N : Usize} (p : _root_.slhdsa.params.Params) (hp : PN p N) (sk : Array U8 N)
    (seed : Array U8 N) (a : address.Adrs)
    (sig : alloc.vec.Vec U8) (i idx j : U32) (S0 : Spec.Bytes) (L0 : Nat)
    (hi : i.val < p.k.val) (hidx : idx.val < 2 ^ p.a.val) (hj : j.val ≤ p.a.val)
    (hL : L0 ≤ 100000) (hlen : sig.length = L0 + j.val * N.val)
    (hinv : bytes sig.val = S0 ++ (List.range j.val).flatMap
      (forsAuth (params p) (bytes sk.val) (bytes seed.val) (adrsS a) i.val idx.val)) :
    shake.fors.fors_sign_loop0_loop0 sk seed a p.a sig i idx j ⦃ r =>
      r.length = L0 + p.a.val * N.val ∧
      bytes r.val = S0 ++ (List.range p.a.val).flatMap
        (forsAuth (params p) (bytes sk.val) (bytes seed.val) (adrsS a) i.val idx.val) ⦄ := by
  have hn : N.val ≤ 32 := hp.le32
  have hv := hp.valid
  have ha14 : p.a.val ≤ 14 := hv.a_le
  have hk35 : p.k.val ≤ 35 := hv.k_le
  unfold shake.fors.fors_sign_loop0_loop0
  apply loop.spec_decr_nat
    (measure := fun (q : alloc.vec.Vec U8 × U32) => p.a.val - q.2.val)
    (inv := fun q => q.2.val ≤ p.a.val ∧ q.1.length = L0 + q.2.val * N.val ∧
      bytes q.1.val = S0 ++ (List.range q.2.val).flatMap
        (forsAuth (params p) (bytes sk.val) (bytes seed.val) (adrsS a) i.val idx.val))
  · rintro ⟨sig, j⟩ ⟨hj, hlen, hinv⟩
    simp only [shake.fors.fors_sign_loop0_loop0.body]
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
      step with fors_node_spec p hp sk i4 j seed a (by rw [hi4]; exact ha3)
        as ⟨node, node_post⟩
      step as ⟨s1, s1_post⟩
      step as ⟨sig1, sig1_post, sig1_len⟩
      step as ⟨j1, j1_post⟩
      refine ⟨by scalar_tac, ?_, ?_, by scalar_tac⟩
      · rw [sig1_len, hlen, s1_post, j1_post, Nat.add_mul]; simp; omega
      · rw [sig1_post, bytes_append, hinv, j1_post, fors_flatMap_range_succ _ j.val]
        simp [show (params p).a = p.a.val from rfl, forsAuth, node_post, hi4, s1_post]
    · simp only [hjA, ↓reduceIte]
      have hjeq : j.val = p.a.val := by scalar_tac
      rw [hjeq] at hlen hinv
      simp [hlen, hinv]
  · exact ⟨hj, hlen, hinv⟩

/-- The part of a FORS signature for tree `i`: the secret value and its authentication path. -/
theorem fors_sign_loop_spec {N : Usize} (p : _root_.slhdsa.params.Params) (hp : PN p N) (sk : Array U8 N)
    (seed : Array U8 N) (a : address.Adrs)
    (indices : alloc.vec.Vec U32) (sig : alloc.vec.Vec U8) (i : U32)
    (hlenI : indices.length = p.k.val) (hbd : ∀ d ∈ indices.val, d.val < 2 ^ p.a.val)
    (hi : i.val ≤ p.k.val) (hlen : sig.length = i.val * (1 + p.a.val) * N.val)
    (hinv : bytes sig.val = (List.range i.val).flatMap
      (forsSignTree (params p) (bytes sk.val) (bytes seed.val) (adrsS a) (nats indices.val))) :
    shake.fors.fors_sign_loop0 p.k sk seed a p.a indices sig i ⦃ r =>
      r.length = p.k.val * (1 + p.a.val) * N.val ∧
      bytes r.val = (List.range p.k.val).flatMap
        (forsSignTree (params p) (bytes sk.val) (bytes seed.val) (adrsS a) (nats indices.val)) ⦄ := by
  have hn : N.val ≤ 32 := hp.le32
  have hv := hp.valid
  have ha14 : p.a.val ≤ 14 := hv.a_le
  have hk35 : p.k.val ≤ 35 := hv.k_le
  unfold shake.fors.fors_sign_loop0
  apply loop.spec_decr_nat
    (measure := fun (q : alloc.vec.Vec U8 × U32) => p.k.val - q.2.val)
    (inv := fun q => q.2.val ≤ p.k.val ∧ q.1.length = q.2.val * (1 + p.a.val) * N.val ∧
      bytes q.1.val = (List.range q.2.val).flatMap
        (forsSignTree (params p) (bytes sk.val) (bytes seed.val) (adrsS a) (nats indices.val)))
  · rintro ⟨sig, i⟩ ⟨hi, hlen, hinv⟩
    simp only [shake.fors.fors_sign_loop0.body]
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
      step with fors_sk_gen_spec p hp sk seed a i3 as ⟨sk1, sk1_post⟩
      step as ⟨s, s_post⟩
      step as ⟨sig1, sig1_post, sig1_len⟩
      have hl1 : sig1.length = sig.length + N.val := by
        rw [sig1_len]; simp [s_post]
      step with fors_sign_inner_spec p hp sk seed a sig1 i idx 0#u32 (bytes sig1.val) sig1.length
        hilt hidx (by simp) (by omega) (by simp) (by simp)
        as ⟨sig2, sig2_len, sig2_post⟩
      step as ⟨i4, i4_post⟩
      refine ⟨by scalar_tac, ?_, ?_, by scalar_tac⟩
      · rw [sig2_len, hl1, hlen, i4_post]; ring
      · rw [sig2_post, sig1_post, bytes_append, hinv, i4_post, fors_flatMap_range_succ _ i.val]
        simp [show (params p).a = p.a.val from rfl, forsSignTree, hind, sk1_post, i3_post, hi2, s_post]
    · simp only [hiK, ↓reduceIte]
      have hieq : i.val = p.k.val := by scalar_tac
      rw [hieq] at hlen hinv
      simp [hlen, hinv]
  · exact ⟨hi, hlen, hinv⟩

@[step]
theorem fors_sign_spec {N : Usize} (p : _root_.slhdsa.params.Params) (hp : PN p N) (md : Slice U8)
    (sk : Array U8 N) (seed : Array U8 N) (a : address.Adrs)
    (hmd : md.length = (p.k.val * p.a.val + 7) / 8) :
    shake.fors.fors_sign p md sk seed a ⦃ r =>
      bytes r.val = Spec.forsSign (params p) (bytes md.val) (bytes sk.val) (bytes seed.val)
        (adrsS a) ∧
      r.length = p.k.val * (1 + p.a.val) * N.val ⦄ := by
  have hv := hp.valid
  have ha1 : 1 ≤ p.a.val := hv.a_pos
  have ha14 : p.a.val ≤ 14 := hv.a_le
  unfold shake.fors.fors_sign
  step as ⟨i, i_post⟩
  have hi : i.val = p.k.val := by rw [i_post]; simp
  step with base_2b_spec md p.a i (by omega) (by rw [hi, hmd]; omega)
    as ⟨indices, hind, hlenI, hbd⟩
  rw [hi] at hind hlenI
  apply WP.spec_mono
  · exact fors_sign_loop_spec p hp sk seed a indices (alloc.vec.Vec.new U8) 0#u32
      (by simpa using hlenI) hbd (by simp) (by simp) (by simp)
  · intro r ⟨h1, h2⟩
    refine ⟨?_, h1⟩
    rw [forsSign_eq, h2, hind]; rfl


@[step] theorem fors_pk_from_sig_spec {N : Usize} (p : _root_.slhdsa.params.Params) (hp : PN p N)
    (sig md : Slice U8) (seed : Array U8 N) (adrs : address.Adrs)
    (hsig : sig.length = p.k.val * (1 + p.a.val) * N.val) (hmd : md.length = (p.k.val*p.a.val+7)/8) :
    shake.fors.fors_pk_from_sig p sig md seed adrs ⦃ out => bytes out.val =
      Spec.forsPkFromSig (params p) (bytes sig.val) (bytes md.val) (bytes seed.val) (adrsS adrs) ⦄ := by
  have ha14 : p.a.val ≤ 14 := hp.valid.a_le
  have hapos : 1 ≤ p.a.val := hp.valid.a_pos
  have hk35 : p.k.val ≤ 35 := hp.valid.k_le
  unfold shake.fors.fors_pk_from_sig
  step as ⟨k, hk⟩
  have heq : k.val = p.k.val := by simp [hk]
  let* ⟨indices, hind, hlen, hbd⟩ ← base_2b_spec md p.a k (by omega) (by rw [heq, hmd]; omega)
  rw [heq] at hind hlen
  let* ⟨a, _, ha⟩ ← with_type_spec
  let* ⟨a1, ha1⟩ ← with_keypair_spec
  let* ⟨s, hs⟩ ← start_spec
  let x := bytes seed.val ++ (adrsS a1).bytes
  let f := forsRoot (params p) (bytes sig.val) (bytes seed.val) (adrsS adrs) (nats indices.val)
  have body : shake.fors.fors_pk_from_sig_loop p.a sig seed adrs.layer adrs.tree adrs.typ adrs.keypair
      adrs.word2 adrs.word3 indices s 0#usize ⦃ out => Absorbed out (x ++ (List.range p.k.val).flatMap f) ⦄ := by
    unfold shake.fors.fors_pk_from_sig_loop
    apply loop.spec_decr_nat (measure := fun (r : shake256.Sponge × Usize) => p.k.val-r.2.val)
      (inv := fun r => r.2.val ≤ p.k.val ∧ Absorbed r.1 (x ++ (List.range r.2.val).flatMap f))
    · rintro ⟨s,i⟩ ⟨hi, inv⟩
      simp only at hi inv
      simp only [shake.fors.fors_pk_from_sig_loop.body]
      spec_split
      · have hlt : i.val < indices.val.length := by scalar_tac
        have hltK : i.val < p.k.val := by scalar_tac
        have hcast : (UScalar.cast .U32 i).val = i.val := by
          simp [UScalar.cast_val_eq, Nat.mod_eq_of_lt (show i.val < 4294967296 by omega)]
        have hspan : (i.val*(1+p.a.val)+1+p.a.val)*N.val ≤ sig.length := by
          rw [hsig]
          apply Nat.mul_le_mul_right
          have h := Nat.mul_le_mul_right (1+p.a.val) (show i.val+1 ≤ p.k.val by omega)
          rw [Nat.add_mul, Nat.one_mul] at h
          omega
        obtain ⟨hshift, hbound⟩ := fors_shl_arith p.a.val i.val ha14 (by omega)
        step as ⟨width, hw⟩
        step as ⟨stride, hstride⟩
        have hsval : stride.val = 1+p.a.val := by simp [hstride, hw]
        have hmul := Nat.mul_le_mul (show i.val ≤ 35 by omega) (show stride.val ≤ 15 by omega)
        step as ⟨off, hoff⟩
        have hOff : off.val = i.val*(1+p.a.val) := by simp [hoff, hstride, hw]
        step as ⟨u, hu⟩
        step as ⟨base, hbase⟩
        have hBase : base.val = i.val*2^p.a.val := by
          rw [hbase, hu, hcast]; simpa [U32.size, U32.numBits] using hshift
        let* ⟨digit, hidx⟩ ← alloc.vec.Vec.index_usize_spec
        have hDigit : digit.val < 2^p.a.val := by rw [hidx]; exact hbd _ (List.getElem_mem _)
        have hNat : (nats indices.val)[i.val]! = digit.val := by
          rw [fors_nats_getElem! _ _ hlt, hidx]
        step as ⟨idx, hleaf⟩
        step as ⟨ad, had⟩
        step as ⟨ad1, had1⟩
        let* ⟨v, hv⟩ ← block_spec N sig off (by rw [hOff]; exact le_trans (Nat.mul_le_mul_right _ (by omega)) hspan)
        let* ⟨val, hval⟩ ← thash_spec
        step as ⟨first, hfirst⟩
        let* ⟨root, hroot⟩ ← climb_spec p hp val idx sig first p.a seed adrs i.val digit.val
          (by simpa [hfirst, hOff] using hspan) (by omega) (by rw [hleaf, hBase]) hDigit
        simp only [lift, bind_ok]
        let* ⟨s', hs'⟩ ← append_spec s _ inv
        step as ⟨next, hnext⟩
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        rw [hnext, List.range_succ, List.flatMap_append]
        simpa only [x, f, forsRoot, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc,
          Array.val_to_slice, hroot, hval, hv, hfirst, hOff, hleaf, hBase, hNat, had1, had, adrsS,
          Spec.F, Spec.block, show (0#u32).val = 0 by decide, params, paramsS_n, hp.n_eq, paramsS_a, bytes_take, bytes_drop, Nat.add_comm 1 p.a.val] using hs'
      · simp only [step_simps]
        have doneAt : i.val = p.k.val := by scalar_tac
        simpa only [doneAt] using inv
    · exact ⟨by simp, by simpa [x] using hs⟩
  let* ⟨s', hs'⟩ ← body
  have hpk : adrsS a1 = { (adrsS adrs).setTypeAndClear Spec.FORS_ROOTS with keypair := (adrsS adrs).keypair } := by
    simp [ha1, ha, adrsS, Spec.Adrs.setTypeAndClear, Spec.FORS_ROOTS]
  rw [forsPkFromSig_eq]
  change shake.hash.digest N s' ⦃ out => bytes out.val = Spec.shake256 ((bytes seed.val ++ _) ++
    (List.range p.k.val).flatMap (forsRoot (params p) _ _ _ (Spec.base2b (bytes md.val) p.a.val p.k.val))) (params p).n ⦄
  rw [← hind, ← hpk, show (params p).n = N.val from hp.n]
  exact digest_spec N s' _ hs'

end slhdsa.Shake

#print axioms slhdsa.Shake.fors_sign_spec
#print axioms slhdsa.Shake.fors_pk_from_sig_spec
