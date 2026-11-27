import Shakebatch.WidthThreeProgram
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.WidthThree
open slhdsa.Shake
set_option linter.concreteInstances false
variable [w : Wots]

abbrev Domain (a : address.Adrs) : Prop :=
  a.typ = address.WOTS_HASH ∧ a.word2 = 0#u32 ∧ a.word3 = 0#u32

/-- Certificates for the production WOTS entry points used at each leaf. -/
class KeyCorrect (w : Wots) : Prop where
  key {N : Usize} (p : slhdsa.params.Params) (hp : PN p N) (sk seed : Array U8 N) (a : address.Adrs) (domain : Domain a) :
    w.keygen sk seed a ⦃ out => bytes out.val = Spec.wotsPkGen (params p) (bytes sk.val) (bytes seed.val) (adrsS a) ⦄
class WotsCorrect (w : Wots) extends KeyCorrect w : Prop where
  sign {N : Usize} (p : slhdsa.params.Params) (hp : PN p N) (m sk seed : Array U8 N) (a : address.Adrs) (domain : Domain a) :
    (do let digits ← wots.wots_digits m; w.sign sk seed a digits.deref) ⦃ out =>
      bytes out.val = Spec.wotsSign (params p) (bytes m.val) (bytes sk.val) (bytes seed.val) (adrsS a) ∧
      out.length = N.val*(2*N.val+3) ⦄

private theorem key_scalar [ck : KeyCorrect w] {N : Usize} (p : slhdsa.params.Params) (hp : PN p N)
    (sk seed : Array U8 N) (a : address.Adrs) (h : Domain a) :
    w.keygen sk seed a = slhdsa.shake.wots.wots_pk_gen sk seed a := by
  obtain ⟨x,hx,px⟩ := spec_imp_exists (ck.key p hp sk seed a h)
  obtain ⟨y,hy,py⟩ := spec_imp_exists (Shake.wots_pk_gen_spec p hp sk seed a)
  rw [hx,hy,ok.injEq]
  exact Aeneas.Std.Array.ext _ _ ((bytes_inj _ _).mp (px.trans py.symm))

private theorem sign_scalar [cw : WotsCorrect w] {N : Usize} (p : slhdsa.params.Params) (hp : PN p N)
    (m sk seed : Array U8 N) (a : address.Adrs) (h : Domain a) :
    (do let digits ← wots.wots_digits m; w.sign sk seed a digits.deref) = slhdsa.shake.wots.wots_sign m sk seed a := by
  obtain ⟨x,hx,px,_⟩ := spec_imp_exists (cw.sign p hp m sk seed a h)
  obtain ⟨y,hy,py,_⟩ := spec_imp_exists (Shake.wots_sign_spec p hp m sk seed a)
  rw [hx,hy,ok.injEq]
  exact alloc.vec.Vec.ext _ _ ((bytes_inj _ _).mp (px.trans py.symm))

private theorem public_key_eq [ck : KeyCorrect w] {N : Usize} (p : slhdsa.params.Params) (hp : PN p N)
    (sk seed : Array U8 N) (a : address.Adrs) (domain : Domain a) :
    shake.wots.wots_pk_gen sk seed a = slhdsa.shake.wots.wots_pk_gen sk seed a := by
  simpa only [shake.wots.wots_pk_gen,shake.batch.available,ShakeBatch.available_for_fips _ p hp,
    KldispRust.shake256.parallel.available,bind_ok,ite_true] using key_scalar p hp sk seed a domain

private theorem public_sign_eq [cw : WotsCorrect w] {N : Usize} (p : slhdsa.params.Params) (hp : PN p N)
    (m sk seed : Array U8 N) (a : address.Adrs) (domain : Domain a) :
    shake.wots.wots_sign m sk seed a = slhdsa.shake.wots.wots_sign m sk seed a := by
  simpa only [shake.wots.wots_sign,shake.batch.available,ShakeBatch.available_for_fips _ p hp,
    KldispRust.shake256.parallel.available,bind_ok,ite_true] using sign_scalar p hp m sk seed a domain

private theorem xmss_node_aux [ck : KeyCorrect w] {N : Usize} (p : _root_.slhdsa.params.Params) (hp : PN p N) (sk : Array U8 N)
    (seed : Array U8 N) (a : address.Adrs) (n : Nat) :
    ∀ (i z : U32), z.val = n → (i.val + 1) * 2 ^ n ≤ 2 ^ 32 →
    shake.batch.xmss_subtree_fallback sk seed i z a ⦃ r =>
      bytes r.val = Spec.xmssNode (params p) (bytes sk.val) i.val n (bytes seed.val)
        (adrsS a) ⦄ := by
  induction n with
  | zero =>
    intro i z hz h
    unfold shake.batch.xmss_subtree_fallback
    have hz0 : z = 0#u32 := by scalar_tac
    simp only [hz0, ↓reduceIte]
    let* ⟨ a1, a1_post, a1_post1 ⟩ ← with_type_spec
    let* ⟨ a2, a2_post ⟩ ← with_keypair_spec
    rw [show shake.batch.keygen sk seed a2 = _ from key_scalar p hp sk seed a2 (by simp [Domain,a2_post,a1_post1])]
    let* ⟨ r, r_post ⟩ ← Shake.wots_pk_gen_spec p hp
    rw [r_post]
    simp [a2_post, a1_post1, Spec.xmssNode, adrsS, Spec.Adrs.setTypeAndClear, Spec.WOTS_HASH,
      address.WOTS_HASH]
  | succ n ih =>
    intro i z hz h
    unfold shake.batch.xmss_subtree_fallback
    have hz0 : ¬ z = 0#u32 := by scalar_tac
    simp only [hz0, ↓reduceIte]
    have hpos : 0 < 2 ^ n := Nat.pow_pos (by decide)
    have he : (2 * i.val + 2) * 2 ^ n = (i.val + 1) * 2 ^ (n + 1) := by ring
    have h1 : (2 * i.val + 1 + 1) * 2 ^ n ≤ 2 ^ 32 := by rw [← he] at h; exact h
    have h0 : (2 * i.val + 1) * 2 ^ n ≤ 2 ^ 32 :=
      le_trans (Nat.mul_le_mul_right _ (by omega)) h1
    have hb : 2 * i.val + 2 ≤ 2 ^ 32 := le_trans (Nat.le_mul_of_pos_right _ hpos) h1
    let* ⟨ i1, i1_post ⟩ ← U32.mul_spec
    let* ⟨ i2, i2_post ⟩ ← U32.sub_spec
    let* ⟨ lnode, lnode_post ⟩ ← ih
    let* ⟨ i3, i3_post ⟩ ← U32.add_spec
    let* ⟨ rnode, rnode_post ⟩ ← ih
    let* ⟨ a1, a1_post, a1_post1 ⟩ ← with_type_spec
    let* ⟨ a2, a2_post ⟩ ← with_word2_spec
    let* ⟨ a3, a3_post ⟩ ← with_word3_spec
    change slhdsa.shake.xmss.hash2 _ _ _ _ ⦃ _ ⦄
    let* ⟨ r, r_post ⟩ ← Shake.hash2_spec p hp
    rw [r_post]
    simp [lnode_post, rnode_post, i1_post, i3_post, a3_post, a2_post, a1_post1, hz,
      Spec.xmssNode, adrsS, Spec.Adrs.setTypeAndClear, Spec.TREE, address.TREE]

@[step]
theorem subtree_spec [ck : KeyCorrect w] {N : Usize} (p : _root_.slhdsa.params.Params) (hp : PN p N) (sk : Array U8 N) (i z : U32)
    (seed : Array U8 N) (a : address.Adrs) (h : (i.val + 1) * 2 ^ z.val ≤ 2 ^ 32) :
    shake.batch.xmss_subtree_fallback sk seed i z a ⦃ r =>
      bytes r.val = Spec.xmssNode (params p) (bytes sk.val) i.val z.val (bytes seed.val)
        (adrsS a) ⦄ :=
  xmss_node_aux p hp sk seed a z.val i z rfl h

theorem node_spec [ck : KeyCorrect w] {N : Usize} (p : slhdsa.params.Params) (hp : PN p N) (sk : Array U8 N) (i z : U32)
    (seed : Array U8 N) (a : address.Adrs) (h : (i.val + 1) * 2 ^ z.val ≤ 2 ^ 32) :
    shake.xmss.xmss_node sk i z seed a ⦃ r =>
      bytes r.val = Spec.xmssNode (params p) (bytes sk.val) i.val z.val (bytes seed.val) (adrsS a) ⦄ := by
  rw [shake.xmss.xmss_node.eq_def]
  by_cases positive : z >= 1#u32
  · simp only [positive,ite_true,shake.batch.available,ShakeBatch.available_for_fips _ p hp,KldispRust.shake256.parallel.available,bind_ok]
    exact subtree_spec p hp sk i z seed a h
  · have zero : z = 0#u32 := by scalar_tac
    subst z
    simp only [positive,ite_false,ite_true]
    let* ⟨a1,_,ht⟩ ← with_type_spec
    let* ⟨a2,hk⟩ ← with_keypair_spec
    rw [public_key_eq p hp sk seed a2 (by simp [Domain,hk,ht])]
    let* ⟨out,post⟩ ← Shake.wots_pk_gen_spec p hp
    simp [post,hk,ht,Spec.xmssNode,adrsS,Spec.Adrs.setTypeAndClear,Spec.WOTS_HASH,address.WOTS_HASH]


variable [cw : WotsCorrect w]

private theorem xmss_sign_loop_spec {N : Usize} (p : _root_.slhdsa.params.Params) (hp : PN p N) (sk : Array U8 N)
    (idx : U32) (seed : Array U8 N) (a : address.Adrs) (sig : alloc.vec.Vec U8)
    (j : U32) (wsig : Spec.Bytes)
    (hidx : idx.val < 2 ^ p.hp.val) (hj : j.val ≤ p.hp.val)
    (hlen : sig.length = N.val * (2 * N.val + 3) + N.val * j.val)
    (hinv : bytes sig.val = wsig ++ (List.range j.val).flatMap fun j =>
      Spec.xmssNode (params p) (bytes sk.val) ((idx.val / 2 ^ j) ^^^ 1) j (bytes seed.val)
        (adrsS a)) :
    shake.batch.xmss_sign_batch_loop {start := j, «end» := p.hp} sk idx seed a sig ⦃ r =>
      bytes r.val = wsig ++ (List.range p.hp.val).flatMap (fun j =>
        Spec.xmssNode (params p) (bytes sk.val) ((idx.val / 2 ^ j) ^^^ 1) j (bytes seed.val)
          (adrsS a)) ∧
      r.length = (2 * N.val + 3 + p.hp.val) * N.val ⦄ := by
  have hn32 := hp.le32
  have hhp := valid_hp_le p hp.valid
  have hidx9 : idx.val < 2 ^ 9 :=
    lt_of_lt_of_le hidx (Nat.pow_le_pow_right (by decide) hhp)
  unfold shake.batch.xmss_sign_batch_loop
  apply loop.spec_decr_nat (measure := fun (q : core.ops.range.Range U32 × alloc.vec.Vec U8) => p.hp.val - q.1.start.val)
    (inv := fun q => q.1.end = p.hp ∧ q.1.start.val ≤ p.hp.val ∧
      q.2.length = N.val * (2 * N.val + 3) + N.val * q.1.start.val ∧
      bytes q.2.val = wsig ++ (List.range q.1.start.val).flatMap fun j =>
        Spec.xmssNode (params p) (bytes sk.val) ((idx.val / 2 ^ j) ^^^ 1) j
          (bytes seed.val) (adrsS a))
  · clear hj hlen hinv sig j
    rintro ⟨it, sig⟩ ⟨stop,hj, hlen, hinv⟩
    simp only [shake.batch.xmss_sign_batch_loop.body]
    simp only at stop hj hlen hinv
    let j := it.start
    by_cases more : it.start.val < it.end.val
    · obtain ⟨⟨o,next⟩,run,item,inc,last⟩ := spec_imp_exists (core.iter.range.IteratorRange.next_U32_some_spec it more)
      have hjlt : j.val < p.hp.val := stop ▸ more
      simp only [run,item,bind_ok]
      let* ⟨ i, i_post, i_post1 ⟩ ← U32.ShiftRight_spec
      let* ⟨ k, k_post, k_post1 ⟩ ← UScalar.xor_spec
      have hk : k.val = (idx.val / 2 ^ j.val) ^^^ 1 := by
        rw [k_post]; simp [i_post, Nat.shiftRight_eq_div_pow, j]
      have hkb : k.val < 2 ^ 9 := by
        rw [hk]
        exact Nat.xor_lt_two_pow (lt_of_le_of_lt (Nat.div_le_self _ _) hidx9) (by decide)
      let* ⟨ node, node_post ⟩ ← subtree_spec p hp
      · calc (k.val + 1) * 2 ^ j.val ≤ 2 ^ 9 * 2 ^ 8 :=
              Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by decide) (by omega))
          _ ≤ 2 ^ 32 := by norm_num
      have hb1 : N.val * (2 * N.val + 3) ≤ 32 * 67 :=
        Nat.mul_le_mul hn32 (by omega)
      have hb2 : N.val * j.val ≤ 32 * 9 := Nat.mul_le_mul hn32 (by omega)
      let* ⟨ s, s_post ⟩ ← Array.to_slice.step_spec
      let* ⟨ sig1, sig1_post, sig1_len ⟩ ← xmss_extend_u8_spec
      refine ⟨last.trans stop,by change next.start.val ≤ _; rw [inc]; exact hjlt, ?_, ?_, ?_⟩
      · rw [sig1_len, hlen, s_post, inc]; simp; ring
      · simp [sig1_post, s_post, hinv, inc, List.range_succ, node_post, hk, j]
      · change p.hp.val - next.start.val < p.hp.val - it.start.val
        rw [inc]; change it.start.val < p.hp.val at hjlt; omega
    · obtain ⟨⟨o,next⟩,run,item,_⟩ := spec_imp_exists (core.iter.range.IteratorRange.next_U32_none_spec it (by omega))
      have hjeq : it.start.val = p.hp.val := by rw [stop] at more; omega
      simp only [run,item,bind_ok]
      simp only [step_simps]
      refine ⟨?_, ?_⟩
      · rw [hinv, hjeq]
      · rw [hlen, hjeq]; ring
  · exact ⟨rfl,hj, hlen, hinv⟩

private theorem scalar_loop_spec {N : Usize} (p : _root_.slhdsa.params.Params) (hp : PN p N) (sk : Array U8 N)
    (idx : U32) (seed : Array U8 N) (a : address.Adrs) (sig : alloc.vec.Vec U8)
    (j : U32) (wsig : Spec.Bytes)
    (hidx : idx.val < 2 ^ p.hp.val) (hj : j.val ≤ p.hp.val)
    (hlen : sig.length = N.val * (2 * N.val + 3) + N.val * j.val)
    (hinv : bytes sig.val = wsig ++ (List.range j.val).flatMap fun j =>
      Spec.xmssNode (params p) (bytes sk.val) ((idx.val / 2 ^ j) ^^^ 1) j (bytes seed.val)
        (adrsS a)) :
    shake.xmss.xmss_sign_loop1 p.hp sk idx seed a sig j ⦃ r =>
      bytes r.val = wsig ++ (List.range p.hp.val).flatMap (fun j =>
        Spec.xmssNode (params p) (bytes sk.val) ((idx.val / 2 ^ j) ^^^ 1) j (bytes seed.val)
          (adrsS a)) ∧
      r.length = (2 * N.val + 3 + p.hp.val) * N.val ⦄ := by
  have hn32 := hp.le32
  have hhp := valid_hp_le p hp.valid
  have hidx9 : idx.val < 2 ^ 9 :=
    lt_of_lt_of_le hidx (Nat.pow_le_pow_right (by decide) hhp)
  unfold shake.xmss.xmss_sign_loop1
  apply loop.spec_decr_nat (measure := fun (q : alloc.vec.Vec U8 × U32) => p.hp.val - q.2.val)
    (inv := fun q => q.2.val ≤ p.hp.val ∧
      q.1.length = N.val * (2 * N.val + 3) + N.val * q.2.val ∧
      bytes q.1.val = wsig ++ (List.range q.2.val).flatMap fun j =>
        Spec.xmssNode (params p) (bytes sk.val) ((idx.val / 2 ^ j) ^^^ 1) j
          (bytes seed.val) (adrsS a))
  · clear hj hlen hinv sig j
    rintro ⟨sig, j⟩ ⟨hj, hlen, hinv⟩
    simp only [shake.xmss.xmss_sign_loop1.body]
    simp only at hj hlen hinv
    simp only [step_simps]
    spec_split
    · rename_i hlt
      have hjlt : j.val < p.hp.val := by scalar_tac
      let* ⟨ i, i_post, i_post1 ⟩ ← U32.ShiftRight_spec
      let* ⟨ k, k_post, k_post1 ⟩ ← UScalar.xor_spec
      have hk : k.val = (idx.val / 2 ^ j.val) ^^^ 1 := by
        rw [k_post]; simp [i_post, Nat.shiftRight_eq_div_pow]
      have hkb : k.val < 2 ^ 9 := by
        rw [hk]
        exact Nat.xor_lt_two_pow (lt_of_le_of_lt (Nat.div_le_self _ _) hidx9) (by decide)
      let* ⟨ node, node_post ⟩ ← node_spec p hp
      · calc (k.val + 1) * 2 ^ j.val ≤ 2 ^ 9 * 2 ^ 8 :=
              Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by decide) (by omega))
          _ ≤ 2 ^ 32 := by norm_num
      have hb1 : N.val * (2 * N.val + 3) ≤ 32 * 67 :=
        Nat.mul_le_mul hn32 (by omega)
      have hb2 : N.val * j.val ≤ 32 * 9 := Nat.mul_le_mul hn32 (by omega)
      let* ⟨ s, s_post ⟩ ← Array.to_slice.step_spec
      let* ⟨ sig1, sig1_post, sig1_len ⟩ ← xmss_extend_u8_spec
      let* ⟨ j1, j1_post ⟩ ← U32.add_spec
      refine ⟨by scalar_tac, ?_, ?_, by scalar_tac⟩
      · rw [sig1_len, hlen, s_post, j1_post]; simp; ring
      · simp [sig1_post, s_post, hinv, j1_post, List.range_succ, node_post, hk]
    · rename_i hge
      have hjeq : j.val = p.hp.val := by scalar_tac
      simp only [step_simps]
      refine ⟨?_, ?_⟩
      · rw [hinv, hjeq]
      · rw [hlen, hjeq]; ring
  · exact ⟨hj, hlen, hinv⟩

@[step]
theorem xmss_sign_spec {N : Usize} (p : _root_.slhdsa.params.Params) (hp : PN p N) (m sk : Array U8 N) (idx : U32)
    (seed : Array U8 N) (a : address.Adrs) (h : idx.val < 2 ^ p.hp.val) :
    shake.xmss.xmss_sign p m sk idx seed a ⦃ r =>
      bytes r.val = Spec.xmssSign (params p) (bytes m.val) (bytes sk.val) idx.val
        (bytes seed.val) (adrsS a) ∧
      r.length = (2 * N.val + 3 + p.hp.val) * N.val ⦄ := by
  unfold shake.xmss.xmss_sign
  by_cases high : p.hp >= 3#u32
  · simp only [high,ite_true,shake.batch.available,ShakeBatch.available_for_fips _ p hp,
      KldispRust.shake256.parallel.available,bind_ok]
    unfold shake.batch.xmss_sign_batch
    obtain ⟨digits,decoded,_⟩ := spec_imp_exists (wots_digits_spec p hp m)
    simp only [decoded,bind_ok]
    let* ⟨ a1, a1_post, a1_post1 ⟩ ← with_type_spec
    let* ⟨ a2, a2_post ⟩ ← with_keypair_spec
    have same := sign_scalar p hp m sk seed a2 (by simp [Domain,a2_post,a1_post1])
    simp only [decoded,bind_ok] at same
    rw [show shake.batch.sign sk seed a2 digits.deref = _ from same]
    let* ⟨ sig, sig_post, sig_len ⟩ ← Shake.wots_sign_spec p hp
    apply WP.spec_mono
    · exact xmss_sign_loop_spec p hp sk idx seed a sig 0#u32 (bytes sig.val) h
        (by scalar_tac) (by simp [sig_len]) (by simp)
    · rintro r ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      rw [h1, sig_post]
      simp [Spec.xmssSign, a2_post, a1_post1, adrsS, Spec.Adrs.setTypeAndClear,
        Spec.WOTS_HASH, address.WOTS_HASH]
      rfl

  · simp only [high,ite_false]
    let* ⟨ a1, a1_post, a1_post1 ⟩ ← with_type_spec
    let* ⟨ a2, a2_post ⟩ ← with_keypair_spec
    rw [show shake.wots.wots_sign m sk seed a2 = _ from public_sign_eq p hp m sk seed a2 (by simp [Domain,a2_post,a1_post1])]
    let* ⟨ sig, sig_post, sig_len ⟩ ← Shake.wots_sign_spec p hp
    apply WP.spec_mono
    · exact scalar_loop_spec p hp sk idx seed a sig 0#u32 (bytes sig.val) h
        (by scalar_tac) (by simp [sig_len]) (by simp)
    · rintro r ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      rw [h1, sig_post]
      simp [Spec.xmssSign, a2_post, a1_post1, adrsS, Spec.Adrs.setTypeAndClear,
        Spec.WOTS_HASH, address.WOTS_HASH]
      rfl

end slhdsa.WidthThree
