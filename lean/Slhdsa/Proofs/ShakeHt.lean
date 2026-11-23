import Slhdsa.Proofs.Ht
import Slhdsa.Proofs.ShakeXmss
open Aeneas Aeneas.Std Result
namespace slhdsa.Shake

theorem ht_verify_loop_spec {N : Usize} (p : _root_.slhdsa.params.Params) (hp : PN p N) (sig : Slice U8)
    (seed : Array U8 N) (xs : Usize) (m0 : Spec.Bytes)
    (node : Array U8 N) (tree : U64) (leaf : U32) (j : U32) (t0 l0 : Nat)
    (hxs : xs.val = (2 * N.val + 3 + p.hp.val) * N.val)
    (hxs' : xs.val = (params p).xmssSigBytes)
    (h : sig.length = p.d.val * xs.val) (hj : j.val ≤ p.d.val) (hl : leaf.val < 2 ^ p.hp.val)
    (hinv : (bytes node.val, tree.val, leaf.val) =
      (List.range j.val).foldl (htVerifyStep (params p) (bytes sig.val) (bytes seed.val))
        (m0, t0, l0)) :
    shake.ht.ht_verify_loop p sig seed xs node tree leaf j ⦃ r =>
      ∃ t l, (bytes r.val, t, l) =
        (List.range p.d.val).foldl (htVerifyStep (params p) (bytes sig.val) (bytes seed.val))
          (m0, t0, l0) ⦄ := by
  have hv := hp.valid
  have hd : p.d.val ≤ 22 := by simpa using hv.d_le
  have hhp : p.hp.val ≤ 9 := by simpa using hv.hp_le
  have hxsb : xs.val ≤ 2432 := by rw [hxs]; exact ht_xs_le p hp
  unfold shake.ht.ht_verify_loop
  apply loop.spec_decr_nat
    (measure := fun (q : Array U8 N × U64 × U32 × U32) => p.d.val - q.2.2.2.val)
    (inv := fun q => q.2.2.2.val ≤ p.d.val ∧ q.2.2.1.val < 2 ^ p.hp.val ∧
      (bytes q.1.val, q.2.1.val, q.2.2.1.val) =
        (List.range q.2.2.2.val).foldl (htVerifyStep (params p) (bytes sig.val) (bytes seed.val))
          (m0, t0, l0))
  · rintro ⟨node, tree, leaf, j⟩ ⟨hj, hl, hinv⟩
    simp only [shake.ht.ht_verify_loop.body]
    simp only at hj hl hinv
    by_cases hjd : j < p.d
    · simp only [hjd, ite_true]
      have hjd' : j.val < p.d.val := by scalar_tac
      have hb1 : j.val * xs.val ≤ 22 * 2432 := Nat.mul_le_mul (by omega) hxsb
      have hb2 : j.val * xs.val + xs.val ≤ p.d.val * xs.val := by
        have : (j.val + 1) * xs.val ≤ p.d.val * xs.val := Nat.mul_le_mul_right _ (by omega)
        rw [Nat.add_mul] at this; omega
      step
      step
      step
      step
      step
      step
      step
      have hsl : s.length = (2 * N.val + 3 + p.hp.val) * N.val := by
        rw [s_post1, i1_post, ← hxs]; omega
      step with xmss_pk_from_sig_spec p hp leaf s node seed adrs hsl hl as ⟨node1, node1_post⟩
      have hlt : p.hp.val < 64 := by omega
      step as ⟨i2, i2_post, i2_bv⟩
      have h2 : i2.val = 2 ^ p.hp.val := ht_shl_val i2 p.hp hhp i2_post
      have hpos : 0 < 2 ^ p.hp.val := by positivity
      step as ⟨i3, i3_post⟩
      step as ⟨i4, i4_post⟩
      step as ⟨leaf1, leaf1_post⟩
      step as ⟨tree1, tree1_post, tree1_bv⟩
      step as ⟨j1, j1_post⟩
      have h5 : leaf1.val = tree.val % 2 ^ p.hp.val := by
        rw [leaf1_post]
        exact ht_leaf_val tree i3 i4 p.hp hhp (by omega) i4_post
      refine ⟨by scalar_tac, ?_, ?_, by scalar_tac⟩
      · rw [h5]; exact Nat.mod_lt _ (by positivity)
      · rw [j1_post, List.range_succ, List.foldl_append, ← hinv]
        simp only [List.foldl_cons, List.foldl_nil, htVerifyStep]
        have hs' : bytes s.val = List.take (params p).xmssSigBytes
            (List.drop (j.val * (params p).xmssSigBytes) (bytes sig.val)) := by
          rw [s_post, ← hxs']
          simp [List.slice, i1_post, off_post, i_post]
        have ha : adrsS adrs = { Spec.Adrs.zero with layer := j.val, tree := tree.val } := by
          simp [adrsS, adrs_post, a1_post, a_post, Spec.Adrs.zero]
        simp only [show (params p).hp = p.hp.val from rfl]
        rw [node1_post, hs', ha, h5, tree1_post]
    · simp only [hjd, ite_false]
      have : j.val = p.d.val := by scalar_tac
      simp only [WP.spec_ok]
      exact ⟨_, _, by rw [← this]; exact hinv⟩
  · exact ⟨hj, hl, hinv⟩

@[step]
theorem ht_verify_spec {N : Usize} (p : _root_.slhdsa.params.Params) (hp : PN p N) (m : Array U8 N) (sig : Slice U8)
    (seed : Array U8 N) (idx_tree : U64) (idx_leaf : U32) (pk_root : Array U8 N)
    (h : sig.length = p.d.val * ((2 * N.val + 3 + p.hp.val) * N.val))
    (hl : idx_leaf.val < 2 ^ p.hp.val) :
    shake.ht.ht_verify p m sig seed idx_tree idx_leaf pk_root ⦃ b =>
      b = Spec.htVerify (params p) (bytes m.val) (bytes sig.val) (bytes seed.val) idx_tree.val
        idx_leaf.val (bytes pk_root.val) ⦄ := by
  have hv := hp.valid
  unfold shake.ht.ht_verify
  let* ⟨xs, hxs, hxs'⟩ ← xmss_sig_bytes_spec p hv
  have hxs2 : xs.val = (2 * N.val + 3 + p.hp.val) * N.val := by rw [hxs, hp.n_eq]
  let* ⟨node1, t, l, hnode1⟩ ← ht_verify_loop_spec p hp sig seed xs (bytes m.val) m idx_tree idx_leaf
    0#u32 idx_tree.val idx_leaf.val hxs2 hxs' (by rw [h, hxs2]) (by simp) hl (by simp)
  step*
  rw [htVerify_eq]
  simp only [show (params p).d = p.d.val from rfl]
  rw [← hnode1, b_post]
  by_cases hn : node1.val = pk_root.val
  · simp [hn]
  · have : bytes node1.val ≠ bytes pk_root.val := fun hb => hn (ht_bytes_injective hb)
    simp [hn, this]

theorem ht_sign_loop_spec {N : Usize} (p : _root_.slhdsa.params.Params) (hp : PN p N) (sk : Array U8 N)
    (seed : Array U8 N) (m0 : Spec.Bytes)
    (sig : alloc.vec.Vec U8) (root : Array U8 N) (tree : U64) (leaf : U32) (j : U32) (t0 l0 : Nat)
    (hj : j.val ≤ p.d.val) (hl : leaf.val < 2 ^ p.hp.val)
    (hlen : sig.length = (2 * N.val + 3 + p.hp.val) * N.val * j.val)
    (hinv : (bytes sig.val, bytes root.val, tree.val, leaf.val) =
      (List.range j.val).foldl (htSignStep (params p) (bytes sk.val) (bytes seed.val))
        ([], m0, t0, l0)) :
    shake.ht.ht_sign_loop p sk seed sig root tree leaf j ⦃ r =>
      r.length = p.d.val * ((2 * N.val + 3 + p.hp.val) * N.val) ∧ bytes r.val =
        ((List.range p.d.val).foldl (htSignStep (params p) (bytes sk.val) (bytes seed.val))
          ([], m0, t0, l0)).1 ⦄ := by
  have hv := hp.valid
  have hd : p.d.val ≤ 22 := by simpa using hv.d_le
  have hhp : p.hp.val ≤ 9 := by simpa using hv.hp_le
  have hxsb := ht_xs_le p hp
  generalize hX : (2 * N.val + 3 + p.hp.val) * N.val = X at *
  unfold shake.ht.ht_sign_loop
  apply loop.spec_decr_nat
    (measure := fun (q : alloc.vec.Vec U8 × Array U8 N × U64 × U32 × U32) =>
      p.d.val - q.2.2.2.2.val)
    (inv := fun q => q.2.2.2.2.val ≤ p.d.val ∧ q.2.2.2.1.val < 2 ^ p.hp.val ∧
      q.1.length = X * q.2.2.2.2.val ∧
      (bytes q.1.val, bytes q.2.1.val, q.2.2.1.val, q.2.2.2.1.val) =
        (List.range q.2.2.2.2.val).foldl (htSignStep (params p) (bytes sk.val) (bytes seed.val))
          ([], m0, t0, l0))
  · rintro ⟨sig, root, tree, leaf, j⟩ ⟨hj, hl, hlen, hinv⟩
    simp only [shake.ht.ht_sign_loop.body]
    simp only at hj hl hlen hinv
    by_cases hjd : j < p.d
    · simp only [hjd, ite_true]
      have hjd' : j.val < p.d.val := by scalar_tac
      have hb1 : X * j.val ≤ 2432 * 22 := Nat.mul_le_mul hxsb (by omega)
      step
      step
      step
      step with xmss_sign_spec p hp root sk leaf seed adrs hl as ⟨s1, s1_post, s1_len⟩
      rw [hX] at s1_len
      step with xmss_pk_from_sig_spec p hp leaf (alloc.vec.Vec.deref s1) root seed
        adrs (by simp [s1_len, hX]) hl as ⟨root1, root1_post⟩
      step with ht_extend_from_slice_spec sig (alloc.vec.Vec.deref s1) (by simp; scalar_tac)
        as ⟨sig1, sig1_post, sig1_len⟩
      have hlt : p.hp.val < 64 := by omega
      step as ⟨i, i_post, i_bv⟩
      have h2 : i.val = 2 ^ p.hp.val := ht_shl_val i p.hp hhp i_post
      have hpos : 0 < 2 ^ p.hp.val := by positivity
      step as ⟨i1, i1_post⟩
      step as ⟨i2, i2_post⟩
      step as ⟨leaf1, leaf1_post⟩
      step as ⟨tree1, tree1_post, tree1_bv⟩
      step as ⟨j1, j1_post⟩
      have h5 : leaf1.val = tree.val % 2 ^ p.hp.val := by
        rw [leaf1_post]
        exact ht_leaf_val tree i1 i2 p.hp hhp (by omega) i2_post
      have ha : adrsS adrs = { Spec.Adrs.zero with layer := j.val, tree := tree.val } := by
        simp [adrsS, adrs_post, a1_post, a_post, Spec.Adrs.zero]
      refine ⟨by scalar_tac, ?_, ?_, ?_, by scalar_tac⟩
      · rw [h5]; exact Nat.mod_lt _ hpos
      · simp only [sig1_len, vec_deref_length, hlen, s1_len, j1_post]; ring
      · rw [j1_post, List.range_succ, List.foldl_append, ← hinv]
        simp only [List.foldl_cons, List.foldl_nil, htSignStep, show (params p).hp = p.hp.val from rfl]
        rw [sig1_post, root1_post, bytes_append, vec_deref_val, s1_post,
          ha, h5, tree1_post]
    · simp only [hjd, ite_false]
      have : j.val = p.d.val := by scalar_tac
      simp only [WP.spec_ok]
      subst hX
      refine ⟨?_, by rw [← this]; rw [← hinv]⟩
      rw [hlen, this, Nat.mul_comm]
  · exact ⟨hj, hl, hlen, hinv⟩

@[step]
theorem ht_sign_spec {N : Usize} (p : _root_.slhdsa.params.Params) (hp : PN p N) (m sk : Array U8 N)
    (seed : Array U8 N) (idx_tree : U64) (idx_leaf : U32)
    (hl : idx_leaf.val < 2 ^ p.hp.val) :
    shake.ht.ht_sign p m sk seed idx_tree idx_leaf ⦃ r =>
      bytes r.val = Spec.htSign (params p) (bytes m.val) (bytes sk.val) (bytes seed.val)
        idx_tree.val idx_leaf.val ∧
      r.length = p.d.val * ((2 * N.val + 3 + p.hp.val) * N.val) ⦄ := by
  unfold shake.ht.ht_sign
  apply WP.spec_mono
  · exact ht_sign_loop_spec p hp sk seed (bytes m.val) (alloc.vec.Vec.new U8) m idx_tree idx_leaf 0#u32
      idx_tree.val idx_leaf.val (by simp) hl (by simp) (by simp)
  · intro r ⟨h1, h2⟩
    exact ⟨by rw [htSign_eq]; exact h2, h1⟩

end slhdsa.Shake
