import PeerEquality.VerifyBoundary

open Aeneas Aeneas.Std Result
namespace slhdsa.PeerCall

/-- Concrete root register, signature and indices including the final iteration. -/
def liveSignPrefix (c : Xmss) (p : Spec.Params) (msg sk pk : Spec.Bytes) (tree leaf k : Nat) :=
  (List.range k).foldl (signNext p.d (signStep c p sk pk)) ([],msg,tree,leaf)

theorem liveSignPrefix_before (c : Xmss) (p : Spec.Params) (msg sk pk tree leaf k) (h : k < p.d) :
    liveSignPrefix c p msg sk pk tree leaf k = signPrefix c p msg sk pk tree leaf k :=
  signNext_prefix _ _ h

theorem liveSignPrefix_complete (c : Xmss) (p : Spec.Params) (msg sk pk tree leaf) (h : 0 < p.d) :
    (liveSignPrefix c p msg sk pk tree leaf p.d).1 = ht c p msg sk pk tree leaf := by
  exact (signNext_signature _ _ _).trans (signPrefix_complete c p h msg sk pk tree leaf).symm

private theorem signPrefix_eq {c : Children} {p : Spec.Params} (laws : ChildLaws c p)
    (msg sk pk : Spec.Bytes) (tree leaf k : Nat) :
    liveSignPrefix (c.xmss p) p msg sk pk tree leaf k =
      (List.range k).foldl (signNext p.d (htSignStep p sk pk)) ([],msg,tree,leaf) := by
  rw [laws.xmss]
  rfl

theorem sha2_sign_layer (set : RcSlhSha2.StandardSet) (route : RcSlhSha2.Routing) {N : Usize} (p : params.Params) (hp : PN p N) (sk : Array U8 N)
    (seed : hash.Seed N) (hs : SeedOk seed) (m0 : Spec.Bytes)
    (sig : alloc.vec.Vec U8) (root : Array U8 N) (tree : U64) (leaf : U32) (j : U32) (t0 l0 : Nat)
    (hj : j.val < p.d.val) (hl : leaf.val < 2 ^ p.hp.val)
    (hlen : sig.length = (2 * N.val + 3 + p.hp.val) * N.val * j.val)
    (suite : RcSlhSha2.params set = paramsS p)
    (hinv : (bytes sig.val,bytes root.val,tree.val,leaf.val) =
      liveSignPrefix ((Providers.sha2 set RcSlhSha2.nativeAlgorithms).xmss (paramsS p)) (paramsS p) m0 (bytes sk.val) (bytes seed.pk_seed.val) t0 l0 j.val) :
    ht.ht_sign_loop.body p sk seed sig root tree leaf j ⦃ r =>
      match r with
      | .cont (sig1,root1,tree1,leaf1,j1) =>
        j1.val = j.val + 1 ∧ leaf1.val < 2 ^ p.hp.val ∧
        sig1.length = (2 * N.val + 3 + p.hp.val) * N.val * j1.val ∧
        (bytes sig1.val,bytes root1.val,tree1.val,leaf1.val) =
          liveSignPrefix ((Providers.sha2 set RcSlhSha2.nativeAlgorithms).xmss (paramsS p)) (paramsS p) m0 (bytes sk.val) (bytes seed.pk_seed.val) t0 l0 j1.val
      | .done _ => False ⦄ := by
  have laws : ChildLaws (Providers.sha2 set RcSlhSha2.nativeAlgorithms) (paramsS p) := by
    rw [← suite]
    exact Providers.sha2_laws _ route _ ((RcSlhSha2.observed_iff _ _).mpr rfl)
  simp only [signPrefix_eq laws] at hinv ⊢
  have hv := hp.valid
  have hd : p.d.val ≤ 22 := by simpa using hv.d_le
  have hhp : p.hp.val ≤ 9 := by simpa using hv.hp_le
  have hxsb := ht_xs_le p hp
  generalize hX : (2 * N.val + 3 + p.hp.val) * N.val = X at *
  have active : j < p.d := by scalar_tac
  simp only [ht.ht_sign_loop.body, active, ite_true]
  have hb1 : X * j.val ≤ 2432 * 22 := Nat.mul_le_mul hxsb (by omega)
  step
  step
  step
  step with xmss_sign_spec p hp root sk leaf seed hs adrs hl as ⟨s1, s1_post, s1_len⟩
  rw [hX] at s1_len
  step with ht_next_message_spec p hp j leaf (alloc.vec.Vec.deref s1) root seed hs
    adrs hj (by simp [s1_len, hX]) hl as ⟨root1, root1_post⟩
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
  refine ⟨j1_post, ?_, ?_, ?_⟩
  · rw [h5]; exact Nat.mod_lt _ hpos
  · simp only [sig1_len, vec_deref_length, hlen, s1_len, j1_post]; ring
  rw [j1_post, List.range_succ, List.foldl_append, ← hinv]
  simp only [List.foldl_cons, List.foldl_nil, signNext, htSignStep, paramsS_hp, paramsS_d]
  rw [sig1_post, root1_post, bytes_append, vec_deref_val, s1_post,
    ha, h5, tree1_post]

theorem shake_sign_layer (impl : PeerShake.Backend.Implementation) {N : Usize} (p : _root_.slhdsa.params.Params) (hp : PN p N) (sk : Array U8 N)
    (seed : Array U8 N) (m0 : Spec.Bytes)
    (sig : alloc.vec.Vec U8) (root : Array U8 N) (tree : U64) (leaf : U32) (j : U32) (t0 l0 : Nat)
    (hj : j.val < p.d.val) (hl : leaf.val < 2 ^ p.hp.val)
    (hlen : sig.length = (2 * N.val + 3 + p.hp.val) * N.val * j.val)
    (hinv : (bytes sig.val,bytes root.val,tree.val,leaf.val) =
      liveSignPrefix ((Providers.nativeShake impl (Shake.params p)).xmss (Shake.params p)) (Shake.params p) m0 (bytes sk.val) (bytes seed.val) t0 l0 j.val) :
    shake.ht.ht_sign_loop.body p sk seed sig root tree leaf j ⦃ r =>
      match r with
      | .cont (sig1,root1,tree1,leaf1,j1) =>
        j1.val = j.val + 1 ∧ leaf1.val < 2 ^ p.hp.val ∧
        sig1.length = (2 * N.val + 3 + p.hp.val) * N.val * j1.val ∧
        (bytes sig1.val,bytes root1.val,tree1.val,leaf1.val) =
          liveSignPrefix ((Providers.nativeShake impl (Shake.params p)).xmss (Shake.params p)) (Shake.params p) m0 (bytes sk.val) (bytes seed.val) t0 l0 j1.val
      | .done _ => False ⦄ := by
  have laws : ChildLaws (Providers.nativeShake impl (Shake.params p)) (Shake.params p) := by
    rw [Providers.nativeShake_eq]
    exact Providers.shake_laws _ (by have v := hp.valid; cases v; constructor <;> assumption) rfl
  simp only [signPrefix_eq laws] at hinv ⊢
  have hv := hp.valid
  have hd : p.d.val ≤ 22 := by simpa using hv.d_le
  have hhp : p.hp.val ≤ 9 := by simpa using hv.hp_le
  have hxsb := ht_xs_le p hp
  generalize hX : (2 * N.val + 3 + p.hp.val) * N.val = X at *
  have active : j < p.d := by scalar_tac
  simp only [shake.ht.ht_sign_loop.body, active, ite_true]
  have hb1 : X * j.val ≤ 2432 * 22 := Nat.mul_le_mul hxsb (by omega)
  step
  step
  step
  step with Shake.xmss_sign_spec p hp root sk leaf seed adrs hl as ⟨s1, s1_post, s1_len⟩
  rw [hX] at s1_len
  step with Shake.ht_next_message_spec p hp j leaf (alloc.vec.Vec.deref s1) root seed
    adrs hj (by simp [s1_len, hX]) hl as ⟨root1, root1_post⟩
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
  refine ⟨j1_post, ?_, ?_, ?_⟩
  · rw [h5]; exact Nat.mod_lt _ hpos
  · simp only [sig1_len, vec_deref_length, hlen, s1_len, j1_post]; ring
  rw [j1_post, List.range_succ, List.foldl_append, ← hinv]
  simp only [List.foldl_cons, List.foldl_nil, signNext, htSignStep, show (Shake.params p).hp = p.hp.val from rfl,
    show (Shake.params p).d = p.d.val from rfl]
  rw [sig1_post, root1_post, bytes_append, vec_deref_val, s1_post,
    ha, h5, tree1_post]

end slhdsa.PeerCall
