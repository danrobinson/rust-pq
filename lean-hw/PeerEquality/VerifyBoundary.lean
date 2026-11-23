import PeerEquality.Providers
import Slhdsa.Proofs.ShakeHt

open Aeneas Aeneas.Std Result
namespace slhdsa.PeerCall

/-- State of the actual verifier after k layers according to the peer's concrete
XMSS recovery. Both live indices are observable, even for a signature that fails. -/
def boundary (c : Children) (p : Spec.Params) (msg sig pk : Spec.Bytes) (tree leaf k : Nat) :=
  verifyPrefix (c.xmss p) p msg sig pk tree leaf k

private theorem boundary_eq {c : Children} {p : Spec.Params} (laws : ChildLaws c p)
    (msg sig pk : Spec.Bytes) (tree leaf k : Nat) :
    boundary c p msg sig pk tree leaf k =
      (List.range k).foldl (htVerifyStep p sig pk) (msg,tree,leaf) := by
  exact verifyPrefix_fips _ _ (congrArg Xmss.recover laws.xmss) _ _ _ _ _ _

theorem sha2_verify_layer (set : RcSlhSha2.StandardSet) (route : RcSlhSha2.Routing) {N : Usize} (p : params.Params) (hp : PN p N) (sig : Slice U8)
    (seed : hash.Seed N) (hs : SeedOk seed) (xs : Usize) (m0 : Spec.Bytes)
    (node : Array U8 N) (tree : U64) (leaf : U32) (j : U32) (t0 l0 : Nat)
    (hxs : xs.val = (2 * N.val + 3 + p.hp.val) * N.val)
    (hxs' : xs.val = (paramsS p).xmssSigBytes)
    (h : sig.length = p.d.val * xs.val) (hj : j.val < p.d.val) (hl : leaf.val < 2 ^ p.hp.val)
    (suite : RcSlhSha2.params set = paramsS p)
    (hinv : (bytes node.val, tree.val, leaf.val) =
      boundary (Providers.sha2 set RcSlhSha2.nativeAlgorithms) (paramsS p) m0 (bytes sig.val) (bytes seed.pk_seed.val) t0 l0 j.val) :
    ht.ht_verify_loop.body p sig seed xs node tree leaf j ⦃ r =>
      match r with
      | .cont (node1,tree1,leaf1,j1) =>
        j1.val = j.val + 1 ∧ leaf1.val < 2 ^ p.hp.val ∧
        (bytes node1.val,tree1.val,leaf1.val) =
          boundary (Providers.sha2 set RcSlhSha2.nativeAlgorithms) (paramsS p) m0 (bytes sig.val) (bytes seed.pk_seed.val) t0 l0 j1.val
      | .done _ => False ⦄ := by
  have laws : ChildLaws (Providers.sha2 set RcSlhSha2.nativeAlgorithms) (paramsS p) := by
    rw [← suite]
    exact Providers.sha2_laws _ route _ ((RcSlhSha2.observed_iff _ _).mpr rfl)
  simp only [boundary_eq laws] at hinv ⊢
  have hv := hp.valid
  have hd : p.d.val ≤ 22 := by simpa using hv.d_le
  have hhp : p.hp.val ≤ 9 := by simpa using hv.hp_le
  have hxsb : xs.val ≤ 2432 := by rw [hxs]; exact ht_xs_le p hp
  have active : j < p.d := by scalar_tac
  simp only [ht.ht_verify_loop.body, active, ite_true]
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
  step with xmss_pk_from_sig_spec p hp leaf s node seed hs adrs hsl hl as ⟨node1, node1_post⟩
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
  refine ⟨j1_post, ?_, ?_⟩
  · rw [h5]; exact Nat.mod_lt _ hpos
  rw [j1_post, List.range_succ, List.foldl_append, ← hinv]
  simp only [List.foldl_cons, List.foldl_nil, htVerifyStep]
  have hs' : bytes s.val = List.take (paramsS p).xmssSigBytes
      (List.drop (j.val * (paramsS p).xmssSigBytes) (bytes sig.val)) := by
    rw [s_post, ← hxs']
    simp [List.slice, i1_post, off_post, i_post]
  have ha : adrsS adrs = { Spec.Adrs.zero with layer := j.val, tree := tree.val } := by
    simp [adrsS, adrs_post, a1_post, a_post, Spec.Adrs.zero]
  simp only [paramsS_hp]
  rw [node1_post, hs', ha, h5, tree1_post]

theorem shake_verify_layer (impl : PeerShake.Backend.Implementation) {N : Usize} (p : _root_.slhdsa.params.Params) (hp : slhdsa.PN p N) (sig : Slice U8)
    (seed : Array U8 N) (xs : Usize) (m0 : Spec.Bytes)
    (node : Array U8 N) (tree : U64) (leaf : U32) (j : U32) (t0 l0 : Nat)
    (hxs : xs.val = (2 * N.val + 3 + p.hp.val) * N.val)
    (hxs' : xs.val = (Shake.params p).xmssSigBytes)
    (h : sig.length = p.d.val * xs.val) (hj : j.val < p.d.val) (hl : leaf.val < 2 ^ p.hp.val)
    (hinv : (bytes node.val, tree.val, leaf.val) =
      boundary (Providers.nativeShake impl (Shake.params p)) (Shake.params p) m0 (bytes sig.val) (bytes seed.val) t0 l0 j.val) :
    shake.ht.ht_verify_loop.body p sig seed xs node tree leaf j ⦃ r =>
      match r with
      | .cont (node1,tree1,leaf1,j1) =>
        j1.val = j.val + 1 ∧ leaf1.val < 2 ^ p.hp.val ∧
        (bytes node1.val,tree1.val,leaf1.val) =
          boundary (Providers.nativeShake impl (Shake.params p)) (Shake.params p) m0 (bytes sig.val) (bytes seed.val) t0 l0 j1.val
      | .done _ => False ⦄ := by
  have laws : ChildLaws (Providers.nativeShake impl (Shake.params p)) (Shake.params p) := by
    rw [Providers.nativeShake_eq]
    exact Providers.shake_laws _ (by have v := hp.valid; cases v; constructor <;> assumption) rfl
  simp only [boundary_eq laws] at hinv ⊢
  have hv := hp.valid
  have hd : p.d.val ≤ 22 := by simpa using hv.d_le
  have hhp : p.hp.val ≤ 9 := by simpa using hv.hp_le
  have hxsb : xs.val ≤ 2432 := by rw [hxs]; exact ht_xs_le p hp
  have active : j < p.d := by scalar_tac
  simp only [shake.ht.ht_verify_loop.body, active, ite_true]
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
  step with Shake.xmss_pk_from_sig_spec p hp leaf s node seed adrs hsl hl as ⟨node1, node1_post⟩
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
  refine ⟨j1_post, ?_, ?_⟩
  · rw [h5]; exact Nat.mod_lt _ hpos
  rw [j1_post, List.range_succ, List.foldl_append, ← hinv]
  simp only [List.foldl_cons, List.foldl_nil, htVerifyStep]
  have hs' : bytes s.val = List.take (Shake.params p).xmssSigBytes
      (List.drop (j.val * (Shake.params p).xmssSigBytes) (bytes sig.val)) := by
    rw [s_post, ← hxs']
    simp [List.slice, i1_post, off_post, i_post]
  have ha : adrsS adrs = { Spec.Adrs.zero with layer := j.val, tree := tree.val } := by
    simp [adrsS, adrs_post, a1_post, a_post, Spec.Adrs.zero]
  simp only [show (Shake.params p).hp = p.hp.val from rfl]
  rw [node1_post, hs', ha, h5, tree1_post]

end slhdsa.PeerCall
