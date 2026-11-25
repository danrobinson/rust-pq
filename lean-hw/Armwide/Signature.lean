import Armwide.ForsTree.Sign
import Armplatform.WideForsDispatch
import Armplatform.Internal
import Armwide.Hypertree
open Aeneas Aeneas.Std Result
namespace slhdsa.NativeArmSignature
open Armwide.Public.Dispatcher (Cpu)
open Armwide.Keygen (Features)
noncomputable section
variable [cpu : Cpu] [features : Features]
abbrev ht.ht_sign {N : Usize} := @Armwide.Hypertree.ht.ht_sign cpu features N
abbrev ht.ht_verify {N : Usize} := @Armwide.Hypertree.ht.ht_verify cpu features N
abbrev fors.fors_sign {N : Usize} := @ArmForsTree.Entry.fors.fors_sign cpu features N
abbrev fors.fors_pk_from_sig {N : Usize} := @WideFors.dispatch N (ok cpu.wide) features.sha512 features.sha512
abbrev hash.prf_msg {N : Usize} := @AppleInternal.slhdsa.hash.prf_msg N
abbrev hash.h_msg {N : Usize} := @AppleInternal.slhdsa.hash.h_msg N

def slh.slh_sign_internal
  {N : Std.Usize} (p : params.Params) (m : Slice Std.U8) (sk : Slice Std.U8)
  (addrnd : Array Std.U8 N) :
  Result (alloc.vec.Vec Std.U8)
  := do
  let sk_seed ← util.block N sk 0#usize
  let sk_prf ← util.block N sk 1#usize
  let pk_seed ← util.block N sk 2#usize
  let pk_root ← util.block N sk 3#usize
  let r ← hash.prf_msg sk_prf addrnd m
  let digest ← hash.h_msg p r pk_seed pk_root m
  let s := alloc.vec.Vec.deref digest
  let idx_tree ← slh.digest_tree p s
  let s1 := alloc.vec.Vec.deref digest
  let idx_leaf ← slh.digest_leaf p s1
  let a ← address.Adrs.new
  let a1 ← address.Adrs.with_tree a idx_tree
  let a2 ← address.Adrs.with_type a1 address.FORS_TREE
  let adrs ← address.Adrs.with_keypair a2 idx_leaf
  let seed ← hash.seed_ctx pk_seed
  let i ← params.Params.md_bytes p
  let md ←
    alloc.vec.Vec.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)
      digest { start := 0#usize, «end» := i }
  let sig_fors ← fors.fors_sign p md sk_seed seed adrs
  let s2 := alloc.vec.Vec.deref sig_fors
  let pk_fors ← fors.fors_pk_from_sig p s2 md seed adrs
  let sig_ht ← ht.ht_sign p pk_fors sk_seed seed idx_tree idx_leaf
  let s3 ← lift (Array.to_slice r)
  let sig ←
    alloc.vec.Vec.extend_from_slice core.clone.CloneU8 (alloc.vec.Vec.new
      Std.U8) s3
  let s4 := alloc.vec.Vec.deref sig_fors
  let sig1 ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 sig s4
  let s5 := alloc.vec.Vec.deref sig_ht
  alloc.vec.Vec.extend_from_slice core.clone.CloneU8 sig1 s5

def slh.slh_verify_internal
  (N : Std.Usize) (p : params.Params) (m : Slice Std.U8) (sig : Slice Std.U8)
  (pk : Slice Std.U8) :
  Result Bool
  := do
  let sig_bytes ← params.Params.sig_bytes p
  let i := Slice.len sig
  if i != sig_bytes
  then ok false
  else
    let i1 ← params.Params.fors_sig_bytes p
    let fors_end ← N + i1
    let pk_seed ← util.block N pk 0#usize
    let pk_root ← util.block N pk 1#usize
    let r ← util.block N sig 0#usize
    let digest ← hash.h_msg p r pk_seed pk_root m
    let s := alloc.vec.Vec.deref digest
    let idx_tree ← slh.digest_tree p s
    let s1 := alloc.vec.Vec.deref digest
    let idx_leaf ← slh.digest_leaf p s1
    let a ← address.Adrs.new
    let a1 ← address.Adrs.with_tree a idx_tree
    let a2 ← address.Adrs.with_type a1 address.FORS_TREE
    let adrs ← address.Adrs.with_keypair a2 idx_leaf
    let seed ← hash.seed_ctx pk_seed
    let s2 ←
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice
        Std.U8) sig { start := N, «end» := fors_end }
    let i2 ← params.Params.md_bytes p
    let s3 ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)
        digest { start := 0#usize, «end» := i2 }
    let pk_fors ← fors.fors_pk_from_sig p s2 s3 seed adrs
    let s4 ←
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice
        Std.U8) sig { start := fors_end, «end» := sig_bytes }
    ht.ht_verify p pk_fors s4 seed idx_tree idx_leaf pk_root

set_option maxHeartbeats 2000000 in
@[step]
theorem slh_sign_internal_spec {N : Usize} (p : params.Params) (hp : PN p N) (m sk : Slice U8)
    (addrnd : Array U8 N) (hsk : sk.length = 4 * N.val) (hm : Room m.length (msgSlack N.val)) :
    slh.slh_sign_internal p m sk addrnd ⦃ sig =>
      bytes sig.val = Spec.slhSignInternal (paramsS p) (bytes m.val) (bytes sk.val)
        (bytes addrnd.val) ∧
      sig.length = (paramsS p).sigBytes ⦄ := by
  have hv := hp.valid
  have hn := hp.le32
  have hmq := hv.m_eq
  simp only [paramsS_m] at hmq
  have hfl := fors_len_le p hp
  have hhl := ht_len_le p hp
  unfold slh.slh_sign_internal
  let* ⟨ sk_seed, sk_seed_post ⟩ ← block_spec
  let* ⟨ sk_prf, sk_prf_post ⟩ ← block_spec
  let* ⟨ pk_seed, pk_seed_post ⟩ ← block_spec
  let* ⟨ pk_root, pk_root_post ⟩ ← block_spec
  let* ⟨ r, r_post ⟩ ← AppleInternal.slhdsa.prf_msg_spec (paramsS p) hp.n hp.nok
  let* ⟨ digest, digest_post, digest_len ⟩ ← AppleInternal.slhdsa.h_msg_spec p hv hp.n_eq
  let* ⟨ idx_tree, idx_tree_post, idx_tree_lt ⟩ ← digest_tree_spec
  let* ⟨ idx_leaf, idx_leaf_post, idx_leaf_lt ⟩ ← digest_leaf_spec
  let* ⟨ a, a_post ⟩ ← adrs_new_spec
  let* ⟨ a1, a1_post ⟩ ← with_tree_spec
  let* ⟨ a2, a2_post, a2_post1 ⟩ ← slhdsa.with_type_spec
  let* ⟨ adrs, adrs_post ⟩ ← slhdsa.with_keypair_spec
  let* ⟨ seed, seed_pk, seed_ok ⟩ ← seed_ctx_spec hp.nok
  let* ⟨ i, i_post, i_post1 ⟩ ← md_bytes_spec
  let* ⟨ md, md_post, md_len ⟩ ← alloc.vec.Vec.index_Range_spec
  let* ⟨ sig_fors, sig_fors_post, sig_fors_len ⟩ ← ArmForsTree.Entry.fors_sign_spec p hp md sk_seed seed seed_ok adrs
    (by simp [adrsS, adrs_post, a2_post1, Spec.FORS_TREE, global_simps])
  let* ⟨ pk_fors, pk_fors_post ⟩ ← WideFors.dispatch_fips cpu.wide features.sha512 features.sha512 p hp (alloc.vec.Vec.deref sig_fors) md seed
    seed_ok adrs
  let* ⟨ sig_ht, sig_ht_post, sig_ht_len ⟩ ← Armwide.Hypertree.ht_sign_spec p hp pk_fors sk_seed seed seed_ok idx_tree
    idx_leaf idx_leaf_lt
  let* ⟨ s3, s3_post ⟩ ← Array.to_slice.step_spec
  let* ⟨ sg0, sg0_post ⟩ ← extend_spec
  have hl0 : sg0.length = N.val := by
    simp only [alloc.vec.Vec.length]; rw [sg0_post, s3_post]; simp
  let* ⟨ sg1, sg1_post ⟩ ← extend_spec
  have hl1 : sg1.length = N.val + p.k.val * (1 + p.a.val) * N.val := by
    have : sg1.val.length = sg0.val.length + sig_fors.val.length := by rw [sg1_post]; simp
    simp only [alloc.vec.Vec.length] at hl0 sig_fors_len ⊢; omega
  let* ⟨ sg2, sg2_post ⟩ ← extend_spec
  have hb0 := bytes_block_N p hp sk sk_seed 0 sk_seed_post
  have hb1 := bytes_block_N p hp sk sk_prf 1 sk_prf_post
  have hb2 := bytes_block_N p hp sk pk_seed 2 pk_seed_post
  have hb3 := bytes_block_N p hp sk pk_root 3 pk_root_post
  have hadrs : adrsS adrs = { { Spec.Adrs.zero with tree := idx_tree.val }.setTypeAndClear
      Spec.FORS_TREE with keypair := idx_leaf.val } := by
    simp [adrsS, adrs_post, a2_post1, a1_post, a_post, Spec.Adrs.setTypeAndClear,
      Spec.Adrs.zero, Spec.FORS_TREE, global_simps]
  have hmd : bytes md.val = (bytes digest.val).take (paramsS p).mdBytes := by
    simp [md_post, List.slice, i_post1]
  have hsig : bytes sg2.val = bytes r.val ++ bytes sig_fors.val ++ bytes sig_ht.val := by
    simp [sg2_post, sg1_post, sg0_post, s3_post]
  simp only [vec_deref_val] at *
  rw [seed_pk] at sig_fors_post pk_fors_post sig_ht_post
  constructor
  · simp only [Spec.slhSignInternal]
    rw [← hb0, ← hb1, ← hb2, ← hb3, ← r_post, ← digest_post, ← hmd, ← idx_tree_post,
      ← idx_leaf_post, ← hadrs, ← sig_fors_post, ← pk_fors_post, ← sig_ht_post, hsig]
  · rw [sigBytes_eq p hv, forsSigBytes_eq p hp, xmssSigBytes_eq p hp]
    have : sg2.val.length = sg1.val.length + sig_ht.val.length := by rw [sg2_post]; simp
    simp only [alloc.vec.Vec.length] at hl1 sig_ht_len ⊢
    simp only [paramsS_n, paramsS_d, hp.n_eq]
    omega

set_option maxHeartbeats 2000000 in
/-- For every byte string `sig`, of any length. -/
@[step]
theorem slh_verify_internal_spec {N : Usize} (p : params.Params) (hp : PN p N) (m sig pk : Slice U8)
    (hpk : pk.length = 2 * N.val) (hm : Room m.length (msgSlack N.val)) :
    slh.slh_verify_internal N p m sig pk ⦃ b =>
      b = Spec.slhVerifyInternal (paramsS p) (bytes m.val) (bytes sig.val) (bytes pk.val) ⦄ := by
  have hv := hp.valid
  have hn := hp.le32
  have hmq := hv.m_eq
  simp only [paramsS_m] at hmq
  have hfl := fors_len_le p hp
  have hhl := ht_len_le p hp
  have hfe := forsSigBytes_eq p hp
  have hxe := xmssSigBytes_eq p hp
  unfold slh.slh_verify_internal
  let* ⟨ sig_bytes, sig_bytes_post, sig_bytes_post1 ⟩ ← sig_bytes_spec
  split
  · rename_i hlen
    have : sig.val.length ≠ (paramsS p).sigBytes := by
      simp only [bne_iff_ne, ne_eq] at hlen
      intro h; apply hlen; scalar_tac
    simp [Spec.slhVerifyInternal, this]
  · rename_i hlen
    have hlen' : sig.val.length = (paramsS p).sigBytes := by
      simp at hlen; scalar_tac
    have hsb : (paramsS p).sigBytes = N.val + p.k.val * (1 + p.a.val) * N.val +
        p.d.val * ((2 * N.val + 3 + p.hp.val) * N.val) := by
      rw [sigBytes_eq p hv, hfe, hxe]; simp [hp.n_eq]
    let* ⟨ i1, i1_post, i1_post1 ⟩ ← fors_sig_bytes_spec
    let* ⟨ fors_end, fors_end_post ⟩ ← Usize.add_spec
    let* ⟨ pk_seed, pk_seed_post ⟩ ← block_spec
    let* ⟨ pk_root, pk_root_post ⟩ ← block_spec
    let* ⟨ r, r_post ⟩ ← block_spec
    let* ⟨ digest, digest_post, digest_len ⟩ ← AppleInternal.slhdsa.h_msg_spec p hv hp.n_eq
    let* ⟨ idx_tree, idx_tree_post, idx_tree_lt ⟩ ← digest_tree_spec
    let* ⟨ idx_leaf, idx_leaf_post, idx_leaf_lt ⟩ ← digest_leaf_spec
    let* ⟨ a, a_post ⟩ ← adrs_new_spec
    let* ⟨ a1, a1_post ⟩ ← with_tree_spec
    let* ⟨ a2, a2_post, a2_post1 ⟩ ← slhdsa.with_type_spec
    let* ⟨ adrs, adrs_post ⟩ ← slhdsa.with_keypair_spec
    let* ⟨ seed, seed_pk, seed_ok ⟩ ← seed_ctx_spec hp.nok
    let* ⟨ s2, s2_post, s2_len ⟩ ← core.slice.index.SliceIndexRangeUsizeSlice.index.step_spec
    let* ⟨ i2, i2_post, i2_post1 ⟩ ← md_bytes_spec
    let* ⟨ s3, s3_post, s3_len ⟩ ← alloc.vec.Vec.index_Range_spec
    let* ⟨ pk_fors, pk_fors_post ⟩ ← WideFors.dispatch_fips cpu.wide features.sha512 features.sha512 p hp s2 s3 seed seed_ok adrs
      (by rw [s2_len, fors_end_post, i1_post, hp.n_eq]; omega) (by rw [s3_len, i2_post]; omega)
    let* ⟨ s4, s4_post, s4_len ⟩ ← core.slice.index.SliceIndexRangeUsizeSlice.index.step_spec
    let* ⟨ b, b_post ⟩ ← Armwide.Hypertree.ht_verify_spec p hp pk_fors s4 seed seed_ok idx_tree idx_leaf pk_root
      (by rw [s4_len, sig_bytes_post1, fors_end_post, i1_post, hfe, hxe]; simp only [hp.n_eq]; omega)
      idx_leaf_lt
    have hb0 := bytes_block_N p hp pk pk_seed 0 pk_seed_post
    have hb1 := bytes_block_N p hp pk pk_root 1 pk_root_post
    have hadrs : adrsS adrs = { { Spec.Adrs.zero with tree := idx_tree.val }.setTypeAndClear
        Spec.FORS_TREE with keypair := idx_leaf.val } := by
      simp [adrsS, adrs_post, a2_post1, a1_post, a_post, Spec.Adrs.setTypeAndClear,
        Spec.Adrs.zero, Spec.FORS_TREE, global_simps]
    have hmd : bytes s3.val = (bytes digest.val).take (paramsS p).mdBytes := by
      simp [s3_post, List.slice, i2_post1]
    have h5 : bytes s2.val =
        ((bytes sig.val).drop (paramsS p).n).take (paramsS p).forsSigBytes := by
      simp [s2_post, List.slice, fors_end_post, i1_post1, hp.n_eq]
    have h9 : bytes s4.val = (bytes sig.val).drop ((paramsS p).n + (paramsS p).forsSigBytes) := by
      rw [s4_post]
      simp only [List.slice]
      rw [List.take_of_length_le (by simp only [List.length_drop, sig_bytes_post1]; omega)]
      simp [fors_end_post, i1_post1, hp.n_eq]
    have hr : bytes r.val = (bytes sig.val).take (paramsS p).n := by
      simp [r_post, hp.n_eq]
    rw [seed_pk] at pk_fors_post b_post
    simp only [vec_deref_val] at *
    simp only [Spec.slhVerifyInternal]
    rw [if_neg (by simp [hlen']), ← hb0, ← hb1, ← hr, ← digest_post, ← hmd, ← idx_tree_post,
      ← idx_leaf_post, ← hadrs, ← h5, ← pk_fors_post, ← h9, ← b_post]


end
end slhdsa.NativeArmSignature
