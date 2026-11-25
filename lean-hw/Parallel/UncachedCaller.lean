import Parallel.UncachedProgram
import Parallel.SigningSlots
open Aeneas Aeneas.Std Result
namespace slhdsa.ParallelCaller
open ParallelFused.Slots
set_option maxHeartbeats 2000000
set_option linter.concreteInstances false

/-- Only the actual, caller-reachable worker arguments require a certificate.
A declined worker uses the original FORS and hypertree continuation. -/
def WorkerCorrect {S : Usize → Type} (worker : Worker S) {N : Usize} (p : params.Params) (P : Spec.Params)
    (seedBytes : S N → Spec.Bytes) (seedOk : S N → Prop) :=
  ∀ (md : Slice U8) (sk : Array U8 N) (seed : S N) (a : address.Adrs) (r : Array U8 N)
    (tree : U64) (leaf : U32), seedOk seed → md.length=P.mdBytes → tree.val<2^(p.h.val-p.hp.val) →
    leaf.val<2^p.hp.val → slhdsa.adrsS a = {{Spec.Adrs.zero with tree:=tree.val}.setTypeAndClear
      Spec.FORS_TREE with keypair:=leaf.val} →
    worker.run p md sk seed a r tree leaf ⦃ res => match res with
      | none => True
      | some out => Output P (bytes md.val) (bytes sk.val) (seedBytes seed) (adrsS a)
          (bytes r.val) tree.val leaf.val (bytes out.val) ⦄

namespace S2
theorem sign_spec [worker : Worker hash.Seed] [cpu : Armwide.Public.Dispatcher.Cpu] [features : Armwide.Keygen.Features] {N : Usize} (p : slhdsa.params.Params) (hp : PN p N)
    (m sk : Slice U8) (rnd : Array U8 N) (hsk : sk.length=4*N.val)
    (hm : Room m.length (msgSlack N.val))
    (worker_ok : WorkerCorrect worker (N:=N) p (paramsS p) (fun s => bytes s.pk_seed.val) SeedOk) :
    slh.slh_sign_internal p m sk rnd ⦃ out =>
      bytes out.val=Spec.slhSignInternal (paramsS p) (bytes m.val) (bytes sk.val) (bytes rnd.val) ∧
      out.length=(paramsS p).sigBytes ⦄ := by
  apply WP.spec_mono (P₀ := fun (out : alloc.vec.Vec U8) =>
    bytes out.val=Spec.slhSignInternal (paramsS p) (bytes m.val) (bytes sk.val) (bytes rnd.val))
  rotate_left
  · intro out value
    refine ⟨value,?_⟩
    have size := (congrArg List.length value).trans (Spec.slhSignInternal_length _ hp.valid _ _ _)
    exact (bytes_length _).symm.trans size
  have hv := hp.valid
  have hn := hp.le32
  have hmq := hv.m_eq
  simp only [paramsS_m] at hmq
  have hfl := fors_len_le p hp
  have hhl := ht_len_le p hp
  unfold S2.slh.slh_sign_internal
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
  let P := paramsS p
  simp only [vec_deref_val] at idx_tree_post idx_leaf_post
  have result : bytes r.val ++ Spec.forsSign P (bytes md.val) (bytes sk_seed.val) (bytes pk_seed.val) (adrsS adrs) ++
      Spec.htSign P (Spec.forsPkFromSig P (Spec.forsSign P (bytes md.val) (bytes sk_seed.val) (bytes pk_seed.val) (adrsS adrs))
        (bytes md.val) (bytes pk_seed.val) (adrsS adrs)) (bytes sk_seed.val) (bytes pk_seed.val) idx_tree.val idx_leaf.val =
      Spec.slhSignInternal P (bytes m.val) (bytes sk.val) (bytes rnd.val) := by
    simp only [Spec.slhSignInternal]
    rw [← hb0, ← hb1, ← hb2, ← hb3, ← r_post, ← digest_post, ← hmd, ← idx_tree_post, ← idx_leaf_post, ← hadrs]
  step with worker_ok md sk_seed seed adrs r idx_tree idx_leaf seed_ok (by rw [md_len,i_post1];omega)
    idx_tree_lt idx_leaf_lt hadrs as ⟨decision,certificate⟩
  cases decision with
  | some out =>
    simp only [WP.spec_ok]
    have delivered := output_fips P hp.valid _ _ _ _ _ _ _ _ idx_leaf_lt certificate
    simp only [seed_pk] at delivered
    exact delivered.trans result
  | none =>
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
    have hsig : bytes sg2.val = bytes r.val ++ bytes sig_fors.val ++ bytes sig_ht.val := by
      simp [sg2_post, sg1_post, sg0_post, s3_post]
    rw [seed_pk] at sig_fors_post pk_fors_post sig_ht_post
    simp only [vec_deref_val] at pk_fors_post
    rw [hsig,sig_ht_post,pk_fors_post,sig_fors_post]
    exact result

end S2
namespace Sh
open slhdsa.Shake
class FallbackCorrect (fallback : Fallback) {N : Usize} (p : slhdsa.params.Params) where
  forsSign (md : Slice U8) (sk pk : Array U8 N) (a : address.Adrs)
    (size : md.length=(p.k.val*p.a.val+7)/8)
    (domain : a.typ=address.FORS_TREE ∧ a.word2=0#u32 ∧ a.word3=0#u32) :
    fallback.forsSign p md sk pk a ⦃ r => bytes r.val=Spec.forsSign (Shake.params p) (bytes md.val)
      (bytes sk.val) (bytes pk.val) (adrsS a) ∧ r.length=p.k.val*(1+p.a.val)*N.val ⦄
  forsRecover (sig md : Slice U8) (pk : Array U8 N) (a : address.Adrs)
    (len : sig.length=p.k.val*(1+p.a.val)*N.val) (size : md.length=(p.k.val*p.a.val+7)/8)
    (domain : a.typ=address.FORS_TREE ∧ a.word2=0#u32 ∧ a.word3=0#u32) :
    fallback.forsRecover p sig md pk a ⦃ r => bytes r.val=Spec.forsPkFromSig (Shake.params p)
      (bytes sig.val) (bytes md.val) (bytes pk.val) (adrsS a) ⦄
  htSign (m sk pk : Array U8 N) (tree : U64) (leaf : U32) (bound : leaf.val<2^p.hp.val) :
    fallback.htSign p m sk pk tree leaf ⦃ r => bytes r.val=Spec.htSign (Shake.params p) (bytes m.val)
      (bytes sk.val) (bytes pk.val) tree.val leaf.val ∧ r.length=p.d.val*((2*N.val+3+p.hp.val)*N.val) ⦄

theorem scalar_correct {N : Usize} (p : slhdsa.params.Params) (hp : PN p N) :
    FallbackCorrect scalar (N:=N) p := ⟨fun md sk pk a size _ => Shake.fors_sign_spec p hp md sk pk a size,
      fun sig md pk a len size _ => Shake.fors_pk_from_sig_spec p hp sig md pk a len size,Shake.ht_sign_spec p hp⟩

theorem sign_spec [fallback : Fallback] [worker : Worker ShakeSeed] {N : Usize} (p : slhdsa.params.Params) (hp : PN p N)
    (m sk : Slice U8) (rnd : Array U8 N) (hsk : sk.length=4*N.val)
    (ops : FallbackCorrect fallback (N:=N) p)
    (worker_ok : WorkerCorrect worker (N:=N) p (Shake.params p) (fun s => bytes s.val) (fun _ => True)) :
    shake.slh.slh_sign_internal p m sk rnd ⦃ out =>
      bytes out.val=Spec.slhSignInternal (Shake.params p) (bytes m.val) (bytes sk.val) (bytes rnd.val) ∧
      out.length=(paramsS p).sigBytes ⦄ := by
  have pv : (Shake.params p).Valid := by obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_⟩ := hp.valid;constructor <;> assumption
  apply WP.spec_mono (P₀ := fun (out : alloc.vec.Vec U8) =>
    bytes out.val=Spec.slhSignInternal (Shake.params p) (bytes m.val) (bytes sk.val) (bytes rnd.val))
  rotate_left
  · intro out value
    refine ⟨value,?_⟩
    have size := (congrArg List.length value).trans (Spec.slhSignInternal_length _ pv _ _ _)
    exact (bytes_length _).symm.trans size
  have hv := hp.valid
  have hn := hp.le32
  have hmq := hv.m_eq
  simp only [paramsS_m] at hmq
  have hfl := fors_len_le p hp
  have hhl := ht_len_le p hp
  unfold Sh.shake.slh.slh_sign_internal
  let* ⟨ sk_seed, sk_seed_post ⟩ ← block_spec
  let* ⟨ sk_prf, sk_prf_post ⟩ ← block_spec
  let* ⟨ pk_seed, pk_seed_post ⟩ ← block_spec
  let* ⟨ pk_root, pk_root_post ⟩ ← block_spec
  let* ⟨ r, r_post ⟩ ← prf_msg_params p hp
  let* ⟨ digest, digest_post, digest_len ⟩ ← h_msg_params p
  let* ⟨ idx_tree, idx_tree_post, idx_tree_lt ⟩ ← Shake.digest_tree_spec
  let* ⟨ idx_leaf, idx_leaf_post, idx_leaf_lt ⟩ ← Shake.digest_leaf_spec
  let* ⟨ a, a_post ⟩ ← adrs_new_spec
  let* ⟨ a1, a1_post ⟩ ← with_tree_spec
  let* ⟨ a2, a2_post, a2_post1 ⟩ ← with_type_spec
  let* ⟨ adrs, adrs_post ⟩ ← with_keypair_spec
  simp only [shake.hash.seed_ctx, bind_ok]
  let* ⟨ i, i_post, i_post1 ⟩ ← md_bytes_spec
  let* ⟨ md, md_post, md_len ⟩ ← alloc.vec.Vec.index_Range_spec
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
  let P := Shake.params p
  simp only [vec_deref_val] at idx_tree_post idx_leaf_post
  have result : bytes r.val ++ Spec.forsSign P (bytes md.val) (bytes sk_seed.val) (bytes pk_seed.val) (adrsS adrs) ++
      Spec.htSign P (Spec.forsPkFromSig P (Spec.forsSign P (bytes md.val) (bytes sk_seed.val) (bytes pk_seed.val) (adrsS adrs))
        (bytes md.val) (bytes pk_seed.val) (adrsS adrs)) (bytes sk_seed.val) (bytes pk_seed.val) idx_tree.val idx_leaf.val =
      Spec.slhSignInternal P (bytes m.val) (bytes sk.val) (bytes rnd.val) := by
    simp only [Spec.slhSignInternal]
    simp only [show Spec.block P=Spec.block (paramsS p) by rfl,show P.mdBytes=(paramsS p).mdBytes by rfl,
      show Spec.digestTree P=Spec.digestTree (paramsS p) by rfl,show Spec.digestLeaf P=Spec.digestLeaf (paramsS p) by rfl]
    rw [← hb0, ← hb1, ← hb2, ← hb3, ← r_post, ← digest_post, ← hmd, ← idx_tree_post, ← idx_leaf_post, ← hadrs]
  step with worker_ok md sk_seed pk_seed adrs r idx_tree idx_leaf trivial (by change md.length=(paramsS p).mdBytes;rw [md_len,i_post1];omega)
    idx_tree_lt idx_leaf_lt hadrs as ⟨decision,certificate⟩
  cases decision with
  | some out =>
    simp only [WP.spec_ok]
    have delivered := output_fips P pv _ _ _ _ _ _ _ _ idx_leaf_lt certificate
    exact delivered.trans result
  | none =>
    have domain : adrs.typ=address.FORS_TREE ∧ adrs.word2=0#u32 ∧ adrs.word3=0#u32 := by simp [adrs_post,a2_post1]
    have small : md.length=(p.k.val*p.a.val+7)/8 := by rw [md_len,i_post];omega
    let* ⟨ sig_fors, sig_fors_post, sig_fors_len ⟩ ← ops.forsSign md sk_seed pk_seed adrs small domain
    let* ⟨ pk_fors, pk_fors_post ⟩ ← ops.forsRecover (alloc.vec.Vec.deref sig_fors) md pk_seed adrs (by simpa only [vec_deref_length] using sig_fors_len) small domain
    let* ⟨ sig_ht, sig_ht_post, sig_ht_len ⟩ ← ops.htSign pk_fors sk_seed pk_seed idx_tree
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
    have hsig : bytes sg2.val = bytes r.val ++ bytes sig_fors.val ++ bytes sig_ht.val := by
      simp [sg2_post, sg1_post, sg0_post, s3_post]
    simp only [vec_deref_val] at pk_fors_post
    rw [hsig,sig_ht_post,pk_fors_post,sig_fors_post]
    exact result

end Sh

end slhdsa.ParallelCaller
