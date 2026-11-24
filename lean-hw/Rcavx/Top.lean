import Rcavx.Block
import Armstream.Proof
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.RustCrypto512
open RcAvxRust RcAvxRust.sha512.x86_avx2 Stream
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

private theorem chunks (b : Slice Block) :
    RcAvxRust.core.slice.Slice.as_rchunks 2#usize b ⦃ head gs =>
      head.val.length ≤ 1 ∧ head.val ++ gs.val.flatMap (·.val) = b.val ⦄ := by
  unfold RcAvxRust.core.slice.Slice.as_rchunks
  simp only [show (2#usize).val=2 by rfl,show (2:Nat)≠0 by decide,ite_false,Slice.from_val,step_simps]
  let tail := Slice.from (b.val.drop (b.length%2)) (by have := b.property; simp; omega)
  have trm : (ChainAvx2Rust.remainder 2#usize tail).val=[] := by
    simp only [ChainAvx2Rust.remainder,Slice.from_val]
    have even : tail.val.length%2=0 := by simp [tail,Slice.length]; omega
    apply List.drop_eq_nil_of_le
    change tail.val.length ≤ 2*(tail.val.length/2)
    omega
  have join := ChainAvx2Rust.chunk_parts tail 2#usize
  rw [trm,List.append_nil] at join
  constructor
  · simp [Slice.length]; omega
  · change b.val.take (b.length%2) ++ (ChainAvx2Rust.fullChunks 2#usize tail).val.flatMap (·.val) = _
    rw [join]; simp only [tail,Slice.from_val,List.take_append_drop]

private theorem groups_fold (groups : List Group) (s : List Spec.SHA512.Word) :
    groups.foldl (fun st g => fold512 st g.val) s = fold512 s (groups.flatMap (·.val)) := by
  induction groups generalizing s with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons,ih,List.flatMap_cons]
    simp only [fold512,List.foldl_append]

theorem compress_spec (st : St) (blocks : Slice Block) :
    compress st blocks ⦃ out => slhdsa.S512.wv out.val = fold512 (slhdsa.S512.wv st.val) blocks.val ⦄ := by
  unfold compress
  simp only [RcAvxRust.core.core_arch.x86.sse2._mm_setzero_si128,RcAvxRust.core.core_arch.x86.avx._mm256_setzero_si256,bind_ok]
  step with chunks blocks as ⟨head,groups,size,join⟩
  have odd : (if head.len=1#usize then do
      let b ← Slice.index_usize head 0#usize
      sha512_compress_x86_64_avx st b
    else ok st) ⦃ out => slhdsa.S512.wv out.val=fold512 (slhdsa.S512.wv st.val) head.val ⦄ := by
    split
    · rename_i one
      have oneN : head.val.length=1 := by scalar_tac
      step as ⟨block,read⟩
      apply WP.spec_mono (single st block)
      intro out hash
      rw [hash]
      have shape : head.val=[block] := by
        apply List.ext_getElem
        · simpa using oneN
        · intro k hk _
          have zero : k=0 := by omega
          subst k
          simpa using read.symm
      simp only [shape,fold512,List.foldl_cons,List.foldl_nil]
    · have empty : head.val=[] := by
        apply List.length_eq_zero_iff.mp
        by_contra hn
        have eq : head.len=1#usize := by scalar_tac
        contradiction
      simp only [empty,step_simps,fold512,List.foldl_nil]
  step with odd as ⟨s,hashed⟩
  simp only [SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter,bind_ok]
  apply WP.spec_mono (paired_loop groups s _ _ _)
  intro out h
  rw [h,groups_fold,hashed,← join]
  simp only [fold512,List.foldl_append]

theorem refines_bulk (st : St) (blocks : Slice Block) (P : St → Prop)
    (h : ArmStreamRust.sha2.sha512.compress512 st blocks ⦃ P ⦄) :
    compress st blocks ⦃ P ⦄ := by
  obtain ⟨model,good,hash⟩ := WP.spec_exists (WP.spec_and h (PlatformStream.bulk512 st blocks))
  apply WP.spec_mono (compress_spec st blocks)
  intro out same
  suffices out=model by simpa [this] using good
  apply Aeneas.Std.Array.ext
  have := congrArg (List.map (fun x : BitVec 64 => (⟨x⟩ : U64))) (same.trans hash.symm)
  simpa [slhdsa.S512.wv,List.map_map,Function.comp_def] using this

#print axioms refines_bulk
end slhdsa.X86.RustCrypto512
