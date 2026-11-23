import Rcni.Block
import Armstream.Proof
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.Intel.RustCrypto
open RcNiRust RcNiRust.sha256.x86_sha X86.Stream
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000

private theorem bodySome (it next : core.slice.iter.Iter (Array U8 64#usize)) (x y : Reg)
    (block : Array U8 64#usize)
    (read : core.slice.iter.IteratorSliceIter.next it = ok (some block,next)) :
    compress_loop.body it x y = blockStep (fun a b => cont (next,a,b)) block x y := by
  simp only [compress_loop.body,read,bind_ok]
  rfl

theorem loop_spec (blocks : Slice (Array U8 64#usize)) (x y : Reg) :
    compress_loop ⟨blocks,0⟩ x y ⦃ a b => stateWords (decode a b)=fold256 (stateWords (decode x y)) blocks.val ⦄ := by
  let iv := stateWords (decode x y)
  unfold compress_loop
  apply loop.spec_decr_nat
    (measure := fun q : core.slice.iter.Iter (Array U8 64#usize) × Reg × Reg => blocks.length-q.1.i)
    (inv := fun q => q.1.slice=blocks ∧ q.1.i≤blocks.length ∧ stateWords (decode q.2.1 q.2.2)=fold256 iv (blocks.val.take q.1.i))
  · rintro ⟨it,a,b⟩ ⟨slice,bound,prior⟩
    simp only at slice bound prior
    simp only
    by_cases more : it.i < blocks.val.length
    · let next := {it with i := it.i+1}
      have index : it.i < it.slice.len.val := by simpa [slice] using more
      have get : core.slice.iter.IteratorSliceIter.next it = ok (some blocks.val[it.i],next) := by
        simp [core.slice.iter.IteratorSliceIter.next,index,next,slice,more,Slice.length]
      rw [bodySome _ _ _ _ _ get]
      apply WP.spec_mono (block_spec _ _ _ _)
      rintro _ ⟨u,v,rfl,hash⟩
      refine ⟨⟨slice,by change it.i+1 ≤ blocks.val.length; omega,?_⟩,by change blocks.val.length-(it.i+1) < blocks.val.length-it.i; omega⟩
      rw [hash,prior]
      change _ = fold256 iv (blocks.val.take (it.i+1))
      rw [List.take_succ_eq_append_getElem more]
      simp only [fold256,List.foldl_append,List.foldl_cons,List.foldl_nil]
    · have get : core.slice.iter.IteratorSliceIter.next it = ok (none,it) := by
        simp [core.slice.iter.IteratorSliceIter.next,slice,more,Slice.length]
      simp only [compress_loop.body,get,bind_ok,step_simps]
      simpa [List.take_of_length_le (Nat.le_of_not_gt more)] using prior
  · exact ⟨rfl,Nat.zero_le _,rfl⟩

private theorem align8 (a b : Reg) :
    core.core_arch.x86.ssse3._mm_alignr_epi8 8#i32 a b = ok ⟨b.w2,b.w3,a.w0,a.w1⟩ := by
  cases a; cases b
  simp [core.core_arch.x86.ssse3._mm_alignr_epi8,get]

private theorem blend240 (a b : Reg) :
    ChainNiRust.core.core_arch.x86.sse41._mm_blend_epi16 240#i32 a b = ok ⟨a.w0,a.w1,b.w2,b.w3⟩ := by
  cases a; cases b
  simp [ChainNiRust.core.core_arch.x86.sse41._mm_blend_epi16,get]
  simp only [show 4294967295#32 = BitVec.allOnes 32 from rfl,BitVec.and_allOnes,and_self]

theorem compress_spec (state : Array U32 8#usize) (blocks : Slice (Array U8 64#usize)) :
    compress state blocks ⦃ out => wv out.val=fold256 (wv state.val) blocks.val ⦄ := by
  unfold compress
  simp only [load_state, bind_ok]
  step as ⟨d,hd⟩
  step as ⟨h,hh⟩
  simp only [bind_ok,bind_tc_eq,
    core.core_arch.x86.sse2._mm_shuffle_epi32, align8, RcNiRust.core.core_arch.x86.sse41._mm_blend_epi16,blend240,
    SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter]
  step with loop_spec as ⟨u,v,hash⟩
  simp only [step_simps,core.core_arch.x86.sse2._mm_shuffle_epi32,align8,blend240,store_state]
  apply Eq.trans _ (Eq.trans hash _)
  · cases u; cases v
    rfl
  · apply congrArg (fun words => fold256 words blocks.val)
    rw [hd,hh]
    apply List.ext_getElem
    · simp [stateWords,wv,decode]
    · intro k _ hk
      have h : k<8 := by simpa [wv] using hk
      interval_cases k <;> simp_all [stateWords,wv,decode,get,Array.make,Memory.readState]

/-- Any total-correctness contract proved for the scalar bulk model also holds
for the locked SHA-NI implementation on its supported instruction set. -/
theorem refines_bulk (state : Array U32 8#usize) (blocks : Slice (Array U8 64#usize))
    (P : Array U32 8#usize → Prop)
    (contract : ArmStreamRust.sha2.sha256.compress256 state blocks ⦃ P ⦄) :
    compress state blocks ⦃ P ⦄ := by
  obtain ⟨other,good,spec⟩ := WP.spec_exists (WP.spec_and contract (PlatformStream.bulk256 state blocks))
  apply WP.spec_mono (compress_spec state blocks)
  intro out same
  suffices out = other by simpa [this] using good
  apply Aeneas.Std.Array.ext
  have := congrArg (List.map (fun w : Word => (⟨w⟩ : U32))) (same.trans spec.symm)
  simpa [wv,List.map_map,Function.comp_def] using this

#print axioms refines_bulk
#print axioms compress_spec
end slhdsa.Intel.RustCrypto
