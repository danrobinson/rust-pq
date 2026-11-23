import Kapplebulk.Word
import Kbulk.Top
open Aeneas Aeneas.Std Result ControlFlow Spec.Keccak
namespace slhdsa.Kapplebulk
open Ksha3 (Rows lane)
open KapplebulkRust.shake256.parallel
open KapplebulkRust.core.core_arch.arm_shared.neon.generated
set_option maxHeartbeats 8000000
set_option maxRecDepth 32768

private theorem nextWord {α : Type} (a : Rows) (block : Slice U8) (k : Usize)
    (hk : k.val<17) (size : block.length=136) (cont : Rows → Result α) (P : α → Prop)
    (rest : ∀ b, remaining b block (k.val+1) = remaining a block k.val → cont b ⦃ out => P out ⦄) :
    (do
    let lo ← 8#usize*k
    let n ← k+1#usize
    let hi ← 8#usize*n
    let s ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8) block ⟨lo,hi⟩
    let r ← core.array.TryFromArrayCopySlice.try_from 8#usize core.marker.CopyU8 s
    let b ← core.result.Result.unwrap core.fmt.DebugTryFromSliceError r
    let w ← lift (core.num.U64.from_le_bytes b)
    let x ← a.index_usize k
    let dup ← vdupq_n_u64 w
    let y ← veorq_u64 x dup
    let out ← a.update k y
    cont out) ⦃ out => P out ⦄ := by
  have combined := WP.spec_bind (load_spec a block k hk size) rest
  simpa only [load, bind_tc_eq, Std.bind_assoc] using combined

private theorem permuteRounds (a : Rows) :
    sha3.blocks_loop0_loop0 ⟨Slice.from KapplebulkRust.shake256.RC.val (by scalar_tac),0⟩ a ⦃ out =>
      lane out 0 = permute (lane a 0) ⦄ := by
  have constants : KapplebulkRust.shake256.RC.val.map (·.bv) = rc.toList := by unfold KapplebulkRust.shake256.RC rc; rfl
  apply WP.spec_mono (Kappleperm.rounds a (Slice.from KapplebulkRust.shake256.RC.val (by scalar_tac)))
  intro out h
  specialize h 0
  simp only [Slice.from_val,constants] at h
  rw [h]
  rfl

private theorem pieces (xs : List U8) (whole : xs.length%136=0) :
    let chunks := (List.toChunksExact 136 (by decide) xs).1
    chunks.flatten = xs ∧ ∀ chunk ∈ chunks, chunk.length = 136 := by
  dsimp only
  rw [List.toChunksExact]
  split
  · have notLong : xs.length < 136 := by assumption
    have z : xs.length = 0 := by omega
    have e : xs=[] := List.length_eq_zero_iff.mp z
    simp [e]
  · have enough : 136 ≤ xs.length := by omega
    have ⟨all,size⟩ := pieces (xs.drop 136) (by simp; omega)
    simp only [List.flatten_cons,all,List.take_append_drop,true_and,List.mem_cons]
    intro c hc
    rcases hc with rfl | hc
    · simp [List.length_take,enough]
    · exact size c hc
termination_by xs.length
decreasing_by simp; omega

def inputBytes (xs : List (Slice U8)) := xs.flatMap (fun x => bytes x.val)

theorem chunks (s : Slice U8) (whole : s.length%136=0) :
    core.slice.Slice.chunks_exact s KapplebulkRust.shake256.RATE ⦃ it =>
      inputBytes it.chunks = bytes s.val ∧ ∀ c ∈ it.chunks, c.length=136 ⦄ := by
  unfold KapplebulkRust.shake256.RATE core.slice.Slice.chunks_exact
  simp only [show (136#usize).val = 136 by rfl,
    show 0<136 by decide,_root_.dite_true,step_simps]
  obtain ⟨flat,lens⟩ := pieces s.val whole
  constructor
  · unfold inputBytes bytes
    with_unfolding_all simpa only [show (136#usize).val = 136 by rfl,List.flatMap_map,Function.comp_def,Slice.from_val,List.flatMap_def, List.map_map, List.attach_map_val, List.map_flatten] using congrArg (List.map (fun x : U8 => x.bv)) flat
  · intro c hc
    obtain ⟨⟨v,hv⟩,_,rfl⟩ := List.mem_map.mp hc
    simpa [Slice.length] using lens v hv

theorem allBlocks (it : core.slice.iter.ChunksExact U8) (a : Rows)
    (size : ∀ c ∈ it.chunks, c.length = 136) :
    sha3.blocks_loop0 it a ⦃ out =>
      (lane out 0,0) = (inputBytes it.chunks).foldl feed (lane a 0,0) ⦄ := by
  unfold sha3.blocks_loop0
  apply loop.spec_decr_nat
    (measure := fun (p : core.slice.iter.ChunksExact U8 × Rows) => p.1.chunks.length)
    (inv := fun p => (∀ c ∈ p.1.chunks, c.length=136) ∧
      (inputBytes p.1.chunks).foldl feed (lane p.2 0,0) =
        (inputBytes it.chunks).foldl feed (lane a 0,0))
  · rintro ⟨cur,state⟩ ⟨lens,same⟩
    simp only at lens same ⊢
    unfold sha3.blocks_loop0.body core.slice.iter.IteratorChunksExact.next
    cases h : cur.chunks with
    | nil => simpa [h,inputBytes,step_simps] using same
    | cons c rest =>
      have sz := lens c (by simp [h])
      simp only [bind_ok]
      apply nextWord state c 0#usize (by decide) sz
      intro b1 h1
      apply nextWord b1 c 1#usize (by decide) sz
      intro b2 h2
      apply nextWord b2 c 2#usize (by decide) sz
      intro b3 h3
      apply nextWord b3 c 3#usize (by decide) sz
      intro b4 h4
      apply nextWord b4 c 4#usize (by decide) sz
      intro b5 h5
      apply nextWord b5 c 5#usize (by decide) sz
      intro b6 h6
      apply nextWord b6 c 6#usize (by decide) sz
      intro b7 h7
      apply nextWord b7 c 7#usize (by decide) sz
      intro b8 h8
      apply nextWord b8 c 8#usize (by decide) sz
      intro b9 h9
      apply nextWord b9 c 9#usize (by decide) sz
      intro b10 h10
      apply nextWord b10 c 10#usize (by decide) sz
      intro b11 h11
      apply nextWord b11 c 11#usize (by decide) sz
      intro b12 h12
      apply nextWord b12 c 12#usize (by decide) sz
      intro b13 h13
      apply nextWord b13 c 13#usize (by decide) sz
      intro b14 h14
      apply nextWord b14 c 14#usize (by decide) sz
      intro b15 h15
      apply nextWord b15 c 15#usize (by decide) sz
      intro b16 h16
      apply nextWord b16 c 16#usize (by decide) sz
      intro b17 h17
      simp only [SharedArray.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter,bind_ok]
      step with permuteRounds b17 as ⟨out,post⟩
      have endEq : remaining b17 c 17 = remaining state c 0 := by
        exact h17.trans (h16.trans (h15.trans (h14.trans (h13.trans (h12.trans (h11.trans (h10.trans (h9.trans (h8.trans (h7.trans (h6.trans (h5.trans (h4.trans (h3.trans (h2.trans h1)))))))))))))))
      have blockEq : (lane out 0,0) = (bytes c.val).foldl feed (lane state 0,0) := by
        simpa [remaining,post,List.drop_eq_nil_of_le (show (bytes c.val).length≤136 by simpa using sz.le)] using endEq
      refine ⟨fun v hv => lens v (by simp [h,hv]),?_,by simp [h]⟩
      simp only [h,inputBytes,List.flatMap_cons,List.foldl_append] at same
      simpa only [inputBytes,blockEq] using same
  · exact ⟨size,rfl⟩

end slhdsa.Kapplebulk
