import Kbulk.Absorb
open Aeneas Aeneas.Std Result ControlFlow
open Spec.Keccak
namespace slhdsa.Oriented.Bulk
open KbulkRust.shake256
set_option maxHeartbeats 3000000

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

private def inputBytes (xs : List (Slice U8)) := xs.flatMap (fun x => bytes x.val)

private theorem chunks (s : Slice U8) (whole : s.length%136=0) :
    core.slice.Slice.chunks_exact s KbulkRust.shake256.RATE ⦃ it =>
      inputBytes it.chunks = bytes s.val ∧ ∀ c ∈ it.chunks, c.length=136 ⦄ := by
  unfold KbulkRust.shake256.RATE core.slice.Slice.chunks_exact
  simp only [show (136#usize).val = 136 by rfl,
    show 0<136 by decide,_root_.dite_true,step_simps]
  obtain ⟨flat,lens⟩ := pieces s.val whole
  constructor
  · unfold inputBytes bytes
    with_unfolding_all simpa only [show (136#usize).val = 136 by rfl,List.flatMap_map,Function.comp_def,Slice.from_val,List.flatMap_def, List.map_map, List.attach_map_val, List.map_flatten] using congrArg (List.map (fun x : U8 => x.bv)) flat
  · intro c hc
    obtain ⟨⟨v,hv⟩,_,rfl⟩ := List.mem_map.mp hc
    simpa [Slice.length] using lens v hv

private theorem permuteRounds (a : Array U64 25#usize) :
    oriented.blocks_loop0_loop1 ⟨Slice.from KbulkRust.shake256.RC.val (by scalar_tac),0⟩ a ⦃ out =>
      decode out = permute (decode a) ⦄ := by
  have constants : KbulkRust.shake256.RC.val.map (·.bv) = rc.toList := by
    unfold KbulkRust.shake256.RC rc; rfl
  have imp := rounds a (Slice.from KbulkRust.shake256.RC.val (by scalar_tac))
  simp only [Slice.from_val,constants] at imp
  exact imp

private theorem allBlocks (it : core.slice.iter.ChunksExact U8) (a : Array U64 25#usize)
    (size : ∀ c ∈ it.chunks, c.length = 136) :
    oriented.blocks_loop0 it a ⦃ out =>
      (decode out,0) = (inputBytes it.chunks).foldl feed (decode a,0) ⦄ := by
  unfold oriented.blocks_loop0
  apply loop.spec_decr_nat
    (measure := fun (p : core.slice.iter.ChunksExact U8 × Array U64 25#usize) => p.1.chunks.length)
    (inv := fun p => (∀ c ∈ p.1.chunks, c.length=136) ∧
      (inputBytes p.1.chunks).foldl feed (decode p.2,0) =
        (inputBytes it.chunks).foldl feed (decode a,0))
  · rintro ⟨cur,state⟩ ⟨lens,same⟩
    simp only at lens same ⊢
    unfold oriented.blocks_loop0.body core.slice.iter.IteratorChunksExact.next
    cases h : cur.chunks with
    | nil => simpa [h,inputBytes,step_simps] using same
    | cons c rest =>
      have sz := lens c (by simp [h])
      simp only [bind_ok]
      step with blockWords c state sz as ⟨x,hx⟩
      simp only [SharedArray.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter,bind_ok]
      step with permuteRounds x as ⟨out,post⟩
      refine ⟨fun v hv => lens v (by simp [h,hv]),?_,by simp [h]⟩
      simp only [h,inputBytes,List.flatMap_cons,List.foldl_append] at same
      simpa only [inputBytes,post,hx] using same
  · exact ⟨size,rfl⟩

theorem blocks_fips (state : Array U64 25#usize) (data : Slice U8) (whole : data.length%136=0) :
    oriented.blocks state data ⦃ out =>
      (Keccak.words out,0) = (bytes data.val).foldl feed (Keccak.words state,0) ⦄ := by
  unfold oriented.blocks
  have initEq : @oriented.blocks.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64 =
      @KorientedRust.shake256.oriented.permute.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64 := by
    with_unfolding_all rfl
  rw [initEq]
  step with start state as ⟨s,hs⟩
  step with chunks data whole as ⟨it,hb,sz⟩
  step with allBlocks it s sz as ⟨p,hp⟩
  have endEq : @oriented.blocks_loop1 = @KorientedRust.shake256.oriented.permute_loop1 := by
    with_unfolding_all rfl
  rw [endEq]
  step with finish p state as ⟨out,ho⟩
  simpa only [ho,hs,hb] using hp
end slhdsa.Oriented.Bulk
