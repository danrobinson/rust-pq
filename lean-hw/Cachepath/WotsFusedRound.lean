import Cachepath.WotsFusedProgram
import Shakebatch.WotsLayout
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.cache.builder.nativeShake.Vector.Fused
open ShakeBatch
set_option linter.concreteInstances false
variable [machine : Machine]

def addressLow (x : U32) : BitVec 64 :=
  (x.bv.extractLsb' 0 8 ++ x.bv.extractLsb' 8 8 ++ x.bv.extractLsb' 16 8 ++ x.bv.extractLsb' 24 8).zeroExtend 64

def compose (input state : Matrix machine.width) (count offset : Nat) (tag : BitVec 64) (k j : Nat) :=
  if offset ≤ k ∧ k < offset+count then cell state (k-offset) j
  else if k=offset-1 then tag else cell input k j

def round (count offset : Usize) (id : U64) (index : U32) (input state : Matrix machine.width) :
    Result (Matrix machine.width × Matrix machine.width) := do
  let swapped ← core.num.U32.swap_bytes index
  let hi ← lift (core.convert.num.FromU64U32.from swapped)
  let hi ← hi <<< 32#i32
  let tag ← lift (id ||| hi)
  let last ← offset - 1#usize
  let tagged ← Array.update input last (Array.repeat machine.width tag)
  let stop ← offset + count
  let dstBack ← core.array.Array.index_mut (core.ops.index.IndexMutSlice
    (core.slice.index.SliceIndexRangeUsizeSlice (Array U64 machine.width))) tagged ⟨offset,stop⟩
  let src ← core.array.Array.index (core.ops.index.IndexSlice
    (core.slice.index.SliceIndexRangeToUsizeSlice (Array U64 machine.width))) state ⟨count⟩
  let copied ← core.slice.Slice.copy_from_slice (Array.Insts.CoreMarkerCopy machine.width core.marker.CopyU64) dstBack.1 src
  let packed := dstBack.2 copied
  let hashed ← machine.permute packed
  ok (packed,hashed)

theorem write_tag (s : Matrix machine.width) (atRow : Usize) (tag : U64) (hr : atRow.val<25)
    (k j : Nat) (hj : j<machine.width.val) : cell (s.set atRow (Array.repeat machine.width tag)) k j =
      if k=atRow.val then tag.bv else cell s k j := by
  unfold cell
  rw [Array.set_val_eq]
  by_cases same : k=atRow.val
  · subst k; rw [setSame _ _ _ (by simpa using hr),Array.repeat_val]; simp [hj]
  · rw [setOther _ _ _ _ (Ne.symm same),ite_eq_right same]

theorem round_spec (count offset : Usize) (id : U64) (index : U32) (input state : Matrix machine.width)
    (pos : 0<offset.val) (fits : offset.val+count.val≤25) (permutes : PermutationCorrect) :
    round count offset id index input state ⦃ packed hashed =>
      (∀ k<25, ∀ j<machine.width.val, cell packed k j=compose input state count.val offset.val (id.bv ||| wordTag index) k j) ∧
      ∀ j<machine.width.val, ShakeBatch.lane hashed j=Spec.Keccak.permute (ShakeBatch.lane packed j) ⦄ := by
  unfold round
  simp only [core.num.U32.swap_bytes,lift,bind_ok]
  step as ⟨hi,_,hibv⟩
  step as ⟨last,lastv⟩
  step as ⟨tagged,hTag⟩
  step as ⟨stop,stopv⟩
  step as ⟨dstBack,_,dstLen,write⟩
  step as ⟨src,srcVal,srcLen⟩
  step as ⟨copied,cp⟩
  all_goals try omega
  step with permutes (dstBack.2 copied) as ⟨hashed,permed⟩
  refine ⟨?_,permed⟩
  intro k hk j hj
  subst copied
  have tl := write_tag input last (id ||| hi) (by omega) k j hj
  have tagEq : (id ||| hi).bv = id.bv ||| wordTag index := congrArg (fun t : BitVec 64 => id.bv ||| t) hibv
  rw [hTag] at write
  unfold compose
  by_cases inside : offset.val ≤ k ∧ k < offset.val+count.val
  · rw [ite_eq_left inside]
    simp only [cell,write]
    rw [List.getElem!_setSlice!_middle _ _ _ _ (by simp;change _ ∧ _ < src.length ∧ _ < 25;omega),srcVal,Array.val_to_slice,
      List.getElem!_slice _ _ _ _ (by simp;omega),Nat.zero_add]
  · simp only [inside,ite_false,cell,write]
    rw [lastv] at tl
    rw [← tagEq]
    by_cases front : k < offset.val
    · rw [List.getElem!_setSlice!_prefix _ _ _ _ front]
      exact tl
    · rw [List.getElem!_setSlice!_suffix _ _ _ _ (by change _ + src.length ≤ k;omega)]
      exact tl

private theorem round_body (count offset : Usize) (id : U64) (it : core.ops.range.Range U32)
    (input state : Matrix machine.width) : generate_loop0_loop0.body count offset id it input state =
    (do let (o,next) ← core.iter.range.IteratorRange.next core.iter.range.StepU32 it
        match o with
        | none => ok (done (input,state))
        | some ix => do
          let (packed,hashed) ← round count offset id ix input state
          ok (cont (next,packed,hashed))) := by
  unfold generate_loop0_loop0.body
  congr 1
  funext q
  rcases q with ⟨o,next⟩
  cases o <;> simp [round,Std.bind_assoc]
  rfl

theorem rounds {P : Nat → Matrix machine.width → Matrix machine.width → Prop}
    (count offset : Usize) (id : U64) (input state : Matrix machine.width) (init : P 0 input state)
    (each : ∀ (i : U32) (old dig : Matrix machine.width), i.val<15 → P i.val old dig →
      round count offset id i old dig ⦃ packed hashed => P (i.val+1) packed hashed ⦄) :
    generate_loop0_loop0 count ⟨0#u32,15#u32⟩ offset input id state ⦃ a b => P 15 a b ⦄ := by
  unfold generate_loop0_loop0
  apply loop.spec_decr_nat (measure := fun q : core.ops.range.Range U32 × Matrix machine.width × Matrix machine.width => 15-q.1.start.val)
    (inv := fun q => q.1.end=15#u32 ∧ q.1.start.val≤15 ∧ P q.1.start.val q.2.1 q.2.2)
  · rintro ⟨it,st,dig⟩ ⟨stop,within,inv⟩
    simp only at stop within inv ⊢
    rw [round_body]
    by_cases more : it.start.val < it.end.val
    · have live : it.start.val < 15 := by rw [stop] at more; exact more
      step with core.iter.range.IteratorRange.next_U32_some_spec it more as ⟨o,next,ho,bump,e⟩
      simp only [ho]
      step with each it.start st dig live inv as ⟨packed,hashed,spec⟩
      exact ⟨e.trans stop,by omega,by simpa only [bump] using spec,by omega⟩
    · step with core.iter.range.IteratorRange.next_U32_none_spec it (by omega) as ⟨o,_,ho,_⟩
      simp only [ho,step_simps]
      have finished : it.start.val=15 := by rw [stop] at more; change ¬it.start.val<15 at more; omega
      simpa only [finished] using inv
  · exact ⟨rfl,by simp,init⟩

end slhdsa.cache.builder.nativeShake.Vector.Fused
