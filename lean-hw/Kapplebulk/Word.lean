import Kapplebulk.Funs
import Kappleperm.Proof
import Shakeabs.Word
open Aeneas Aeneas.Std Result Spec.Keccak
namespace slhdsa.Kapplebulk
open Ksha3 (Rows lane)
open KapplebulkRust.core.core_arch.arm_shared.neon.generated
set_option maxHeartbeats 2000000

def load (a : Rows) (block : Slice U8) (k : Usize) : Result Rows := do
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
  a.update k y

private theorem setLane (a : Rows) (k : Usize) (v : Ksha3.Reg) (hk : k.val<25) :
    lane (a.set k v) 0 = (lane a 0).setIfInBounds k.val (v 0) := by
  apply ext25 _ _ (by simp [lane]) (by simp [lane])
  intro i hi
  unfold lane
  rw [ofFnAt _ _ hi]
  rw [getElem!_pos ((_root_.Array.ofFn (n := 25) fun i => a.val[i.val]! 0).setIfInBounds k.val (v 0)) i (by simpa using hi),_root_.Array.getElem_setIfInBounds (by simpa using hi)]
  rw [Array.set_val_eq,getElem!_pos _ _ (by simp; omega),List.getElem_set]
  split <;> rename_i eq
  · rfl
  · simp only [_root_.Array.getElem_ofFn,getElem!_pos a.val i (by simpa using hi)]

def remaining (a : Rows) (block : Slice U8) (i : Nat) :=
  ((bytes block.val).drop (8*i)).foldl feed (if i=17 then (permute (lane a 0),0) else (lane a 0,8*i))

theorem load_spec (a : Rows) (block : Slice U8) (k : Usize) (hk : k.val<17) (size : block.length=136) :
    load a block k ⦃ out => remaining out block (k.val+1) = remaining a block k.val ⦄ := by
  unfold load
  step as ⟨lo,hl⟩
  step as ⟨n,hn⟩
  step as ⟨hi,hh⟩
  step as ⟨s,sub,len⟩
  have eight : s.length=8 := by scalar_tac
  simp only [core.array.TryFromArrayCopySlice.try_from,show s.length=(8#usize).val by exact eight,
    _root_.dite_true,core.result.Result.unwrap,bind_ok,lift,vdupq_n_u64,veorq_u64,
    Ksha3Rust.core.core_arch.arm_shared.neon.generated.vdupq_n_u64,
    Ksha3Rust.core.core_arch.arm_shared.neon.generated.veorq_u64]
  step as ⟨v,hv⟩
  step as ⟨out,hout⟩
  let input := Array.from s.val (show s.val.length=(8#usize).val by exact eight)
  have data : (bytes block.val).drop (8*k.val) = bytes s.val ++ (bytes block.val).drop (8*(k.val+1)) := by
    rw [sub,List.slice,bytes_take,bytes_drop,hh,hn,hl,show 8*(k.val+1)-8*k.val=8 by omega,
      show 8*(k.val+1)=8*k.val+8 by omega,← List.drop_drop]
    exact (List.take_append_drop _ _).symm
  have fed := feedWord (lane a 0) k.val (bytes s.val) (by simpa using eight) (by simp [lane]; omega) hk
  dsimp only at fed
  unfold remaining
  rw [if_neg (by omega : k.val≠17),data,List.foldl_append,fed,hout,setLane _ _ _ (by omega)]
  simp only [hv,PlatformShake.loaded,Array.from_val]
  unfold lane
  rw [ofFnAt _ _ (by omega)]
  simp only [getElem!_pos a.val k.val (by simp; omega)]
  by_cases last : k.val=16
  · simp [last]
  · simp [last,show k.val+1≠17 by omega,Nat.mul_succ]
end slhdsa.Kapplebulk
