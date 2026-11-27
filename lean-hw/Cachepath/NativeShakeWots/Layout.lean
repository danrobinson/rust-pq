import Cachepath.NativeShakeWots.Pack
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.NativeShakeWots
open ShakeBatch NativeVerify.Wots
set_option linter.concreteInstances false
variable [machine : Machine]

/-- Common suffix of the two translated register writes. -/
noncomputable def header (n offset : Usize) (state1 : Matrix machine.width) (w0 w1 : U64)
    (w2 w3 : Array U64 machine.width) : Result (Matrix machine.width) := do
  let a := Array.repeat machine.width w0
  let state2 ← Array.update state1 n a
  let i ← n + 1#usize
  let a1 := Array.repeat machine.width w1
  let state3 ← Array.update state2 i a1
  let i1 ← n + 2#usize
  let state4 ← Array.update state3 i1 w2
  let i2 ← n + 3#usize
  let state5 ← Array.update state4 i2 w3
  let pad ← offset + n
  let a2 := Array.repeat machine.width 31#u64
  let state6 ← Array.update state5 pad a2
  let i3 ← pad + 1#usize
  let (s, index_mut_back) ←
    core.array.Array.index_mut (core.ops.index.IndexMutSlice
      (core.slice.index.SliceIndexRangeUsizeSlice (Array Std.U64 machine.width)))
      state6 { start := i3, «end» := 25#usize }
  let (iter, into_iter_back) ←
    core.slice.Slice.iter_mut s
  let (im, back) ← fill_prf_loop1 iter (fun im1 => im1)
  let i4 ← 1#u64 <<< 63#i32
  let im1 := back im
  let s1 := into_iter_back im1
  let state7 := index_mut_back s1
  let a3 := Array.repeat machine.width i4
  Array.update state7 16#usize a3
def headerWord (n : Nat) (w0 w1 : U64) (w2 w3 : Array U64 machine.width) (old : Nat → Nat → BitVec 64)
    (k l : Nat) : BitVec 64 :=
  if k=16 then 1 <<< 63 else if 2*n+4<k then 0 else if k=2*n+4 then 31
  else if k=n+3 then w3.val[l]!.bv else if k=n+2 then w2.val[l]!.bv
  else if k=n+1 then w1.bv else if k=n then w0.bv else old k l

theorem header_spec (n offset : Usize) (s : Matrix machine.width) (w0 w1 : U64)
    (w2 w3 : Array U64 machine.width) (small : n.val≤4) (off : offset.val=n.val+4) :
    header n offset s w0 w1 w2 w3 ⦃ out => ∀ k < 25, ∀ l < machine.width.val,
      cell out k l = headerWord n.val w0 w1 w2 w3 (cell s) k l ⦄ := by
  unfold header
  step as ⟨s1,u0⟩
  step as ⟨j1,v1⟩
  step as ⟨s2,u1⟩
  step as ⟨j2,v2⟩
  step as ⟨s3,u2⟩
  step as ⟨j3,v3⟩
  step as ⟨s4,u3⟩
  step as ⟨pad,pv⟩
  step as ⟨s5,marker⟩
  step as ⟨first,fv⟩
  step as ⟨part,back,partVal,partLen,write⟩
  simp only [core.slice.Slice.iter_mut,bind_ok]
  have zeros : fill_prf_loop1 ⟨part,0⟩ id ⦃ it restore => (restore it).slice.length=part.length ∧
      ∀ j < part.length, (restore it).slice.val[j]! = Array.repeat machine.width 0#u64 ⦄ :=
    NativeVerify.Fors.zero_leaf_tail part
  obtain ⟨⟨it,restore⟩,hz,length,zero⟩ := spec_imp_exists zeros
  change fill_prf_loop1 ⟨part,0⟩ (fun x=>x) = ok (it,restore) at hz
  change (do let (im,b) ← fill_prf_loop1 ⟨part,0⟩ (fun x=>x)
             let hi ← 1#u64 <<< 63#i32
             Array.update (back (b im).slice) 16#usize (Array.repeat machine.width hi)) ⦃ _ => _ ⦄
  rw [hz]
  simp only [bind_ok]
  try dsimp only
  step as ⟨last,_,high⟩
  step as ⟨out,finish⟩
  rename_i k hk l hl
  rw [finish,broadcast _ _ _ _ _ (by decide) hl]
  by_cases endWord : k=16
  · simp only [show (16#usize).val=16 by rfl,endWord,ite_true,headerWord]
    exact high
  · simp only [show (16#usize).val=16 by rfl,endWord,ite_false]
    have tail : cell (back (restore it).slice) k l = if pad.val<k then 0 else cell s5 k l := by
      unfold cell
      rw [write]
      by_cases beyond : pad.val<k
      · rw [ite_eq_left beyond,List.getElem!_setSlice!_middle _ _ _ _ (by simp; change _ ∧ _ < (restore it).slice.length ∧ _ < 25;omega),
          zero _ (by omega),Array.repeat_val]
        simp [hl]
      · rw [ite_eq_right beyond,List.getElem!_setSlice!_prefix _ _ _ _ (by omega)]
    rw [tail,marker,broadcast _ _ _ _ _ (by omega) hl,u3,setRow _ _ _ _ _ (by omega),u2,setRow _ _ _ _ _ (by omega),
        u1,broadcast _ _ _ _ _ (by omega) hl,u0,broadcast _ _ _ _ _ (by omega) hl]
    simp only [headerWord,endWord,ite_false,v1,v2,v3,pv,off]
    split_ifs <;> first | rfl | omega

end slhdsa.NativeShakeWots
