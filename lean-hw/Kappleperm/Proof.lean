import Kappleperm.Funs
import Ksha3.Top
import Slhdsa.Proofs.Keccak
open Aeneas Aeneas.Std Result ControlFlow
open Spec.Keccak slhdsa.KeccakRegisters
namespace slhdsa.Kappleperm
open KapplepermRust.shake256.parallel
open Ksha3 (lane)
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
theorem rounds (a : Regs 2#usize) (keys : Slice U64) :
    sha3.permute_loop ⟨keys,0⟩ a ⦃ out => ∀ j, lane out j = (keys.val.map (·.bv)).foldl round (lane a j) ⦄ := by
  unfold sha3.permute_loop
  apply loop.spec_decr_nat
    (measure := fun (p : core.slice.iter.Iter U64 × Regs 2#usize) => keys.length-p.1.i)
    (inv := fun p => p.1.slice = keys ∧ p.1.i ≤ keys.length ∧
      ∀ j, lane p.2 j = ((keys.val.take p.1.i).map (·.bv)).foldl round (lane a j))
  · rintro ⟨it,state⟩ ⟨slice,bound,prior⟩
    simp only at slice bound prior ⊢
    unfold sha3.permute_loop.body
    by_cases more : it.i < keys.length
    · let next := {it with i := it.i+1}
      have index : it.i < it.slice.len.val := by simpa [slice] using more
      have get : core.slice.iter.IteratorSliceIter.next it = ok (some keys.val[it.i],next) := by
        simp [core.slice.iter.IteratorSliceIter.next,index,next,slice,more,Slice.length]
      rw [get]
      simp only [bind_ok]
      step with Ksha3.round_fips state _ as ⟨out,post⟩
      refine ⟨slice,by change it.i+1 ≤ keys.length; omega,?_,by change keys.length-(it.i+1) < keys.length-it.i; omega⟩
      intro j
      rw [post j,prior j]
      change _ = (((keys.val.take (it.i+1)).map _).foldl _ _)
      rw [List.take_succ_eq_append_getElem more,List.map_append,List.foldl_append]
      rfl
    · have doneIt : core.slice.iter.IteratorSliceIter.next it = ok (none,it) := by
        simp [core.slice.iter.IteratorSliceIter.next,slice,more,Slice.length] at *
      rw [doneIt]
      simp only [step_simps]
      simpa [show it.i=keys.length by omega,Slice.length] using prior
  · exact ⟨rfl,Nat.zero_le _,by simp⟩


def view (m : Matrix 2#usize) (j : Fin 2) : State := _root_.Array.ofFn (n := 25) fun i => m.val[i.val]!.val[j.val]!.bv

private theorem pack_view (x : Matrix 2#usize) (j : Fin 2) : lane (pack x) j = view x j := by
  unfold Ksha3.lane view
  congr 1
  funext i
  fin_cases j <;> simp [pack,Array.from_val,getElem!_pos,i.isLt]

private theorem unpack_view (x : Regs 2#usize) (j : Fin 2) : view (unpack x) j = lane x j := by
  unfold Ksha3.lane view
  congr 1
  funext i
  have hi : i.val < x.val.length := by simpa using i.isLt
  change ((unpack x).val[i.val]!).val[j.val]!.bv = x.val[i.val]! j
  rw [getElem!_pos _ i.val (by simpa using i.isLt),getElem!_pos x.val i.val hi]
  simp only [unpack,Array.from_val,List.getElem_map]
  rw [List.getElem!_ofFn _ j.val j.isLt]

theorem permute_fips (words : Matrix 2#usize) :
    sha3.permute words ⦃ out => ∀ j, view out j = permute (view words j) ⦄ := by
  unfold sha3.permute
  simp only [KapplepermRust.core.intrinsics.transmute,transmute,bind_ok,
    SharedArray.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter,
    SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter]
  step with rounds (pack words) _ as ⟨r,hr⟩
  intro j
  change view (unpack r) j = _
  rw [unpack_view,hr j,pack_view]
  have constants : KapplepermRust.shake256.RC.val.map (·.bv) = rc.toList := by unfold KapplepermRust.shake256.RC rc; rfl
  simp only [Slice.from_val]
  change (KapplepermRust.shake256.RC.val.map (·.bv)).foldl round _ = _
  rw [constants]
  rfl
end slhdsa.Kappleperm
