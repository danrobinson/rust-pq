import Chainavx2.Funs
import Chainvectors.Save
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.Avx2.Chain
open ChainAvx2Rust.sha256.x86.avx2

/-- The extracted scheduler uses exactly the longest of the eight unsigned ranges. -/
theorem longest_spec (lengths : Array U32 8#usize) :
    chains_loop0_loop0 ⟨0#usize,8#usize⟩ lengths 0#u32 ⦃ out =>
      ∀ cap : Nat, out.val ≤ cap ↔ ∀ i : Fin 8, lengths.val[i.val]!.val ≤ cap ⦄ := by
  unfold chains_loop0_loop0
  apply loop.spec_decr_nat (measure := fun p : core.ops.range.Range Usize × U32 => 8-p.1.start.val)
    (inv := fun p => p.1.end.val = 8 ∧ p.1.start.val ≤ 8 ∧ ∀ cap : Nat,
      p.2.val ≤ cap ↔ ∀ i : Fin 8, i.val < p.1.start.val → lengths.val[i.val]!.val ≤ cap)
  · rintro ⟨it,acc⟩ ⟨he,hi,inv⟩
    simp only at he hi inv
    unfold chains_loop0_loop0.body
    by_cases lt : it.start.val < it.end.val
    · step with core.iter.range.IteratorRange.next_Usize_some_spec it lt as ⟨o,next,ho,hn,hend⟩
      simp only [ho]
      step as ⟨word,hw⟩
      have hw' : word = lengths.val[it.start.val]! := by rw [hw,getElem!_pos]
      simp only [core.cmp.impls.OrdU32.max, lift, bind_ok, step_simps]
      refine ⟨by rw [hend,he],by omega,?_,by omega⟩
      intro cap
      have mx : (if word < acc then acc else word).val = max acc.val word.val := by
        split <;> rename_i h
        · exact (Nat.max_eq_left (by scalar_tac)).symm
        · exact (Nat.max_eq_right (by scalar_tac)).symm
      rw [mx, Nat.max_le, inv, hw']
      constructor
      · rintro ⟨prev,here⟩ i h
        by_cases eq : i.val = it.start.val
        · simpa [eq] using here
        · exact prev i (by omega)
      · intro all
        exact ⟨fun i h => all i (by omega),all ⟨it.start.val,by omega⟩ (by change it.start.val < next.start.val; omega)⟩
    · step with core.iter.range.IteratorRange.next_Usize_none_spec it (by omega) as ⟨o,next,ho,_⟩
      simp only [ho,step_simps]
      intro cap
      rw [inv]
      exact ⟨fun h i => h i (by have := i.isLt; omega),fun h i _ => h i⟩
  · simp

theorem range_lengths_spec (N off : Usize) (starts ends : Slice U32)
    (hs : off.val + 8 ≤ starts.length) (he : off.val + 8 ≤ ends.length) :
    core.array.from_fn 8#usize (chains.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU32 N) (ends,off,starts)
      ⦃ a => ∀ j, j < 8 → a.val[j]!.val = ends.val[off.val+j]!.val - starts.val[off.val+j]!.val ⦄ := by
  apply WP.spec_mono (core.array.from_fn.spec_stateless_getElem! 8#usize (chains.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU32 N) (ends,off,starts)
    (fun j (x : U32) => x.val = ends.val[off.val+j]!.val - starts.val[off.val+j]!.val) ?_)
  · intro a h j hj; simpa only [Array.getElem!_Nat_eq] using h j hj
  intro i hi
  change i.val < 8 at hi
  dsimp only
  unfold chains.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut
  have bound := starts.property
  step as ⟨pos,hp⟩
  step as ⟨stop,hstop⟩
  step as ⟨start,hstart⟩
  simp only [lift,bind_ok,step_simps]
  constructor
  · have small : stop.val-start.val < 2^32 := by have := stop.bv.isLt; change stop.val < 2^32 at this; omega
    change (BitVec.ofNat 32 (max 0 (stop.val-start.val))).toNat = _
    rw [Nat.zero_max,BitVec.toNat_ofNat,Nat.mod_eq_of_lt small,hstop,hstart,← getElem!_pos,← getElem!_pos,hp]
  · rfl

end slhdsa.Avx2.Chain
