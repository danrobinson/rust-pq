import Cachepath.NativeShakeWots.Program
import Cachepath.NativeShakeWots.Hashes
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.NativeShakeWots
open ShakeBatch NativeVerify NativeVerify.Wots cache.builder.nativeShake.Vector.Fused
set_option linter.concreteInstances false
variable [machine : Machine]

theorem chunk_ids (N first active : Usize) (nonempty : 0<active.val)
    (fits : first.val+active.val≤67) :
    core.array.from_fn machine.width (keygen.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64 N) (first,active)
    ⦃ out => ∀ (l : Nat) (live : l<active.val), l<machine.width.val →
      out.val[l]!.bv=addressLow (U32.ofNatCore (first.val+l) (by change _ < 2^32; omega)) ⦄ := by
  apply WP.spec_mono (core.array.from_fn.spec_stateless_getElem! machine.width _ (first,active)
    (fun l w => ∀ h : l<active.val, w.bv=addressLow (U32.ofNatCore (first.val+l) (by change _ < 2^32; omega))) ?_)
  · intro a indexed l live hl
    simpa only [Array.getElem!_Nat_eq] using indexed l hl live
  intro i hi
  simp only [keygen.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64,
    keygen.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut,lift,bind_ok]
  change (do let last ← active-1#usize
             let atId ← first + core.cmp.impls.OrdUsize.min i last
             let swapped ← ShakeBatch.core.num.U32.swap_bytes (UScalar.cast .U32 atId)
             Result.ok (core.convert.num.FromU64U32.from swapped,(first,active))) ⦃ v g => _ ⦄
  step as ⟨last,lastv⟩
  have minVal : (core.cmp.impls.OrdUsize.min i last).val=min i.val last.val := by
    change (if last < i then last else i).val=_
    split <;> rename_i h
    · exact (min_eq_right (show last.val ≤ i.val from Nat.le_of_lt h)).symm
    · exact (min_eq_left (show i.val ≤ last.val from Nat.le_of_not_gt h)).symm
  step as ⟨j,jv⟩
  all_goals try scalar_tac
  simp only [ShakeBatch.core.num.U32.swap_bytes,bind_ok,WP.spec_ok]
  refine ⟨?_,rfl⟩
  intro live
  have eq : j.val=first.val+i.val := by rw [jv,minVal,min_eq_left (by omega)]
  have bits : UScalar.cast .U32 j=U32.ofNatCore (first.val+i.val) (by scalar_tac) := by scalar_tac
  rw [← bits]
  rfl

variable [stream : Stream] [ok : StreamCorrect]

theorem absorb_chunk {N : Usize} (s : Matrix machine.width) (active : Usize) (pk : stream.State)
    (first : Nat) (initial : Spec.Bytes) (root : Nat → Spec.Bytes)
    (prior : ok.Absorbed pk (initial ++ (List.range first).flatMap root))
    (tips : ∀ l<active.val, digest N s l=root (first+l))
    (small : N.val≤32) (align : N.val%8=0) (fits : active.val≤machine.width.val) :
    keygen_loop0_loop1 N ⟨0#usize,active⟩ s pk ⦃ out =>
      ok.Absorbed out (initial ++ (List.range (first+active.val)).flatMap root) ⦄ := by
  unfold keygen_loop0_loop1
  apply range_fold (keygen_loop0_loop1.body N s) active pk (fun i st =>
    ok.Absorbed st (initial ++ (List.range (first+i)).flatMap root))
  · simpa using prior
  · intro it st stop live prev
    unfold keygen_loop0_loop1.body
    step with core.iter.range.IteratorRange.next_Usize_some_spec it (by simpa [stop] using live) as ⟨_,next,tag,idx,ends⟩
    simp only [tag]
    step with extract_digest N s it.start small align (by omega) as ⟨v,vb⟩
    simp only [lift,bind_ok]
    let* ⟨out,w⟩ ← ok.append st _ prev v.to_slice
    refine ⟨next,out,rfl,ends.trans stop,idx,?_⟩
    rw [idx,← Nat.add_assoc,List.range_succ,List.flatMap_append]
    rw [Array.val_to_slice,vb,tips _ live] at w
    simpa only [List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc] using w
  · intro it st last stop
    unfold keygen_loop0_loop1.body
    obtain ⟨⟨_,_⟩,no,tag,_⟩ := spec_imp_exists (core.iter.range.IteratorRange.next_Usize_none_spec it (by rw [stop,last]))
    simp [no,tag]

end slhdsa.NativeShakeWots
