import Shakebatch.RecoverProgram
import Slhdsa.Proofs.ShakeHash

open Aeneas Aeneas.Std Result
namespace slhdsa.ShakeBatch

class StreamCorrect [s : Stream] where
  Absorbed : s.State → Spec.Bytes → Prop
  start {N : Usize} (pk : Array U8 N) (a : address.Adrs) :
    s.start pk a ⦃ out => Absorbed out (bytes pk.val ++ (adrsS a).bytes) ⦄
  append (s0 : s.State) (initialBytes : Spec.Bytes) (prior : Absorbed s0 initialBytes) (data : Slice U8) :
    s.absorb s0 data ⦃ out => Absorbed out (initialBytes ++ bytes data.val) ⦄
  digest (N : Usize) (s0 : s.State) (initialBytes : Spec.Bytes) (prior : Absorbed s0 initialBytes) :
    s.digest N s0 ⦃ out => bytes out.val=Spec.shake256 initialBytes N.val ⦄

variable [stream : Stream] [ok : StreamCorrect]

theorem absorb_roots {N : Usize} (slice : Slice (Array U8 N)) (pk : stream.State)
    (initialBytes : Spec.Bytes) (first : Nat) (root : Nat → Spec.Bytes)
    (prior : ok.Absorbed pk (initialBytes ++ (List.range first).flatMap root))
    (values : ∀ j < slice.length, bytes slice.val[j]!.val=root (first+j)) :
    shake.fors_batch.recover_loop0_loop1 ⟨slice,0⟩ pk ⦃ out =>
      ok.Absorbed out (initialBytes ++ (List.range (first+slice.length)).flatMap root) ⦄ := by
  unfold shake.fors_batch.recover_loop0_loop1
  apply loop.spec_decr_nat (measure := fun q : core.slice.iter.Iter (Array U8 N) × stream.State => slice.length-q.1.i)
    (inv := fun q => q.1.slice=slice ∧ q.1.i ≤ slice.length ∧
      ok.Absorbed q.2 (initialBytes ++ (List.range (first+q.1.i)).flatMap root))
  · rintro ⟨⟨s,i⟩,state⟩ ⟨rfl,le,old⟩
    simp only at le old
    unfold shake.fors_batch.recover_loop0_loop1.body core.slice.iter.IteratorSliceIter.next
    by_cases live : i < s.length
    · have hl : i < s.len.val := by simpa using live
      simp only [dif_pos hl,lift,bind_ok]
      let* ⟨out,hout⟩ ← ok.append state _ old (s[i]).to_slice
      refine ⟨by omega,?_,by omega⟩
      have value : bytes s[i].val=root (first+i) := by
        have eq : s.val[i]! = s[i] := getElem!_pos s.val i live
        rw [← eq]; exact values i live
      rw [← Nat.add_assoc,List.range_succ,List.flatMap_append]
      simpa only [Array.val_to_slice,value,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc] using hout
    · have hl : ¬ i < s.len.val := by simpa using live
      simp only [dif_neg hl,step_simps]
      simpa only [show i=s.length by omega] using old
  · simpa using prior

end slhdsa.ShakeBatch
