import Armwide.Xmss.PairedParents
import Spec.Correctness

open Aeneas Aeneas.Std Result
namespace slhdsa.ArmXmss
open H512.Multi

private def row (N : Usize) (b : Spec.Bytes) : Array U8 N :=
  .from (List.ofFn (fun i : Fin N.val => (⟨b[i.val]!⟩ : U8))) (by simp)

private theorem row_eq (N : Usize) (b : Spec.Bytes) (len : b.length=N.val) :
    bytes (row N b).val=b := by
  apply List.ext_getElem
  · simp [bytes,row,len]
  · intro i hi hj
    simp [bytes,row,List.getElem?_eq_getElem hj]

private def asSize (i : Nat) : Usize := ⟨BitVec.ofNat _ i⟩

/-- The native implementation overwrites only the reported number of nodes;
the unprocessed tail remains in the input array for the extracted scalar loop. -/
def pairedBuffer {N} (state : Array U64 8#usize) (a : address.Adrs) (first : U32)
    (roots : Nodes N) (count : Usize) (enabled : Bool) : Usize × Nodes N :=
  let input := old roots
  let result := match enabled with
    | true => parentsBatch N.val (S512.wv state.val) (adrsS a) first.val count.val input
    | false => (0,input)
  let done := result.1
  let values := result.2
  (asSize done,.from (List.ofFn (fun i : Fin 16 =>
    if i.val < done then row N (values i.val) else roots.val[i.val]!)) (by simp))

theorem full_level {N} (p : params.Params) (hp : PN p N) (seed : hash.Seed N)
    (hs : SeedOk seed) (wide : N.val=24 ∨ N.val=32) (enabled : Bool) (a : address.Adrs)
    (first : U32) (roots : Nodes N) (count : Usize) (size : count.val ≤ 8) (room : first.val+count.val ≤ 2^32) :
    let packed := pairedBuffer seed.state512 a first roots count enabled
    xmss.arm.batch_root_512_loop0_loop0 ⟨packed.1,count⟩ seed.pk_seed seed.state seed.state512
      packed.2 a first ⦃ out => ∀ j < count.val, bytes out.val[j]!.val=parent p seed a first roots j ⦄ := by
  have width : (paramsS p).n=N.val := congrArg UScalar.val hp.n_eq
  have slen : (bytes seed.pk_seed.val).length=(paramsS p).n := by rw [width];simp
  have stateEq : S512.wv seed.state512.val=pkState512 N.val (bytes seed.pk_seed.val) := by
    rw [hs.2 (by omega)]; simp [pkState512,toByte_zero]
  have vals := parents_batch_eq_fips (paramsS p) rfl (by rw [width];exact wide)
    (bytes seed.pk_seed.val) slen (adrsS a) first.val count.val (old roots)
    (by intro i _;rw [width];simp [old])
  simp only [width] at vals
  cases enabled with
  | false =>
    apply paired_then_remainder p hp seed hs wide false a first roots _ count _ size room
    · rfl
    · intro i hi _
      change bytes ((List.ofFn (fun k : Fin 16 => roots.val[k.val]!))[i]!).val = old roots i
      rw [getElem!_pos _ i (by simpa using hi),List.getElem_ofFn]
      rfl
  | true =>
    let result := parentsBatch N.val (pkState512 N.val (bytes seed.pk_seed.val))
      (adrsS a) first.val count.val (old roots)
    have small : result.1 ≤ 8 := by have h : result.1=count.val/2*2 := vals.1;omega
    have natEq : (asSize result.1).val=result.1 := by
      change result.1 % 2^System.Platform.numBits = result.1
      apply Nat.mod_eq_of_lt
      rcases System.Platform.numBits_eq with bits|bits <;> rw [bits] <;> omega
    apply paired_then_remainder p hp seed hs wide true a first roots _ count _ size room
    · simpa [pairedBuffer,pairResult,stateEq,result] using natEq
    · intro i hi active
      change (i < (pairedBuffer seed.state512 a first roots count true).1.val ∨ _) at active
      simp only [pairedBuffer,stateEq] at active ⊢
      change (i < (asSize result.1).val ∨ 2*(asSize result.1).val ≤ i) at active
      rw [natEq] at active
      simp only [pairResult,ite_true,stateEq]
      change bytes ((List.ofFn (fun k : Fin 16 => if k.val < result.1 then row N (result.2 k.val)
        else roots.val[k.val]!))[i]!).val=result.2 i
      rw [getElem!_pos _ i (by simpa using hi),List.getElem_ofFn]
      rcases active with early|late
      · simp only [early,ite_true]
        apply row_eq
        rw [show result.2 i=_ from vals.2.1 i early,Spec.H_length _ hp.valid,width]
      · simp only [show ¬i < result.1 by omega,ite_false]
        exact (vals.2.2 i late).symm

end slhdsa.ArmXmss
