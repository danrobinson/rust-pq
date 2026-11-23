import Shakebatch.Header
import Shakebatch.Digest
open Aeneas Aeneas.Std Result
namespace slhdsa.ShakeBatch
set_option linter.concreteInstances false
variable [machine : Machine]

omit machine in
theorem address_length (a : address.Adrs) : (adrsS a).bytes.length=32 := by
  simp [Spec.Adrs.bytes,Spec.toByte]

omit machine in
theorem inputWord_eq (xs : List U8) (k : Nat) : inputWord xs k=Spec.Keccak.messageWord (bytes xs) k := by
  simp [inputWord,Spec.Keccak.messageWord,Nat.mul_comm]

omit machine in
theorem addressWord_eq (a : address.Adrs) (k : Nat) : addressWord a k=Spec.Keccak.messageWord (adrsS a).bytes k := by
  simp [addressWord,Spec.Keccak.messageWord,Nat.mul_comm]

omit machine in
theorem short_layout {N : Usize} (seed value : Array U8 N) (a : address.Adrs)
    (bound : N.val ≤ 32) (aligned : N.val%8=0) (k : Nat) :
    (if N.val/8+4 ≤ k ∧ k < N.val/8+4+N.val/8 then inputWord value.val (k-(N.val/8+4))
     else let v := initialWord seed a (2*N.val+32) k; if k=16 then v ||| 0x8000000000000000 else v) =
      Spec.Keccak.paddedWord (bytes seed.val ++ ((adrsS a).bytes ++ bytes value.val)) k := by
  have s : (bytes seed.val).length = 8*(N.val/8) := by simp; omega
  have a4 : (adrsS a).bytes.length=8*4 := address_length a
  have size : (2*N.val+32)/8=N.val/8+4+N.val/8 := by omega
  simp only [Spec.Keccak.paddedWord,List.length_append,bytes_length,Array.length_eq,address_length,
    Spec.Keccak.messageWord_append _ _ _ _ s,Spec.Keccak.messageWord_append _ _ _ _ a4,
    initialWord,inputWord_eq,addressWord_eq]
  have size' : (N.val + (32+N.val))/8=N.val/8+4+N.val/8 := by omega
  rw [size,size']
  split_ifs <;> (first | rfl | omega | (congr 1 <;> omega))

theorem short_fips {N : Usize} (seed : Array U8 N) (addresses : Array address.Adrs machine.width)
    (values : Array (Array U8 N) machine.width) (permutes : PermutationCorrect)
    (bound : N.val ≤ 32) (aligned : N.val%8=0) :
    shake.batch.short seed addresses values ⦃ out => ∀ j < machine.width.val,
      bytes out.val[j]!.val = Spec.shake256 (bytes seed.val ++ ((adrsS addresses.val[j]!).bytes ++ bytes values.val[j]!.val)) N.val ⦄ := by
  unfold shake.batch.short
  step as ⟨a,twice⟩
  step as ⟨size,sz⟩
  step with header_spec seed addresses size bound (by omega) as ⟨st,header⟩
  step as ⟨n,nn⟩
  step as ⟨offset,off⟩
  step with put_spec st offset values (by omega) as ⟨st1,put⟩
  step with permutes st1 as ⟨st2,permuted⟩
  step with read_digest N st2 (by omega) aligned as ⟨out,read⟩
  rename_i j hj
  rw [read j hj,permuted j hj,Spec.shake256,Spec.Keccak.padded_fips _ (by simp [address_length];omega) (by simp [address_length];omega)]
  apply congrArg (fun a => Spec.Keccak.squeeze (Spec.Keccak.permute a) 0 N.val)
  apply Spec.Keccak.ext25 _ _ (by simp [lane]) (by simp [Spec.Keccak.padded])
  intro k hk
  simp only [lane,Spec.Keccak.padded,Spec.Keccak.ofFnAt _ _ hk,put k hk j hj,header k hk j hj,off,nn,sz,twice]
  exact short_layout seed _ _ bound aligned k

end slhdsa.ShakeBatch
