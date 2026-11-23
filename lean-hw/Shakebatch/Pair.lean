import Shakebatch.Short
open Aeneas Aeneas.Std Result
namespace slhdsa.ShakeBatch
set_option linter.concreteInstances false
variable [machine : Machine]

omit machine in
theorem pair_layout {N : Usize} (seed left right : Array U8 N) (a : address.Adrs)
    (bound : N.val ≤ 32) (aligned : N.val%8=0) (k : Nat) :
    (if 2*N.val/8+4 ≤ k ∧ k < 2*N.val/8+4+N.val/8 then inputWord right.val (k-(2*N.val/8+4))
     else if N.val/8+4 ≤ k ∧ k < N.val/8+4+N.val/8 then inputWord left.val (k-(N.val/8+4))
     else let v := initialWord seed a (3*N.val+32) k; if k=16 then v ||| 0x8000000000000000 else v) =
      Spec.Keccak.paddedWord (bytes seed.val ++ ((adrsS a).bytes ++ (bytes left.val ++ bytes right.val))) k := by
  have s : (bytes seed.val).length = 8*(N.val/8) := by simp; omega
  have l : (bytes left.val).length = 8*(N.val/8) := by simp; omega
  have a4 : (adrsS a).bytes.length=8*4 := address_length a
  have size : (3*N.val+32)/8=2*(N.val/8)+4+N.val/8 := by omega
  simp only [Spec.Keccak.paddedWord,List.length_append,bytes_length,Array.length_eq,address_length,
    Spec.Keccak.messageWord_append _ _ _ _ s,Spec.Keccak.messageWord_append _ _ _ _ a4,
    Spec.Keccak.messageWord_append _ _ _ _ l,initialWord,inputWord_eq,addressWord_eq]
  have size' : (N.val + (32+(N.val+N.val)))/8=2*(N.val/8)+4+N.val/8 := by omega
  rw [size,size',show 2*N.val/8=2*(N.val/8) by omega]
  split_ifs <;> (first | rfl | omega | (congr 1 <;> omega))

theorem pair_fips {N : Usize} (seed : Array U8 N) (addresses : Array address.Adrs machine.width)
    (left right : Array (Array U8 N) machine.width) (permutes : PermutationCorrect)
    (bound : N.val ≤ 32) (aligned : N.val%8=0) :
    shake.batch.pair seed addresses left right ⦃ out => ∀ j < machine.width.val,
      bytes out.val[j]!.val = Spec.shake256 (bytes seed.val ++ ((adrsS addresses.val[j]!).bytes ++
        (bytes left.val[j]!.val ++ bytes right.val[j]!.val))) N.val ⦄ := by
  unfold shake.batch.pair
  step as ⟨a,three⟩
  step as ⟨size,sz⟩
  step with header_spec seed addresses size bound (by omega) as ⟨st,header⟩
  step as ⟨n,nn⟩
  step as ⟨offset,off⟩
  step with put_spec st offset left (by omega) as ⟨st1,put1⟩
  step as ⟨twice,tw⟩
  step as ⟨n2,nn2⟩
  step as ⟨offset2,off2⟩
  step with put_spec st1 offset2 right (by omega) as ⟨st2,put2⟩
  step with permutes st2 as ⟨st3,permuted⟩
  step with read_digest N st3 (by omega) aligned as ⟨out,read⟩
  rename_i j hj
  rw [read j hj,permuted j hj,Spec.shake256,Spec.Keccak.padded_fips _ (by simp [address_length];omega) (by simp [address_length];omega)]
  apply congrArg (fun a => Spec.Keccak.squeeze (Spec.Keccak.permute a) 0 N.val)
  apply Spec.Keccak.ext25 _ _ (by simp [lane]) (by simp [Spec.Keccak.padded])
  intro k hk
  simp only [lane,Spec.Keccak.padded,Spec.Keccak.ofFnAt _ _ hk,put2 k hk j hj,
    put1 k hk j hj,header k hk j hj,off,nn,sz,three,off2,nn2,tw]
  exact pair_layout seed _ _ _ bound aligned k

end slhdsa.ShakeBatch
