import Shakebatch.Padding
open Aeneas Aeneas.Std Result
namespace slhdsa.ShakeBatch
set_option linter.concreteInstances false
variable [machine : Machine]

omit machine in
private theorem repeated {α} [Inhabited α] (n : Usize) (v : α) (j : Nat) (bound : j < n.val) :
    (Array.repeat n v).val[j]! = v := by rw [Array.repeat_val]; simp [bound]

def initialWord {N : Usize} (seed : Array U8 N) (addr : address.Adrs) (size k : Nat) : BitVec 64 :=
  if k=size/8 then 31 else if N.val/8 ≤ k ∧ k < N.val/8+4 then addressWord addr (k-N.val/8)
  else if k < N.val/8 then inputWord seed.val k else 0

theorem header_spec {N : Usize} (seed : Array U8 N) (addresses : Array address.Adrs machine.width)
    (size : Usize) (hf : N.val ≤ 32) (hs : size.val < 136) :
    shake.batch.header seed addresses size ⦃ out =>
      ∀ k < 25, ∀ j < machine.width.val, cell out k j =
        let w := initialWord seed addresses.val[j]! size.val k
        if k=16 then w ||| 0x8000000000000000 else w ⦄ := by
  unfold shake.batch.header
  step as ⟨base,b⟩
  let zero := Array.repeat 25#usize (Array.repeat machine.width 0#u64)
  step with seed_rows seed zero base (by omega) (by omega) as ⟨st,sw⟩
  step with address_rows st base addresses (by omega) as ⟨st1,aw⟩
  step as ⟨atPad,pv⟩
  step as ⟨st2,upd⟩
  step as ⟨row,restore,read,write⟩
  step as ⟨it,back,islice,idx,into⟩
  rcases it with ⟨s,start⟩
  simp only at islice idx into
  subst start
  change (do let (it1,restore1) ← shake.batch.header_loop2 ⟨s,0⟩ id; ok (restore (back (restore1 it1)))) ⦃ _ => _ ⦄
  step with high_bit s as ⟨it1,back1,len,top⟩
  have n : s.length=machine.width.val := by simpa [Slice.length,islice]
  have saved := into (back1 it1) (len.trans n)
  have prior (k : Nat) (hk : k < 25) (j : Nat) (hj : j < machine.width.val) :
      cell st2 k j = initialWord seed addresses.val[j]! size.val k := by
    unfold initialWord
    by_cases pad : k=atPad.val
    · subst k
      rw [cell,upd,Array.set_val_eq,setSame st1.val atPad.val _ (by simpa using hk),repeated _ _ j hj,pv]
      simp only [if_pos (Eq.refl (size.val/8))]
      rfl
    · rw [show cell st2 k j=cell st1 k j by
            simp only [cell,upd,Array.set_val_eq,setOther _ _ _ _ (Ne.symm pad)],
          aw k hk j hj,sw k hk j hj]
      simp only [pv] at pad
      have zeroed : cell (Array.repeat 25#usize (Array.repeat machine.width 0#u64)) k j=0 := by
        rw [cell,repeated 25#usize _ k hk,repeated _ _ j hj]; rfl
      simp only [pad,ite_false,b,zeroed]
  intro k hk j hj
  rw [write]
  by_cases eq : k=16
  · subst k
    simp only [ite_true,cell,Array.set_val_eq]
    simp only [show (16#usize).val=16 by rfl]
    rw [setSame st2.val 16 _ (by simp),saved,top j (by omega)]
    change s.val[j]!.bv ||| 0x8000000000000000 = _
    rw [islice,read,← getElem!_pos]
    exact congrArg (fun w : BitVec 64 => w ||| 0x8000000000000000) (prior 16 (by decide) j hj)
  · simp only [eq,ite_false]
    convert prior k hk j hj using 1
    simp only [cell,Array.set_val_eq,setOther _ _ _ _ (show (16#usize).val ≠ k from Ne.symm eq)]

end slhdsa.ShakeBatch
