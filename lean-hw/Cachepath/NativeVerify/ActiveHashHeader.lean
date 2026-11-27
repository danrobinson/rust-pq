import Cachepath.NativeVerify.ActiveHashHeaderRows
open Aeneas Aeneas.Std Result
namespace slhdsa.NativeVerify.ActiveHash
open ShakeBatch
variable [machine : Machine]
private theorem active_high_bit (s : Slice U64) :
    header_active_loop2 ⟨s,0⟩ id ⦃ it back =>
      (back it).slice.length=s.length ∧ ∀ j < s.length, (back it).slice.val[j]! = lastBit s.val[j]! ⦄ := high_bit s
omit machine in
private theorem repeated {α} [Inhabited α] (n : Usize) (v : α) (j : Nat) (bound : j < n.val) :
    (Array.repeat n v).val[j]! = v := by rw [Array.repeat_val]; simp [bound]

theorem header_spec {N : Usize} (seed : Array U8 N) (addresses : Array address.Adrs machine.width)
    (size active : Usize) (boundActive : active.val ≤ machine.width.val) (hf : N.val ≤ 32) (hs : size.val < 136) :
    header_active seed addresses size active ⦃ out =>
      ∀ k < 25, ∀ j < active.val, cell out k j =
        let w := initialWord seed addresses.val[j]! size.val k
        if k=16 then w ||| 0x8000000000000000 else w ⦄ := by
  unfold header_active
  step with seed_spec seed hf as ⟨words,keys⟩
  step as ⟨base,b⟩
  let zero := Array.repeat 25#usize (Array.repeat machine.width 0#u64)
  step with seed_rows words zero base (by omega) as ⟨st,sw⟩
  step with address_rows st base addresses active boundActive (by omega) as ⟨st1,aw⟩
  step as ⟨atPad,pv⟩
  step as ⟨st2,upd⟩
  step as ⟨row,restore,read,write⟩
  step as ⟨it,back,islice,idx,into⟩
  rcases it with ⟨s,start⟩
  simp only at islice idx into
  subst start
  change (do let (it1,restore1) ← header_active_loop2 ⟨s,0⟩ id; ok (restore (back (restore1 it1)))) ⦃ _ => _ ⦄
  step with active_high_bit s as ⟨it1,back1,len,top⟩
  have n : s.length=machine.width.val := by simpa [Slice.length,islice]
  have saved := into (back1 it1) (len.trans n)
  have prior (k : Nat) (hk : k < 25) (j : Nat) (hj : j < active.val) :
      cell st2 k j = initialWord seed addresses.val[j]! size.val k := by
    unfold initialWord
    by_cases pad : k=atPad.val
    · subst k
      rw [cell,upd,Array.set_val_eq,setSame st1.val atPad.val _ (by simpa using hk),repeated _ _ j (hj.trans_le boundActive),pv]
      simp only [if_pos (Eq.refl (size.val/8))]
      rfl
    · rw [show cell st2 k j=cell st1 k j by
            simp only [cell,upd,Array.set_val_eq,setOther _ _ _ _ (Ne.symm pad)],
          aw k hk j hj,sw k hk j (hj.trans_le boundActive)]
      simp only [pv] at pad
      have zeroed : cell (Array.repeat 25#usize (Array.repeat machine.width 0#u64)) k j=0 := by
        rw [cell,repeated 25#usize _ k hk,repeated _ _ j (hj.trans_le boundActive)]; rfl
      simp only [pad,ite_false,b,zeroed]
      split_ifs <;> first | rfl | (rw [keys k (by omega),if_pos (by omega)])
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

end slhdsa.NativeVerify.ActiveHash
