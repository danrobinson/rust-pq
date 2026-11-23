import Wotswide.Hash
import Wotsx86.Proof
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.Wots.Wide

private theorem value_in_row {N : Usize} {expect base buf i}
    (width : N.val ≤ 32) (row : rowComplete N expect base buf i) :
    blkVal N.val buf.val[i]! = expect i := by
  unfold rowComplete at row
  have h := congrArg List.length row
  simp at h
  have size : (expect i).length = N.val := by omega
  unfold blkVal
  rw [row,List.append_assoc]
  have head : (bytes (base.val[i]!.val.take 22)).length = 22 := by simp
  rw [List.drop_left' head,List.take_left' size]

/-- The returned WOTS public key for the supplied base-16 chain digits. -/
theorem recover_fips {N : Usize} (P : Spec.Params) [Fact (P.family=.sha2)]
    (seed : WotsWideRust.hash.Seed N) (a : WotsWideRust.address.Adrs)
    (sig : Slice U8) (digits : Slice U32) (width : N.val=P.n) (shape : NOk N)
    (seedOK : SeedOk (coreSeed seed)) (cpu : GatherRust.avx512Available=true)
    (count : digits.length=2*N.val+3) (valid : ∀ i < digits.length, digits.val[i]!.val < 16)
    (available : N.val*digits.length ≤ sig.length) :
    WotsWideRust.wots.wide.recover seed a sig digits ⦃ r =>
      bytes r.val = Spec.T P (bytes seed.pk_seed.val) (Spec.wotsPkAdrs (adrsS (coreAddress a)))
        ((List.range digits.length).flatMap fun i =>
          chainAt P N (bytes seed.pk_seed.val) (adrsS (coreAddress a)) sig digits i 15) ⦄ := by
  let initial := Array.repeat 67#usize (Array.repeat 64#usize 0#u8)
  let base := Array.to_slice initial
  have small : digits.length ≤ 67 := by have := shape.le32; omega
  have kernel := Checked.recover_fips P N (bytes seed.pk_seed.val) seed.state (WotsWideRust.checkedAddress a)
    sig digits base cpu width (width ▸ shape) (by simp [← width]) (by rw [← width]; exact seedOK.1)
    count valid (by simpa [base,initial] using small) available
  unfold WotsWideRust.wots.wide.recover
  simp only [lift,Array.to_slice_mut,bind_tc_eq,bind_ok,WotsWideRust.sha256.x86.recover]
  step with kernel as ⟨out,frame⟩
  have len : out.val.length = (67#usize).val := by simpa [base,initial,Slice.length] using frame.1.1
  simp only [WotsWideRust.address.Adrs.with_type,WotsWideRust.address.Adrs.with_keypair,bind_ok]
  step as ⟨blocks,hb,hl⟩
  have sliced : blocks.val = out.val.take digits.length := by simpa [List.slice,Array.val_to_slice,Array.from_slice_val _ _ len] using hb
  have size : blocks.length = digits.length := by simp [Slice.length,sliced,List.length_take,len,Nat.min_eq_left small]
  rw [thash_eq _ _ _ shape (size.trans count)]
  step with thash_values_spec P width.symm shape _ seedOK _ blocks (size.trans count) as ⟨result,hr⟩
  rw [hr,size]
  congr 1
  · unfold WotsWideRust.address.WOTS_PK; rfl
  apply List.flatMap_congr
  intro i hi
  have bound := List.mem_range.mp hi
  rw [sliced,List.getElem!_eq_getElem?_getD,List.getElem?_take_of_lt bound,← List.getElem!_eq_getElem?_getD]
  exact value_in_row shape.le32 (frame.2 i bound)

end slhdsa.X86.Wots.Wide
