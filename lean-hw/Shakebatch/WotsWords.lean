import Shakebatch.Digest
open Aeneas Aeneas.Std Result
namespace slhdsa.ShakeBatch
set_option linter.concreteInstances false
variable [machine : Machine]

omit machine in
private theorem from_to_bytes (x : U64) : (core.num.U64.from_le_bytes (core.num.U64.to_le_bytes x)).bv=x.bv := by
  have back := BitVec.fromLEBytes_toLEBytes (show 64%8=0 by decide) x.bv
  have h : (x.bv.toLEBytes.map (@UScalar.mk UScalarTy.U8)).map (·.bv) = x.bv.toLEBytes := by simp
  have val : (core.num.U64.to_le_bytes x).val = x.bv.toLEBytes.map (@UScalar.mk UScalarTy.U8) := by
    unfold core.num.U64.to_le_bytes
    rw [Array.from_val]
  apply BitVec.eq_of_toNat_eq
  change (BitVec.fromLEBytes ((core.num.U64.to_le_bytes x).val.map (·.bv))).toNat = _
  rw [val,h,back]
  rfl

omit machine in
theorem pack_le_word (v : List U8) (p : Nat) (w : U64) (fits : 8*p+8 ≤ v.length)
    (agree : ∀ b < 8, v[8*p+b]! = (core.num.U64.to_le_bytes w).val[b]!) :
    inputWord v p=w.bv := by
  have seg : (v.drop (p*8)).take 8 = (core.num.U64.to_le_bytes w).val := by
    apply List.ext_getElem
    · simp; omega
    · intro b hl hr
      rw [List.getElem_take,List.getElem_drop,← getElem!_pos,← getElem!_pos]
      rw [Nat.mul_comm p 8]
      exact agree b (by simpa using hr)
  rw [inputWord,seg,← PlatformShake.loaded,from_to_bytes]

theorem digest_words {N : Usize} (s : Matrix machine.width) (small : N.val ≤ 136) (align : N.val%8=0) :
    ∃ out : Array (Array U8 N) machine.width,
      (∀ j < machine.width.val, bytes out.val[j]!.val = Spec.Keccak.squeeze (lane s j) 0 N.val) ∧
      (∀ j < machine.width.val, ∀ w < N.val/8, inputWord out.val[j]!.val w = cell s w j) := by
  obtain ⟨out,digest,raw⟩ := WP.spec_exists (WP.spec_and (read_digest N s small align) (read_spec N s small align))
  refine ⟨out,digest,?_⟩
  intro j hj w hw
  apply pack_le_word <;> try (simp;omega)
  intro b hb
  have h := raw j hj (8*w+b) (by omega)
  simpa [outputByte,stateByte,show (8*w+b)/8=w by omega,show (8*w+b)%8=b by omega] using h

end slhdsa.ShakeBatch
