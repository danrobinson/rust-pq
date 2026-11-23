import Peerarmkeccak.Unpack
open Aeneas Aeneas.Std Result Spec.Keccak
namespace PeerKeccak.Arm
open PeerArmRust
open slhdsa.Ksha3 (Reg Rows lane)
set_option maxRecDepth 8192

theorem both (m : States) :
    backends.aarch64_sha3.p1600_armv8_sha3_times2 m 24#usize
      ⦃ out => ∀ j : Fin 2, slhdsa.Keccak.words out.val[j.val]! =
        permute (slhdsa.Keccak.words m.val[j.val]!) ⦄ := by
  unfold backends.aarch64_sha3.p1600_armv8_sha3_times2
  simp only [show 24#usize ≤ 24#usize by decide,ite_true]
  step with packed m as ⟨s,arr⟩
  step as ⟨first,sub⟩
  have start : first=0#usize := UScalar.eq_of_val_eq (by scalar_tac)
  rw [start]
  step as ⟨keys,contents,length⟩
  simp only [SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter,bind_ok]
  step with rounds s keys as ⟨v,allRounds⟩
  simp only [consts.PLEN]
  step with unpacked m v as ⟨out,read⟩
  rename_i j
  rw [read j,allRounds j,arr j]
  have table : keys.val.map (·.bv)=rc.toList := by
    rw [contents]
    simp only [Array.val_to_slice,List.drop_zero]
    unfold consts.RC rc
    rfl
  rw [table];rfl

theorem single (state : Array U64 25#usize) :
    backends.aarch64_sha3.p1600_armv8_sha3 state 24#usize ⦃ out =>
      slhdsa.Keccak.words out = permute (slhdsa.Keccak.words state) ⦄ := by
  unfold backends.aarch64_sha3.p1600_armv8_sha3
  let zero := Array.repeat 25#usize core.default.DefaultU64.default
  rw [show core.default.DefaultArray.default 25#usize core.default.DefaultU64 = ok zero by
    exact Aeneas.Std.bind_ok core.default.DefaultU64.default (fun x => ok (Array.repeat 25#usize x))]
  simp only [bind_ok]
  step with both (Array.make 2#usize [state,zero]) as ⟨s,pair⟩
  step as ⟨out,read⟩
  rw [read,← getElem!_pos]
  exact pair 0

#print axioms both
#print axioms single
end PeerKeccak.Arm
