import Cachepath.NativeVerify.WotsRound
import Cachepath.WotsFusedChain
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.NativeVerify.Wots
open ShakeBatch cache.builder.nativeShake.Vector.Fused
set_option linter.concreteInstances false
variable [machine : Machine]

theorem round_fips {N : Usize} (seed : Array U8 N) (addr : address.Adrs) (n offset pad active : Usize)
    (sw aw : Array U64 4#usize) (ids : Array Usize machine.width) (steps : Array U32 machine.width)
    (values : LaneValues machine.width) (out : Matrix machine.width)
    (small : N.val≤32) (align : N.val%8=0) (count : n.val=N.val/8)
    (off : offset.val=n.val+4) (padding : pad.val=offset.val+n.val)
    (seedWords : ∀ k<n.val, sw.val[k]!.bv = inputWord seed.val k)
    (addrWords : ∀ k<4, aw.val[k]!.bv = addressWord addr k)
    (layout : RoundLayout n offset pad active sw aw ids steps values out)
    (l : Nat) (live : l<active.val) (v : Array U8 N)
    (words : ∀ k<n.val, laneWord values l k=inputWord v.val k) :
    Spec.Keccak.squeeze (ShakeBatch.lane out l) 0 N.val = Spec.shake256
      (bytes seed.val ++ ((adrsS {addr with word2:=UScalar.cast .U32 ids.val[l]!,word3:=steps.val[l]!}).bytes
        ++ bytes v.val)) N.val := by
  obtain ⟨before,hash,layout⟩ := layout
  apply hashed_short seed v addr _ _ before out l small align (hash l live)
  intro k hk
  rw [layout k hk l live]
  unfold baseWord initialWord
  have size : (2*N.val+32)/8=pad.val := by omega
  rw [size,← count,← off]
  by_cases payload : offset.val≤k ∧ k<offset.val+n.val
  · rw [ite_eq_left payload,← words _ (by omega)]
    simp only [ite_eq_right (by omega : k≠16),ite_eq_right (by omega : ¬pad.val<k),
      ite_eq_right (by omega : k≠pad.val),ite_eq_right (by omega : k≠n.val+3),
      ite_eq_right (by omega : ¬k<n.val),ite_eq_right (by omega : ¬k<offset.val)]
  · rw [ite_eq_right payload]
    by_cases tag : k=n.val+3
    · have last : k=offset.val-1 := by omega
      simp only [ite_eq_left last,ite_eq_right (by omega : k≠16),ite_eq_right (by omega : ¬pad.val<k),
        ite_eq_right (by omega : k≠pad.val),ite_eq_left tag]
    · have notLast : k≠offset.val-1 := by omega
      rw [ite_eq_right notLast]
      split_ifs <;> first | rfl | omega | exact seedWords _ (by omega) | exact addrWords _ (by omega) | decide

end slhdsa.NativeVerify.Wots
