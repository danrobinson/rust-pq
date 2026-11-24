import Peerarmkeccak.Xof
import Mathlib.Tactic.IntervalCases

namespace PeerShake.Buffer
set_option maxRecDepth 2000

/-- The two low index bits give the descriptor tail count in Rust's Wasm loop. -/
theorem descriptorMask (n : BitVec 32) :
    (n &&& 3)=n%4 ∧ (n &&& (-4))=n-n%4 := by
  have mask : n &&& (-4) = (n >>> (2 : Nat)) <<< (2 : Nat) := by
    ext i hi
    interval_cases i <;> simp
  constructor
  · apply BitVec.eq_of_toNat_eq
    change (n.toNat &&& (2^2-1)) = n.toNat % 4
    rw [Nat.and_two_pow_sub_one_eq_mod]
  · rw [mask]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft,BitVec.toNat_ushiftRight,Nat.shiftLeft_eq,Nat.shiftRight_eq_div_pow,
      BitVec.toNat_sub,BitVec.toNat_umod]
    change (n.toNat / 4 * 4) % 4294967296 = (4294967296 - n.toNat % 4 + n.toNat) % 4294967296
    have base : 4294967296 - n.toNat%4 + n.toNat = n.toNat/4*4 + 4294967296 := by omega
    rw [base,Nat.add_mod_right]

/-- Rust's eight-way rate-block iterator first consumes a zero-to-seven-block prefix.
A valid block slice is bounded by the signed byte offset to its end. -/
theorem blockMask (n : BitVec 32) (nonempty : 0<n) (bound : n≤15790320) :
    (n &&& 7)=n%8 ∧ ((n+536870911) &&& 536870911)=n-1 := by
  constructor
  · apply BitVec.eq_of_toNat_eq
    change (n.toNat &&& (2^3-1)) = n.toNat % 8
    rw [Nat.and_two_pow_sub_one_eq_mod]
  · apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and,BitVec.toNat_add,BitVec.toNat_sub]
    have mask : (536870911 : BitVec 32).toNat=2^29-1 := by decide
    rw [mask,Nat.and_two_pow_sub_one_eq_mod]
    have lo : 0<n.toNat := nonempty
    have hi : n.toNat≤15790320 := bound
    change ((n.toNat+536870911)%4294967296)%536870912=(4294967295+n.toNat)%4294967296
    rw [Nat.mod_eq_of_lt (by omega : n.toNat+536870911<4294967296)]
    have src : n.toNat+536870911 = (n.toNat-1)+536870912 := by omega
    have dst : 4294967295+n.toNat = (n.toNat-1)+4294967296 := by omega
    rw [src,dst,Nat.add_mod_right,Nat.add_mod_right,Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)]


theorem descriptorStep32 (length index : Int) (size : 0≤length ∧ length≤(2^31-1)/8)
    (live : 0≤index ∧ index<length) :
    0≤8*index ∧ 8*index+8≤2^31-1 ∧ index+1≤length ∧
      (index+1=length ↔ index=length-1) ∧ length-(index+1)<length-index := by omega

/-- A four-descriptor iteration visits exactly its next four elements. The
residual iterator then visits exactly the final zero-to-three descriptors. -/
theorem descriptorFour (n k j : Int) (nBound : 0≤n ∧ n≤(2^31-1)/8)
    (live : 0≤k ∧ k<n/4) (lane : 0≤j ∧ j<4) :
    (4*k+j)/4=k ∧ (4*k+j)%4=j ∧ (4*k+j)*8+8≤2^31-1 ∧
      (4*(k+1)=n-n%4 ↔ k+1=n/4) ∧ 4*(k+1)≤n ∧ n/4-(k+1)<n/4-k := by omega

theorem descriptorTail (n j : Int) (nBound : 0≤n ∧ n≤(2^31-1)/8)
    (live : 0≤j ∧ j<n%4) :
    0≤n-n%4+j ∧ n-n%4+j<n ∧ (n-n%4+j)*8+8≤2^31-1 ∧
      (j+1=n%4 ↔ n-n%4+j+1=n) := by omega

/-- A short prefix accounts for the remainder before the eight-way block loop.
Every callback receives the start of its block, in original order. -/
theorem blockEight (n k j : Int) (nBound : 0<n ∧ n≤(2^31-1)/136)
    (live : 0≤k ∧ k<n/8) (lane : 0≤j ∧ j<8) :
    (n%8+8*k+j-n%8)/8=k ∧ (n%8+8*k+j-n%8)%8=j ∧
      0≤(n%8+8*k+j)*136 ∧ (n%8+8*k+j+1)*136≤2^31-1 ∧
      (n%8+8*(k+1)=n ↔ k+1=n/8) ∧ n/8-(k+1)<n/8-k := by omega

theorem blockPrefix (n j : Int) (nBound : 0<n ∧ n≤(2^31-1)/136)
    (live : 0≤j ∧ j<n%8) :
    (n-1<7 ↔ n<8) ∧ j*136≥0 ∧ (j+1)*136≤n*136 ∧ n*136≤2^31-1 ∧
      n%8-(j+1)<n%8-j := by omega

end PeerShake.Buffer
