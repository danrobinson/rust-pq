import Slhdsa.Proofs.Hash

open Aeneas Aeneas.Std Result
namespace slhdsa

private theorem full_eq (x : Spec.Adrs) : x.bytes =
    [BitVec.ofNat 8 (x.layer >>> 24),
      BitVec.ofNat 8 (x.layer >>> 16),
      BitVec.ofNat 8 (x.layer >>> 8),
      BitVec.ofNat 8 x.layer,
      BitVec.ofNat 8 (x.tree >>> 88),
      BitVec.ofNat 8 (x.tree >>> 80),
      BitVec.ofNat 8 (x.tree >>> 72),
      BitVec.ofNat 8 (x.tree >>> 64),
      BitVec.ofNat 8 (x.tree >>> 56),
      BitVec.ofNat 8 (x.tree >>> 48),
      BitVec.ofNat 8 (x.tree >>> 40),
      BitVec.ofNat 8 (x.tree >>> 32),
      BitVec.ofNat 8 (x.tree >>> 24),
      BitVec.ofNat 8 (x.tree >>> 16),
      BitVec.ofNat 8 (x.tree >>> 8),
      BitVec.ofNat 8 x.tree,
      BitVec.ofNat 8 (x.typ >>> 24),
      BitVec.ofNat 8 (x.typ >>> 16),
      BitVec.ofNat 8 (x.typ >>> 8),
      BitVec.ofNat 8 x.typ,
      BitVec.ofNat 8 (x.keypair >>> 24),
      BitVec.ofNat 8 (x.keypair >>> 16),
      BitVec.ofNat 8 (x.keypair >>> 8),
      BitVec.ofNat 8 x.keypair,
      BitVec.ofNat 8 (x.word2 >>> 24),
      BitVec.ofNat 8 (x.word2 >>> 16),
      BitVec.ofNat 8 (x.word2 >>> 8),
      BitVec.ofNat 8 x.word2,
      BitVec.ofNat 8 (x.word3 >>> 24),
      BitVec.ofNat 8 (x.word3 >>> 16),
      BitVec.ofNat 8 (x.word3 >>> 8),
      BitVec.ofNat 8 x.word3] := rfl

/-- SHAKE hashes the full 32-byte ADRS, including the high zero word of the
96-bit tree field. This holds for every Rust address. -/
@[step] theorem adrs_full_spec (a : address.Adrs) :
    address.Adrs.full a ⦃ out => bytes out.val = (adrsS a).bytes ⦄ := by
  unfold address.Adrs.full
  step*
  rw [full_eq]
  have high (k : Nat) (hk : 64 ≤ k) : a.tree.val >>> k = 0 := by
    rw [Nat.shiftRight_eq_div_pow]
    apply Nat.div_eq_of_lt
    have bound : a.tree.val < 2^64 := a.tree.hBounds
    exact lt_of_lt_of_le bound (Nat.pow_le_pow_right (by decide) hk)
  simp [bytes, adrsS, setWidth_shr64, setWidth_shr32, high _ (by decide : 64 ≤ 88),
    high _ (by decide : 64 ≤ 80), high _ (by decide : 64 ≤ 72), high _ (by decide : 64 ≤ 64), *]

#print axioms adrs_full_spec
end slhdsa
