import Armwide.PackProgram
import Armwide.SignStores
import Slhdsa.Proofs.Hash
namespace slhdsa.Armwide.Transitions
open Spec.SHA256
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- Codes below 256 are literal bytes. The next eight inputs are two u32 header
words in big-endian order, followed by the bytes of the incoming digest registers. -/
private def operand (c t : Nat) (lo hi : Arm.V) (v : Nat) : Spec.Byte :=
  if v < 256 then BitVec.ofNat 8 v
  else if v < 260 then (Spec.toByte c 4)[v-256]!
  else if v < 264 then (Spec.toByte t 4)[v-260]!
  else ((vwords lo ++ vwords hi).flatMap Arm.beBytes)[v-264]!

def nativeBlock (n : Nat) (a : Spec.Adrs) (c t : Nat) (lo hi : Arm.V) : Spec.Bytes :=
  ({a with word2 := 0, word3 := 0}.compress.take 16) ++ (packIndices n).map (operand c t lo hi)

theorem native_block_padded (n : Nat) (hn : n=16 ∨ n=24 ∨ n=32) (a : Spec.Adrs)
    (c t : Nat) (hc : c < 65536) (lo hi : Arm.V) :
    nativeBlock n a c t lo hi = padFrom 64 ({a with word2 := c, word3 := t}.compress ++ Kernel.storeN n lo hi) := by
  have size : (Kernel.storeN n lo hi).length = n := by rcases hn with rfl|rfl|rfl <;> rfl
  have high16 : c >>> 16 = 0 := by rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_eq_of_lt hc
  have high24 : c >>> 24 = 0 := by rw [Nat.shiftRight_eq_div_pow]; apply Nat.div_eq_of_lt; omega
  rw [padFrom_blk _ _ (by omega),size,compress_eq]
  unfold nativeBlock
  rw [compress_eq]
  dsimp only
  rw [high16,high24]
  rcases hn with rfl|rfl|rfl <;> rfl

/-- Use the saved four-round head prepared before the chain and the three vectors produced
by the live make_hdr and pack_short functions for this chain and step. -/
def hashRegisters (n : Nat) (st : List Word) (a : Spec.Adrs) (c t : Nat) (lo hi : Arm.V) : Arm.V × Arm.V :=
  let base := {a with word2 := 0, word3 := 0}
  let (m0,a1,e1) := Kernel.makeHead st base.compress
  let b := nativeBlock n a c t lo hi
  Kernel.finishFromR4 (n != 16) st a1 e1 m0 (beV b 16) (beV b 32) (beV b 48)

private theorem head_same (st : List Word) (n : Nat) (a : Spec.Adrs) (c t : Nat) (lo hi : Arm.V) :
    Kernel.makeHead st {a with word2 := 0,word3 := 0}.compress = Kernel.makeHead st (nativeBlock n a c t lo hi) := by
  unfold Kernel.makeHead nativeBlock
  rw [compress_eq]
  rfl

/-- The value written from the two SHA-256 result registers is exactly the FIPS 205
seeded short tweakable hash at the current chain index and step. -/
theorem native_tweakable_hash (n : Nat) (hn : n=16 ∨ n=24 ∨ n=32) (pk : Spec.Bytes)
    (hpk : pk.length=n) (a : Spec.Adrs) (c t : Nat) (hc : c < 65536) (lo hi : Arm.V) :
    let out := hashRegisters n (seedState n pk) a c t lo hi
    storedBytes n out.1 out.2 = th256 n pk {a with word2:=c,word3:=t} (Kernel.storeN n lo hi) := by
  have size : (Kernel.storeN n lo hi).length = n := by rcases hn with rfl|rfl|rfl <;> rfl
  have bs := native_block_padded n hn a c t hc lo hi
  have bl : (nativeBlock n a c t lo hi).length=64 := by rw [bs]; exact padFrom_blk_length _ _ (by omega)
  have ss : (seedState n pk).length=8 := by simp [seedState,compress]
  simp only [hashRegisters,head_same (seedState n pk) n a c t lo hi,stored_eq n hn]
  apply Eq.trans (Kernel.finishFromR4_storeN_eq_fips n hn _ ss _ bl)
  rw [bs]
  exact th256_one n pk hpk (by omega) _ _ (by omega)

end slhdsa.Armwide.Transitions
