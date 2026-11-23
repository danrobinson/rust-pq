import RcSlhSha2.Digest
import RcSlhSha2.Buffer

namespace slhdsa.RcSlhSha2
open Spec

def absorb (pre : Bytes) (parts : List Bytes) : Bytes := parts.foldl (· ++ ·) pre

theorem absorb_eq (pre : Bytes) (parts : List Bytes) :
    absorb pre parts = pre ++ parts.flatten := by
  induction parts generalizing pre with
  | nil => simp [absorb]
  | cons x xs ih =>
    change absorb (pre ++ x) xs = _
    rw [ih]; simp [List.append_assoc]

theorem absorb_buffer (width : Nat) (b : Buffer) (parts : List Bytes) :
    absorb b.bytes parts = (parts.foldl (feed width) b).bytes := by
  rw [absorb_eq, feed_many]

/-- Each mutable output chunk receives the pre of one new hash digest.
A checked u32 is written big-endian in exactly four bytes. -/
def mgf (hash : Bytes → Bytes) (width : Nat) (seed : Bytes) (len : Nat) : Bytes :=
  (List.range ((len+width-1)/width)).flatMap fun i =>
    (hash (seed ++ toByte (i % 2^32) 4)).take (min width (len - width*i))

/-- Short HMAC keys comprise every key supplied by these SLH parameter sets.
The second in-place XOR transforms the inner key block into the outer one. -/
def mac (hash : Bytes → Bytes) (width : Nat) (key msg : Bytes) : Bytes :=
  let paddedKey := key ++ List.replicate (width - key.length) 0#8
  let inner := paddedKey.map (· ^^^ 0x36#8)
  let outer := inner.map (fun b => b ^^^ (0x36#8 ^^^ 0x5c#8))
  hash (outer ++ hash (inner ++ msg))

private theorem outer_key (xs : Bytes) :
    (xs.map (· ^^^ 0x36#8)).map (fun b => b ^^^ (0x36#8 ^^^ 0x5c#8)) =
      xs.map (· ^^^ 0x5c#8) := by
  simp [List.map_map, Function.comp_def, BitVec.xor_assoc]

theorem mac256 (key msg : Bytes) (h : key.length ≤ 64) :
    mac digest256 64 key msg = hmacSha256 key msg := by
  simp only [mac,digest256_eq,outer_key,hmacSha256,ite_eq_right (Nat.not_lt.mpr h)]

theorem mac512 (key msg : Bytes) (h : key.length ≤ 128) :
    mac digest512 128 key msg = hmacSha512 key msg := by
  simp only [mac,digest512_eq,outer_key,hmacSha512,ite_eq_right (Nat.not_lt.mpr h)]

private theorem chunks1 (hash : Bytes → Bytes) (width len : Nat) (seed : Bytes)
    (one : (len+width-1)/width=1) (short : len≤width) :
    mgf hash width seed len = Spec.mgf1 hash width seed len := by
  simp [mgf,Spec.mgf1,one,List.range_succ,Nat.min_eq_right short]

private theorem chunks2 (hash : Bytes → Bytes) (width len : Nat) (seed : Bytes)
    (size : ∀ b, (hash b).length = width) (two : (len+width-1)/width=2) (long : width ≤ len)
    (room : len-width ≤ width) : mgf hash width seed len = Spec.mgf1 hash width seed len := by
  simp only [mgf,Spec.mgf1,two,show List.range 2 = [0,1] by decide,List.flatMap_cons,
    List.flatMap_nil,List.append_nil, Nat.mul_zero, Nat.sub_zero,Nat.min_eq_left long,
    Nat.mul_one,Nat.min_eq_right room]
  simp only [show 0 % 2^32 = 0 by decide,show 1 % 2^32 = 1 by decide]
  have h0 : (hash (seed ++ toByte 0 4)).length = width := size _
  rw [List.take_of_length_le (h0.le),List.take_append, h0]
  rw [List.take_of_length_le (h0.le.trans long)]

theorem mgf256 (seed : Bytes) (m : Nat) (sizes : m=30 ∨ m=34) :
    mgf digest256 32 seed m = Spec.mgf1 sha256 32 seed m := by
  rw [digest256_eq]
  rcases sizes with rfl | rfl
  · apply chunks1 <;> decide
  · apply chunks2 _ _ _ _ sha256_length <;> decide

theorem mgf512 (seed : Bytes) (m : Nat) (sizes : m=39 ∨ m=42 ∨ m=47 ∨ m=49) :
    mgf digest512 64 seed m = Spec.mgf1 sha512 64 seed m := by
  rw [digest512_eq]
  rcases sizes with rfl | rfl | rfl | rfl <;> apply chunks1 <;> decide

end slhdsa.RcSlhSha2
