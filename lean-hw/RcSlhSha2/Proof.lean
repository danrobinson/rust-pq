import RcSlhSha2.Suite
import Slhdsa.Proofs.Hash

namespace slhdsa.RcSlhSha2
open Spec

inductive StandardSet where
  | s128 | f128 | s192 | f192 | s256 | f256

def config : StandardSet → Bool × Nat × Nat
  | .s128 => suite128s | .f128 => suite128f
  | .s192 => suite192s | .f192 => suite192f
  | .s256 => suite256s | .f256 => suite256f

def params : StandardSet → Params
  | .s128 => sha2_128s | .f128 => sha2_128f
  | .s192 => sha2_192s | .f192 => sha2_192f
  | .s256 => sha2_256s | .f256 => sha2_256f

structure Hashes where
  prf : Bytes
  f : Bytes
  h : Bytes
  t : Bytes
  hmsg : Bytes
  prfmsg : Bytes

def suite (s : StandardSet) (seed addr secret m1 m2 : Bytes) (rows : List Bytes)
    (r root key rand : Bytes) (msg : List (List Bytes)) : Hashes :=
  let (levelOne,n,m) := config s
  if levelOne then
    ⟨l1_prf_sk n seed addr secret, l1_f n seed addr m1, l1_h n seed addr m1 m2,
     l1_t n seed addr rows, l1_hmsg m r seed root msg, l1_prfmsg n key rand msg⟩
  else
    ⟨l35_prf_sk n seed addr secret, l35_f n seed addr m1, l35_h n seed addr m1 m2,
     l35_t n seed addr rows, l35_hmsg m r seed root msg, l35_prfmsg n key rand msg⟩

def standard (p : Params) (seed : Bytes) (addr : Adrs) (secret m1 m2 : Bytes) (rows : List Bytes)
    (r root key rand : Bytes) (msg : List (List Bytes)) : Hashes :=
  ⟨PRF p seed secret addr, F p seed addr m1, H p seed addr (m1 ++ m2),
   T p seed addr rows.flatten, Hmsg p r seed root msg.flatten.flatten,
   PRFmsg p key rand msg.flatten.flatten⟩

theorem compressed_eq (a : Adrs) : compressed a.bytes = a.compress := rfl

attribute [local irreducible] digest256 digest512 SHA256.sha256 SHA512.sha512
  Spec.hmacSha256 Spec.hmacSha512 Spec.mgf1 mgf mac absorb

/-- All six functions, for all six standard SHA-2 parameter sets. All message
fragments and tweakable-hash rows are arbitrary, including empty fragments.
The array-typed key is exactly n bytes in the original Rust interface. -/
theorem suite_is_fips (s : StandardSet) (seed : Bytes) (addr : Adrs) (secret m1 m2 : Bytes)
    (rows : List Bytes) (r root key rand : Bytes) (msg : List (List Bytes))
    (hk : key.length = (params s).n) :
    suite s seed addr.bytes secret m1 m2 rows r root key rand msg =
      standard (params s) seed addr secret m1 m2 rows r root key rand msg := by
  have short : key.length ≤ 64 := by rw [hk]; cases s <;> decide
  have small : key.length ≤ 128 := by omega
  have mg30 (seed : Bytes) := mgf256 seed 30 (Or.inl rfl)
  have mg34 (seed : Bytes) := mgf256 seed 34 (Or.inr rfl)
  have mg39 (seed : Bytes) := mgf512 seed 39 (Or.inl rfl)
  have mg42 (seed : Bytes) := mgf512 seed 42 (Or.inr (Or.inl rfl))
  have mg47 (seed : Bytes) := mgf512 seed 47 (Or.inr (Or.inr (Or.inl rfl)))
  have mg49 (seed : Bytes) := mgf512 seed 49 (Or.inr (Or.inr (Or.inr rfl)))
  have mc256 := fun msg => mac256 key msg short
  have mc512 := fun msg => mac512 key msg small
  simp only [digest256_eq, digest512_eq] at mg30 mg34 mg39 mg42 mg47 mg49 mc256 mc512
  cases s <;>
    simp [suite,standard,params,config,suite128s,suite128f,suite192s,suite192f,suite256s,suite256f,
      sha2_128s,sha2_128f,sha2_192s,sha2_192f,sha2_256s,sha2_256f, F,H,T,PRF,Hmsg,PRFmsg,
      l1_f,l1_h,l1_t,l1_prf_sk,l1_hmsg,l1_prfmsg,l35_f,l35_h,l35_t,l35_prf_sk,l35_hmsg,l35_prfmsg,
      l1_cached_hasher,l35_cached_hasher_256,l35_cached_hasher_512,compressed_eq,absorb_eq,
      toByte_zero,mc256,mc512,mg30,mg34,mg39,mg42,mg47,mg49,
      digest256_eq,digest512_eq,List.append_assoc]

/-- Every checked usize-to-u32 conversion in the peer MGF succeeds. -/
theorem mgf_counter_fits (s : StandardSet) :
    let (levelOne,_,m) := config s
    let width := if levelOne then 32 else 64
    ∀ i < (m+width-1)/width, i < 2^32 := by
  cases s <;> dsimp [config,suite128s,suite128f,suite192s,suite192f,suite256s,suite256f] <;> omega

/-- The machine bit counter agrees with the unbounded padding equation on
the permitted FIPS 180-4 message domain (bytes < 2^61 or 2^125). -/
theorem machine_length (bytes : Nat) :
    (bytes < 2^61 → 8 * (bytes % 64 + 64 * (bytes / 64)) < 2^64) ∧
    (bytes < 2^125 → 8 * (bytes % 128 + 128 * (bytes / 128)) < 2^128) := by
  simp only [Nat.mod_add_div]; constructor <;> omega

end slhdsa.RcSlhSha2
