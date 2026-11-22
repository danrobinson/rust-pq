import Ideal.Games.PrfFine
import Ideal.Inst.SkPrf128

/-!
# PRF security on the secret-key address domain at SLH-DSA-SHA2-128s, marked form

`skPrf_bound_128s_marked`: as `skPrf_bound_128s`, with the `2^-128` term charged only to the
`qM` compression queries whose block is a key block `blk128 a k` of SOME secret-key address `a`
and key `k` (`Prf.markQ blk128`).  The other compression queries enter only the birthday term.

`blk128_take22`: the first 22 bytes of a key block are the compressed address, so a block whose
first 22 bytes are not the key of a secret-key address is never marked.
-/

open OracleComp OracleSpec ENNReal PRFScheme SLHDSA SLHDSA.Concrete

namespace Ideal

/-- **PRF security on the secret-key address domain at SLH-DSA-SHA2-128s, marked form.** -/
theorem skPrf_bound_128s_marked (A : PrfAdvI St Blk (Bytes 16) SkAd (Bytes 16)) (qM q qO : ℕ)
    (hqM : IsQueryBoundP A (Prf.markQ blk128) qM)
    (hq : IsQueryBoundP A (fun i => isCompQ i = true) q)
    (hO : IsQueryBoundP A (fun i => isPrfQ i = true) qO) :
    skPrfAdvantageI A ≤
      (qM : ℝ≥0∞) / 2 ^ 128 + (((q + qO) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  let : Fintype SkAd := Fintype.ofFinite SkAd
  rw [skPrfAdvantageI_eq]
  refine (prfAdvantageI_le_marked IV128 sb128 blk128 out16 blk128_injective sb128_ne_blk128
    sb128_injective prEvent_out16 A qM q qO hqM hq hO).trans (le_of_eq ?_)
  rw [card_bytes 16, card_St, div_eq_mul_inv, div_eq_mul_inv]
  norm_num

/-- Byte `j < 22` of the first block of `tblocks a xs` is byte `j` of the address key `a`. -/
theorem tblocks_fst_get_lt (a : Bytes 22) (xs : List (Bytes 16)) (j : ℕ) (hj : j < 22) :
    (tblocks a xs).1[j]'(by omega) = a[j] := by
  rw [tblocks_fst_eq]
  simp only [Vector.getElem_ofFn, tbytes]
  rw [List.getD_eq_getElem?_getD, List.append_assoc, List.getElem?_append_left (by simpa using hj)]
  rw [List.getElem?_eq_getElem (by simpa using hj)]
  simp

/-- A first `tblocks` block equal to a key block carries the key's address. -/
theorem key_of_tblocks_eq_blk128 {key : Bytes 22} {xs : List (Bytes 16)} {a : SkAd} {k : Bytes 16}
    (h : (tblocks key xs).1 = blk128 a k) : key = sha2AdrsKey a.val := by
  apply Vector.ext
  intro j hj
  have h1 := congrArg (fun v : Blk => v[j]'(by omega)) h
  simp only [blk128] at h1
  rwa [tblocks_fst_get_lt _ _ j hj, tblocks_fst_get_lt _ _ j hj] at h1

end Ideal

#print axioms Ideal.skPrf_bound_128s_marked
#print axioms Ideal.key_of_tblocks_eq_blk128
