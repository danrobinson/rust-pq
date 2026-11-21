import Ideal.Sha.Shape

/-!
# Shape of `PRF_msg = Trunc_16(HMAC-SHA-256(SK.prf, opt_rand ‖ M))` at SLH-DSA-SHA2-128s

For every table `g : CF St Blk` (`msgPrf_shape`):

`(primsG (liftC g)).PRFmsg k r M
   = out16 (g (g (IV128, okey k), oblock (mdFold g (g (IV128, ikey k)) (iblocks r M))))`

where `ikey k = (k ‖ 0^48) ⊕ 0x36^64`, `okey k = (k ‖ 0^48) ⊕ 0x5c^64`, `iblocks r M` are the
blocks of `r ‖ M ‖ pad` (the SHA-256 padding of the `80 + |M|`-byte inner message, after its key
block) and `oblock s = s ‖ 0x80 ‖ 0^21 ‖ len(96)` is the single block after the outer key block.
-/

namespace Ideal

open SLHDSA SLHDSA.Concrete VCVio.Algorithms.Sha2

/-! ## The blocks -/

/-- The HMAC key block `k ‖ 0^48`, as a byte list. -/
def key0L (k : Bytes 16) : List UInt8 := k.toList ++ List.replicate 48 0

/-- The inner key block `(k ‖ 0^48) ⊕ 0x36^64`. -/
def ikey (k : Bytes 16) : Blk := ⟨((key0L k).map (· ^^^ 0x36)).toArray, by simp [key0L]⟩

/-- The outer key block `(k ‖ 0^48) ⊕ 0x5c^64`. -/
def okey (k : Bytes 16) : Blk := ⟨((key0L k).map (· ^^^ 0x5c)).toArray, by simp [key0L]⟩

/-- The bytes of `pad(ikey ‖ r ‖ M)` after the key block. -/
def ibytes (r : Bytes 16) (M : List UInt8) : List UInt8 := r.toList ++ M ++ tailL (80 + M.length)

/-- The blocks of `pad(ikey ‖ r ‖ M)` after the key block. -/
def iblocks (r : Bytes 16) (M : List UInt8) : List Blk := blocksOf (ibytes r M)

/-- The single block of `pad(okey ‖ inner)` after the key block. -/
def oblock (s : St) : Blk := ⟨(s.toList ++ tailL 96).toArray, by simp [tailL_length]⟩

theorem ikey_toList (k : Bytes 16) : (ikey k).toList = (key0L k).map (· ^^^ 0x36) := rfl
theorem okey_toList (k : Bytes 16) : (okey k).toList = (key0L k).map (· ^^^ 0x5c) := rfl
theorem oblock_toList (s : St) : (oblock s).toList = s.toList ++ tailL 96 := rfl

theorem xor_right_injective (c : UInt8) : Function.Injective fun x : UInt8 => x ^^^ c := by
  intro a b h
  have h' : (a ^^^ c) ^^^ c = (b ^^^ c) ^^^ c := congrArg (· ^^^ c) h
  simpa [UInt8.xor_assoc] using h'

theorem key0L_injective : Function.Injective key0L := by
  intro a b h
  exact Vector.toList_inj.mp (List.append_inj h (by simp)).1

theorem ikey_injective : Function.Injective ikey := by
  intro a b h
  have := congrArg Vector.toList h
  rw [ikey_toList, ikey_toList] at this
  exact key0L_injective (List.map_injective_iff.mpr (xor_right_injective _) this)

theorem okey_injective : Function.Injective okey := by
  intro a b h
  have := congrArg Vector.toList h
  rw [okey_toList, okey_toList] at this
  exact key0L_injective (List.map_injective_iff.mpr (xor_right_injective _) this)

theorem ikey_get16 (k : Bytes 16) : (ikey k).toList[16]? = some 0x36 := by
  rw [ikey_toList, key0L, List.map_append, List.getElem?_append_right (by simp)]
  simp

theorem okey_get16 (k : Bytes 16) : (okey k).toList[16]? = some 0x5c := by
  rw [okey_toList, key0L, List.map_append, List.getElem?_append_right (by simp)]
  simp

/-- Inner and outer key blocks are never equal. -/
theorem ikey_ne_okey (k k' : Bytes 16) : ikey k ≠ okey k' := by
  intro h
  have h1 := ikey_get16 k
  rw [h, okey_get16] at h1
  exact absurd (Option.some.inj h1) (by decide)

theorem oblock_injective : Function.Injective oblock := by
  intro a b h
  have := congrArg Vector.toList h
  rw [oblock_toList, oblock_toList] at this
  exact Vector.toList_inj.mp (List.append_inj this (by simp)).1

theorem ibytes_length (r : Bytes 16) (M : List UInt8) :
    (ibytes r M).length = 64 * ((M.length + 24) / 64 + 1) := by
  simp [ibytes, tailL_length]; omega

/-- Number of inner blocks after the key block. -/
theorem iblocks_length (r : Bytes 16) (M : List UInt8) :
    (iblocks r M).length = (M.length + 24) / 64 + 1 := by
  rw [iblocks, blocksOf_length, ibytes_length]; omega

theorem iblocks_ne_nil (r : Bytes 16) (M : List UInt8) : iblocks r M ≠ [] := by
  intro h
  have := iblocks_length r M
  rw [h] at this
  simp at this

/-- The inner blocks determine `(opt_rand, M)`. -/
theorem iblocks_injective {r r' : Bytes 16} {M M' : List UInt8}
    (h : iblocks r M = iblocks r' M') : r = r' ∧ M = M' := by
  have ht := blocksOf_injective _ _ (by rw [ibytes_length]; omega)
    (by rw [ibytes_length]; omega) h
  have h1 := strip_tail _ _ _ _ ht
  obtain ⟨h2, h3⟩ := List.append_inj h1 (by simp)
  exact ⟨Vector.toList_inj.mp h2, h3⟩

/-! ## HMAC bytes -/

theorem hmacKey0G_toList (c : CompressFn) (k : Bytes 16) :
    (hmacKey0G c (bytesToByteArray k)).data.toList = key0L k := by
  have hs : (bytesToByteArray k).size = 16 := by simp [bytesToByteArray, ByteArray.size]
  unfold hmacKey0G
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  simp [hs]
  rw [push_loop]
  simp [bytesToByteArray, Vector.toList, key0L]

theorem xor_loop (b : ByteArray) (c : UInt8) (l : List Nat) (out : ByteArray) :
    (l.foldl (fun o i => o.push (b[i]! ^^^ c)) out).data.toList
      = out.data.toList ++ l.map (fun i => b[i]! ^^^ c) := by
  induction l generalizing out with
  | nil => simp
  | cons x xs ih => rw [List.foldl_cons, ih]; simp

theorem xorConst_toList (b : ByteArray) (c : UInt8) :
    (xorConst b c).data.toList = b.data.toList.map (· ^^^ c) := by
  unfold xorConst
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  simp
  rw [xor_loop]
  simp
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp at h1 h2 ⊢
    rw [ba_get, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using h1)]
    simp

/-- The blocks of the inner hash input. -/
theorem padBlocks_inner (c : CompressFn) (k r : Bytes 16) (M : List UInt8) :
    padBlocks (xorConst (hmacKey0G c (bytesToByteArray k)) 0x36 ++
        (bytesToByteArray r ++ ByteArray.mk M.toArray)) = ikey k :: iblocks r M := by
  unfold padBlocks
  have e : (xorConst (hmacKey0G c (bytesToByteArray k)) 0x36 ++
        (bytesToByteArray r ++ ByteArray.mk M.toArray)).data.toList
      = (ikey k).toList ++ (r.toList ++ M) := by
    simp only [ByteArray.data_append, Array.toList_append, xorConst_toList, hmacKey0G_toList,
      ikey_toList]
    rfl
  have e2 : padL ((ikey k).toList ++ (r.toList ++ M)) = (ikey k).toList ++ ibytes r M := by
    simp only [padL, ibytes, List.append_assoc, List.length_append, Vector.length_toList]
    rw [show 64 + (16 + M.length) = 80 + M.length by omega]
  rw [e, e2, blocksOf_cons, iblocks]

/-- The blocks of the outer hash input. -/
theorem padBlocks_outer (c : CompressFn) (k : Bytes 16) (s : St) :
    padBlocks (xorConst (hmacKey0G c (bytesToByteArray k)) 0x5c ++ digestBytes s)
      = [okey k, oblock s] := by
  unfold padBlocks
  have e : (xorConst (hmacKey0G c (bytesToByteArray k)) 0x5c ++ digestBytes s).data.toList
      = (okey k).toList ++ s.toList := by
    simp only [ByteArray.data_append, Array.toList_append, xorConst_toList, hmacKey0G_toList,
      okey_toList]
    rfl
  have e2 : padL ((okey k).toList ++ s.toList) = (okey k).toList ++ ((oblock s).toList ++ []) := by
    simp only [padL, oblock_toList, List.append_assoc, List.length_append, Vector.length_toList,
      List.append_nil]
  rw [e, e2, blocksOf_cons, blocksOf_cons]
  rfl

/-- **Shape of `PRF_msg` at SLH-DSA-SHA2-128s over a table.** -/
theorem msgPrf_shape (g : CF St Blk) (k r : Bytes 16) (M : List UInt8) :
    (primsG (liftC g)).PRFmsg k r M =
      out16 (g (g (IV128, okey k), oblock (mdFold g (g (IV128, ikey k)) (iblocks r M)))) := by
  show sha2PRFmsgG (liftC g) (n := 16) k r M = _
  simp only [sha2PRFmsgG, ite_true, hmacSha256G, sha256G_shape, padBlocks_inner, padBlocks_outer,
    prefix_out16]
  rfl

end Ideal

#print axioms Ideal.msgPrf_shape
#print axioms Ideal.ikey_injective
#print axioms Ideal.okey_injective
#print axioms Ideal.ikey_ne_okey
#print axioms Ideal.iblocks_injective
#print axioms Ideal.iblocks_length
#print axioms Ideal.oblock_injective
