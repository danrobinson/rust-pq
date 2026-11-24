import Ideal.Sha.HmacShape
import MIdeal.State512
import MIdeal.SkPrf

namespace MIdeal.Sha512
open Ideal MLink SLHDSA SLHDSA.Concrete VCVio.Algorithms.Sha2
variable (S : Sha2Set)

private theorem width : S.vp.params.n ≤ 32 := by cases S <;> decide

def key0L (k : S.Node) : List UInt8 := k.toList ++ List.replicate (128-S.vp.params.n) 0

/-- The inner key block `(zero-padded key) ⊕ 0x36 repeated 128 times`. -/
def ikey (k : S.Node) : Block512 := ⟨((key0L S k).map (· ^^^ 0x36)).toArray, by simp [key0L]; have := width S; omega⟩

/-- The outer key block `(zero-padded key) ⊕ 0x5c repeated 128 times`. -/
def okey (k : S.Node) : Block512 := ⟨((key0L S k).map (· ^^^ 0x5c)).toArray, by simp [key0L]; have := width S; omega⟩

/-- The bytes of `pad(ikey ‖ r ‖ M)` after the key block. -/
def ibytes (r : S.Node) (M : List UInt8) : List UInt8 := r.toList ++ M ++ tailL ((128+S.vp.params.n) + M.length)

/-- The blocks of `pad(ikey ‖ r ‖ M)` after the key block. -/
def iblocks (r : S.Node) (M : List UInt8) : List Block512 := blocksOf (ibytes S r M)

/-- The single block of `pad(okey ‖ inner)` after the key block. -/
def oblock (s : Chain512) : Block512 := ⟨((serialize s).toList ++ tailL 192).toArray, by simp [tailL_length]⟩

theorem ikey_toList (k : S.Node) : (ikey S k).toList = (key0L S k).map (· ^^^ 0x36) := rfl
theorem okey_toList (k : S.Node) : (okey S k).toList = (key0L S k).map (· ^^^ 0x5c) := rfl
theorem oblock_toList (s : Chain512) : (oblock s).toList = (serialize s).toList ++ tailL 192 := rfl

theorem key0L_injective : Function.Injective (key0L S) := by
  intro a b h
  exact Vector.toList_inj.mp (List.append_inj h (by simp)).1

theorem ikey_injective : Function.Injective (ikey S) := by
  intro a b h
  have := congrArg Vector.toList h
  rw [ikey_toList, ikey_toList] at this
  exact key0L_injective S (List.map_injective_iff.mpr (xor_right_injective _) this)

theorem okey_injective : Function.Injective (okey S) := by
  intro a b h
  have := congrArg Vector.toList h
  rw [okey_toList, okey_toList] at this
  exact key0L_injective S (List.map_injective_iff.mpr (xor_right_injective _) this)

theorem key_blocks_distinct (k : S.Node) : ikey S k ≠ okey S k := by
  intro h
  have e := congrArg (fun b : Block512 => b.toList[S.vp.params.n]?) h
  have hw := width S
  simp [ikey, okey, key0L, List.getElem?_append_right, Vector.toList, show S.vp.params.n < 128 by omega] at e

theorem oblock_injective : Function.Injective oblock := by
  intro s t h
  have e := congrArg Vector.toList h
  rw [oblock_toList, oblock_toList] at e
  exact serialize_injective (Vector.toList_inj.mp (List.append_cancel_right e))

theorem ibytes_length (r : S.Node) (M : List UInt8) :
    (ibytes S r M).length = 128 * ((M.length + S.vp.params.n + 16) / 128 + 1) := by
  simp [ibytes, tailL_length]; omega

/-- Number of inner blocks after the key block. -/
theorem iblocks_length (r : S.Node) (M : List UInt8) :
    (iblocks S r M).length = (M.length + S.vp.params.n + 16) / 128 + 1 := by
  rw [iblocks, blocksOf_length, ibytes_length]; omega

theorem iblocks_ne_nil (r : S.Node) (M : List UInt8) : iblocks S r M ≠ [] := by
  intro h
  have := iblocks_length S r M
  rw [h] at this
  simp at this

/-- The inner blocks determine `(opt_rand, M)`. -/
theorem iblocks_injective {r r' : S.Node} {M M' : List UInt8}
    (h : iblocks S r M = iblocks S r' M') : r = r' ∧ M = M' := by
  have ht := blocksOf_injective _ _ (by rw [ibytes_length]; omega)
    (by rw [ibytes_length]; omega) h
  have h1 := strip_tail _ _ _ _ ht
  obtain ⟨h2, h3⟩ := List.append_inj h1 (by simp)
  exact ⟨Vector.toList_inj.mp h2, h3⟩

/-! ## HMAC bytes -/

theorem hmacKey0Sha512G_toList (c : Compress512Fn) (k : S.Node) :
    (hmacKey0Sha512G c (bytesToByteArray k)).data.toList = key0L S k := by
  have hs : (bytesToByteArray k).size = S.vp.params.n := by simp [bytesToByteArray, ByteArray.size]
  unfold hmacKey0Sha512G
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  simp [hs, show ¬ 128 < S.vp.params.n by have := width S; omega]
  rw [Ideal.push_loop]
  simp [bytesToByteArray, Vector.toList, key0L]

/-- The blocks of the inner hash input. -/
theorem padBlocks_inner (c : Compress512Fn) (k r : S.Node) (M : List UInt8) :
    padBlocks (xorConst (hmacKey0Sha512G c (bytesToByteArray k)) 0x36 ++
        (bytesToByteArray r ++ ByteArray.mk M.toArray)) = ikey S k :: iblocks S r M := by
  unfold padBlocks
  have e : (xorConst (hmacKey0Sha512G c (bytesToByteArray k)) 0x36 ++
        (bytesToByteArray r ++ ByteArray.mk M.toArray)).data.toList
      = (ikey S k).toList ++ (r.toList ++ M) := by
    simp only [ByteArray.data_append, Array.toList_append, xorConst_toList, hmacKey0Sha512G_toList,
      ikey_toList]
    rfl
  have e2 : padL ((ikey S k).toList ++ (r.toList ++ M)) = (ikey S k).toList ++ ibytes S r M := by
    simp only [padL, ibytes, List.append_assoc, List.length_append, Vector.length_toList]
    rw [show 128 + (S.vp.params.n + M.length) = (128+S.vp.params.n) + M.length by omega]
  rw [e, e2, blocksOf_cons, iblocks]

/-- The blocks of the outer hash input. -/
theorem padBlocks_outer (c : Compress512Fn) (k : S.Node) (s : Chain512) :
    padBlocks (xorConst (hmacKey0Sha512G c (bytesToByteArray k)) 0x5c ++ bytesToByteArray (serialize s))
      = [okey S k, oblock s] := by
  unfold padBlocks
  have e : (xorConst (hmacKey0Sha512G c (bytesToByteArray k)) 0x5c ++ bytesToByteArray (serialize s)).data.toList
      = (okey S k).toList ++ (serialize s).toList := by
    simp only [ByteArray.data_append, Array.toList_append, xorConst_toList, hmacKey0Sha512G_toList,
      okey_toList]
    rfl
  have e2 : padL ((okey S k).toList ++ (serialize s).toList) = (okey S k).toList ++ ((oblock s).toList ++ []) := by
    simp only [padL, oblock_toList, List.append_assoc, List.length_append, Vector.length_toList,
      List.append_nil]
  rw [e, e2, blocksOf_cons, blocksOf_cons]
  rfl


/-- The actual SHA-512 message PRF expanded into its compression table calls. -/
theorem msgPrf_shape (g : CompressionTables) (hw : S.vp.params.n ≠ 16) (k r : S.Node) (M : List UInt8) :
    (tablePrimitives g S.vp.params).PRFmsg k r M =
      byteArrayPrefixOrZero (stateBytes64 (g.2 (g.2 (initial,okey S k),
        oblock (mdFold g.2 (g.2 (initial,ikey S k)) (iblocks S r M)))).toArray) S.vp.params.n := by
  change sha2PRFmsgMixed _ _ k r M = _
  simp only [sha2PRFmsgMixed, if_neg hw, hmacSha512G, sha512_shape, padBlocks_inner,
    show ∀ s, stateBytes64 ((s : Chain512).toArray) = bytesToByteArray (serialize s) from fun _ => rfl,
    padBlocks_outer]
  rfl

end MIdeal.Sha512

#print axioms MIdeal.Sha512.msgPrf_shape
#print axioms MIdeal.Sha512.key_blocks_distinct
#print axioms MIdeal.Sha512.iblocks_injective
