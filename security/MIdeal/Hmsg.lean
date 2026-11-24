import Ideal.Sha.HmsgShape
import MIdeal.State512

namespace MIdeal.Hmsg
open MLink Ideal SLHDSA SLHDSA.Concrete VCVio.Algorithms.Sha2

/-- 128f requires two MGF1 counters to produce the 34-byte digest. -/
theorem mgf128f (c : CompressFn) (seed : ByteArray) :
    mgf1G c seed 34 = (sha256G c (seed ++ u32be 0) ++ sha256G c (seed ++ u32be 1)).extract 0 34 := by
  unfold mgf1G
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  simp
  rw [show List.range' 0 2 = [0,1] from rfl]
  simp

def counterBlocks (r pk : Bytes 16) (s : St) (ctr : UInt32) :=
  padBlocks (bytesToByteArray r ++ bytesToByteArray pk ++ digestBytes s ++ u32be ctr)

theorem counter_length (r pk : Bytes 16) (s : St) (ctr : UInt32) :
    (counterBlocks r pk s ctr).length = 2 := by
  rw [counterBlocks, padBlocks_length]
  simp [digestBytes, bytesToByteArray, ByteArray.size, u32be]

theorem counter_injective (r pk : Bytes 16) (s : St) :
    counterBlocks r pk s 0 ≠ counterBlocks r pk s 1 := by
  intro h
  have e := padBlocks_injective h
  have e' := congrArg (fun b : ByteArray => b.data.toList) e
  simp only [ByteArray.data_append, Array.toList_append, List.append_right_inj] at e'
  contradiction

theorem hmsg_128f (g : CompressionTables) (r pk root : Bytes 16) (m : List Byte) :
    (tablePrimitives g Sha2Set.s128f.vp.params).Hmsg r pk root m =
      let s := mdFold g.1 IV128 (iblocksH r pk root m)
      let block := fun ctr => digestBytes (mdFold g.1 IV128 (counterBlocks r pk s ctr))
      byteArrayPrefixOrZero ((block 0 ++ block 1).extract 0 34) 34 := by
  change byteArrayPrefixOrZero (mgf1G (liftC g.1) (bytesToByteArray r ++ bytesToByteArray pk ++
    sha256G (liftC g.1) (hInner r pk root m)) 34) 34 = _
  rw [mgf128f, sha256G_shape, sha256G_shape, sha256G_shape]
  rfl

private theorem mgf_wide (c : Compress512Fn) (seed : ByteArray) (len : ℕ)
    (h : (len+63)/64 = 1) :
    mgf1Sha512G c seed len = (sha512G c (seed ++ u32be 0)).extract 0 len := by
  unfold mgf1Sha512G
  simp only [h, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  simp

variable (S : Sha2Set)

def inner (r pk root : S.Node) (m : List Byte) :=
  Sha512.padBlocks (bytesToByteArray r ++ bytesToByteArray pk ++ bytesToByteArray root ++ ByteArray.mk m.toArray)

def outer (r pk : S.Node) (st : Chain512) :=
  Sha512.padBlocks (bytesToByteArray r ++ bytesToByteArray pk ++ stateBytes64 st.toArray ++ u32be 0)

theorem outer_length (hw : S.vp.params.n ≠ 16) (r pk : S.Node) (s : Chain512) :
    (outer S r pk s).length = 2 := by
  rw [outer, Sha512.padBlocks_length]
  simp only [ByteArray.size_append, stateBytes64_size, show (u32be 0).size = 4 from rfl]
  have size (v : S.Node) : (bytesToByteArray v).size = S.vp.params.n := by simp [bytesToByteArray, ByteArray.size]
  rw [size, size]
  have width : S.vp.params.n = 16 ∨ S.vp.params.n = 24 ∨ S.vp.params.n = 32 := by cases S <;> decide +kernel
  rcases width.resolve_left hw with w|w <;> rw [w] <;> decide

theorem hmsg_wide (g : CompressionTables) (hw : S.vp.params.n ≠ 16) (r pk root : S.Node) (m : List Byte) :
    (tablePrimitives g S.vp.params).Hmsg r pk root m =
      let s := mdFold g.2 Sha512.initial (inner S r pk root m)
      let result := mdFold g.2 Sha512.initial (outer S r pk s)
      byteArrayPrefixOrZero ((stateBytes64 result.toArray).extract 0 S.vp.params.m) S.vp.params.m := by
  change sha2HmsgMixed _ _ S.vp.params r pk root m = _
  have h : (S.vp.params.m + 63)/64 = 1 := by cases S <;> decide
  simp only [sha2HmsgMixed, ite_eq_right hw, mgf_wide _ _ _ h, Sha512.sha512_shape]
  rfl
end MIdeal.Hmsg

#print axioms MIdeal.Hmsg.hmsg_128f
#print axioms MIdeal.Hmsg.counter_injective
#print axioms MIdeal.Hmsg.hmsg_wide
