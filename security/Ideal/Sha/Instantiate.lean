import Ideal.Sha.Generic
import Ideal.Core.Defs
import Link.Sha256

/-!
# Finite compression tables and the real SHA-256 compression function as a table

`St := Bytes 32` is the big-endian serialisation of the eight SHA-256 chaining words and
`Blk := Bytes 64` a message block.  `liftC g` turns a table `g : CF St Blk` into a compression
function of VCVio's shape (`Array UInt32 → ByteArray → Nat → Array UInt32`), and `realCF` is the
table of the real compression function: `liftC realCF = VCVio.Algorithms.Sha2.compress`
(`liftC_realCF`).  Hence `primsG (liftC realCF) = Link.prims`: the ideal model is the real
construction with only the compression function replaced.
-/

namespace Ideal

open SLHDSA SLHDSA.Concrete VCVio.Algorithms.Sha2

/-- Chaining values: 32 bytes (big-endian serialisation of the 8 state words). -/
abbrev St := Bytes 32
/-- Message blocks: 64 bytes. -/
abbrev Blk := Bytes 64

instance : DecidableEq St := inferInstance
instance : DecidableEq Blk := inferInstance
instance : Fintype St := inferInstance
instance : Fintype Blk := inferInstance
instance : SampleableType St := inferInstance
instance : SampleableType Blk := inferInstance
noncomputable instance : SampleableType (CF St Blk) := inferInstance

/-- `Bytes n` has `256 ^ n` elements. -/
theorem card_bytes (n : ℕ) : Fintype.card (Bytes n) = 256 ^ n := by
  rw [← Nat.card_eq_fintype_card]
  change Nat.card (Vector UInt8 n) = 256 ^ n
  rw [Nat.card_congr (arrayVectorEquivFin UInt8 n), Nat.card_fun, Nat.card_eq_fintype_card,
    ← FinEnum.card_eq_fintypeCard, FinEnum.card_UInt8, Nat.card_eq_fintype_card,
    Fintype.card_fin]
  norm_num

theorem card_St : Fintype.card St = 2 ^ 256 := by
  rw [card_bytes]; norm_num

theorem card_Blk : Fintype.card Blk = 2 ^ 512 := by
  rw [card_bytes, show (256 : ℕ) = 2 ^ 8 from rfl, ← pow_mul]

/-! ## Big-endian words -/

/-- Big-endian word from four bytes (as in `readWord256`). -/
def beWord (a b c d : UInt8) : UInt32 :=
  a.toUInt32 <<< 24 ||| b.toUInt32 <<< 16 ||| c.toUInt32 <<< 8 ||| d.toUInt32

theorem beWord_bytes (x : UInt32) :
    beWord (x >>> 24).toUInt8 (x >>> 16).toUInt8 (x >>> 8).toUInt8 x.toUInt8 = x := by
  apply UInt32.eq_of_toBitVec_eq
  rw [beWord, Link.be32]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [Link.app4]
  simp
  split_ifs with h1 h2 h3
  · simp [h1]
  · rw [show 8 + (i - 8) = i by omega]; simp; omega
  · rw [show 16 + (i - 16) = i by omega]; simp; omega
  · rw [show 24 + (i - 24) = i by omega]; simp; omega

theorem byte0 (a b c d : UInt8) : (beWord a b c d >>> 24).toUInt8 = a := by
  apply UInt8.eq_of_toBitVec_eq
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have ge : ∀ (x : BitVec 8) (j : Nat), 8 ≤ j → x.getLsbD j = false :=
    fun x j h => BitVec.getLsbD_of_ge x j h
  simp [beWord, hi, show i < 32 by omega, show 24 + i < 32 by omega,
    ge _ (24 + i) (by omega), ge _ (24 + i - 8) (by omega), ge _ (24 + i - 16) (by omega)]
theorem byte1 (a b c d : UInt8) : (beWord a b c d >>> 16).toUInt8 = b := by
  apply UInt8.eq_of_toBitVec_eq
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have ge : ∀ (x : BitVec 8) (j : Nat), 8 ≤ j → x.getLsbD j = false :=
    fun x j h => BitVec.getLsbD_of_ge x j h
  simp [beWord, hi, show i < 32 by omega, show 16 + i < 32 by omega, show 16 + i < 24 by omega,
    ge _ (16 + i) (by omega), ge _ (16 + i - 8) (by omega)]
theorem byte2 (a b c d : UInt8) : (beWord a b c d >>> 8).toUInt8 = c := by
  apply UInt8.eq_of_toBitVec_eq
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have ge : ∀ (x : BitVec 8) (j : Nat), 8 ≤ j → x.getLsbD j = false :=
    fun x j h => BitVec.getLsbD_of_ge x j h
  simp [beWord, hi, show i < 32 by omega, show 8 + i < 32 by omega, show 8 + i < 24 by omega,
    show 8 + i < 16 by omega]
theorem byte3 (a b c d : UInt8) : (beWord a b c d).toUInt8 = d := by
  apply UInt8.eq_of_toBitVec_eq
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [beWord, hi]
theorem ba_get (m : ByteArray) (i : Nat) : m[i]! = m.data.toList.getD i 0 := by
  by_cases h : i < m.size <;> simp [h] <;> rfl

/-! ## State encoding and the lift of a table -/

/-- Serialise a state array (reading `a[0]! … a[7]!`) to 32 bytes; this is `stateBytes32`. -/
def encSt (a : Array UInt32) : St :=
  Vector.ofFn fun i : Fin 32 => (u32be a[i.val / 4]!)[i.val % 4]!
/-- Read 32 bytes as the 8-word state array. -/
def decSt (s : St) : Array UInt32 :=
  #[beWord s[0] s[1] s[2] s[3], beWord s[4] s[5] s[6] s[7],
    beWord s[8] s[9] s[10] s[11], beWord s[12] s[13] s[14] s[15],
    beWord s[16] s[17] s[18] s[19], beWord s[20] s[21] s[22] s[23],
    beWord s[24] s[25] s[26] s[27], beWord s[28] s[29] s[30] s[31]]
/-- The 64-byte block of `m` at offset `base` (reading `m[base + j]!`). -/
def blkAt (m : ByteArray) (base : Nat) : Blk := Vector.ofFn fun j : Fin 64 => m[base + j.val]!
/-- A table as a compression function of VCVio's shape. -/
def liftC (g : CF St Blk) : CompressFn := fun st m base => decSt (g (encSt st, blkAt m base))
/-- The real SHA-256 compression function as a table. -/
def realCF : CF St Blk := fun q => encSt (compress (decSt q.1) (bytesToByteArray q.2) 0)

theorem stateBytes32_eq (a : Array UInt32) : stateBytes32 a = bytesToByteArray (encSt a) := by
  simp [stateBytes32, encSt, bytesToByteArray]

theorem u32be_get0 (x : UInt32) : (u32be x)[0]! = (x >>> 24).toUInt8 := rfl
theorem u32be_get1 (x : UInt32) : (u32be x)[1]! = (x >>> 16).toUInt8 := rfl
theorem u32be_get2 (x : UInt32) : (u32be x)[2]! = (x >>> 8).toUInt8 := rfl
theorem u32be_get3 (x : UInt32) : (u32be x)[3]! = x.toUInt8 := rfl

theorem decSt_encSt (a : Array UInt32) :
    decSt (encSt a) = #[a[0]!, a[1]!, a[2]!, a[3]!, a[4]!, a[5]!, a[6]!, a[7]!] := by
  simp only [decSt, encSt, Vector.getElem_ofFn]
  simp [u32be_get0, u32be_get1, u32be_get2, u32be_get3, beWord_bytes]

theorem encSt_decSt (s : St) : encSt (decSt s) = s := by
  apply Vector.ext
  intro i hi
  simp only [encSt, Vector.getElem_ofFn]
  interval_cases i <;>
    simp [decSt, u32be_get0, u32be_get1, u32be_get2, u32be_get3, byte0, byte1, byte2, byte3]

theorem compress_size (st : Array UInt32) (m : ByteArray) (b : Nat) :
    (compress st m b).size = 8 := by
  simp [compress, feedForward256]

theorem lit8 (a : Array UInt32) (h : a.size = 8) :
    #[a[0]!, a[1]!, a[2]!, a[3]!, a[4]!, a[5]!, a[6]!, a[7]!] = a := by
  apply Array.ext
  · simp [h]
  · intro i h1 h2
    simp at h1
    interval_cases i <;> simp [h]

theorem compress_st (st : Array UInt32) (m : ByteArray) (b : Nat) :
    compress #[st[0]!, st[1]!, st[2]!, st[3]!, st[4]!, st[5]!, st[6]!, st[7]!] m b
      = compress st m b := by
  simp [compress, feedForward256, runRounds256]

theorem readWord_blk (m : ByteArray) (base t : Nat) (ht : t < 16) :
    readWord256 (bytesToByteArray (blkAt m base)) 0 t = readWord256 m base t := by
  have key : ∀ j, j < 64 → (bytesToByteArray (blkAt m base))[j]! = m[base + j]! := by
    intro j hj
    rw [ba_get]
    simp only [bytesToByteArray, blkAt, Vector.toArray_ofFn, Array.toList_ofFn,
      List.getD_eq_getElem?_getD, List.getElem?_ofFn, hj, dite_true, Option.getD_some]
  unfold readWord256
  simp only [Nat.zero_add]
  rw [key _ (by omega), key _ (by omega), key _ (by omega), key _ (by omega)]
  simp [Nat.add_assoc]

theorem load_congr (f g : Nat → UInt32) (l : List Nat) (h : ∀ t ∈ l, f t = g t)
    (w : Array UInt32) :
    l.foldl (fun b a => b.setIfInBounds a (f a)) w = l.foldl (fun b a => b.setIfInBounds a (g a)) w := by
  induction l generalizing w with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rw [h x (by simp), ih (fun t ht => h t (by simp [ht]))]

theorem loadSchedule_blk (m : ByteArray) (base : Nat) :
    loadSchedule256 (bytesToByteArray (blkAt m base)) 0 = loadSchedule256 m base := by
  unfold loadSchedule256
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  simp
  apply load_congr
  intro t ht
  exact readWord_blk m base t (by simp at ht; omega)

/-- **The real compression function is the lift of its table.** -/
theorem liftC_realCF : liftC realCF = compress := by
  funext st m base
  simp only [liftC, realCF, decSt_encSt]
  rw [lit8 _ (compress_size _ _ _), compress_st]
  unfold compress
  rw [loadSchedule_blk]

/-- The generic bundle at the table of the real compression function is VCVio's bundle. -/
theorem primsG_liftC_realCF : primsG (liftC realCF) = Link.prims := by
  rw [liftC_realCF]; rfl

theorem sha2PrimitivesG_liftC_realCF (p : Params) :
    sha2PrimitivesG (liftC realCF) p = sha2Primitives p := by
  rw [liftC_realCF]; rfl

/-- One step of the lifted table on a decoded state. -/
theorem liftC_decSt (g : CF St Blk) (s : St) (m : ByteArray) (base : Nat) :
    liftC g (decSt s) m base = decSt (g (s, blkAt m base)) := by
  simp only [liftC, encSt_decSt]

theorem decSt_injective : Function.Injective decSt := fun a b h => by
  rw [← encSt_decSt a, ← encSt_decSt b, h]

end Ideal

#print axioms Ideal.liftC_realCF
#print axioms Ideal.primsG_liftC_realCF
#print axioms Ideal.encSt_decSt
#print axioms Ideal.decSt_encSt
#print axioms Ideal.card_St
