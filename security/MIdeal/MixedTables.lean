import Ideal.Sha.Instantiate
import Ideal.Sha.Mixed
import MLink.Sha512

namespace Ideal

open SLHDSA SLHDSA.Concrete VCVio.Algorithms.Sha2

/-- The SHA-512 table is indexed by eight chaining words and a 128-byte block. -/
abbrev Chain512 := Vector UInt64 8
abbrev Block512 := Bytes 128

def chainAt512 (st : Array UInt64) : Chain512 := Vector.ofFn fun i => st[i.val]!
def blockAt512 (msg : ByteArray) (base : Nat) : Block512 :=
  Vector.ofFn fun i => msg[base + i.val]!

def lift512 (table : CF Chain512 Block512) : Compress512Fn :=
  fun st msg base => (table (chainAt512 st, blockAt512 msg base)).toArray

def realTable512 : CF Chain512 Block512 := fun (st, block) =>
  ⟨compress512 st.toArray (bytesToByteArray block) 0, MLink.compress512_size ..⟩

private theorem readWord_blockAt512 (msg : ByteArray) (base t : Nat) (ht : t < 16) :
    MLink.readWord512 (bytesToByteArray (blockAt512 msg base)) 0 t =
      MLink.readWord512 msg base t := by
  have get (j : Nat) (hj : j < 128) :
      (bytesToByteArray (blockAt512 msg base))[j]! = msg[base + j]! := by
    rw [ba_get]
    simp only [bytesToByteArray, blockAt512, Vector.toArray_ofFn, Array.toList_ofFn,
      List.getD_eq_getElem?_getD, List.getElem?_ofFn, hj, dite_true, Option.getD_some]
  unfold MLink.readWord512
  simp only [Nat.zero_add]
  repeat rw [get _ (by omega)]
  simp [Nat.add_assoc]

private theorem load_words_congr (ts : List Nat) (acc : Array UInt64)
    (f g : Nat → UInt64) (h : ∀ t ∈ ts, f t = g t) :
    ts.foldl (fun a t => a.setIfInBounds t (f t)) acc =
      ts.foldl (fun a t => a.setIfInBounds t (g t)) acc := by
  induction ts generalizing acc with
  | nil => rfl
  | cons t ts ih =>
    simp only [List.foldl_cons, h t (by simp)]
    exact ih _ (fun j hj => h j (by simp [hj]))

theorem lift512_real : lift512 realTable512 = compress512 := by
  funext st msg base
  change compress512 (chainAt512 st).toArray (bytesToByteArray (blockAt512 msg base)) 0 = _
  have load : MLink.loadSchedule512 (bytesToByteArray (blockAt512 msg base)) 0 =
      MLink.loadSchedule512 msg base := by
    unfold MLink.loadSchedule512
    apply load_words_congr
    intro t ht
    exact readWord_blockAt512 msg base t (by simp at ht; omega)
  simp only [MLink.compress512_unfold, load, MLink.runRounds512]
  simp [chainAt512]

/-- One shared table per compression width, used by every hash component. -/
abbrev CompressionTables := CF St Blk × CF Chain512 Block512

def tablePrimitives (tables : CompressionTables) (p : Params) : Primitives p :=
  sha2PrimitivesMixed (liftC tables.1) (lift512 tables.2) p

theorem tablePrimitives_real (p : Params) :
    tablePrimitives (realCF, realTable512) p = sha2Primitives p := by
  simp only [tablePrimitives, liftC_realCF, lift512_real, sha2PrimitivesMixed_real]

end Ideal

#print axioms Ideal.lift512_real
#print axioms Ideal.tablePrimitives_real
