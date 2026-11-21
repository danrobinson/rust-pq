import Ideal.Sha.Instantiate
import ToMathlib.Data.ByteArray
import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# Merkle–Damgård shape of SHA-256 and of the tweakable hash at SLH-DSA-SHA2-128s

For every table `g : CF St Blk`:

* `sha256G_shape`: `sha256G (liftC g) msg = digestBytes (mdFold g IV128 (padBlocks msg))`;
* `thash_shape`: the 128s tweakable hash is `out16 (keyedChain IV128 sb128 g pk (tblocks a xs))`,
  where the first block `sb128 pk = PK.seed ‖ 0^48` depends on the public seed only and the
  remaining blocks `tblocks a xs` on the tweak and message only.
-/

namespace Ideal

open SLHDSA SLHDSA.Concrete VCVio.Algorithms.Sha2

/-! ## Padding on byte lists -/

/-- The 8-byte big-endian bit length of an `n`-byte message. -/
def len8 (n : Nat) : List UInt8 := (u64be (n.toUInt64 * 8)).data.toList

@[simp] theorem len8_length (n : Nat) : (len8 n).length = 8 := rfl

/-- The SHA-256 padding suffix of an `n`-byte message: `0x80`, zeros, bit length. -/
def tailL (n : Nat) : List UInt8 :=
  0x80 :: (List.replicate ((119 - n % 64) % 64) 0 ++ len8 n)

/-- SHA-256 padding on byte lists. -/
def padL (l : List UInt8) : List UInt8 := l ++ tailL l.length

theorem tailL_length (n : Nat) : (tailL n).length = 9 + (119 - n % 64) % 64 := by
  simp [tailL]; omega

theorem padL_length (l : List UInt8) : (padL l).length = 64 * ((l.length + 8) / 64 + 1) := by
  simp [padL, tailL_length]; omega

theorem push_loop {γ} (c : UInt8) (l : List γ) (out : ByteArray) :
    (l.foldl (fun b _ => b.push c) out).data.toList
      = out.data.toList ++ List.replicate l.length c := by
  induction l generalizing out with
  | nil => simp
  | cons x xs ih => simp [ih, List.replicate_succ]

theorem pad_toList (m : ByteArray) : (pad m).data.toList = padL m.data.toList := by
  unfold pad
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  simp
  rw [push_loop]
  have : (120 - (m.size + 1) % 64) % 64 = (119 - m.size % 64) % 64 := by omega
  simp [padL, tailL, len8, this]

theorem strip_zeros (z z' : Nat) (r r' : List UInt8)
    (h : List.replicate z (0 : UInt8) ++ 0x80 :: r = List.replicate z' 0 ++ 0x80 :: r') :
    r = r' := by
  induction z generalizing z' with
  | zero =>
    cases z' with
    | zero => simpa using h
    | succ z' =>
      simp [List.replicate_succ] at h
  | succ z ih =>
    cases z' with
    | zero => simp [List.replicate_succ] at h
    | succ z' =>
      simp only [List.replicate_succ, List.cons_append, List.cons.injEq, true_and] at h
      exact ih z' h

theorem strip_tail (l l' : List UInt8) (n n' : Nat) (h : l ++ tailL n = l' ++ tailL n') :
    l = l' := by
  unfold tailL at h
  rw [← List.cons_append, ← List.append_assoc, ← List.cons_append, ← List.append_assoc] at h
  have h1 := (List.append_inj' h (by simp)).1
  have h2 := congrArg List.reverse h1
  simp only [List.reverse_append, List.reverse_cons, List.reverse_replicate,
    List.append_assoc, List.singleton_append] at h2
  have h3 := strip_zeros _ _ _ _ h2
  simpa using h3

theorem padL_injective : Function.Injective padL := fun _ _ h => strip_tail _ _ _ _ h

/-! ## Blocks -/

/-- Split a byte list into 64-byte blocks (a trailing partial block is dropped). -/
def blocksOf (l : List UInt8) : List Blk :=
  (List.range (l.length / 64)).map fun k => Vector.ofFn fun j : Fin 64 => l.getD (k * 64 + j) 0

@[simp] theorem blocksOf_length (l : List UInt8) : (blocksOf l).length = l.length / 64 := by
  simp [blocksOf]

theorem blocksOf_cons (b : Blk) (l : List UInt8) : blocksOf (b.toList ++ l) = b :: blocksOf l := by
  unfold blocksOf
  rw [show (b.toList ++ l).length / 64 = l.length / 64 + 1 by simp, List.range_succ_eq_map]
  simp only [List.map_cons, List.map_map]
  refine congrArg₂ List.cons ?_ (List.map_congr_left ?_)
  · apply Vector.ext
    intro i hi
    simp only [Vector.getElem_ofFn]
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp; omega)]
    simp [hi]
  · intro k _
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_ofFn, Function.comp, Nat.succ_mul]
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp; omega),
      List.getD_eq_getElem?_getD]
    congr 2
    simp; omega

theorem blocksOf_flat (n : Nat) (l : List UInt8) (h : l.length = 64 * n) :
    (blocksOf l).flatMap Vector.toList = l := by
  induction n generalizing l with
  | zero =>
    have : l = [] := List.eq_nil_of_length_eq_zero (by simpa using h)
    subst this; rfl
  | succ n ih =>
    let b : Blk := ⟨(l.take 64).toArray, by simp; omega⟩
    have hl : l = b.toList ++ l.drop 64 := by simp [b]
    rw [hl, blocksOf_cons, List.flatMap_cons, ih _ (by simp; omega)]

theorem blocksOf_injective (l l' : List UInt8) (h : l.length % 64 = 0) (h' : l'.length % 64 = 0)
    (e : blocksOf l = blocksOf l') : l = l' := by
  rw [← blocksOf_flat (l.length / 64) l (by omega), ← blocksOf_flat (l'.length / 64) l' (by omega),
    e]

/-- The padded message, as a list of 64-byte blocks. -/
def padBlocks (msg : ByteArray) : List Blk := blocksOf (padL msg.data.toList)

theorem padBlocks_length (msg : ByteArray) : (padBlocks msg).length = (msg.size + 8) / 64 + 1 := by
  simp [padBlocks, padL_length]

theorem padBlocks_injective : Function.Injective padBlocks := by
  intro a b h
  have h1 := blocksOf_injective _ _ (by rw [padL_length]; omega) (by rw [padL_length]; omega) h
  have h2 := padL_injective h1
  cases a; cases b
  simp at h2
  simp [h2]

/-! ## The digest shape -/

/-- The SHA-256 initial chaining value. -/
def IV128 : St := encSt iv

theorem iv_eq : iv = decSt IV128 := by
  rw [IV128, decSt_encSt]; rfl

/-- The digest as a byte array. -/
abbrev digestBytes (s : St) : ByteArray := bytesToByteArray s

theorem fold_liftC (g : CF St Blk) (p : ByteArray) (l : List Nat) (s : St) :
    l.foldl (fun b a => liftC g b p (a * 64)) (decSt s)
      = decSt (mdFold g s (l.map fun k => blkAt p (k * 64))) := by
  induction l generalizing s with
  | nil => rfl
  | cons x xs ih => simp only [List.foldl_cons, List.map_cons, liftC_decSt, ih]; rfl

theorem blkAt_eq (p : ByteArray) (k : Nat) :
    blkAt p (k * 64) = Vector.ofFn fun j : Fin 64 => p.data.toList.getD (k * 64 + j) 0 := by
  simp only [blkAt, ba_get]

theorem extract32 (s : St) : (bytesToByteArray s).extract 0 32 = bytesToByteArray s := by
  have := @ByteArray.extract_zero_size (bytesToByteArray s)
  rwa [show (bytesToByteArray s).size = 32 by simp [bytesToByteArray, ByteArray.size]] at this

/-- **Merkle–Damgård shape of SHA-256 over a table.** -/
theorem sha256G_shape (g : CF St Blk) (msg : ByteArray) :
    sha256G (liftC g) msg = digestBytes (mdFold g IV128 (padBlocks msg)) := by
  unfold sha256G sha256FamilyG
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  simp
  rw [iv_eq, fold_liftC, stateBytes32_eq, encSt_decSt, extract32]
  refine congrArg (fun l => bytesToByteArray (mdFold g IV128 l)) ?_
  unfold padBlocks blocksOf
  rw [← pad_toList, List.range_eq_range']
  simp only [blkAt_eq]
  rw [show (pad msg).size = (pad msg).data.toList.length by
    rw [Array.length_toList]; rfl]

/-! ## The tweakable hash at SLH-DSA-SHA2-128s -/

/-- Concatenation of 16-byte nodes as a byte list. -/
def flat (xs : List (Bytes 16)) : List UInt8 := xs.flatMap Vector.toList

@[simp] theorem flat_nil : flat [] = [] := rfl
@[simp] theorem flat_cons (x : Bytes 16) (xs : List (Bytes 16)) :
    flat (x :: xs) = x.toList ++ flat xs := rfl

@[simp] theorem flat_length (xs : List (Bytes 16)) : (flat xs).length = 16 * xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]; omega

theorem flat_injective : Function.Injective flat := by
  intro xs
  induction xs with
  | nil =>
    intro xs' h
    have := congrArg List.length h
    simp at this
    exact this.symm
  | cons x xs ih =>
    intro xs' h
    cases xs' with
    | nil => have := congrArg List.length h; simp at this
    | cons x' xs' =>
      simp only [flat_cons] at h
      obtain ⟨h1, h2⟩ := List.append_inj h (by simp)
      rw [Vector.toList_inj.mp h1, ih h2]

theorem concat_toList (xs : List (Bytes 16)) : (concatBytes xs).data.toList = flat xs := by
  unfold concatBytes
  suffices h : ∀ acc : ByteArray,
      (xs.foldl (fun out value => out ++ bytesToByteArray value) acc).data.toList
        = acc.data.toList ++ flat xs by
    simpa using h ByteArray.empty
  induction xs with
  | nil => intro acc; simp
  | cons y ys ih =>
    intro acc
    simp only [List.foldl_cons, ih, flat_cons]
    simp [bytesToByteArray, Vector.toList]

/-- The seed block `PK.seed ‖ 0^48`. -/
def sb128 (pk : Bytes 16) : Blk :=
  ⟨(pk.toList ++ List.replicate 48 0).toArray, by
    rw [List.size_toArray, List.length_append, Vector.length_toList, List.length_replicate]⟩

theorem sb128_toList (pk : Bytes 16) : (sb128 pk).toList = pk.toList ++ List.replicate 48 0 := rfl

theorem sb128_injective : Function.Injective sb128 := by
  intro a b h
  have := congrArg Vector.toList h
  rw [sb128_toList, sb128_toList] at this
  exact Vector.toList_inj.mp (List.append_inj this (by simp)).1

/-- The bytes of `pad(PK.seed ‖ 0^48 ‖ ADRSc ‖ concat xs)` after the seed block. -/
def tbytes (a : Bytes 22) (xs : List (Bytes 16)) : List UInt8 :=
  a.toList ++ flat xs ++ tailL (86 + 16 * xs.length)

theorem tbytes_length (a : Bytes 22) (xs : List (Bytes 16)) :
    (tbytes a xs).length = 64 * ((30 + 16 * xs.length) / 64 + 1) := by
  simp [tbytes, tailL_length]; omega

/-- The 64-byte blocks, after the seed block, of `pad(PK.seed ‖ 0^48 ‖ ADRSc ‖ concat xs)`:
the first one and the list of the remaining ones.  They do not depend on `PK.seed`. -/
def tblocks (a : Bytes 22) (xs : List (Bytes 16)) : Blk × List Blk :=
  ((blocksOf (tbytes a xs)).headD (Vector.replicate 64 0), (blocksOf (tbytes a xs)).tail)

theorem blocksOf_tbytes (a : Bytes 22) (xs : List (Bytes 16)) :
    blocksOf (tbytes a xs) = (tblocks a xs).1 :: (tblocks a xs).2 := by
  have hl : (blocksOf (tbytes a xs)).length = (30 + 16 * xs.length) / 64 + 1 := by
    rw [blocksOf_length, tbytes_length]; omega
  unfold tblocks
  cases h : blocksOf (tbytes a xs) with
  | nil => rw [h] at hl; simp at hl
  | cons b bs => rfl

/-- Exact number of continuation blocks. -/
theorem tblocks_snd_length (a : Bytes 22) (xs : List (Bytes 16)) :
    (tblocks a xs).2.length = (22 + 16 * xs.length + 8) / 64 := by
  have hl : (blocksOf (tbytes a xs)).length = (30 + 16 * xs.length) / 64 + 1 := by
    rw [blocksOf_length, tbytes_length]; omega
  rw [blocksOf_tbytes] at hl
  simp at hl
  omega

theorem tblocks_snd_length_le (a : Bytes 22) (xs : List (Bytes 16)) :
    (tblocks a xs).2.length ≤ (xs.length + 2) / 4 := by
  rw [tblocks_snd_length]; omega

theorem tblocks_snd_of_length_one (a : Bytes 22) (xs : List (Bytes 16)) (h : xs.length = 1) :
    (tblocks a xs).2 = [] :=
  List.eq_nil_of_length_eq_zero (by rw [tblocks_snd_length, h])

theorem tblocks_snd_of_length_two (a : Bytes 22) (xs : List (Bytes 16)) (h : xs.length = 2) :
    (tblocks a xs).2 = [] :=
  List.eq_nil_of_length_eq_zero (by rw [tblocks_snd_length, h])

theorem tblocks_injective {a a' : Bytes 22} {xs xs' : List (Bytes 16)}
    (h : tblocks a xs = tblocks a' xs') : a = a' ∧ xs = xs' := by
  have hb : blocksOf (tbytes a xs) = blocksOf (tbytes a' xs') := by
    rw [blocksOf_tbytes, blocksOf_tbytes, h]
  have ht := blocksOf_injective _ _ (by rw [tbytes_length]; omega) (by rw [tbytes_length]; omega) hb
  have h1 := strip_tail _ _ _ _ ht
  obtain ⟨h2, h3⟩ := List.append_inj h1 (by simp)
  exact ⟨Vector.toList_inj.mp h2, flat_injective h3⟩

/-- First 16 bytes of the chaining value (the truncated digest). -/
def out16 (s : St) : Bytes 16 := Vector.ofFn fun i : Fin 16 => s[i.val]

/-- First 22 bytes of a block (where the tweak sits in the first block of `tblocks`). -/
def btw128 (B : Blk) : Bytes 22 := Vector.ofFn fun i : Fin 22 => B[i.val]

theorem btw128_tblocks (a : Bytes 22) (xs : List (Bytes 16)) : btw128 (tblocks a xs).1 = a := by
  have h := blocksOf_tbytes a xs
  have h2 : (tblocks a xs).1 = Vector.ofFn fun j : Fin 64 => (tbytes a xs).getD (0 * 64 + j) 0 := by
    have hl := tbytes_length a xs
    unfold blocksOf at h
    rw [hl, show 64 * ((30 + 16 * xs.length) / 64 + 1) / 64 = (30 + 16 * xs.length) / 64 + 1 by omega,
      List.range_succ_eq_map] at h
    simp only [List.map_cons] at h
    exact (List.cons.inj h).1.symm
  rw [h2]
  apply Vector.ext
  intro i hi
  simp only [btw128, Vector.getElem_ofFn, tbytes, List.append_assoc]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp; omega)]
  simp [hi]

theorem prefix_out16 (s : St) : byteArrayPrefixOrZero (bytesToByteArray s) 16 = out16 s := by
  have hraw : ((bytesToByteArray s).extract 0 16).toList = s.toList.take 16 := by
    rw [ByteArray.toList_eq_toList_data, ByteArray.data_extract, Array.toList_extract]
    simp [bytesToByteArray, Vector.toList]
  have hl : ((bytesToByteArray s).extract 0 16).toList.length = 16 := by
    rw [hraw]; simp
  simp only [byteArrayPrefixOrZero, byteArrayPrefixChecked, decodeExact, hl, dite_true]
  apply Vector.ext
  intro i hi
  simp [out16, hraw]

/-- **Merkle–Damgård shape of the tweakable hash at SLH-DSA-SHA2-128s**: a keyed chain whose
first block is the seed block and whose remaining blocks depend on tweak and message only. -/
theorem thash_shape (g : CF St Blk) (pk : Bytes 16) (a : Bytes 22) (xs : List (Bytes 16)) :
    sha2ThashG (liftC g) Link.vp.params pk a xs
      = out16 (keyedChain IV128 sb128 g pk (tblocks a xs)) := by
  have hp : padBlocks (sha2Prefix256Key pk a ++ concatBytes xs)
      = sb128 pk :: (tblocks a xs).1 :: (tblocks a xs).2 := by
    unfold padBlocks
    have e : (sha2Prefix256Key pk a ++ concatBytes xs).data.toList
        = (sb128 pk).toList ++ (a.toList ++ flat xs) := by
      simp only [sha2Prefix256Key, bytesToByteArray, zeroByteArray, ByteArray.data_append,
        Array.toList_append, concat_toList, sb128_toList, List.append_assoc,
        Array.toList_replicate]
      rfl
    have e2 : padL ((sb128 pk).toList ++ (a.toList ++ flat xs))
        = (sb128 pk).toList ++ tbytes a xs := by
      simp only [padL, tbytes, sb128_toList, List.append_assoc, List.length_append,
        Vector.length_toList, List.length_replicate, flat_length]
      rw [show 16 + (48 + (22 + 16 * xs.length)) = 86 + 16 * xs.length by omega]
    rw [e, e2, blocksOf_cons, blocksOf_tbytes]
  rw [sha2ThashG_128, sha256G_shape, hp, prefix_out16]
  rfl

/-- `thash_shape` for the `Thash` field of the 128s bundle. -/
theorem primsG_Thash_shape (g : CF St Blk) (pk : Bytes 16) (a : Bytes 22) (xs : List (Bytes 16)) :
    (primsG (liftC g)).Thash pk a xs = out16 (keyedChain IV128 sb128 g pk (tblocks a xs)) :=
  thash_shape g pk a xs

/-! ## `out16` of a uniform chaining value is uniform -/

/-- Last 16 bytes of the chaining value. -/
def lo16 (s : St) : Bytes 16 := Vector.ofFn fun i : Fin 16 => s[i.val + 16]

theorem split_bijective : Function.Bijective fun s : St => (out16 s, lo16 s) := by
  constructor
  · intro s t h
    simp only [Prod.mk.injEq] at h
    apply Vector.ext
    intro i hi
    by_cases h16 : i < 16
    · have := congrArg (fun v : Bytes 16 => v[i]) h.1
      simpa [out16] using this
    · have := congrArg (fun v : Bytes 16 => v[i - 16]'(by omega)) h.2
      simp only [lo16, Vector.getElem_ofFn] at this
      simpa [show i - 16 + 16 = i by omega] using this
  · rintro ⟨a, b⟩
    refine ⟨Vector.ofFn fun i : Fin 32 => if h : i.val < 16 then a[i.val] else b[i.val - 16], ?_⟩
    simp only [Prod.mk.injEq]
    constructor
    · apply Vector.ext; intro i hi; simp [out16]
    · apply Vector.ext; intro i hi; simp [lo16]

open OracleComp in
/-- Events of `out16` of a uniform chaining value are events of a uniform 16-byte string. -/
theorem prEvent_out16 (p : Bytes 16 → Prop) :
    Pr{let u ← $ᵗ St}[p (out16 u)] = Pr{let y ← $ᵗ (Bytes 16)}[p y] :=
  (SampleableType.prEvent_uniformSample_comp_of_bijective split_bijective (fun z => p z.1)).trans
    (SampleableType.prEvent_uniformSample_fst p)

open OracleComp in
/-- `out16` is balanced. -/
theorem prEvent_out16_eq (y : Bytes 16) :
    Pr{let u ← $ᵗ St}[out16 u = y] = ((2 : ENNReal) ^ 128)⁻¹ := by
  rw [prEvent_out16 (· = y), SampleableType.prEvent_uniformSample_eq_singleton, card_bytes]
  norm_num

open OracleComp in
/-- `out16 <$> $ᵗ St` is uniform on `Bytes 16`. -/
theorem out16_uniform :
    (out16 <$> ($ᵗ St : ProbComp St)) =ᵈ ($ᵗ (Bytes 16) : ProbComp (Bytes 16)) := by
  apply OracleComp.evalDistEq_of_forall_prEvent_eq_output
  intro y
  rw [prEvent_map]
  exact prEvent_out16 (· = y)

open OracleComp in
/-- `out16 <$> $ᵗ St` is uniform on `Bytes 16`, as an equality of output measures. -/
theorem evalDist_out16 :
    letI : MeasurableSpace (Bytes 16) := ⊤
    𝒟[out16 <$> ($ᵗ St : ProbComp St)] = 𝒟[($ᵗ (Bytes 16) : ProbComp (Bytes 16))] :=
  evalDistEq_iff_evalDist_eq.mp out16_uniform

end Ideal

#print axioms Ideal.sha256G_shape
#print axioms Ideal.padBlocks_injective
#print axioms Ideal.padBlocks_length
#print axioms Ideal.thash_shape
#print axioms Ideal.primsG_Thash_shape
#print axioms Ideal.sb128_injective
#print axioms Ideal.btw128_tblocks
#print axioms Ideal.tblocks_injective
#print axioms Ideal.tblocks_snd_length
#print axioms Ideal.tblocks_snd_of_length_one
#print axioms Ideal.tblocks_snd_of_length_two
#print axioms Ideal.prEvent_out16_eq
#print axioms Ideal.out16_uniform
#print axioms Ideal.evalDist_out16
