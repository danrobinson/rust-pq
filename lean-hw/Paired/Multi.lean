import Paired.Proof

/-!
# ARM64 SHA-512 `paired.rs` multi-block compression, NEON stores, and parent callers

This module extends `Paired.Proof` (which proves `lane_step`, `load_block`,
`paired_step`, and `compress_parents` against `Spec.SHA512.compress`) to cover
the surrounding operations and callers in `rust/src/sha512/paired.rs`:

1. **NEON big-endian truncation store (`store_trunc`)**:
   `vrev64q_u8` on `ab` and `cd` followed by `vst1q_u8` (+ `vst1_u8(vget_low_u8)`
   for `N = 24` or `vst1q_u8` for `N = 32`) produces exact FIPS 180-4 big-endian
   bytes `(st.flatMap (fun w => Spec.toByte w.toNat 8)).take N`.
2. **Block loader + 80-round kernel + feed-forward (`load_block` + `rounds_lanes`
   + `add_store_state`)**:
   One block step equals `Spec.SHA512.compress`.
3. **Multi-block compression (`compress_multi_1`, `compress_multi_2`,
   `compress_multi_4`)**:
   Iterated block compression from any 8-word state across any positive multiple
   of 128 bytes followed by `store_trunc` equals iterated `Spec.SHA512.compress`
   followed by big-endian truncation to `N ∈ {24, 32}` bytes, and equals FIPS 205
   `Spec.T` / `Spec.H` when continuing from the precomputed `PK.seed` state on a
   SHA-512-padded suffix.
4. **Parent-hashing callers (`parents_batch` and `path_parents_batch`)**:
   Both the 4-way main loop (`compress_parents_4_active`) and the 2-way tail
   (`compress_parents`), including in-place overwrite safety for `parents_batch`
   and left/right sibling selection + `idx >>= 1` for `path_parents_batch`,
   compute exact FIPS 205 `Spec.H` (and one level of `Spec.climb`) for `N ∈ {24, 32}`.
-/

namespace slhdsa.H512.Multi
open Spec.SHA512
open slhdsa.H512

/-! ## 1. NEON `vrev64q_u8` big-endian serialization (`store_trunc`) -/

/-- The 8 big-endian bytes of a 64-bit word (`vrev64q_u8` on one 64-bit lane). -/
def beBytes64 (w : Word) : Spec.Bytes :=
  [w.extractLsb' 56 8, w.extractLsb' 48 8, w.extractLsb' 40 8, w.extractLsb' 32 8,
   w.extractLsb' 24 8, w.extractLsb' 16 8, w.extractLsb' 8 8, w.extractLsb' 0 8]

theorem beBytes64_length (w : Word) : (beBytes64 w).length = 8 := rfl

/-- `beBytes64 w` equals FIPS 180-4 `Spec.toByte w.toNat 8`. -/
theorem beBytes64_eq_toByte (w : Word) : beBytes64 w = Spec.toByte w.toNat 8 := by
  have hbyte : ∀ k, w.extractLsb' (8 * k) 8 = BitVec.ofNat 8 (w.toNat >>> (8 * k)) := by
    intro k
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.extractLsb']
  have hr8 : List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] := rfl
  simp only [beBytes64, Spec.toByte, hr8, List.map_cons, List.map_nil]
  change [w.extractLsb' (8 * 7) 8, w.extractLsb' (8 * 6) 8, w.extractLsb' (8 * 5) 8,
    w.extractLsb' (8 * 4) 8, w.extractLsb' (8 * 3) 8, w.extractLsb' (8 * 2) 8,
    w.extractLsb' (8 * 1) 8, w.extractLsb' (8 * 0) 8] = _
  rw [hbyte 7, hbyte 6, hbyte 5, hbyte 4, hbyte 3, hbyte 2, hbyte 1, hbyte 0]

/-- `store_trunc::<N>(ab, cd)`: writes `vrev64q_u8(ab)` (16 bytes), followed by
the low 8 bytes of `vrev64q_u8(cd)` when `N = 24` or all 16 bytes when `N = 32`. -/
def storeTrunc (N : Nat) (ab cd : Arm.V2) : Spec.Bytes :=
  let abBe := beBytes64 ab.e0 ++ beBytes64 ab.e1
  let cdBe := beBytes64 cd.e0 ++ beBytes64 cd.e1
  if N = 24 then abBe ++ cdBe.take 8 else abBe ++ cdBe

/-- `store_trunc::<N>` on the first two state vectors `(vOf2 st 0, vOf2 st 2)`
equals FIPS 180-4 big-endian serialization of `st` truncated to `N ∈ {24, 32}` bytes. -/
theorem storeTrunc_eq_fips (N : Nat) (hN : N = 24 ∨ N = 32)
    (st : List Word) (hst : st.length = 8) :
    storeTrunc N (vOf2 st 0) (vOf2 st 2) =
      (st.flatMap fun w => Spec.toByte w.toNat 8).take N := by
  rcases st with _ | ⟨w0, _ | ⟨w1, _ | ⟨w2, _ | ⟨w3, ws⟩⟩⟩⟩ <;> simp at hst
  have hlen : ∀ w : Word, (Spec.toByte w.toNat 8).length = 8 := fun _ => by simp [Spec.toByte]
  set a := Spec.toByte w0.toNat 8
  set b := Spec.toByte w1.toNat 8
  set c := Spec.toByte w2.toNat 8
  set d := Spec.toByte w3.toNat 8
  rcases hN with rfl | rfl
  · simp only [storeTrunc, vOf2, ↓reduceIte, beBytes64_eq_toByte, List.flatMap_cons,
      List.getElem!_cons_zero, List.getElem!_cons_succ]
    change (a ++ b) ++ (c ++ d).take 8 = (a ++ (b ++ (c ++ (d ++ ws.flatMap fun w => Spec.toByte w.toNat 8)))).take 24
    have habc : (a ++ b ++ c).length = 24 := by simp [a, b, c, hlen]
    have hc : c.length = 8 := hlen w2
    rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega),
      show a ++ (b ++ (c ++ (d ++ ws.flatMap fun w => Spec.toByte w.toNat 8))) =
        (a ++ b ++ c) ++ (d ++ ws.flatMap fun w => Spec.toByte w.toNat 8) by simp [List.append_assoc],
      List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
  · simp only [storeTrunc, vOf2, show (32 : Nat) ≠ 24 by decide, ↓reduceIte, beBytes64_eq_toByte,
      List.flatMap_cons, List.getElem!_cons_zero, List.getElem!_cons_succ]
    change (a ++ b) ++ (c ++ d) = (a ++ (b ++ (c ++ (d ++ ws.flatMap fun w => Spec.toByte w.toNat 8)))).take 32
    have habcd : (a ++ b ++ c ++ d).length = 32 := by simp [a, b, c, d, hlen]
    rw [show a ++ (b ++ (c ++ (d ++ ws.flatMap fun w => Spec.toByte w.toNat 8))) =
        (a ++ b ++ c ++ d) ++ (ws.flatMap fun w => Spec.toByte w.toNat 8) by simp [List.append_assoc],
      List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
    simp [List.append_assoc]

private theorem toLEBytes_eq_range : ∀ (n : Nat) (x : BitVec (8 * n)),
    x.toLEBytes = (List.range n).map fun i => BitVec.ofNat 8 (x.toNat >>> (8 * i))
  | 0, x => by
    rw [BitVec.toLEBytes]
    simp only [Nat.mul_zero, Nat.lt_irrefl, ↓reduceIte, List.range_zero, List.map_nil]
  | n + 1, x => by
    rw [BitVec.toLEBytes]
    simp only [show 8 * (n + 1) > 0 by omega, ↓reduceIte]
    have hshr_lt : x.toNat >>> 8 < 2 ^ (8 * n) := by
      have hx := x.isLt
      rw [Nat.shiftRight_eq_div_pow]
      have : 2 ^ (8 * (n + 1)) = 2 ^ (8 * n) * 2 ^ 8 := by rw [← Nat.pow_add]; congr 1
      omega
    have hrec : BitVec.toLEBytes ((x >>> 8).setWidth (8 * (n + 1) - 8)) =
        (List.range n).map fun i => BitVec.ofNat 8 ((x.toNat >>> 8) >>> (8 * i)) := by
      have hw : 8 * (n + 1) - 8 = 8 * n := by omega
      have hcast : BitVec.toLEBytes ((x >>> 8).setWidth (8 * (n + 1) - 8)) =
          BitVec.toLEBytes ((x >>> 8).setWidth (8 * n)) := by
        cases hw; rfl
      rw [hcast, toLEBytes_eq_range n ((x >>> 8).setWidth (8 * n))]
      apply List.map_congr_left
      intro i _
      have : ((x >>> 8).setWidth (8 * n)).toNat = x.toNat >>> 8 := by
        simp [BitVec.toNat_ushiftRight, Nat.mod_eq_of_lt hshr_lt]
      rw [this]
    rw [hrec]
    have h0 : x.setWidth 8 = BitVec.ofNat 8 (x.toNat >>> (8 * 0)) := by
      apply BitVec.eq_of_toNat_eq; simp
    rw [h0, List.range_succ_eq_map, List.map_cons, List.map_map]
    congr 1
    apply List.map_congr_left
    intro i _
    simp only [Function.comp_def]
    congr 1
    rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow,
      Nat.div_div_eq_div_mul, ← Nat.pow_add]
    congr 2; omega

private theorem toBEBytes_eq_toByte64 (w : Word) : w.toBEBytes = Spec.toByte w.toNat 8 := by
  rw [BitVec.toBEBytes, toLEBytes_eq_range 8 w, ← List.map_reverse]
  apply List.ext_getElem
  · simp [Spec.toByte]
  · intro i hi1 hi2
    simp only [List.getElem_map, List.getElem_reverse, List.getElem_range, Spec.toByte,
      List.length_range]

/-- Bridge to `Paired.encode` in `Paired/Proof.lean`: the byte representation
of `Paired.encode ws` equals `ws.flatMap (fun w => Spec.toByte w.toNat 8)`. -/
theorem paired_encode_eq_toByte (ws : List Word) :
    (Paired.encode ws).map (·.bv) = ws.flatMap fun w => Spec.toByte w.toNat 8 := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp only [Paired.encode, List.flatMap_cons, List.map_append]
    rw [show List.map (fun x => x.bv) (List.flatMap (fun w => List.map (fun b => (⟨b⟩ : Aeneas.Std.U8)) w.toBEBytes) ws) =
        (Paired.encode ws).map (·.bv) from rfl, ih]
    congr 1
    have hbe : (w.toBEBytes.map (fun b => (⟨b⟩ : Aeneas.Std.U8))).map (·.bv) = w.toBEBytes := by
      rw [List.map_map]
      exact List.map_id' _
    rw [hbe, toBEBytes_eq_toByte64]

/-! ## 2. Single-block hardware compression with feed-forward (`add_store_state`) -/

private theorem add2_comm (a b : Arm.V2) : Arm.ADD2 a b = Arm.ADD2 b a := by
  cases a; cases b; simp [Arm.ADD2, BitVec.add_comm]

/-- Model of one block of `compress_block_lanes_in_place` / `compress_multi_1_active`:
load state as 4 `V2` vectors, load block via `blockVs` (`load_block`), run 40
`kstep`s (`rounds_lanes`), and accumulate feed-forward via `Arm.ADD2` (`add_store_state`). -/
def compressBlockHw (st : List Word) (B : Spec.Bytes) : List Word :=
  let v0 := vOf2 st 0
  let v1 := vOf2 st 2
  let v2 := vOf2 st 4
  let v3 := vOf2 st 6
  let res := kcompress v0 v1 v2 v3 (blockVs B)
  vwords2 (Arm.ADD2 v0 res.ab) ++ vwords2 (Arm.ADD2 v1 res.cd) ++
    (vwords2 (Arm.ADD2 v2 res.ef) ++ vwords2 (Arm.ADD2 v3 res.gh))

theorem compressBlockHw_length (st : List Word) (B : Spec.Bytes) :
    (compressBlockHw st B).length = 8 := by
  unfold compressBlockHw
  dsimp only
  generalize kcompress (vOf2 st 0) (vOf2 st 2) (vOf2 st 4) (vOf2 st 6) (blockVs B) = res
  simp only [vwords2, List.length_append, List.length_cons, List.length_nil]

/-- One hardware block (`load_block` + 40 `lane_step`s + `add_store_state`)
equals FIPS 180-4 `Spec.SHA512.compress`. -/
theorem compressBlockHw_eq_fips (st : List Word) (B : Spec.Bytes) :
    compressBlockHw st B = Spec.SHA512.compress st B := by
  unfold compressBlockHw
  dsimp only
  rw [add2_comm (vOf2 st 0), add2_comm (vOf2 st 2), add2_comm (vOf2 st 4), add2_comm (vOf2 st 6)]
  exact kcompress_eq st B

/-- Single-block parent compression (`compress_parents` / `compress_parents_4_active`):
loads initial state, runs 40 steps on `blockVs B`, adds `initial[0..2]` to
`state[0..2]`, and serializes via `storeTrunc N`. -/
def compressParentHw (N : Nat) (st : List Word) (B : Spec.Bytes) : Spec.Bytes :=
  let v0 := vOf2 st 0
  let v1 := vOf2 st 2
  let v2 := vOf2 st 4
  let v3 := vOf2 st 6
  let res := kcompress v0 v1 v2 v3 (blockVs B)
  storeTrunc N (Arm.ADD2 v0 res.ab) (Arm.ADD2 v1 res.cd)

private theorem compress512_length (st : List Word) (B : Spec.Bytes) :
    (Spec.SHA512.compress st B).length = 8 := by
  rw [← compressBlockHw_eq_fips]
  exact compressBlockHw_length st B

theorem compressParentHw_eq_fips (N : Nat) (hN : N = 24 ∨ N = 32)
    (st : List Word) (B : Spec.Bytes) :
    compressParentHw N st B =
      ((Spec.SHA512.compress st B).flatMap fun w => Spec.toByte w.toNat 8).take N := by
  have hcomp := compressBlockHw_eq_fips st B
  have hlen : (Spec.SHA512.compress st B).length = 8 := compress512_length st B
  rw [← storeTrunc_eq_fips N hN (Spec.SHA512.compress st B) hlen, ← hcomp]
  unfold compressParentHw compressBlockHw
  dsimp only
  generalize kcompress (vOf2 st 0) (vOf2 st 2) (vOf2 st 4) (vOf2 st 6) (blockVs B) = res
  simp only [vOf2, vwords2, List.cons_append, List.nil_append, List.getElem!_cons_zero,
    List.getElem!_cons_succ]

/-! ## 3. Multi-block compression (`compress_multi_1`, `compress_multi_2`, `compress_multi_4`) -/

/-- Reference iterated FIPS 180-4 SHA-512 block compression over `msg`. -/
def iterCompress (st : List Word) (msg : Spec.Bytes) : List Word :=
  (List.range (msg.length / 128)).foldl (fun acc k => Spec.SHA512.compress acc (blockAt msg k)) st

private theorem iterCompress_length (st : List Word) (hst : st.length = 8) (msg : Spec.Bytes) :
    (iterCompress st msg).length = 8 := by
  unfold iterCompress
  generalize msg.length / 128 = n
  induction n with
  | zero => exact hst
  | succ n ih =>
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    exact compress512_length _ _

/-- Hardware 1-lane multi-block compression (`compress_multi_1_active`). -/
def compressMulti1 (N : Nat) (st : List Word) (msg : Spec.Bytes) : Spec.Bytes :=
  let acc := (List.range (msg.length / 128)).foldl
    (fun acc k => compressBlockHw acc (blockAt msg k)) st
  storeTrunc N (vOf2 acc 0) (vOf2 acc 2)

/-- Hardware 2-lane lockstep multi-block compression (`compress_multi_2` /
`compress_multi_lanes::<2, N, L>`). -/
def compressMulti2 (N : Nat) (st : List Word) (m0 m1 : Spec.Bytes) (blocks : Nat) :
    Spec.Bytes × Spec.Bytes :=
  let (a0, a1) := (List.range blocks).foldl
    (fun (acc : List Word × List Word) k =>
      (compressBlockHw acc.1 (blockAt m0 k), compressBlockHw acc.2 (blockAt m1 k)))
    (st, st)
  (storeTrunc N (vOf2 a0 0) (vOf2 a0 2), storeTrunc N (vOf2 a1 0) (vOf2 a1 2))

/-- Hardware 4-lane lockstep multi-block compression (`compress_multi_4` /
`compress_multi_lanes::<4, N, L>`). -/
def compressMulti4 (N : Nat) (st : List Word) (m0 m1 m2 m3 : Spec.Bytes) (blocks : Nat) :
    Spec.Bytes × Spec.Bytes × Spec.Bytes × Spec.Bytes :=
  let (a0, a1, a2, a3) := (List.range blocks).foldl
    (fun (acc : List Word × List Word × List Word × List Word) k =>
      (compressBlockHw acc.1 (blockAt m0 k),
       compressBlockHw acc.2.1 (blockAt m1 k),
       compressBlockHw acc.2.2.1 (blockAt m2 k),
       compressBlockHw acc.2.2.2 (blockAt m3 k)))
    (st, st, st, st)
  (storeTrunc N (vOf2 a0 0) (vOf2 a0 2),
   storeTrunc N (vOf2 a1 0) (vOf2 a1 2),
   storeTrunc N (vOf2 a2 0) (vOf2 a2 2),
   storeTrunc N (vOf2 a3 0) (vOf2 a3 2))

private theorem hwFold_eq_iter (st : List Word) (msg : Spec.Bytes) (n : Nat) :
    (List.range n).foldl (fun acc k => compressBlockHw acc (blockAt msg k)) st =
      (List.range n).foldl (fun acc k => Spec.SHA512.compress acc (blockAt msg k)) st := by
  induction n with
  | zero => simp only [List.range_zero, List.foldl_nil]
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_append, ih]
    simp only [List.foldl_cons, List.foldl_nil, compressBlockHw_eq_fips]

/-- **`compress_multi_1` theorem**:
`compressMulti1 N st msg` equals iterated `Spec.SHA512.compress` followed by
big-endian truncation to `N ∈ {24, 32}` bytes. -/
theorem compress_multi_1_eq_iter (N : Nat) (hN : N = 24 ∨ N = 32)
    (st : List Word) (hst : st.length = 8) (msg : Spec.Bytes) :
    compressMulti1 N st msg =
      ((iterCompress st msg).flatMap fun w => Spec.toByte w.toNat 8).take N := by
  unfold compressMulti1
  dsimp only
  rw [hwFold_eq_iter]
  exact storeTrunc_eq_fips N hN (iterCompress st msg) (iterCompress_length st hst msg)

private theorem foldl_pair_eq (st : List Word) (m0 m1 : Spec.Bytes) (n : Nat) :
    (List.range n).foldl
      (fun (acc : List Word × List Word) k =>
        (compressBlockHw acc.1 (blockAt m0 k), compressBlockHw acc.2 (blockAt m1 k)))
      (st, st) =
      ((List.range n).foldl (fun acc k => Spec.SHA512.compress acc (blockAt m0 k)) st,
       (List.range n).foldl (fun acc k => Spec.SHA512.compress acc (blockAt m1 k)) st) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_append, List.foldl_append, ih]
    simp only [List.foldl_cons, List.foldl_nil, compressBlockHw_eq_fips]

/-- **`compress_multi_2` theorem**:
Lockstep 2-lane `compressMulti2 N st m0 m1 blocks` equals iterated
`Spec.SHA512.compress` followed by big-endian truncation to `N ∈ {24, 32}` bytes
on BOTH lanes. -/
theorem compress_multi_2_eq_iter (N : Nat) (hN : N = 24 ∨ N = 32)
    (st : List Word) (hst : st.length = 8)
    (m0 m1 : Spec.Bytes) (blocks : Nat)
    (hm0 : m0.length / 128 = blocks) (hm1 : m1.length / 128 = blocks) :
    compressMulti2 N st m0 m1 blocks =
      (((iterCompress st m0).flatMap fun w => Spec.toByte w.toNat 8).take N,
       ((iterCompress st m1).flatMap fun w => Spec.toByte w.toNat 8).take N) := by
  unfold compressMulti2
  rw [foldl_pair_eq]
  dsimp only
  have h0 : (List.range blocks).foldl (fun acc k => Spec.SHA512.compress acc (blockAt m0 k)) st = iterCompress st m0 := by
    unfold iterCompress; rw [hm0]
  have h1 : (List.range blocks).foldl (fun acc k => Spec.SHA512.compress acc (blockAt m1 k)) st = iterCompress st m1 := by
    unfold iterCompress; rw [hm1]
  rw [h0, h1]
  exact Prod.ext
    (storeTrunc_eq_fips N hN (iterCompress st m0) (iterCompress_length st hst m0))
    (storeTrunc_eq_fips N hN (iterCompress st m1) (iterCompress_length st hst m1))

private theorem foldl_quad_eq (st : List Word) (m0 m1 m2 m3 : Spec.Bytes) (n : Nat) :
    (List.range n).foldl
      (fun (acc : List Word × List Word × List Word × List Word) k =>
        (compressBlockHw acc.1 (blockAt m0 k),
         compressBlockHw acc.2.1 (blockAt m1 k),
         compressBlockHw acc.2.2.1 (blockAt m2 k),
         compressBlockHw acc.2.2.2 (blockAt m3 k)))
      (st, st, st, st) =
      ((List.range n).foldl (fun acc k => Spec.SHA512.compress acc (blockAt m0 k)) st,
       (List.range n).foldl (fun acc k => Spec.SHA512.compress acc (blockAt m1 k)) st,
       (List.range n).foldl (fun acc k => Spec.SHA512.compress acc (blockAt m2 k)) st,
       (List.range n).foldl (fun acc k => Spec.SHA512.compress acc (blockAt m3 k)) st) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_append, List.foldl_append,
      List.foldl_append, List.foldl_append, ih]
    simp only [List.foldl_cons, List.foldl_nil, compressBlockHw_eq_fips]

/-- **`compress_multi_4` theorem**:
Lockstep 4-lane `compressMulti4 N st m0 m1 m2 m3 blocks` equals iterated
`Spec.SHA512.compress` followed by big-endian truncation to `N ∈ {24, 32}` bytes
on ALL FOUR lanes. -/
theorem compress_multi_4_eq_iter (N : Nat) (hN : N = 24 ∨ N = 32)
    (st : List Word) (hst : st.length = 8)
    (m0 m1 m2 m3 : Spec.Bytes) (blocks : Nat)
    (hm0 : m0.length / 128 = blocks) (hm1 : m1.length / 128 = blocks)
    (hm2 : m2.length / 128 = blocks) (hm3 : m3.length / 128 = blocks) :
    compressMulti4 N st m0 m1 m2 m3 blocks =
      (((iterCompress st m0).flatMap fun w => Spec.toByte w.toNat 8).take N,
       ((iterCompress st m1).flatMap fun w => Spec.toByte w.toNat 8).take N,
       ((iterCompress st m2).flatMap fun w => Spec.toByte w.toNat 8).take N,
       ((iterCompress st m3).flatMap fun w => Spec.toByte w.toNat 8).take N) := by
  unfold compressMulti4
  rw [foldl_quad_eq]
  dsimp only
  have h0 : (List.range blocks).foldl (fun acc k => Spec.SHA512.compress acc (blockAt m0 k)) st = iterCompress st m0 := by
    unfold iterCompress; rw [hm0]
  have h1 : (List.range blocks).foldl (fun acc k => Spec.SHA512.compress acc (blockAt m1 k)) st = iterCompress st m1 := by
    unfold iterCompress; rw [hm1]
  have h2 : (List.range blocks).foldl (fun acc k => Spec.SHA512.compress acc (blockAt m2 k)) st = iterCompress st m2 := by
    unfold iterCompress; rw [hm2]
  have h3 : (List.range blocks).foldl (fun acc k => Spec.SHA512.compress acc (blockAt m3 k)) st = iterCompress st m3 := by
    unfold iterCompress; rw [hm3]
  rw [h0, h1, h2, h3]
  refine Prod.ext
    (storeTrunc_eq_fips N hN (iterCompress st m0) (iterCompress_length st hst m0))
    (Prod.ext
      (storeTrunc_eq_fips N hN (iterCompress st m1) (iterCompress_length st hst m1))
      (Prod.ext
        (storeTrunc_eq_fips N hN (iterCompress st m2) (iterCompress_length st hst m2))
        (storeTrunc_eq_fips N hN (iterCompress st m3) (iterCompress_length st hst m3))))

/-! ## 4. Connecting precomputed `PK.seed` state + suffix blocks to FIPS 205 `Spec.T` / `Spec.H` -/

/-- Precomputed first-block SHA-512 state `compress(H0, PK.seed ‖ 0^{128 - N})`. -/
def pkState512 (N : Nat) (pkSeed : Spec.Bytes) : List Word :=
  Spec.SHA512.compress Spec.SHA512.H0 (pkSeed ++ Spec.toByte 0 (128 - N))

private theorem blockAt_append_128 (b0 rest : Spec.Bytes) (hb0 : b0.length = 128) :
    blockAt (b0 ++ rest) 0 = b0 ∧
    ∀ k, blockAt (b0 ++ rest) (k + 1) = blockAt rest k := by
  constructor
  · simp [blockAt, hb0]
  · intro k
    have hmul : 128 * (k + 1) = 128 + 128 * k := by omega
    simp only [blockAt, hmul, List.drop_append, hb0]
    rw [List.drop_of_length_le (by omega), List.nil_append, show 128 + 128 * k - 128 = 128 * k by omega]

private theorem foldl_range_succ_zero {α : Type} (f : α → Nat → α) (x : α) (n : Nat) :
    (List.range (n + 1)).foldl f x = (List.range n).foldl (fun a k => f a (k + 1)) (f x 0) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, ih, List.range_succ, List.foldl_append]
    rfl

/-- Continuing `iterCompress` from `pkState512` over the remaining blocks of
`Spec.SHA512.pad (b0 ++ suffix)` (where `b0 = pkSeed ++ toByte 0 (128 - N)` has
length 128) computes exact `Spec.SHA512.sha512 (b0 ++ suffix)` truncated to `N`. -/
theorem compress_multi_1_eq_sha512_from_pkState (N : Nat) (hN : N = 24 ∨ N = 32)
    (pkSeed suffix : Spec.Bytes) (hpk : pkSeed.length = N) :
    let b0 := pkSeed ++ Spec.toByte 0 (128 - N)
    let paddedSuffix := (Spec.SHA512.pad (b0 ++ suffix)).drop 128
    compressMulti1 N (pkState512 N pkSeed) paddedSuffix =
      (Spec.SHA512.sha512 (b0 ++ suffix)).take N := by
  intro b0 paddedSuffix
  have hb0_len : b0.length = 128 := by simp [b0, Spec.toByte, hpk]; omega
  have hpad_eq : Spec.SHA512.pad (b0 ++ suffix) = b0 ++ paddedSuffix := by
    have hpre : (Spec.SHA512.pad (b0 ++ suffix)).take 128 = b0 := by
      unfold Spec.SHA512.pad
      simp only [List.append_assoc]
      rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
    exact (List.take_append_drop 128 (Spec.SHA512.pad (b0 ++ suffix))).symm.trans (by rw [hpre])
  have hlen_div : (Spec.SHA512.pad (b0 ++ suffix)).length / 128 = paddedSuffix.length / 128 + 1 := by
    rw [hpad_eq, List.length_append, hb0_len]
    omega
  have hst_len : (pkState512 N pkSeed).length = 8 := compress512_length _ _
  rw [compress_multi_1_eq_iter N hN (pkState512 N pkSeed) hst_len]
  unfold Spec.SHA512.sha512 iterCompress pkState512
  dsimp only
  rw [hlen_div, foldl_range_succ_zero]
  obtain ⟨hb_zero, hb_succ⟩ := blockAt_append_128 b0 paddedSuffix hb0_len
  rw [hpad_eq, hb_zero]
  have hcongr : ∀ n (init : List Word),
      (List.range n).foldl (fun acc k => Spec.SHA512.compress acc (blockAt paddedSuffix k)) init =
      (List.range n).foldl (fun acc k => Spec.SHA512.compress acc (blockAt (b0 ++ paddedSuffix) (k + 1))) init := by
    intro n
    induction n with
    | zero => intro init; simp only [List.range_zero, List.foldl_nil]
    | succ n ih =>
      intro init
      rw [List.range_succ, List.foldl_append, List.foldl_append, ih]
      simp only [List.foldl_cons, List.foldl_nil, hb_succ]
  rw [hcongr]

/-- **FIPS 205 `Spec.T` theorem for `compress_multi_1`**:
Continuing from `pkState512` over the padded suffix of `adrs.compress ++ msg`
computes exact FIPS 205 `Spec.T p pkSeed adrs msg` for SHA-2 Category 3 & 5
(`p.n ∈ {24, 32}`). -/
theorem compress_multi_1_eq_fips_T (p : Spec.Params)
    (hfam : p.family = .sha2) (hN : p.n = 24 ∨ p.n = 32)
    (pkSeed msg : Spec.Bytes) (hpk : pkSeed.length = p.n) (adrs : Spec.Adrs) :
    let b0 := pkSeed ++ Spec.toByte 0 (128 - p.n)
    let paddedSuffix := (Spec.SHA512.pad (b0 ++ (adrs.compress ++ msg))).drop 128
    compressMulti1 p.n (pkState512 p.n pkSeed) paddedSuffix =
      Spec.T p pkSeed adrs msg := by
  have hne16 : p.n ≠ 16 := by omega
  have h := compress_multi_1_eq_sha512_from_pkState p.n hN pkSeed (adrs.compress ++ msg) hpk
  dsimp only at h ⊢
  rw [h]
  simp only [Spec.T, hfam, hne16, ↓reduceIte, List.append_assoc]

/-! ## 5. `parent_block_512` and single-block `Spec.H` -/

/-- Exact 128-byte second SHA-512 block built by `sha512::paired::parent_block_512`:
`adrs.compress (22) ‖ left (N) ‖ right (N) ‖ 0x80 ‖ 0^{97 - 2N} ‖ toByte ((150 + 2N)*8) 8`. -/
def parentBlock512 (N : Nat) (adrs : Spec.Adrs) (left right : Spec.Bytes) : Spec.Bytes :=
  adrs.compress ++ left ++ right ++ [0x80#8] ++
    List.replicate (120 - (22 + 2 * N + 1)) 0#8 ++
    Spec.toByte ((150 + 2 * N) * 8) 8

private theorem toByte_zero_pad16 (v : Nat) (hv : v < 2 ^ 64) :
    Spec.toByte v 16 = List.replicate 8 0#8 ++ Spec.toByte v 8 := by
  have hdiv : ∀ i, i < 8 → v >>> (8 * (15 - i)) = 0 := by
    intro i hi
    rw [Nat.shiftRight_eq_div_pow]
    apply Nat.div_eq_of_lt
    have hpow : 2 ^ 64 ≤ 2 ^ (8 * (15 - i)) := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  apply List.ext_getElem
  · simp [Spec.toByte]
  · intro i hi1 hi2
    simp only [Spec.toByte, List.length_map, List.length_range] at hi1
    simp only [Spec.toByte, List.getElem_map, List.getElem_range, List.getElem_append,
      List.length_replicate, List.getElem_replicate]
    by_cases hlt : i < 8
    · rw [dif_pos hlt, show 16 - 1 - i = 15 - i by omega, hdiv i hlt]
    · rw [dif_neg hlt]; congr 2; omega

private theorem adrs_compress_length (adrs : Spec.Adrs) : adrs.compress.length = 22 := by
  simp [Spec.Adrs.compress, Spec.Adrs.bytes, Spec.toByte]

/-- `parentBlock512` is the exact second 128-byte block of `Spec.SHA512.pad`
for `PK.seed ‖ 0^{128 - N} ‖ ADRSc ‖ left ‖ right` when `N ∈ {24, 32}`. -/
theorem parentBlock512_eq_pad_drop128 (N : Nat) (hN : N = 24 ∨ N = 32)
    (pkSeed left right : Spec.Bytes) (adrs : Spec.Adrs)
    (hpk : pkSeed.length = N) (hl : left.length = N) (hr : right.length = N) :
    let b0 := pkSeed ++ Spec.toByte 0 (128 - N)
    (Spec.SHA512.pad (b0 ++ (adrs.compress ++ (left ++ right)))).drop 128 =
      parentBlock512 N adrs left right := by
  intro b0
  have hb0 : b0.length = 128 := by simp [b0, Spec.toByte, hpk]; omega
  have hac : adrs.compress.length = 22 := adrs_compress_length adrs
  have htot : (b0 ++ (adrs.compress ++ (left ++ right))).length = 150 + 2 * N := by
    simp [hb0, hac, hl, hr]; omega
  have hzeros : (239 - (150 + 2 * N) % 128) % 128 + 8 = 120 - (22 + 2 * N + 1) := by
    rcases hN with rfl | rfl <;> decide
  have hbits_lt : 8 * (150 + 2 * N) < 2 ^ 64 := by omega
  unfold Spec.SHA512.pad parentBlock512
  rw [htot, toByte_zero_pad16 _ hbits_lt]
  have hmul : 8 * (150 + 2 * N) = (150 + 2 * N) * 8 := Nat.mul_comm _ _
  rw [hmul]
  have hdrop : ∀ rest : Spec.Bytes, (b0 ++ rest).drop 128 = rest := fun rest => by
    rw [← hb0, List.drop_append_of_le_length (Nat.le_refl _), List.drop_length, List.nil_append]
  rw [show b0 ++ (adrs.compress ++ (left ++ right)) ++ [0x80#8] ++
      List.replicate ((239 - (150 + 2 * N) % 128) % 128) 0#8 ++
      (List.replicate 8 0#8 ++ Spec.toByte ((150 + 2 * N) * 8) 8) =
      b0 ++ (adrs.compress ++ left ++ right ++ [0x80#8] ++
        (List.replicate ((239 - (150 + 2 * N) % 128) % 128) 0#8 ++ List.replicate 8 0#8) ++
        Spec.toByte ((150 + 2 * N) * 8) 8) by simp [List.append_assoc]]
  rw [hdrop, ← List.replicate_add, hzeros]

/-- Compressing `parentBlock512` via `compressParentHw` from `pkState512`
computes exact FIPS 205 `Spec.H` for `N ∈ {24, 32}`! -/
theorem compressParentHw_eq_fips_H (p : Spec.Params)
    (hfam : p.family = .sha2) (hN : p.n = 24 ∨ p.n = 32)
    (pkSeed left right : Spec.Bytes) (adrs : Spec.Adrs)
    (hpk : pkSeed.length = p.n) (hl : left.length = p.n) (hr : right.length = p.n) :
    compressParentHw p.n (pkState512 p.n pkSeed) (parentBlock512 p.n adrs left right) =
      Spec.H p pkSeed adrs (left ++ right) := by
  have hne16 : p.n ≠ 16 := by omega
  have hpad := parentBlock512_eq_pad_drop128 p.n hN pkSeed left right adrs hpk hl hr
  have hpb_len : (parentBlock512 p.n adrs left right).length = 128 := by
    simp only [parentBlock512, List.length_append, adrs_compress_length, hl, hr,
      List.length_cons, List.length_nil, List.length_replicate, Spec.toByte,
      List.length_map, List.length_range]
    omega
  have hcm := compress_multi_1_eq_sha512_from_pkState p.n hN pkSeed
    (adrs.compress ++ (left ++ right)) hpk
  dsimp only at hpad hcm
  rw [hpad] at hcm
  have hcm1 : compressMulti1 p.n (pkState512 p.n pkSeed) (parentBlock512 p.n adrs left right) =
      compressParentHw p.n (pkState512 p.n pkSeed) (parentBlock512 p.n adrs left right) := by
    have hst_len : (pkState512 p.n pkSeed).length = 8 := compress512_length _ _
    rw [compress_multi_1_eq_iter p.n hN (pkState512 p.n pkSeed) hst_len,
      compressParentHw_eq_fips p.n hN]
    unfold iterCompress
    rw [hpb_len, show (128 : Nat) / 128 = 1 by rfl, show List.range 1 = [0] by rfl]
    simp only [List.foldl_cons, List.foldl_nil, blockAt, Nat.mul_zero, List.drop_zero,
      List.take_of_length_le (by omega : (parentBlock512 p.n adrs left right).length ≤ 128)]
  rw [← hcm1, hcm]
  simp only [Spec.H, hfam, hne16, ↓reduceIte, List.append_assoc]

/-! ## 6. `parents_batch` (4-way + 2-way, in-place overwrite safety) -/

/-- Functional model of `sha512::paired::parents_batch_active`:
- While `j + 4 ≤ count`, reads children `values[2*(j+lane)]`, `values[2*(j+lane)+1]`
  for `lane ∈ 0..3`, hashes them in 4 lockstep lanes via `compressParentHw`, and
  overwrites `values[j..j+4]` in place.
- If `j + 2 ≤ count`, does the same for 2 lanes via `compressParentHw` and
  overwrites `values[j..j+2]` in place.
- Returns `(done, values')`. -/
def parentsBatchLoop4 (N : Nat) (st : List Word) (adrs : Spec.Adrs) (first : Nat)
    (count j : Nat) (values : Nat → Spec.Bytes) (fuel : Nat) : Nat × (Nat → Spec.Bytes) :=
  match fuel with
  | 0 => (j, values)
  | fuel' + 1 =>
    if j + 4 ≤ count then
      let p0 := compressParentHw N st (parentBlock512 N { adrs with word3 := first + j } (values (2 * j)) (values (2 * j + 1)))
      let p1 := compressParentHw N st (parentBlock512 N { adrs with word3 := first + j + 1 } (values (2 * (j + 1))) (values (2 * (j + 1) + 1)))
      let p2 := compressParentHw N st (parentBlock512 N { adrs with word3 := first + j + 2 } (values (2 * (j + 2))) (values (2 * (j + 2) + 1)))
      let p3 := compressParentHw N st (parentBlock512 N { adrs with word3 := first + j + 3 } (values (2 * (j + 3))) (values (2 * (j + 3) + 1)))
      let values' := fun idx =>
        if idx = j then p0
        else if idx = j + 1 then p1
        else if idx = j + 2 then p2
        else if idx = j + 3 then p3
        else values idx
      parentsBatchLoop4 N st adrs first count (j + 4) values' fuel'
    else
      (j, values)

def parentsBatch (N : Nat) (st : List Word) (adrs : Spec.Adrs) (first count : Nat)
    (values : Nat → Spec.Bytes) : Nat × (Nat → Spec.Bytes) :=
  if count < 2 then (0, values)
  else
    let (j, v1) := parentsBatchLoop4 N st adrs first count 0 values (count / 4 + 1)
    if j + 2 ≤ count then
      let p0 := compressParentHw N st (parentBlock512 N { adrs with word3 := first + j } (v1 (2 * j)) (v1 (2 * j + 1)))
      let p1 := compressParentHw N st (parentBlock512 N { adrs with word3 := first + j + 1 } (v1 (2 * (j + 1))) (v1 (2 * (j + 1) + 1)))
      let v2 := fun idx =>
        if idx = j then p0
        else if idx = j + 1 then p1
        else v1 idx
      (j + 2, v2)
    else
      (j, v1)

private def parentsBatchLoop4Gen (N : Nat) (f : Spec.Bytes → Spec.Bytes)
    (adrs : Spec.Adrs) (first count j : Nat) (values : Nat → Spec.Bytes) :
    Nat → Nat × (Nat → Spec.Bytes)
  | 0 => (j, values)
  | fuel' + 1 =>
    if j + 4 ≤ count then
      let p0 := f (parentBlock512 N { adrs with word3 := first + j } (values (2 * j)) (values (2 * j + 1)))
      let p1 := f (parentBlock512 N { adrs with word3 := first + j + 1 } (values (2 * (j + 1))) (values (2 * (j + 1) + 1)))
      let p2 := f (parentBlock512 N { adrs with word3 := first + j + 2 } (values (2 * (j + 2))) (values (2 * (j + 2) + 1)))
      let p3 := f (parentBlock512 N { adrs with word3 := first + j + 3 } (values (2 * (j + 3))) (values (2 * (j + 3) + 1)))
      let values' := fun idx =>
        if idx = j then p0
        else if idx = j + 1 then p1
        else if idx = j + 2 then p2
        else if idx = j + 3 then p3
        else values idx
      parentsBatchLoop4Gen N f adrs first count (j + 4) values' fuel'
    else
      (j, values)

private theorem parentsBatchLoop4_spec_gen (N : Nat)
    (f : Spec.Bytes → Spec.Bytes) (g : Spec.Adrs → Spec.Bytes → Spec.Bytes)
    (hfg : ∀ adrs l r, l.length = N → r.length = N →
      f (parentBlock512 N adrs l r) = g adrs (l ++ r))
    (adrs : Spec.Adrs) (first count : Nat) (orig : Nat → Spec.Bytes)
    (horig : ∀ k < 2 * count, (orig k).length = N)
    (j : Nat) (values : Nat → Spec.Bytes) (fuel : Nat)
    (hj_le : j ≤ count) (hj_mod : j % 4 = 0) (hfuel : (count - j) / 4 < fuel)
    (hdone : ∀ i < j, values i = g { adrs with word3 := first + i } (orig (2 * i) ++ orig (2 * i + 1)))
    (huntouched : ∀ k, 2 * j ≤ k → values k = orig k) :
    let (j', v') := parentsBatchLoop4Gen N f adrs first count j values fuel
    j' = (count / 4) * 4 ∧
    (∀ i < j', v' i = g { adrs with word3 := first + i } (orig (2 * i) ++ orig (2 * i + 1))) ∧
    (∀ k, 2 * j' ≤ k → v' k = orig k) := by
  induction fuel generalizing j values with
  | zero => omega
  | succ fuel' ih =>
    unfold parentsBatchLoop4Gen
    by_cases h4 : j + 4 ≤ count
    · simp only [h4, ↓reduceIte]
      have hH0 : f (parentBlock512 N { adrs with word3 := first + j } (values (2 * j)) (values (2 * j + 1))) =
          g { adrs with word3 := first + j } (orig (2 * j) ++ orig (2 * j + 1)) := by
        rw [huntouched (2 * j) (by omega), huntouched (2 * j + 1) (by omega)]
        exact hfg _ _ _ (horig _ (by omega)) (horig _ (by omega))
      have hH1 : f (parentBlock512 N { adrs with word3 := first + j + 1 } (values (2 * (j + 1))) (values (2 * (j + 1) + 1))) =
          g { adrs with word3 := first + (j + 1) } (orig (2 * (j + 1)) ++ orig (2 * (j + 1) + 1)) := by
        rw [huntouched (2 * (j + 1)) (by omega), huntouched (2 * (j + 1) + 1) (by omega), Nat.add_assoc]
        exact hfg _ _ _ (horig _ (by omega)) (horig _ (by omega))
      have hH2 : f (parentBlock512 N { adrs with word3 := first + j + 2 } (values (2 * (j + 2))) (values (2 * (j + 2) + 1))) =
          g { adrs with word3 := first + (j + 2) } (orig (2 * (j + 2)) ++ orig (2 * (j + 2) + 1)) := by
        rw [huntouched (2 * (j + 2)) (by omega), huntouched (2 * (j + 2) + 1) (by omega), Nat.add_assoc]
        exact hfg _ _ _ (horig _ (by omega)) (horig _ (by omega))
      have hH3 : f (parentBlock512 N { adrs with word3 := first + j + 3 } (values (2 * (j + 3))) (values (2 * (j + 3) + 1))) =
          g { adrs with word3 := first + (j + 3) } (orig (2 * (j + 3)) ++ orig (2 * (j + 3) + 1)) := by
        rw [huntouched (2 * (j + 3)) (by omega), huntouched (2 * (j + 3) + 1) (by omega), Nat.add_assoc]
        exact hfg _ _ _ (horig _ (by omega)) (horig _ (by omega))
      apply ih (j + 4) _ (by omega) (by omega) (by omega)
      · intro i hi
        by_cases h0 : i = j
        · subst h0; simp only [↓reduceIte]; exact hH0
        · simp only [h0, ↓reduceIte]
          by_cases h1 : i = j + 1
          · subst h1; simp only [↓reduceIte]; exact hH1
          · simp only [h1, ↓reduceIte]
            by_cases h2 : i = j + 2
            · subst h2; simp only [↓reduceIte]; exact hH2
            · simp only [h2, ↓reduceIte]
              by_cases h3 : i = j + 3
              · subst h3; simp only [↓reduceIte]; exact hH3
              · simp only [h3, ↓reduceIte]; exact hdone i (by omega)
      · intro k hk
        simp only [show ¬k = j by omega, show ¬k = j + 1 by omega,
          show ¬k = j + 2 by omega, show ¬k = j + 3 by omega, ↓reduceIte]
        exact huntouched k (by omega)
    · simp only [h4, ↓reduceIte]
      exact ⟨by omega, hdone, huntouched⟩

private theorem parentsBatchLoop4_eq_go (N : Nat) (st : List Word) (adrs : Spec.Adrs) (first count j : Nat)
    (values : Nat → Spec.Bytes) (fuel : Nat) :
    parentsBatchLoop4 N st adrs first count j values fuel =
      parentsBatchLoop4Gen N (compressParentHw N st) adrs first count j values fuel := by
  induction fuel generalizing j values with
  | zero => rfl
  | succ fuel' ih =>
    unfold parentsBatchLoop4 parentsBatchLoop4Gen
    by_cases h4 : j + 4 ≤ count
    · simp only [h4, ↓reduceIte]; exact ih _ _
    · simp only [h4, ↓reduceIte]

/-- **Main theorem for `sha512::paired::parents_batch`**:
For any `count` and `N ∈ {24, 32}`, `parentsBatch` returns `done = (count / 2) * 2`,
writes exact FIPS 205 `Spec.H p pkSeed { adrs with word3 := first + i } (orig (2*i) ++ orig (2*i+1))`
into every slot `0 ≤ i < done`, AND leaves every untouched tail slot `k ≥ 2 * done`
(in particular the remaining pair `(2 * done, 2 * done + 1)` when `count` is odd)
completely intact for the scalar tail! -/
theorem parents_batch_eq_fips (p : Spec.Params) (hfam : p.family = .sha2)
    (hN : p.n = 24 ∨ p.n = 32) (pkSeed : Spec.Bytes) (hpk : pkSeed.length = p.n)
    (adrs : Spec.Adrs) (first count : Nat) (orig : Nat → Spec.Bytes)
    (horig : ∀ k < 2 * count, (orig k).length = p.n) :
    let (done, out) := parentsBatch p.n (pkState512 p.n pkSeed) adrs first count orig
    done = (count / 2) * 2 ∧
    (∀ i < done, out i = Spec.H p pkSeed { adrs with word3 := first + i }
      (orig (2 * i) ++ orig (2 * i + 1))) ∧
    (∀ k, 2 * done ≤ k → out k = orig k) := by
  have hfg : ∀ adr l r, l.length = p.n → r.length = p.n →
      compressParentHw p.n (pkState512 p.n pkSeed) (parentBlock512 p.n adr l r) =
      Spec.H p pkSeed adr (l ++ r) :=
    fun adr l r hl hr => compressParentHw_eq_fips_H p hfam hN pkSeed l r adr hpk hl hr
  unfold parentsBatch
  by_cases hlt2 : count < 2
  · simp only [hlt2, ↓reduceIte]
    exact ⟨by omega, fun i hi => by omega, fun _ _ => trivial⟩
  · simp only [hlt2, ↓reduceIte]
    have h4 := parentsBatchLoop4_spec_gen p.n (compressParentHw p.n (pkState512 p.n pkSeed))
      (Spec.H p pkSeed) hfg adrs first count orig horig
      0 orig (count / 4 + 1) (by omega) rfl (by omega) (fun i hi => by omega) (fun _ _ => rfl)
    rw [← parentsBatchLoop4_eq_go] at h4
    rcases hres : parentsBatchLoop4 p.n (pkState512 p.n pkSeed) adrs first count 0 orig (count / 4 + 1) with ⟨j, v1⟩
    rw [hres] at h4
    obtain ⟨hj_eq, hv1_done, hv1_unt⟩ := h4
    dsimp only
    by_cases h2 : j + 2 ≤ count
    · simp only [h2, ↓reduceIte]
      have hH0 : compressParentHw p.n (pkState512 p.n pkSeed)
          (parentBlock512 p.n { adrs with word3 := first + j } (v1 (2 * j)) (v1 (2 * j + 1))) =
          Spec.H p pkSeed { adrs with word3 := first + j } (orig (2 * j) ++ orig (2 * j + 1)) := by
        rw [hv1_unt (2 * j) (by omega), hv1_unt (2 * j + 1) (by omega)]
        exact hfg _ _ _ (horig _ (by omega)) (horig _ (by omega))
      have hH1 : compressParentHw p.n (pkState512 p.n pkSeed)
          (parentBlock512 p.n { adrs with word3 := first + j + 1 } (v1 (2 * (j + 1))) (v1 (2 * (j + 1) + 1))) =
          Spec.H p pkSeed { adrs with word3 := first + (j + 1) }
            (orig (2 * (j + 1)) ++ orig (2 * (j + 1) + 1)) := by
        rw [hv1_unt (2 * (j + 1)) (by omega), hv1_unt (2 * (j + 1) + 1) (by omega), Nat.add_assoc]
        exact hfg _ _ _ (horig _ (by omega)) (horig _ (by omega))
      refine ⟨by omega, ?_, ?_⟩
      · intro i hi
        by_cases h0 : i = j
        · subst h0; simp only [↓reduceIte]; exact hH0
        · simp only [h0, ↓reduceIte]
          by_cases h1 : i = j + 1
          · subst h1; simp only [↓reduceIte]; exact hH1
          · simp only [h1, ↓reduceIte]; exact hv1_done i (by omega)
      · intro k hk
        simp only [show ¬k = j by omega, show ¬k = j + 1 by omega, ↓reduceIte]
        exact hv1_unt k (by omega)
    · simp only [h2, ↓reduceIte]
      exact ⟨by omega, hv1_done, hv1_unt⟩

/-! ## 7. `path_parents_batch` (4-way + 2-way FORS auth-path climbing) -/

/-- One lane's parent computation in `sha512::paired::path_parents_batch_active`:
reads `pos = indices[i]`, halves `idx' = pos / 2`, extracts sibling from `sig`
at byte offset `N * (i * (height + 1) + 1 + offset)`, orders `(node, sibling)`
by `pos % 2 == 0`, and computes `compressParentHw` with `adrs.with_word3 idx'`. -/
def pathLaneHash (N : Nat) (st : List Word) (adrs : Spec.Adrs)
    (sig : Spec.Bytes) (height offset : Nat) (i : Nat)
    (node : Spec.Bytes) (pos : Nat) : Spec.Bytes :=
  let idx' := pos / 2
  let start := N * (i * (height + 1) + 1 + offset)
  let sibling := (sig.drop start).take N
  let (left, right) := if pos % 2 = 0 then (node, sibling) else (sibling, node)
  compressParentHw N st (parentBlock512 N { adrs with word3 := idx' } left right)

def pathBatchLoop4 (N : Nat) (st : List Word) (adrs : Spec.Adrs)
    (sig : Spec.Bytes) (height offset count j : Nat)
    (values : Nat → Spec.Bytes) (indices : Nat → Nat) (fuel : Nat) :
    Nat × (Nat → Spec.Bytes) × (Nat → Nat) :=
  match fuel with
  | 0 => (j, values, indices)
  | fuel' + 1 =>
    if j + 4 ≤ count then
      let p0 := pathLaneHash N st adrs sig height offset j (values j) (indices j)
      let p1 := pathLaneHash N st adrs sig height offset (j + 1) (values (j + 1)) (indices (j + 1))
      let p2 := pathLaneHash N st adrs sig height offset (j + 2) (values (j + 2)) (indices (j + 2))
      let p3 := pathLaneHash N st adrs sig height offset (j + 3) (values (j + 3)) (indices (j + 3))
      let values' := fun idx =>
        if idx = j then p0
        else if idx = j + 1 then p1
        else if idx = j + 2 then p2
        else if idx = j + 3 then p3
        else values idx
      let indices' := fun idx =>
        if idx = j ∨ idx = j + 1 ∨ idx = j + 2 ∨ idx = j + 3 then indices idx / 2
        else indices idx
      pathBatchLoop4 N st adrs sig height offset count (j + 4) values' indices' fuel'
    else
      (j, values, indices)

def pathParentsBatch (N : Nat) (st : List Word) (adrs : Spec.Adrs)
    (sig : Spec.Bytes) (height offset count : Nat)
    (values : Nat → Spec.Bytes) (indices : Nat → Nat) :
    Nat × (Nat → Spec.Bytes) × (Nat → Nat) :=
  if count < 2 then (0, values, indices)
  else
    let (j, v1, idx1) := pathBatchLoop4 N st adrs sig height offset count 0 values indices (count / 4 + 1)
    if j + 2 ≤ count then
      let p0 := pathLaneHash N st adrs sig height offset j (v1 j) (idx1 j)
      let p1 := pathLaneHash N st adrs sig height offset (j + 1) (v1 (j + 1)) (idx1 (j + 1))
      let v2 := fun idx =>
        if idx = j then p0
        else if idx = j + 1 then p1
        else v1 idx
      let idx2 := fun idx =>
        if idx = j ∨ idx = j + 1 then idx1 idx / 2
        else idx1 idx
      (j + 2, v2, idx2)
    else
      (j, v1, idx1)

private theorem pathLaneHash_eq_fips (p : Spec.Params) (hfam : p.family = .sha2)
    (hN : p.n = 24 ∨ p.n = 32) (pkSeed sig : Spec.Bytes) (adrs : Spec.Adrs)
    (height offset i : Nat) (node : Spec.Bytes) (pos : Nat)
    (hpk : pkSeed.length = p.n) (hnode : node.length = p.n)
    (hsig : p.n * (i * (height + 1) + 1 + offset) + p.n ≤ sig.length) :
    let sibling := (sig.drop (p.n * (i * (height + 1) + 1 + offset))).take p.n
    pathLaneHash p.n (pkState512 p.n pkSeed) adrs sig height offset i node pos =
      if pos % 2 = 0 then
        Spec.H p pkSeed { adrs with word3 := pos / 2 } (node ++ sibling)
      else
        Spec.H p pkSeed { adrs with word3 := pos / 2 } (sibling ++ node) := by
  intro sibling
  have hsib : sibling.length = p.n := by
    simp only [sibling, List.length_take, List.length_drop]
    omega
  unfold pathLaneHash
  split
  · exact compressParentHw_eq_fips_H p hfam hN pkSeed node sibling _ hpk hnode hsib
  · exact compressParentHw_eq_fips_H p hfam hN pkSeed sibling node _ hpk hsib hnode

private theorem pathBatchLoop4_spec (p : Spec.Params) (hfam : p.family = .sha2)
    (hN : p.n = 24 ∨ p.n = 32) (pkSeed sig : Spec.Bytes) (hpk : pkSeed.length = p.n)
    (adrs : Spec.Adrs) (height offset count : Nat)
    (origV : Nat → Spec.Bytes) (origIdx : Nat → Nat)
    (horigV : ∀ i < count, (origV i).length = p.n)
    (hsig : ∀ i < count, p.n * (i * (height + 1) + 1 + offset) + p.n ≤ sig.length)
    (j : Nat) (values : Nat → Spec.Bytes) (indices : Nat → Nat) (fuel : Nat)
    (hj_le : j ≤ count) (hj_mod : j % 4 = 0) (hfuel : (count - j) / 4 < fuel)
    (hdoneV : ∀ i < j,
      let sibling := (sig.drop (p.n * (i * (height + 1) + 1 + offset))).take p.n
      values i = if origIdx i % 2 = 0 then
        Spec.H p pkSeed { adrs with word3 := origIdx i / 2 } (origV i ++ sibling)
      else
        Spec.H p pkSeed { adrs with word3 := origIdx i / 2 } (sibling ++ origV i))
    (hdoneI : ∀ i < j, indices i = origIdx i / 2)
    (huntV : ∀ i, j ≤ i → values i = origV i)
    (huntI : ∀ i, j ≤ i → indices i = origIdx i) :
    let (j', v', idx') := pathBatchLoop4 p.n (pkState512 p.n pkSeed) adrs sig height offset count j values indices fuel
    j' = (count / 4) * 4 ∧
    (∀ i < j',
      let sibling := (sig.drop (p.n * (i * (height + 1) + 1 + offset))).take p.n
      v' i = if origIdx i % 2 = 0 then
        Spec.H p pkSeed { adrs with word3 := origIdx i / 2 } (origV i ++ sibling)
      else
        Spec.H p pkSeed { adrs with word3 := origIdx i / 2 } (sibling ++ origV i)) ∧
    (∀ i < j', idx' i = origIdx i / 2) ∧
    (∀ i, j' ≤ i → v' i = origV i ∧ idx' i = origIdx i) := by
  induction fuel generalizing j values indices with
  | zero => omega
  | succ fuel' ih =>
    unfold pathBatchLoop4
    by_cases h4 : j + 4 ≤ count
    · simp only [h4, ↓reduceIte]
      have hLane : ∀ lane < 4,
          pathLaneHash p.n (pkState512 p.n pkSeed) adrs sig height offset (j + lane)
            (values (j + lane)) (indices (j + lane)) =
          let sibling := (sig.drop (p.n * ((j + lane) * (height + 1) + 1 + offset))).take p.n
          if origIdx (j + lane) % 2 = 0 then
            Spec.H p pkSeed { adrs with word3 := origIdx (j + lane) / 2 } (origV (j + lane) ++ sibling)
          else
            Spec.H p pkSeed { adrs with word3 := origIdx (j + lane) / 2 } (sibling ++ origV (j + lane)) := by
        intro lane hl
        rw [huntV (j + lane) (by omega), huntI (j + lane) (by omega)]
        exact pathLaneHash_eq_fips p hfam hN pkSeed sig adrs height offset (j + lane)
          (origV (j + lane)) (origIdx (j + lane)) hpk (horigV _ (by omega)) (hsig _ (by omega))
      have hL0 : pathLaneHash p.n (pkState512 p.n pkSeed) adrs sig height offset j (values j) (indices j) =
          let sibling := (sig.drop (p.n * (j * (height + 1) + 1 + offset))).take p.n
          if origIdx j % 2 = 0 then
            Spec.H p pkSeed { adrs with word3 := origIdx j / 2 } (origV j ++ sibling)
          else
            Spec.H p pkSeed { adrs with word3 := origIdx j / 2 } (sibling ++ origV j) := by
        have := hLane 0 (by omega); simp only [Nat.add_zero] at this; exact this
      apply ih (j + 4) _ _ (by omega) (by omega) (by omega)
      · intro i hi
        dsimp only
        by_cases h0 : i = j
        · subst h0; simp only [↓reduceIte]; exact hL0
        · simp only [h0, ↓reduceIte]
          by_cases h1 : i = j + 1
          · subst h1; simp only [↓reduceIte]; exact hLane 1 (by omega)
          · simp only [h1, ↓reduceIte]
            by_cases h2 : i = j + 2
            · subst h2; simp only [↓reduceIte]; exact hLane 2 (by omega)
            · simp only [h2, ↓reduceIte]
              by_cases h3 : i = j + 3
              · subst h3; simp only [↓reduceIte]; exact hLane 3 (by omega)
              · simp only [h3, ↓reduceIte]; exact hdoneV i (by omega)
      · intro i hi
        by_cases hcur : i = j ∨ i = j + 1 ∨ i = j + 2 ∨ i = j + 3
        · simp only [hcur, ↓reduceIte]; rw [huntI i (by omega)]
        · simp only [hcur, ↓reduceIte]; exact hdoneI i (by omega)
      · intro i hi
        simp only [show ¬i = j by omega, show ¬i = j + 1 by omega,
          show ¬i = j + 2 by omega, show ¬i = j + 3 by omega, ↓reduceIte]
        exact huntV i (by omega)
      · intro i hi
        simp only [show ¬(i = j ∨ i = j + 1 ∨ i = j + 2 ∨ i = j + 3) by omega, ↓reduceIte]
        exact huntI i (by omega)
    · simp only [h4, ↓reduceIte]
      exact ⟨by omega, hdoneV, hdoneI, fun i hi => ⟨huntV i hi, huntI i hi⟩⟩

/-- **Main theorem for `sha512::paired::path_parents_batch`**:
For any `count` FORS trees, `height`, `offset < height`, and `N ∈ {24, 32}`,
`pathParentsBatch` returns `done = (count / 2) * 2` such that:
- Every processed tree `i < done` has its node replaced by exact FIPS 205 `Spec.H`
  with sibling ordering `(node, sibling)` when `origIdx i` is even and
  `(sibling, node)` when `origIdx i` is odd, at address `word3 := origIdx i / 2`,
  and its index halved (`origIdx i / 2`);
- Every unprocessed tail tree `i ≥ done` (at most 1 tree when `count` is odd)
  has both `values[i]` and `indices[i]` untouched for the scalar tail! -/
theorem path_parents_batch_eq_fips (p : Spec.Params) (hfam : p.family = .sha2)
    (hN : p.n = 24 ∨ p.n = 32) (pkSeed sig : Spec.Bytes) (hpk : pkSeed.length = p.n)
    (adrs : Spec.Adrs) (height offset count : Nat)
    (origV : Nat → Spec.Bytes) (origIdx : Nat → Nat)
    (horigV : ∀ i < count, (origV i).length = p.n)
    (hsig : ∀ i < count, p.n * (i * (height + 1) + 1 + offset) + p.n ≤ sig.length) :
    let (done, outV, outIdx) := pathParentsBatch p.n (pkState512 p.n pkSeed) adrs sig height offset count origV origIdx
    done = (count / 2) * 2 ∧
    (∀ i < done,
      let sibling := (sig.drop (p.n * (i * (height + 1) + 1 + offset))).take p.n
      outV i = if origIdx i % 2 = 0 then
        Spec.H p pkSeed { adrs with word3 := origIdx i / 2 } (origV i ++ sibling)
      else
        Spec.H p pkSeed { adrs with word3 := origIdx i / 2 } (sibling ++ origV i)) ∧
    (∀ i < done, outIdx i = origIdx i / 2) ∧
    (∀ i, done ≤ i → outV i = origV i ∧ outIdx i = origIdx i) := by
  unfold pathParentsBatch
  by_cases hlt2 : count < 2
  · simp only [hlt2, ↓reduceIte]
    exact ⟨by omega, fun _ hi => by omega, fun _ hi => by omega, fun _ _ => ⟨trivial, trivial⟩⟩
  · simp only [hlt2, ↓reduceIte]
    have h4 := pathBatchLoop4_spec p hfam hN pkSeed sig hpk adrs height offset count origV origIdx
      horigV hsig 0 origV origIdx (count / 4 + 1) (by omega) rfl (by omega)
      (fun _ hi => by omega) (fun _ hi => by omega) (fun _ _ => rfl) (fun _ _ => rfl)
    rcases hres : pathBatchLoop4 p.n (pkState512 p.n pkSeed) adrs sig height offset count 0 origV origIdx (count / 4 + 1) with ⟨j, v1, idx1⟩
    rw [hres] at h4
    obtain ⟨hj_eq, hv1_done, hi1_done, hunt1⟩ := h4
    dsimp only
    by_cases h2 : j + 2 ≤ count
    · simp only [h2, ↓reduceIte]
      have hL0 : pathLaneHash p.n (pkState512 p.n pkSeed) adrs sig height offset j (v1 j) (idx1 j) =
          let sibling := (sig.drop (p.n * (j * (height + 1) + 1 + offset))).take p.n
          if origIdx j % 2 = 0 then
            Spec.H p pkSeed { adrs with word3 := origIdx j / 2 } (origV j ++ sibling)
          else
            Spec.H p pkSeed { adrs with word3 := origIdx j / 2 } (sibling ++ origV j) := by
        rw [(hunt1 j le_rfl).1, (hunt1 j le_rfl).2]
        exact pathLaneHash_eq_fips p hfam hN pkSeed sig adrs height offset j
          (origV j) (origIdx j) hpk (horigV _ (by omega)) (hsig _ (by omega))
      have hL1 : pathLaneHash p.n (pkState512 p.n pkSeed) adrs sig height offset (j + 1) (v1 (j + 1)) (idx1 (j + 1)) =
          let sibling := (sig.drop (p.n * ((j + 1) * (height + 1) + 1 + offset))).take p.n
          if origIdx (j + 1) % 2 = 0 then
            Spec.H p pkSeed { adrs with word3 := origIdx (j + 1) / 2 } (origV (j + 1) ++ sibling)
          else
            Spec.H p pkSeed { adrs with word3 := origIdx (j + 1) / 2 } (sibling ++ origV (j + 1)) := by
        rw [(hunt1 (j + 1) (by omega)).1, (hunt1 (j + 1) (by omega)).2]
        exact pathLaneHash_eq_fips p hfam hN pkSeed sig adrs height offset (j + 1)
          (origV (j + 1)) (origIdx (j + 1)) hpk (horigV _ (by omega)) (hsig _ (by omega))
      refine ⟨by omega, ?_, ?_, ?_⟩
      · intro i hi
        by_cases h0 : i = j
        · subst h0; simp only [↓reduceIte]; exact hL0
        · simp only [h0, ↓reduceIte]
          by_cases h1 : i = j + 1
          · subst h1; simp only [↓reduceIte]; exact hL1
          · simp only [h1, ↓reduceIte]; exact hv1_done i (by omega)
      · intro i hi
        by_cases hcur : i = j ∨ i = j + 1
        · simp only [hcur, ↓reduceIte]; rw [(hunt1 i (by omega)).2]
        · simp only [hcur, ↓reduceIte]; exact hi1_done i (by omega)
      · intro i hi
        simp only [show ¬i = j by omega, show ¬i = j + 1 by omega, ↓reduceIte]
        exact hunt1 i (by omega)
    · simp only [h2, ↓reduceIte]
      exact ⟨by omega, hv1_done, hi1_done, hunt1⟩

/-- Note on FIPS 205 `Spec.climb` index halving:
In `Spec.climb`, even positions use `ti / 2` and odd positions use `(ti - 1) / 2`.
Both equal `ti / 2` in natural-number division (i.e. `indices[i] >>= 1`). -/
theorem climb_halve_eq_div2 (ti : Nat) (hodd : ti % 2 ≠ 0) : (ti - 1) / 2 = ti / 2 := by
  omega

#print axioms beBytes64_eq_toByte
#print axioms storeTrunc_eq_fips
#print axioms paired_encode_eq_toByte
#print axioms compressBlockHw_eq_fips
#print axioms compressParentHw_eq_fips
#print axioms compress_multi_1_eq_iter
#print axioms compress_multi_2_eq_iter
#print axioms compress_multi_4_eq_iter
#print axioms compress_multi_1_eq_fips_T
#print axioms compressParentHw_eq_fips_H
#print axioms parents_batch_eq_fips
#print axioms path_parents_batch_eq_fips
#print axioms climb_halve_eq_div2

end slhdsa.H512.Multi
