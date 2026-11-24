import Slhdsa.Proofs.Hw.Rounds

/-!
# ARM64 SHA-256 `arm_wide.rs` 4-round head + 60-round deferred-schedule kernel

This module proves, directly over the Armv8 instruction semantics in `Arm.lean`
and the FIPS 180-4 SHA-256 specification in `Spec.Sha256`, that the two kernel
entry points in `rust/src/sha256/arm_wide.rs`:

1. `make_head` (rounds `0..3`) followed by `finish_from_r4` (rounds `4..63` with
   deferred `W16..W19` and `W20..W23` schedule updates after step 1's
   `vsha256hq_u32` / `vsha256h2q_u32`, and optional `NEED_EFGH` gating on
   step 15 and the feed-forward add), and
2. `compress_block_lanes` (all 64 rounds `0..63`, with optional `NEED_EFGH`
   gating on step 15)

compute exact FIPS 180-4 `Spec.SHA256.compress` (all 8 words when
`needEfgh = true`, and the first 4 words — i.e., the 16-byte truncated digest
for SLH-DSA-128 — when `needEfgh = false`).

We also prove that big-endian byte serialization (`store_n` for `N ∈ {16, 24, 32}`
via `vrev32q_u8`) matches `Spec.SHA256.compress` serialized with `Spec.toByte`.
-/

namespace slhdsa.Armwide.Kernel
open Spec.SHA256

/-- Four-round head (`arm_wide::make_head`): computes `(m0, a1, e1)` from the
initial state `st` and the first 16 bytes of the 64-byte block `B`. -/
def makeHead (st : List Word) (B : Spec.Bytes) : Arm.V × Arm.V × Arm.V :=
  let abcd0 := vOf st 0
  let efgh0 := vOf st 4
  let m0 := beV B 0
  let w := Arm.ADD m0 (vOf K 0)
  let a1 := Arm.SHA256H abcd0 efgh0 w
  let e1 := Arm.SHA256H2 efgh0 abcd0 w
  (m0, a1, e1)

/-- Step `I` of `arm_wide::step_lanes` for a single lane with `NEED_EFGH`. -/
def stepLane (needEfgh : Bool) (s : KState) (i : Nat) : KState :=
  let w := Arm.ADD s.m[i % 4]! (vOf K (4 * i))
  let abcd' := Arm.SHA256H s.abcd s.efgh w
  let efgh' := if i < 15 || needEfgh then Arm.SHA256H2 s.efgh s.abcd w else s.efgh
  let m' := if i < 12 then
      s.m.set (i % 4)
        (Arm.SHA256SU1 (Arm.SHA256SU0 s.m[i % 4]! s.m[(i + 1) % 4]!)
          s.m[(i + 2) % 4]! s.m[(i + 3) % 4]!)
    else s.m
  ⟨abcd', efgh', m'⟩

/-- Deferred-schedule rounds `4..63` + feed-forward (`arm_wide::finish_from_r4`)
for one lane. -/
def finishFromR4 (needEfgh : Bool) (st : List Word)
    (a1 e1 m0 m1 m2 m3 : Arm.V) : Arm.V × Arm.V :=
  -- Step 1 (rounds 4..7) with deferred w16 & w20 schedule updates
  let w1 := Arm.ADD m1 (vOf K 4)
  let a2 := Arm.SHA256H a1 e1 w1
  let e2 := Arm.SHA256H2 e1 a1 w1
  let w16 := Arm.SHA256SU1 (Arm.SHA256SU0 m0 m1) m2 m3
  let w20 := Arm.SHA256SU1 (Arm.SHA256SU0 m1 m2) m3 w16
  let s2 : KState := ⟨a2, e2, [w16, w20, m2, m3]⟩
  -- Steps 2..15
  let s16 := [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15].foldl (stepLane needEfgh) s2
  -- Feed-forward
  let abcdOut := Arm.ADD s16.abcd (vOf st 0)
  let efghOut := if needEfgh then Arm.ADD s16.efgh (vOf st 4) else ⟨0, 0, 0, 0⟩
  (abcdOut, efghOut)

/-- Full 64-round single-lane kernel (`arm_wide::compress_block_lanes`) + feed-forward. -/
def compressBlockLane (needEfgh : Bool) (st : List Word) (B : Spec.Bytes) : Arm.V × Arm.V :=
  let s0 : KState := ⟨vOf st 0, vOf st 4, [beV B 0, beV B 16, beV B 32, beV B 48]⟩
  let s16 := (List.range 16).foldl (stepLane needEfgh) s0
  let abcdOut := Arm.ADD s16.abcd (vOf st 0)
  let efghOut := if needEfgh then Arm.ADD s16.efgh (vOf st 4) else ⟨0, 0, 0, 0⟩
  (abcdOut, efghOut)

/-- For steps `i < 15`, `stepLane needEfgh` is identical to `kstep` regardless of `needEfgh`. -/
private theorem stepLane_eq_kstep_lt15 (needEfgh : Bool) (s : KState) (i : Nat) (hi : i < 15) :
    stepLane needEfgh s i = kstep s i := by
  simp [stepLane, kstep, hi]

/-- For `needEfgh = true`, `stepLane true` is identical to `kstep` for all `i`. -/
private theorem stepLane_true_eq_kstep (s : KState) (i : Nat) :
    stepLane true s i = kstep s i := by
  simp [stepLane, kstep]

/-- For step 15, `stepLane needEfgh` produces the exact same `abcd` as `kstep`. -/
private theorem stepLane_abcd_eq_kstep (needEfgh : Bool) (s : KState) (i : Nat) :
    (stepLane needEfgh s i).abcd = (kstep s i).abcd := by
  simp [stepLane, kstep]

/-- Key algebraic equivalence: running `makeHead` (rounds 0..3) followed by
`finishFromR4`'s deferred step 1 (`w16` and `w20` computed after `a2, e2`)
produces the exact same `KState` as the first two standard steps `kstep · 0`
and `kstep · 1` of `kcompress`. -/
theorem deferred_step01_eq_kstep01 (st : List Word) (B : Spec.Bytes) :
    let (m0, a1, e1) := makeHead st B
    let m1 := beV B 16
    let m2 := beV B 32
    let m3 := beV B 48
    let w1 := Arm.ADD m1 (vOf K 4)
    let a2 := Arm.SHA256H a1 e1 w1
    let e2 := Arm.SHA256H2 e1 a1 w1
    let w16 := Arm.SHA256SU1 (Arm.SHA256SU0 m0 m1) m2 m3
    let w20 := Arm.SHA256SU1 (Arm.SHA256SU0 m1 m2) m3 w16
    (⟨a2, e2, [w16, w20, m2, m3]⟩ : KState) =
      kstep (kstep ⟨vOf st 0, vOf st 4, [beV B 0, beV B 16, beV B 32, beV B 48]⟩ 0) 1 := by
  simp [makeHead, kstep]

private theorem foldl_range16_split (f : KState → Nat → KState) (s0 : KState) :
    (List.range 16).foldl f s0 =
      [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15].foldl f (f (f s0 0) 1) := by
  rfl

private theorem foldl_steps2_14_eq (needEfgh : Bool) (s2 : KState) :
    [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14].foldl (stepLane needEfgh) s2 =
      [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14].foldl kstep s2 := by
  simp [stepLane, kstep]

/-- **Main theorem (`NEED_EFGH = true`)**:
`make_head` (rounds 0..3) followed by `finish_from_r4<L, true>` (rounds 4..63 with
deferred schedule) computes the exact 8-word FIPS 180-4 `Spec.SHA256.compress`. -/
theorem finishFromR4_true_eq_compress (st : List Word) (hst : st.length = 8)
    (B : Spec.Bytes) (hB : B.length = 64) :
    let (m0, a1, e1) := makeHead st B
    let (abcd, efgh) := finishFromR4 true st a1 e1 m0 (beV B 16) (beV B 32) (beV B 48)
    vwords abcd ++ vwords efgh = compress st B := by
  dsimp only [finishFromR4]
  have h01 := deferred_step01_eq_kstep01 st B
  dsimp only at h01
  have hsteps : ∀ s, [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15].foldl (stepLane true) s =
      [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15].foldl kstep s := by
    intro s
    simp only [List.foldl_cons, List.foldl_nil, stepLane_true_eq_kstep]
  rw [hsteps, h01]
  have hcomp := kcompress_eq st hst B hB
  simp only [kcompress, foldl_range16_split] at hcomp
  exact hcomp

/-- **Main theorem (`NEED_EFGH = false`, SLH-DSA-128 fast path)**:
`make_head` (rounds 0..3) followed by `finish_from_r4<L, false>` (skipping `efgh`
on step 15 and in feed-forward) computes the exact first 4 words (`16` bytes) of
FIPS 180-4 `Spec.SHA256.compress`. -/
theorem finishFromR4_false_eq_compress_take4 (st : List Word) (hst : st.length = 8)
    (B : Spec.Bytes) (hB : B.length = 64) :
    let (m0, a1, e1) := makeHead st B
    let (abcd, _) := finishFromR4 false st a1 e1 m0 (beV B 16) (beV B 32) (beV B 48)
    vwords abcd = (compress st B).take 4 := by
  dsimp only [finishFromR4]
  have h01 := deferred_step01_eq_kstep01 st B
  dsimp only at h01
  have hsplit : ∀ (f : KState → Nat → KState) (s : KState),
      [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15].foldl f s =
        f ([2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14].foldl f s) 15 := by
    intro f s; rfl
  rw [hsplit (stepLane false), foldl_steps2_14_eq false, h01, stepLane_abcd_eq_kstep]
  have hcomp := kcompress_eq st hst B hB
  simp only [kcompress, foldl_range16_split, hsplit kstep] at hcomp
  rw [← hcomp]
  simp [vwords]

/-- **`compress_block_lanes` (`NEED_EFGH = true`)**:
All 16 steps + feed-forward compute exact FIPS 180-4 `Spec.SHA256.compress`. -/
theorem compressBlockLane_true_eq_compress (st : List Word) (hst : st.length = 8)
    (B : Spec.Bytes) (hB : B.length = 64) :
    let (abcd, efgh) := compressBlockLane true st B
    vwords abcd ++ vwords efgh = compress st B := by
  dsimp only [compressBlockLane]
  have hfold : ∀ (l : List Nat) (s : KState), l.foldl (stepLane true) s = l.foldl kstep s := by
    intro l
    induction l with
    | nil => intro s; rfl
    | cons x xs ih =>
      intro s; simp only [List.foldl_cons, stepLane_true_eq_kstep, ih]
  rw [hfold]
  exact kcompress_eq st hst B hB

/-- **`compress_block_lanes` (`NEED_EFGH = false`)**:
All 16 steps (skipping `efgh` on step 15) + feed-forward compute the exact first
4 words of FIPS 180-4 `Spec.SHA256.compress`. -/
theorem compressBlockLane_false_eq_compress_take4 (st : List Word) (hst : st.length = 8)
    (B : Spec.Bytes) (hB : B.length = 64) :
    let (abcd, _) := compressBlockLane false st B
    vwords abcd = (compress st B).take 4 := by
  dsimp only [compressBlockLane]
  have h15 : (List.range 16).foldl (stepLane false)
      ⟨vOf st 0, vOf st 4, [beV B 0, beV B 16, beV B 32, beV B 48]⟩ =
      stepLane false ((List.range 15).foldl (stepLane false)
        ⟨vOf st 0, vOf st 4, [beV B 0, beV B 16, beV B 32, beV B 48]⟩) 15 := by
    rw [show (16 : Nat) = 15 + 1 by rfl, List.range_succ, List.foldl_append]
    rfl
  have hlt15 : ∀ n, n ≤ 15 → ∀ s, (List.range n).foldl (stepLane false) s = (List.range n).foldl kstep s := by
    intro n hn
    induction n with
    | zero => intro s; rfl
    | succ n ih =>
      intro s
      rw [List.range_succ, List.foldl_append, List.foldl_append, ih (by omega)]
      simp only [List.foldl_cons, List.foldl_nil, stepLane_eq_kstep_lt15 false _ n (by omega)]
  rw [h15, hlt15 15 le_rfl, stepLane_abcd_eq_kstep]
  have hcomp := kcompress_eq st hst B hB
  have h16k : kcompress (vOf st 0) (vOf st 4) (beV B 0) (beV B 16) (beV B 32) (beV B 48) =
      kstep ((List.range 15).foldl kstep ⟨vOf st 0, vOf st 4, [beV B 0, beV B 16, beV B 32, beV B 48]⟩) 15 := by
    unfold kcompress
    rw [show (16 : Nat) = 15 + 1 by rfl, List.range_succ, List.foldl_append]
    rfl
  rw [h16k] at hcomp
  rw [← hcomp]
  simp [vwords]

/-! ## Big-endian serialization (`store_n` / `vrev32q_u8`) -/

/-- `Arm.beBytes w` equals `Spec.toByte w.toNat 4` (FIPS 180-4 big-endian word encoding). -/
theorem beBytes_eq_toByte (w : Word) : Arm.beBytes w = Spec.toByte w.toNat 4 := by
  have hbyte : ∀ k, (w.extractLsb' (8 * k) 8) = BitVec.ofNat 8 (w.toNat >>> (8 * k)) := by
    intro k
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.extractLsb']
  have hr4 : List.range 4 = [0, 1, 2, 3] := rfl
  simp only [Arm.beBytes, Spec.toByte, hr4, List.map_cons, List.map_nil]
  change [w.extractLsb' (8 * 3) 8, w.extractLsb' (8 * 2) 8, w.extractLsb' (8 * 1) 8, w.extractLsb' (8 * 0) 8] = _
  rw [hbyte 3, hbyte 2, hbyte 1, hbyte 0]

/-- `store_n` model: `vrev32q_u8` on `abcd` (16 bytes), followed by 0, 8, or 16 bytes
of `vrev32q_u8` on `efgh` for `N ∈ {16, 24, 32}`. -/
def storeN (N : Nat) (abcd efgh : Arm.V) : Spec.Bytes :=
  let lo := (vwords abcd).flatMap Arm.beBytes
  let hi := (vwords efgh).flatMap Arm.beBytes
  if N = 16 then lo
  else if N = 24 then lo ++ hi.take 8
  else lo ++ hi

/-- **`store_n` matches FIPS 180-4 big-endian truncation** for `N ∈ {16, 24, 32}`:
combining `makeHead` + `finishFromR4` (`needEfgh = (N != 16)`) + `storeN N`
produces the exact first `N` bytes of FIPS 180-4 `Spec.SHA256.compress`! -/
theorem finishFromR4_storeN_eq_fips (N : Nat) (hN : N = 16 ∨ N = 24 ∨ N = 32)
    (st : List Word) (hst : st.length = 8) (B : Spec.Bytes) (hB : B.length = 64) :
    let (m0, a1, e1) := makeHead st B
    let (abcd, efgh) := finishFromR4 (N != 16) st a1 e1 m0 (beV B 16) (beV B 32) (beV B 48)
    storeN N abcd efgh = ((compress st B).flatMap fun w => Spec.toByte w.toNat 4).take N := by
  have hflat : ∀ ws : List Word, ws.flatMap Arm.beBytes = ws.flatMap fun w => Spec.toByte w.toNat 4 := by
    intro ws
    induction ws with
    | nil => rfl
    | cons w ws ih => simp [beBytes_eq_toByte, ih]
  rcases hN with rfl | rfl | rfl
  · dsimp only [storeN]
    simp only [bne_self_eq_false, ↓reduceIte]
    have h4 := finishFromR4_false_eq_compress_take4 st hst B hB
    dsimp only at h4 ⊢
    rw [h4, hflat]
    have hlen : (compress st B).length = 8 := by simp [compress]
    rcases hcomp : compress st B with _ | ⟨w0, _ | ⟨w1, _ | ⟨w2, _ | ⟨w3, ws⟩⟩⟩⟩
    · simp [hcomp] at hlen
    · simp [hcomp] at hlen
    · simp [hcomp] at hlen
    · simp [hcomp] at hlen
    · have hlen4 : ∀ w : Word, (Spec.toByte w.toNat 4).length = 4 := fun _ => by simp [Spec.toByte]
      simp only [List.take_succ_cons, List.take_zero, List.flatMap_cons, List.flatMap_nil,
        List.append_nil]
      set a := Spec.toByte w0.toNat 4
      set b := Spec.toByte w1.toNat 4
      set c := Spec.toByte w2.toNat 4
      set d := Spec.toByte w3.toNat 4
      have habcd : (a ++ b ++ c ++ d).length = 16 := by simp [a, b, c, d, hlen4]
      rw [show a ++ (b ++ (c ++ (d ++ List.flatMap (fun w => Spec.toByte (BitVec.toNat w) 4) ws))) =
          (a ++ b ++ c ++ d) ++ List.flatMap (fun w => Spec.toByte (BitVec.toNat w) 4) ws by
          simp [List.append_assoc],
        List.take_append_of_le_length (by omega),
        List.take_of_length_le (by omega)]
      simp [List.append_assoc]
  · dsimp only [storeN]
    simp only [show (24 != 16) = true by decide, show (24 : Nat) ≠ 16 by decide, ↓reduceIte]
    have h8 := finishFromR4_true_eq_compress st hst B hB
    dsimp only at h8 ⊢
    rw [← h8, List.flatMap_append, ← hflat, ← hflat]
    have h16 : ∀ v : Arm.V, ((vwords v).flatMap Arm.beBytes).length = 16 :=
      fun _ => by simp [vwords, Arm.beBytes]
    generalize (finishFromR4 true st (makeHead st B).2.1 (makeHead st B).2.2
      (makeHead st B).1 (beV B 16) (beV B 32) (beV B 48)).1 = abcd
    generalize (finishFromR4 true st (makeHead st B).2.1 (makeHead st B).2.2
      (makeHead st B).1 (beV B 16) (beV B 32) (beV B 48)).2 = efgh
    rw [List.take_append]
    rw [List.take_of_length_le (l := (vwords abcd).flatMap Arm.beBytes) (by rw [h16]; omega), h16]
  · dsimp only [storeN]
    simp only [show (32 != 16) = true by decide, show (32 : Nat) ≠ 16 by decide,
      show (32 : Nat) ≠ 24 by decide, ↓reduceIte]
    have h8 := finishFromR4_true_eq_compress st hst B hB
    dsimp only at h8 ⊢
    rw [← h8, List.flatMap_append, ← hflat, ← hflat]
    rw [List.take_of_length_le (by simp [vwords, Arm.beBytes])]

#print axioms deferred_step01_eq_kstep01
#print axioms finishFromR4_true_eq_compress
#print axioms finishFromR4_false_eq_compress_take4
#print axioms compressBlockLane_true_eq_compress
#print axioms compressBlockLane_false_eq_compress_take4
#print axioms finishFromR4_storeN_eq_fips

end slhdsa.Armwide.Kernel
