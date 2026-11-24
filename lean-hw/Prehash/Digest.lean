import Prehashdigest.Funs
import Spec.PreHash
import Slhdsa.Proofs.Shake256
import Slhdsa.Proofs.Sha256
import Slhdsa.Proofs.Sha512
import Slhdsa.Proofs.Slh
import Slhdsa.Proofs.ShakeSlh
import Mathlib.Tactic.IntervalCases

open Aeneas Aeneas.Std Result
open slhdsa

namespace slhdsa.prehash.digest

open PrehashDigestRust

/-! ## Bridging views between extracted Rust types and FIPS 205 specification -/

/-- Specification-level view of `PrehashDigestRust.prehash.PreHash`. -/
def preHashS : PrehashDigestRust.prehash.PreHash → Spec.PreHash.PreHash
  | .Sha256   => .sha256
  | .Sha512   => .sha512
  | .Shake128 => .shake128
  | .Shake256 => .shake256

/-- Specification-level parameter set for `(family, p)`. -/
def familyParams (family : cache.HashFamily) (p : PrehashDigestRust.params.Params) : Spec.Params :=
  match family with
  | .Sha2  => paramsS (toSlhParams p)
  | .Shake => Shake.params (toSlhParams p)

/-! ## Keccak-f[1600] equivalence and SHAKE128 proof (FIPS 202 §6.2) -/

private theorem rho_pi_eq : PrehashDigestRust.prehash.rho_pi = slhdsa.shake256.rho_pi := rfl
private theorem chi_eq : PrehashDigestRust.prehash.chi = slhdsa.shake256.chi := rfl
private theorem round_loop0_eq :
    PrehashDigestRust.prehash.round_loop0 = slhdsa.shake256.round_loop0 := rfl
private theorem round_loop1_eq :
    PrehashDigestRust.prehash.round_loop1 = slhdsa.shake256.round_loop1 := rfl
private theorem round_eq : PrehashDigestRust.prehash.round = slhdsa.shake256.round := by
  funext a rc
  unfold PrehashDigestRust.prehash.round slhdsa.shake256.round
  rw [round_loop0_eq, round_loop1_eq, rho_pi_eq, chi_eq]

private theorem rc_eq : PrehashDigestRust.prehash.RC = slhdsa.shake256.RC := by
  simp only [PrehashDigestRust.prehash.RC, slhdsa.shake256.RC]

theorem keccak_f1600_portable_eq :
    PrehashDigestRust.prehash.keccak_f1600_portable = slhdsa.shake256.permute := by
  funext s
  unfold PrehashDigestRust.prehash.keccak_f1600_portable
    PrehashDigestRust.prehash.keccak_f1600_portable_loop
    PrehashDigestRust.prehash.keccak_f1600_portable_loop.body
    slhdsa.shake256.permute slhdsa.shake256.permute_loop slhdsa.shake256.permute_loop.body
  simp only [rc_eq, round_eq]

@[step]
theorem keccak_f1600_spec (a : Array U64 25#usize) :
    PrehashDigestRust.prehash.keccak_f1600 a
      ⦃ out => Keccak.words out = Spec.Keccak.permute (Keccak.words a) ⦄ := by
  unfold PrehashDigestRust.prehash.keccak_f1600
  rw [keccak_f1600_portable_eq]
  exact Keccak.permute_spec a

private theorem words_set {n : Usize} (a : Array U64 n) (i : Usize) (v : U64) :
    Keccak.words (a.set i v) = (Keccak.words a).setIfInBounds i.val v.bv := by
  apply _root_.Array.ext
  · simp [Keccak.words]
  · intro j h1 h2
    simp only [Keccak.words, Array.set_val_eq, List.getElem_toArray, List.getElem_map,
      List.getElem_set]
    split <;> simp_all

private theorem from_le_bytes_eight (b0 b1 b2 b3 b4 b5 b6 b7 : U8) :
    (core.num.U64.from_le_bytes (Array.make 8#usize [b0, b1, b2, b3, b4, b5, b6, b7])).bv =
      Spec.Keccak.laneBytes 0 [b0.bv, b1.bv, b2.bv, b3.bv, b4.bv, b5.bv, b6.bv, b7.bv] := by
  change (BitVec.fromLEBytes [b0.bv, b1.bv, b2.bv, b3.bv, b4.bv, b5.bv, b6.bv, b7.bv]).cast
      (by rfl) = _
  simp only [BitVec.fromLEBytes, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul,
    BitVec.cast_eq, Spec.Keccak.laneBytes]
  ext i hi
  interval_cases i <;>
    simp [BitVec.getElem_or, BitVec.getElem_shiftLeft, BitVec.getElem_setWidth, BitVec.getElem_xor]

private theorem drop_eight_eq {α : Type} (l : List α) (i : Nat) (h : i + 8 ≤ l.length) :
    l.drop i =
      [l[i], l[i + 1], l[i + 2], l[i + 3], l[i + 4], l[i + 5], l[i + 6], l[i + 7]] ++
        l.drop (i + 8) := by
  have step (k : Nat) (hk : k < l.length) : l.drop k = l[k] :: l.drop (k + 1) :=
    (List.getElem_cons_drop hk).symm
  rw [step i (by omega), step (i + 1) (by omega), step (i + 2) (by omega),
    step (i + 3) (by omega), step (i + 4) (by omega), step (i + 5) (by omega),
    step (i + 6) (by omega), step (i + 7) (by omega)]
  rfl

set_option maxHeartbeats 2000000 in
private theorem shake128_loop0_spec (input : Slice U8) (lanes : Array U64 25#usize)
    (pos i : Usize) (hi : i.val ≤ input.length) (hpos : pos.val < 168) (hal : pos.val % 8 = 0) :
    PrehashDigestRust.prehash.shake128_loop0 input lanes pos i ⦃ r =>
      r.2.2.val ≤ input.length ∧ r.2.1.val < 168 ∧
      ((bytes input.val).drop r.2.2.val).foldl Spec.PreHash.feed128 (Keccak.words r.1, r.2.1.val) =
        ((bytes input.val).drop i.val).foldl Spec.PreHash.feed128 (Keccak.words lanes, pos.val) ⦄ := by
  let target :=
    ((bytes input.val).drop i.val).foldl Spec.PreHash.feed128 (Keccak.words lanes, pos.val)
  unfold PrehashDigestRust.prehash.shake128_loop0
  apply loop.spec_decr_nat
    (measure := fun (p : Array U64 25#usize × Usize × Usize) => input.length - p.2.2.val)
    (inv := fun p => p.2.2.val ≤ input.length ∧ p.2.1.val < 168 ∧ p.2.1.val % 8 = 0 ∧
      ((bytes input.val).drop p.2.2.val).foldl Spec.PreHash.feed128 (Keccak.words p.1, p.2.1.val) =
        target)
  · rintro ⟨st, p, k⟩ ⟨hk, hp, hmod, acc⟩
    simp only at hk hp hmod acc
    simp only [PrehashDigestRust.prehash.shake128_loop0.body, step_simps]
    step as ⟨i2, hi2⟩
    spec_split
    · step as ⟨i3, hi3⟩
      spec_split
      · have hk8 : k.val + 8 ≤ input.val.length := by scalar_tac
        have hlen : k.val + 8 ≤ (bytes input.val).length := by simpa using hk8
        step as ⟨b0, hb0⟩
        step as ⟨k1, hk1⟩
        step as ⟨b1, hb1⟩
        step as ⟨k2, hk2⟩
        step as ⟨b2, hb2⟩
        step as ⟨k3, hk3⟩
        step as ⟨b3, hb3⟩
        step as ⟨k4, hk4⟩
        step as ⟨b4, hb4⟩
        step as ⟨k5, hk5⟩
        step as ⟨b5, hb5⟩
        step as ⟨k6, hk6⟩
        step as ⟨b6, hb6⟩
        step as ⟨k7, hk7⟩
        step as ⟨b7, hb7⟩
        step as ⟨word, hword_def⟩
        step as ⟨idx, hidx⟩
        step as ⟨cur, hcur⟩
        step as ⟨xored, hxored_val, hxored_bv⟩
        step as ⟨_, back, _, hback⟩
        step as ⟨pos1, hpos1⟩
        step as ⟨k8, hk8'⟩
        have hdrop := drop_eight_eq (bytes input.val) k.val hlen
        rw [hdrop, List.foldl_append] at acc
        have hlane : p.val = 8 * (p.val / 8) := by omega
        have hrate : p.val / 8 < 21 := by omega
        have hval25 : p.val / 8 < (Keccak.words st).size := by simp [Keccak.words]; omega
        have h8 : ([ (bytes input.val)[k.val], (bytes input.val)[k.val + 1],
            (bytes input.val)[k.val + 2], (bytes input.val)[k.val + 3],
            (bytes input.val)[k.val + 4], (bytes input.val)[k.val + 5],
            (bytes input.val)[k.val + 6], (bytes input.val)[k.val + 7] ]).length = 8 := rfl
        have hfw := Spec.PreHash.feedWord128 (Keccak.words st) (p.val / 8) _ h8 hval25 hrate
        rw [← hlane] at hfw
        rw [hfw] at acc
        have hword : word.bv = Spec.Keccak.laneBytes 0
            [ (bytes input.val)[k.val], (bytes input.val)[k.val + 1],
              (bytes input.val)[k.val + 2], (bytes input.val)[k.val + 3],
              (bytes input.val)[k.val + 4], (bytes input.val)[k.val + 5],
              (bytes input.val)[k.val + 6], (bytes input.val)[k.val + 7] ] := by
          have hfl := from_le_bytes_eight b0 b1 b2 b3 b4 b5 b6 b7
          have hwbv : word.bv =
              (core.num.U64.from_le_bytes (Array.make 8#usize [b0, b1, b2, b3, b4, b5, b6, b7])).bv := by
            rw [hword_def]; rfl
          rw [hwbv, hfl]
          simp only [bytes, List.getElem_map, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7,
            hk1, hk2, hk3, hk4, hk5, hk6, hk7]
        have hnext : Keccak.words (back xored) =
            (Keccak.words st).setIfInBounds (p.val / 8)
              ((Keccak.words st)[p.val / 8]! ^^^ word.bv) := by
          rw [hback, words_set]
          simp only [hidx, hxored_bv, hcur,
            Keccak.words_get st (p.val / 8) (by change p.val / 8 < 25; omega)]
        by_cases hbound : pos1 = PrehashDigestRust.prehash.RATE_SHAKE128
        · simp only [hbound, ↓reduceIte]
          have hp168 : p.val + 8 = 168 := by
            rw [← hpos1, hbound]; simp [PrehashDigestRust.prehash.RATE_SHAKE128]
          have h20 : p.val / 8 = 20 := by omega
          have hilen : input.length = input.val.length := rfl
          step with keccak_f1600_spec as ⟨lanes2, hlanes2⟩
          refine ⟨by omega, by decide, by decide, ?_, by omega⟩
          simp only [h20, ↓reduceIte] at acc
          change ((bytes input.val).drop k8.val).foldl Spec.PreHash.feed128 (Keccak.words lanes2, 0) = target
          rw [hlanes2, hnext, hword]
          simpa only [hk8', h20] using acc
        · simp only [hbound, ↓reduceIte, step_simps]
          have hpne : p.val + 8 ≠ 168 := by
            intro bad; apply hbound; apply UScalar.eq_of_val_eq
            rw [hpos1, bad]; simp [PrehashDigestRust.prehash.RATE_SHAKE128]
          have hne20 : p.val / 8 ≠ 20 := by omega
          have hilen : input.length = input.val.length := rfl
          simp only [hne20, ↓reduceIte] at acc
          refine ⟨by omega, by omega, by omega, ?_, by omega⟩
          rw [hnext, hword]
          simpa only [hk8', hpos1, ← hlane] using acc
      · simp only [step_simps]; exact ⟨hk, hp, acc⟩
    · simp only [step_simps]; exact ⟨hk, hp, acc⟩
  · exact ⟨hi, hpos, hal, rfl⟩

private theorem shake128_loop1_spec (input : Slice U8) (lanes : Array U64 25#usize)
    (pos i : Usize) (hi : i.val ≤ input.length) (hpos : pos.val < 168) :
    PrehashDigestRust.prehash.shake128_loop1 input lanes pos i ⦃ r =>
      (Keccak.words r.1, r.2.val) =
        ((bytes input.val).drop i.val).foldl Spec.PreHash.feed128 (Keccak.words lanes, pos.val) ∧
      r.2.val < 168 ⦄ := by
  let target :=
    ((bytes input.val).drop i.val).foldl Spec.PreHash.feed128 (Keccak.words lanes, pos.val)
  unfold PrehashDigestRust.prehash.shake128_loop1
  apply loop.spec_decr_nat
    (measure := fun (p : Array U64 25#usize × Usize × Usize) => input.length - p.2.2.val)
    (inv := fun p => p.2.2.val ≤ input.length ∧ p.2.1.val < 168 ∧
      ((bytes input.val).drop p.2.2.val).foldl Spec.PreHash.feed128 (Keccak.words p.1, p.2.1.val) =
        target)
  · rintro ⟨st, p, k⟩ ⟨hk, hp, acc⟩
    simp only at hk hp acc
    simp only [PrehashDigestRust.prehash.shake128_loop1.body, step_simps]
    spec_split
    · have hkd : k.val < input.val.length := by scalar_tac
      rw [← List.getElem_cons_drop (show k.val < (bytes input.val).length by simpa),
        List.foldl_cons] at acc
      simp only [bytes, List.getElem_map] at acc
      step as ⟨i2, hi2⟩
      step as ⟨i3, hi3⟩
      step as ⟨i4, hi4⟩
      step as ⟨i5, hi5⟩
      step as ⟨i6, hi6_val, hi6_bv⟩
      step as ⟨i7, hi7⟩
      step as ⟨i8, hi8⟩
      step as ⟨i9, hi9_val, hi9_bv⟩
      step as ⟨_, back, _, hback⟩
      step as ⟨pos1, hpos1⟩
      have inLane : Keccak.words (back i9) =
          Spec.Keccak.xorByte (Keccak.words st) p.val (input.val[k.val]).bv := by
        rw [hback, words_set, Spec.Keccak.xorByte]
        simp only [hi7, hi9_bv, hi8, hi6_bv, hi3, hi2, hi5, hi4,
          UScalar.cast_bv_eq, Keccak.words_get st (p.val / 8) (by scalar_tac)]
        rfl
      by_cases boundary : pos1 = PrehashDigestRust.prehash.RATE_SHAKE128
      · simp only [boundary, ↓reduceIte]
        step with keccak_f1600_spec as ⟨lanes3, hlanes3⟩
        step as ⟨k1, hk1⟩
        have he : p.val + 1 = 168 := by
          rw [← hpos1, boundary]; simp [PrehashDigestRust.prehash.RATE_SHAKE128]
        refine ⟨by scalar_tac, by decide, ?_, by scalar_tac⟩
        rw [hk1]
        have hstep : (Keccak.words lanes3, (0#usize).val) =
            Spec.PreHash.feed128 (Keccak.words st, p.val) (input.val[k.val]).bv := by
          simp only [Spec.PreHash.feed128, he, ↓reduceIte, hlanes3, inLane]; rfl
        simpa only [hstep, bytes] using acc
      · simp only [boundary, ↓reduceIte, bind_ok]
        step as ⟨k1, hk1⟩
        have he : p.val + 1 ≠ 168 := by
          intro bad; apply boundary; apply UScalar.eq_of_val_eq
          rw [hpos1, bad]; simp [PrehashDigestRust.prehash.RATE_SHAKE128]
        refine ⟨by scalar_tac, by scalar_tac, ?_, by scalar_tac⟩
        rw [hk1]
        have hstep : (Keccak.words (back i9), pos1.val) =
            Spec.PreHash.feed128 (Keccak.words st, p.val) (input.val[k.val]).bv := by
          simp [Spec.PreHash.feed128, inLane, hpos1, he]
        simpa only [hstep, bytes] using acc
    · simp only [step_simps]
      have endAt : k.val = input.val.length := by scalar_tac
      have stop : (bytes input.val).drop k.val = [] := List.drop_eq_nil_of_le (by simp [endAt])
      simpa only [stop, List.foldl_nil, target] using And.intro acc hp
  · exact ⟨hi, hpos, rfl⟩

private theorem put_prefix (out : Slice U8) (i : Usize) (x : U8) (hi : i.val < out.length) :
    bytes ((out.set i x).val.take (i.val + 1)) = bytes (out.val.take i.val) ++ [x.bv] := by
  rw [Slice.set_val_eq, List.take_succ_eq_append_getElem (by simpa),
    List.take_set_of_le (le_refl i.val), List.getElem_set_self]
  simp

private def emits128 (a : Array U64 25#usize) (out : Slice U8) (pos i : Nat) : Spec.Bytes :=
  bytes (out.val.take i) ++ Spec.PreHash.squeeze128 (Keccak.words a) pos (out.length - i)

private theorem emit128_step (block a : Array U64 25#usize) (buf : Slice U8)
    (pos atPos idx : Usize) (byte : U8) (valid : idx.val < buf.length)
    (next : (Keccak.words block, atPos.val) =
      (if pos.val = 168 then (Spec.Keccak.permute (Keccak.words a), 0)
       else (Keccak.words a, pos.val)))
    (byteEq : byte.bv = Spec.Keccak.extractByte (Keccak.words block) atPos.val) :
    emits128 block (buf.set idx byte) (atPos.val + 1) (idx.val + 1) =
      emits128 a buf pos.val idx.val := by
  unfold emits128
  rw [put_prefix _ _ _ valid]
  have count : buf.length - idx.val = (buf.length - (idx.val + 1)) + 1 := by omega
  rw [count, Spec.PreHash.squeeze128, ← next]
  simp [byteEq, Slice.length]

private theorem shake128_loop2_spec (initial : Array U64 25#usize) (out : Slice U8) :
    PrehashDigestRust.prehash.shake128_loop2 out initial 0#usize 0#usize ⦃ r =>
      bytes r.val = Spec.PreHash.squeeze128 (Keccak.words initial) 0 out.length ⦄ := by
  let target := Spec.PreHash.squeeze128 (Keccak.words initial) 0 out.length
  unfold PrehashDigestRust.prehash.shake128_loop2
  apply loop.spec_decr_nat
    (measure := fun (p : Slice U8 × Array U64 25#usize × Usize × Usize) => out.length - p.2.2.2.val)
    (inv := fun p => p.1.length = out.length ∧ p.2.2.2.val ≤ out.length ∧
      p.2.2.1.val ≤ 168 ∧ emits128 p.2.1 p.1 p.2.2.1.val p.2.2.2.val = target)
  · rintro ⟨buf, a, pos, idx⟩ ⟨len, bound, rate, acc⟩
    simp only at len bound rate acc
    simp only [PrehashDigestRust.prehash.shake128_loop2.body, step_simps]
    spec_split
    · have valid : idx.val < buf.length := by scalar_tac
      have run : (if pos = PrehashDigestRust.prehash.RATE_SHAKE128 then do
          let a' ← PrehashDigestRust.prehash.keccak_f1600 a
          ok (a', 0#usize) else ok (a, pos)) ⦃ pair =>
          pair.2.val < 168 ∧ (Keccak.words pair.1, pair.2.val) =
            (if pos.val = 168 then (Spec.Keccak.permute (Keccak.words a), 0)
             else (Keccak.words a, pos.val)) ⦄ := by
        by_cases atEnd : pos = PrehashDigestRust.prehash.RATE_SHAKE128
        · subst pos; simp only [↓reduceIte]; step*; simp [PrehashDigestRust.prehash.RATE_SHAKE128, *]
        · have endNe : pos.val ≠ 168 := by
            intro he; apply atEnd; apply UScalar.eq_of_val_eq
            simp [he, PrehashDigestRust.prehash.RATE_SHAKE128]
          simp [atEnd, endNe]; omega
      let* ⟨block, atPos, fits, next⟩ ← run
      step*
      refine ⟨by scalar_tac, by scalar_tac, by scalar_tac, ?_, by scalar_tac⟩
      rw [s_post, out_pos2_post, out_i1_post, ← acc]
      apply emit128_step _ _ _ _ _ _ _ valid next
      simp only [Spec.Keccak.extractByte, Keccak.words_get block (atPos.val / 8) (by scalar_tac),
        *, UScalar.cast_bv_eq]
      rfl
    · simp only [step_simps]
      have doneAt : idx.val = buf.length := by scalar_tac
      simpa [emits128, doneAt, Spec.PreHash.squeeze128, Slice.length, target] using acc
  · simp [emits128, target]

/-- Extracted Rust `prehash::shake128` computes FIPS 202 `Spec.PreHash.shake128` for
arbitrary input slices and arbitrary output buffer lengths. -/
@[step]
theorem shake128_spec (input output : Slice U8) :
    PrehashDigestRust.prehash.shake128 input output ⦃ r =>
      bytes r.val = Spec.PreHash.shake128 (bytes input.val) output.length ⦄ := by
  unfold PrehashDigestRust.prehash.shake128
  let* ⟨lanes1, pos, i, hi, hpos, h0⟩ ←
    shake128_loop0_spec input (Array.repeat 25#usize 0#u64) 0#usize 0#usize
      (by simp) (by decide) (by decide)
  let* ⟨lanes2, pos1, h1, hpos1⟩ ← shake128_loop1_spec input lanes1 pos i hi hpos
  simp only [PrehashDigestRust.prehash.RATE_SHAKE128]
  step*
  apply WP.spec_mono (shake128_loop2_spec lanes5 output)
  intro r hr
  rw [hr, lanes5_post, Spec.PreHash.shake128]
  congr 2
  have hinit : (Keccak.words (Array.repeat 25#usize 0#u64), 0) = Spec.Keccak.initial := by
    simp [Keccak.words, Spec.Keccak.initial, Array.repeat_val]
    rfl
  have habsorb : (Keccak.words lanes2, pos1.val) =
      (bytes input.val).foldl Spec.PreHash.feed128 Spec.Keccak.initial := by
    rw [h1, h0]
    simp only [List.drop_zero, hinit]
  rw [← habsorb]
  simp only
  have ha : Keccak.words lanes3 = Spec.Keccak.xorByte (Keccak.words lanes2) pos1.val 31 := by
    rw [lanes3_post, words_set, Spec.Keccak.xorByte]
    simp only [*, Keccak.words_get lanes2 (pos1.val / 8) (by scalar_tac)]
    rfl
  have addr : i9.val = 20 := by scalar_tac
  rw [lanes4_post, words_set, ← ha, Spec.Keccak.xorByte]
  simp only [addr, Keccak.words_get lanes3 20 (by decide), i11_post1, i10_post, i7_post1]
  rfl

/-! ## `PreHash::hash_stack` and `PreHash::hash` (`digest_spec`) -/

/-- Sufficient length room for pre-hashing across all four FIPS 205 pre-hash functions. -/
def HashRoom (ph : PrehashDigestRust.prehash.PreHash) (len : Nat) : Prop :=
  match ph with
  | .Sha256   => Room len 72
  | .Sha512   => len + 144 ≤ Usize.max
  | .Shake128 => True
  | .Shake256 => True

theorem hashRoom_of_room (ph : PrehashDigestRust.prehash.PreHash) (len : Nat)
    (h : Room len 144) : HashRoom ph len := by
  unfold Room at h
  cases ph
  · exact ⟨by omega, by omega⟩
  · exact h.1
  · trivial
  · trivial

private theorem setSlice_zero_take {α : Type} (l s : List α) (h : s.length ≤ l.length) :
    (l.setSlice! 0 s).take s.length = s := by
  simp only [List.setSlice!, Nat.sub_zero, List.take_zero, List.nil_append,
    show min s.length l.length = s.length by omega, List.take_of_length_le (le_refl _)]
  exact List.take_left' rfl

@[step]
theorem hash_stack_spec (ph : PrehashDigestRust.prehash.PreHash) (m : Slice U8)
    (hm : HashRoom ph m.length) :
    PrehashDigestRust.prehash.PreHash.hash_stack ph m ⦃ r =>
      r.2.val = (preHashS ph).digestLen ∧
      bytes (r.1.val.take r.2.val) = Spec.PreHash.prehashDigest (preHashS ph) (bytes m.val) ⦄ := by
  unfold PrehashDigestRust.prehash.PreHash.hash_stack
  cases ph
  · -- Sha256
    simp only [preHashS, Spec.PreHash.PreHash.digestLen, Spec.PreHash.prehashDigest]
    have hrm : Room m.length 72 := hm
    step with slhdsa.sha256_spec m hrm as ⟨d, hd⟩
    step*
    refine ⟨rfl, ?_⟩
    rw [s_post2, s2_post, s1_post, Array.val_to_slice]
    have h32 : d.val.length = 32 := by simp
    have htake : ((Array.repeat 64#usize 0#u8).val.setSlice! 0 d.val).take 32 = d.val := by
      simpa [h32] using setSlice_zero_take (Array.repeat 64#usize 0#u8).val d.val (by simp)
    change bytes (((Array.repeat 64#usize 0#u8).val.setSlice! 0 d.val).take 32) = _
    rw [htake, hd]
  · -- Sha512
    simp only [preHashS, Spec.PreHash.PreHash.digestLen, Spec.PreHash.prehashDigest]
    have hrm : m.length + 144 ≤ Usize.max := hm
    step with slhdsa.sha512_spec m hrm as ⟨d, hd⟩
    step*
    refine ⟨rfl, ?_⟩
    rw [to_slice_mut_back_post, s2_post, s1_post]
    have hfrom : ((Array.repeat 64#usize 0#u8).from_slice d.to_slice).val = d.val := by
      simp [Array.from_slice, Array.to_slice]
    rw [hfrom, List.take_of_length_le (by simp), hd]
  · -- Shake128
    simp only [preHashS, Spec.PreHash.PreHash.digestLen, Spec.PreHash.prehashDigest]
    step*
    refine ⟨rfl, ?_⟩
    rw [s_post2]
    have hs1len : s1.val.length = 32 := by
      have := congrArg List.length s1_post
      simp at this; scalar_tac
    have htake : ((Array.repeat 64#usize 0#u8).val.setSlice! 0 s1.val).take 32 = s1.val := by
      simpa [hs1len] using setSlice_zero_take (Array.repeat 64#usize 0#u8).val s1.val (by simp [hs1len])
    change bytes (((Array.repeat 64#usize 0#u8).val.setSlice! 0 s1.val).take 32) = _
    rw [htake, s1_post]
    simp [s_post1]
  · -- Shake256
    simp only [preHashS, Spec.PreHash.PreHash.digestLen, Spec.PreHash.prehashDigest]
    step as ⟨s, back, hs, hslen, hback⟩
    step with slhdsa.Keccak.shake256_spec m s as ⟨s1, hs1⟩
    refine ⟨rfl, ?_⟩
    rw [hback]
    have hs1len : s1.val.length = 64 := by
      have := congrArg List.length hs1
      simp [hslen] at this; exact this
    have htake : ((Array.repeat 64#usize 0#u8).val.setSlice! 0 s1.val).take 64 = s1.val := by
      simpa [hs1len] using setSlice_zero_take (Array.repeat 64#usize 0#u8).val s1.val (by simp [hs1len])
    change bytes (((Array.repeat 64#usize 0#u8).val.setSlice! 0 s1.val).take 64) = _
    rw [htake, hs1]
    simp [hslen]

/-- Extracted Rust `PreHash::hash` computes the exact FIPS 205 pre-hash digest `PH(m)`
for all four approved pre-hash algorithms (`Sha256`, `Sha512`, `Shake128`, `Shake256`). -/
@[step]
theorem digest_spec (ph : PrehashDigestRust.prehash.PreHash) (m : Slice U8)
    (hm : HashRoom ph m.length) :
    PrehashDigestRust.prehash.PreHash.hash ph m ⦃ out =>
      bytes out.val = Spec.PreHash.prehashDigest (preHashS ph) (bytes m.val) ⦄ := by
  unfold PrehashDigestRust.prehash.PreHash.hash
  step with hash_stack_spec ph m hm as ⟨buf, len, hlen, hbytes⟩
  have hle : len.val ≤ 64 := by rw [hlen]; cases ph <;> decide
  step as ⟨out, _, hout_len⟩
  simp only [lift, bind_ok, alloc.vec.Vec.deref_mut]
  step as ⟨s1, hs1, hs1_len⟩
  step as ⟨s2, hs2⟩
  · simp only [Slice.length, hs1_len]; exact hout_len
  simp only [hs2]
  change bytes s1.val = _
  rw [hs1, List.slice]
  simpa using hbytes

/-! ## OID, digest length, and `format_prehash_message` framing -/

@[step]
theorem oid_spec (ph : PrehashDigestRust.prehash.PreHash) :
    PrehashDigestRust.prehash.PreHash.oid_der ph ⦃ r => bytes r.val = (preHashS ph).oid ⦄ := by
  cases ph <;> simp [PrehashDigestRust.prehash.PreHash.oid_der, preHashS,
    Spec.PreHash.PreHash.oid, PrehashDigestRust.prehash.OID_SHA256,
    PrehashDigestRust.prehash.OID_SHA512, PrehashDigestRust.prehash.OID_SHAKE128,
    PrehashDigestRust.prehash.OID_SHAKE256, bytes]

@[step]
theorem digest_len_spec (ph : PrehashDigestRust.prehash.PreHash) :
    PrehashDigestRust.prehash.PreHash.digest_len ph ⦃ r => r.val = (preHashS ph).digestLen ⦄ := by
  cases ph <;> simp [PrehashDigestRust.prehash.PreHash.digest_len, preHashS,
    Spec.PreHash.PreHash.digestLen]

private theorem setSlice_gen {α : Type} (pre suf s : List α) (i : Nat)
    (hpre : pre.length = i) (hs : s.length ≤ suf.length) :
    (pre ++ suf).setSlice! i s = (pre ++ s) ++ suf.drop s.length := by
  subst i
  simp [List.setSlice!, hs, List.append_assoc]

private theorem setSlice_prefix {α : Type} (l : List α) (a b c : List α) (hd : List α)
    (hlen : l.length = 332) (ha : a.length ≤ 255) (hb : b.length = 11) (hc : c.length ≤ 64)
    (hhd : hd.length = 2) (hpre : l.take 2 = hd) :
    (((l.setSlice! 2 a).setSlice! (2 + a.length) b).setSlice! (2 + a.length + 11) c).take
      (2 + a.length + 11 + c.length) = hd ++ a ++ b ++ c := by
  have h1 : l = hd ++ l.drop 2 := by rw [← hpre, List.take_append_drop]
  have hdrop : (l.drop 2).length = 330 := by simp [hlen]
  rw [h1, setSlice_gen hd (l.drop 2) a 2 hhd (by omega)]
  have h2len : (hd ++ a).length = 2 + a.length := by simp [hhd]
  rw [setSlice_gen (hd ++ a) ((l.drop 2).drop a.length) b (2 + a.length) h2len
    (by simp [hlen]; omega)]
  have h3len : (hd ++ a ++ b).length = 2 + a.length + 11 := by simp [hhd, hb]; omega
  rw [setSlice_gen (hd ++ a ++ b) (((l.drop 2).drop a.length).drop b.length) c
      (2 + a.length + 11) h3len (by simp [hlen, hb]; omega)]
  have h4len : (hd ++ a ++ b ++ c).length = 2 + a.length + 11 + c.length := by
    simp [hhd, hb]; omega
  exact List.take_left' h4len

@[step]
theorem format_prehash_message_spec (ctx : Slice U8) (ph : PrehashDigestRust.prehash.PreHash)
    (digest : Slice U8) :
    PrehashDigestRust.prehash.format_prehash_message ctx ph digest ⦃ r =>
      if ctx.length > 255 ∨ digest.length ≠ (preHashS ph).digestLen then r = none
      else ∃ mp len, r = some (mp, len) ∧
        len.val = 2 + ctx.length + 11 + digest.length ∧
        len.val ≤ 332 ∧
        bytes (mp.val.take len.val) =
          Spec.PreHash.prehashFrame (bytes ctx.val) (preHashS ph) (bytes digest.val) ⦄ := by
  unfold PrehashDigestRust.prehash.format_prehash_message
  by_cases hctx : ctx.length > 255
  · have hc : (Slice.len ctx) > 255#usize := by scalar_tac
    simp only [hc, ↓reduceIte, hctx, true_or, step_simps]
  · have hc : ¬ ((Slice.len ctx) > 255#usize) := by scalar_tac
    simp only [hc, ↓reduceIte, hctx, false_or]
    let* ⟨dlen, hdlen⟩ ← digest_len_spec ph
    by_cases hdig : digest.length ≠ (preHashS ph).digestLen
    · have hne : (Slice.len digest != dlen) = true := by
        simp only [bne_iff_ne, ne_eq]
        intro h; apply hdig
        rw [← hdlen]; exact congrArg UScalar.val h
      simp [hne, hdig]
    · have heq : digest.length = (preHashS ph).digestLen := Classical.not_not.mp hdig
      have hdeq : Slice.len digest = dlen :=
        UScalar.eq_of_val_eq (by rw [hdlen]; exact heq)
      have hne : (Slice.len digest != dlen) = false := by simp [hdeq]
      have hdl_le : digest.length ≤ 64 := by
        rw [heq]; cases ph <;> decide
      simp only [hne, Bool.false_eq_true, ↓reduceIte]
      let* ⟨oid, hoid⟩ ← oid_spec ph
      step*
      all_goals try scalar_tac
      simp only [hdig, ↓reduceIte]
      refine ⟨index_mut_back2 s9, total, rfl, by scalar_tac, by scalar_tac, ?_⟩
      have hmp2_len : mp2.val.length = 332 := by simp
      have hmp2_take : mp2.val.take 2 = [1#u8, i9] := by
        rw [mp2_post, Array.set_val_eq, mp1_post, Array.set_val_eq, Array.repeat_val]
        rfl
      have hmp5 : (index_mut_back2 s9).val =
          (((mp2.val.setSlice! 2 ctx.val).setSlice! (2 + ctx.length) oid.val).setSlice!
            (2 + ctx.length + 11) digest.val) := by
        rw [s8_post2, s4_post2, s1_post2, s9_post, s6_post, s5_post, s2_post,
          Array.val_to_slice]
        simp only [off1_post, off_post, s7_post, Slice.length]
        have hcl : ctx.len.val = ctx.val.length := rfl
        have hol : oid.to_slice.len.val = 11 := by simp [Slice.len, Array.to_slice]
        rw [hcl, hol]
      have htot : total.val = 2 + ctx.length + 11 + digest.length := by scalar_tac
      have hctx_le : ctx.val.length ≤ 255 := by scalar_tac
      rw [hmp5, htot]
      have htake := setSlice_prefix mp2.val ctx.val oid.val digest.val [1#u8, i9]
        hmp2_len hctx_le (by simp) hdl_le rfl hmp2_take
      simp only [Slice.length] at htake ⊢
      rw [htake]
      simp only [bytes_append, hoid, Spec.PreHash.prehashFrame_eq_cons, bytes_cons, bytes_nil]
      congr 5
      apply BitVec.eq_of_toNat_eq
      simp [i9_post]

/-! ## Algorithms 23 & 25 (`hash_slh_sign_prehashed`, `hash_slh_verify_prehashed`,
    `hash_slh_sign`, `hash_slh_verify`) -/

private theorem room_mp {N : Usize} (p : PrehashDigestRust.params.Params)
    (hp : PN (toSlhParams p) N) {len : Nat} (hlen : len ≤ 332) : Room len (msgSlack N.val) := by
  have hn := hp.le32
  have hu : 4294967295 ≤ Usize.max := by
    rcases Usize.bounds_eq with h | h <;> rw [h] <;> scalar_tac
  have hsl : msgSlack N.val ≤ 304 := by unfold msgSlack; split <;> omega
  exact ⟨by omega, by omega⟩

/-- Extracted Rust `prehash::hash_slh_sign_prehashed` implements FIPS 205 Algorithm 23
(pre-hashed mode) for both SHA-2 and SHAKE families and all 12 parameter sets. -/
theorem hash_slh_sign_prehashed_spec {N : Usize} (family : cache.HashFamily)
    (p : PrehashDigestRust.params.Params)
    (hp : PN (toSlhParams p) N) (digest ctx : Slice U8)
    (ph : PrehashDigestRust.prehash.PreHash)
    (sk : Slice U8) (addrnd : Array U8 N) (hsk : sk.length = 4 * N.val) :
    PrehashDigestRust.prehash.hash_slh_sign_prehashed family p digest ctx ph sk addrnd ⦃ r =>
      r.map (fun v => bytes v.val) =
        Spec.PreHash.hashSlhSignPrehashed (familyParams family p)
          (bytes digest.val) (bytes ctx.val) (preHashS ph) (bytes sk.val) (bytes addrnd.val) ⦄ := by
  unfold PrehashDigestRust.prehash.hash_slh_sign_prehashed
  step with format_prehash_message_spec ctx ph digest as ⟨o, ho⟩
  by_cases hbad : ctx.length > 255 ∨ digest.length ≠ (preHashS ph).digestLen
  · simp only [hbad, ↓reduceIte] at ho
    subst o
    simp only [Spec.PreHash.hashSlhSignPrehashed, bytes_length, hbad, ↓reduceIte, step_simps,
      Option.map_none]
  · simp only [hbad, ↓reduceIte] at ho
    obtain ⟨mp, len, rfl, hlen, hle, hbytes⟩ := ho
    simp only [Spec.PreHash.hashSlhSignPrehashed, bytes_length, hbad, ↓reduceIte]
    cases family
    · -- SHA-2
      simp only [familyParams]
      step as ⟨s, hs, hslen⟩
      have hsb : bytes s.val =
          Spec.PreHash.prehashFrame (bytes ctx.val) (preHashS ph) (bytes digest.val) := by
        rw [hs, List.slice]; simpa using hbytes
      have hrm : Room s.length (msgSlack N.val) := room_mp p hp (by rw [hslen]; omega)
      step with slhdsa.slh_sign_internal_spec (toSlhParams p) hp s sk addrnd hsk hrm as ⟨sig, hsig, _⟩
      simp [hsig, hsb]
    · -- SHAKE
      simp only [familyParams]
      step as ⟨s, hs, hslen⟩
      have hsb : bytes s.val =
          Spec.PreHash.prehashFrame (bytes ctx.val) (preHashS ph) (bytes digest.val) := by
        rw [hs, List.slice]; simpa using hbytes
      step with slhdsa.Shake.slh_sign_internal_all_lengths (toSlhParams p) hp s sk addrnd hsk
        as ⟨sig, hsig, _⟩
      simp [hsig, hsb]

/-- Extracted Rust `prehash::hash_slh_verify_prehashed` implements FIPS 205 Algorithm 25
(pre-hashed mode) for both SHA-2 and SHAKE families and all 12 parameter sets. -/
theorem hash_slh_verify_prehashed_spec (N : Usize) (family : cache.HashFamily)
    (p : PrehashDigestRust.params.Params)
    (hp : PN (toSlhParams p) N) (digest sig ctx : Slice U8)
    (ph : PrehashDigestRust.prehash.PreHash)
    (pk : Slice U8) (hpk : pk.length = 2 * N.val) :
    PrehashDigestRust.prehash.hash_slh_verify_prehashed N family p digest sig ctx ph pk ⦃ b =>
      b = Spec.PreHash.hashSlhVerifyPrehashed (familyParams family p)
          (bytes digest.val) (bytes sig.val) (bytes ctx.val) (preHashS ph) (bytes pk.val) ⦄ := by
  unfold PrehashDigestRust.prehash.hash_slh_verify_prehashed
  step with format_prehash_message_spec ctx ph digest as ⟨o, ho⟩
  by_cases hbad : ctx.length > 255 ∨ digest.length ≠ (preHashS ph).digestLen
  · simp only [hbad, ↓reduceIte] at ho
    subst o
    simp only [Spec.PreHash.hashSlhVerifyPrehashed, bytes_length, hbad, ↓reduceIte, step_simps]
  · simp only [hbad, ↓reduceIte] at ho
    obtain ⟨mp, len, rfl, hlen, hle, hbytes⟩ := ho
    simp only [Spec.PreHash.hashSlhVerifyPrehashed, bytes_length, hbad, ↓reduceIte]
    cases family
    · -- SHA-2
      simp only [familyParams]
      step as ⟨s, hs, hslen⟩
      have hsb : bytes s.val =
          Spec.PreHash.prehashFrame (bytes ctx.val) (preHashS ph) (bytes digest.val) := by
        rw [hs, List.slice]; simpa using hbytes
      have hrm : Room s.length (msgSlack N.val) := room_mp p hp (by rw [hslen]; omega)
      step with slhdsa.slh_verify_internal_spec (toSlhParams p) hp s sig pk hpk hrm as ⟨b, hb⟩
      rw [hb, hsb]
    · -- SHAKE
      simp only [familyParams]
      step as ⟨s, hs, hslen⟩
      have hsb : bytes s.val =
          Spec.PreHash.prehashFrame (bytes ctx.val) (preHashS ph) (bytes digest.val) := by
        rw [hs, List.slice]; simpa using hbytes
      step with slhdsa.Shake.slh_verify_internal_all_lengths (toSlhParams p) hp s sig pk hpk
        as ⟨b, hb⟩
      rw [hb, hsb]

/-- Extracted Rust `prehash::hash_slh_sign` implements FIPS 205 Algorithm 23
for both SHA-2 and SHAKE families, all 4 pre-hash functions, and all 12 parameter sets. -/
theorem hash_slh_sign_spec {N : Usize} (family : cache.HashFamily)
    (p : PrehashDigestRust.params.Params)
    (hp : PN (toSlhParams p) N) (m ctx : Slice U8)
    (ph : PrehashDigestRust.prehash.PreHash)
    (sk : Slice U8) (addrnd : Array U8 N) (hsk : sk.length = 4 * N.val)
    (hm : HashRoom ph m.length) :
    PrehashDigestRust.prehash.hash_slh_sign family p m ctx ph sk addrnd ⦃ r =>
      r.map (fun v => bytes v.val) =
        Spec.PreHash.hashSlhSign (familyParams family p)
          (bytes m.val) (bytes ctx.val) (preHashS ph) (bytes sk.val) (bytes addrnd.val) ⦄ := by
  unfold PrehashDigestRust.prehash.hash_slh_sign
  by_cases hctx : ctx.length > 255
  · have hc : (Slice.len ctx) > 255#usize := by scalar_tac
    simp only [hc, ↓reduceIte, Spec.PreHash.hashSlhSign, bytes_length, hctx, step_simps,
      Option.map_none]
  · have hc : ¬ ((Slice.len ctx) > 255#usize) := by scalar_tac
    simp only [hc, ↓reduceIte, Spec.PreHash.hashSlhSign, bytes_length, hctx]
    step with hash_stack_spec ph m hm as ⟨digest, dlen, hdlen, hbytes⟩
    have hdle : dlen.val ≤ 64 := by rw [hdlen]; cases ph <;> decide
    step as ⟨s, hs, hslen⟩
    have hsb : bytes s.val = Spec.PreHash.prehashDigest (preHashS ph) (bytes m.val) := by
      rw [hs, List.slice]; simpa using hbytes
    step with hash_slh_sign_prehashed_spec family p hp s ctx ph sk addrnd hsk as ⟨r, hr⟩
    rw [hr, hsb]

/-- Extracted Rust `prehash::hash_slh_verify` implements FIPS 205 Algorithm 25
for both SHA-2 and SHAKE families, all 4 pre-hash functions, and all 12 parameter sets. -/
theorem hash_slh_verify_spec (N : Usize) (family : cache.HashFamily)
    (p : PrehashDigestRust.params.Params)
    (hp : PN (toSlhParams p) N) (m sig ctx : Slice U8)
    (ph : PrehashDigestRust.prehash.PreHash)
    (pk : Slice U8) (hpk : pk.length = 2 * N.val) (hm : HashRoom ph m.length) :
    PrehashDigestRust.prehash.hash_slh_verify N family p m sig ctx ph pk ⦃ b =>
      b = Spec.PreHash.hashSlhVerify (familyParams family p)
          (bytes m.val) (bytes sig.val) (bytes ctx.val) (preHashS ph) (bytes pk.val) ⦄ := by
  unfold PrehashDigestRust.prehash.hash_slh_verify
  by_cases hctx : ctx.length > 255
  · have hc : (Slice.len ctx) > 255#usize := by scalar_tac
    simp only [hc, ↓reduceIte, Spec.PreHash.hashSlhVerify, bytes_length, hctx, step_simps]
  · have hc : ¬ ((Slice.len ctx) > 255#usize) := by scalar_tac
    simp only [hc, ↓reduceIte, Spec.PreHash.hashSlhVerify, bytes_length, hctx]
    step with hash_stack_spec ph m hm as ⟨digest, dlen, hdlen, hbytes⟩
    have hdle : dlen.val ≤ 64 := by rw [hdlen]; cases ph <;> decide
    step as ⟨s, hs, hslen⟩
    have hsb : bytes s.val = Spec.PreHash.prehashDigest (preHashS ph) (bytes m.val) := by
      rw [hs, List.slice]; simpa using hbytes
    step with hash_slh_verify_prehashed_spec N family p hp s sig ctx ph pk hpk as ⟨b, hb⟩
    rw [hb, hsb]

/-- End-to-end completeness of the extracted Rust HashSLH-DSA sign & verify pair:
for any well-formed key, context `|ctx| ≤ 255`, message `m`, and pre-hash algorithm `ph`,
signing succeeds and `hash_slh_verify` returns `true`. -/
theorem hash_slh_complete_rust {N : Usize} (family : cache.HashFamily)
    (p : PrehashDigestRust.params.Params)
    (hp : PN (toSlhParams p) N) (m ctx sk pk : Slice U8)
    (ph : PrehashDigestRust.prehash.PreHash)
    (addrnd : Array U8 N)
    (hsk : sk.length = 4 * N.val) (hpk : pk.length = 2 * N.val)
    (hpk_eq : bytes pk.val = Spec.skPk (familyParams family p) (bytes sk.val))
    (hk : Spec.KeyOk (familyParams family p) (bytes sk.val))
    (hc : ctx.length ≤ 255) (hm : HashRoom ph m.length) :
    ∃ sig, PrehashDigestRust.prehash.hash_slh_sign family p m ctx ph sk addrnd = ok (some sig) ∧
      PrehashDigestRust.prehash.hash_slh_verify N family p m (alloc.vec.Vec.deref sig) ctx ph pk =
        ok true := by
  have hv : (familyParams family p).Valid := by
    cases family
    · exact hp.valid
    · exact ⟨hp.valid.n_cases, hp.valid.lgw_eq, hp.valid.d_ge, hp.valid.d_le, hp.valid.hp_pos,
        hp.valid.hp_le, hp.valid.h_eq, hp.valid.tree_le, hp.valid.a_pos, hp.valid.a_le,
        hp.valid.k_pos, hp.valid.k_le, hp.valid.m_eq⟩
  obtain ⟨r, hr_eq, hr_spec⟩ :=
    spec_imp_exists (hash_slh_sign_spec family p hp m ctx ph sk addrnd hsk hm)
  obtain ⟨spec_sig, hspec_sign, hspec_ver⟩ :=
    Spec.PreHash.hashSlh_complete (familyParams family p) hv (bytes m.val) (bytes ctx.val)
      (bytes sk.val) (bytes addrnd.val) (preHashS ph) (by simpa using hc) hk
  rw [hspec_sign] at hr_spec
  cases r with
  | none => simp at hr_spec
  | some sig =>
    simp only [Option.map_some, Option.some.injEq] at hr_spec
    obtain ⟨b, hb_eq, hb_spec⟩ :=
      spec_imp_exists (hash_slh_verify_spec N family p hp m (alloc.vec.Vec.deref sig) ctx ph pk
        hpk hm)
    have hb_true : b = true := by
      rw [hb_spec, vec_deref_val, hr_spec, hpk_eq, hspec_ver]
    subst hb_true
    exact ⟨sig, hr_eq, hb_eq⟩

end slhdsa.prehash.digest
