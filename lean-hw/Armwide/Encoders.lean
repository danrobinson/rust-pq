import Armwide.Funs
import Spec.SlhDsa

open Aeneas Aeneas.Std Result

/-!
# Verified ARM64 SHA-256 / SHA-512 Stack Encoders (`Armwide.Encoders`)

Proofs of the Aeneas-extracted pure-Rust stack encoders used by the ARMv8
SHA-256/SHA-512 backends (`rust/src/wots/arm.rs`, `rust/src/fors/arm.rs`,
`rust/src/xmss/arm.rs`, and `rust/src/sha512/paired.rs`):

- `wots_digits_stack_spec`: `wots::arm::wots_digits_stack` matches FIPS 205
  `Spec.wotsDigits` (message base-16 nibbles + 3 checksum nibbles) for
  `N ∈ {16, 24, 32}`.
- `base_2b_stack_spec` / `base_2b_stack_valid_params`: `fors::arm::base_2b_stack`
  matches FIPS 205 `Spec.base2b` for all valid `(a, k)` geometries.
- `prepare_tlen_spec` / `prepare_tlen_sha256_pad` / `prepare_tlen_sha512_pad`:
  `xmss::arm::prepare_tlen` writes the exact FIPS 205 `WOTS_PK` compressed address,
  `0x80` delimiter, and big-endian bit-length trailer for `N ∈ {16, 24, 32}`.
- `parent_block_512_spec`: `sha512::paired::parent_block_512` builds the exact
  FIPS 180-4 / FIPS 205 padded second SHA-512 block for `N ∈ {24, 32}`.
-/

namespace slhdsa.Armwide

def bytes (l : List U8) : Spec.Bytes := l.map (·.bv)
def nats (l : List U32) : List Nat := l.map (·.val)

def adrsS (a : address.Adrs) : Spec.Adrs :=
  ⟨a.layer.val, a.tree.val, a.typ.val, a.keypair.val, a.word2.val, a.word3.val⟩

@[simp] theorem bytes_length (l : List U8) : (bytes l).length = l.length := by simp [bytes]
@[simp] theorem bytes_append (a b : List U8) : bytes (a ++ b) = bytes a ++ bytes b := by simp [bytes]
@[simp] theorem bytes_cons (x : U8) (l : List U8) : bytes (x :: l) = x.bv :: bytes l := by simp [bytes]
@[simp] theorem bytes_nil : bytes [] = [] := rfl
@[simp] theorem bytes_replicate (k : Nat) (x : U8) :
    bytes (List.replicate k x) = List.replicate k x.bv := by simp [bytes]
@[simp] theorem bytes_take (k : Nat) (l : List U8) : bytes (l.take k) = (bytes l).take k := by
  simp [bytes, List.map_take]
@[simp] theorem bytes_drop (k : Nat) (l : List U8) : bytes (l.drop k) = (bytes l).drop k := by
  simp [bytes, List.map_drop]
@[simp] theorem nats_length (l : List U32) : (nats l).length = l.length := by simp [nats]
@[simp] theorem nats_append (a b : List U32) : nats (a ++ b) = nats a ++ nats b := by simp [nats]
@[simp] theorem nats_cons (x : U32) (l : List U32) : nats (x :: l) = x.val :: nats l := by simp [nats]
@[simp] theorem nats_nil : nats [] = [] := rfl

private theorem bytes_getElem! (l : List U8) (i : Nat) (h : i < l.length) :
    (bytes l)[i]! = (l[i]!).bv := by
  simp [bytes, List.getElem!_eq_getElem?_getD, h]

/-! ## Address helpers -/

@[step]
theorem with_type_spec (a : address.Adrs) (x : U32) :
    address.Adrs.with_type a x ⦃ r => adrsS r = (adrsS a).setTypeAndClear x.val ∧
      r = { a with typ := x, keypair := 0#u32, word2 := 0#u32, word3 := 0#u32 } ⦄ := by
  unfold address.Adrs.with_type
  simp [adrsS, Spec.Adrs.setTypeAndClear]

@[step]
theorem with_keypair_spec (a : address.Adrs) (x : U32) :
    address.Adrs.with_keypair a x ⦃ r => r = { a with keypair := x } ⦄ := by
  unfold address.Adrs.with_keypair
  simp

private theorem compress_eq (x : Spec.Adrs) :
    x.compress = [BitVec.ofNat 8 x.layer,
      BitVec.ofNat 8 (x.tree >>> 56), BitVec.ofNat 8 (x.tree >>> 48),
      BitVec.ofNat 8 (x.tree >>> 40), BitVec.ofNat 8 (x.tree >>> 32),
      BitVec.ofNat 8 (x.tree >>> 24), BitVec.ofNat 8 (x.tree >>> 16),
      BitVec.ofNat 8 (x.tree >>> 8), BitVec.ofNat 8 x.tree,
      BitVec.ofNat 8 x.typ,
      BitVec.ofNat 8 (x.keypair >>> 24), BitVec.ofNat 8 (x.keypair >>> 16),
      BitVec.ofNat 8 (x.keypair >>> 8), BitVec.ofNat 8 x.keypair,
      BitVec.ofNat 8 (x.word2 >>> 24), BitVec.ofNat 8 (x.word2 >>> 16),
      BitVec.ofNat 8 (x.word2 >>> 8), BitVec.ofNat 8 x.word2,
      BitVec.ofNat 8 (x.word3 >>> 24), BitVec.ofNat 8 (x.word3 >>> 16),
      BitVec.ofNat 8 (x.word3 >>> 8), BitVec.ofNat 8 x.word3] := rfl

private theorem setWidth_shr64 (x : U64) (k : Nat) :
    BitVec.setWidth 8 (x.bv >>> k) = BitVec.ofNat 8 (x.val >>> k) := by
  rw [← U64.bv_toNat, ← BitVec.toNat_ushiftRight, BitVec.ofNat_toNat]

private theorem setWidth_shr32 (x : U32) (k : Nat) :
    BitVec.setWidth 8 (x.bv >>> k) = BitVec.ofNat 8 (x.val >>> k) := by
  rw [← U32.bv_toNat, ← BitVec.toNat_ushiftRight, BitVec.ofNat_toNat]

@[step]
theorem adrs_compress_spec (a : address.Adrs) :
    address.Adrs.compress a ⦃ r => bytes r.val = (adrsS a).compress ⦄ := by
  unfold address.Adrs.compress
  step*
  rw [compress_eq]
  simp [bytes, adrsS, setWidth_shr64, setWidth_shr32, *]

/-! ## `fors::arm::base_2b_stack` -/

private theorem fill_step (xs : Spec.Bytes) (b inp bits T : Nat) (h : bits < b) :
    Spec.base2bFill xs b inp bits T =
      Spec.base2bFill xs b (inp + 1) (bits + 8) ((T <<< 8) + xs[inp]!.toNat) := by
  conv_lhs => rw [Spec.base2bFill]
  simp [h]

private theorem fill_done (xs : Spec.Bytes) (b inp bits T : Nat) (h : ¬ bits < b) :
    Spec.base2bFill xs b inp bits T = (inp, bits, T) := by
  rw [Spec.base2bFill]
  simp [h]

private theorem go_succ (xs : Spec.Bytes) (b n inp bits T inp' bits' T' : Nat)
    (hf : Spec.base2bFill xs b inp bits T = (inp', bits', T')) :
    Spec.base2bGo xs b (n + 1) inp bits T =
      (T' >>> (bits' - b)) % 2 ^ b :: Spec.base2bGo xs b n inp' (bits' - b) T' := by
  simp [Spec.base2bGo, hf]

private theorem digit_eq (T s b t : Nat) (ht : t = T % 2 ^ 32) (hs : s + b ≤ 32) :
    (t >>> s) &&& (2 ^ b - 1) = (T >>> s) % 2 ^ b := by
  subst ht
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
  have h32 : 2 ^ 32 = 2 ^ s * 2 ^ (32 - s) := by rw [← Nat.pow_add]; congr 1; omega
  rw [h32, Nat.mod_mul_right_div_self]
  exact Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))

private theorem shl8_add_lt (t : U32) (b : U8) :
    (t.bv <<< 8).toNat + b.val < 2 ^ 32 := by
  have hb : b.val < 256 := b.hBounds
  have hmod : (t.bv <<< 8).toNat % 256 = 0 := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, show (2 : Nat) ^ 8 = 256 by rfl]
    omega
  have hlt : (t.bv <<< 8).toNat < 2 ^ 32 := (t.bv <<< 8).isLt
  omega

private theorem shl8_add_eq32 (t : U32) (b : U8) (T : Nat) (ht : t.val = T % 2 ^ 32) :
    (t.bv <<< 8).toNat + b.val = ((T <<< 8) + b.val) % 2 ^ 32 := by
  have hlt := shl8_add_lt t b
  rw [BitVec.toNat_shiftLeft, show t.bv.toNat = t.val from rfl, ht, Nat.shiftLeft_eq] at hlt ⊢
  rw [Nat.shiftLeft_eq]
  have h1 : (T % 2 ^ 32 * 2 ^ 8) % 2 ^ 32 = (T * 2 ^ 8) % 2 ^ 32 := by
    rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
  rw [h1] at hlt ⊢
  have h2 : ((T * 2 ^ 8) % 2 ^ 32 + b.val) % 2 ^ 32 = (T * 2 ^ 8 + b.val) % 2 ^ 32 := by
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
  rw [← h2, Nat.mod_eq_of_lt hlt]

private theorem base_2b_stack_inner_spec (md : Slice U8) (b : U32) (inp : Usize) (bits total : U32)
    (T c : Nat) (hb : 1 ≤ b.val ∧ b.val ≤ 16) (hbits : bits.val < b.val + 8)
    (ht : total.val = T % 2 ^ 32) (hc : 8 * inp.val = c + bits.val)
    (hroom : c + b.val ≤ 8 * md.length) :
    fors.arm.base_2b_stack_loop0_loop0 md b inp bits total ⦃ r => ∃ T',
      Spec.base2bFill (bytes md.val) b.val inp.val bits.val T = (r.1.val, r.2.1.val, T') ∧
      r.2.2.val = T' % 2 ^ 32 ∧ 8 * r.1.val = c + r.2.1.val ∧
      b.val ≤ r.2.1.val ∧ r.2.1.val < b.val + 8 ⦄ := by
  unfold fors.arm.base_2b_stack_loop0_loop0
  apply loop.spec_decr_nat (measure := fun (p : Usize × U32 × U32) => b.val - p.2.1.val)
    (inv := fun p => ∃ T',
      Spec.base2bFill (bytes md.val) b.val inp.val bits.val T =
        Spec.base2bFill (bytes md.val) b.val p.1.val p.2.1.val T' ∧
      p.2.2.val = T' % 2 ^ 32 ∧ 8 * p.1.val = c + p.2.1.val ∧ p.2.1.val < b.val + 8)
  · rintro ⟨inp, bits, total⟩ ⟨T', hf, ht, hc, hbits⟩
    simp only [fors.arm.base_2b_stack_loop0_loop0.body]
    simp only at hf ht hc hbits
    spec_split
    · have hlt : inp.val < md.val.length := by scalar_tac
      have hbl : bits.val < b.val := by scalar_tac
      let* ⟨ i, i_post1, i_post ⟩ ← U32.ShiftLeft_IScalar_spec
      let* ⟨ i1, i1_post ⟩ ← Slice.index_usize_spec
      let* ⟨ i2, i2_post ⟩ ← UScalar.cast.step_spec
      have hi_bv : i.val = (total.bv <<< 8).toNat := by
        rw [← UScalar.bv_toNat, i_post]
      have hi2_val : i2.val = i1.val := by simp [i2_post]
      have hadd : i.val + i2.val ≤ U32.max := by
        have := shl8_add_lt total i1
        rw [hi_bv, hi2_val]
        scalar_tac
      let* ⟨ total1, total1_post ⟩ ← U32.add_spec
      let* ⟨ inp1, inp1_post ⟩ ← Usize.add_spec
      let* ⟨ bits1, bits1_post ⟩ ← U32.add_spec
      refine ⟨⟨(T' <<< 8) + ((md.val)[inp.val]).bv.toNat, ?_, ?_, by scalar_tac, by scalar_tac⟩,
        by scalar_tac⟩
      · rw [hf, fill_step _ _ _ _ _ hbl, bytes_getElem! _ _ hlt, inp1_post, bits1_post]
        simp [hlt]
      · have h1 : total1.val = (total.bv <<< 8).toNat + i1.val := by
          rw [total1_post, hi_bv, hi2_val]
        rw [h1, shl8_add_eq32 total i1 T' ht, i1_post]
        rfl
    · simp only [step_simps]
      have hbl : ¬ bits.val < b.val := by scalar_tac
      exact ⟨T', by rw [hf, fill_done _ _ _ _ _ hbl], ht, hc, by scalar_tac, hbits⟩
  · exact ⟨T, rfl, ht, hc, hbits⟩

private theorem take_set_at {α} (l : List α) (i : Nat) (x : α) (hi : i < l.length) :
    (l.set i x).take (i + 1) = l.take i ++ [x] := by
  apply List.ext_getElem
  · simp [Nat.min_eq_left (Nat.succ_le_of_lt hi), Nat.min_eq_left (Nat.le_of_lt hi)]
  · intro j hj1 hj2
    have hjl : j ≤ i := by simp at hj1; omega
    rcases Nat.lt_or_eq_of_le hjl with hlt | rfl
    · rw [List.getElem_take, List.getElem_set_ne (by omega), List.getElem_append_left (by simp; omega),
        List.getElem_take]
    · rw [List.getElem_take, List.getElem_set_self, List.getElem_append_right (by simp)]
      simp [Nat.min_eq_left (Nat.le_of_lt hi)]

private theorem base_2b_stack_loop_spec (md : Slice U8) (b : U32) (out_len : Usize)
    (out : Array U32 35#usize) (inp : Usize) (bits total mask : U32) (i : Usize) (T : Nat)
    (hb : 1 ≤ b.val ∧ b.val ≤ 16) (hout : out_len.val ≤ 35)
    (hx : out_len.val * b.val ≤ 8 * md.length)
    (hmask : mask.val = 2 ^ b.val - 1)
    (ht : total.val = T % 2 ^ 32) (hc : 8 * inp.val = i.val * b.val + bits.val)
    (hbits : bits.val ≤ 7) (hi : i.val ≤ out_len.val)
    (hbound : ∀ j < i.val, (out.val[j]!).val < 2 ^ b.val) :
    fors.arm.base_2b_stack_loop0 md b out_len out inp bits total mask i ⦃ r =>
      nats (r.val.take out_len.val) = nats (out.val.take i.val) ++
        Spec.base2bGo (bytes md.val) b.val (out_len.val - i.val) inp.val bits.val T ∧
      ∀ j < out_len.val, (r.val[j]!).val < 2 ^ b.val ⦄ := by
  unfold fors.arm.base_2b_stack_loop0
  apply loop.spec_decr_nat
    (measure := fun (p : Array U32 35#usize × Usize × U32 × U32 × Usize) => out_len.val - p.2.2.2.2.val)
    (inv := fun p => ∃ T', p.2.2.2.1.val = T' % 2 ^ 32 ∧
      8 * p.2.1.val = p.2.2.2.2.val * b.val + p.2.2.1.val ∧ p.2.2.1.val ≤ 7 ∧
      p.2.2.2.2.val ≤ out_len.val ∧
      (∀ j < p.2.2.2.2.val, (p.1.val[j]!).val < 2 ^ b.val) ∧
      nats (p.1.val.take p.2.2.2.2.val) ++
        Spec.base2bGo (bytes md.val) b.val (out_len.val - p.2.2.2.2.val) p.2.1.val p.2.2.1.val T' =
      nats (out.val.take i.val) ++
        Spec.base2bGo (bytes md.val) b.val (out_len.val - i.val) inp.val bits.val T)
  · rintro ⟨out', inp', bits', total', i'⟩ ⟨T', ht, hc, hbits, hi, hbound, hgo⟩
    simp only [fors.arm.base_2b_stack_loop0.body]
    simp only at ht hc hbits hi hbound hgo
    spec_split
    · have hroom : i'.val * b.val + b.val ≤ 8 * md.length := by
        have h1 : (i'.val + 1) * b.val ≤ out_len.val * b.val :=
          Nat.mul_le_mul_right _ (by scalar_tac)
        rw [Nat.add_mul] at h1
        omega
      have hin := base_2b_stack_inner_spec md b inp' bits' total' T' (i'.val * b.val) hb
        (by scalar_tac) ht hc hroom
      step with hin
      let* ⟨ bits2, bits2_post, bits2_post1 ⟩ ← U32.sub_spec
      let* ⟨ i1, i1_post, i1_post1 ⟩ ← U32.ShiftRight_spec
      let* ⟨ i2, i2_post, i2_post1 ⟩ ← UScalar.and_spec
      let* ⟨ a, a_post ⟩ ← Array.update_spec
      let* ⟨ i3, i3_post ⟩ ← Usize.add_spec
      have hpos : 0 < 2 ^ b.val := Nat.pow_pos (by omega)
      have hd : i2.val = (T' >>> bits2.val) % 2 ^ b.val := by
        rw [i2_post, UScalar.val_and, i1_post, hmask]
        exact digit_eq T' bits2.val b.val total1.val inp1_post1 (by scalar_tac)
      have hn : out_len.val - i'.val = (out_len.val - i3.val) + 1 := by scalar_tac
      have hmul : i3.val * b.val = i'.val * b.val + b.val := by
        rw [i3_post, Nat.add_mul, Nat.one_mul]
      have ha_val : a.val = out'.val.set i'.val i2 := by rw [a_post, Array.set_val_eq]
      have hi'_len : i'.val < out'.val.length := by simp; scalar_tac
      refine ⟨⟨T', inp1_post1, by scalar_tac, by scalar_tac, by scalar_tac, ?_, ?_⟩, by scalar_tac⟩
      · intro j hj
        have hj' : j < i'.val + 1 := by scalar_tac
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj' with hlt | rfl
        · rw [ha_val, List.getElem!_eq_getElem?_getD, List.getElem?_set_ne (by omega)]
          simpa [List.getElem!_eq_getElem?_getD] using hbound j hlt
        · rw [ha_val, List.getElem!_eq_getElem?_getD, List.getElem?_set_self hi'_len]
          simpa [hd] using Nat.mod_lt _ hpos
      · rw [ha_val, i3_post, take_set_at _ _ _ hi'_len, nats_append, nats_cons, nats_nil]
        rw [← hgo, hn, go_succ _ _ _ _ _ _ _ _ _ inp1_post, ← bits2_post, ← hd]
        simp [List.append_assoc, i3_post]
    · simp only [step_simps]
      have hie : i'.val = out_len.val := by scalar_tac
      have hn : out_len.val - i'.val = 0 := by omega
      rw [hn, hie] at hgo
      simp only [Spec.base2bGo, List.append_nil] at hgo
      exact ⟨hgo, fun j hj => hbound j (by omega)⟩
  · exact ⟨T, ht, hc, hbits, hi, hbound, rfl⟩

/-- `fors::arm::base_2b_stack` computes FIPS 205 Algorithm 4 (`Spec.base2b`) directly
on the stack without heap allocation for every valid `(b, out_len)` geometry
(including all six FIPS 205 SHA-2 parameter sets). -/
@[step]
theorem base_2b_stack_spec (md : Slice U8) (b : U32) (out_len : Usize)
    (hb : 1 ≤ b.val ∧ b.val ≤ 16) (hout : out_len.val ≤ 35)
    (hx : out_len.val * b.val ≤ 8 * md.length) :
    fors.arm.base_2b_stack md b out_len ⦃ r =>
      nats (r.val.take out_len.val) = Spec.base2b (bytes md.val) b.val out_len.val ∧
      ∀ j < out_len.val, (r.val[j]!).val < 2 ^ b.val ⦄ := by
  unfold fors.arm.base_2b_stack
  let* ⟨ i, i_post1, i_post ⟩ ← U32.ShiftLeft_spec
  have hpow : 2 ^ b.val ≤ 2 ^ 16 := Nat.pow_le_pow_right (by omega) hb.2
  have hpos : 0 < 2 ^ b.val := Nat.pow_pos (by omega)
  have hi : i.val = 2 ^ b.val := by
    rw [i_post1, Nat.shiftLeft_eq, Nat.one_mul]
    exact Nat.mod_eq_of_lt (by scalar_tac)
  let* ⟨ mask, mask_post, mask_post1 ⟩ ← U32.sub_spec
  have hmask : mask.val = 2 ^ b.val - 1 := by omega
  have h := base_2b_stack_loop_spec md b out_len (Array.repeat 35#usize 0#u32) 0#usize 0#u32 0#u32
    mask 0#usize 0 hb hout hx hmask (by simp) (by simp) (by simp) (by scalar_tac) (by simp)
  simpa [Spec.base2b, nats] using h

/-- Corollary: `base_2b_stack` matches `Spec.base2b` for every valid FIPS 205 parameter set. -/
theorem base_2b_stack_valid_params (p : Spec.Params) (hv : p.Valid) (md : Slice U8)
    (hmd : p.mdBytes ≤ md.length) :
    fors.arm.base_2b_stack md (U32.ofNat p.a (by have := hv.a_le; scalar_tac))
      (Usize.ofNat p.k (by have := hv.k_le; scalar_tac)) ⦃ r =>
      nats (r.val.take p.k) = Spec.base2b (bytes md.val) p.a p.k ∧
      ∀ j < p.k, (r.val[j]!).val < 2 ^ p.a ⦄ := by
  have ha1 := hv.a_pos
  have ha2 := hv.a_le
  have hk := hv.k_le
  have hroom : p.k * p.a ≤ 8 * md.length := by
    simp only [Spec.Params.mdBytes] at hmd
    omega
  simpa using base_2b_stack_spec md (U32.ofNat p.a (by scalar_tac))
    (Usize.ofNat p.k (by scalar_tac)) ⟨by simp; omega, by simp; omega⟩ (by simp; omega)
    (by simpa using hroom)

/-! ## `wots::arm::wots_digits_stack` -/

/-- Nibbles of a byte list in FIPS 205 big-endian order: `[hi_0, lo_0, hi_1, lo_1, ...]`. -/
def nibbles (l : Spec.Bytes) : List Nat :=
  l.flatMap fun b => [b.toNat / 16, b.toNat % 16]

private theorem base2bGo_nibble_step (xs : Spec.Bytes) (n i : Nat) (T : Nat)
    (hi : i < xs.length) :
    Spec.base2bGo xs 4 (2 * (n + 1)) i 0 T =
      xs[i]!.toNat / 16 :: xs[i]!.toNat % 16 :: Spec.base2bGo xs 4 (2 * n) (i + 1) 0 ((T <<< 8) + xs[i]!.toNat) := by
  have hfill1 : Spec.base2bFill xs 4 i 0 T = (i + 1, 8, (T <<< 8) + xs[i]!.toNat) := by
    rw [fill_step _ _ _ _ _ (by omega), fill_done _ _ _ _ _ (by omega)]
  have hfill2 : Spec.base2bFill xs 4 (i + 1) 4 ((T <<< 8) + xs[i]!.toNat) =
      (i + 1, 4, (T <<< 8) + xs[i]!.toNat) := by
    rw [fill_done _ _ _ _ _ (by omega)]
  rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega, go_succ _ _ _ _ _ _ _ _ _ hfill1]
  simp only [show 8 - 4 = 4 from rfl]
  rw [go_succ _ _ _ _ _ _ _ _ _ hfill2]
  simp only [show 4 - 4 = 0 from rfl, Nat.shiftRight_zero, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq,
    Nat.pow_zero, Nat.div_one]
  have hb : xs[i]!.toNat < 256 := xs[i]!.isLt
  have h1 : ((T * 2 ^ 8 + xs[i]!.toNat) / 2 ^ 4) % 2 ^ 4 = xs[i]!.toNat / 16 := by
    simp only [show (2 : Nat) ^ 8 = 256 by rfl, show (2 : Nat) ^ 4 = 16 by rfl]
    omega
  have h2 : (T * 2 ^ 8 + xs[i]!.toNat) % 2 ^ 4 = xs[i]!.toNat % 16 := by
    simp only [show (2 : Nat) ^ 8 = 256 by rfl, show (2 : Nat) ^ 4 = 16 by rfl]
    omega
  rw [h1, h2]

private theorem base2bGo_nibbles_aux (xs : Spec.Bytes) (n i T : Nat) (h : i + n ≤ xs.length) :
    Spec.base2bGo xs 4 (2 * n) i 0 T = nibbles ((xs.drop i).take n) := by
  induction n generalizing i T with
  | zero => simp [Spec.base2bGo, nibbles]
  | succ n ih =>
    rw [base2bGo_nibble_step xs n i T (by omega), ih (i + 1) _ (by omega)]
    have hdrop : (xs.drop i).take (n + 1) = xs[i]! :: (xs.drop (i + 1)).take n := by
      have hi : i < xs.length := by omega
      rw [List.drop_eq_getElem_cons hi, List.take_succ_cons, List.getElem!_eq_getElem?_getD,
        List.getElem?_eq_getElem hi]
      rfl
    rw [hdrop]
    simp [nibbles]

theorem base2b_4_eq_nibbles (xs : Spec.Bytes) :
    Spec.base2b xs 4 (2 * xs.length) = nibbles xs := by
  unfold Spec.base2b
  simpa using base2bGo_nibbles_aux xs xs.length 0 0 (by omega)

theorem base2b_checksum3 (csum : Nat) (hc : csum < 4096) :
    Spec.base2b (Spec.toByte (csum <<< 4) 2) 4 3 =
      [(csum >>> 8) &&& 15, (csum >>> 4) &&& 15, csum &&& 15] := by
  have hb0 : (Spec.toByte (csum <<< 4) 2)[0]!.toNat = csum / 16 := by
    simp only [Spec.toByte, show List.range 2 = [0, 1] from rfl, List.map_cons, List.map_nil]
    simp [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
    omega
  have hb1 : (Spec.toByte (csum <<< 4) 2)[1]!.toNat = (csum * 16) % 256 := by
    simp only [Spec.toByte, show List.range 2 = [0, 1] from rfl, List.map_cons, List.map_nil]
    simp [Nat.shiftLeft_eq]
  unfold Spec.base2b
  have hfill1 : Spec.base2bFill (Spec.toByte (csum <<< 4) 2) 4 0 0 0 =
      (1, 8, csum / 16) := by
    rw [fill_step _ _ _ _ _ (by omega), fill_done _ _ _ _ _ (by omega), hb0]
    simp
  have hfill2 : Spec.base2bFill (Spec.toByte (csum <<< 4) 2) 4 1 4 (csum / 16) =
      (1, 4, csum / 16) := by
    rw [fill_done _ _ _ _ _ (by omega)]
  have hfill3 : Spec.base2bFill (Spec.toByte (csum <<< 4) 2) 4 1 0 (csum / 16) =
      (2, 8, ((csum / 16) <<< 8) + (csum * 16) % 256) := by
    rw [fill_step _ _ _ _ _ (by omega), fill_done _ _ _ _ _ (by omega), hb1]
  rw [go_succ _ _ 2 _ _ _ _ _ _ hfill1]
  simp only [show 8 - 4 = 4 from rfl]
  rw [go_succ _ _ 1 _ _ _ _ _ _ hfill2]
  simp only [show 4 - 4 = 0 from rfl]
  rw [go_succ _ _ 0 _ _ _ _ _ _ hfill3]
  simp only [Spec.base2bGo, show 8 - 4 = 4 from rfl, Nat.shiftRight_zero,
    Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, Nat.pow_zero, Nat.div_one,
    show (15 : Nat) = 2 ^ 4 - 1 by rfl, Nat.and_two_pow_sub_one_eq_mod]
  simp only [show (2 : Nat) ^ 4 = 16 by rfl, show (2 : Nat) ^ 8 = 256 by rfl]
  refine (List.cons.injEq _ _ _ _).mpr ⟨by omega, (List.cons.injEq _ _ _ _).mpr ⟨by omega,
    (List.cons.injEq _ _ _ _).mpr ⟨by omega, rfl⟩⟩⟩

private theorem wots_digits_stack_loop_spec {N : Usize} (hN : N.val ≤ 32) (m : Array U8 N)
    (digits : Array U32 67#usize) (csum : U32) (i : Usize) (hi : i.val ≤ N.val)
    (hdig : nats (digits.val.take (2 * i.val)) = nibbles ((bytes m.val).take i.val))
    (hcsum : csum.val = (nibbles ((bytes m.val).take i.val)).foldl (fun c x => c + (15 - x)) 0)
    (hcb : csum.val ≤ 30 * i.val)
    (hb : ∀ j < 2 * i.val, (digits.val[j]!).val < 16) :
    wots.arm.wots_digits_stack_loop m digits csum i ⦃ r =>
      nats (r.1.val.take (2 * N.val)) = nibbles (bytes m.val) ∧
      r.2.val = (nibbles (bytes m.val)).foldl (fun c x => c + (15 - x)) 0 ∧
      r.2.val ≤ 30 * N.val ∧
      ∀ j < 2 * N.val, (r.1.val[j]!).val < 16 ⦄ := by
  unfold wots.arm.wots_digits_stack_loop
  apply loop.spec_decr_nat
    (measure := fun (p : Array U32 67#usize × U32 × Usize) => N.val - p.2.2.val)
    (inv := fun p => p.2.2.val ≤ N.val ∧
      nats (p.1.val.take (2 * p.2.2.val)) = nibbles ((bytes m.val).take p.2.2.val) ∧
      p.2.1.val = (nibbles ((bytes m.val).take p.2.2.val)).foldl (fun c x => c + (15 - x)) 0 ∧
      p.2.1.val ≤ 30 * p.2.2.val ∧
      ∀ j < 2 * p.2.2.val, (p.1.val[j]!).val < 16)
  · rintro ⟨digits, csum, i⟩ ⟨hi, hdig, hcsum, hcb, hb⟩
    simp only [wots.arm.wots_digits_stack_loop.body]
    simp only at hi hdig hcsum hcb hb
    spec_split
    · have him : i.val < m.val.length := by scalar_tac
      let* ⟨ byte, byte_post ⟩ ← Array.index_usize_spec
      let* ⟨ i1, i1_post, i1_post1 ⟩ ← U8.ShiftRight_IScalar_spec
      let* ⟨ hi_v, hi_post ⟩ ← UScalar.cast.step_spec
      let* ⟨ i2, i2_post, i2_post1 ⟩ ← UScalar.and_spec
      let* ⟨ lo_v, lo_post ⟩ ← UScalar.cast.step_spec
      have hbyte : byte.val < 256 := byte.hBounds
      have hhi_val : hi_v.val = byte.val / 16 := by
        have h1 : hi_v.val = i1.val := by simp [hi_post]
        rw [h1, i1_post, Nat.shiftRight_eq_div_pow]
      have hlo_val : lo_v.val = byte.val % 16 := by
        have h1 : lo_v.val = i2.val := by simp [lo_post]
        rw [h1, i2_post, UScalar.val_and, show (15#u8).val = 2 ^ 4 - 1 by decide,
          Nat.and_two_pow_sub_one_eq_mod]
      have hhi_lt : hi_v.val < 16 := by omega
      have hlo_lt : lo_v.val < 16 := by omega
      let* ⟨ i3, i3_post ⟩ ← Usize.mul_spec
      let* ⟨ digits1, digits1_post ⟩ ← Array.update_spec
      let* ⟨ i4, i4_post ⟩ ← Usize.add_spec
      let* ⟨ a, a_post ⟩ ← Array.update_spec
      let* ⟨ i5, i5_post, i5_post1 ⟩ ← U32.sub_spec
      let* ⟨ i6, i6_post, i6_post1 ⟩ ← U32.sub_spec
      let* ⟨ csum1, csum1_post ⟩ ← U32.add_spec
      let* ⟨ i7, i7_post ⟩ ← Usize.add_spec
      have hdig1_val : digits1.val = digits.val.set i3.val hi_v := by
        rw [digits1_post, Array.set_val_eq]
      have ha_val : a.val = digits1.val.set i4.val lo_v := by
        rw [a_post, Array.set_val_eq]
      have htake_m : (bytes m.val).take (i.val + 1) = (bytes m.val).take i.val ++ [byte.bv] := by
        rw [← bytes_take, List.take_succ_eq_append_getElem him, bytes_append, bytes_cons, bytes_nil,
          bytes_take, byte_post]
      have htake_a : nats (a.val.take (2 * i7.val)) =
          nats (digits.val.take (2 * i.val)) ++ [hi_v.val, lo_v.val] := by
        rw [i7_post, show 2 * (i.val + 1) = (2 * i.val + 1) + 1 by omega, ha_val,
          show i4.val = 2 * i.val + 1 by omega, take_set_at _ _ _ (by simp [hdig1_val]; omega),
          hdig1_val, show i3.val = 2 * i.val by omega, take_set_at _ _ _ (by simp; omega)]
        simp [nats, List.append_assoc]
      refine ⟨by scalar_tac, ?_, ?_, by omega, ?_, by scalar_tac⟩
      · rw [htake_a, hdig, i7_post, htake_m]
        simp [nibbles, hhi_val, hlo_val]
      · rw [i7_post, htake_m]
        unfold nibbles at hcsum ⊢
        simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
          List.append_nil, List.foldl_append, List.foldl_cons, List.foldl_nil]
        rw [← hcsum]
        have hbv : byte.bv.toNat = byte.val := rfl
        rw [hbv, csum1_post, i6_post, i5_post, hhi_val, hlo_val]
        omega
      · intro j hj
        have hj' : j < 2 * i.val + 2 := by scalar_tac
        by_cases h1 : j < 2 * i.val
        · rw [ha_val, List.getElem!_eq_getElem?_getD, List.getElem?_set_ne (by omega),
            hdig1_val, List.getElem?_set_ne (by omega)]
          simpa [List.getElem!_eq_getElem?_getD] using hb j h1
        · by_cases h2 : j = 2 * i.val
          · subst h2
            rw [ha_val, List.getElem!_eq_getElem?_getD, List.getElem?_set_ne (by omega),
              hdig1_val, show i3.val = 2 * i.val by omega, List.getElem?_set_self (by simp; omega)]
            simpa using hhi_lt
          · have h3 : j = 2 * i.val + 1 := by omega
            subst h3
            rw [ha_val, List.getElem!_eq_getElem?_getD, show i4.val = 2 * i.val + 1 by omega,
              List.getElem?_set_self (by simp [hdig1_val]; omega)]
            simpa using hlo_lt
    · simp only [step_simps]
      have hie : i.val = N.val := by scalar_tac
      have htake : (bytes m.val).take N.val = bytes m.val :=
        List.take_of_length_le (by simp)
      rw [hie] at hdig hcsum hcb hb
      rw [htake] at hdig hcsum
      exact ⟨hdig, hcsum, hcb, hb⟩
  · exact ⟨hi, hdig, hcsum, hcb, hb⟩

/-- `wots::arm::wots_digits_stack` computes FIPS 205 `Spec.wotsDigits` (message
base-16 nibbles followed by the 3 big-endian checksum nibbles) on the stack for
`N ∈ {16, 24, 32}`. -/
@[step]
theorem wots_digits_stack_spec {N : Usize} (p : Spec.Params) (hv : p.Valid) (hN : p.n = N.val)
    (m : Array U8 N) :
    wots.arm.wots_digits_stack m ⦃ r =>
      nats (r.val.take (2 * N.val + 3)) = Spec.wotsDigits p (bytes m.val) ∧
      ∀ j < 2 * N.val + 3, (r.val[j]!).val < 16 ⦄ := by
  have hn_cases : N.val = 16 ∨ N.val = 24 ∨ N.val = 32 := by
    have := hv.n_cases; omega
  have hN32 : N.val ≤ 32 := by omega
  unfold wots.arm.wots_digits_stack
  step with wots_digits_stack_loop_spec hN32 m (Array.repeat 67#usize 0#u32) 0#u32 0#usize
    (by scalar_tac) (by simp [nibbles]) (by simp [nibbles]) (by simp) (by simp)
    as ⟨digits1, csum, hdig1, hcsum1, hcb1, hb1⟩
  let* ⟨ len1, len1_post ⟩ ← Usize.mul_spec
  let* ⟨ i, i_post, i_post1 ⟩ ← U32.ShiftRight_IScalar_spec
  let* ⟨ i1, i1_post, i1_post1 ⟩ ← UScalar.and_spec
  let* ⟨ digits2, digits2_post ⟩ ← Array.update_spec
  let* ⟨ i2, i2_post, i2_post1 ⟩ ← U32.ShiftRight_IScalar_spec
  let* ⟨ i3, i3_post ⟩ ← Usize.add_spec
  let* ⟨ i4, i4_post, i4_post1 ⟩ ← UScalar.and_spec
  let* ⟨ digits3, digits3_post ⟩ ← Array.update_spec
  let* ⟨ i5, i5_post ⟩ ← Usize.add_spec
  let* ⟨ i6, i6_post, i6_post1 ⟩ ← UScalar.and_spec
  let* ⟨ digits4, digits4_post ⟩ ← Array.update_spec
  have hlen1 : p.len1 = 2 * N.val := by
    simp only [Spec.Params.len1, hv.lgw_eq, hN]; omega
  have hlen2 : p.len2 = 3 := by
    simp only [Spec.Params.len2, Spec.Params.len1, Spec.Params.w, hv.lgw_eq, hN]
    rcases hn_cases with h | h | h <;> rw [h] <;> decide
  have hw : p.w = 16 := by simp [Spec.Params.w, hv.lgw_eq]
  have hi1_val : i1.val = (csum.val >>> 8) &&& 15 := by
    rw [i1_post, UScalar.val_and, i_post]; rfl
  have hi4_val : i4.val = (csum.val >>> 4) &&& 15 := by
    rw [i4_post, UScalar.val_and, i2_post]; rfl
  have hi6_val : i6.val = csum.val &&& 15 := by
    rw [i6_post, UScalar.val_and]; rfl
  have hi1_lt : i1.val < 16 := by
    rw [hi1_val, show (15 : Nat) = 2 ^ 4 - 1 by rfl, Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_lt _ (by omega)
  have hi4_lt : i4.val < 16 := by
    rw [hi4_val, show (15 : Nat) = 2 ^ 4 - 1 by rfl, Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_lt _ (by omega)
  have hi6_lt : i6.val < 16 := by
    rw [hi6_val, show (15 : Nat) = 2 ^ 4 - 1 by rfl, Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_lt _ (by omega)
  have hd2_val : digits2.val = digits1.val.set len1.val i1 := by
    rw [digits2_post, Array.set_val_eq]
  have hd3_val : digits3.val = digits2.val.set i3.val i4 := by
    rw [digits3_post, Array.set_val_eq]
  have hd4_val : digits4.val = digits3.val.set i5.val i6 := by
    rw [digits4_post, Array.set_val_eq]
  refine ⟨?_, ?_⟩
  · have htake : digits4.val.take (2 * N.val + 3) =
        digits1.val.take (2 * N.val) ++ [i1, i4, i6] := by
      rw [hd4_val, show i5.val = 2 * N.val + 2 by omega, take_set_at _ _ _ (by simp [hd3_val, hd2_val]; omega),
        hd3_val, show i3.val = 2 * N.val + 1 by omega, take_set_at _ _ _ (by simp [hd2_val]; omega),
        hd2_val, show len1.val = 2 * N.val by omega, take_set_at _ _ _ (by simp; omega)]
      simp [List.append_assoc]
    rw [htake, nats_append, hdig1]
    simp only [Spec.wotsDigits, hlen1, hlen2, hw, hv.lgw_eq]
    have hmlen : (bytes m.val).length = N.val := by simp
    rw [← hmlen, base2b_4_eq_nibbles]
    simp only [show (16 : Nat) - 1 = 15 from rfl, show (8 - (3 * 4) % 8) % 8 = 4 from rfl,
      show (3 * 4 + 7) / 8 = 2 from rfl]
    rw [← hcsum1, base2b_checksum3 csum.val (by omega)]
    simp [nats, hi1_val, hi4_val, hi6_val]
  · intro j hj
    by_cases h1 : j < 2 * N.val
    · rw [hd4_val, List.getElem!_eq_getElem?_getD, List.getElem?_set_ne (by omega),
        hd3_val, List.getElem?_set_ne (by omega),
        hd2_val, List.getElem?_set_ne (by omega)]
      simpa [List.getElem!_eq_getElem?_getD] using hb1 j h1
    · by_cases h2 : j = 2 * N.val
      · subst h2
        rw [hd4_val, List.getElem!_eq_getElem?_getD, List.getElem?_set_ne (by omega),
          hd3_val, List.getElem?_set_ne (by omega),
          hd2_val, show len1.val = 2 * N.val by omega, List.getElem?_set_self (by simp; omega)]
        simpa using hi1_lt
      · by_cases h3 : j = 2 * N.val + 1
        · subst h3
          rw [hd4_val, List.getElem!_eq_getElem?_getD, List.getElem?_set_ne (by omega),
            hd3_val, show i3.val = 2 * N.val + 1 by omega, List.getElem?_set_self (by simp [hd2_val]; omega)]
          simpa using hi4_lt
        · have h4 : j = 2 * N.val + 2 := by omega
          subst h4
          rw [hd4_val, List.getElem!_eq_getElem?_getD,
            show i5.val = 2 * N.val + 2 by omega, List.getElem?_set_self (by simp [hd3_val, hd2_val]; omega)]
          simpa using hi6_lt

/-! ## `xmss::arm::prepare_tlen` -/

private theorem WOTS_PK_eq : address.WOTS_PK = 1#u32 := by with_unfolding_all rfl

private theorem bytes_map_mk (l : List (BitVec 8)) : bytes (l.map UScalar.mk) = l := by
  simp [bytes]

private theorem toLEBytes_eq_range : ∀ (n : Nat) (x : BitVec (8 * n)),
    x.toLEBytes = (List.range n).map fun i => BitVec.ofNat 8 (x.toNat >>> (8 * i))
  | 0, x => by
    rw [BitVec.toLEBytes]; simp
  | n + 1, x => by
    rw [BitVec.toLEBytes, if_pos (by omega)]
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

private theorem toBEBytes_eq_toByte (n : Nat) (x : BitVec (8 * n)) :
    x.toBEBytes = Spec.toByte x.toNat n := by
  rw [BitVec.toBEBytes, toLEBytes_eq_range n x, ← List.map_reverse]
  apply List.ext_getElem
  · simp [Spec.toByte]
  · intro i hi1 hi2
    simp only [List.getElem_map, List.getElem_reverse, List.getElem_range, Spec.toByte,
      List.length_range]

private theorem u16_toBEBytes_eq (x : BitVec 16) :
    x.toBEBytes = Spec.toByte x.toNat 2 :=
  toBEBytes_eq_toByte 2 x

private theorem u64_toBEBytes_eq (x : BitVec 64) :
    x.toBEBytes = Spec.toByte x.toNat 8 :=
  toBEBytes_eq_toByte 8 x

private theorem toByte_small_prefix (x n : Nat) (hn : 2 ≤ n) (hx : x < 65536) :
    Spec.toByte x n = List.replicate (n - 2) 0#8 ++ Spec.toByte x 2 := by
  apply List.ext_getElem
  · simp [Spec.toByte]; omega
  · intro i hi1 hi2
    simp only [Spec.toByte, List.getElem_map, List.getElem_range]
    by_cases h : i < n - 2
    · rw [List.getElem_append_left (by simp; omega), List.getElem_replicate]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
      have hpow : 65536 ≤ 2 ^ (8 * (n - 1 - i)) := by
        calc 65536 = 2 ^ 16 := by norm_num
          _ ≤ 2 ^ (8 * (n - 1 - i)) := Nat.pow_le_pow_right (by omega) (by omega)
      have : x / 2 ^ (8 * (n - 1 - i)) = 0 := Nat.div_eq_of_lt (by omega)
      simp [this]
    · rw [List.getElem_append_right (by simp; omega)]
      simp only [List.length_replicate, Spec.toByte, List.getElem_map, List.getElem_range]
      congr 2
      omega

private theorem setSlice_at_zero {α} (l s : List α) (h : s.length ≤ l.length) :
    l.setSlice! 0 s = s ++ l.drop s.length := by
  simp [List.setSlice!, min_eq_left h]

private theorem setSlice_at_end {α} (l s : List α) (k : Nat) (hk : k + s.length = l.length) :
    l.setSlice! k s = l.take k ++ s := by
  have hm : min s.length (l.length - k) = s.length := by omega
  have hd : l.drop (k + s.length) = [] := by rw [hk, List.drop_length]
  simp [List.setSlice!, hm, hd]

private theorem setSlice_mid_exact {α} (A B C s : List α) (hs : s.length = B.length) :
    (A ++ B ++ C).setSlice! A.length s = A ++ s ++ C := by
  have hm : min s.length (A.length + B.length + C.length - A.length) = s.length := by omega
  simp only [List.setSlice!, List.length_append, hm]
  rw [List.take_append_of_le_length (by simp), List.take_append_of_le_length le_rfl,
    List.take_length, List.take_of_length_le le_rfl,
    List.drop_append_of_le_length (by simp [hs]),
    List.drop_eq_nil_of_le (by simp [hs])]
  simp

private theorem list_set_mid {α} (A B : List α) (x y : α) :
    (A ++ x :: B).set A.length y = A ++ y :: B := by
  induction A with
  | nil => rfl
  | cons a A ih => simp [ih]

/-- `xmss::arm::prepare_tlen` writes the exact FIPS 205 `WOTS_PK` compressed address
at `[0..22)`, the `0x80` padding delimiter at `[size]`, and the 16-bit big-endian
bit-length `((block + size) * 8)` at `[L - 2 .. L)`, leaving every other byte untouched. -/
@[step]
theorem prepare_tlen_spec {L : Usize} (m : Array U8 L) (adrs : address.Adrs) (keypair : U32)
    (size block : Usize)
    (hsize_lo : 22 ≤ size.val) (hsize_hi : size.val + 3 ≤ L.val)
    (hbits : (block.val + size.val) * 8 < 65536) :
    xmss.arm.prepare_tlen m adrs keypair size block ⦃ r =>
      bytes (r.val.take 22) = ({ (adrsS adrs).setTypeAndClear Spec.WOTS_PK with keypair := keypair.val }).compress ∧
      (r.val.drop 22).take (size.val - 22) = (m.val.drop 22).take (size.val - 22) ∧
      (r.val[size.val]!).bv = 0x80#8 ∧
      (r.val.drop (size.val + 1)).take (L.val - 2 - (size.val + 1)) =
        (m.val.drop (size.val + 1)).take (L.val - 2 - (size.val + 1)) ∧
      bytes (r.val.drop (L.val - 2)) = Spec.toByte ((block.val + size.val) * 8) 2 ⦄ := by
  unfold xmss.arm.prepare_tlen
  step*
  have ha2_len : a2.val.length = 22 := by simp
  have ha3_len : a3.val.length = 2 := by simp
  have hm1 : (index_mut_back s2).val = a2.val ++ m.val.drop 22 := by
    rw [s_post2, s2_post, s1_post, Array.val_to_slice, setSlice_at_zero m.val a2.val (by scalar_tac),
      ha2_len]
  have hpk : adrsS a1 = { (adrsS adrs).setTypeAndClear Spec.WOTS_PK with keypair := keypair.val } := by
    rw [a1_post, a_post1]
    simp [adrsS, Spec.Adrs.setTypeAndClear, Spec.WOTS_PK, WOTS_PK_eq]
  have hm2 : m2.val = (index_mut_back s2).val.set size.val 128#u8 := by
    rw [m2_post, Array.set_val_eq]
  have hr : (index_mut_back1 s5).val = m2.val.take (L.val - 2) ++ a3.val := by
    rw [s3_post2, s5_post, s4_post, Array.val_to_slice, i_post]
    exact setSlice_at_end m2.val a3.val (L.val - 2) (by scalar_tac)
  have hm1_len : (index_mut_back s2).val.length = L.val := by simp
  have hm2_len : m2.val.length = L.val := by simp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hr, List.take_append_of_le_length (by simp [hm2_len]; omega),
      List.take_take, min_eq_left (by omega), hm2]
    have htake22 : ((index_mut_back s2).val.set size.val 128#u8).take 22 =
        (index_mut_back s2).val.take 22 := by
      apply List.ext_getElem (by simp [hm1_len])
      intro j hj1 hj2
      rw [List.getElem_take, List.getElem_take, List.getElem_set_ne (by simp at hj1; omega)]
    rw [htake22, hm1, List.take_append_of_le_length (by omega),
      List.take_of_length_le (by omega : a2.val.length ≤ 22), a2_post, hpk]
  · apply List.ext_getElem
    · simp [hr, hm2_len]; omega
    · intro j hj1 hj2
      simp only [List.length_take, List.length_drop, hr, List.length_append, List.length_take,
        hm2_len, ha3_len] at hj1
      have hj : j < size.val - 22 := by omega
      rw [List.getElem_take, List.getElem_drop, List.getElem_take, List.getElem_drop]
      have h1 : (index_mut_back1 s5).val[22 + j]'(by simp; omega) =
          (m2.val.take (L.val - 2) ++ a3.val)[22 + j]'(by simp [hm2_len, ha3_len]; omega) := by
        simp [hr]
      rw [h1, List.getElem_append_left (by simp [hm2_len]; omega), List.getElem_take]
      have h2 : m2.val[22 + j]'(by simp [hm2_len]; omega) =
          ((index_mut_back s2).val.set size.val 128#u8)[22 + j]'(by simp [hm1_len]; omega) := by
        simp [hm2]
      rw [h2, List.getElem_set_ne (by omega)]
      have h3 : (index_mut_back s2).val[22 + j]'(by simp [hm1_len]; omega) =
          (a2.val ++ m.val.drop 22)[22 + j]'(by simp [ha2_len]; omega) := by
        simp [hm1]
      rw [h3, List.getElem_append_right (by omega)]
      simp [ha2_len]
  · rw [hr, List.getElem!_eq_getElem?_getD,
      List.getElem?_append_left (by simp [hm2_len]; omega),
      List.getElem?_take_of_lt (by omega), hm2, List.getElem?_set_self (by omega)]
    rfl
  · apply List.ext_getElem
    · simp [hr, hm2_len]; omega
    · intro j hj1 hj2
      simp only [List.length_take, List.length_drop, hr, List.length_append, List.length_take,
        hm2_len, ha3_len] at hj1
      have hj : j < L.val - 2 - (size.val + 1) := by omega
      rw [List.getElem_take, List.getElem_drop, List.getElem_take, List.getElem_drop]
      have h1 : (index_mut_back1 s5).val[size.val + 1 + j]'(by simp; omega) =
          (m2.val.take (L.val - 2) ++ a3.val)[size.val + 1 + j]'(by simp [hm2_len, ha3_len]; omega) := by
        simp [hr]
      rw [h1, List.getElem_append_left (by simp [hm2_len]; omega), List.getElem_take]
      have h2 : m2.val[size.val + 1 + j]'(by simp [hm2_len]; omega) =
          ((index_mut_back s2).val.set size.val 128#u8)[size.val + 1 + j]'(by simp [hm1_len]; omega) := by
        simp [hm2]
      rw [h2, List.getElem_set_ne (by omega)]
      have h3 : (index_mut_back s2).val[size.val + 1 + j]'(by simp [hm1_len]; omega) =
          (a2.val ++ m.val.drop 22)[size.val + 1 + j]'(by simp [ha2_len]; omega) := by
        simp [hm1]
      rw [h3, List.getElem_append_right (by omega)]
      simp only [ha2_len, List.getElem_drop]
      congr 1; omega
  · rw [hr, List.drop_append_of_le_length (by simp [hm2_len])]
    simp only [List.drop_take, Nat.sub_self, List.take_zero, List.nil_append]
    rw [a3_post, bytes_map_mk, u16_toBEBytes_eq]
    have hi3_val : i3.bv.toNat = (block.val + size.val) * 8 := by
      change i3.val = _
      have h1 : i3.val = i2.val % 65536 := by simp [i3_post]
      rw [h1, i2_post, i1_post, Nat.mod_eq_of_lt hbits]
    rw [hi3_val]

/-- Decomposition of a prepared zero-initialized buffer into its 5 segments. -/
private theorem prepare_tlen_zero_decomp {L : Usize} (r : Array U8 L) (adrs : address.Adrs)
    (keypair : U32) (size block : Usize)
    (hsize_lo : 22 ≤ size.val) (hsize_hi : size.val + 3 ≤ L.val)
    (h0 : bytes (r.val.take 22) = ({ (adrsS adrs).setTypeAndClear Spec.WOTS_PK with keypair := keypair.val }).compress)
    (h2 : (r.val[size.val]!).bv = 0x80#8)
    (h3 : (r.val.drop (size.val + 1)).take (L.val - 2 - (size.val + 1)) =
      ((Array.repeat L 0#u8).val.drop (size.val + 1)).take (L.val - 2 - (size.val + 1)))
    (h4 : bytes (r.val.drop (L.val - 2)) = Spec.toByte ((block.val + size.val) * 8) 2) :
    bytes r.val =
      ({ (adrsS adrs).setTypeAndClear Spec.WOTS_PK with keypair := keypair.val }).compress ++
        ((bytes r.val).drop 22).take (size.val - 22) ++
        ([0x80#8] ++ List.replicate (L.val - 2 - (size.val + 1)) 0#8 ++
          Spec.toByte ((block.val + size.val) * 8) 2) := by
  have hrlen : (bytes r.val).length = L.val := by simp
  have hzero : ((bytes r.val).drop (size.val + 1)).take (L.val - 2 - (size.val + 1)) =
      List.replicate (L.val - 2 - (size.val + 1)) 0#8 := by
    rw [← bytes_drop, ← bytes_take, h3]
    simp only [Array.repeat_val, List.drop_replicate, List.take_replicate, bytes_replicate]
    have hmin : min (L.val - 2 - (size.val + 1)) (L.val - (size.val + 1)) = L.val - 2 - (size.val + 1) := by
      omega
    rw [hmin]
    rfl
  have h582 : (bytes r.val)[size.val]! = 0x80#8 := by
    rw [bytes_getElem! _ _ (by simp; omega), h2]
  have hsplit1 : bytes r.val = (bytes r.val).take (L.val - 2) ++ (bytes r.val).drop (L.val - 2) :=
    (List.take_append_drop _ _).symm
  have hsplit2 : (bytes r.val).take (L.val - 2) =
      (bytes r.val).take (size.val + 1) ++ ((bytes r.val).drop (size.val + 1)).take (L.val - 2 - (size.val + 1)) := by
    conv_lhs => rw [← List.take_append_drop (size.val + 1) ((bytes r.val).take (L.val - 2))]
    rw [List.take_take, min_eq_left (by omega), List.drop_take]
  have hsplit3 : (bytes r.val).take (size.val + 1) =
      (bytes r.val).take size.val ++ [(bytes r.val)[size.val]!] := by
    rw [List.take_succ_eq_append_getElem (by omega), List.getElem!_eq_getElem?_getD,
      List.getElem?_eq_getElem (by omega)]
    rfl
  have hsplit4 : (bytes r.val).take size.val =
      (bytes r.val).take 22 ++ ((bytes r.val).drop 22).take (size.val - 22) := by
    conv_lhs => rw [← List.take_append_drop 22 ((bytes r.val).take size.val)]
    rw [List.take_take, min_eq_left (by omega), List.drop_take]
  have hd : (bytes r.val).drop (L.val - 2) = Spec.toByte ((block.val + size.val) * 8) 2 := by
    rw [← bytes_drop, h4]
  have ht : (bytes r.val).take 22 =
      ({ (adrsS adrs).setTypeAndClear Spec.WOTS_PK with keypair := keypair.val }).compress := by
    rw [← bytes_take, h0]
  conv_lhs => rw [hsplit1, hsplit2, hsplit3, hsplit4, ht, h582, hzero, hd]
  simp [List.append_assoc]

/-- Writing the `WOTS` endpoints payload into a zero-initialized buffer prepared by
`prepare_tlen` yields the exact FIPS 180-4 / FIPS 205 padded SHA-256 suffix for `N = 16`. -/
theorem prepare_tlen_sha256_pad (adrs : address.Adrs) (keypair : U32)
    (pkBlock payload : Spec.Bytes) (hpkb : pkBlock.length = 64) (hpay : payload.length = 560) :
    xmss.arm.prepare_tlen (Array.repeat 640#usize 0#u8) adrs keypair 582#usize 64#usize ⦃ r =>
      let wotsPk := { (adrsS adrs).setTypeAndClear Spec.WOTS_PK with keypair := keypair.val }
      (bytes r.val).setSlice! 22 payload =
        (Spec.SHA256.pad (pkBlock ++ wotsPk.compress ++ payload)).drop 64 ⦄ := by
  step with prepare_tlen_spec (Array.repeat 640#usize 0#u8) adrs keypair 582#usize 64#usize
    (by decide) (by decide) (by decide) as ⟨r, h0, h1, h2, h3, h4⟩
  set wotsPk := { (adrsS adrs).setTypeAndClear Spec.WOTS_PK with keypair := keypair.val }
  have hclen : wotsPk.compress.length = 22 := rfl
  have hdecomp := prepare_tlen_zero_decomp r adrs keypair 582#usize 64#usize (by decide) (by decide) h0 h2 h3 h4
  have hmid_len : (((bytes r.val).drop 22).take (582 - 22)).length = 560 := by simp
  rw [hdecomp]
  have hset := setSlice_mid_exact wotsPk.compress (((bytes r.val).drop 22).take (582 - 22))
    ([0x80#8] ++ List.replicate (640 - 2 - (582 + 1)) 0#8 ++ Spec.toByte ((64 + 582) * 8) 2)
    payload (by rw [hpay, hmid_len])
  rw [hclen] at hset
  change (wotsPk.compress ++ ((bytes r.val).drop 22).take (582 - 22) ++
    ([0x80#8] ++ List.replicate (640 - 2 - (582 + 1)) 0#8 ++ Spec.toByte ((64 + 582) * 8) 2)).setSlice! 22 payload = _
  rw [hset]
  unfold Spec.SHA256.pad
  have hmlen : (pkBlock ++ wotsPk.compress ++ payload).length = 646 := by
    simp [hpkb, hclen, hpay]
  rw [hmlen, show (119 - 646 % 64) % 64 = 49 by decide, show 8 * 646 = 5168 by decide,
    toByte_small_prefix 5168 8 (by decide) (by decide)]
  simp only [List.append_assoc, List.drop_append_of_le_length (by omega : 64 ≤ pkBlock.length)]
  rw [← hpkb, List.drop_length, List.nil_append]
  have hrep : List.replicate 49 0#8 ++ (List.replicate (8 - 2) 0#8 ++ Spec.toByte 5168 2) =
      List.replicate 55 0#8 ++ Spec.toByte 5168 2 := by
    rw [← List.append_assoc, ← List.replicate_add]
  rw [hrep]

/-- Writing the `WOTS` endpoints payload into a zero-initialized buffer prepared by
`prepare_tlen` yields the exact FIPS 180-4 / FIPS 205 padded SHA-512 suffix for
`N = 24` (`L = 1280, size = 1246`) and `N = 32` (`L = 2304, size = 2166`). -/
theorem prepare_tlen_sha512_pad (L size : Usize)
    (hparam : (L.val = 1280 ∧ size.val = 1246) ∨ (L.val = 2304 ∧ size.val = 2166))
    (adrs : address.Adrs) (keypair : U32)
    (pkBlock payload : Spec.Bytes) (hpkb : pkBlock.length = 128) (hpay : payload.length = size.val - 22) :
    xmss.arm.prepare_tlen (Array.repeat L 0#u8) adrs keypair size 128#usize ⦃ r =>
      let wotsPk := { (adrsS adrs).setTypeAndClear Spec.WOTS_PK with keypair := keypair.val }
      (bytes r.val).setSlice! 22 payload =
        (Spec.SHA512.pad (pkBlock ++ wotsPk.compress ++ payload)).drop 128 ⦄ := by
  have hsize_lo : 22 ≤ size.val := by rcases hparam with ⟨_, h⟩ | ⟨_, h⟩ <;> omega
  have hsize_hi : size.val + 3 ≤ L.val := by rcases hparam with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  have hbits : (128 + size.val) * 8 < 65536 := by rcases hparam with ⟨_, h⟩ | ⟨_, h⟩ <;> omega
  step with prepare_tlen_spec (Array.repeat L 0#u8) adrs keypair size 128#usize
    hsize_lo hsize_hi (by simpa using hbits) as ⟨r, h0, h1, h2, h3, h4⟩
  set wotsPk := { (adrsS adrs).setTypeAndClear Spec.WOTS_PK with keypair := keypair.val }
  have hclen : wotsPk.compress.length = 22 := rfl
  have hdecomp := prepare_tlen_zero_decomp r adrs keypair size 128#usize hsize_lo hsize_hi h0 h2 h3 h4
  have hmid_len : (((bytes r.val).drop 22).take (size.val - 22)).length = size.val - 22 := by
    simp; omega
  rw [hdecomp]
  have hset := setSlice_mid_exact wotsPk.compress (((bytes r.val).drop 22).take (size.val - 22))
    ([0x80#8] ++ List.replicate (L.val - 2 - (size.val + 1)) 0#8 ++ Spec.toByte ((128 + size.val) * 8) 2)
    payload (by rw [hpay, hmid_len])
  rw [hclen] at hset
  change (wotsPk.compress ++ ((bytes r.val).drop 22).take (size.val - 22) ++
    ([0x80#8] ++ List.replicate (L.val - 2 - (size.val + 1)) 0#8 ++ Spec.toByte ((128 + size.val) * 8) 2)).setSlice! 22 payload = _
  rw [hset]
  unfold Spec.SHA512.pad
  have hmlen : (pkBlock ++ wotsPk.compress ++ payload).length = 128 + size.val := by
    simp [hpkb, hclen, hpay]; omega
  have hzero_len : (239 - (128 + size.val) % 128) % 128 + 14 = L.val - 2 - (size.val + 1) := by
    rcases hparam with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> decide
  rw [hmlen, show 8 * (128 + size.val) = (128 + size.val) * 8 by omega,
    toByte_small_prefix ((128 + size.val) * 8) 16 (by decide) hbits]
  simp only [List.append_assoc, List.drop_append_of_le_length (by omega : 128 ≤ pkBlock.length)]
  have hdrop : pkBlock.drop 128 = [] := List.drop_eq_nil_of_le (by omega)
  rw [hdrop, List.nil_append]
  have hrep : List.replicate ((239 - (128 + size.val) % 128) % 128) 0#8 ++
      (List.replicate (16 - 2) 0#8 ++ Spec.toByte ((128 + size.val) * 8) 2) =
      List.replicate (L.val - 2 - (size.val + 1)) 0#8 ++ Spec.toByte ((128 + size.val) * 8) 2 := by
    rw [← List.append_assoc, ← List.replicate_add, show 16 - 2 = 14 by decide, hzero_len]
  rw [hrep]

/-! ## `sha512::paired::parent_block_512` -/

/-- `sha512::paired::parent_block_512` fills a zero-initialized 128-byte buffer with
the exact second 128-byte block of `Spec.SHA512.pad (pkBlock ‖ ADRSc ‖ left ‖ right)`
for `N ∈ {24, 32}`. -/
@[step]
theorem parent_block_512_spec (N : Usize) (hN : N.val = 24 ∨ N.val = 32)
    (adrs : address.Adrs) (left right : Slice U8)
    (hl : left.length = N.val) (hr : right.length = N.val)
    (pkBlock : Spec.Bytes) (hpkb : pkBlock.length = 128) :
    sha512.paired.parent_block_512 N (Array.repeat 128#usize 0#u8) adrs left right ⦃ r =>
      bytes r.val =
        (Spec.SHA512.pad (pkBlock ++ (adrsS adrs).compress ++ bytes left.val ++ bytes right.val)).drop 128 ⦄ := by
  unfold sha512.paired.parent_block_512
  step*
  all_goals try scalar_tac
  have hclen : (adrsS adrs).compress.length = 22 := rfl
  have hll : (bytes left.val).length = N.val := by simp [hl]
  have hrl : (bytes right.val).length = N.val := by simp [hr]
  have ha_len : a.val.length = 22 := by simp
  have hb1 : (index_mut_back s2).val = a.val ++ List.replicate 106 0#u8 := by
    rw [s_post2, s2_post, s1_post, Array.val_to_slice, Array.repeat_val,
      setSlice_at_zero _ _ (by scalar_tac), ha_len]
    simp
  have hb2 : (index_mut_back1 s4).val = a.val ++ left.val ++ List.replicate (106 - N.val) 0#u8 := by
    rw [s3_post2, s4_post, hb1]
    have hsplit : List.replicate 106 0#u8 = List.replicate N.val 0#u8 ++ List.replicate (106 - N.val) 0#u8 := by
      rw [← List.replicate_add]; congr 1; omega
    rw [hsplit, ← List.append_assoc]
    simpa [ha_len] using setSlice_mid_exact a.val (List.replicate N.val 0#u8)
      (List.replicate (106 - N.val) 0#u8) left.val (by simp [hl])
  have hb3 : (index_mut_back2 s6).val = a.val ++ left.val ++ right.val ++ List.replicate (106 - 2 * N.val) 0#u8 := by
    rw [s5_post2, s6_post, hb2, i_post]
    have hsplit : List.replicate (106 - N.val) 0#u8 =
        List.replicate N.val 0#u8 ++ List.replicate (106 - 2 * N.val) 0#u8 := by
      rw [← List.replicate_add]; congr 1; omega
    have hlen_al : 22 + N.val = (a.val ++ left.val).length := by simp [ha_len, hl]
    rw [hsplit, ← List.append_assoc, hlen_al]
    exact setSlice_mid_exact (a.val ++ left.val) (List.replicate N.val 0#u8)
      (List.replicate (106 - 2 * N.val) 0#u8) right.val (by simp [hr])
  have hb4 : block4.val = a.val ++ left.val ++ right.val ++ [128#u8] ++ List.replicate (105 - 2 * N.val) 0#u8 := by
    rw [block4_post, Array.set_val_eq, hb3, i3_post, i1_post]
    have hrep : List.replicate (106 - 2 * N.val) 0#u8 = 0#u8 :: List.replicate (105 - 2 * N.val) 0#u8 := by
      rw [show 106 - 2 * N.val = (105 - 2 * N.val) + 1 by omega, List.replicate_succ]
    rw [hrep]
    have hidx : 22 + 2 * N.val = (a.val ++ left.val ++ right.val).length := by simp [ha_len, hl, hr]; omega
    rw [hidx, list_set_mid]
    simp [List.append_assoc]
  have hres : (index_mut_back3 s9).val =
      a.val ++ left.val ++ right.val ++ [128#u8] ++ List.replicate (97 - 2 * N.val) 0#u8 ++ a1.val := by
    rw [s7_post2, s9_post, s8_post, Array.val_to_slice, setSlice_at_end _ _ 120 (by scalar_tac), hb4]
    have hlen_pre : (a.val ++ left.val ++ right.val ++ [128#u8]).length = 23 + 2 * N.val := by
      simp [ha_len, hl, hr]; omega
    rw [List.take_append, List.take_of_length_le (by omega : (a.val ++ left.val ++ right.val ++ [128#u8]).length ≤ 120),
      hlen_pre, List.take_replicate,
      min_eq_left (by omega : 120 - (23 + 2 * N.val) ≤ 105 - 2 * N.val),
      show 120 - (23 + 2 * N.val) = 97 - 2 * N.val by omega]
  rw [hres]
  simp only [bytes_append, bytes_cons, bytes_nil, bytes_replicate, a_post, a1_post,
    bytes_map_mk, u64_toBEBytes_eq]
  have hi6_val : i6.bv.toNat = (150 + 2 * N.val) * 8 := by
    change i6.val = _
    have h1 : i6.val = i5.val := by simp [i6_post]
    rw [h1, i5_post, i4_post, i1_post]
  rw [hi6_val]
  unfold Spec.SHA512.pad
  have hmlen : (pkBlock ++ (adrsS adrs).compress ++ bytes left.val ++ bytes right.val).length = 150 + 2 * N.val := by
    simp [hpkb, hclen, hll, hrl]; omega
  rw [hmlen, show 8 * (150 + 2 * N.val) = (150 + 2 * N.val) * 8 by omega]
  have hbits_lt : (150 + 2 * N.val) * 8 < 65536 := by omega
  rw [toByte_small_prefix ((150 + 2 * N.val) * 8) 16 (by decide) hbits_lt,
    toByte_small_prefix ((150 + 2 * N.val) * 8) 8 (by decide) hbits_lt]
  have hrep_eq : (239 - (150 + 2 * N.val) % 128) % 128 + 14 = (97 - 2 * N.val) + 6 := by
    rcases hN with h | h <;> rw [h] <;> decide
  simp only [List.append_assoc, List.drop_append_of_le_length (by omega : 128 ≤ pkBlock.length)]
  have hdrop : pkBlock.drop 128 = [] := List.drop_eq_nil_of_le (by omega)
  rw [hdrop, List.nil_append]
  have htail : List.replicate (97 - 2 * N.val) 0#8 ++
      (List.replicate (8 - 2) 0#8 ++ Spec.toByte ((150 + 2 * N.val) * 8) 2) =
      List.replicate ((239 - (150 + 2 * N.val) % 128) % 128) 0#8 ++
        (List.replicate (16 - 2) 0#8 ++ Spec.toByte ((150 + 2 * N.val) * 8) 2) := by
    rw [← List.append_assoc, ← List.append_assoc, ← List.replicate_add, ← List.replicate_add,
      show 8 - 2 = 6 by decide, show 16 - 2 = 14 by decide, hrep_eq]
  change (adrsS adrs).compress ++ (bytes left.val ++ (bytes right.val ++
    ([0x80#8] ++ (List.replicate (97 - 2 * N.val) 0#8 ++
      (List.replicate (8 - 2) 0#8 ++ Spec.toByte ((150 + 2 * N.val) * 8) 2))))) = _
  rw [htail]

#print axioms wots_digits_stack_spec
#print axioms base_2b_stack_spec
#print axioms base_2b_stack_valid_params
#print axioms prepare_tlen_spec
#print axioms prepare_tlen_sha256_pad
#print axioms prepare_tlen_sha512_pad
#print axioms parent_block_512_spec

end slhdsa.Armwide
