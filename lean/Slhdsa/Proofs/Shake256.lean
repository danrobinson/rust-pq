import Slhdsa.Proofs.Keccak
open Aeneas Aeneas.Std Result
namespace slhdsa.Keccak

def view (s : shake256.Sponge) := (words s.lanes, s.pos.val)

private theorem words_set {n : Usize} (a : Array U64 n) (i : Usize) (v : U64) :
    words (a.set i v) = (words a).setIfInBounds i.val v.bv := by
  apply _root_.Array.ext
  · simp [words]
  · intro j h1 h2
    simp only [words, Array.set_val_eq, List.getElem_toArray, List.getElem_map,
      List.getElem_set, _root_.Array.getElem_setIfInBounds]
    split <;> simp_all

@[step] theorem new_spec : shake256.Sponge.new ⦃ s => view s = Spec.Keccak.initial ∧ s.pos.val < 136 ⦄ := by
  simp [shake256.Sponge.new, view, words, Spec.Keccak.initial, Array.repeat_val]
  rfl

private theorem absorb_loop_spec (data : Slice U8) (s : shake256.Sponge) (i : Usize)
    (hi : i.val ≤ data.length) (hs : s.pos.val < 136) :
    shake256.Sponge.absorb_loop s data i ⦃ out =>
      view out = ((bytes data.val).drop i.val).foldl Spec.Keccak.feed (view s) ∧ out.pos.val < 136 ⦄ := by
  let target := ((bytes data.val).drop i.val).foldl Spec.Keccak.feed (view s)
  unfold shake256.Sponge.absorb_loop
  apply loop.spec_decr_nat
    (measure := fun (p : shake256.Sponge × Usize) => data.length - p.2.val)
    (inv := fun p => p.2.val ≤ data.length ∧ p.1.pos.val < 136 ∧
      ((bytes data.val).drop p.2.val).foldl Spec.Keccak.feed (view p.1) = target)
  · rintro ⟨state,k⟩ ⟨hk,hpos,acc⟩
    simp only at hk hpos acc
    simp only [shake256.Sponge.absorb_loop.body, step_simps]
    spec_split
    · have hkd : k.val < data.val.length := by scalar_tac
      rw [← List.getElem_cons_drop (show k.val < (bytes data.val).length by simpa),
        List.foldl_cons] at acc
      simp only [bytes, List.getElem_map] at acc
      step*
      have inLane : words (index_mut_back i9) =
          Spec.Keccak.xorByte (words state.lanes) state.pos.val (data.val[k.val]).bv := by
        rw [index_mut_back_post, words_set, Spec.Keccak.xorByte]
        simp only [i7_post, i9_post1, i8_post, i6_post1, i3_post, i2_post, i5_post, i4_post,
          UScalar.cast_bv_eq]
        have hget := words_get state.lanes (state.pos.val/8) (by scalar_tac)
        rw [hget]
        rfl
      have next (s' : shake256.Sponge) (eq : view s' = Spec.Keccak.feed (view state) (data.val[k.val]).bv) :
          ((bytes data.val).drop (k.val+1)).foldl Spec.Keccak.feed (view s') = target := by
        simpa only [eq, bytes] using acc
      by_cases boundary : i10 = shake256.RATE
      · simp only [boundary, ↓reduceIte]
        step*
        have he : state.pos.val + 1 = 136 := by rw [← i10_post, boundary]; simp [shake256.RATE]
        refine ⟨by scalar_tac, by simp, ?_, by scalar_tac⟩
        rw [i12_post]
        apply next
        simp only [view, Spec.Keccak.feed, he, ↓reduceIte, x_post, inLane]; rfl
      · simp only [boundary, ↓reduceIte, bind_ok, uncurry]
        step*
        have he : state.pos.val + 1 ≠ 136 := by
          intro bad; apply boundary; apply UScalar.eq_of_val_eq; rw [i10_post, bad]; simp [shake256.RATE]
        refine ⟨by scalar_tac, by scalar_tac, ?_, by scalar_tac⟩
        rw [i12_post]
        apply next
        simp [view, Spec.Keccak.feed, inLane, i10_post, he]
    · simp only [step_simps]
      have endAt : k.val = data.val.length := by scalar_tac
      have stop : (bytes data.val).drop k.val = [] := List.drop_eq_nil_of_le (by simp [endAt])
      simpa only [stop, List.foldl_nil, target] using And.intro acc hpos
  · exact ⟨hi, hs, rfl⟩

@[step] theorem absorb_spec (s : shake256.Sponge) (data : Slice U8) (hs : s.pos.val < 136) :
    shake256.Sponge.absorb s data ⦃ out =>
      view out = (bytes data.val).foldl Spec.Keccak.feed (view s) ∧ out.pos.val < 136 ⦄ := by
  unfold shake256.Sponge.absorb
  simpa using absorb_loop_spec data s 0#usize (by simp) hs

private theorem put_prefix (out : Slice U8) (i : Usize) (x : U8) (hi : i.val < out.length) :
    bytes ((out.set i x).val.take (i.val+1)) =
    bytes (out.val.take i.val) ++ [x.bv] := by
  rw [Slice.set_val_eq, List.take_succ_eq_append_getElem (by simpa),
    List.take_set_of_le (le_refl i.val), List.getElem_set_self]
  simp

private def emits (a : Array U64 25#usize) (out : Slice U8) (pos i : Nat) : Spec.Bytes :=
  bytes (out.val.take i) ++ Spec.Keccak.squeeze (words a) pos (out.length - i)

private theorem emit_step (block a : Array U64 25#usize) (buf : Slice U8) (pos atPos idx : Usize)
    (byte : U8) (valid : idx.val < buf.length)
    (next : (words block, atPos.val) = (if pos.val = 136 then (Spec.Keccak.permute (words a), 0) else (words a, pos.val)))
    (byteEq : byte.bv = Spec.Keccak.extractByte (words block) atPos.val) :
    emits block (buf.set idx byte) (atPos.val+1) (idx.val+1) = emits a buf pos.val idx.val := by
  unfold emits
  rw [put_prefix _ _ _ valid]
  have count : buf.length - idx.val = (buf.length - (idx.val+1)) + 1 := by omega
  rw [count, Spec.Keccak.squeeze, ← next]
  simp [byteEq, Slice.length]

private theorem squeeze_loop_spec (initial : Array U64 25#usize) (out : Slice U8) :
    shake256.Sponge.finish_loop initial out 0#usize 0#usize ⦃ r =>
      bytes r.val = Spec.Keccak.squeeze (words initial) 0 out.length ⦄ := by
  let target := Spec.Keccak.squeeze (words initial) 0 out.length
  unfold shake256.Sponge.finish_loop
  apply loop.spec_decr_nat
    (measure := fun (p : Array U64 25#usize × Slice U8 × Usize × Usize) => out.length - p.2.2.2.val)
    (inv := fun p => p.2.1.length = out.length ∧ p.2.2.2.val ≤ out.length ∧
      p.2.2.1.val ≤ 136 ∧ emits p.1 p.2.1 p.2.2.1.val p.2.2.2.val = target)
  · rintro ⟨a,buf,pos,idx⟩ ⟨len, bound, rate, acc⟩
    simp only at len bound rate acc
    simp only [shake256.Sponge.finish_loop.body, step_simps]
    spec_split
    · have valid : idx.val < buf.length := by scalar_tac
      have run : (if pos = shake256.RATE then do
          let a' ← shake256.permute a
          ok (a', 0#usize) else ok (a,pos)) ⦃ pair =>
          pair.2.val < 136 ∧ (words pair.1, pair.2.val) =
            (if pos.val = 136 then (Spec.Keccak.permute (words a), 0) else (words a, pos.val)) ⦄ := by
        by_cases atEnd : pos = shake256.RATE
        · subst pos; simp only [↓reduceIte]; step*; simp [shake256.RATE, *]
        · have endNe : pos.val ≠ 136 := by
            intro he; apply atEnd; apply UScalar.eq_of_val_eq; simp [he, shake256.RATE]
          simp [atEnd, endNe]; omega
      let* ⟨block, atPos, fits, next⟩ ← run
      step*
      refine ⟨by scalar_tac, by scalar_tac, by scalar_tac, ?_, by scalar_tac⟩
      rw [s_post, pos2_post, i8_post, ← acc]
      apply emit_step _ _ _ _ _ _ _ valid next
      simp only [Spec.Keccak.extractByte, words_get block (atPos.val/8) (by scalar_tac),
        *, UScalar.cast_bv_eq]
      rfl
    · simp only [step_simps]
      have doneAt : idx.val = buf.length := by scalar_tac
      simpa [emits, doneAt, Spec.Keccak.squeeze, Slice.length, target] using acc
  · simp [emits, target]

/-- Padding and squeezing for an arbitrary output length, including the
shared suffix/end-bit byte at rate position 135. -/
@[step] theorem finish_spec (s : shake256.Sponge) (out : Slice U8) (hs : s.pos.val < 136) :
    shake256.Sponge.finish s out ⦃ r =>
      bytes r.val = Spec.Keccak.squeeze (Spec.Keccak.finalize (view s)) 0 out.length ⦄ := by
  unfold shake256.Sponge.finish
  simp only [shake256.RATE]
  step*
  apply WP.spec_mono (squeeze_loop_spec _ out)
  intro r hr
  rw [hr, a2_post, Spec.Keccak.finalize]
  congr 2
  have ha : words a = Spec.Keccak.xorByte (words s.lanes) s.pos.val 31 := by
    rw [a_post, words_set, Spec.Keccak.xorByte]
    simp only [*, words_get s.lanes (s.pos.val/8) (by scalar_tac)]
    rfl
  have addr : i8.val = 16 := by scalar_tac
  rw [a1_post, words_set]
  unfold view
  simp only
  rw [← ha, Spec.Keccak.xorByte]
  simp only [addr, words_get a 16 (by decide), i10_post1, i9_post, i6_post1]
  rfl

/-- The production SHAKE256 routine refines the byte-oriented FIPS 202
specification for every input slice and every output buffer size. -/
@[step] theorem shake256_spec (input out : Slice U8) :
    shake256.shake256 input out ⦃ r => bytes r.val = Spec.shake256 (bytes input.val) out.length ⦄ := by
  unfold shake256.shake256
  let* ⟨s, init, hs⟩ ← new_spec
  let* ⟨s', feed, hs'⟩ ← absorb_spec s input hs
  simpa only [Spec.shake256, feed, init] using finish_spec s' out hs'
#print axioms shake256_spec

end slhdsa.Keccak
