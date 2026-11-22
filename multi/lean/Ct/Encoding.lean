import Ct.Tactic
import Ct.Erase

/-!
# Constant time: `encoding.rs` (generic part)

(Adapted from the main tree's `lean/Ct/Encoding.lean`: here the codec is generic, with the DER
prefix and the buffers as slices; the per-set wrappers and the headline statements are in
`Ct/Sets/*.lean`.)

* `secret_keys_equal`: nothing about the two keys reaches the trace (the loop reads every byte
  and only combines them with `^` and `|`); only their lengths.
* `der_encode`: nothing about the key (or the previous contents of the output buffer) reaches
  the trace; only the prefix (public, a constant of the set) and the lengths.
* `secret_key_from`, `public_key_from`, `signature_len_ok`: the trace is determined by the
  input's length (and the buffer's).
* `der_decode`: the trace is determined by the input's length and its first `|prefix|` bytes,
  the ASN.1 structure that precedes the key. Where the input first differs from the expected
  prefix is revealed; the key bytes are not.
-/

open Aeneas Aeneas.Std Ct

set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Ct.Encoding

open slhdsa_leak

/-! ## Lengths only -/

@[ct_rel] theorem secret_key_from (b b' sk sk' : Slice U8) (h : b.length = b'.length)
    (hs : sk.length = sk'.length) :
    Rel (encoding.secret_key_from b sk) (encoding.secret_key_from b' sk')
      (fun p q => p.1 = q.1 ∧ p.2.length = q.2.length) := by
  unfold encoding.secret_key_from
  simp only [(Ct.Facts.slice_len_congr h).symm, (Ct.Facts.slice_len_congr hs).symm]
  ct_steps
  all_goals ct_side

@[ct_rel] theorem public_key_from (b b' pk pk' : Slice U8) (h : b.length = b'.length)
    (hs : pk.length = pk'.length) :
    Rel (encoding.public_key_from b pk) (encoding.public_key_from b' pk')
      (fun p q => p.1 = q.1 ∧ p.2.length = q.2.length) := by
  unfold encoding.public_key_from
  simp only [(Ct.Facts.slice_len_congr h).symm, (Ct.Facts.slice_len_congr hs).symm]
  ct_steps
  all_goals ct_side

@[ct_rel] theorem signature_len_ok (p : slhdsa.params.Params) (b b' : Slice U8)
    (h : b.length = b'.length) :
    Rel (encoding.signature_len_ok p b) (encoding.signature_len_ok p b') (fun _ _ => True) := by
  unfold encoding.signature_len_ok
  simp only [(Ct.Facts.slice_len_congr h).symm]
  ct_steps

/-! ## Nothing but lengths -/

theorem secret_keys_equal_loop_body (a b a' b' : Slice U8) (ha : a.length = a'.length)
    (hb : b.length = b'.length) (d d' : U8) (i : Usize) :
    Rel (encoding.secret_keys_equal_loop.body a b d i)
      (encoding.secret_keys_equal_loop.body a' b' d' i)
      (CFRel (fun p q => p.2 = q.2) (fun _ _ => True)) := by
  unfold encoding.secret_keys_equal_loop.body
  simp only [(Ct.Facts.slice_len_congr ha).symm]
  ct_steps
  all_goals simp_all

@[ct_rel] theorem secret_keys_equal_loop (a b a' b' : Slice U8) (ha : a.length = a'.length)
    (hb : b.length = b'.length) (d d' : U8) (i : Usize) :
    Rel (encoding.secret_keys_equal_loop a b d i) (encoding.secret_keys_equal_loop a' b' d' i)
      (fun _ _ => True) := by
  unfold encoding.secret_keys_equal_loop
  refine Rel.loop (fun p q => p.2 = q.2) ?_ rfl
  rintro ⟨x, j⟩ ⟨x', j'⟩ (rfl : j = j')
  exact secret_keys_equal_loop_body a b a' b' ha hb x x' j

@[ct_rel] theorem secret_keys_equal (a b a' b' : Slice U8) (ha : a.length = a'.length)
    (hb : b.length = b'.length) :
    Rel (encoding.secret_keys_equal a b) (encoding.secret_keys_equal a' b') (fun _ _ => True) := by
  unfold encoding.secret_keys_equal
  ct_steps

set_option maxHeartbeats 1000000 in
@[ct_rel] theorem der_encode (pre key key' out out' : Slice U8) (hk : key.length = key'.length)
    (ho : out.length = out'.length) :
    Rel (encoding.der_encode pre key out) (encoding.der_encode pre key' out')
      (fun p q => p.length = q.length) := by
  unfold encoding.der_encode
  simp only [(Ct.Facts.slice_len_congr hk).symm]
  ct_steps
  all_goals ct_side

/-! ## The decoder: the length and the prefix -/

theorem slice_index_ok {s : Slice U8} {i : Usize} {x : U8}
    (h : Aeneas.Std.Slice.index_usize s i = Aeneas.Std.Result.ok x) :
    x = s.val[i.val]! := by
  simp only [Aeneas.Std.Slice.index_usize] at h
  split at h
  · simp at h
  · rename_i y hy
    simp only [Aeneas.Std.Result.ok.injEq] at h
    subst h
    rw [Aeneas.Std.Slice.getElem?_Usize_eq] at hy
    simp [List.getElem!_eq_getElem?_getD, hy]

theorem der_decode_loop_body (pre der der' key key' : Slice U8) (l : Usize) (i : Usize)
    (h : der.length = der'.length) (hk : key.length = key'.length)
    (hp : ∀ j < l.val, der.val[j]! = der'.val[j]!) :
    Rel (encoding.der_decode_loop.body pre der key l i)
      (encoding.der_decode_loop.body pre der' key' l i)
      (CFRel (fun p q => p = q) (fun p q => p.1 = q.1)) := by
  unfold encoding.der_decode_loop.body
  simp only [(Ct.Facts.slice_len_congr h).symm]
  ct_steps
  all_goals first | ct_side | skip
  rename_i hlt _ x y hx hy _ _
  have e1 := slice_index_ok hx
  have e2 := slice_index_ok hy
  have e3 := hp i.val (by simpa [UScalar.lt_equiv] using hlt)
  rw [e1, e2, e3]

@[ct_rel] theorem der_decode_loop (pre der der' key key' : Slice U8) (l : Usize) (i : Usize)
    (h : der.length = der'.length) (hk : key.length = key'.length)
    (hp : ∀ j < l.val, der.val[j]! = der'.val[j]!) :
    Rel (encoding.der_decode_loop pre der key l i) (encoding.der_decode_loop pre der' key' l i)
      (fun p q => p.1 = q.1) := by
  unfold encoding.der_decode_loop
  refine Rel.loop (fun p q => p = q) ?_ rfl
  rintro j j' (rfl : j = j')
  exact der_decode_loop_body pre der der' key key' l j h hk hp

@[ct_rel] theorem der_decode (pre der der' key key' : Slice U8) (h : der.length = der'.length)
    (hk : key.length = key'.length) (hp : ∀ j < pre.length, der.val[j]! = der'.val[j]!) :
    Rel (encoding.der_decode pre der key) (encoding.der_decode pre der' key')
      (fun p q => p.1 = q.1) := by
  unfold encoding.der_decode
  simp only [(Ct.Facts.slice_len_congr h).symm, (Ct.Facts.slice_len_congr hk).symm]
  ct_steps
  all_goals first | ct_side | skip

theorem getElem!_of_take_eq {l l' : List U8} {n : Nat} (h : l.take n = l'.take n) :
    ∀ j < n, l[j]! = l'[j]! := by
  intro j hj
  have := congrArg (fun x : List U8 => x[j]?) h
  simp only [List.getElem?_take, hj, ite_true] at this
  simp [List.getElem!_eq_getElem?_getD, this]

end Ct.Encoding
