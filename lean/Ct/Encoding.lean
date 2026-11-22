import Ct.Tactic
import Ct.Erase
import Slhdsa.EncodingTheorems

/-!
# Constant time: `encoding.rs`

* `secret_keys_equal`: nothing about the two keys reaches the trace (the loop reads every byte
  and only combines them with `^` and `|`).
* `pkcs8_encode`, `spki_encode`: nothing about the key (or the previous contents of the output
  buffer) reaches the trace.
* `secret_key_from`, `public_key_from`, `signature_len_ok`: the trace is determined by the
  input's length.
* `pkcs8_decode`, `spki_decode`: the trace is determined by the input's length and its first
  20 (18) bytes, the ASN.1 structure that precedes the key. Where the input first differs from
  the expected prefix is revealed; the key bytes are not.
-/

open Aeneas Aeneas.Std Ct

set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Ct.Encoding

open slhdsa_leak

/-! ## Lengths only -/

@[ct_rel] theorem secret_key_from (b b' : Slice U8) (h : b.length = b'.length) :
    Rel (encoding.secret_key_from b) (encoding.secret_key_from b') (fun _ _ => True) := by
  unfold encoding.secret_key_from
  simp only [(Ct.Facts.slice_len_congr h).symm]
  ct_steps
  all_goals (ct_facts; simp_all)

@[ct_rel] theorem public_key_from (b b' : Slice U8) (h : b.length = b'.length) :
    Rel (encoding.public_key_from b) (encoding.public_key_from b') (fun _ _ => True) := by
  unfold encoding.public_key_from
  simp only [(Ct.Facts.slice_len_congr h).symm]
  ct_steps
  all_goals (ct_facts; simp_all)

@[ct_rel] theorem signature_len_ok (b b' : Slice U8) (h : b.length = b'.length) :
    Rel (encoding.signature_len_ok b) (encoding.signature_len_ok b') (fun _ _ => True) := by
  unfold encoding.signature_len_ok
  simp only [(Ct.Facts.slice_len_congr h).symm]
  ct_steps
  all_goals (ct_facts; simp_all)

/-! ## Nothing -/

theorem secret_keys_equal_loop_body (a b a' b' : Std.Array U8 64#usize) (d d' : U8) (i : Usize) :
    Rel (encoding.secret_keys_equal_loop.body a b d i)
      (encoding.secret_keys_equal_loop.body a' b' d' i)
      (CFRel (fun p q => p.2 = q.2) (fun _ _ => True)) := by
  unfold encoding.secret_keys_equal_loop.body
  ct_steps
  all_goals simp_all

@[ct_rel] theorem secret_keys_equal_loop (a b a' b' : Std.Array U8 64#usize) (d d' : U8)
    (i : Usize) :
    Rel (encoding.secret_keys_equal_loop a b d i) (encoding.secret_keys_equal_loop a' b' d' i)
      (fun _ _ => True) := by
  unfold encoding.secret_keys_equal_loop
  refine Rel.loop (fun p q => p.2 = q.2) ?_ rfl
  rintro ⟨x, j⟩ ⟨x', j'⟩ (rfl : j = j')
  exact secret_keys_equal_loop_body a b a' b' x x' j

@[ct_rel] theorem secret_keys_equal (a b a' b' : Std.Array U8 64#usize) :
    Rel (encoding.secret_keys_equal a b) (encoding.secret_keys_equal a' b') (fun _ _ => True) := by
  unfold encoding.secret_keys_equal
  ct_steps
  all_goals simp_all

@[ct_rel] theorem pkcs8_encode (sk sk' : Std.Array U8 64#usize) (out out' : Std.Array U8 84#usize) :
    Rel (encoding.pkcs8_encode sk out) (encoding.pkcs8_encode sk' out') (fun _ _ => True) := by
  unfold encoding.pkcs8_encode
  ct_steps
  all_goals (ct_facts; simp_all)

@[ct_rel] theorem spki_encode (pk pk' : Std.Array U8 32#usize) :
    Rel (encoding.spki_encode pk) (encoding.spki_encode pk') (fun _ _ => True) := by
  unfold encoding.spki_encode
  ct_steps
  all_goals (ct_facts; simp_all)

/-! ## The decoders: the length and the prefix -/

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

theorem pkcs8_decode_loop_body (der der' : Slice U8) (sk sk' : Std.Array U8 64#usize) (i : Usize)
    (h : der.length = der'.length) (hp : ∀ j < 20, der.val[j]! = der'.val[j]!) :
    Rel (encoding.pkcs8_decode_loop.body der sk i) (encoding.pkcs8_decode_loop.body der' sk' i)
      (CFRel (fun p q => p = q) (fun _ _ => True)) := by
  unfold encoding.pkcs8_decode_loop.body
  ct_steps
  all_goals (ct_facts; simp_all)
  rename_i x y p hlt hx hy _
  have e1 := slice_index_ok hx
  have e2 := slice_index_ok hy
  have e3 := hp i.val hlt
  simp_all

@[ct_rel] theorem pkcs8_decode_loop (der der' : Slice U8) (sk sk' : Std.Array U8 64#usize)
    (i : Usize) (h : der.length = der'.length) (hp : ∀ j < 20, der.val[j]! = der'.val[j]!) :
    Rel (encoding.pkcs8_decode_loop der sk i) (encoding.pkcs8_decode_loop der' sk' i)
      (fun _ _ => True) := by
  unfold encoding.pkcs8_decode_loop
  refine Rel.loop (fun p q => p = q) ?_ rfl
  rintro j j' (rfl : j = j')
  exact pkcs8_decode_loop_body der der' sk sk' j h hp

@[ct_rel] theorem pkcs8_decode (der der' : Slice U8) (sk sk' : Std.Array U8 64#usize)
    (h : der.length = der'.length) (hp : ∀ j < 20, der.val[j]! = der'.val[j]!) :
    Rel (encoding.pkcs8_decode der sk) (encoding.pkcs8_decode der' sk') (fun _ _ => True) := by
  unfold encoding.pkcs8_decode
  simp only [(Ct.Facts.slice_len_congr h).symm]
  ct_steps
  all_goals (ct_facts; simp_all)

theorem spki_decode_loop_body (der der' : Slice U8) (i : Usize)
    (h : der.length = der'.length) (hp : ∀ j < 18, der.val[j]! = der'.val[j]!) :
    Rel (encoding.spki_decode_loop.body der i) (encoding.spki_decode_loop.body der' i)
      (CFRel (fun p q => p = q) (fun _ _ => True)) := by
  unfold encoding.spki_decode_loop.body
  ct_steps
  all_goals (ct_facts; simp_all)
  rename_i x y p hlt hx hy _
  have e1 := slice_index_ok hx
  have e2 := slice_index_ok hy
  have e3 := hp i.val hlt
  simp_all

@[ct_rel] theorem spki_decode_loop (der der' : Slice U8) (i : Usize)
    (h : der.length = der'.length) (hp : ∀ j < 18, der.val[j]! = der'.val[j]!) :
    Rel (encoding.spki_decode_loop der i) (encoding.spki_decode_loop der' i) (fun _ _ => True) := by
  unfold encoding.spki_decode_loop
  refine Rel.loop (fun p q => p = q) ?_ rfl
  rintro j j' (rfl : j = j')
  exact spki_decode_loop_body der der' j h hp

@[ct_rel] theorem spki_decode (der der' : Slice U8) (h : der.length = der'.length)
    (hp : ∀ j < 18, der.val[j]! = der'.val[j]!) :
    Rel (encoding.spki_decode der) (encoding.spki_decode der') (fun _ _ => True) := by
  unfold encoding.spki_decode
  simp only [(Ct.Facts.slice_len_congr h).symm]
  ct_steps
  all_goals (ct_facts; simp_all)

theorem getElem!_of_take_eq {l l' : List U8} {n : Nat} (h : l.take n = l'.take n) :
    ∀ j < n, l[j]! = l'[j]! := by
  intro j hj
  have := congrArg (fun x : List U8 => x[j]?) h
  simp only [List.getElem?_take, hj, ite_true] at this
  simp [List.getElem!_eq_getElem?_getD, this]

/-! ## Headline statements

A run returning `(r, t)` returns `r` with trace `t`. The first group is the relational
statements: any two runs that return, on inputs that agree on what is named, have the same
trace. The second group adds that the runs do return, with the results of the functional
theorems (`Slhdsa/EncodingTheorems.lean`). -/

/-- Comparing two private keys: the same trace whatever the four keys. -/
theorem secret_keys_equal_ct (a b a' b' : Std.Array U8 64#usize) :
    Rel (slhdsa_leak.encoding.secret_keys_equal a b) (slhdsa_leak.encoding.secret_keys_equal a' b')
      (fun _ _ => True) :=
  secret_keys_equal a b a' b'

/-- PKCS#8 encoding: the same trace whatever the keys and the previous buffer contents. -/
theorem pkcs8_encode_ct (sk sk' : Std.Array U8 64#usize) (out out' : Std.Array U8 84#usize) :
    Rel (slhdsa_leak.encoding.pkcs8_encode sk out) (slhdsa_leak.encoding.pkcs8_encode sk' out')
      (fun _ _ => True) :=
  pkcs8_encode sk sk' out out'

/-- SPKI encoding: the same trace whatever the keys. -/
theorem spki_encode_ct (pk pk' : Std.Array U8 32#usize) :
    Rel (slhdsa_leak.encoding.spki_encode pk) (slhdsa_leak.encoding.spki_encode pk')
      (fun _ _ => True) :=
  spki_encode pk pk'

/-- Keys and signatures from bytes: the trace is determined by the input's length. -/
theorem secret_key_from_ct (b b' : Slice U8) (h : b.length = b'.length) :
    Rel (slhdsa_leak.encoding.secret_key_from b) (slhdsa_leak.encoding.secret_key_from b')
      (fun _ _ => True) :=
  secret_key_from b b' h

theorem public_key_from_ct (b b' : Slice U8) (h : b.length = b'.length) :
    Rel (slhdsa_leak.encoding.public_key_from b) (slhdsa_leak.encoding.public_key_from b')
      (fun _ _ => True) :=
  public_key_from b b' h

theorem signature_len_ok_ct (b b' : Slice U8) (h : b.length = b'.length) :
    Rel (slhdsa_leak.encoding.signature_len_ok b) (slhdsa_leak.encoding.signature_len_ok b')
      (fun _ _ => True) :=
  signature_len_ok b b' h

/-- PKCS#8 decoding: on inputs of equal length whose first 20 bytes agree, the same trace,
whatever the remaining bytes and the previous buffer contents. -/
theorem pkcs8_decode_ct (der der' : Slice U8) (sk sk' : Std.Array U8 64#usize)
    (h : der.length = der'.length) (hp : der.val.take 20 = der'.val.take 20) :
    Rel (slhdsa_leak.encoding.pkcs8_decode der sk) (slhdsa_leak.encoding.pkcs8_decode der' sk')
      (fun _ _ => True) :=
  pkcs8_decode der der' sk sk' h (getElem!_of_take_eq hp)

/-- SPKI decoding: on inputs of equal length whose first 18 bytes agree, the same trace,
whatever the remaining bytes. -/
theorem spki_decode_ct (der der' : Slice U8) (h : der.length = der'.length)
    (hp : der.val.take 18 = der'.val.take 18) :
    Rel (slhdsa_leak.encoding.spki_decode der) (slhdsa_leak.encoding.spki_decode der')
      (fun _ _ => True) :=
  spki_decode der der' h (getElem!_of_take_eq hp)

/-- And they return: comparing keys returns whether they are equal, with one trace for all
pairs of keys. -/
theorem secret_keys_equal_trace (a b a' b' : Std.Array U8 64#usize) :
    ∃ t, (slhdsa_leak.encoding.secret_keys_equal a b).run = .ok (decide (a = b), t) ∧
      (slhdsa_leak.encoding.secret_keys_equal a' b').run = .ok (decide (a' = b'), t) := by
  obtain ⟨t, h1, h2, -⟩ := (secret_keys_equal_ct a b a' b').same_trace
    ((slhdsa_leak.encoding.secret_keys_equal.erase_eq _ _).trans
      (slhdsa.secret_keys_equal_correct a b))
    ((slhdsa_leak.encoding.secret_keys_equal.erase_eq _ _).trans
      (slhdsa.secret_keys_equal_correct a' b'))
  exact ⟨t, h1, h2⟩

/-- PKCS#8 decoding returns the verified results, with one trace for all inputs of a given
length and first 20 bytes. -/
theorem pkcs8_decode_trace (der der' : Slice U8) (sk sk' : Std.Array U8 64#usize)
    (h : der.length = der'.length) (hp : der.val.take 20 = der'.val.take 20) :
    ∃ r r' t, slhdsa.encoding.pkcs8_decode der sk = .ok r ∧
      slhdsa.encoding.pkcs8_decode der' sk' = .ok r' ∧
      (slhdsa_leak.encoding.pkcs8_decode der sk).run = .ok (r, t) ∧
      (slhdsa_leak.encoding.pkcs8_decode der' sk').run = .ok (r', t) := by
  obtain ⟨r, hr, -⟩ := slhdsa.pkcs8_decode_correct der sk
  obtain ⟨r', hr', -⟩ := slhdsa.pkcs8_decode_correct der' sk'
  obtain ⟨t, h1, h2, -⟩ := (pkcs8_decode_ct der der' sk sk' h hp).same_trace
    ((slhdsa_leak.encoding.pkcs8_decode.erase_eq _ _).trans hr)
    ((slhdsa_leak.encoding.pkcs8_decode.erase_eq _ _).trans hr')
  exact ⟨r, r', t, hr, hr', h1, h2⟩

/-- SPKI decoding: the same, with 18 bytes. -/
theorem spki_decode_trace (der der' : Slice U8) (h : der.length = der'.length)
    (hp : der.val.take 18 = der'.val.take 18) :
    ∃ r r' t, slhdsa.encoding.spki_decode der = .ok r ∧ slhdsa.encoding.spki_decode der' = .ok r' ∧
      (slhdsa_leak.encoding.spki_decode der).run = .ok (r, t) ∧
      (slhdsa_leak.encoding.spki_decode der').run = .ok (r', t) := by
  obtain ⟨r, hr, -⟩ := slhdsa.spki_decode_correct der
  obtain ⟨r', hr', -⟩ := slhdsa.spki_decode_correct der'
  obtain ⟨t, h1, h2, -⟩ := (spki_decode_ct der der' h hp).same_trace
    ((slhdsa_leak.encoding.spki_decode.erase_eq _).trans hr)
    ((slhdsa_leak.encoding.spki_decode.erase_eq _).trans hr')
  exact ⟨r, r', t, hr, hr', h1, h2⟩

end Ct.Encoding

#print axioms Ct.Encoding.secret_keys_equal_ct
#print axioms Ct.Encoding.pkcs8_encode_ct
#print axioms Ct.Encoding.spki_encode_ct
#print axioms Ct.Encoding.secret_key_from_ct
#print axioms Ct.Encoding.public_key_from_ct
#print axioms Ct.Encoding.signature_len_ok_ct
#print axioms Ct.Encoding.pkcs8_decode_ct
#print axioms Ct.Encoding.spki_decode_ct
#print axioms Ct.Encoding.secret_keys_equal_trace
#print axioms Ct.Encoding.pkcs8_decode_trace
#print axioms Ct.Encoding.spki_decode_trace
