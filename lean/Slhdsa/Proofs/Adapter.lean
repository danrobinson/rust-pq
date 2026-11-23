import Slhdsa.Proofs.Api
import Slhdsa.Proofs.Encoding
import Spec.Correctness
open Aeneas Aeneas.Std Result

/-! The decisions of the RustCrypto-style adapter (`rust/src/adapter.rs`), for
any valid parameter set: what each function computes, against FIPS 205
(`Spec`) and the byte-level facts of `Spec/Keys.lean`. -/

namespace slhdsa

/-- The randomness the adapter's signers use: the caller's `addrnd` if there is
one (`has`), or `PK.seed` (the third block of the private key). -/
def randS (P : Spec.Params) (sk : Spec.Bytes) (has : Bool) (addrnd : Slice U8) : Spec.Bytes :=
  if has then bytes addrnd.val else Spec.block P sk 2

@[step]
theorem adapter_append_spec (m : alloc.vec.Vec U8) (part : Slice U8)
    (h : m.length + part.length ≤ Usize.max) :
    adapter.append m part ⦃ r => r.val = m.val ++ part.val ⦄ := by
  unfold adapter.append
  exact extend_from_slice_u8_spec m part h

@[step]
theorem adapter_randomizer_spec {N : Usize} (p : params.Params) (hp : PN p N) (sk : Slice U8)
    (has : Bool) (addrnd : Slice U8) (hsk : sk.length = 4 * N.val)
    (hr : has = true → addrnd.length = N.val) :
    adapter.randomizer N sk has addrnd ⦃ a => bytes a.val = randS (paramsS p) (bytes sk.val) has addrnd ⦄ := by
  unfold adapter.randomizer
  have := hp.le32
  cases has with
  | false =>
    step
    simp only [Bool.false_eq_true, ↓reduceIte]
    let* ⟨ b, b_post ⟩ ← block_spec
    simp only [randS, Bool.false_eq_true, ↓reduceIte]
    exact bytes_block_N p hp sk b 2 b_post
  | true =>
    have hl := hr rfl
    step
    simp only [↓reduceIte]
    let* ⟨ r1, r1_post ⟩ ← block_spec
    have := bytes_block_N p hp addrnd r1 0 r1_post
    rw [this]
    simp only [randS, ↓reduceIte, Spec.block, Nat.zero_mul, List.drop_zero]
    have hl' : addrnd.val.length = N.val := hl
    rw [List.take_of_length_le (by simp only [bytes_length, hp.n]; omega)]

/-- A randomizer of the wrong length fails its `assert!`. -/
theorem adapter_randomizer_panic (N : Usize) (sk r : Slice U8) (h : r.length ≠ N.val) :
    adapter.randomizer N sk true r = fail .assertionFailure := by
  unfold adapter.randomizer
  have : ¬ (r.len = N) := by
    intro e; apply h; have := congrArg UScalar.val e; simpa using this
  simp [massert, this]

/-- **Signing through the adapter.** A context of more than 255 bytes is
refused, with `sig` untouched; otherwise `sig` receives the signature of
Algorithm 22 with the adapter's randomness. -/
@[step]
theorem adapter_sign_into_spec {N : Usize} (p : params.Params) (hp : PN p N)
    (m ctx sk : Slice U8) (has : Bool) (addrnd : Slice U8) (sig : Slice U8)
    (hsk : sk.length = 4 * N.val) (hsig : sig.length = (paramsS p).sigBytes)
    (hr : has = true → addrnd.length = N.val) (hm : Room m.length (msgSlack N.val + 257)) :
    adapter.sign_into N p m ctx sk has addrnd sig ⦃ r =>
      (r.1 = true ↔ ctx.length ≤ 255) ∧
      (r.1 = true → Spec.slhSign (paramsS p) (bytes m.val) (bytes ctx.val) (bytes sk.val)
          (randS (paramsS p) (bytes sk.val) has addrnd) = some (bytes r.2.val)) ∧
      (r.1 = false → r.2 = sig) ⦄ := by
  unfold adapter.sign_into
  simp only
  split
  · rename_i hc
    have : ¬ ctx.length ≤ 255 := by scalar_tac
    simp [this]
  · rename_i hc
    have hc' : ctx.length ≤ 255 := by scalar_tac
    have hm' := hm
    simp only [Room] at hm'
    let* ⟨ rand, rand_post ⟩ ← adapter_randomizer_spec p hp sk has addrnd hsk hr
    let* ⟨ mp, mp_post, mp_len ⟩ ← with_context_spec m ctx hc' (by omega)
    have hl : (alloc.vec.Vec.deref mp).length = 2 + ctx.length + m.length := by
      simpa [alloc.vec.Vec.deref, Slice.length] using mp_len
    have hroom : Room (alloc.vec.Vec.deref mp).length (msgSlack N.val) := by
      simp only [Room] at hm ⊢; rw [hl]; omega
    let* ⟨ s, s_post, s_len ⟩ ← slh_sign_internal_spec p hp (alloc.vec.Vec.deref mp) sk rand hsk hroom
    step*
    have hnot : ¬ (bytes ctx.val).length > 255 := by simp; scalar_tac
    refine ⟨by simp [hc'], fun _ => ?_, fun h => by simp at h⟩
    simp only [Spec.slhSign, hnot, ↓reduceIte, Option.some.injEq]
    rw [sig1_post, ← rand_post, ← mp_post]
    simpa [alloc.vec.Vec.deref] using s_post.symm

/-- The context test comes first: a long context is refused whatever the other
arguments, a randomizer of the wrong length included. -/
theorem adapter_sign_into_long_ctx (N : Usize) (p : params.Params) (m ctx sk : Slice U8)
    (has : Bool) (addrnd : Slice U8) (sig : Slice U8) (hc : 255 < ctx.length) :
    adapter.sign_into N p m ctx sk has addrnd sig = ok (false, sig) := by
  unfold adapter.sign_into
  have : Slice.len ctx > 255#usize := by simp [GT.gt, UScalar.lt_equiv]; scalar_tac
  simp [this]

/-- **Signing without context through the adapter**: `sig` receives the
signature of Algorithm 19 with the adapter's randomness. -/
@[step]
theorem adapter_sign_internal_into_spec {N : Usize} (p : params.Params) (hp : PN p N)
    (m sk : Slice U8) (has : Bool) (addrnd : Slice U8) (sig : Slice U8)
    (hsk : sk.length = 4 * N.val) (hsig : sig.length = (paramsS p).sigBytes)
    (hr : has = true → addrnd.length = N.val) (hm : Room m.length (msgSlack N.val)) :
    adapter.sign_internal_into N p m sk has addrnd sig ⦃ r =>
      bytes r.val = Spec.slhSignInternal (paramsS p) (bytes m.val) (bytes sk.val)
        (randS (paramsS p) (bytes sk.val) has addrnd) ⦄ := by
  unfold adapter.sign_internal_into
  let* ⟨ rand, rand_post ⟩ ← adapter_randomizer_spec p hp sk has addrnd hsk hr
  let* ⟨ s, s_post, s_len ⟩ ← slh_sign_internal_spec p hp m sk rand hsk hm
  step*
  rw [r_post, ← rand_post, ← s_post]
  simp [alloc.vec.Vec.deref]

/-- **Key generation from three separate seeds**: Algorithm 18. -/
@[step]
theorem adapter_keygen_seeds_spec {N : Usize} (p : params.Params) (hp : PN p N)
    (sk_seed sk_prf pk_seed sk pk : Slice U8)
    (h1 : sk_seed.length = N.val) (h2 : sk_prf.length = N.val) (h3 : pk_seed.length = N.val)
    (hsk : sk.length = 4 * N.val) (hpk : pk.length = 2 * N.val) :
    adapter.keygen_seeds N p sk_seed sk_prf pk_seed sk pk ⦃ r =>
      (bytes r.1.val, bytes r.2.val) =
        Spec.slhKeygenInternal (paramsS p) (bytes sk_seed.val) (bytes sk_prf.val) (bytes pk_seed.val) ⦄ := by
  unfold adapter.keygen_seeds
  have := hp.le32
  step*
  · have e : ∀ (s : Slice U8) (b : Array U8 N), s.length = N.val →
        b.val = (s.val.drop (0 * N.val)).take N.val → bytes b.val = bytes s.val := by
      intro s b hs hb
      have hs' : s.val.length = N.val := hs
      rw [hb, Nat.zero_mul, List.drop_zero, List.take_of_length_le (by omega)]
    rw [r_post, e _ _ h1 a_post, e _ _ h2 b_post, e _ _ h3 c_post]

/-- Seeds of the wrong length fail the `assert!`. -/
theorem adapter_keygen_seeds_panic (N : Usize) (p : params.Params) (sk_seed sk_prf pk_seed sk pk : Slice U8)
    (h : ¬ (sk_seed.length = N.val ∧ sk_prf.length = N.val ∧ pk_seed.length = N.val)) :
    adapter.keygen_seeds N p sk_seed sk_prf pk_seed sk pk = fail .assertionFailure := by
  unfold adapter.keygen_seeds
  have e : ∀ s : Slice U8, (s.len = N) ↔ s.length = N.val := by
    intro s; constructor
    · intro e; have := congrArg UScalar.val e; simpa using this
    · intro e; apply UScalar.eq_of_val_eq; simpa using e
  by_cases h1 : sk_seed.length = N.val
  · by_cases h2 : sk_prf.length = N.val
    · have h3 : ¬ pk_seed.length = N.val := fun h3 => h ⟨h1, h2, h3⟩
      simp [massert, (e _).2 h1, (e _).2 h2, show ¬ (pk_seed.len = N) from fun x => h3 ((e _).1 x)]
    · simp [massert, (e _).2 h1, show ¬ (sk_prf.len = N) from fun x => h2 ((e _).1 x)]
  · simp [massert, show ¬ (sk_seed.len = N) from fun x => h1 ((e _).1 x)]

/-- **A private key from bytes**: exactly the `4n`-byte strings are accepted;
the public key is then the one the private key holds. -/
@[step]
theorem adapter_signing_key_from_spec {N : Usize} (p : params.Params) (hp : PN p N) (b sk pk : Slice U8)
    (hsk : sk.length = 4 * N.val) (hpk : pk.length = 2 * N.val) :
    adapter.signing_key_from N b sk pk ⦃ r =>
      (r.1 = true ↔ b.length = 4 * N.val) ∧
      (r.1 = true → r.2.1.val = b.val ∧ bytes r.2.2.val = Spec.skPk (paramsS p) (bytes b.val)) ∧
      (r.1 = false → r.2.1 = sk ∧ r.2.2 = pk) ⦄ := by
  unfold adapter.signing_key_from
  let* ⟨ ok1, sk1, h1, h2, h3 ⟩ ← enc_secret_key_from_spec
  split
  · rename_i hok
    have hb : b.length = sk.length := by rw [h1] at hok; simpa using hok
    have hs : sk1.val = b.val := h2 hok
    have hs1 : sk1.length = 4 * N.val := by
      simp only [Slice.length] at hb hsk ⊢; rw [hs]; omega
    let* ⟨ pk1, pk1_post, pk1_len ⟩ ← api_public_key_spec p hp sk1 pk hs1 hpk
    refine ⟨?_, fun _ => ⟨hs, ?_⟩, fun h => by simp at h⟩
    · simp only [true_iff]; simp only [Slice.length] at hb hsk ⊢; omega
    · rw [pk1_post, hs]
  · rename_i hok
    have hf : ok1 = false := by simpa using hok
    have hb : ¬ b.length = sk.length := by rw [h1] at hf; simpa using hf
    simp only [WP.spec_ok]
    refine ⟨?_, fun h => by simp at h, fun _ => by simp [h3 hf]⟩
    simp only [Bool.false_eq_true, false_iff]
    intro e; apply hb; simp only [Slice.length] at e hsk ⊢; omega

/-- **A signature from bytes**: exactly the strings of the length of Table 2. -/
@[step]
theorem adapter_signature_from_spec (p : params.Params) (hv : (paramsS p).Valid) (b sig : Slice U8)
    (hsig : sig.length = (paramsS p).sigBytes) :
    adapter.signature_from p b sig ⦃ r =>
      (r.1 = true ↔ b.length = (paramsS p).sigBytes) ∧
      (r.1 = true → r.2.val = b.val) ∧ (r.1 = false → r.2 = sig) ⦄ := by
  unfold adapter.signature_from
  let* ⟨ ok1, ok1_post ⟩ ← enc_signature_len_ok_spec p hv b
  split
  · rename_i hok
    have hb : b.length = (paramsS p).sigBytes := by simpa [ok1_post] using hok
    step*
  · rename_i hok
    have hb : ¬ b.length = (paramsS p).sigBytes := by simpa [ok1_post] using hok
    simp [hb]

/-- **Comparison of public byte strings**: equality. -/
@[step]
theorem adapter_bytes_equal_spec (a b : Slice U8) :
    adapter.bytes_equal a b ⦃ r => r = decide (a.val = b.val) ⦄ := by
  unfold adapter.bytes_equal
  simp only
  split
  · rename_i h
    have hne : a.length ≠ b.length := by
      intro e; apply absurd h; simp [Slice.len]; exact e
    have : a.val ≠ b.val := fun e => hne (by simp [Slice.length, e])
    simp [this]
  · rename_i h
    have hl : a.length = b.length := by simpa [Slice.len] using h
    exact enc_secret_keys_equal_spec a b hl

end slhdsa
