import Slhdsa.Proofs.Sets
open Aeneas Aeneas.Std Result

/-!
# Main results

The Rust functions of the `slhdsa` crate (the optimised implementation in
`rust/`), as translated to Lean by Aeneas, never panic and compute
exactly the functions of the FIPS 205 transcription in `Spec/SlhDsa.lean`,
for each of SLH-DSA-SHA2-{128s,128f,192s,192f,256s,256f}.

`bytes` maps machine bytes to the specification's bytes. `Room len slack`
says a message of `len` bytes plus `slack` more fits in memory and its bit
length fits in SHA-256's 64-bit length field. The slack is 152 bytes for the
internal functions and 409 for the pure ones when `n = 16` (SHA-256
throughout; the same numbers as the single-set tree), and 304 / 561 when
`n = 24, 32` (SHA-512 for `H_msg` and `PRF_msg`).

* `slhdsa.sha2_128s.keygen_correct` … `slhdsa.sha2_256f.verify_correct`: five
  theorems per parameter set, about the functions with fixed-size key types
  in `sets.rs`. Their only hypothesis is `Room`.
* `slhdsa.generic.*`: the same five theorems about the generic functions of
  `slh.rs`, for any `params.Params` value `p` whose specification-level view
  satisfies `Spec.Params.Valid`, with `N = p.n` (`PN p N`). Those functions
  take slices, so the key lengths appear as hypotheses there.
-/

namespace slhdsa

/-- The Rust SHA-256 is SHA-256. -/
theorem sha256_correct (msg : Slice U8) (h : Room msg.length 72) :
    ∃ d, sha256.sha256 msg = ok d ∧ bytes d.val = Spec.sha256 (bytes msg.val) :=
  spec_imp_exists (sha256_spec msg h)

/-- The Rust SHA-512 is SHA-512. The hypothesis says only that the padded
message fits in memory. -/
theorem sha512_correct (msg : Slice U8) (h : msg.length + 144 ≤ Usize.max) :
    ∃ d, sha512.sha512 msg = ok d ∧ bytes d.val = Spec.sha512 (bytes msg.val) :=
  spec_imp_exists (sha512_spec msg h)

/-! ## The generic functions, for any valid parameter set -/

namespace generic

theorem keygen_correct {N : Usize} (p : params.Params) (hp : PN p N)
    (sk_seed sk_prf pk_seed : Array U8 N) (sk pk : Slice U8)
    (hsk : sk.length = 4 * N.val) (hpk : pk.length = 2 * N.val) :
    ∃ sk' pk', slh.slh_keygen_internal p sk_seed sk_prf pk_seed sk pk = ok (sk', pk') ∧
      (bytes sk'.val, bytes pk'.val) =
        Spec.slhKeygenInternal (paramsS p) (bytes sk_seed.val) (bytes sk_prf.val) (bytes pk_seed.val) := by
  obtain ⟨⟨sk', pk'⟩, h, hp, -⟩ :=
    spec_imp_exists (slh_keygen_internal_spec p hp sk_seed sk_prf pk_seed sk pk hsk hpk)
  exact ⟨sk', pk', h, hp⟩

theorem sign_internal_correct {N : Usize} (p : params.Params) (hp : PN p N)
    (m sk : Slice U8) (addrnd : Array U8 N) (hsk : sk.length = 4 * N.val)
    (hm : Room m.length (msgSlack N.val)) :
    ∃ sig, slh.slh_sign_internal p m sk addrnd = ok sig ∧
      bytes sig.val = Spec.slhSignInternal (paramsS p) (bytes m.val) (bytes sk.val) (bytes addrnd.val) := by
  obtain ⟨sig, h, hp, -⟩ := spec_imp_exists (slh_sign_internal_spec p hp m sk addrnd hsk hm)
  exact ⟨sig, h, hp⟩

/-- For every byte string `sig` offered as a signature. -/
theorem verify_internal_correct {N : Usize} (p : params.Params) (hp : PN p N)
    (m sig pk : Slice U8) (hpk : pk.length = 2 * N.val) (hm : Room m.length (msgSlack N.val)) :
    slh.slh_verify_internal N p m sig pk =
      ok (Spec.slhVerifyInternal (paramsS p) (bytes m.val) (bytes sig.val) (bytes pk.val)) := by
  obtain ⟨b, h, hp⟩ := spec_imp_exists (slh_verify_internal_spec p hp m sig pk hpk hm)
  rw [h, hp]

theorem sign_correct {N : Usize} (p : params.Params) (hp : PN p N)
    (m ctx sk : Slice U8) (addrnd : Array U8 N) (hsk : sk.length = 4 * N.val)
    (hm : Room m.length (msgSlack N.val + 257)) :
    ∃ r, slh.slh_sign p m ctx sk addrnd = ok r ∧
      r.map (fun v => bytes v.val) =
        Spec.slhSign (paramsS p) (bytes m.val) (bytes ctx.val) (bytes sk.val) (bytes addrnd.val) :=
  spec_imp_exists (slh_sign_spec p hp m ctx sk addrnd hsk hm)

theorem verify_correct {N : Usize} (p : params.Params) (hp : PN p N)
    (m sig ctx pk : Slice U8) (hpk : pk.length = 2 * N.val) (hm : Room m.length (msgSlack N.val + 257)) :
    slh.slh_verify N p m sig ctx pk =
      ok (Spec.slhVerify (paramsS p) (bytes m.val) (bytes sig.val) (bytes ctx.val) (bytes pk.val)) := by
  obtain ⟨b, h, hp⟩ := spec_imp_exists (slh_verify_spec p hp m sig ctx pk hpk hm)
  rw [h, hp]

end generic

/-! ## SLH-DSA-SHA2-128s -/

namespace sha2_128s

/-- Key generation: for all seeds, the Rust `sha2_128s::slh_keygen_internal`
returns the secret and public key of FIPS 205 Algorithm 18. -/
theorem keygen_correct (sk_seed sk_prf pk_seed : Array U8 16#usize) :
    ∃ sk pk, sets.sha2_128s.slh_keygen_internal sk_seed sk_prf pk_seed = ok (sk, pk) ∧
      (bytes sk.val, bytes pk.val) =
        Spec.slhKeygenInternal Spec.sha2_128s (bytes sk_seed.val) (bytes sk_prf.val)
          (bytes pk_seed.val) := by
  obtain ⟨⟨sk, pk⟩, h, hp⟩ :=
    spec_imp_exists (sha2_128s.slh_keygen_internal_spec sk_seed sk_prf pk_seed)
  exact ⟨sk, pk, h, hp⟩

/-- Signing: the Rust `sha2_128s::slh_sign_internal` returns the signature of
FIPS 205 Algorithm 19. -/
theorem sign_internal_correct (m : Slice U8) (sk : Array U8 64#usize)
    (addrnd : Array U8 16#usize) (hm : Room m.length 152) :
    ∃ sig, sets.sha2_128s.slh_sign_internal m sk addrnd = ok sig ∧
      bytes sig.val =
        Spec.slhSignInternal Spec.sha2_128s (bytes m.val) (bytes sk.val) (bytes addrnd.val) :=
  spec_imp_exists (sha2_128s.slh_sign_internal_spec m sk addrnd hm)

/-- Verification: the Rust `sha2_128s::slh_verify_internal` returns the verdict
of FIPS 205 Algorithm 20, for every byte string offered as a signature. -/
theorem verify_internal_correct (m sig : Slice U8) (pk : Array U8 32#usize)
    (hm : Room m.length 152) :
    sets.sha2_128s.slh_verify_internal m sig pk =
      ok (Spec.slhVerifyInternal Spec.sha2_128s (bytes m.val) (bytes sig.val) (bytes pk.val)) := by
  obtain ⟨b, h, hp⟩ := spec_imp_exists (sha2_128s.slh_verify_internal_spec m sig pk hm)
  rw [h, hp]

/-- Pure signing with a context string (FIPS 205 Algorithm 22). -/
theorem sign_correct (m ctx : Slice U8) (sk : Array U8 64#usize)
    (addrnd : Array U8 16#usize) (hm : Room m.length 409) :
    ∃ r, sets.sha2_128s.slh_sign m ctx sk addrnd = ok r ∧
      r.map (fun v => bytes v.val) =
        Spec.slhSign Spec.sha2_128s (bytes m.val) (bytes ctx.val) (bytes sk.val)
          (bytes addrnd.val) :=
  spec_imp_exists (sha2_128s.slh_sign_spec m ctx sk addrnd hm)

/-- Pure verification with a context string (FIPS 205 Algorithm 24). -/
theorem verify_correct (m sig ctx : Slice U8) (pk : Array U8 32#usize)
    (hm : Room m.length 409) :
    sets.sha2_128s.slh_verify m sig ctx pk =
      ok (Spec.slhVerify Spec.sha2_128s (bytes m.val) (bytes sig.val) (bytes ctx.val)
        (bytes pk.val)) := by
  obtain ⟨b, h, hp⟩ := spec_imp_exists (sha2_128s.slh_verify_spec m sig ctx pk hm)
  rw [h, hp]

end sha2_128s

/-! ## SLH-DSA-SHA2-128f -/

namespace sha2_128f

/-- Key generation: for all seeds, the Rust `sha2_128f::slh_keygen_internal`
returns the secret and public key of FIPS 205 Algorithm 18. -/
theorem keygen_correct (sk_seed sk_prf pk_seed : Array U8 16#usize) :
    ∃ sk pk, sets.sha2_128f.slh_keygen_internal sk_seed sk_prf pk_seed = ok (sk, pk) ∧
      (bytes sk.val, bytes pk.val) =
        Spec.slhKeygenInternal Spec.sha2_128f (bytes sk_seed.val) (bytes sk_prf.val)
          (bytes pk_seed.val) := by
  obtain ⟨⟨sk, pk⟩, h, hp⟩ :=
    spec_imp_exists (sha2_128f.slh_keygen_internal_spec sk_seed sk_prf pk_seed)
  exact ⟨sk, pk, h, hp⟩

/-- Signing: the Rust `sha2_128f::slh_sign_internal` returns the signature of
FIPS 205 Algorithm 19. -/
theorem sign_internal_correct (m : Slice U8) (sk : Array U8 64#usize)
    (addrnd : Array U8 16#usize) (hm : Room m.length 152) :
    ∃ sig, sets.sha2_128f.slh_sign_internal m sk addrnd = ok sig ∧
      bytes sig.val =
        Spec.slhSignInternal Spec.sha2_128f (bytes m.val) (bytes sk.val) (bytes addrnd.val) :=
  spec_imp_exists (sha2_128f.slh_sign_internal_spec m sk addrnd hm)

/-- Verification: the Rust `sha2_128f::slh_verify_internal` returns the verdict
of FIPS 205 Algorithm 20, for every byte string offered as a signature. -/
theorem verify_internal_correct (m sig : Slice U8) (pk : Array U8 32#usize)
    (hm : Room m.length 152) :
    sets.sha2_128f.slh_verify_internal m sig pk =
      ok (Spec.slhVerifyInternal Spec.sha2_128f (bytes m.val) (bytes sig.val) (bytes pk.val)) := by
  obtain ⟨b, h, hp⟩ := spec_imp_exists (sha2_128f.slh_verify_internal_spec m sig pk hm)
  rw [h, hp]

/-- Pure signing with a context string (FIPS 205 Algorithm 22). -/
theorem sign_correct (m ctx : Slice U8) (sk : Array U8 64#usize)
    (addrnd : Array U8 16#usize) (hm : Room m.length 409) :
    ∃ r, sets.sha2_128f.slh_sign m ctx sk addrnd = ok r ∧
      r.map (fun v => bytes v.val) =
        Spec.slhSign Spec.sha2_128f (bytes m.val) (bytes ctx.val) (bytes sk.val)
          (bytes addrnd.val) :=
  spec_imp_exists (sha2_128f.slh_sign_spec m ctx sk addrnd hm)

/-- Pure verification with a context string (FIPS 205 Algorithm 24). -/
theorem verify_correct (m sig ctx : Slice U8) (pk : Array U8 32#usize)
    (hm : Room m.length 409) :
    sets.sha2_128f.slh_verify m sig ctx pk =
      ok (Spec.slhVerify Spec.sha2_128f (bytes m.val) (bytes sig.val) (bytes ctx.val)
        (bytes pk.val)) := by
  obtain ⟨b, h, hp⟩ := spec_imp_exists (sha2_128f.slh_verify_spec m sig ctx pk hm)
  rw [h, hp]

end sha2_128f

/-! ## SLH-DSA-SHA2-192s -/

namespace sha2_192s

/-- Key generation: for all seeds, the Rust `sha2_192s::slh_keygen_internal`
returns the secret and public key of FIPS 205 Algorithm 18. -/
theorem keygen_correct (sk_seed sk_prf pk_seed : Array U8 24#usize) :
    ∃ sk pk, sets.sha2_192s.slh_keygen_internal sk_seed sk_prf pk_seed = ok (sk, pk) ∧
      (bytes sk.val, bytes pk.val) =
        Spec.slhKeygenInternal Spec.sha2_192s (bytes sk_seed.val) (bytes sk_prf.val)
          (bytes pk_seed.val) := by
  obtain ⟨⟨sk, pk⟩, h, hp⟩ :=
    spec_imp_exists (sha2_192s.slh_keygen_internal_spec sk_seed sk_prf pk_seed)
  exact ⟨sk, pk, h, hp⟩

/-- Signing: the Rust `sha2_192s::slh_sign_internal` returns the signature of
FIPS 205 Algorithm 19. -/
theorem sign_internal_correct (m : Slice U8) (sk : Array U8 96#usize)
    (addrnd : Array U8 24#usize) (hm : Room m.length 304) :
    ∃ sig, sets.sha2_192s.slh_sign_internal m sk addrnd = ok sig ∧
      bytes sig.val =
        Spec.slhSignInternal Spec.sha2_192s (bytes m.val) (bytes sk.val) (bytes addrnd.val) :=
  spec_imp_exists (sha2_192s.slh_sign_internal_spec m sk addrnd hm)

/-- Verification: the Rust `sha2_192s::slh_verify_internal` returns the verdict
of FIPS 205 Algorithm 20, for every byte string offered as a signature. -/
theorem verify_internal_correct (m sig : Slice U8) (pk : Array U8 48#usize)
    (hm : Room m.length 304) :
    sets.sha2_192s.slh_verify_internal m sig pk =
      ok (Spec.slhVerifyInternal Spec.sha2_192s (bytes m.val) (bytes sig.val) (bytes pk.val)) := by
  obtain ⟨b, h, hp⟩ := spec_imp_exists (sha2_192s.slh_verify_internal_spec m sig pk hm)
  rw [h, hp]

/-- Pure signing with a context string (FIPS 205 Algorithm 22). -/
theorem sign_correct (m ctx : Slice U8) (sk : Array U8 96#usize)
    (addrnd : Array U8 24#usize) (hm : Room m.length 561) :
    ∃ r, sets.sha2_192s.slh_sign m ctx sk addrnd = ok r ∧
      r.map (fun v => bytes v.val) =
        Spec.slhSign Spec.sha2_192s (bytes m.val) (bytes ctx.val) (bytes sk.val)
          (bytes addrnd.val) :=
  spec_imp_exists (sha2_192s.slh_sign_spec m ctx sk addrnd hm)

/-- Pure verification with a context string (FIPS 205 Algorithm 24). -/
theorem verify_correct (m sig ctx : Slice U8) (pk : Array U8 48#usize)
    (hm : Room m.length 561) :
    sets.sha2_192s.slh_verify m sig ctx pk =
      ok (Spec.slhVerify Spec.sha2_192s (bytes m.val) (bytes sig.val) (bytes ctx.val)
        (bytes pk.val)) := by
  obtain ⟨b, h, hp⟩ := spec_imp_exists (sha2_192s.slh_verify_spec m sig ctx pk hm)
  rw [h, hp]

end sha2_192s

/-! ## SLH-DSA-SHA2-192f -/

namespace sha2_192f

/-- Key generation: for all seeds, the Rust `sha2_192f::slh_keygen_internal`
returns the secret and public key of FIPS 205 Algorithm 18. -/
theorem keygen_correct (sk_seed sk_prf pk_seed : Array U8 24#usize) :
    ∃ sk pk, sets.sha2_192f.slh_keygen_internal sk_seed sk_prf pk_seed = ok (sk, pk) ∧
      (bytes sk.val, bytes pk.val) =
        Spec.slhKeygenInternal Spec.sha2_192f (bytes sk_seed.val) (bytes sk_prf.val)
          (bytes pk_seed.val) := by
  obtain ⟨⟨sk, pk⟩, h, hp⟩ :=
    spec_imp_exists (sha2_192f.slh_keygen_internal_spec sk_seed sk_prf pk_seed)
  exact ⟨sk, pk, h, hp⟩

/-- Signing: the Rust `sha2_192f::slh_sign_internal` returns the signature of
FIPS 205 Algorithm 19. -/
theorem sign_internal_correct (m : Slice U8) (sk : Array U8 96#usize)
    (addrnd : Array U8 24#usize) (hm : Room m.length 304) :
    ∃ sig, sets.sha2_192f.slh_sign_internal m sk addrnd = ok sig ∧
      bytes sig.val =
        Spec.slhSignInternal Spec.sha2_192f (bytes m.val) (bytes sk.val) (bytes addrnd.val) :=
  spec_imp_exists (sha2_192f.slh_sign_internal_spec m sk addrnd hm)

/-- Verification: the Rust `sha2_192f::slh_verify_internal` returns the verdict
of FIPS 205 Algorithm 20, for every byte string offered as a signature. -/
theorem verify_internal_correct (m sig : Slice U8) (pk : Array U8 48#usize)
    (hm : Room m.length 304) :
    sets.sha2_192f.slh_verify_internal m sig pk =
      ok (Spec.slhVerifyInternal Spec.sha2_192f (bytes m.val) (bytes sig.val) (bytes pk.val)) := by
  obtain ⟨b, h, hp⟩ := spec_imp_exists (sha2_192f.slh_verify_internal_spec m sig pk hm)
  rw [h, hp]

/-- Pure signing with a context string (FIPS 205 Algorithm 22). -/
theorem sign_correct (m ctx : Slice U8) (sk : Array U8 96#usize)
    (addrnd : Array U8 24#usize) (hm : Room m.length 561) :
    ∃ r, sets.sha2_192f.slh_sign m ctx sk addrnd = ok r ∧
      r.map (fun v => bytes v.val) =
        Spec.slhSign Spec.sha2_192f (bytes m.val) (bytes ctx.val) (bytes sk.val)
          (bytes addrnd.val) :=
  spec_imp_exists (sha2_192f.slh_sign_spec m ctx sk addrnd hm)

/-- Pure verification with a context string (FIPS 205 Algorithm 24). -/
theorem verify_correct (m sig ctx : Slice U8) (pk : Array U8 48#usize)
    (hm : Room m.length 561) :
    sets.sha2_192f.slh_verify m sig ctx pk =
      ok (Spec.slhVerify Spec.sha2_192f (bytes m.val) (bytes sig.val) (bytes ctx.val)
        (bytes pk.val)) := by
  obtain ⟨b, h, hp⟩ := spec_imp_exists (sha2_192f.slh_verify_spec m sig ctx pk hm)
  rw [h, hp]

end sha2_192f

/-! ## SLH-DSA-SHA2-256s -/

namespace sha2_256s

/-- Key generation: for all seeds, the Rust `sha2_256s::slh_keygen_internal`
returns the secret and public key of FIPS 205 Algorithm 18. -/
theorem keygen_correct (sk_seed sk_prf pk_seed : Array U8 32#usize) :
    ∃ sk pk, sets.sha2_256s.slh_keygen_internal sk_seed sk_prf pk_seed = ok (sk, pk) ∧
      (bytes sk.val, bytes pk.val) =
        Spec.slhKeygenInternal Spec.sha2_256s (bytes sk_seed.val) (bytes sk_prf.val)
          (bytes pk_seed.val) := by
  obtain ⟨⟨sk, pk⟩, h, hp⟩ :=
    spec_imp_exists (sha2_256s.slh_keygen_internal_spec sk_seed sk_prf pk_seed)
  exact ⟨sk, pk, h, hp⟩

/-- Signing: the Rust `sha2_256s::slh_sign_internal` returns the signature of
FIPS 205 Algorithm 19. -/
theorem sign_internal_correct (m : Slice U8) (sk : Array U8 128#usize)
    (addrnd : Array U8 32#usize) (hm : Room m.length 304) :
    ∃ sig, sets.sha2_256s.slh_sign_internal m sk addrnd = ok sig ∧
      bytes sig.val =
        Spec.slhSignInternal Spec.sha2_256s (bytes m.val) (bytes sk.val) (bytes addrnd.val) :=
  spec_imp_exists (sha2_256s.slh_sign_internal_spec m sk addrnd hm)

/-- Verification: the Rust `sha2_256s::slh_verify_internal` returns the verdict
of FIPS 205 Algorithm 20, for every byte string offered as a signature. -/
theorem verify_internal_correct (m sig : Slice U8) (pk : Array U8 64#usize)
    (hm : Room m.length 304) :
    sets.sha2_256s.slh_verify_internal m sig pk =
      ok (Spec.slhVerifyInternal Spec.sha2_256s (bytes m.val) (bytes sig.val) (bytes pk.val)) := by
  obtain ⟨b, h, hp⟩ := spec_imp_exists (sha2_256s.slh_verify_internal_spec m sig pk hm)
  rw [h, hp]

/-- Pure signing with a context string (FIPS 205 Algorithm 22). -/
theorem sign_correct (m ctx : Slice U8) (sk : Array U8 128#usize)
    (addrnd : Array U8 32#usize) (hm : Room m.length 561) :
    ∃ r, sets.sha2_256s.slh_sign m ctx sk addrnd = ok r ∧
      r.map (fun v => bytes v.val) =
        Spec.slhSign Spec.sha2_256s (bytes m.val) (bytes ctx.val) (bytes sk.val)
          (bytes addrnd.val) :=
  spec_imp_exists (sha2_256s.slh_sign_spec m ctx sk addrnd hm)

/-- Pure verification with a context string (FIPS 205 Algorithm 24). -/
theorem verify_correct (m sig ctx : Slice U8) (pk : Array U8 64#usize)
    (hm : Room m.length 561) :
    sets.sha2_256s.slh_verify m sig ctx pk =
      ok (Spec.slhVerify Spec.sha2_256s (bytes m.val) (bytes sig.val) (bytes ctx.val)
        (bytes pk.val)) := by
  obtain ⟨b, h, hp⟩ := spec_imp_exists (sha2_256s.slh_verify_spec m sig ctx pk hm)
  rw [h, hp]

end sha2_256s

/-! ## SLH-DSA-SHA2-256f -/

namespace sha2_256f

/-- Key generation: for all seeds, the Rust `sha2_256f::slh_keygen_internal`
returns the secret and public key of FIPS 205 Algorithm 18. -/
theorem keygen_correct (sk_seed sk_prf pk_seed : Array U8 32#usize) :
    ∃ sk pk, sets.sha2_256f.slh_keygen_internal sk_seed sk_prf pk_seed = ok (sk, pk) ∧
      (bytes sk.val, bytes pk.val) =
        Spec.slhKeygenInternal Spec.sha2_256f (bytes sk_seed.val) (bytes sk_prf.val)
          (bytes pk_seed.val) := by
  obtain ⟨⟨sk, pk⟩, h, hp⟩ :=
    spec_imp_exists (sha2_256f.slh_keygen_internal_spec sk_seed sk_prf pk_seed)
  exact ⟨sk, pk, h, hp⟩

/-- Signing: the Rust `sha2_256f::slh_sign_internal` returns the signature of
FIPS 205 Algorithm 19. -/
theorem sign_internal_correct (m : Slice U8) (sk : Array U8 128#usize)
    (addrnd : Array U8 32#usize) (hm : Room m.length 304) :
    ∃ sig, sets.sha2_256f.slh_sign_internal m sk addrnd = ok sig ∧
      bytes sig.val =
        Spec.slhSignInternal Spec.sha2_256f (bytes m.val) (bytes sk.val) (bytes addrnd.val) :=
  spec_imp_exists (sha2_256f.slh_sign_internal_spec m sk addrnd hm)

/-- Verification: the Rust `sha2_256f::slh_verify_internal` returns the verdict
of FIPS 205 Algorithm 20, for every byte string offered as a signature. -/
theorem verify_internal_correct (m sig : Slice U8) (pk : Array U8 64#usize)
    (hm : Room m.length 304) :
    sets.sha2_256f.slh_verify_internal m sig pk =
      ok (Spec.slhVerifyInternal Spec.sha2_256f (bytes m.val) (bytes sig.val) (bytes pk.val)) := by
  obtain ⟨b, h, hp⟩ := spec_imp_exists (sha2_256f.slh_verify_internal_spec m sig pk hm)
  rw [h, hp]

/-- Pure signing with a context string (FIPS 205 Algorithm 22). -/
theorem sign_correct (m ctx : Slice U8) (sk : Array U8 128#usize)
    (addrnd : Array U8 32#usize) (hm : Room m.length 561) :
    ∃ r, sets.sha2_256f.slh_sign m ctx sk addrnd = ok r ∧
      r.map (fun v => bytes v.val) =
        Spec.slhSign Spec.sha2_256f (bytes m.val) (bytes ctx.val) (bytes sk.val)
          (bytes addrnd.val) :=
  spec_imp_exists (sha2_256f.slh_sign_spec m ctx sk addrnd hm)

/-- Pure verification with a context string (FIPS 205 Algorithm 24). -/
theorem verify_correct (m sig ctx : Slice U8) (pk : Array U8 64#usize)
    (hm : Room m.length 561) :
    sets.sha2_256f.slh_verify m sig ctx pk =
      ok (Spec.slhVerify Spec.sha2_256f (bytes m.val) (bytes sig.val) (bytes ctx.val)
        (bytes pk.val)) := by
  obtain ⟨b, h, hp⟩ := spec_imp_exists (sha2_256f.slh_verify_spec m sig ctx pk hm)
  rw [h, hp]

end sha2_256f

end slhdsa

#print axioms slhdsa.sha256_correct
#print axioms slhdsa.sha512_correct
#print axioms slhdsa.generic.keygen_correct
#print axioms slhdsa.generic.sign_internal_correct
#print axioms slhdsa.generic.verify_internal_correct
#print axioms slhdsa.generic.sign_correct
#print axioms slhdsa.generic.verify_correct
#print axioms slhdsa.sha2_128s.keygen_correct
#print axioms slhdsa.sha2_128s.sign_internal_correct
#print axioms slhdsa.sha2_128s.verify_internal_correct
#print axioms slhdsa.sha2_128s.sign_correct
#print axioms slhdsa.sha2_128s.verify_correct
#print axioms slhdsa.sha2_128f.keygen_correct
#print axioms slhdsa.sha2_128f.sign_internal_correct
#print axioms slhdsa.sha2_128f.verify_internal_correct
#print axioms slhdsa.sha2_128f.sign_correct
#print axioms slhdsa.sha2_128f.verify_correct
#print axioms slhdsa.sha2_192s.keygen_correct
#print axioms slhdsa.sha2_192s.sign_internal_correct
#print axioms slhdsa.sha2_192s.verify_internal_correct
#print axioms slhdsa.sha2_192s.sign_correct
#print axioms slhdsa.sha2_192s.verify_correct
#print axioms slhdsa.sha2_192f.keygen_correct
#print axioms slhdsa.sha2_192f.sign_internal_correct
#print axioms slhdsa.sha2_192f.verify_internal_correct
#print axioms slhdsa.sha2_192f.sign_correct
#print axioms slhdsa.sha2_192f.verify_correct
#print axioms slhdsa.sha2_256s.keygen_correct
#print axioms slhdsa.sha2_256s.sign_internal_correct
#print axioms slhdsa.sha2_256s.verify_internal_correct
#print axioms slhdsa.sha2_256s.sign_correct
#print axioms slhdsa.sha2_256s.verify_correct
#print axioms slhdsa.sha2_256f.keygen_correct
#print axioms slhdsa.sha2_256f.sign_internal_correct
#print axioms slhdsa.sha2_256f.verify_internal_correct
#print axioms slhdsa.sha2_256f.sign_correct
#print axioms slhdsa.sha2_256f.verify_correct
