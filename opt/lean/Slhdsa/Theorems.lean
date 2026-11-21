import Slhdsa.Proofs.Slh
open Aeneas Aeneas.Std Result

/-!
# Main results

The Rust functions of the `slhdsa` crate, as translated to Lean by Aeneas,
never panic and compute exactly the functions of the FIPS 205 transcription
in `Spec/SlhDsa.lean`.

`bytes` maps machine bytes to the specification's bytes. `Room len slack`
says a message of `len` bytes plus `slack` more fits in memory and its bit
length fits in SHA-256's 64-bit length field, i.e. the message is under
2^61 bytes, the limit of SHA-256 itself.
-/

namespace slhdsa

/-- Key generation: for all seeds, the Rust `slh_keygen_internal` returns the
secret and public key of FIPS 205 Algorithm 18. -/
theorem keygen_correct (sk_seed sk_prf pk_seed : Array U8 16#usize) :
    ∃ sk pk, slh.slh_keygen_internal sk_seed sk_prf pk_seed = ok (sk, pk) ∧
      (bytes sk.val, bytes pk.val) =
        Spec.slhKeygenInternal (bytes sk_seed.val) (bytes sk_prf.val) (bytes pk_seed.val) := by
  obtain ⟨⟨sk, pk⟩, h, hp⟩ := spec_imp_exists (slh_keygen_internal_spec sk_seed sk_prf pk_seed)
  exact ⟨sk, pk, h, hp⟩

/-- Signing: the Rust `slh_sign_internal` returns the signature of FIPS 205
Algorithm 19. -/
theorem sign_internal_correct (m : Slice U8) (sk : Array U8 64#usize) (addrnd : Array U8 16#usize)
    (hm : Room m.length 152) :
    ∃ sig, slh.slh_sign_internal m sk addrnd = ok sig ∧
      bytes sig.val = Spec.slhSignInternal (bytes m.val) (bytes sk.val) (bytes addrnd.val) :=
  spec_imp_exists (slh_sign_internal_spec m sk addrnd hm)

/-- Verification: the Rust `slh_verify_internal` returns the verdict of FIPS
205 Algorithm 20, for every byte string offered as a signature. -/
theorem verify_internal_correct (m sig : Slice U8) (pk : Array U8 32#usize)
    (hm : Room m.length 152) :
    slh.slh_verify_internal m sig pk =
      ok (Spec.slhVerifyInternal (bytes m.val) (bytes sig.val) (bytes pk.val)) := by
  obtain ⟨b, h, hp⟩ := spec_imp_exists (slh_verify_internal_spec m sig pk hm)
  rw [h, hp]

/-- Pure signing with a context string (FIPS 205 Algorithm 22). -/
theorem sign_correct (m ctx : Slice U8) (sk : Array U8 64#usize) (addrnd : Array U8 16#usize)
    (hm : Room m.length 409) :
    ∃ r, slh.slh_sign m ctx sk addrnd = ok r ∧
      r.map (fun v => bytes v.val) =
        Spec.slhSign (bytes m.val) (bytes ctx.val) (bytes sk.val) (bytes addrnd.val) :=
  spec_imp_exists (slh_sign_spec m ctx sk addrnd hm)

/-- Pure verification with a context string (FIPS 205 Algorithm 24). -/
theorem verify_correct (m sig ctx : Slice U8) (pk : Array U8 32#usize)
    (hm : Room m.length 409) :
    slh.slh_verify m sig ctx pk =
      ok (Spec.slhVerify (bytes m.val) (bytes sig.val) (bytes ctx.val) (bytes pk.val)) := by
  obtain ⟨b, h, hp⟩ := spec_imp_exists (slh_verify_spec m sig ctx pk hm)
  rw [h, hp]

/-- The Rust SHA-256 is SHA-256. -/
theorem sha256_correct (msg : Slice U8) (h : Room msg.length 72) :
    ∃ d, sha256.sha256 msg = ok d ∧ bytes d.val = Spec.sha256 (bytes msg.val) :=
  spec_imp_exists (sha256_spec msg h)

end slhdsa

#print axioms slhdsa.keygen_correct
#print axioms slhdsa.sign_internal_correct
#print axioms slhdsa.verify_internal_correct
#print axioms slhdsa.sign_correct
#print axioms slhdsa.verify_correct
#print axioms slhdsa.sha256_correct
