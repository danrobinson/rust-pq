import Slhdsa.Proofs.Adapter
import Slhdsa.Proofs.Sets

/-!
# The adapter's decisions (`rust/src/adapter.rs`), headline statements

What the RustCrypto-style adapter `compat/` decides is computed by the functions of
`rust/src/adapter.rs`, which it calls at each set's `PARAMS` and `N` (for which `PN` holds:
`slhdsa.sha2_<set>.pn`). Proved in `Proofs/Adapter.lean`, for every valid parameter set, and
listed here with their axioms:

* `adapter_append_spec`: appending a part of a multi-part message is list append;
* `adapter_randomizer_spec`, `adapter_randomizer_panic`: the randomizer is the caller's
  `addrnd` or `PK.seed` (`randS`); an `addrnd` of the wrong length fails its `assert!`;
* `adapter_sign_into_spec`, `adapter_sign_into_long_ctx`: signing writes the signature of
  Algorithm 22 with that randomness into the caller's buffer and reports success exactly when
  the context has at most 255 bytes; a longer context is refused first, whatever the other
  arguments;
* `adapter_sign_internal_into_spec`: the same for Algorithm 19;
* `adapter_keygen_seeds_spec`, `adapter_keygen_seeds_panic`: Algorithm 18 on three separate
  `n`-byte seeds; seeds of another length fail the `assert!`;
* `adapter_signing_key_from_spec`: exactly the `4n`-byte strings are private keys, and the
  public key is `Spec.skPk` of the private key;
* `adapter_signature_from_spec`: exactly the strings of the signature length are signatures;
* `adapter_bytes_equal_spec`: the comparison of public byte strings is equality.

Verification goes through `api.verify` and `slh.slh_verify_internal` directly
(`api_verify_spec`, `slh_verify_internal_spec`), and encoding through `encoding.der_encode`
(`enc_der_encode_spec`).
-/

#print axioms slhdsa.adapter_append_spec
#print axioms slhdsa.adapter_randomizer_spec
#print axioms slhdsa.adapter_randomizer_panic
#print axioms slhdsa.adapter_sign_into_spec
#print axioms slhdsa.adapter_sign_into_long_ctx
#print axioms slhdsa.adapter_sign_internal_into_spec
#print axioms slhdsa.adapter_keygen_seeds_spec
#print axioms slhdsa.adapter_keygen_seeds_panic
#print axioms slhdsa.adapter_signing_key_from_spec
#print axioms slhdsa.adapter_signature_from_spec
#print axioms slhdsa.adapter_bytes_equal_spec
#print axioms slhdsa.api_verify_spec
#print axioms slhdsa.slh_verify_internal_spec
#print axioms slhdsa.enc_der_encode_spec
