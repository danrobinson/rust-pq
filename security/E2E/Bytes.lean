import E2E.FinalSplit
import Reduction.Bytes

/-!
# End to end on byte strings: the Rust functions *are* the cores of the scheme in the game

`E2E/FinalSplit.lean` relates the Rust functions to a scheme whose game is played on typed keys
and signatures.  Here the game is played on byte strings, and the scheme in the game is defined
from the very functions the Rust code is proved to compute:

* `Reduction.byteKeygen`, `byteSign`, `byteVerify`, `byteSignPure`, `byteVerifyPure` (at
  `Link.vp`, `Link.prims`, `Reduction.codec128s`) are deterministic functions on byte strings;
* `Reduction.bytesAlg` / `Reduction.pureBytesAlg` are the signature schemes whose `keygen`,
  `sign`, `verify` are "sample, then apply these functions" (`BytesEndToEnd.keygen_alg`,
  `sign_alg`, `verify_alg`, by `rfl`);
* the Aeneas translations of the Rust functions are **pointwise equal** to these functions
  (`rust_keygen_bytes`, `rust_sign_internal_bytes`, `rust_verify_internal_bytes`,
  `rust_sign_bytes`, `rust_verify_bytes`), for all inputs under the `Room` length bound;
* the byte-level schemes satisfy the SUF-CMA and EUF-CMA bounds of the headline theorems
  (`bytes_standard_model_security`, `pure_standard_model_security`), at the explicit typed
  forgers `Reduction.bytesToTyped A` resp. `Reduction.toInternal (Reduction.pureBytesToTyped A)`.
-/

namespace E2E

open Aeneas Aeneas.Std Result
open SLHDSA SLHDSA.Concrete SLHDSA.Security OracleComp OracleSpec SignatureAlg ENNReal
open slhdsa (bytes Room)
open Link (vp prims cv sp sigBytes pkBytes skBytes)
open Reduction (bPrfC bPrfWC sufCheck rUd rPre rTcr toDspr toTcr toInternal bTcrArS codec128s
  byteKeygen byteSign byteVerify byteSignPure byteVerifyPure bytesAlg pureBytesAlg bytesToTyped
  bytesToTypedS pureBytesToTyped)
open Reduction.Lazy (bPrfMsgL bPrfMsgWL bItsrL bOpenPreS bWotsS)
open TweakableHash

/-! ### Byte representations -/

/-- The bytes of a Rust slice or array (a list of Aeneas `U8`) as a list of Lean `UInt8`, the
byte type of the scheme: each `U8` is read through its bit-vector (`slhdsa.bytes`, then
`Link.cv`).  A length-preserving bijection (`wire_length`, `wire_injective`,
`wire_surjective`). -/
def wire (l : List U8) : List SLHDSA.Byte := cv (bytes l)

@[simp] theorem wire_length (l : List U8) : (wire l).length = l.length := by simp [wire]

theorem wire_injective : Function.Injective wire := by
  intro a b h
  apply slhdsa.ht_bytes_injective
  have := congrArg sp h
  simpa [wire] using this

theorem wire_surjective : Function.Surjective wire := by
  intro l
  refine ⟨l.map fun b => (⟨b.toBitVec⟩ : U8), ?_⟩
  simp [wire, cv, bytes, Function.comp_def]

/-- The spec reading of VCVio's secret-key wire encoding is
`SK.seed ‖ SK.prf ‖ PK.seed ‖ PK.root`. -/
theorem sp_encodeSecretKey (k : SecretKeyCore prims.core) :
    sp (encodeSecretKey codec128s k) = skBytes k := by
  rw [encodeSecretKey_eq, Link.sp_append, Link.sp_append, Link.sp_append]
  rfl

/-- Every 64-byte Rust secret-key array parses: it is the wire encoding of `secretKey sk`. -/
theorem decodeSecretKey_wire (sk : Array U8 64#usize) :
    decodeSecretKey codec128s (wire sk.val) = .ok (secretKey sk) := by
  rw [decodeSecretKey_eq_ok_iff, wire, ← skBytes_secretKey, ← sp_encodeSecretKey, Link.cv_sp]

theorem cv_sigBytes (s : GeneralScheme.SignatureCore vp prims.core) :
    cv (sigBytes s) = encodeSignature vp codec128s s := by
  rw [← Link.sp_encodeSignature, Link.cv_sp]
  rfl

theorem cv_pkBytes (k : PublicKeyCore prims.core) :
    cv (pkBytes k) = encodePublicKey codec128s k := by
  rw [← Link.sp_encodePublicKey, Link.cv_sp]
  rfl

theorem cv_skBytes (k : SecretKeyCore prims.core) :
    cv (skBytes k) = encodeSecretKey codec128s k := by
  rw [← sp_encodeSecretKey, Link.cv_sp]

/-! ### The Rust functions are the byte-level cores -/

/-- **Rust `slh_verify_internal` = `byteVerify`** (FIPS 205 Alg. 20), pointwise: for every
message slice under the `Room` bound, every slice offered as a signature and every public-key
array, the Rust function does not panic and returns `byteVerify` of the bytes of its
arguments. -/
theorem rust_verify_internal_bytes (m sig : Slice U8) (pk : Array U8 32#usize)
    (hm : Room m.length 152) :
    slhdsa.slh.slh_verify_internal m sig pk =
      ok (byteVerify vp prims codec128s (wire m.val) (wire sig.val) (wire pk.val)) := by
  rw [rust_verify_internal m sig pk hm]
  congr 1
  have e1 : decodeSignature vp codec128s (wire sig.val) = Link.decodeSig (cv (bytes sig.val)) :=
    rfl
  have e2 : decodePublicKey codec128s (wire pk.val) = Link.decodePk (cv (bytes pk.val)) := rfl
  unfold byteVerify
  rw [e1, e2]
  cases Link.decodeSig (cv (bytes sig.val)) <;> cases Link.decodePk (cv (bytes pk.val)) <;> rfl

/-- **Rust `slh_sign_internal` = `byteSign`** (FIPS 205 Alg. 19 with `opt_rand = addrnd`),
pointwise: the Rust function does not panic and the bytes of the signature array it returns are
`byteSign` of the bytes of the message and of the secret key, and of `addrnd` read as a node. -/
theorem rust_sign_internal_bytes (m : Slice U8) (sk : Array U8 64#usize)
    (addrnd : Array U8 16#usize) (hm : Room m.length 152) :
    ∃ sig, slhdsa.slh.slh_sign_internal m sk addrnd = ok sig ∧
      wire sig.val = byteSign vp prims codec128s (wire m.val) (wire sk.val) (node addrnd) := by
  obtain ⟨sig, h, hp⟩ := rust_sign_internal m sk addrnd hm
  refine ⟨sig, h, ?_⟩
  simp only [byteSign, decodeSecretKey_wire]
  rw [wire, hp, cv_sigBytes]
  rfl

/-- **Rust `slh_keygen_internal` = `byteKeygen`** (FIPS 205 Alg. 18), pointwise: the Rust
function does not panic and returns arrays `(sk, pk)` whose bytes are the pair
`byteKeygen = (pk bytes, sk bytes)` at the three seeds read as nodes. -/
theorem rust_keygen_bytes (sk_seed sk_prf pk_seed : Array U8 16#usize) :
    ∃ sk pk, slhdsa.slh.slh_keygen_internal sk_seed sk_prf pk_seed = ok (sk, pk) ∧
      (wire pk.val, wire sk.val) =
        byteKeygen vp prims codec128s (node sk_seed) (node sk_prf) (node pk_seed) := by
  obtain ⟨sk, pk, h, hsk, hpk⟩ := rust_keygen sk_seed sk_prf pk_seed
  refine ⟨sk, pk, h, ?_⟩
  simp only [byteKeygen, wire, hsk, hpk, cv_pkBytes, cv_skBytes]

/-- **Rust `slh_sign` = `byteSignPure`** (FIPS 205 Alg. 22 with caller-supplied `addrnd`),
pointwise: the Rust function does not panic; it returns `None` exactly when `byteSignPure` is
`none` (context longer than 255 bytes), and otherwise `Some` of an array with the bytes
`byteSignPure` returns. -/
theorem rust_sign_bytes (m ctx : Slice U8) (sk : Array U8 64#usize)
    (addrnd : Array U8 16#usize) (hm : Room m.length 409) :
    ∃ r, slhdsa.slh.slh_sign m ctx sk addrnd = ok r ∧
      r.map (fun v => wire v.val) =
        byteSignPure vp prims codec128s (wire m.val) (wire ctx.val) (wire sk.val)
          (node addrnd) := by
  obtain ⟨r, h, hp⟩ := rust_sign m ctx sk addrnd hm
  refine ⟨r, h, ?_⟩
  simp only [byteSignPure, decodeSecretKey_wire]
  have h1 : r.map (fun v => wire v.val) = (r.map (fun v => bytes v.val)).map cv := by
    cases r <;> rfl
  rw [h1, hp, Option.map_map]
  exact congrArg (fun f => Option.map f _) (funext fun s => cv_sigBytes s)

/-- **Rust `slh_verify` = `byteVerifyPure`** (FIPS 205 Alg. 24), pointwise. -/
theorem rust_verify_bytes (m sig ctx : Slice U8) (pk : Array U8 32#usize)
    (hm : Room m.length 409) :
    slhdsa.slh.slh_verify m sig ctx pk =
      ok (byteVerifyPure vp prims codec128s (wire m.val) (wire sig.val) (wire ctx.val)
        (wire pk.val)) := by
  rw [rust_verify m sig ctx pk hm]
  congr 1
  have e1 : decodeSignature vp codec128s (wire sig.val) = Link.decodeSig (cv (bytes sig.val)) :=
    rfl
  have e2 : decodePublicKey codec128s (wire pk.val) = Link.decodePk (cv (bytes pk.val)) := rfl
  unfold byteVerifyPure
  rw [e1, e2]
  cases Link.decodeSig (cv (bytes sig.val)) <;> cases Link.decodePk (cv (bytes pk.val)) <;> rfl

/-! ### Summary -/

/-- **The Rust internal functions are the deterministic cores of the byte-level scheme.**
Let `B = Reduction.bytesAlg vp prims codec128s optRand pkSeedDist` (public keys, secret keys,
messages, signatures: `List UInt8`).

* `keygen_alg`, `sign_alg`, `sign_alg_bad`, `verify_alg`: `B` is "sample, then apply
  `byteKeygen` / `byteSign` / `byteVerify`".
* `keygen`, `sign`, `verify`: the Rust `slh_keygen_internal`, `slh_sign_internal`,
  `slh_verify_internal` never panic and are pointwise equal to `byteKeygen`, `byteSign`,
  `byteVerify` on the bytes (`wire`) of their arguments (seeds and `addrnd` read as nodes by
  `node`), under the `Room` bound on the message length.
* `correct`: `B` is perfectly complete. -/
structure BytesEndToEnd (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (pkSeedDist : ProbComp prims.PkSeed) : Prop where
  keygen_alg : (bytesAlg vp prims codec128s optRand pkSeedDist).keygen = do
    let pkSeed ← pkSeedDist
    let skSeed ← $ᵗ prims.SkSeed
    let skPrf ← $ᵗ prims.SkPrf
    pure (byteKeygen vp prims codec128s skSeed skPrf pkSeed)
  keygen : ∀ sk_seed sk_prf pk_seed : Array U8 16#usize,
    ∃ sk pk, slhdsa.slh.slh_keygen_internal sk_seed sk_prf pk_seed = ok (sk, pk) ∧
      (wire pk.val, wire sk.val) =
        byteKeygen vp prims codec128s (node sk_seed) (node sk_prf) (node pk_seed)
  sign_alg : ∀ (pk sk m : List SLHDSA.Byte) (k : PublicKeyCore prims.core),
    Link.decodePk pk = .ok k →
    (bytesAlg vp prims codec128s optRand pkSeedDist).sign pk sk m = do
      let addrnd ← optRand k
      pure (byteSign vp prims codec128s m sk addrnd)
  sign_alg_bad : ∀ (pk sk m : List SLHDSA.Byte), pk.length ≠ 32 →
    (bytesAlg vp prims codec128s optRand pkSeedDist).sign pk sk m = pure []
  sign : ∀ (m : Slice U8) (sk : Array U8 64#usize) (addrnd : Array U8 16#usize),
    Room m.length 152 →
    ∃ sig, slhdsa.slh.slh_sign_internal m sk addrnd = ok sig ∧
      wire sig.val = byteSign vp prims codec128s (wire m.val) (wire sk.val) (node addrnd)
  verify_alg : ∀ pk m sig : List SLHDSA.Byte,
    (bytesAlg vp prims codec128s optRand pkSeedDist).verify pk m sig =
      pure (byteVerify vp prims codec128s m sig pk)
  verify : ∀ (m sig : Slice U8) (pk : Array U8 32#usize), Room m.length 152 →
    slhdsa.slh.slh_verify_internal m sig pk =
      ok (byteVerify vp prims codec128s (wire m.val) (wire sig.val) (wire pk.val))
  correct : (bytesAlg vp prims codec128s optRand pkSeedDist).PerfectlyComplete
    ProbCompRuntime.probComp

theorem sign_bad_pk (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (pkSeedDist : ProbComp prims.PkSeed) (pk sk m : List SLHDSA.Byte) (h : pk.length ≠ 32) :
    (bytesAlg vp prims codec128s optRand pkSeedDist).sign pk sk m = pure [] := by
  have : decodePublicKey codec128s pk = .error (.invalidLength 32 pk.length) :=
    WireCodec.decode_eq_error_of_length_ne _ _ h
  simp only [bytesAlg, this]

/-- `BytesEndToEnd` holds for every `opt_rand` source and every `PK.seed` distribution. -/
theorem bytes_end_to_end (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (pkSeedDist : ProbComp prims.PkSeed) : BytesEndToEnd optRand pkSeedDist where
  keygen_alg := rfl
  keygen := rust_keygen_bytes
  sign_alg := fun pk sk m k hk => by
    have hk' : decodePublicKey codec128s pk = .ok k := hk
    simp only [bytesAlg, hk']
  sign_alg_bad := sign_bad_pk optRand pkSeedDist
  sign := rust_sign_internal_bytes
  verify_alg := fun _ _ _ => rfl
  verify := rust_verify_internal_bytes
  correct := Reduction.bytesAlg_perfectlyComplete optRand pkSeedDist

/-- **The Rust public API functions are the deterministic cores of the byte-level external pure
scheme.**  Let `X = Reduction.pureBytesAlg vp prims codec128s optRand pkSeedDist` (messages are
`(message, context)` pairs of byte strings; signatures are `Option (List UInt8)`).

* `keygen_alg`, `sign_alg`, `sign_alg_tooLong`, `verify_alg`: `X` is "sample, then apply
  `byteKeygen` / `byteSignPure` / `byteVerifyPure`"; for a context longer than 255 bytes signing
  returns `none` without sampling, which is also the value of `byteSignPure` on every `addrnd`.
* `keygen`, `sign`, `verify`: the Rust `slh_keygen_internal`, `slh_sign`, `slh_verify` never
  panic and are pointwise equal to `byteKeygen`, `byteSignPure`, `byteVerifyPure` under the
  `Room` bound (the Rust `Option` of `slh_sign` is the scheme's `Option`).
* `correct`: for contexts of at most 255 bytes the keygen–sign–verify run accepts with
  probability 1. -/
structure PureBytesEndToEnd (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (pkSeedDist : ProbComp prims.PkSeed) : Prop where
  keygen_alg : (pureBytesAlg vp prims codec128s optRand pkSeedDist).keygen = do
    let pkSeed ← pkSeedDist
    let skSeed ← $ᵗ prims.SkSeed
    let skPrf ← $ᵗ prims.SkPrf
    pure (byteKeygen vp prims codec128s skSeed skPrf pkSeed)
  keygen : ∀ sk_seed sk_prf pk_seed : Array U8 16#usize,
    ∃ sk pk, slhdsa.slh.slh_keygen_internal sk_seed sk_prf pk_seed = ok (sk, pk) ∧
      (wire pk.val, wire sk.val) =
        byteKeygen vp prims codec128s (node sk_seed) (node sk_prf) (node pk_seed)
  sign_alg : ∀ (pk sk m ctx : List SLHDSA.Byte) (k : PublicKeyCore prims.core),
    Link.decodePk pk = .ok k → ctx.length ≤ 255 →
    (pureBytesAlg vp prims codec128s optRand pkSeedDist).sign pk sk (m, ctx) = do
      let addrnd ← optRand k
      pure (byteSignPure vp prims codec128s m ctx sk addrnd)
  sign_alg_tooLong : ∀ (pk sk m ctx : List SLHDSA.Byte), 255 < ctx.length →
    (pureBytesAlg vp prims codec128s optRand pkSeedDist).sign pk sk (m, ctx) = pure none ∧
      ∀ addrnd, byteSignPure vp prims codec128s m ctx sk addrnd = none
  sign : ∀ (m ctx : Slice U8) (sk : Array U8 64#usize) (addrnd : Array U8 16#usize),
    Room m.length 409 →
    ∃ r, slhdsa.slh.slh_sign m ctx sk addrnd = ok r ∧
      r.map (fun v => wire v.val) =
        byteSignPure vp prims codec128s (wire m.val) (wire ctx.val) (wire sk.val) (node addrnd)
  verify_alg : ∀ pk m ctx sig : List SLHDSA.Byte,
    (pureBytesAlg vp prims codec128s optRand pkSeedDist).verify pk (m, ctx) (some sig) =
        pure (byteVerifyPure vp prims codec128s m sig ctx pk) ∧
      (pureBytesAlg vp prims codec128s optRand pkSeedDist).verify pk (m, ctx) none = pure false
  verify : ∀ (m sig ctx : Slice U8) (pk : Array U8 32#usize), Room m.length 409 →
    slhdsa.slh.slh_verify m sig ctx pk =
      ok (byteVerifyPure vp prims codec128s (wire m.val) (wire sig.val) (wire ctx.val)
        (wire pk.val))
  correct : ∀ m ctx : List SLHDSA.Byte, ctx.length ≤ 255 →
    ProbCompRuntime.probComp.evalDist (do
      let (pk, sk) ← (pureBytesAlg vp prims codec128s optRand pkSeedDist).keygen
      let sig ← (pureBytesAlg vp prims codec128s optRand pkSeedDist).sign pk sk (m, ctx)
      (pureBytesAlg vp prims codec128s optRand pkSeedDist).verify pk (m, ctx) sig) {true} = 1

/-- `PureBytesEndToEnd` holds for every `opt_rand` source and every `PK.seed` distribution. -/
theorem pure_bytes_end_to_end (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (pkSeedDist : ProbComp prims.PkSeed) : PureBytesEndToEnd optRand pkSeedDist where
  keygen_alg := rfl
  keygen := rust_keygen_bytes
  sign_alg := fun pk sk m ctx k hk hc => by
    have hk' : decodePublicKey codec128s pk = .ok k := hk
    simp only [pureBytesAlg, hk', hc, ite_true]
  sign_alg_tooLong := fun pk sk m ctx hc => by
    refine ⟨?_, fun addrnd => Reduction.byteSignPure_tooLong m ctx sk addrnd hc⟩
    have : ¬ ctx.length ≤ 255 := by omega
    simp only [pureBytesAlg, this, ite_false]
  sign := rust_sign_bytes
  verify_alg := fun _ _ _ _ => ⟨rfl, rfl⟩
  verify := rust_verify_bytes
  correct := fun m ctx hc => Reduction.pureBytesAlg_complete optRand pkSeedDist m ctx hc

/-- **The Rust internal functions and standard-model SUF-CMA / EUF-CMA security, on byte
strings.**  Fix how `opt_rand` and `PK.seed` are sampled (`optRand`, `pkSeedDist`; arbitrary).
Let `B = Reduction.bytesAlg vp prims codec128s optRand pkSeedDist`: SLH-DSA-SHA2-128s, FIPS 205
Algorithms 18–20, as a signature scheme all of whose public keys, secret keys, messages and
signatures are byte strings.

1. `BytesEndToEnd optRand pkSeedDist`: `B.keygen`, `B.sign`, `B.verify` are "sample, then apply
   `byteKeygen`, `byteSign`, `byteVerify`", and the Aeneas translations of the Rust
   `slh_keygen_internal`, `slh_sign_internal`, `slh_verify_internal` never panic and are
   **pointwise equal** to `byteKeygen`, `byteSign`, `byteVerify`; `B` is perfectly complete.
2. For **every** strong forger `S` against `B` — `S` receives the 32 public-key bytes, has a
   signing oracle from message bytes to signature bytes, and wins if it outputs a message and a
   byte string that `byteVerify` accepts and that the oracle never returned for that message —
   the SUF-CMA advantage is at most the twelve standard-model advantages of
   `E2E.standard_model_security_split`, at the typed forger `bytesToTypedS S` (which encodes the
   public key, runs `S` once, makes one signing query per signing query of `S` and encodes the
   answer, and decodes `S`'s output; `Reduction.bytesToTypedS_queryBound`).
3. The same for every chosen-message forger `A` (EUF-CMA: the message was never queried).

**The remaining gap between "the scheme in the game" (`B`) and "the Rust functions".**

(i) *Sampling.*  `B.keygen` draws `PK.seed ← pkSeedDist` and `SK.seed`, `SK.prf` uniformly, and
    `B.sign` draws `opt_rand ← optRand pk` (`pk` the parsed public key).  The Rust functions take
    `sk_seed`, `sk_prf`, `pk_seed` and `addrnd` as *arguments*; no Rust code that samples them is
    part of the statement.  The caller must supply them with these distributions (and the
    assumptions on the right are plausible only for `pkSeedDist` close to uniform).
(ii) *Length bounds.*  The Rust equalities hold for message slices with `Room m.length 152`
    (`m.length + 152 ≤ usize::MAX` and `< 2^61`), resp. `Room m.length 409` for the external
    functions; `B` is defined on all byte strings.
(iii) *Fixed-length arrays.*  The Rust public key is a `[u8; 32]`, the secret key a `[u8; 64]`,
    the returned signature a `[u8; 7856]`; `B` takes arbitrary byte strings.  On a public key
    that is not 32 bytes `B.verify` rejects (`Reduction.byteVerify_of_pk_length_ne`) and `B.sign`
    returns `[]` (`sign_alg_bad`); on a secret key that is not 64 bytes `byteSign` returns `[]`
    (`Reduction.byteSign_of_sk_length_ne`); `[]` is never accepted
    (`Reduction.byteVerify_nil`).  None of these inputs can be passed to the Rust functions, and
    none arises in the games (keys there come from `B.keygen`).  Every 32-byte / 64-byte string
    parses (`Link.decodePk_ok`, `decodeSecretKey_wire`): no well-formedness of the secret key is
    assumed, in particular `byteSign` does not check that the `PK.root` in the secret key
    matches.  The signature argument of the Rust verifier is a slice, of any length, as in `B`.
(iv) *Byte representations.*  Rust bytes are Aeneas `U8` values; the scheme's bytes are Lean
    `UInt8`.  They are identified by `wire = Link.cv ∘ slhdsa.bytes` (a `U8` to its bit-vector
    to `UInt8`), a length-preserving bijection of lists.  The 16-byte seed and `addrnd` arrays
    are read as VCVio nodes (`Vector UInt8 16`) by `node` (`nd_node`: same bytes); in `B` these
    are the typed carriers `prims.SkSeed`, `prims.SkPrf`, `prims.PkSeed`, `prims.Y`, all
    definitionally `Vector UInt8 16`.  `byteKeygen` returns `(pk, sk)`, the Rust function
    `(sk, pk)`.  A Rust `Result` is `ok` (no panic) in every statement.
(v) *Signing uses the public key only for `optRand`.*  `B.sign pk sk m` parses `pk` to evaluate
    `optRand`; the Rust `slh_sign_internal` has no public-key argument (FIPS 205's deterministic
    variant takes `opt_rand = PK.seed` from the secret key; here that is `optRand`'s choice).
(vi) Outside the statement, as before: the twelve advantages are not bounded (assumptions on the
    SHA-256-based functions), no running-time claim, single key, the Rust compiler, the Aeneas
    extraction, side channels. -/
theorem bytes_standard_model_security (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (pkSeedDist : ProbComp prims.PkSeed) :
    BytesEndToEnd optRand pkSeedDist ∧
    (∀ S : SignatureAlg.StrongUnforgeableAdversary
        (bytesAlg vp prims codec128s optRand pkSeedDist),
      SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S ≤
        (Reduction.skPrfC vp prims).prfAdvantage (bPrfWC sufCheck ((bytesToTypedS S).toUnforgeableAdversary)) +
        (Reduction.msgPrf vp prims).prfAdvantage (bPrfMsgWL sufCheck ((bytesToTypedS S).toUnforgeableAdversary)) +
        KeyedHash.ITSRAdvantage (bItsrL ((bytesToTypedS S).toUnforgeableAdversary)) +
        (SM_DT_DSPR_SourceFinalValidity.advantage (toDspr (bOpenPreS ((bytesToTypedS S).toUnforgeableAdversary))) +
          3 * SM_DT_TCR_SourceFinalValidity.advantage (toTcr (bOpenPreS ((bytesToTypedS S).toUnforgeableAdversary)))) +
        (SM_DT_TCR_Advantage (bTcrArS 1 ((bytesToTypedS S).toUnforgeableAdversary)) + SM_DT_TCR_Advantage (bTcrArS 2 ((bytesToTypedS S).toUnforgeableAdversary)) +
          SM_DT_TCR_Advantage (bTcrArS 35 ((bytesToTypedS S).toUnforgeableAdversary)) + SM_DT_TCR_Advantage (bTcrArS 14 ((bytesToTypedS S).toUnforgeableAdversary))) +
        ((vp.params.w - 2 : ℕ) : ℝ≥0∞) *
          SM_DT_UD_Advantage (rUd pkSeedDist (bWotsS ((bytesToTypedS S).toUnforgeableAdversary))) +
        SM_DT_PRE_Advantage (rPre pkSeedDist (bWotsS ((bytesToTypedS S).toUnforgeableAdversary))) +
        SM_DT_TCR_Advantage (rTcr pkSeedDist (bWotsS ((bytesToTypedS S).toUnforgeableAdversary)))) ∧
    ∀ A : SignatureAlg.UnforgeableAdversary (bytesAlg vp prims codec128s optRand pkSeedDist),
      SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤
        (Reduction.skPrfC vp prims).prfAdvantage (bPrfC (bytesToTyped A)) +
        (Reduction.msgPrf vp prims).prfAdvantage (bPrfMsgL (bytesToTyped A)) +
        KeyedHash.ITSRAdvantage (bItsrL (bytesToTyped A)) +
        (SM_DT_DSPR_SourceFinalValidity.advantage (toDspr (bOpenPreS (bytesToTyped A))) +
          3 * SM_DT_TCR_SourceFinalValidity.advantage (toTcr (bOpenPreS (bytesToTyped A)))) +
        (SM_DT_TCR_Advantage (bTcrArS 1 (bytesToTyped A)) + SM_DT_TCR_Advantage (bTcrArS 2 (bytesToTyped A)) +
          SM_DT_TCR_Advantage (bTcrArS 35 (bytesToTyped A)) + SM_DT_TCR_Advantage (bTcrArS 14 (bytesToTyped A))) +
        ((vp.params.w - 2 : ℕ) : ℝ≥0∞) *
          SM_DT_UD_Advantage (rUd pkSeedDist (bWotsS (bytesToTyped A))) +
        SM_DT_PRE_Advantage (rPre pkSeedDist (bWotsS (bytesToTyped A))) +
        SM_DT_TCR_Advantage (rTcr pkSeedDist (bWotsS (bytesToTyped A))) :=
  ⟨bytes_end_to_end optRand pkSeedDist,
    fun S => Reduction.slhdsa_bytes_suf_cma_128s optRand pkSeedDist S,
    fun A => Reduction.slhdsa_bytes_euf_cma_128s optRand pkSeedDist A⟩

/-- **The Rust public API and standard-model SUF-CMA / EUF-CMA security, on byte strings.**
Let `X = Reduction.pureBytesAlg vp prims codec128s optRand pkSeedDist`: the external pure
interface of SLH-DSA-SHA2-128s (FIPS 205 Algorithms 21, 22, 24) as a signature scheme on byte
strings — messages are `(message, context)` pairs, a signature is `Option (List UInt8)` as
returned by the Rust `slh_sign` (`none` for a context longer than 255 bytes).

1. `PureBytesEndToEnd optRand pkSeedDist`: `X` is "sample, then apply `byteKeygen`,
   `byteSignPure`, `byteVerifyPure`", and the Rust `slh_keygen_internal`, `slh_sign`,
   `slh_verify` never panic and are pointwise equal to these functions; `X` is complete for
   contexts of at most 255 bytes.
2. For every strong forger `S` against `X` — a forgery is `((message, context), some bytes)`
   that `byteVerifyPure` accepts and that was never returned for that `(message, context)`;
   `none` is never accepted — the SUF-CMA advantage is at most the twelve advantages at the
   internal typed forger `toInternal (pureBytesToTyped S)`.
3. The same for every chosen-message forger `A` (EUF-CMA).

The gap between `X` and the Rust functions is as in `bytes_standard_model_security`, items
(i)–(vi), with these changes: the `Room` slack is 409; `X.sign` returns `none` without sampling
when the context is over-long, or when the public key does not parse, and `byteSignPure` returns
`none` when the secret key is not 64 bytes; contexts are slices on the Rust side and arbitrary
byte strings in `X`.  Pure mode only (no pre-hash interface). -/
theorem pure_bytes_standard_model_security
    (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (pkSeedDist : ProbComp prims.PkSeed) :
    PureBytesEndToEnd optRand pkSeedDist ∧
    (∀ S : SignatureAlg.StrongUnforgeableAdversary
        (pureBytesAlg vp prims codec128s optRand pkSeedDist),
      SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S ≤
        (Reduction.skPrfC vp prims).prfAdvantage (bPrfWC sufCheck (toInternal (pureBytesToTyped S.toUnforgeableAdversary))) +
        (Reduction.msgPrf vp prims).prfAdvantage (bPrfMsgWL sufCheck (toInternal (pureBytesToTyped S.toUnforgeableAdversary))) +
        KeyedHash.ITSRAdvantage (bItsrL (toInternal (pureBytesToTyped S.toUnforgeableAdversary))) +
        (SM_DT_DSPR_SourceFinalValidity.advantage (toDspr (bOpenPreS (toInternal (pureBytesToTyped S.toUnforgeableAdversary)))) +
          3 * SM_DT_TCR_SourceFinalValidity.advantage (toTcr (bOpenPreS (toInternal (pureBytesToTyped S.toUnforgeableAdversary))))) +
        (SM_DT_TCR_Advantage (bTcrArS 1 (toInternal (pureBytesToTyped S.toUnforgeableAdversary))) + SM_DT_TCR_Advantage (bTcrArS 2 (toInternal (pureBytesToTyped S.toUnforgeableAdversary))) +
          SM_DT_TCR_Advantage (bTcrArS 35 (toInternal (pureBytesToTyped S.toUnforgeableAdversary))) + SM_DT_TCR_Advantage (bTcrArS 14 (toInternal (pureBytesToTyped S.toUnforgeableAdversary)))) +
        ((vp.params.w - 2 : ℕ) : ℝ≥0∞) *
          SM_DT_UD_Advantage (rUd pkSeedDist (bWotsS (toInternal (pureBytesToTyped S.toUnforgeableAdversary)))) +
        SM_DT_PRE_Advantage (rPre pkSeedDist (bWotsS (toInternal (pureBytesToTyped S.toUnforgeableAdversary)))) +
        SM_DT_TCR_Advantage (rTcr pkSeedDist (bWotsS (toInternal (pureBytesToTyped S.toUnforgeableAdversary))))) ∧
    ∀ A : SignatureAlg.UnforgeableAdversary
        (pureBytesAlg vp prims codec128s optRand pkSeedDist),
      SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤
        (Reduction.skPrfC vp prims).prfAdvantage (bPrfC (toInternal (pureBytesToTyped A))) +
        (Reduction.msgPrf vp prims).prfAdvantage (bPrfMsgL (toInternal (pureBytesToTyped A))) +
        KeyedHash.ITSRAdvantage (bItsrL (toInternal (pureBytesToTyped A))) +
        (SM_DT_DSPR_SourceFinalValidity.advantage (toDspr (bOpenPreS (toInternal (pureBytesToTyped A)))) +
          3 * SM_DT_TCR_SourceFinalValidity.advantage (toTcr (bOpenPreS (toInternal (pureBytesToTyped A))))) +
        (SM_DT_TCR_Advantage (bTcrArS 1 (toInternal (pureBytesToTyped A))) + SM_DT_TCR_Advantage (bTcrArS 2 (toInternal (pureBytesToTyped A))) +
          SM_DT_TCR_Advantage (bTcrArS 35 (toInternal (pureBytesToTyped A))) + SM_DT_TCR_Advantage (bTcrArS 14 (toInternal (pureBytesToTyped A)))) +
        ((vp.params.w - 2 : ℕ) : ℝ≥0∞) *
          SM_DT_UD_Advantage (rUd pkSeedDist (bWotsS (toInternal (pureBytesToTyped A)))) +
        SM_DT_PRE_Advantage (rPre pkSeedDist (bWotsS (toInternal (pureBytesToTyped A)))) +
        SM_DT_TCR_Advantage (rTcr pkSeedDist (bWotsS (toInternal (pureBytesToTyped A)))) :=
  ⟨pure_bytes_end_to_end optRand pkSeedDist,
    fun S => Reduction.slhdsa_pure_bytes_suf_cma_128s optRand pkSeedDist S,
    fun A => Reduction.slhdsa_pure_bytes_euf_cma_128s optRand pkSeedDist A⟩

/-- **Resources**: if the byte-level forger makes at most `qs` signing queries (on every public
key), so does the typed forger, and the resource statement `Reduction.FinalResources` of the
typed headline applies to it. -/
theorem bytes_standard_model_resources (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (pkSeedDist : ProbComp prims.PkSeed)
    (A : SignatureAlg.UnforgeableAdversary (bytesAlg vp prims codec128s optRand pkSeedDist))
    (qs : ℕ) (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs) :
    (∀ pk, IsQueryBoundP ((bytesToTyped A).main pk) (fun i => i.isRight = true) qs) ∧
      Reduction.FinalResources (bytesToTyped A) qs (Reduction.counts128s qs) :=
  ⟨Reduction.bytesToTyped_queryBound A qs hA,
    standard_model_resources_final optRand pkSeedDist (bytesToTyped A) qs
      (Reduction.bytesToTyped_queryBound A qs hA)⟩

/-- **Resources, external pure interface.** -/
theorem pure_bytes_standard_model_resources
    (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (pkSeedDist : ProbComp prims.PkSeed)
    (A : SignatureAlg.UnforgeableAdversary (pureBytesAlg vp prims codec128s optRand pkSeedDist))
    (qs : ℕ) (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs) :
    (∀ pk, IsQueryBoundP ((toInternal (pureBytesToTyped A)).main pk)
        (fun i => i.isRight = true) qs) ∧
      Reduction.FinalResources (toInternal (pureBytesToTyped A)) qs (Reduction.counts128s qs) :=
  ⟨Reduction.toInternal_pureBytesToTyped_queryBound A qs hA,
    standard_model_resources_final optRand pkSeedDist (toInternal (pureBytesToTyped A)) qs
      (Reduction.toInternal_pureBytesToTyped_queryBound A qs hA)⟩

end E2E

#print axioms E2E.wire_injective
#print axioms E2E.wire_surjective
#print axioms E2E.rust_verify_internal_bytes
#print axioms E2E.rust_sign_internal_bytes
#print axioms E2E.rust_keygen_bytes
#print axioms E2E.rust_sign_bytes
#print axioms E2E.rust_verify_bytes
#print axioms E2E.bytes_end_to_end
#print axioms E2E.pure_bytes_end_to_end
#print axioms E2E.bytes_standard_model_security
#print axioms E2E.pure_bytes_standard_model_security
#print axioms E2E.bytes_standard_model_resources
#print axioms E2E.pure_bytes_standard_model_resources
