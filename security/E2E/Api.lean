import E2E.HeadlineGen
import E2E.FinalSplit

/-!
# The security statements, attached to the crate's interface module `api`

The headline theorems (`E2E.rust_pure_security`, `rust_pure_securityG`,
`pure_standard_model_security_split`, `Ideal.rust_ideal_security_closed_pure`) name the functions
`slh.slh_keygen_internal`, `slh.slh_sign`, `slh.slh_verify`.  A program calls the interface module
`rust/src/api.rs` instead.  Here:

1. **The interface functions are the scheme's cores** (`api_keygen_bytes`, `api_sign_bytes`,
   `api_sign_deterministic_bytes`, `api_verify_bytes`, collected in `api_pure_cores` and in the
   structure `ApiPureBytesEndToEnd`; typed form `ApiPureEndToEnd`).  They rest on four identities
   of Rust functions:
   * `api_keygen_eq`: `api.keygen seeds _ _` returns exactly what `slh_keygen_internal` returns on
     the three 16-byte blocks `SK.seed ‖ SK.prf ‖ PK.seed` of `seeds` (the buffers passed in are
     overwritten, their contents are irrelevant);
   * `api_sign_eq`, `api_verify_eq`: `api.sign = slh.slh_sign`, `api.verify = slh.slh_verify`;
   * `api_sign_deterministic_eq`: `api.sign_deterministic m ctx sk` is `slh_sign m ctx sk` with
     `addrnd` := the `PK.seed` block (bytes 32–47) of `sk`.
   Key generation and deterministic signing are stated on a split of the 48-byte seed string,
   resp. of the 64-byte private key, into 16-byte arrays (`seeds.val = sk_seed.val ++ sk_prf.val
   ++ pk_seed.val`, `sk.val = sk_seed.val ++ sk_prf.val ++ pk_seed.val ++ pk_root.val`), so that
   the blocks are read by the same `node` as in the existing statements.  Every such array has
   exactly one such split (`seeds_split`, `sk_split`): the hypothesis restricts nothing.
2. **Headline forms** with the `api` functions in place of the `slh` ones: `api_pure_security`,
   `api_pure_security_linear`, `api_pure_securityG`, `api_pure_standard_model_security_split`
   (and `Ideal.api_ideal_security_closed_pure` in `Ideal/RustFinalClosedPureApi.lean`).  Each is
   the existing theorem with its part (1) replaced; the bounds are those theorems' own, not
   re-proved.
3. **The checked signers on well-formed keys** (`api_sign_checked_eq_sign`,
   `api_sign_deterministic_checked_eq`, and their key-generation forms): for a private key with
   `Spec.KeyOk` — every key that key generation writes — `api.sign_checked` *is* `api.sign` and
   `api.sign_deterministic_checked` *is* `api.sign_deterministic`, as Rust functions of the
   remaining arguments: the same `Result`, hence the same signing oracle.  Corollaries
   `api_sign_checked_bytes`, `api_sign_deterministic_checked_bytes`.

Nothing here is specific to one build: the file uses the Rust functions only through
`Slhdsa/Theorems.lean` and `Slhdsa/ApiTheorems.lean`, which are the same statements for the
default and the `hw-sha2` translation.
-/

namespace E2E

open Aeneas Aeneas.Std Result
open SLHDSA SLHDSA.Concrete SLHDSA.Security OracleComp OracleSpec SignatureAlg ENNReal
open slhdsa (bytes Room)
open Link (vp prims cv sp sigBytes pkBytes skBytes)
open Reduction (bPrfC bPrfWC sufCheck rUd rPre rTcr rTcrT toDspr toTcr toInternal bTcrArM bTcrArS
  codec128s externalAlg byteKeygen byteSignPure byteVerifyPure pureBytesAlg pureBytesToTyped
  prfRealPr prfIdealPr msgRealPr msgIdealPr)
open Reduction.Lazy (bPrfMsgL bPrfMsgWL bItsrL bOpenPreS bWotsS)
open TweakableHash

/-! ### Splitting the seed string and the private key into 16-byte blocks -/

theorem bytes_append (a b : List U8) : bytes (a ++ b) = bytes a ++ bytes b := by
  simp [bytes]

theorem block_cons0 (x rest : Spec.Bytes) (hx : x.length = Spec.n) :
    Spec.block (x ++ rest) 0 = x := by
  simp [Spec.block, List.take_left' hx]

theorem block_consS (x rest : Spec.Bytes) (hx : x.length = Spec.n) (i : Nat) :
    Spec.block (x ++ rest) (i + 1) = Spec.block rest i := by
  simp only [Spec.block, Nat.add_mul, Nat.one_mul, Nat.add_comm _ Spec.n, ← List.drop_drop,
    List.drop_left' hx]

theorem bytes16_length (x : Array U8 16#usize) : (bytes x.val).length = Spec.n := by
  simp [Spec.n]

/-- The three 16-byte blocks of a 48-byte string `a ‖ b ‖ c`. -/
theorem block_seeds (seeds : Array U8 48#usize) (a b c : Array U8 16#usize)
    (h : seeds.val = a.val ++ b.val ++ c.val) :
    Spec.block (bytes seeds.val) 0 = bytes a.val ∧ Spec.block (bytes seeds.val) 1 = bytes b.val ∧
      Spec.block (bytes seeds.val) 2 = bytes c.val := by
  have hc : Spec.block (bytes c.val) 0 = bytes c.val := by
    simpa using block_cons0 (bytes c.val) [] (bytes16_length c)
  rw [h, List.append_assoc, bytes_append, bytes_append]
  refine ⟨block_cons0 _ _ (bytes16_length a), ?_, ?_⟩
  · rw [block_consS _ _ (bytes16_length a) 0, block_cons0 _ _ (bytes16_length b)]
  · rw [block_consS _ _ (bytes16_length a) 1, block_consS _ _ (bytes16_length b) 0, hc]

/-- The `PK.seed` block (block 2) of a 64-byte private key `a ‖ b ‖ c ‖ d` is `c`. -/
theorem block_sk_pkSeed (sk : Array U8 64#usize) (a b c d : Array U8 16#usize)
    (h : sk.val = a.val ++ b.val ++ c.val ++ d.val) :
    Spec.block (bytes sk.val) 2 = bytes c.val := by
  rw [h, List.append_assoc, List.append_assoc, bytes_append, bytes_append, bytes_append,
    block_consS _ _ (bytes16_length a) 1, block_consS _ _ (bytes16_length b) 0,
    block_cons0 _ _ (bytes16_length c)]

/-- Every 48-byte string is `SK.seed ‖ SK.prf ‖ PK.seed` for exactly one triple of 16-byte
arrays. -/
theorem seeds_split (seeds : Array U8 48#usize) :
    ∃! abc : Array U8 16#usize × Array U8 16#usize × Array U8 16#usize,
      seeds.val = abc.1.val ++ abc.2.1.val ++ abc.2.2.val := by
  have hl : seeds.val.length = 48 := by simp
  refine ⟨(Aeneas.Std.Array.from (seeds.val.take 16) (by simp [hl]),
    Aeneas.Std.Array.from ((seeds.val.drop 16).take 16) (by simp [hl]),
    Aeneas.Std.Array.from (seeds.val.drop 32) (by simp [hl])), ?_, ?_⟩
  · simp only [Aeneas.Std.Array.from_val]
    rw [show seeds.val.drop 32 = (seeds.val.drop 16).drop 16 by simp, List.append_assoc,
      List.take_append_drop, List.take_append_drop]
  · rintro ⟨a, b, c⟩ h
    simp only at h
    have ha : a.val.length = 16 := by simp
    have hb : b.val.length = 16 := by simp
    have hc : c.val.length = 16 := by simp
    simp only [Prod.mk.injEq]
    refine ⟨?_, ?_, ?_⟩ <;> apply Aeneas.Std.Array.ext <;> simp only [Aeneas.Std.Array.from_val, h, List.append_assoc]
    · rw [List.take_left' ha]
    · rw [List.drop_left' ha, List.take_left' hb]
    · rw [show (32 : Nat) = 16 + 16 by rfl, ← List.drop_drop, List.drop_left' ha,
        List.drop_left' hb]

/-- Every 64-byte private key is `SK.seed ‖ SK.prf ‖ PK.seed ‖ PK.root` for exactly one
quadruple of 16-byte arrays. -/
theorem sk_split (sk : Array U8 64#usize) :
    ∃! abcd : Array U8 16#usize × Array U8 16#usize × Array U8 16#usize × Array U8 16#usize,
      sk.val = abcd.1.val ++ abcd.2.1.val ++ abcd.2.2.1.val ++ abcd.2.2.2.val := by
  have hl : sk.val.length = 64 := by simp
  refine ⟨(Aeneas.Std.Array.from (sk.val.take 16) (by simp [hl]),
    Aeneas.Std.Array.from ((sk.val.drop 16).take 16) (by simp [hl]),
    Aeneas.Std.Array.from ((sk.val.drop 32).take 16) (by simp [hl]),
    Aeneas.Std.Array.from (sk.val.drop 48) (by simp [hl])), ?_, ?_⟩
  · simp only [Aeneas.Std.Array.from_val]
    rw [show sk.val.drop 32 = (sk.val.drop 16).drop 16 by simp,
      show sk.val.drop 48 = ((sk.val.drop 16).drop 16).drop 16 by simp, List.append_assoc,
      List.append_assoc, List.take_append_drop, List.take_append_drop, List.take_append_drop]
  · rintro ⟨a, b, c, d⟩ h
    simp only at h
    have ha : a.val.length = 16 := by simp
    have hb : b.val.length = 16 := by simp
    have hc : c.val.length = 16 := by simp
    simp only [Prod.mk.injEq]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> apply Aeneas.Std.Array.ext <;> simp only [Aeneas.Std.Array.from_val, h, List.append_assoc]
    · rw [List.take_left' ha]
    · rw [List.drop_left' ha, List.take_left' hb]
    · rw [show (32 : Nat) = 16 + 16 by rfl, ← List.drop_drop, List.drop_left' ha,
        List.drop_left' hb, List.take_left' hc]
    · rw [show (48 : Nat) = 16 + 16 + 16 by rfl, ← List.drop_drop, ← List.drop_drop,
        List.drop_left' ha, List.drop_left' hb, List.drop_left' hc]

/-! ### Signatures returned by the Rust signers -/

/-- Two optional Rust signature vectors with the same bytes are equal. -/
theorem optVec_eq {r r' : Option (alloc.vec.Vec U8)}
    (h : r.map (fun v => bytes v.val) = r'.map (fun v => bytes v.val)) : r = r' := by
  cases r <;> cases r' <;> simp at h ⊢
  exact alloc.vec.Vec.ext _ _ (slhdsa.ht_bytes_injective h)

theorem map_wire (r : Option (alloc.vec.Vec U8)) :
    r.map (fun v => wire v.val) = (r.map (fun v => bytes v.val)).map cv := by
  cases r <;> rfl

/-! ### The interface functions are Rust functions the headline theorems name -/

/-- `api.sign` is `slh_sign`. -/
theorem api_sign_eq (m ctx : Slice U8) (sk : Array U8 64#usize) (addrnd : Array U8 16#usize) :
    slhdsa.api.sign m ctx sk addrnd = slhdsa.slh.slh_sign m ctx sk addrnd := rfl

/-- `api.verify` is `slh_verify`. -/
theorem api_verify_eq (m sig ctx : Slice U8) (pk : Array U8 32#usize) :
    slhdsa.api.verify m sig ctx pk = slhdsa.slh.slh_verify m sig ctx pk := rfl

/-- **`api.keygen` is `slh_keygen_internal` on the three blocks of `seeds`**: for
`seeds = SK.seed ‖ SK.prf ‖ PK.seed`, `api.keygen seeds sk0 pk0` returns the same pair of arrays
as `slh_keygen_internal SK.seed SK.prf PK.seed`, whatever the buffers `sk0`, `pk0` held. -/
theorem api_keygen_eq (seeds : Array U8 48#usize) (sk0 : Array U8 64#usize)
    (pk0 : Array U8 32#usize) (sk_seed sk_prf pk_seed : Array U8 16#usize)
    (hs : seeds.val = sk_seed.val ++ sk_prf.val ++ pk_seed.val) :
    slhdsa.api.keygen seeds sk0 pk0 = slhdsa.slh.slh_keygen_internal sk_seed sk_prf pk_seed := by
  obtain ⟨sk', pk', h1, e1⟩ := slhdsa.api_keygen_correct seeds sk0 pk0
  obtain ⟨sk, pk, h2, e2⟩ := slhdsa.keygen_correct sk_seed sk_prf pk_seed
  obtain ⟨b0, b1, b2⟩ := block_seeds seeds sk_seed sk_prf pk_seed hs
  rw [b0, b1, b2, ← e2, Prod.mk.injEq] at e1
  rw [h1, h2]
  congr 2
  · exact Aeneas.Std.Array.ext _ _ (slhdsa.ht_bytes_injective e1.1)
  · exact Aeneas.Std.Array.ext _ _ (slhdsa.ht_bytes_injective e1.2)

/-- **`api.sign_deterministic` is `slh_sign` with `addrnd := PK.seed`**: for
`sk = SK.seed ‖ SK.prf ‖ PK.seed ‖ PK.root`, `api.sign_deterministic m ctx sk` returns the same
as `slh_sign m ctx sk PK.seed`. -/
theorem api_sign_deterministic_eq (m ctx : Slice U8) (sk : Array U8 64#usize)
    (sk_seed sk_prf pk_seed pk_root : Array U8 16#usize)
    (hsk : sk.val = sk_seed.val ++ sk_prf.val ++ pk_seed.val ++ pk_root.val)
    (hm : Room m.length 409) :
    slhdsa.api.sign_deterministic m ctx sk = slhdsa.slh.slh_sign m ctx sk pk_seed := by
  obtain ⟨r, h1, e1, -⟩ := slhdsa.api_sign_deterministic_correct m ctx sk hm
  obtain ⟨r', h2, e2⟩ := slhdsa.sign_correct m ctx sk pk_seed hm
  rw [block_sk_pkSeed sk sk_seed sk_prf pk_seed pk_root hsk, ← e2] at e1
  rw [h1, h2, optVec_eq e1]

/-! ### 1. The interface functions are the cores of the byte-level scheme -/

/-- **Rust `api.keygen` = `byteKeygen`** on the three 16-byte blocks of `seeds`: for
`seeds = SK.seed ‖ SK.prf ‖ PK.seed`, the Rust function does not panic and returns arrays
`(sk, pk)` whose bytes are `byteKeygen = (pk bytes, sk bytes)` at the three blocks read as nodes.
(The buffers `sk0`, `pk0` passed in are irrelevant.) -/
theorem api_keygen_bytes (seeds : Array U8 48#usize) (sk0 : Array U8 64#usize)
    (pk0 : Array U8 32#usize) (sk_seed sk_prf pk_seed : Array U8 16#usize)
    (hs : seeds.val = sk_seed.val ++ sk_prf.val ++ pk_seed.val) :
    ∃ sk pk, slhdsa.api.keygen seeds sk0 pk0 = ok (sk, pk) ∧
      (wire pk.val, wire sk.val) =
        byteKeygen vp prims codec128s (node sk_seed) (node sk_prf) (node pk_seed) := by
  rw [api_keygen_eq seeds sk0 pk0 sk_seed sk_prf pk_seed hs]
  exact rust_keygen_bytes sk_seed sk_prf pk_seed

/-- **Rust `api.sign` = `byteSignPure`** (FIPS 205 Alg. 22 with caller-supplied `addrnd`),
pointwise, as `rust_sign_bytes`. -/
theorem api_sign_bytes (m ctx : Slice U8) (sk : Array U8 64#usize)
    (addrnd : Array U8 16#usize) (hm : Room m.length 409) :
    ∃ r, slhdsa.api.sign m ctx sk addrnd = ok r ∧
      r.map (fun v => wire v.val) =
        byteSignPure vp prims codec128s (wire m.val) (wire ctx.val) (wire sk.val)
          (node addrnd) :=
  rust_sign_bytes m ctx sk addrnd hm

/-- **Rust `api.sign_deterministic` = `byteSignPure` with `addrnd := PK.seed`**: for
`sk = SK.seed ‖ SK.prf ‖ PK.seed ‖ PK.root`, the Rust function does not panic and returns
`byteSignPure` of the bytes of the message, context and key and of the `PK.seed` block of the key
read as a node (FIPS 205's deterministic variant). -/
theorem api_sign_deterministic_bytes (m ctx : Slice U8) (sk : Array U8 64#usize)
    (sk_seed sk_prf pk_seed pk_root : Array U8 16#usize)
    (hsk : sk.val = sk_seed.val ++ sk_prf.val ++ pk_seed.val ++ pk_root.val)
    (hm : Room m.length 409) :
    ∃ r, slhdsa.api.sign_deterministic m ctx sk = ok r ∧
      r.map (fun v => wire v.val) =
        byteSignPure vp prims codec128s (wire m.val) (wire ctx.val) (wire sk.val)
          (node pk_seed) := by
  rw [api_sign_deterministic_eq m ctx sk sk_seed sk_prf pk_seed pk_root hsk hm]
  exact rust_sign_bytes m ctx sk pk_seed hm

/-- **Rust `api.verify` = `byteVerifyPure`** (FIPS 205 Alg. 24), pointwise. -/
theorem api_verify_bytes (m sig ctx : Slice U8) (pk : Array U8 32#usize)
    (hm : Room m.length 409) :
    slhdsa.api.verify m sig ctx pk =
      ok (byteVerifyPure vp prims codec128s (wire m.val) (wire sig.val) (wire ctx.val)
        (wire pk.val)) :=
  rust_verify_bytes m sig ctx pk hm

/-- **The interface functions are the deterministic cores of the byte-level external pure
scheme** `Reduction.pureBytesAlg`: part (a) of `rust_pure_security` for `api.keygen`, `api.sign`,
`api.sign_deterministic`, `api.verify`. -/
theorem api_pure_cores :
    ((∀ (seeds : Array U8 48#usize) (sk0 : Array U8 64#usize) (pk0 : Array U8 32#usize)
          (sk_seed sk_prf pk_seed : Array U8 16#usize),
        seeds.val = sk_seed.val ++ sk_prf.val ++ pk_seed.val →
        ∃ sk pk, slhdsa.api.keygen seeds sk0 pk0 = ok (sk, pk) ∧
          (wire pk.val, wire sk.val) =
            byteKeygen vp prims codec128s (node sk_seed) (node sk_prf) (node pk_seed)) ∧
      (∀ (m ctx : Slice U8) (sk : Array U8 64#usize) (addrnd : Array U8 16#usize),
        Room m.length 409 →
        ∃ r, slhdsa.api.sign m ctx sk addrnd = ok r ∧
          r.map (fun v => wire v.val) =
            byteSignPure vp prims codec128s (wire m.val) (wire ctx.val) (wire sk.val)
              (node addrnd)) ∧
      (∀ (m ctx : Slice U8) (sk : Array U8 64#usize)
          (sk_seed sk_prf pk_seed pk_root : Array U8 16#usize),
        sk.val = sk_seed.val ++ sk_prf.val ++ pk_seed.val ++ pk_root.val → Room m.length 409 →
        ∃ r, slhdsa.api.sign_deterministic m ctx sk = ok r ∧
          r.map (fun v => wire v.val) =
            byteSignPure vp prims codec128s (wire m.val) (wire ctx.val) (wire sk.val)
              (node pk_seed)) ∧
      (∀ (m sig ctx : Slice U8) (pk : Array U8 32#usize), Room m.length 409 →
        slhdsa.api.verify m sig ctx pk =
          ok (byteVerifyPure vp prims codec128s (wire m.val) (wire sig.val) (wire ctx.val)
            (wire pk.val)))) :=
  ⟨api_keygen_bytes, api_sign_bytes, api_sign_deterministic_bytes, api_verify_bytes⟩

/-- **`PureBytesEndToEnd` for the interface.**  The fields `keygen_alg`, `sign_alg`,
`sign_alg_tooLong`, `verify_alg`, `correct` (the scheme `X = pureBytesAlg …`) are those of
`PureBytesEndToEnd`; `keygen`, `sign`, `sign_deterministic`, `verify` say that `api.keygen`,
`api.sign`, `api.sign_deterministic`, `api.verify` never panic and are pointwise equal to
`byteKeygen`, `byteSignPure` (with `addrnd`, resp. with the `PK.seed` block of the key),
`byteVerifyPure`. -/
structure ApiPureBytesEndToEnd (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (pkSeedDist : ProbComp prims.PkSeed) : Prop where
  keygen_alg : (pureBytesAlg vp prims codec128s optRand pkSeedDist).keygen = do
    let pkSeed ← pkSeedDist
    let skSeed ← $ᵗ prims.SkSeed
    let skPrf ← $ᵗ prims.SkPrf
    pure (byteKeygen vp prims codec128s skSeed skPrf pkSeed)
  keygen : ∀ (seeds : Array U8 48#usize) (sk0 : Array U8 64#usize) (pk0 : Array U8 32#usize)
      (sk_seed sk_prf pk_seed : Array U8 16#usize),
    seeds.val = sk_seed.val ++ sk_prf.val ++ pk_seed.val →
    ∃ sk pk, slhdsa.api.keygen seeds sk0 pk0 = ok (sk, pk) ∧
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
    ∃ r, slhdsa.api.sign m ctx sk addrnd = ok r ∧
      r.map (fun v => wire v.val) =
        byteSignPure vp prims codec128s (wire m.val) (wire ctx.val) (wire sk.val) (node addrnd)
  sign_deterministic : ∀ (m ctx : Slice U8) (sk : Array U8 64#usize)
      (sk_seed sk_prf pk_seed pk_root : Array U8 16#usize),
    sk.val = sk_seed.val ++ sk_prf.val ++ pk_seed.val ++ pk_root.val → Room m.length 409 →
    ∃ r, slhdsa.api.sign_deterministic m ctx sk = ok r ∧
      r.map (fun v => wire v.val) =
        byteSignPure vp prims codec128s (wire m.val) (wire ctx.val) (wire sk.val) (node pk_seed)
  verify_alg : ∀ pk m ctx sig : List SLHDSA.Byte,
    (pureBytesAlg vp prims codec128s optRand pkSeedDist).verify pk (m, ctx) (some sig) =
        pure (byteVerifyPure vp prims codec128s m sig ctx pk) ∧
      (pureBytesAlg vp prims codec128s optRand pkSeedDist).verify pk (m, ctx) none = pure false
  verify : ∀ (m sig ctx : Slice U8) (pk : Array U8 32#usize), Room m.length 409 →
    slhdsa.api.verify m sig ctx pk =
      ok (byteVerifyPure vp prims codec128s (wire m.val) (wire sig.val) (wire ctx.val)
        (wire pk.val))
  correct : ∀ m ctx : List SLHDSA.Byte, ctx.length ≤ 255 →
    ProbCompRuntime.probComp.evalDist (do
      let (pk, sk) ← (pureBytesAlg vp prims codec128s optRand pkSeedDist).keygen
      let sig ← (pureBytesAlg vp prims codec128s optRand pkSeedDist).sign pk sk (m, ctx)
      (pureBytesAlg vp prims codec128s optRand pkSeedDist).verify pk (m, ctx) sig) {true} = 1

/-- `ApiPureBytesEndToEnd` holds for every `opt_rand` source and every `PK.seed` distribution. -/
theorem api_pure_bytes_end_to_end (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (pkSeedDist : ProbComp prims.PkSeed) : ApiPureBytesEndToEnd optRand pkSeedDist :=
  have h := pure_bytes_end_to_end optRand pkSeedDist
  { keygen_alg := h.keygen_alg
    keygen := api_keygen_bytes
    sign_alg := h.sign_alg
    sign_alg_tooLong := h.sign_alg_tooLong
    sign := api_sign_bytes
    sign_deterministic := api_sign_deterministic_bytes
    verify_alg := h.verify_alg
    verify := api_verify_bytes
    correct := h.correct }

/-- **`PureEndToEnd` (typed form, `Reduction.externalAlg`) for the interface.**  As
`PureEndToEnd`, with `api.keygen` (on the three blocks of `seeds`), `api.sign`,
`api.sign_deterministic` (randomness: the `PK.seed` block of the key) and `api.verify` in place of
`slh_keygen_internal`, `slh_sign`, `slh_verify`. -/
structure ApiPureEndToEnd (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (pkSeedDist : ProbComp prims.PkSeed) : Prop where
  keygen_alg : (externalAlg vp prims optRand pkSeedDist).keygen = do
    let pkSeed ← pkSeedDist
    let skSeed ← $ᵗ prims.SkSeed
    let skPrf ← $ᵗ prims.SkPrf
    pure (GeneralScheme.keygenInternal vp prims skSeed skPrf pkSeed)
  keygen : ∀ (seeds : Array U8 48#usize) (sk0 : Array U8 64#usize) (pk0 : Array U8 32#usize)
      (sk_seed sk_prf pk_seed : Array U8 16#usize),
    seeds.val = sk_seed.val ++ sk_prf.val ++ pk_seed.val →
    ∃ sk pk, slhdsa.api.keygen seeds sk0 pk0 = ok (sk, pk) ∧
      bytes sk.val =
        skBytes (GeneralScheme.keygenInternal vp prims (node sk_seed) (node sk_prf)
          (node pk_seed)).2 ∧
      bytes pk.val =
        pkBytes (GeneralScheme.keygenInternal vp prims (node sk_seed) (node sk_prf)
          (node pk_seed)).1
  sign_alg : ∀ pk sk (message context : List SLHDSA.Byte), context.length ≤ 255 →
    (externalAlg vp prims optRand pkSeedDist).sign pk sk (message, context) =
      (do let addrnd ← optRand pk
          pure (External.signPureWithRandomizer vp prims message context sk addrnd))
  sign_alg_tooLong : ∀ pk sk (message context : List SLHDSA.Byte), 255 < context.length →
    (externalAlg vp prims optRand pkSeedDist).sign pk sk (message, context) =
        pure (.error (.contextTooLong context.length)) ∧
      ∀ addrnd, External.signPureWithRandomizer vp prims message context sk addrnd =
        .error (.contextTooLong context.length)
  sign : ∀ (m ctx : Slice U8) (sk : Array U8 64#usize) (addrnd : Array U8 16#usize),
    Room m.length 409 →
    ∃ r, slhdsa.api.sign m ctx sk addrnd = ok r ∧
      r.map (fun v => bytes v.val) =
        (External.signPureWithRandomizer vp prims (cv (bytes m.val)) (cv (bytes ctx.val))
          (secretKey sk) (node addrnd)).toOption.map sigBytes
  sign_deterministic : ∀ (m ctx : Slice U8) (sk : Array U8 64#usize)
      (sk_seed sk_prf pk_seed pk_root : Array U8 16#usize),
    sk.val = sk_seed.val ++ sk_prf.val ++ pk_seed.val ++ pk_root.val → Room m.length 409 →
    ∃ r, slhdsa.api.sign_deterministic m ctx sk = ok r ∧
      r.map (fun v => bytes v.val) =
        (External.signPureWithRandomizer vp prims (cv (bytes m.val)) (cv (bytes ctx.val))
          (secretKey sk) (node pk_seed)).toOption.map sigBytes
  verify : ∀ (m sig ctx : Slice U8) (pk : Array U8 32#usize), Room m.length 409 →
    ∃ b, slhdsa.api.verify m sig ctx pk = ok b ∧
      match Link.decodeSig (cv (bytes sig.val)), Link.decodePk (cv (bytes pk.val)) with
      | .ok s, .ok k =>
        (externalAlg vp prims optRand pkSeedDist).verify k
          (cv (bytes m.val), cv (bytes ctx.val)) (.ok s) = pure b
      | _, _ => b = false
  correct : ∀ (message context : List SLHDSA.Byte), context.length ≤ 255 →
    ∀ (skSeed : prims.SkSeed) (skPrf : prims.SkPrf) (pkSeed : prims.PkSeed) (addrnd : prims.Y),
    ∃ σ, External.signPureWithRandomizer vp prims message context
        (GeneralScheme.keygenInternal vp prims skSeed skPrf pkSeed).2 addrnd = .ok σ ∧
      (externalAlg vp prims optRand pkSeedDist).verify
        (GeneralScheme.keygenInternal vp prims skSeed skPrf pkSeed).1 (message, context) (.ok σ) =
          pure true

/-- `ApiPureEndToEnd` holds for every `opt_rand` source and every `PK.seed` distribution. -/
theorem api_pure_end_to_end (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (pkSeedDist : ProbComp prims.PkSeed) : ApiPureEndToEnd optRand pkSeedDist :=
  have h := pure_end_to_end optRand pkSeedDist
  { keygen_alg := h.keygen_alg
    keygen := fun seeds sk0 pk0 a b c hs => by
      rw [api_keygen_eq seeds sk0 pk0 a b c hs]
      exact rust_keygen a b c
    sign_alg := h.sign_alg
    sign_alg_tooLong := h.sign_alg_tooLong
    sign := rust_sign
    sign_deterministic := fun m ctx sk a b c d hsk hm => by
      rw [api_sign_deterministic_eq m ctx sk a b c d hsk hm]
      exact rust_sign m ctx sk c hm
    verify := h.verify
    correct := h.correct }

/-! ### 2. Headline forms for the interface -/

/-- **The Rust interface `api` and the standard-model security of the scheme it computes
(SLH-DSA-SHA2-128s, external pure interface, FIPS 205 Alg. 21/22/24) — final statement.**

`E2E.rust_pure_security` with part (a) about the interface functions: `api.keygen` (on the three
16-byte blocks `SK.seed ‖ SK.prf ‖ PK.seed` of its 48-byte argument), `api.sign`,
`api.sign_deterministic` (with `addrnd` the `PK.seed` block of the key) and `api.verify` never
panic and are pointwise equal to `byteKeygen`, `byteSignPure`, `byteVerifyPure` under
`Room m.length 409`.  Parts (b), (c) — the SUF-CMA and EUF-CMA bounds for the scheme
`X = Reduction.pureBytesAlg vp prims codec128s optRand pkSeedDist` — are those of
`rust_pure_security`, unchanged, and so is the list (i)–(vi) of what lies between `X` and the
Rust code, with these additions: (i) `api.keygen` takes the three seeds as one 48-byte string
(the caller samples it: `SK.seed`, `SK.prf` uniform, `PK.seed` from `pkSeedDist`); a signing oracle
of the game served by `api.sign_deterministic` is the scheme at `optRand pk = pure pk.pkSeed`
(the deterministic variant; `rust_pure_security_deterministic` for the uniform-`PK.seed` bound);
by `api_sign_deterministic_bytes` it uses the `PK.seed` held in the *secret* key, which in the
games is the one in the public key (both from `byteKeygen`). -/
theorem api_pure_security (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (pkSeedDist : ProbComp prims.PkSeed) :
    ((∀ (seeds : Array U8 48#usize) (sk0 : Array U8 64#usize) (pk0 : Array U8 32#usize)
          (sk_seed sk_prf pk_seed : Array U8 16#usize),
        seeds.val = sk_seed.val ++ sk_prf.val ++ pk_seed.val →
        ∃ sk pk, slhdsa.api.keygen seeds sk0 pk0 = ok (sk, pk) ∧
          (wire pk.val, wire sk.val) =
            byteKeygen vp prims codec128s (node sk_seed) (node sk_prf) (node pk_seed)) ∧
      (∀ (m ctx : Slice U8) (sk : Array U8 64#usize) (addrnd : Array U8 16#usize),
        Room m.length 409 →
        ∃ r, slhdsa.api.sign m ctx sk addrnd = ok r ∧
          r.map (fun v => wire v.val) =
            byteSignPure vp prims codec128s (wire m.val) (wire ctx.val) (wire sk.val)
              (node addrnd)) ∧
      (∀ (m ctx : Slice U8) (sk : Array U8 64#usize)
          (sk_seed sk_prf pk_seed pk_root : Array U8 16#usize),
        sk.val = sk_seed.val ++ sk_prf.val ++ pk_seed.val ++ pk_root.val → Room m.length 409 →
        ∃ r, slhdsa.api.sign_deterministic m ctx sk = ok r ∧
          r.map (fun v => wire v.val) =
            byteSignPure vp prims codec128s (wire m.val) (wire ctx.val) (wire sk.val)
              (node pk_seed)) ∧
      (∀ (m sig ctx : Slice U8) (pk : Array U8 32#usize), Room m.length 409 →
        slhdsa.api.verify m sig ctx pk =
          ok (byteVerifyPure vp prims codec128s (wire m.val) (wire sig.val) (wire ctx.val)
            (wire pk.val)))) ∧
    (∀ S : SignatureAlg.StrongUnforgeableAdversary
        (pureBytesAlg vp prims codec128s optRand pkSeedDist),
      SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S ≤
        (Reduction.skPrfC vp prims).prfAdvantage (bPrfWC sufCheck (toInternal (pureBytesToTyped S.toUnforgeableAdversary))) +
        (Reduction.msgPrf vp prims).prfAdvantage (bPrfMsgWL sufCheck (toInternal (pureBytesToTyped S.toUnforgeableAdversary))) +
        KeyedHash.ITSRAdvantage (bItsrL (toInternal (pureBytesToTyped S.toUnforgeableAdversary))) +
        (SM_DT_DSPR_SourceFinalValidity.advantage (toDspr (bOpenPreS (toInternal (pureBytesToTyped S.toUnforgeableAdversary)))) +
          3 * SM_DT_TCR_SourceFinalValidity.advantage (toTcr (bOpenPreS (toInternal (pureBytesToTyped S.toUnforgeableAdversary))))) +
        (SM_DT_TCR_Advantage (bTcrArM 1 (toInternal (pureBytesToTyped S.toUnforgeableAdversary))) +
          SM_DT_TCR_Advantage (bTcrArM 2 (toInternal (pureBytesToTyped S.toUnforgeableAdversary))) +
          SM_DT_TCR_Advantage (bTcrArM 35 (toInternal (pureBytesToTyped S.toUnforgeableAdversary))) +
          SM_DT_TCR_Advantage (bTcrArM 14 (toInternal (pureBytesToTyped S.toUnforgeableAdversary)))) +
        ((vp.params.w - 2 : ℕ) : ℝ≥0∞) *
          SM_DT_UD_Advantage (rUd pkSeedDist (bWotsS (toInternal (pureBytesToTyped S.toUnforgeableAdversary)))) +
        SM_DT_PRE_Advantage (rPre pkSeedDist (bWotsS (toInternal (pureBytesToTyped S.toUnforgeableAdversary)))) +
        SM_DT_TCR_Advantage (rTcrT (vp := vp) pkSeedDist (bWotsS (toInternal (pureBytesToTyped S.toUnforgeableAdversary))))) ∧
    ∀ A : SignatureAlg.UnforgeableAdversary
        (pureBytesAlg vp prims codec128s optRand pkSeedDist),
      SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤
        (Reduction.skPrfC vp prims).prfAdvantage (bPrfC (toInternal (pureBytesToTyped A))) +
        (Reduction.msgPrf vp prims).prfAdvantage (bPrfMsgL (toInternal (pureBytesToTyped A))) +
        KeyedHash.ITSRAdvantage (bItsrL (toInternal (pureBytesToTyped A))) +
        (SM_DT_DSPR_SourceFinalValidity.advantage (toDspr (bOpenPreS (toInternal (pureBytesToTyped A)))) +
          3 * SM_DT_TCR_SourceFinalValidity.advantage (toTcr (bOpenPreS (toInternal (pureBytesToTyped A))))) +
        (SM_DT_TCR_Advantage (bTcrArM 1 (toInternal (pureBytesToTyped A))) +
          SM_DT_TCR_Advantage (bTcrArM 2 (toInternal (pureBytesToTyped A))) +
          SM_DT_TCR_Advantage (bTcrArM 35 (toInternal (pureBytesToTyped A))) +
          SM_DT_TCR_Advantage (bTcrArM 14 (toInternal (pureBytesToTyped A)))) +
        ((vp.params.w - 2 : ℕ) : ℝ≥0∞) *
          SM_DT_UD_Advantage (rUd pkSeedDist (bWotsS (toInternal (pureBytesToTyped A)))) +
        SM_DT_PRE_Advantage (rPre pkSeedDist (bWotsS (toInternal (pureBytesToTyped A)))) +
        SM_DT_TCR_Advantage (rTcrT (vp := vp) pkSeedDist (bWotsS (toInternal (pureBytesToTyped A)))) :=
  ⟨api_pure_cores, (rust_pure_security optRand pkSeedDist).2⟩

/-- **`api_pure_security` in linear (signed-pair) form** (legend: `rust_security_linear`). -/
theorem api_pure_security_linear (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (pkSeedDist : ProbComp prims.PkSeed) :
    ((∀ (seeds : Array U8 48#usize) (sk0 : Array U8 64#usize) (pk0 : Array U8 32#usize)
          (sk_seed sk_prf pk_seed : Array U8 16#usize),
        seeds.val = sk_seed.val ++ sk_prf.val ++ pk_seed.val →
        ∃ sk pk, slhdsa.api.keygen seeds sk0 pk0 = ok (sk, pk) ∧
          (wire pk.val, wire sk.val) =
            byteKeygen vp prims codec128s (node sk_seed) (node sk_prf) (node pk_seed)) ∧
      (∀ (m ctx : Slice U8) (sk : Array U8 64#usize) (addrnd : Array U8 16#usize),
        Room m.length 409 →
        ∃ r, slhdsa.api.sign m ctx sk addrnd = ok r ∧
          r.map (fun v => wire v.val) =
            byteSignPure vp prims codec128s (wire m.val) (wire ctx.val) (wire sk.val)
              (node addrnd)) ∧
      (∀ (m ctx : Slice U8) (sk : Array U8 64#usize)
          (sk_seed sk_prf pk_seed pk_root : Array U8 16#usize),
        sk.val = sk_seed.val ++ sk_prf.val ++ pk_seed.val ++ pk_root.val → Room m.length 409 →
        ∃ r, slhdsa.api.sign_deterministic m ctx sk = ok r ∧
          r.map (fun v => wire v.val) =
            byteSignPure vp prims codec128s (wire m.val) (wire ctx.val) (wire sk.val)
              (node pk_seed)) ∧
      (∀ (m sig ctx : Slice U8) (pk : Array U8 32#usize), Room m.length 409 →
        slhdsa.api.verify m sig ctx pk =
          ok (byteVerifyPure vp prims codec128s (wire m.val) (wire sig.val) (wire ctx.val)
            (wire pk.val)))) ∧
    (∀ S : SignatureAlg.StrongUnforgeableAdversary
        (pureBytesAlg vp prims codec128s optRand pkSeedDist),
      SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S +
          (prfIdealPr (bPrfWC sufCheck (toInternal (pureBytesToTyped S.toUnforgeableAdversary))) +
            msgIdealPr (bPrfMsgWL sufCheck (toInternal (pureBytesToTyped S.toUnforgeableAdversary))) +
            SM_DT_DSPR_SourceFinalValidity.SPProbability (toDspr (bOpenPreS (toInternal (pureBytesToTyped S.toUnforgeableAdversary)))) +
            ((vp.params.w - 2 : ℕ) : ℝ≥0∞) *
              SM_DT_UD_IdealSuccess (rUd pkSeedDist (bWotsS (toInternal (pureBytesToTyped S.toUnforgeableAdversary))))) ≤
        prfRealPr (bPrfWC sufCheck (toInternal (pureBytesToTyped S.toUnforgeableAdversary))) +
        msgRealPr (bPrfMsgWL sufCheck (toInternal (pureBytesToTyped S.toUnforgeableAdversary))) +
        KeyedHash.ITSRAdvantage (bItsrL (toInternal (pureBytesToTyped S.toUnforgeableAdversary))) +
        (SM_DT_DSPR_SourceFinalValidity.Success (toDspr (bOpenPreS (toInternal (pureBytesToTyped S.toUnforgeableAdversary)))) +
          3 * SM_DT_TCR_SourceFinalValidity.advantage (toTcr (bOpenPreS (toInternal (pureBytesToTyped S.toUnforgeableAdversary))))) +
        (SM_DT_TCR_Advantage (bTcrArM 1 (toInternal (pureBytesToTyped S.toUnforgeableAdversary))) +
          SM_DT_TCR_Advantage (bTcrArM 2 (toInternal (pureBytesToTyped S.toUnforgeableAdversary))) +
          SM_DT_TCR_Advantage (bTcrArM 35 (toInternal (pureBytesToTyped S.toUnforgeableAdversary))) +
          SM_DT_TCR_Advantage (bTcrArM 14 (toInternal (pureBytesToTyped S.toUnforgeableAdversary)))) +
        ((vp.params.w - 2 : ℕ) : ℝ≥0∞) *
          SM_DT_UD_RealSuccess (rUd pkSeedDist (bWotsS (toInternal (pureBytesToTyped S.toUnforgeableAdversary)))) +
        SM_DT_PRE_Advantage (rPre pkSeedDist (bWotsS (toInternal (pureBytesToTyped S.toUnforgeableAdversary)))) +
        SM_DT_TCR_Advantage (rTcrT (vp := vp) pkSeedDist (bWotsS (toInternal (pureBytesToTyped S.toUnforgeableAdversary))))) ∧
    ∀ A : SignatureAlg.UnforgeableAdversary
        (pureBytesAlg vp prims codec128s optRand pkSeedDist),
      SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A +
          (prfIdealPr (bPrfC (toInternal (pureBytesToTyped A))) +
            msgIdealPr (bPrfMsgL (toInternal (pureBytesToTyped A))) +
            SM_DT_DSPR_SourceFinalValidity.SPProbability (toDspr (bOpenPreS (toInternal (pureBytesToTyped A)))) +
            ((vp.params.w - 2 : ℕ) : ℝ≥0∞) *
              SM_DT_UD_IdealSuccess (rUd pkSeedDist (bWotsS (toInternal (pureBytesToTyped A))))) ≤
        prfRealPr (bPrfC (toInternal (pureBytesToTyped A))) +
        msgRealPr (bPrfMsgL (toInternal (pureBytesToTyped A))) +
        KeyedHash.ITSRAdvantage (bItsrL (toInternal (pureBytesToTyped A))) +
        (SM_DT_DSPR_SourceFinalValidity.Success (toDspr (bOpenPreS (toInternal (pureBytesToTyped A)))) +
          3 * SM_DT_TCR_SourceFinalValidity.advantage (toTcr (bOpenPreS (toInternal (pureBytesToTyped A))))) +
        (SM_DT_TCR_Advantage (bTcrArM 1 (toInternal (pureBytesToTyped A))) +
          SM_DT_TCR_Advantage (bTcrArM 2 (toInternal (pureBytesToTyped A))) +
          SM_DT_TCR_Advantage (bTcrArM 35 (toInternal (pureBytesToTyped A))) +
          SM_DT_TCR_Advantage (bTcrArM 14 (toInternal (pureBytesToTyped A)))) +
        ((vp.params.w - 2 : ℕ) : ℝ≥0∞) *
          SM_DT_UD_RealSuccess (rUd pkSeedDist (bWotsS (toInternal (pureBytesToTyped A)))) +
        SM_DT_PRE_Advantage (rPre pkSeedDist (bWotsS (toInternal (pureBytesToTyped A)))) +
        SM_DT_TCR_Advantage (rTcrT (vp := vp) pkSeedDist (bWotsS (toInternal (pureBytesToTyped A)))) :=
  ⟨api_pure_cores, (rust_pure_security_linear optRand pkSeedDist).2⟩

/-- **The interface and standard-model SUF-CMA / EUF-CMA security, per-function TCR terms.**
`E2E.pure_standard_model_security_split` with `ApiPureEndToEnd` (the interface functions) in
place of `PureEndToEnd`; the bounds are that theorem's. -/
theorem api_pure_standard_model_security_split
    (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (pkSeedDist : ProbComp prims.PkSeed) :
    ApiPureEndToEnd optRand pkSeedDist ∧
    (∀ S : SignatureAlg.StrongUnforgeableAdversary (externalAlg vp prims optRand pkSeedDist),
      SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S ≤
        (Reduction.skPrfC vp prims).prfAdvantage (bPrfWC sufCheck (toInternal S.toUnforgeableAdversary)) +
        (Reduction.msgPrf vp prims).prfAdvantage (bPrfMsgWL sufCheck (toInternal S.toUnforgeableAdversary)) +
        KeyedHash.ITSRAdvantage (bItsrL (toInternal S.toUnforgeableAdversary)) +
        (SM_DT_DSPR_SourceFinalValidity.advantage (toDspr (bOpenPreS (toInternal S.toUnforgeableAdversary))) +
          3 * SM_DT_TCR_SourceFinalValidity.advantage (toTcr (bOpenPreS (toInternal S.toUnforgeableAdversary)))) +
        (SM_DT_TCR_Advantage (bTcrArS 1 (toInternal S.toUnforgeableAdversary)) + SM_DT_TCR_Advantage (bTcrArS 2 (toInternal S.toUnforgeableAdversary)) +
          SM_DT_TCR_Advantage (bTcrArS 35 (toInternal S.toUnforgeableAdversary)) + SM_DT_TCR_Advantage (bTcrArS 14 (toInternal S.toUnforgeableAdversary))) +
        ((vp.params.w - 2 : ℕ) : ℝ≥0∞) *
          SM_DT_UD_Advantage (rUd pkSeedDist (bWotsS (toInternal S.toUnforgeableAdversary))) +
        SM_DT_PRE_Advantage (rPre pkSeedDist (bWotsS (toInternal S.toUnforgeableAdversary))) +
        SM_DT_TCR_Advantage (rTcr pkSeedDist (bWotsS (toInternal S.toUnforgeableAdversary)))) ∧
    ∀ A : SignatureAlg.UnforgeableAdversary (externalAlg vp prims optRand pkSeedDist),
      SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤
        (Reduction.skPrfC vp prims).prfAdvantage (bPrfC (toInternal A)) +
        (Reduction.msgPrf vp prims).prfAdvantage (bPrfMsgL (toInternal A)) +
        KeyedHash.ITSRAdvantage (bItsrL (toInternal A)) +
        (SM_DT_DSPR_SourceFinalValidity.advantage (toDspr (bOpenPreS (toInternal A))) +
          3 * SM_DT_TCR_SourceFinalValidity.advantage (toTcr (bOpenPreS (toInternal A)))) +
        (SM_DT_TCR_Advantage (bTcrArS 1 (toInternal A)) + SM_DT_TCR_Advantage (bTcrArS 2 (toInternal A)) +
          SM_DT_TCR_Advantage (bTcrArS 35 (toInternal A)) + SM_DT_TCR_Advantage (bTcrArS 14 (toInternal A))) +
        ((vp.params.w - 2 : ℕ) : ℝ≥0∞) *
          SM_DT_UD_Advantage (rUd pkSeedDist (bWotsS (toInternal A))) +
        SM_DT_PRE_Advantage (rPre pkSeedDist (bWotsS (toInternal A))) +
        SM_DT_TCR_Advantage (rTcr pkSeedDist (bWotsS (toInternal A))) :=
  ⟨api_pure_end_to_end optRand pkSeedDist,
    (pure_standard_model_security_split optRand pkSeedDist).2⟩

section General

open Reduction.Gen

variable {κ : Type} (ds : OracleSpec.{0, 0} κ) [OracleSpec.AnswerMeasure ds]
  [∀ d, Fintype (ds.Range d)]

/-- **The interface, external pure scheme, forgers over `ds + unifSpec`.**
`E2E.rust_pure_securityG` with part (a) about the interface functions. -/
theorem api_pure_securityG (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (pkSeedDist : ProbComp prims.PkSeed) :
    ((∀ (seeds : Array U8 48#usize) (sk0 : Array U8 64#usize) (pk0 : Array U8 32#usize)
          (sk_seed sk_prf pk_seed : Array U8 16#usize),
        seeds.val = sk_seed.val ++ sk_prf.val ++ pk_seed.val →
        ∃ sk pk, slhdsa.api.keygen seeds sk0 pk0 = ok (sk, pk) ∧
          (wire pk.val, wire sk.val) =
            byteKeygen vp prims codec128s (node sk_seed) (node sk_prf) (node pk_seed)) ∧
      (∀ (m ctx : Slice U8) (sk : Array U8 64#usize) (addrnd : Array U8 16#usize),
        Room m.length 409 →
        ∃ r, slhdsa.api.sign m ctx sk addrnd = ok r ∧
          r.map (fun v => wire v.val) =
            byteSignPure vp prims codec128s (wire m.val) (wire ctx.val) (wire sk.val)
              (node addrnd)) ∧
      (∀ (m ctx : Slice U8) (sk : Array U8 64#usize)
          (sk_seed sk_prf pk_seed pk_root : Array U8 16#usize),
        sk.val = sk_seed.val ++ sk_prf.val ++ pk_seed.val ++ pk_root.val → Room m.length 409 →
        ∃ r, slhdsa.api.sign_deterministic m ctx sk = ok r ∧
          r.map (fun v => wire v.val) =
            byteSignPure vp prims codec128s (wire m.val) (wire ctx.val) (wire sk.val)
              (node pk_seed)) ∧
      (∀ (m sig ctx : Slice U8) (pk : Array U8 32#usize), Room m.length 409 →
        slhdsa.api.verify m sig ctx pk =
          ok (byteVerifyPure vp prims codec128s (wire m.val) (wire sig.val) (wire ctx.val)
            (wire pk.val)))) ∧
    (∀ S : SignatureAlg.StrongUnforgeableAdversary
        (liftAlg ds (pureBytesAlg vp prims codec128s optRand pkSeedDist)),
      sufAdvG ds S ≤
        betaSufG ds optRand pkSeedDist (toInternalSG ds (pureBytesToTypedSG ds S)).main) ∧
    ∀ A : SignatureAlg.UnforgeableAdversary
        (liftAlg ds (pureBytesAlg vp prims codec128s optRand pkSeedDist)),
      eufAdvG ds A ≤
        betaEufG ds optRand pkSeedDist (toInternalG ds (pureBytesToTypedG ds A)).main :=
  ⟨api_pure_cores, (rust_pure_securityG ds optRand pkSeedDist).2⟩

end General

/-! ### 3. The checked signers on well-formed keys -/

/-- At the level of the specification: for a well-formed key the checked signer (Algorithm 22 on
`slhSignInternalChecked`) *is* Algorithm 22, on every message, context and randomness. -/
theorem spec_slhSignChecked_eq (msg ctx sk addrnd : Spec.Bytes) (hk : Spec.KeyOk sk) :
    Spec.slhSignChecked msg ctx sk addrnd = Spec.slhSign msg ctx sk addrnd := by
  by_cases hc : ctx.length ≤ 255
  · obtain ⟨sig, h⟩ := Spec.slhSignChecked_complete msg ctx sk addrnd hc hk
    rw [h, (Spec.slhSignChecked_sound _ _ _ _ _ h).1]
  · have hc' : ctx.length > 255 := by omega
    simp [Spec.slhSignChecked, Spec.slhSign, hc']

theorem slhSign_tooLong (msg : Spec.Bytes) (ctx : Slice U8) (sk addrnd : Spec.Bytes)
    (hc : 255 < ctx.length) : Spec.slhSign msg (bytes ctx.val) sk addrnd = none := by
  have hc' : (bytes ctx.val).length > 255 := by rw [slhdsa.bytes_length]; exact hc
  unfold Spec.slhSign
  rw [ite_eq_left hc']

/-- **On a well-formed private key the checked hedged signer is the plain one**: for every
message under the `Room` bound, every context and every `addrnd`, `api.sign_checked` returns
exactly what `api.sign` returns — `ok (some sig)` with the same `sig` for a context of at most
255 bytes, `ok none` for a longer one.  So a signing oracle served by `api.sign_checked` with a
key satisfying `Spec.KeyOk` is the signing oracle served by `api.sign`. -/
theorem api_sign_checked_eq_sign (m ctx : Slice U8) (sk : Array U8 64#usize)
    (addrnd : Array U8 16#usize) (hm : Room m.length 409) (hk : Spec.KeyOk (bytes sk.val)) :
    slhdsa.api.sign_checked m ctx sk addrnd = slhdsa.api.sign m ctx sk addrnd ∧
      (ctx.length ≤ 255 → ∃ sig, slhdsa.api.sign m ctx sk addrnd = ok (some sig)) ∧
      (255 < ctx.length → slhdsa.api.sign m ctx sk addrnd = ok none) := by
  obtain ⟨r1, h1, e1⟩ := slhdsa.spec_imp_exists (slhdsa.api_sign_checked_spec m ctx sk addrnd hm)
  obtain ⟨r2, h2, e2⟩ := slhdsa.api_sign_correct m ctx sk addrnd hm
  rw [spec_slhSignChecked_eq _ _ _ _ hk, ← e2] at e1
  have heq : slhdsa.api.sign_checked m ctx sk addrnd = slhdsa.api.sign m ctx sk addrnd := by
    rw [h1, h2, optVec_eq e1]
  refine ⟨heq, fun hc => ?_, fun hc => ?_⟩
  · rw [← heq]
    exact slhdsa.api_sign_checked_complete m ctx sk addrnd hm hc hk
  · rw [slhSign_tooLong _ ctx _ _ hc, Option.map_eq_none_iff] at e2
    rw [h2, e2]

/-- **On a well-formed private key the checked deterministic signer is the plain one**:
`api.sign_deterministic_checked` returns exactly what `api.sign_deterministic` returns, `some` of
the same signature for a context of at most 255 bytes, `none` otherwise. -/
theorem api_sign_deterministic_checked_eq (m ctx : Slice U8) (sk : Array U8 64#usize)
    (hm : Room m.length 409) (hk : Spec.KeyOk (bytes sk.val)) :
    slhdsa.api.sign_deterministic_checked m ctx sk = slhdsa.api.sign_deterministic m ctx sk ∧
      (ctx.length ≤ 255 → ∃ sig, slhdsa.api.sign_deterministic m ctx sk = ok (some sig)) ∧
      (255 < ctx.length → slhdsa.api.sign_deterministic m ctx sk = ok none) := by
  obtain ⟨r1, h1, e1⟩ :=
    slhdsa.spec_imp_exists (slhdsa.api_sign_deterministic_checked_spec m ctx sk hm)
  obtain ⟨r2, h2, e2, -⟩ := slhdsa.api_sign_deterministic_correct m ctx sk hm
  rw [spec_slhSignChecked_eq _ _ _ _ hk, ← e2] at e1
  have heq : slhdsa.api.sign_deterministic_checked m ctx sk =
      slhdsa.api.sign_deterministic m ctx sk := by
    rw [h1, h2, optVec_eq e1]
  refine ⟨heq, fun hc => ?_, fun hc => ?_⟩
  · rw [← heq]
    exact slhdsa.api_sign_deterministic_checked_complete m ctx sk hm hc hk
  · rw [slhSign_tooLong _ ctx _ _ hc, Option.map_eq_none_iff] at e2
    rw [h2, e2]

/-- **With a key written by `api.keygen`, the checked signers are the plain signers**: on every
message under the `Room` bound, every context and every `addrnd`, `api.sign_checked` and
`api.sign_deterministic_checked` return exactly what `api.sign` and `api.sign_deterministic`
return: `some` of the same signature for a context of at most 255 bytes, `none` otherwise.  The
checked signer is the same signing oracle as the plain one on honest keys. -/
theorem api_keygen_checked_eq (seeds : Array U8 48#usize) (sk0 : Array U8 64#usize)
    (pk0 : Array U8 32#usize) (sk : Array U8 64#usize) (pk : Array U8 32#usize)
    (hkg : slhdsa.api.keygen seeds sk0 pk0 = ok (sk, pk)) :
    ∀ (m ctx : Slice U8) (addrnd : Array U8 16#usize), Room m.length 409 →
      (slhdsa.api.sign_checked m ctx sk addrnd = slhdsa.api.sign m ctx sk addrnd ∧
        (ctx.length ≤ 255 → ∃ sig, slhdsa.api.sign m ctx sk addrnd = ok (some sig)) ∧
        (255 < ctx.length → slhdsa.api.sign m ctx sk addrnd = ok none)) ∧
      (slhdsa.api.sign_deterministic_checked m ctx sk = slhdsa.api.sign_deterministic m ctx sk ∧
        (ctx.length ≤ 255 → ∃ sig, slhdsa.api.sign_deterministic m ctx sk = ok (some sig)) ∧
        (255 < ctx.length → slhdsa.api.sign_deterministic m ctx sk = ok none)) := by
  have hk := (slhdsa.api_keygen_keyOk seeds sk0 pk0 sk pk hkg).1
  exact fun m ctx addrnd hm =>
    ⟨api_sign_checked_eq_sign m ctx sk addrnd hm hk, api_sign_deterministic_checked_eq m ctx sk hm hk⟩

/-- The same for a key written by `slh_keygen_internal`. -/
theorem keygen_internal_checked_eq (sk_seed sk_prf pk_seed : Array U8 16#usize)
    (sk : Array U8 64#usize) (pk : Array U8 32#usize)
    (hkg : slhdsa.slh.slh_keygen_internal sk_seed sk_prf pk_seed = ok (sk, pk)) :
    ∀ (m ctx : Slice U8) (addrnd : Array U8 16#usize), Room m.length 409 →
      (slhdsa.api.sign_checked m ctx sk addrnd = slhdsa.api.sign m ctx sk addrnd ∧
        (ctx.length ≤ 255 → ∃ sig, slhdsa.api.sign m ctx sk addrnd = ok (some sig)) ∧
        (255 < ctx.length → slhdsa.api.sign m ctx sk addrnd = ok none)) ∧
      (slhdsa.api.sign_deterministic_checked m ctx sk = slhdsa.api.sign_deterministic m ctx sk ∧
        (ctx.length ≤ 255 → ∃ sig, slhdsa.api.sign_deterministic m ctx sk = ok (some sig)) ∧
        (255 < ctx.length → slhdsa.api.sign_deterministic m ctx sk = ok none)) := by
  have hk := (slhdsa.keygen_keyOk sk_seed sk_prf pk_seed sk pk hkg).1
  exact fun m ctx addrnd hm =>
    ⟨api_sign_checked_eq_sign m ctx sk addrnd hm hk, api_sign_deterministic_checked_eq m ctx sk hm hk⟩

/-- **Rust `api.sign_checked` = `byteSignPure` on well-formed keys** (part (a) of
`api_pure_security` for the checked hedged signer). -/
theorem api_sign_checked_bytes (m ctx : Slice U8) (sk : Array U8 64#usize)
    (addrnd : Array U8 16#usize) (hm : Room m.length 409) (hk : Spec.KeyOk (bytes sk.val)) :
    ∃ r, slhdsa.api.sign_checked m ctx sk addrnd = ok r ∧
      r.map (fun v => wire v.val) =
        byteSignPure vp prims codec128s (wire m.val) (wire ctx.val) (wire sk.val)
          (node addrnd) := by
  rw [(api_sign_checked_eq_sign m ctx sk addrnd hm hk).1]
  exact api_sign_bytes m ctx sk addrnd hm

/-- **Rust `api.sign_deterministic_checked` = `byteSignPure` with `addrnd := PK.seed` on
well-formed keys** (part (a) of `api_pure_security` for the checked deterministic signer). -/
theorem api_sign_deterministic_checked_bytes (m ctx : Slice U8) (sk : Array U8 64#usize)
    (sk_seed sk_prf pk_seed pk_root : Array U8 16#usize)
    (hsk : sk.val = sk_seed.val ++ sk_prf.val ++ pk_seed.val ++ pk_root.val)
    (hm : Room m.length 409) (hk : Spec.KeyOk (bytes sk.val)) :
    ∃ r, slhdsa.api.sign_deterministic_checked m ctx sk = ok r ∧
      r.map (fun v => wire v.val) =
        byteSignPure vp prims codec128s (wire m.val) (wire ctx.val) (wire sk.val)
          (node pk_seed) := by
  rw [(api_sign_deterministic_checked_eq m ctx sk hm hk).1]
  exact api_sign_deterministic_bytes m ctx sk sk_seed sk_prf pk_seed pk_root hsk hm

/-- **The signing items of part (a), for the checked signers, on well-formed keys**: the two
signing conjuncts of `api_pure_cores` with `api.sign_checked`, `api.sign_deterministic_checked`
in place of `api.sign`, `api.sign_deterministic`, for every private key satisfying `Spec.KeyOk`
(in particular every key written by `api.keygen`, `slhdsa.api_keygen_keyOk`). -/
theorem api_checked_pure_cores :
    (∀ (m ctx : Slice U8) (sk : Array U8 64#usize) (addrnd : Array U8 16#usize),
        Room m.length 409 → Spec.KeyOk (bytes sk.val) →
        ∃ r, slhdsa.api.sign_checked m ctx sk addrnd = ok r ∧
          r.map (fun v => wire v.val) =
            byteSignPure vp prims codec128s (wire m.val) (wire ctx.val) (wire sk.val)
              (node addrnd)) ∧
      (∀ (m ctx : Slice U8) (sk : Array U8 64#usize)
          (sk_seed sk_prf pk_seed pk_root : Array U8 16#usize),
        sk.val = sk_seed.val ++ sk_prf.val ++ pk_seed.val ++ pk_root.val → Room m.length 409 →
        Spec.KeyOk (bytes sk.val) →
        ∃ r, slhdsa.api.sign_deterministic_checked m ctx sk = ok r ∧
          r.map (fun v => wire v.val) =
            byteSignPure vp prims codec128s (wire m.val) (wire ctx.val) (wire sk.val)
              (node pk_seed)) :=
  ⟨api_sign_checked_bytes, api_sign_deterministic_checked_bytes⟩

end E2E

#print axioms E2E.bytes_append
#print axioms E2E.block_cons0
#print axioms E2E.block_consS
#print axioms E2E.bytes16_length
#print axioms E2E.block_seeds
#print axioms E2E.block_sk_pkSeed
#print axioms E2E.seeds_split
#print axioms E2E.sk_split
#print axioms E2E.optVec_eq
#print axioms E2E.map_wire
#print axioms E2E.api_sign_eq
#print axioms E2E.api_verify_eq
#print axioms E2E.api_keygen_eq
#print axioms E2E.api_sign_deterministic_eq
#print axioms E2E.api_keygen_bytes
#print axioms E2E.api_sign_bytes
#print axioms E2E.api_sign_deterministic_bytes
#print axioms E2E.api_verify_bytes
#print axioms E2E.api_pure_cores
#print axioms E2E.api_pure_bytes_end_to_end
#print axioms E2E.api_pure_end_to_end
#print axioms E2E.api_pure_security
#print axioms E2E.api_pure_security_linear
#print axioms E2E.api_pure_standard_model_security_split
#print axioms E2E.api_pure_securityG
#print axioms E2E.spec_slhSignChecked_eq
#print axioms E2E.slhSign_tooLong
#print axioms E2E.api_sign_checked_eq_sign
#print axioms E2E.api_sign_deterministic_checked_eq
#print axioms E2E.api_keygen_checked_eq
#print axioms E2E.keygen_internal_checked_eq
#print axioms E2E.api_sign_checked_bytes
#print axioms E2E.api_sign_deterministic_checked_bytes
#print axioms E2E.api_checked_pure_cores
