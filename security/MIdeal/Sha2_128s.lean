import ME2E.Sha2_128s
import ME2E.Api.Sha2_128s
import Ideal.Realize.FinalTight8
import Ideal.Realize.FinalPureTight8

/-!
# SLH-DSA-SHA2-128s of the six-set tree: the closed ideal-compression bound attached to the Rust functions

Counterpart, for the six-set tree's Rust functions `slhdsa::sets::sha2_128s::*` (Aeneas:
`slhdsa.sets.sha2_128s.*`, `../lean`), of the three single-set corollaries of the single-set tree's
`Ideal/RustFinalClosedTight8.lean` (git commit `26aa3d8`; deleted from this tree with the single-set crate):

* `rust_ideal_security_closed_tight8` (internal interface: `slh_keygen_internal`,
  `slh_sign_internal`, `slh_verify_internal`);
* `rust_ideal_security_closed_pure_tight8` (external pure interface: `slh_keygen_internal`,
  `slh_sign`, `slh_verify`);
* `api_ideal_security_closed_pure_tight8` (the interface functions `keygen`, `sign`,
  `sign_deterministic`, `verify`).

Each statement is the single-set one under textual renamings only (`scripts/check_ideal128s.py`,
run by `scripts/check.sh`): Rust names `slhdsa.slh.slh_f` / `slhdsa.api.f` →
`slhdsa.sets.sha2_128s.slh_f` / `slhdsa.sets.sha2_128s.f`; the real scheme's parameters
`vp prims codec128s` / `Link.vp Link.prims Reduction.codec128s` → `Sha2Set.s128s.vp Sha2Set.s128s.prims
(codec Sha2Set.s128s)` (`rfl`-equal: `vp_eq`, `prims_eq`, `codec_eq`, `bytesAlg_eq`, `pureBytesAlg_eq`);
`node x` → `node Sha2Set.s128s x`; `E2E.PureBytesEndToEnd` / `E2E.ApiPureBytesEndToEnd` → their six-set
counterparts `PureBytesEndToEnd` (below, same fields) / `ME2E.sha2_128s.ApiPureBytesEndToEnd`.

* Conjunct 1 (real code, real SHA-256): the Rust functions of `../lean` never panic and are
  pointwise the byte-level cores of `Reduction.bytesAlg` / `pureBytesAlg` at `Sha2Set.s128s`
  (`ME2E.sha2_128s.*`, which rest on `../lean`'s refinement theorems and `MLink`'s
  `Spec` = VCVio identification at `Sha2Set.s128s`).
* Conjunct 2 (link): the byte-level scheme over the generic SHA-2 primitives `primsG (liftC g)` at
  the table `g = realCF` of the real SHA-256 compression function IS that scheme
  (`Ideal.bytesAlg_realCF`, `pureBytesAlg_realCF`, plus the `rfl` bridges).
* Conjunct 3 (IDEAL-MODEL scheme only): the bound of `Ideal/Realize/FinalTight8.lean` /
  `FinalPureTight8.lean`, proved by the very theorems `Ideal.suf_ideal_closed_tight8`, …,
  `Ideal.euf_ideal_pure_closed_tight8_2_64` of `Ideal` (library `Ideal`); its text is the
  single-set text verbatim.  It is
  about a uniformly random compression table and says nothing about the real compression function.

Scope: SLH-DSA-SHA2-128s only.  The ideal-model analysis is of SHA-256 with 16-byte outputs
(`Bytes 16` nodes, `Link.vp`, SHA-256-only primitives, `2^128` / `2^256` denominators); see
`STATUS.md` §5.
-/

namespace MIdeal.sha2_128s

open Aeneas Aeneas.Std Result
open SLHDSA SLHDSA.Concrete SLHDSA.Security OracleComp OracleSpec SignatureAlg ENNReal
open slhdsa (bytes Room)
open MLink (Sha2Set)
open MReduction (codec)
open Reduction (byteKeygen byteSign byteVerify bytesAlg byteSignPure byteVerifyPure pureBytesAlg)
open ME2E (wire node)
open Ideal Ideal.Realize

/-! ### The six-set names of the real 128s scheme are the single-set ones (`rfl`) -/

theorem vp_eq : Sha2Set.s128s.vp = Link.vp := rfl
theorem prims_eq : Sha2Set.s128s.prims = Link.prims := rfl
theorem codec_eq : codec Sha2Set.s128s = Reduction.codec128s := rfl

theorem bytesAlg_eq (optRand : PublicKeyCore Sha2Set.s128s.prims.core → ProbComp Sha2Set.s128s.prims.Y)
    (pkSeedDist : ProbComp Sha2Set.s128s.prims.PkSeed) :
    bytesAlg Sha2Set.s128s.vp Sha2Set.s128s.prims (codec Sha2Set.s128s) optRand pkSeedDist =
      bytesAlg Link.vp Link.prims Reduction.codec128s optRand pkSeedDist := rfl

theorem pureBytesAlg_eq (optRand : PublicKeyCore Sha2Set.s128s.prims.core → ProbComp Sha2Set.s128s.prims.Y)
    (pkSeedDist : ProbComp Sha2Set.s128s.prims.PkSeed) :
    pureBytesAlg Sha2Set.s128s.vp Sha2Set.s128s.prims (codec Sha2Set.s128s) optRand pkSeedDist =
      pureBytesAlg Link.vp Link.prims Reduction.codec128s optRand pkSeedDist := rfl

/-! ### The external pure scheme and the Rust functions (`E2E.PureBytesEndToEnd` at the six-set names) -/

/-- **`E2E.PureBytesEndToEnd` for the six-set tree** (fields as in the single-set `E2E/Bytes.lean`):
`keygen_alg`, `sign_alg`, `sign_alg_tooLong`, `verify_alg`, `correct` describe
`X = pureBytesAlg Sha2Set.s128s.vp Sha2Set.s128s.prims (codec Sha2Set.s128s) optRand pkSeedDist` ("sample, then apply the
cores"; complete for contexts of at most 255 bytes); `keygen`, `sign`, `verify` say that
`slhdsa.sets.sha2_128s.{slh_keygen_internal, slh_sign, slh_verify}` never panic and are
pointwise `byteKeygen`, `byteSignPure`, `byteVerifyPure`. -/
structure PureBytesEndToEnd (optRand : PublicKeyCore Sha2Set.s128s.prims.core → ProbComp Sha2Set.s128s.prims.Y)
    (pkSeedDist : ProbComp Sha2Set.s128s.prims.PkSeed) : Prop where
  keygen_alg : (pureBytesAlg Sha2Set.s128s.vp Sha2Set.s128s.prims (codec Sha2Set.s128s) optRand pkSeedDist).keygen = do
    let pkSeed ← pkSeedDist
    let skSeed ← $ᵗ Sha2Set.s128s.prims.SkSeed
    let skPrf ← $ᵗ Sha2Set.s128s.prims.SkPrf
    pure (byteKeygen Sha2Set.s128s.vp Sha2Set.s128s.prims (codec Sha2Set.s128s) skSeed skPrf pkSeed)
  keygen : ∀ sk_seed sk_prf pk_seed : Array U8 16#usize,
    ∃ sk pk, slhdsa.sets.sha2_128s.slh_keygen_internal sk_seed sk_prf pk_seed = ok (sk, pk) ∧
      (wire pk.val, wire sk.val) =
        byteKeygen Sha2Set.s128s.vp Sha2Set.s128s.prims (codec Sha2Set.s128s) (node Sha2Set.s128s sk_seed) (node Sha2Set.s128s sk_prf) (node Sha2Set.s128s pk_seed)
  sign_alg : ∀ (pk sk m ctx : List SLHDSA.Byte) (k : PublicKeyCore Sha2Set.s128s.prims.core),
    MLink.decodePk Sha2Set.s128s pk = .ok k → ctx.length ≤ 255 →
    (pureBytesAlg Sha2Set.s128s.vp Sha2Set.s128s.prims (codec Sha2Set.s128s) optRand pkSeedDist).sign pk sk (m, ctx) = do
      let addrnd ← optRand k
      pure (byteSignPure Sha2Set.s128s.vp Sha2Set.s128s.prims (codec Sha2Set.s128s) m ctx sk addrnd)
  sign_alg_tooLong : ∀ (pk sk m ctx : List SLHDSA.Byte), 255 < ctx.length →
    (pureBytesAlg Sha2Set.s128s.vp Sha2Set.s128s.prims (codec Sha2Set.s128s) optRand pkSeedDist).sign pk sk (m, ctx) = pure none ∧
      ∀ addrnd, byteSignPure Sha2Set.s128s.vp Sha2Set.s128s.prims (codec Sha2Set.s128s) m ctx sk addrnd = none
  sign : ∀ (m ctx : Slice U8) (sk : Array U8 64#usize) (addrnd : Array U8 16#usize),
    Room m.length 409 →
    ∃ r, slhdsa.sets.sha2_128s.slh_sign m ctx sk addrnd = ok r ∧
      r.map (fun v => wire v.val) =
        byteSignPure Sha2Set.s128s.vp Sha2Set.s128s.prims (codec Sha2Set.s128s) (wire m.val) (wire ctx.val) (wire sk.val) (node Sha2Set.s128s addrnd)
  verify_alg : ∀ pk m ctx sig : List SLHDSA.Byte,
    (pureBytesAlg Sha2Set.s128s.vp Sha2Set.s128s.prims (codec Sha2Set.s128s) optRand pkSeedDist).verify pk (m, ctx) (some sig) =
        pure (byteVerifyPure Sha2Set.s128s.vp Sha2Set.s128s.prims (codec Sha2Set.s128s) m sig ctx pk) ∧
      (pureBytesAlg Sha2Set.s128s.vp Sha2Set.s128s.prims (codec Sha2Set.s128s) optRand pkSeedDist).verify pk (m, ctx) none = pure false
  verify : ∀ (m sig ctx : Slice U8) (pk : Array U8 32#usize), Room m.length 409 →
    slhdsa.sets.sha2_128s.slh_verify m sig ctx pk =
      ok (byteVerifyPure Sha2Set.s128s.vp Sha2Set.s128s.prims (codec Sha2Set.s128s) (wire m.val) (wire sig.val) (wire ctx.val)
        (wire pk.val))
  correct : ∀ m ctx : List SLHDSA.Byte, ctx.length ≤ 255 →
    ProbCompRuntime.probComp.evalDist (do
      let (pk, sk) ← (pureBytesAlg Sha2Set.s128s.vp Sha2Set.s128s.prims (codec Sha2Set.s128s) optRand pkSeedDist).keygen
      let sig ← (pureBytesAlg Sha2Set.s128s.vp Sha2Set.s128s.prims (codec Sha2Set.s128s) optRand pkSeedDist).sign pk sk (m, ctx)
      (pureBytesAlg Sha2Set.s128s.vp Sha2Set.s128s.prims (codec Sha2Set.s128s) optRand pkSeedDist).verify pk (m, ctx) sig) {true} = 1

/-- `PureBytesEndToEnd` holds for every `opt_rand` source and every `PK.seed` distribution
(`ME2E.pure_bytes_scheme` and `ME2E.sha2_128s.rust_*_bytes`). -/
theorem pure_bytes_end_to_end (optRand : PublicKeyCore Sha2Set.s128s.prims.core → ProbComp Sha2Set.s128s.prims.Y)
    (pkSeedDist : ProbComp Sha2Set.s128s.prims.PkSeed) : PureBytesEndToEnd optRand pkSeedDist :=
  have h := ME2E.pure_bytes_scheme Sha2Set.s128s optRand pkSeedDist
  { keygen_alg := h.keygen_alg
    keygen := ME2E.sha2_128s.rust_keygen_bytes
    sign_alg := h.sign_alg
    sign_alg_tooLong := h.sign_alg_tooLong
    sign := ME2E.sha2_128s.rust_sign_bytes
    verify_alg := h.verify_alg
    verify := ME2E.sha2_128s.rust_verify_bytes
    correct := h.correct }

/-! ### Link: at the real compression table the ideal-model scheme is the real one -/

/-- **At the table of the real compression function the byte-level external pure scheme is the
real one** at `Sha2Set.s128s` (`Ideal.bytesAlg_realCF` for `pureBytesAlg`; same proof as the single-set
`Ideal.pureBytesAlg_realCF`). -/
theorem pureBytesAlg_realCF
    (optRand : ∀ c : CompressFn, PublicKeyCore (primsG c).core → ProbComp (primsG c).Y)
    (pkSeedDist : ProbComp (Bytes 16)) :
    Reduction.pureBytesAlg Link.vp (primsG (liftC realCF)) (codecG realCF)
        (optRand (liftC realCF)) pkSeedDist =
      Reduction.pureBytesAlg Sha2Set.s128s.vp Sha2Set.s128s.prims (codec Sha2Set.s128s)
        (optRand VCVio.Algorithms.Sha2.compress) pkSeedDist :=
  congrArg (fun c => Reduction.pureBytesAlg Link.vp (primsG c) (codecC c) (optRand c) pkSeedDist)
    liftC_realCF

/-! ### The three headline statements -/

/-- **SLH-DSA-SHA2-128s, six-set tree, internal interface: the Rust functions, and the closed
ideal-compression bound of the scheme they compute.**  `Ideal.rust_ideal_security_closed_tight8`
with conjunct 1 about `slhdsa.sets.sha2_128s.{slh_keygen_internal, slh_sign_internal,
slh_verify_internal}` and conjunct 2 ending in the scheme of conjunct 1; conjunct 3 verbatim
(general bound with coefficient `QlinT8 qf qs ℓ`, and the points `2^-77 + 2^-132 + 2^-63`
(`qf ≤ 2^60`, `qs ≤ 2^20`), `2^-63 + 2^-94 + 2^-59` (`qf ≤ 2^64`, `qs ≤ 2^40`),
`2^-45 + 2^-46 + 2^-39` (`qf ≤ 2^64`, `qs ≤ 2^64`), messages of at most `2^26` bytes; SUF and
EUF).  Conjunct 3 is about the IDEAL-MODEL scheme only. -/
theorem rust_ideal_security_closed_tight8 (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) :
    ((∀ sk_seed sk_prf pk_seed : Array U8 16#usize,
        ∃ sk pk, slhdsa.sets.sha2_128s.slh_keygen_internal sk_seed sk_prf pk_seed = ok (sk, pk) ∧
          (wire pk.val, wire sk.val) =
            byteKeygen Sha2Set.s128s.vp Sha2Set.s128s.prims (codec Sha2Set.s128s) (node Sha2Set.s128s sk_seed) (node Sha2Set.s128s sk_prf) (node Sha2Set.s128s pk_seed)) ∧
      (∀ (m : Slice U8) (sk : Array U8 64#usize) (addrnd : Array U8 16#usize),
        Room m.length 152 →
        ∃ sig, slhdsa.sets.sha2_128s.slh_sign_internal m sk addrnd = ok sig ∧
          wire sig.val = byteSign Sha2Set.s128s.vp Sha2Set.s128s.prims (codec Sha2Set.s128s) (wire m.val) (wire sk.val) (node Sha2Set.s128s addrnd)) ∧
      (∀ (m sig : Slice U8) (pk : Array U8 32#usize), Room m.length 152 →
        slhdsa.sets.sha2_128s.slh_verify_internal m sig pk =
          ok (byteVerify Sha2Set.s128s.vp Sha2Set.s128s.prims (codec Sha2Set.s128s) (wire m.val) (wire sig.val) (wire pk.val)))) ∧
    (Reduction.bytesAlg Link.vp (primsG (liftC realCF)) (codecG realCF) (optRandU oR realCF)
        ($ᵗ (Bytes 16)) =
      Reduction.bytesAlg Sha2Set.s128s.vp Sha2Set.s128s.prims (codec Sha2Set.s128s)
        (fun pk => oR pk.pkSeed pk.pkRoot) ($ᵗ (Bytes 16))) ∧
    (∀ (S : ForgerI) (qf qs ℓ : ℕ),
      (∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List SLHDSA.Byte) i = true) qf) →
      (∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List SLHDSA.Byte) i = true) qs) →
      (∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQ (S := List SLHDSA.Byte) ℓ i = true) 0) →
      (∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ) →
      (QcAll qf qs ℓ ≤ 2 ^ 126 →
        sufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤
          epsItsrF qf (2 * qs) qf (Itsr.itsrQc qs) (Itsr.itsrLc ℓ) qs ℓ +
            ((QlinT8 qf qs ℓ : ℕ) : ℝ≥0∞) / 2 ^ 128 +
            (polyP8 (QcAll qf qs ℓ) (NAll qs) qs (ellB ℓ) : ℝ≥0∞) / 2 ^ 256 ∧
        eufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤
          epsItsrF qf (2 * qs) qf (Itsr.itsrQc qs) (Itsr.itsrLc ℓ) qs ℓ +
            ((QlinT8 qf qs ℓ : ℕ) : ℝ≥0∞) / 2 ^ 128 +
            (polyP8 (QcAll qf qs ℓ) (NAll qs) qs (ellB ℓ) : ℝ≥0∞) / 2 ^ 256) ∧
      (qf ≤ 2 ^ 60 → qs ≤ 2 ^ 20 → ℓ ≤ 2 ^ 26 →
        sufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤
            ((2 : ℝ≥0∞) ^ 77)⁻¹ + ((2 : ℝ≥0∞) ^ 132)⁻¹ + ((2 : ℝ≥0∞) ^ 63)⁻¹ ∧
          eufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤
            ((2 : ℝ≥0∞) ^ 77)⁻¹ + ((2 : ℝ≥0∞) ^ 132)⁻¹ + ((2 : ℝ≥0∞) ^ 63)⁻¹) ∧
      (qf ≤ 2 ^ 64 → qs ≤ 2 ^ 40 → ℓ ≤ 2 ^ 26 →
        sufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤
            ((2 : ℝ≥0∞) ^ 63)⁻¹ + ((2 : ℝ≥0∞) ^ 94)⁻¹ + ((2 : ℝ≥0∞) ^ 59)⁻¹ ∧
          eufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤
            ((2 : ℝ≥0∞) ^ 63)⁻¹ + ((2 : ℝ≥0∞) ^ 94)⁻¹ + ((2 : ℝ≥0∞) ^ 59)⁻¹) ∧
      (qf ≤ 2 ^ 64 → qs ≤ 2 ^ 64 → ℓ ≤ 2 ^ 26 →
        sufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤
            ((2 : ℝ≥0∞) ^ 45)⁻¹ + ((2 : ℝ≥0∞) ^ 46)⁻¹ + ((2 : ℝ≥0∞) ^ 39)⁻¹ ∧
          eufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤
            ((2 : ℝ≥0∞) ^ 45)⁻¹ + ((2 : ℝ≥0∞) ^ 46)⁻¹ + ((2 : ℝ≥0∞) ^ 39)⁻¹)) :=
  ⟨⟨ME2E.sha2_128s.rust_keygen_bytes, ME2E.sha2_128s.rust_sign_internal_bytes,
      ME2E.sha2_128s.rust_verify_internal_bytes⟩,
    bytesAlg_realCF (fun _ pk => oR pk.pkSeed pk.pkRoot) ($ᵗ (Bytes 16)),
    fun S _ _ _ hqf hqs hlong hout =>
      ⟨fun hQ => ⟨suf_ideal_closed_tight8 S oR hqf hqs hlong hout hQ,
          euf_ideal_closed_tight8 S oR hqf hqs hlong hout hQ⟩,
        fun hf hs hℓ => ⟨suf_ideal_closed_tight8_2_20 S oR hqf hqs hlong hout hf hs hℓ,
          euf_ideal_closed_tight8_2_20 S oR hqf hqs hlong hout hf hs hℓ⟩,
        fun hf hs hℓ => ⟨suf_ideal_closed_tight8_2_40 S oR hqf hqs hlong hout hf hs hℓ,
          euf_ideal_closed_tight8_2_40 S oR hqf hqs hlong hout hf hs hℓ⟩,
        fun hf hs hℓ => ⟨suf_ideal_closed_tight8_2_64 S oR hqf hqs hlong hout hf hs hℓ,
          euf_ideal_closed_tight8_2_64 S oR hqf hqs hlong hout hf hs hℓ⟩⟩⟩

/-- **SLH-DSA-SHA2-128s, six-set tree, external pure interface: the Rust functions, and the closed
ideal-compression bound of the scheme they compute.**
`Ideal.rust_ideal_security_closed_pure_tight8` with conjunct 1 `PureBytesEndToEnd` (about
`slhdsa.sets.sha2_128s.{slh_keygen_internal, slh_sign, slh_verify}`) and conjunct 2 ending in the
scheme of conjunct 1; conjunct 3 verbatim (message parts of at most `2^26 - 257` bytes).
Conjunct 3 is about the IDEAL-MODEL scheme only. -/
theorem rust_ideal_security_closed_pure_tight8 (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) :
    PureBytesEndToEnd (fun pk => oR pk.pkSeed pk.pkRoot) ($ᵗ (Bytes 16)) ∧
    (Reduction.pureBytesAlg Link.vp (primsG (liftC realCF)) (codecG realCF) (optRandU oR realCF)
        ($ᵗ (Bytes 16)) =
      Reduction.pureBytesAlg Sha2Set.s128s.vp Sha2Set.s128s.prims (codec Sha2Set.s128s)
        (fun pk => oR pk.pkSeed pk.pkRoot) ($ᵗ (Bytes 16))) ∧
    (∀ (S : ForgerP) (qf qs ℓ : ℕ),
      (∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQP i = true) qf) →
      (∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQP i = true) qs) →
      (∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQP ℓ i = true) 0) →
      (∀ pk, ∀ z ∈ support (S.main pk), z.1.1.length ≤ ℓ) →
      (QcAll qf qs (ℓ + 257) ≤ 2 ^ 126 →
        sufP S (optRandU oR) ($ᵗ (Bytes 16)) ≤
          epsItsrF qf (2 * qs) qf (Itsr.itsrQc qs) (Itsr.itsrLc (ℓ + 257)) qs (ℓ + 257) +
            ((QlinT8 qf qs (ℓ + 257) : ℕ) : ℝ≥0∞) / 2 ^ 128 +
            (polyP8 (QcAll qf qs (ℓ + 257)) (NAll qs) qs (ellB (ℓ + 257)) : ℝ≥0∞) / 2 ^ 256 ∧
        eufP S (optRandU oR) ($ᵗ (Bytes 16)) ≤
          epsItsrF qf (2 * qs) qf (Itsr.itsrQc qs) (Itsr.itsrLc (ℓ + 257)) qs (ℓ + 257) +
            ((QlinT8 qf qs (ℓ + 257) : ℕ) : ℝ≥0∞) / 2 ^ 128 +
            (polyP8 (QcAll qf qs (ℓ + 257)) (NAll qs) qs (ellB (ℓ + 257)) : ℝ≥0∞) / 2 ^ 256) ∧
      (qf ≤ 2 ^ 60 → qs ≤ 2 ^ 20 → ℓ + 257 ≤ 2 ^ 26 →
        sufP S (optRandU oR) ($ᵗ (Bytes 16)) ≤
            ((2 : ℝ≥0∞) ^ 77)⁻¹ + ((2 : ℝ≥0∞) ^ 132)⁻¹ + ((2 : ℝ≥0∞) ^ 63)⁻¹ ∧
          eufP S (optRandU oR) ($ᵗ (Bytes 16)) ≤
            ((2 : ℝ≥0∞) ^ 77)⁻¹ + ((2 : ℝ≥0∞) ^ 132)⁻¹ + ((2 : ℝ≥0∞) ^ 63)⁻¹) ∧
      (qf ≤ 2 ^ 64 → qs ≤ 2 ^ 40 → ℓ + 257 ≤ 2 ^ 26 →
        sufP S (optRandU oR) ($ᵗ (Bytes 16)) ≤
            ((2 : ℝ≥0∞) ^ 63)⁻¹ + ((2 : ℝ≥0∞) ^ 94)⁻¹ + ((2 : ℝ≥0∞) ^ 59)⁻¹ ∧
          eufP S (optRandU oR) ($ᵗ (Bytes 16)) ≤
            ((2 : ℝ≥0∞) ^ 63)⁻¹ + ((2 : ℝ≥0∞) ^ 94)⁻¹ + ((2 : ℝ≥0∞) ^ 59)⁻¹) ∧
      (qf ≤ 2 ^ 64 → qs ≤ 2 ^ 64 → ℓ + 257 ≤ 2 ^ 26 →
        sufP S (optRandU oR) ($ᵗ (Bytes 16)) ≤
            ((2 : ℝ≥0∞) ^ 45)⁻¹ + ((2 : ℝ≥0∞) ^ 46)⁻¹ + ((2 : ℝ≥0∞) ^ 39)⁻¹ ∧
          eufP S (optRandU oR) ($ᵗ (Bytes 16)) ≤
            ((2 : ℝ≥0∞) ^ 45)⁻¹ + ((2 : ℝ≥0∞) ^ 46)⁻¹ + ((2 : ℝ≥0∞) ^ 39)⁻¹)) :=
  ⟨pure_bytes_end_to_end _ _,
    pureBytesAlg_realCF (fun _ pk => oR pk.pkSeed pk.pkRoot) ($ᵗ (Bytes 16)),
    fun S _ _ _ hqf hqs hlong hout =>
      ⟨fun hQ => ⟨suf_ideal_pure_closed_tight8 S oR hqf hqs hlong hout hQ,
          euf_ideal_pure_closed_tight8 S oR hqf hqs hlong hout hQ⟩,
        fun hf hs hℓ => ⟨suf_ideal_pure_closed_tight8_2_20 S oR hqf hqs hlong hout hf hs hℓ,
          euf_ideal_pure_closed_tight8_2_20 S oR hqf hqs hlong hout hf hs hℓ⟩,
        fun hf hs hℓ => ⟨suf_ideal_pure_closed_tight8_2_40 S oR hqf hqs hlong hout hf hs hℓ,
          euf_ideal_pure_closed_tight8_2_40 S oR hqf hqs hlong hout hf hs hℓ⟩,
        fun hf hs hℓ => ⟨suf_ideal_pure_closed_tight8_2_64 S oR hqf hqs hlong hout hf hs hℓ,
          euf_ideal_pure_closed_tight8_2_64 S oR hqf hqs hlong hout hf hs hℓ⟩⟩⟩

/-- **SLH-DSA-SHA2-128s, six-set tree, the interface functions: the closed ideal-compression
bound of the scheme they compute.**  `Ideal.api_ideal_security_closed_pure_tight8` with
conjunct 1 `ME2E.sha2_128s.ApiPureBytesEndToEnd` (about `slhdsa.sets.sha2_128s.{keygen, sign,
sign_deterministic, verify}`); conjuncts 2 and 3 those of
`rust_ideal_security_closed_pure_tight8`.  Conjunct 3 is about the IDEAL-MODEL scheme only. -/
theorem api_ideal_security_closed_pure_tight8 (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) :
    ME2E.sha2_128s.ApiPureBytesEndToEnd (fun pk => oR pk.pkSeed pk.pkRoot) ($ᵗ (Bytes 16)) ∧
    (Reduction.pureBytesAlg Link.vp (primsG (liftC realCF)) (codecG realCF) (optRandU oR realCF)
        ($ᵗ (Bytes 16)) =
      Reduction.pureBytesAlg Sha2Set.s128s.vp Sha2Set.s128s.prims (codec Sha2Set.s128s)
        (fun pk => oR pk.pkSeed pk.pkRoot) ($ᵗ (Bytes 16))) ∧
    (∀ (S : ForgerP) (qf qs ℓ : ℕ),
      (∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQP i = true) qf) →
      (∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQP i = true) qs) →
      (∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQP ℓ i = true) 0) →
      (∀ pk, ∀ z ∈ support (S.main pk), z.1.1.length ≤ ℓ) →
      (QcAll qf qs (ℓ + 257) ≤ 2 ^ 126 →
        sufP S (optRandU oR) ($ᵗ (Bytes 16)) ≤
          epsItsrF qf (2 * qs) qf (Itsr.itsrQc qs) (Itsr.itsrLc (ℓ + 257)) qs (ℓ + 257) +
            ((QlinT8 qf qs (ℓ + 257) : ℕ) : ℝ≥0∞) / 2 ^ 128 +
            (polyP8 (QcAll qf qs (ℓ + 257)) (NAll qs) qs (ellB (ℓ + 257)) : ℝ≥0∞) / 2 ^ 256 ∧
        eufP S (optRandU oR) ($ᵗ (Bytes 16)) ≤
          epsItsrF qf (2 * qs) qf (Itsr.itsrQc qs) (Itsr.itsrLc (ℓ + 257)) qs (ℓ + 257) +
            ((QlinT8 qf qs (ℓ + 257) : ℕ) : ℝ≥0∞) / 2 ^ 128 +
            (polyP8 (QcAll qf qs (ℓ + 257)) (NAll qs) qs (ellB (ℓ + 257)) : ℝ≥0∞) / 2 ^ 256) ∧
      (qf ≤ 2 ^ 60 → qs ≤ 2 ^ 20 → ℓ + 257 ≤ 2 ^ 26 →
        sufP S (optRandU oR) ($ᵗ (Bytes 16)) ≤
            ((2 : ℝ≥0∞) ^ 77)⁻¹ + ((2 : ℝ≥0∞) ^ 132)⁻¹ + ((2 : ℝ≥0∞) ^ 63)⁻¹ ∧
          eufP S (optRandU oR) ($ᵗ (Bytes 16)) ≤
            ((2 : ℝ≥0∞) ^ 77)⁻¹ + ((2 : ℝ≥0∞) ^ 132)⁻¹ + ((2 : ℝ≥0∞) ^ 63)⁻¹) ∧
      (qf ≤ 2 ^ 64 → qs ≤ 2 ^ 40 → ℓ + 257 ≤ 2 ^ 26 →
        sufP S (optRandU oR) ($ᵗ (Bytes 16)) ≤
            ((2 : ℝ≥0∞) ^ 63)⁻¹ + ((2 : ℝ≥0∞) ^ 94)⁻¹ + ((2 : ℝ≥0∞) ^ 59)⁻¹ ∧
          eufP S (optRandU oR) ($ᵗ (Bytes 16)) ≤
            ((2 : ℝ≥0∞) ^ 63)⁻¹ + ((2 : ℝ≥0∞) ^ 94)⁻¹ + ((2 : ℝ≥0∞) ^ 59)⁻¹) ∧
      (qf ≤ 2 ^ 64 → qs ≤ 2 ^ 64 → ℓ + 257 ≤ 2 ^ 26 →
        sufP S (optRandU oR) ($ᵗ (Bytes 16)) ≤
            ((2 : ℝ≥0∞) ^ 45)⁻¹ + ((2 : ℝ≥0∞) ^ 46)⁻¹ + ((2 : ℝ≥0∞) ^ 39)⁻¹ ∧
          eufP S (optRandU oR) ($ᵗ (Bytes 16)) ≤
            ((2 : ℝ≥0∞) ^ 45)⁻¹ + ((2 : ℝ≥0∞) ^ 46)⁻¹ + ((2 : ℝ≥0∞) ^ 39)⁻¹)) :=
  ⟨ME2E.sha2_128s.api_pure_bytes_end_to_end _ _, (rust_ideal_security_closed_pure_tight8 oR).2⟩

end MIdeal.sha2_128s
