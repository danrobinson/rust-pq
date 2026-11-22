import E2E.GuardedRom
import E2E.Api

/-!
# Random-oracle model for the external pure interface (context strings)

`E2E.end_to_end` (field `security`, from `Link.security_128s`) bounds forgers against
`romScheme prims.core (Equiv.refl _) optRand pkSeedDist`, FIPS 205's **internal** algorithms
(Alg. 18–20) with the tweakable hash, `H_msg` and `PRF_msg` as three independent random oracles.
The crate's interface (`slh_sign`, `slh_verify`, and the module `api`) is the **external pure**
interface (Alg. 22/24), whose messages are `(message, context)` pairs.  This file gives the
random-oracle theorem for that interface, by the reduction already used in the standard model
(`Reduction.toInternal`) and in the ideal model (`ForgerP.toI`), now over the random-oracle
interface:

* `pureRomScheme optRand pkSeedDist` — the external pure scheme in the random-oracle model:
  `GuardedRom.scheme (romScheme …) Reduction.pureEncode`, i.e. signing `(M, ctx)` returns the
  error `contextTooLong` if `|ctx| > 255` and otherwise `.ok` of the random-oracle signature of
  `M' = 0x00 ‖ toByte(|ctx|, 1) ‖ ctx ‖ M`; verification accepts only `.ok σ` with `|ctx| ≤ 255`
  and then verifies `σ` on `M'`.  Its signature type is that of `Reduction.externalAlg`.
* `pureRomScheme_instantiation` — with its three oracles answered by the SHA-2 functions, it is
  exactly `Reduction.externalAlg vp prims optRand pkSeedDist`, the typed scheme the Rust code is
  linked to by `PureEndToEnd` / `ApiPureEndToEnd`.
* `toInternalRom` — the wrapper forger against the internal random-oracle scheme;
  `pure_rom_advantage_le` (advantage does not decrease), `toInternalRom_romQueryBound` (same
  `qh`, same `qs`).
* `pure_security_128s`, `pure_security_128s_euf` — the bound: **exactly the internal bound**
  `securityBound vp.params (256 ^ 16) 2 1 qh qs`, with the same `qh` and `qs`.
* Headlines `pure_rom_security` (functions `slh_keygen_internal`, `slh_sign`, `slh_verify`) and
  `api_pure_rom_security` (functions `api.keygen`, `api.sign`, `api.sign_deterministic`,
  `api.verify`).

**The bound.**  The internal bound `securityBound vp.params (256^16) 2 1 qh qs` depends only on
the parameter set, the number `qh` of the forger's hash queries and the number `qs` of its signing
queries — not on message lengths.  The wrapper forwards each hash query once and turns each
signing query into at most one signing query (none for an over-long context), so the pure bound
is the internal bound at the same `(qh, qs)`: nothing grows.  The internal messages the wrapper
signs and forges on are at most 257 bytes longer than the external ones (`2 + |ctx|`,
`|ctx| ≤ 255`); since the bound does not mention message length this costs nothing.  The hash
queries made by the signing oracle and the verifier on the longer `M'` are the scheme's own and
are not charged to the forger, as in the internal theorem.
-/

namespace E2E

open Aeneas Aeneas.Std Result
open SLHDSA SLHDSA.Concrete SLHDSA.Security OracleComp OracleSpec SignatureAlg ENNReal
open slhdsa (bytes Room)
open Link (vp prims cv sp sigBytes pkBytes skBytes)
open Reduction (externalAlg pureEncode constSig byteKeygen byteSignPure byteVerifyPure codec128s)

/-! ### The scheme -/

/-- **The external pure SLH-DSA scheme in the random-oracle model** (FIPS 205 Alg. 21/22/24 on
top of the three-oracle `romScheme` of `Link.security_128s`).  Messages are `(message, context)`
pairs of byte lists; signatures are `Except External.Error (SignatureCore …)`.

* key generation is that of `romScheme` (`PK.seed ← pkSeedDist`, `SK.seed`, `SK.prf` uniform, the
  root computed with oracle queries);
* signing `(M, ctx)`: if `|ctx| > 255` the error `contextTooLong |ctx|` (nothing sampled, no
  query); otherwise `.ok σ` with `σ ← romScheme.sign pk sk (0x00 ‖ |ctx| ‖ ctx ‖ M)` (draws
  `opt_rand ← optRand pk`, queries `PRF_msg`, signs with oracle queries);
* verifying `(M, ctx)` against `.ok σ`: `romScheme.verify pk (0x00 ‖ |ctx| ‖ ctx ‖ M) σ` if
  `|ctx| ≤ 255`, `false` otherwise; an error value is never accepted. -/
noncomputable def pureRomScheme (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (pkSeedDist : ProbComp prims.PkSeed) :
    SignatureAlg (OracleComp (unifSpec + hashSpec prims.core)) (List SLHDSA.Byte × List SLHDSA.Byte)
      (PublicKeyCore prims.core) (SecretKeyCore prims.core)
      (Except External.Error (GeneralScheme.SignatureCore vp prims.core)) :=
  GuardedRom.scheme (romScheme (vp := vp) prims.core (Equiv.refl _) optRand pkSeedDist) pureEncode

/-- Signing in `pureRomScheme` with a context of at most 255 bytes is internal random-oracle
signing of `0x00 ‖ |ctx| ‖ ctx ‖ M`. -/
theorem pureRomScheme_sign (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (pkSeedDist : ProbComp prims.PkSeed) (pk : PublicKeyCore prims.core)
    (sk : SecretKeyCore prims.core) (message context : List SLHDSA.Byte)
    (h : context.length ≤ 255) :
    (pureRomScheme optRand pkSeedDist).sign pk sk (message, context) =
      Except.ok <$> (romScheme (vp := vp) prims.core (Equiv.refl _) optRand pkSeedDist).sign pk sk
        ([0, UInt8.ofNat context.length] ++ context ++ message) := by
  simp only [pureRomScheme, GuardedRom.scheme, pureEncode,
    External.encodePureMessage_eq_ok context message h]

/-- Signing with an over-long context returns the error and makes no query. -/
theorem pureRomScheme_sign_tooLong (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (pkSeedDist : ProbComp prims.PkSeed) (pk : PublicKeyCore prims.core)
    (sk : SecretKeyCore prims.core) (message context : List SLHDSA.Byte)
    (h : 255 < context.length) :
    (pureRomScheme optRand pkSeedDist).sign pk sk (message, context) =
      pure (.error (.contextTooLong context.length)) := by
  have he : External.encodePureMessage context message =
      .error (.contextTooLong context.length) := by
    unfold External.encodePureMessage External.encodeMessage
    rw [External.requireContext_eq_error context h]; rfl
  simp only [pureRomScheme, GuardedRom.scheme, pureEncode, he]

/-- Verification in `pureRomScheme` of a signature value with a context of at most 255 bytes is
internal random-oracle verification of `0x00 ‖ |ctx| ‖ ctx ‖ M`. -/
theorem pureRomScheme_verify_ok (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (pkSeedDist : ProbComp prims.PkSeed) (pk : PublicKeyCore prims.core)
    (message context : List SLHDSA.Byte) (σ : GeneralScheme.SignatureCore vp prims.core)
    (h : context.length ≤ 255) :
    (pureRomScheme optRand pkSeedDist).verify pk (message, context) (.ok σ) =
      (romScheme (vp := vp) prims.core (Equiv.refl _) optRand pkSeedDist).verify pk
        ([0, UInt8.ofNat context.length] ++ context ++ message) σ := by
  simp only [pureRomScheme, GuardedRom.scheme, pureEncode,
    External.encodePureMessage_eq_ok context message h]

/-- **Instantiation.**  Answering the three oracles of `pureRomScheme` by the SHA-2 functions of
FIPS 205 §11.2.1 (`romAnswer prims`), uniform sampling untouched, gives exactly
`Reduction.externalAlg vp prims optRand pkSeedDist`, the typed external pure scheme of
`PureEndToEnd` / `ApiPureEndToEnd`.  An identity of programs; it does not transfer the bound. -/
theorem pureRomScheme_instantiation (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (pkSeedDist : ProbComp prims.PkSeed) :
    (pureRomScheme optRand pkSeedDist).map (simulateQ' (unifFwdAnswerImpl (romAnswer prims))) =
      externalAlg vp prims optRand pkSeedDist := by
  rw [pureRomScheme, GuardedRom.map_scheme, Link.romScheme_map_romAnswer_128s]
  rfl

/-! ### The reduction and the bound -/

/-- **The wrapper forger.**  `toInternalRom S`, on the public key `pk`: runs `S pk` once;
forwards every uniform-sampling and hash query unchanged; answers a signing query `(M, ctx)`
with the error if `|ctx| > 255` (no query) and otherwise with `.ok σ`, `σ` the answer of its own
signing oracle on `0x00 ‖ |ctx| ‖ ctx ‖ M` (one query); outputs `(0x00 ‖ |ctx| ‖ ctx ‖ M, σ)`
when `S` outputs `((M, ctx), .ok σ)` with `|ctx| ≤ 255`, and the fixed pair
`([], constSig default)` otherwise (where `S` has lost). -/
noncomputable def toInternalRom {optRand : PublicKeyCore prims.core → ProbComp prims.Y}
    {pkSeedDist : ProbComp prims.PkSeed}
    (S : StrongUnforgeableAdversary (pureRomScheme optRand pkSeedDist)) :
    StrongUnforgeableAdversary (romScheme (vp := vp) prims.core (Equiv.refl _) optRand pkSeedDist) :=
  GuardedRom.reduceS _ pureEncode ([], constSig default) S

/-- **Pure advantage ≤ internal advantage** in the random-oracle model, by injectivity of
`(M, ctx) ↦ 0x00 ‖ |ctx| ‖ ctx ‖ M` on `|ctx| ≤ 255` (`Reduction.pureEncode_injective`). -/
theorem pure_rom_advantage_le {optRand : PublicKeyCore prims.core → ProbComp prims.Y}
    {pkSeedDist : ProbComp prims.PkSeed}
    (S : StrongUnforgeableAdversary (pureRomScheme optRand pkSeedDist)) :
    strongUnforgeableAdvantage (ProbCompRuntime.rom (hashSpec prims.core)) S ≤
      strongUnforgeableAdvantage (ProbCompRuntime.rom (hashSpec prims.core)) (toInternalRom S) :=
  GuardedRom.strongUnforgeableAdvantage_le _ pureEncode Reduction.pureEncode_injective _ S

/-- **Resources of the wrapper**: if `S` makes at most `qh` hash queries and `qs` signing
queries (on every path, for every public key), so does `toInternalRom S`. -/
theorem toInternalRom_romQueryBound {optRand : PublicKeyCore prims.core → ProbComp prims.Y}
    {pkSeedDist : ProbComp prims.PkSeed}
    (S : StrongUnforgeableAdversary (pureRomScheme optRand pkSeedDist)) {qh qs : ℕ}
    (hS : S.RomQueryBound qh qs) : (toInternalRom S).RomQueryBound qh qs :=
  GuardedRom.romQueryBound_reduceS _ pureEncode _ S hS

/-- **SUF-CMA security of the external pure interface of SLH-DSA-SHA2-128s in the three-oracle
model.**  Every strong forger against `pureRomScheme optRand pkSeedDist` — it gets the public key,
the three random oracles and a signing oracle on `(message, context)` pairs, and wins with a pair
`((M, ctx), s)` that verifies and was never returned by the signing oracle — making at most `qh`
hash and `qs` signing queries wins with probability at most
`securityBound vp.params (256 ^ 16) 2 1 qh qs`: the internal bound of `Link.security_128s` at the
same `qh`, `qs`.  For every `opt_rand` source and every distribution of `PK.seed`. -/
theorem pure_security_128s (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (pkSeedDist : ProbComp prims.PkSeed)
    (S : StrongUnforgeableAdversary (pureRomScheme optRand pkSeedDist)) {qh qs : ℕ}
    (hS : S.RomQueryBound qh qs) :
    strongUnforgeableAdvantage (ProbCompRuntime.rom (hashSpec prims.core)) S ≤
      securityBound vp.params (256 ^ 16) 2 1 qh qs :=
  (pure_rom_advantage_le S).trans
    (Link.security_128s (Equiv.refl _) optRand pkSeedDist (toInternalRom S)
      (toInternalRom_romQueryBound S hS))

/-- **EUF-CMA security of the external pure interface in the three-oracle model**: the same bound
for a forgery on a `(message, context)` pair never submitted. -/
theorem pure_security_128s_euf (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (pkSeedDist : ProbComp prims.PkSeed)
    (A : UnforgeableAdversary (pureRomScheme optRand pkSeedDist)) {qh qs : ℕ}
    (hA : A.RomQueryBound qh qs) :
    unforgeableAdvantage (ProbCompRuntime.rom (hashSpec prims.core)) A ≤
      securityBound vp.params (256 ^ 16) 2 1 qh qs :=
  (unforgeableAdvantage_le_strongUnforgeableAdvantage _ A).trans
    (pure_security_128s optRand pkSeedDist ⟨A.main⟩ hA)

/-! ### Headlines: the Rust functions -/

/-- **The Rust external pure interface and its security in the random-oracle model.**

Fix how `opt_rand` and `PK.seed` are sampled (`optRand`, `pkSeedDist`; arbitrary).  Let
`X = Reduction.externalAlg vp prims optRand pkSeedDist` (FIPS 205 Alg. 21/22/24 at
SLH-DSA-SHA2-128s, messages `(message, context)`) and `R = pureRomScheme optRand pkSeedDist`
(the same with the tweakable hash, `H_msg` and `PRF_msg` as three oracles).

1. `PureEndToEnd optRand pkSeedDist`: the Rust `slh_keygen_internal`, `slh_sign`, `slh_verify`
   never panic and compute the deterministic cores of `X` on the FIPS byte encodings (under
   `Room m.length 409`), and `X` is correct.
2. `X` is `R` with its oracles answered by the SHA-2 functions (`romAnswer prims`).
3. SUF-CMA: every strong forger against `R` with at most `qh` hash and `qs` signing queries has
   advantage at most `securityBound vp.params (256 ^ 16) 2 1 qh qs` when the three oracles are
   independent random oracles (`ProbCompRuntime.rom`).
4. EUF-CMA: the same for every chosen-message forger.

The bound is that of the internal interface (`EndToEnd.security`) at the same `qh`, `qs`.  Same
caveat as `EndToEnd`: nothing transfers the bound from `R` to `X` (the SHA-256 instantiation);
that step is the random-oracle methodology.  The Rust code computes only the deterministic cores;
sampling the seeds and `addrnd` is the caller's obligation.  Pure mode only. -/
theorem pure_rom_security (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (pkSeedDist : ProbComp prims.PkSeed) :
    PureEndToEnd optRand pkSeedDist ∧
    (pureRomScheme optRand pkSeedDist).map (simulateQ' (unifFwdAnswerImpl (romAnswer prims))) =
      externalAlg vp prims optRand pkSeedDist ∧
    (∀ (S : StrongUnforgeableAdversary (pureRomScheme optRand pkSeedDist)) (qh qs : ℕ),
      S.RomQueryBound qh qs →
      strongUnforgeableAdvantage (ProbCompRuntime.rom (hashSpec prims.core)) S ≤
        securityBound vp.params (256 ^ 16) 2 1 qh qs) ∧
    ∀ (A : UnforgeableAdversary (pureRomScheme optRand pkSeedDist)) (qh qs : ℕ),
      A.RomQueryBound qh qs →
      unforgeableAdvantage (ProbCompRuntime.rom (hashSpec prims.core)) A ≤
        securityBound vp.params (256 ^ 16) 2 1 qh qs :=
  ⟨pure_end_to_end optRand pkSeedDist, pureRomScheme_instantiation optRand pkSeedDist,
    fun S _ _ hS => pure_security_128s optRand pkSeedDist S hS,
    fun A _ _ hA => pure_security_128s_euf optRand pkSeedDist A hA⟩

/-- **The Rust interface `api` and its security in the random-oracle model.**  `pure_rom_security`
with `ApiPureEndToEnd` in place of `PureEndToEnd`: `api.keygen` (on the three 16-byte blocks
`SK.seed ‖ SK.prf ‖ PK.seed` of its 48-byte argument), `api.sign`, `api.sign_deterministic` (with
`addrnd` the `PK.seed` block of the key, i.e. the scheme at `optRand pk = pure pk.pkSeed`) and
`api.verify` never panic and compute the deterministic cores of `X = externalAlg …`; `X` is
`pureRomScheme` instantiated with SHA-2; and `pureRomScheme` with random oracles satisfies the
SUF-CMA and EUF-CMA bound `securityBound vp.params (256 ^ 16) 2 1 qh qs`.  Caveats as in
`pure_rom_security`. -/
theorem api_pure_rom_security (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (pkSeedDist : ProbComp prims.PkSeed) :
    ApiPureEndToEnd optRand pkSeedDist ∧
    (pureRomScheme optRand pkSeedDist).map (simulateQ' (unifFwdAnswerImpl (romAnswer prims))) =
      externalAlg vp prims optRand pkSeedDist ∧
    (∀ (S : StrongUnforgeableAdversary (pureRomScheme optRand pkSeedDist)) (qh qs : ℕ),
      S.RomQueryBound qh qs →
      strongUnforgeableAdvantage (ProbCompRuntime.rom (hashSpec prims.core)) S ≤
        securityBound vp.params (256 ^ 16) 2 1 qh qs) ∧
    ∀ (A : UnforgeableAdversary (pureRomScheme optRand pkSeedDist)) (qh qs : ℕ),
      A.RomQueryBound qh qs →
      unforgeableAdvantage (ProbCompRuntime.rom (hashSpec prims.core)) A ≤
        securityBound vp.params (256 ^ 16) 2 1 qh qs :=
  ⟨api_pure_end_to_end optRand pkSeedDist, (pure_rom_security optRand pkSeedDist).2⟩

end E2E

#print axioms E2E.pureRomScheme_sign
#print axioms E2E.pureRomScheme_sign_tooLong
#print axioms E2E.pureRomScheme_verify_ok
#print axioms E2E.pureRomScheme_instantiation
#print axioms E2E.pure_rom_advantage_le
#print axioms E2E.toInternalRom_romQueryBound
#print axioms E2E.pure_security_128s
#print axioms E2E.pure_security_128s_euf
#print axioms E2E.pure_rom_security
#print axioms E2E.api_pure_rom_security
