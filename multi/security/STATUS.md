# multi/security — security of SLH-DSA-SHA2, all six parameter sets: status

Lean 4.36.0, Lake project `multi/security/`. Extends `security/` (SHA2-128s only) to SLH-DSA-SHA2-{128s,128f,192s,192f,256s,256f}. **State: closed
for the portable (default) build of the current `multi/rust`** (2026-11-22).
Everything below is proved for all six sets; no `sorry`, `axiom`, `native_decide`, `bv_decide`; nothing conditional. Nothing outside `multi/security/`
was modified (no file added to `security/`). No defect found in `multi/lean` or `multi/rust`. Re-run: `scripts/check.sh` (`scripts/check.sh clean` for
a from-scratch build).

**2026-11-22 update (after the rewrite of `multi/rust` / re-proof of `multi/lean`).** Before: `MLink`, `MReduction` and `ME2E.Basic` still built
against the new `multi/lean`; `ME2E.Sha2_128s` and `ME2E.Sha2_128f` did not (6 errors each): they called `slhdsa.sha2_128{s,f}.*_correct` with
`Room m.length 304 / 561`, whereas `multi/lean` now states the n = 16 sets with `Room m.length 152 / 409` (the single-set tree's constants). The
other four sets built unchanged (same names `slhdsa.sha2_<set>.*_correct`, `slhdsa.sets.sha2_<set>.slh_*`). Repair: the generator
(`ME2E/gen/gen.py`) takes the slack per set (152/409 for n = 16, 304/561 otherwise), so the 128s/128f headlines are now *stronger* than before
(weaker hypothesis) and their 128s statements are character-for-character the single-set `E2E.*` ones up to the renamings (textual check in the
generator; it no longer needs "modulo `Room`"). New: §3a (the `api` functions, the checked signers, typed end-to-end forms) and §4a (the
random-oracle theorem for the context-string interface, typed and byte level, Rust and `api` forms), for all six sets.

## Layout

| library | source | content |
|---|---|---|
| `Spec`, `Slhdsa` | `multi/lean`, compiled in place (`srcDir`) | parameterised FIPS 205 spec; Rust extraction + refinement |
| `Reduction` | `security/Reduction/*.lean`, compiled in place, **unmodified** | generic standard-model reduction (65 modules; not `Gen/`) |
| `LinkSecurity` | `security/Link/Security.lean`, in place, unmodified | VCVio-only ROM file that `Reduction` imports |
| `Shim` | `shim/Link/{Basic,Hash,Verify}.lean`, `shim/Reduction/PrfDomainNonVacuity.lean` | see below |
| `MLink` (15 modules) | `MLink/` | Spec = VCVio scheme, one proof generic in `S : MLink.Sha2Set`; ROM statement |
| `MReduction` (8) | `MReduction/` | Reduction headlines, linear forms, corollaries, resources, audit at the six sets |
| `E2ERom` | `security/E2E/{GuardedRom,CodedRom}.lean`, in place, unmodified | scheme behind a partial message encoding / seen through encodings, over any oracle interface (no parameter set in them) |
| `ME2E` (21) | `ME2E/` | Rust `sets.sha2_<set>.slh_*` = scheme cores; ten headline theorems per set (`Sha2_<set>`); `api` + checked signers + typed forms (`Api`, `Api/Sha2_<set>`); pure-interface ROM theorem (`PureRom`, `Rom/Sha2_<set>`) |

**How security's Reduction is imported.** A path dependency or a wholesale import is impossible: `security/Link` is built on the single-set `Spec` of
`/lean`, whose declaration names (`Spec.PRF`, …) clash with the parameterised `Spec` of `multi/lean`, and 24 `Reduction` modules mention `Link.vp`,
`Link.prims` (their 128s instances). Resolution, with no change to `security/`: `Reduction` is a `lean_lib` with `srcDir = "../../security"` and an
explicit root list; its imports `Link.Basic`, `Link.Hash`, `Link.Verify` are satisfied by three stand-in modules in `shim/` that keep, verbatim, only
the Spec-free declarations (`Link.S128`, `vp`, `prims`, `Node`, `Dom`, `BaseDom`, `decodeSig`, `decodePk`); `Link.Security` is the original file. The
one `Reduction` module that mentions the old `Spec`, `PrfDomainNonVacuity`, is replaced by a copy with exactly one theorem (`prf_128s_spec`, 7 lines)
removed — `check.sh` diffs it against the original; its generic replacement is `MReduction.prf_spec S`. So every generic theorem and every `*_128s`
theorem of `security/Reduction` is the same source here, and `MReduction/Check128s.lean` shows ten of our `.s128s` statements are `rfl`-equal to them.
`security`'s own `Link` (rest), `E2E`, `Ideal`, `Reduction/Gen` are not built here.

Vocabulary (`MLink/Basic.lean`): `inductive Sha2Set | s128s | s128f | s192s | s192f | s256s | s256f`; `S.fips : FipsParameterSet`, `S.spec :
Spec.Params` (`Spec.sha2_128s` …), `S.vp := S.fips.validatedParams`, `S.prims := sha2Primitives S.vp.params` (`= approvedPrimitives S.fips`,
`prims_eq_approved`), `S.Node := Bytes S.vp.params.n`; `sp`/`cv` (UInt8 ↔ BitVec 8 lists), `nd`, `sigBytes S`, `pkBytes S`, `skBytes S`; numeric
agreement of the two parameter records by `cases S <;> decide`. `MReduction.codec S := sha2WireCodec S.vp.params` (`= approvedWireCodec S.fips` by
`rfl` per set; for a variable `S` the two are only `HEq`, hence this spelling; same for `MLink.decodeSig S`, `decodePk S`).

## 1. Link (generic in `S`; verbatim)

```lean
theorem MLink.sha512_eq (b : ByteArray) : spA (sha512 b) = Spec.sha512 (spA b)          -- VCVio Sha2.lean; no length bound
theorem MLink.hmacSha512_eq (key msg) : spA (hmacSha512 key msg) = Spec.hmacSha512 (spA key) (spA msg)
theorem MLink.mgf1Sha512_eq (seed l) : spA (mgf1Sha512 seed l) = Spec.mgf1 Spec.sha512 64 (spA seed) l   -- all l
-- likewise sha256_eq, hmacSha256_eq, mgf1Sha256_eq;  F_eq, H_eq, PRF_eq (hyp. Dom a), Tl_eq (Dom a, ys.length ≠ 1), PRFmsg_eq, Hmsg_eq
theorem MLink.keygen_eq (skSeed skPrf pkSeed : S.Node) :
    Spec.slhKeygenInternal S.spec (nd skSeed) (nd skPrf) (nd pkSeed) =
      (skBytes S (GeneralScheme.keygenInternal S.vp S.prims skSeed skPrf pkSeed).2, pkBytes S (….1))
theorem MLink.sign_eq (msg : Spec.Bytes) (sk : SecretKeyCore S.prims.core) (addrnd : S.Node) :
    Spec.slhSignInternal S.spec msg (skBytes S sk) (nd addrnd) =
      sigBytes S (GeneralScheme.signInternal S.vp S.prims (cv msg) sk addrnd)
theorem MLink.slhSign_eq (msg ctx) (sk) (addrnd) : Spec.slhSign S.spec msg ctx (skBytes S sk) (nd addrnd) =
      (External.signPureWithRandomizer S.vp S.prims (cv msg) (cv ctx) sk addrnd).toOption.map (sigBytes S)
theorem MLink.verify_eq (msg sig pk : Spec.Bytes) (hp : pk.length = 2 * S.spec.n) :
    Spec.slhVerifyInternal S.spec msg sig pk =
      match decodeSig S (cv sig), decodePk S (cv pk) with
      | .ok s, .ok k => GeneralScheme.verifyInternal S.vp S.prims (cv msg) s k
      | _, _ => false
theorem MLink.slhVerify_eq …  -- same with Spec.slhVerify … ctx and External.verifyPure … (cv ctx) k
```
Byte forms: `keygen_eq_bytes`, `sign_eq_bytes`, `slhSign_eq_bytes` (existential over `decodeSk S`), `decodeSig_ok/_error` (length `S.spec.sigBytes`),
`decodePk_ok`, `decodeSk_ok`, `sp_encodeSignature`, `sp_encodePublicKey`. Address-domain facts re-derived for every set (layer < 256, tree < 2^64
incl. 256f where h − h' = 64 and treeBytes = 8, leaf < 2^h', FORS index < 2^32; digest split incl. sets with k·a not a multiple of 8; 128f's two-block
MGF1). `T_l` is only applied at lengths `len`, `k` (≠ 1). No Spec/VCVio discrepancy at any set. Details: `status/B.md`, `status/C.md`.

## 2. Reduction instances (`MReduction`; details and full numerals table: `status/D.md`)

Naming: generic `MReduction.slhdsa_sha2_<base> (S : Sha2Set)` and per set `MReduction.slhdsa_sha2_<set>_<base>`, `<set>` ∈ 128s, 128f, 192s, 192f,
256s, 256f; `<base>` ∈ `{bytes,pure_bytes}_{suf,euf}_cma_final` (+ `_final_explicit`), `{suf,euf,pure_suf,pure_euf}_cma_final_memo`,
`{,pure_}{,bytes_}{suf,euf}_cma_{deterministic,hedged}`, `{…}_cma_final_linear`, `{bytes,pure_bytes}_{suf,euf}_cma_linear`, `_final_tight`,
`_final_split`. Resources: `final_resources_final_<set>`, `final_resources_final_external_<set>`, `directCounts<set>`, `arityTargets_<set>`,
`thashArityProblemT_cap_<set>`, `wotsTcrProblemT_cap_<set>`, …. `structural S : Reduction.Structural S.vp S.prims`, `keyDiscipline S`. Verbatim:

```lean
theorem slhdsa_sha2_256f_bytes_suf_cma_final
    (optRand : PublicKeyCore Sha2Set.s256f.prims.core → ProbComp Sha2Set.s256f.prims.Y)
    (pkSeedDist : ProbComp Sha2Set.s256f.prims.PkSeed)
    (F : BytesStrongForger Sha2Set.s256f.vp Sha2Set.s256f.prims (codec Sha2Set.s256f) optRand pkSeedDist) :
    SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp F ≤
      betaSufFinalMemo (bytesToTypedS F).toUnforgeableAdversary
```
(`betaSufFinalMemo` = `boundFinalTight` at the twelve explicit adversaries; written out in `_final_explicit` and in §3.) The 128s form is the same
with `s128s`; games, adversaries, bound are those of `security/status/FINAL3.md` §1–§6 at `S.vp`, `S.prims`.

**Which function each game is about** (proved in `MReduction/Audit.lean`: `thash_class`, `thash_class_sha512`, `fHash_eval`, `prf_spec`,
`prfMsg_spec`, `hmsg_spec`; arities 1, 2, `len`, `k` pairwise distinct at every set, `arities_pairwise`; `(len,k)` = (35,14), (35,33), (51,17),
(51,33), (67,22), (67,35)):

| term | 128s, 128f (n = 16) | 192s, 192f, 256s, 256f (n = 24, 32) |
|---|---|---|
| PRF on `SkAdrs` (`skPrfC`) | Trunc_n SHA-256(PK.seed‖0^(64−n)‖ADRSc‖SK.seed) | same (SHA-256) |
| PRF_msg (`msgPrf`) | HMAC-SHA-256 | HMAC-SHA-512 |
| ITSR on H_msg | MGF1-SHA-256 ∘ SHA-256 | MGF1-SHA-512 ∘ SHA-512 |
| SM-DSPR + 3·SM-TCR at FORS leaves (F) | SHA-256 | SHA-256 |
| SM-TCR class 1 (F) | SHA-256 | SHA-256 |
| SM-TCR classes 2 (H), `len` (T_len), `k` (T_k) | SHA-256, pad 64−n | SHA-512, pad 128−n |
| 14·SM-UD, SM-PRE, chain SM-TCR (F) | SHA-256 | SHA-256 |

Caveats found by the audit: (1) the collection oracle of every SM game is the whole `Thash`, so at n = 24/32 an "F" (SHA-256) game also gives
collection access to the SHA-512 functions and vice versa; the loose cap `tcrTargets` and the phase-1 structure walk mix both. (2) VCVio's `sha2Thash`
uses the F formula for singleton lists at every n (not FIPS `T_1`); never reached, since `T` is only used at arities `len`, `k`. (3) the unrestricted
PRF game `skPrf` (not used by any final theorem) is broken at every set (`skPrf_broken S`), as at 128s. No generic `Reduction` theorem bakes in a 128s
numeral or instance; `w − 2 = 14` everywhere. Non-vacuity lemmas are generic; instances `games_can_be_lost S`, `class_game_winnable S`, `caps_pos S`.

Key numerals (all Lean-proved; log2 approximations in `status/D.md` computed outside Lean):

| | 128s | 128f | 192s | 192f | 256s | 256f |
|---|---|---|---|---|---|---|
| n / pk / sk / sig bytes | 16/32/64/7856 | 16/32/64/17088 | 24/48/96/16224 | 24/48/96/35664 | 32/64/128/29792 | 32/64/128/49856 |
| `len`, `k` | 35, 14 | 35, 33 | 51, 17 | 51, 33 | 67, 22 | 67, 35 |
| cap FORS DSPR/TCR ≈ | 2^78.81 | 2^77.04 | 2^81.09 | 2^79.04 | 2^82.46 | 2^82.13 |
| cap class 1 / 2 ≈ | 2^78.82 / 2^78.81 | 2^77.41 / 2^77.02 | 2^81.09 / 2^81.09 | 2^79.19 / 2^79.04 | 2^82.46 / 2^82.46 | 2^82.21 / 2^82.13 |
| hashes keygen / sign / verify | 269824 / 2007385 / 3928 | 4216 / 108847 / 11870 | 392704 / 3311666 / 5681 | 6136 / 169105 / 17216 | 257792 / 2791676 / 8443 | 16112 / 327266 / 17521 |
| `bTcrArM` phase 2 ≤ kg + qs·sign + | 7857 | 23741 | 11363 | 34433 | 16887 | 35043 |

## 3. E2E (`ME2E.sha2_<set>.*`; ten per set: `rust_security`, `rust_pure_security`, `…_linear` ×2,
`…_deterministic`/`_hedged` ×4, `…_resources` ×2; plus `bytes_end_to_end`, `pure_bytes_end_to_end`)

Verbatim, `ME2E.sha2_192f.rust_security` (other sets: array sizes n, 2n, 4n; arities `len`, `k`; `Room` 152 / 409 at 128s, 128f and 304 / 561 at
the other sets, as in `multi/lean/Slhdsa/Theorems.lean`; 128s is the old `E2E.rust_security` modulo Rust names — textual check in the generator).
For 128s the file is `ME2E/Sha2_128s.lean`, `rust_security` at line 258, `rust_pure_security` at line 336; its part (a) reads
`… Room m.length 152 → ∃ sig, slhdsa.sets.sha2_128s.slh_sign_internal m sk addrnd = ok sig ∧ wire sig.val = byteSign Sha2Set.s128s.vp
Sha2Set.s128s.prims (codec Sha2Set.s128s) (wire m.val) (wire sk.val) (node Sha2Set.s128s addrnd)) ∧ …`:

```lean
theorem rust_security (optRand : PublicKeyCore Sha2Set.s192f.prims.core → ProbComp Sha2Set.s192f.prims.Y)
    (pkSeedDist : ProbComp Sha2Set.s192f.prims.PkSeed) :
    ((∀ sk_seed sk_prf pk_seed : Array U8 24#usize,
        ∃ sk pk, slhdsa.sets.sha2_192f.slh_keygen_internal sk_seed sk_prf pk_seed = ok (sk, pk) ∧
          (wire pk.val, wire sk.val) = byteKeygen Sha2Set.s192f.vp Sha2Set.s192f.prims (codec Sha2Set.s192f)
            (node Sha2Set.s192f sk_seed) (node Sha2Set.s192f sk_prf) (node Sha2Set.s192f pk_seed)) ∧
      (∀ (m : Slice U8) (sk : Array U8 96#usize) (addrnd : Array U8 24#usize), Room m.length 304 →
        ∃ sig, slhdsa.sets.sha2_192f.slh_sign_internal m sk addrnd = ok sig ∧
          wire sig.val = byteSign Sha2Set.s192f.vp Sha2Set.s192f.prims (codec Sha2Set.s192f) (wire m.val) (wire sk.val) (node Sha2Set.s192f addrnd)) ∧
      (∀ (m sig : Slice U8) (pk : Array U8 48#usize), Room m.length 304 →
        slhdsa.sets.sha2_192f.slh_verify_internal m sig pk =
          ok (byteVerify Sha2Set.s192f.vp Sha2Set.s192f.prims (codec Sha2Set.s192f) (wire m.val) (wire sig.val) (wire pk.val)))) ∧
    (∀ F : SignatureAlg.StrongUnforgeableAdversary (bytesAlg Sha2Set.s192f.vp Sha2Set.s192f.prims (codec Sha2Set.s192f) optRand pkSeedDist),
      SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp F ≤
        (Reduction.skPrfC Sha2Set.s192f.vp Sha2Set.s192f.prims).prfAdvantage (bPrfWC sufCheck T) +
        (Reduction.msgPrf Sha2Set.s192f.vp Sha2Set.s192f.prims).prfAdvantage (bPrfMsgWL sufCheck T) +
        KeyedHash.ITSRAdvantage (bItsrL T) +
        (SM_DT_DSPR_SourceFinalValidity.advantage (toDspr (bOpenPreS T)) + 3 * SM_DT_TCR_SourceFinalValidity.advantage (toTcr (bOpenPreS T))) +
        (SM_DT_TCR_Advantage (bTcrArM 1 T) + SM_DT_TCR_Advantage (bTcrArM 2 T) +
          SM_DT_TCR_Advantage (bTcrArM 51 T) + SM_DT_TCR_Advantage (bTcrArM 33 T)) +
        ((Sha2Set.s192f.vp.params.w - 2 : ℕ) : ℝ≥0∞) * SM_DT_UD_Advantage (rUd pkSeedDist (bWotsS T)) +
        SM_DT_PRE_Advantage (rPre pkSeedDist (bWotsS T)) +
        SM_DT_TCR_Advantage (rTcrT (vp := Sha2Set.s192f.vp) pkSeedDist (bWotsS T))) ∧
    ∀ A : SignatureAlg.UnforgeableAdversary (bytesAlg …), SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤ …
      -- the same twelve terms with bPrfC, bPrfMsgL and (bytesToTyped A)
```
where `T` abbreviates `(bytesToTypedS F).toUnforgeableAdversary` in this summary only (written out in the file). Resources, verbatim for 256f:
`rust_security_resources … (A) (qs) (hA) : (∀ pk, IsQueryBoundP ((bytesToTyped A).main pk) (fun i => i.isRight = true) qs) ∧
Reduction.FinalResourcesFinal (bytesToTyped A) qs (MReduction.directCounts256f qs) (16112 + qs * 327266 + 35043)`.

**Exact remaining gap, every set** (docstring items (i)–(vi) of each `rust_security`): (i) sampling: the scheme draws `PK.seed ← pkSeedDist`,
`SK.seed`, `SK.prf` uniform, `opt_rand ← optRand pk`; the Rust functions take seeds and `addrnd` as arguments, no sampling code is covered. (ii) `Room
m.length 304` (internal sign/verify), `561` (pure) at n = 24, 32, and `152` / `409` at n = 16: `m.length + slack ≤ usize::MAX` and `< 2^61`; keygen
unconditional; the scheme is total. (iii)
Rust keys are arrays of 2n / 4n bytes (seeds n), the signature a `Vec<u8>` of `sigBytes` (`rust_sign_internal_length`; no length theorem for the
`slh_sign` result); the scheme takes any byte strings (wrong-length keys: reject / `[]` / `none`, never accepted); no secret-key well-formedness
check. (iv) `U8` ↔ `UInt8` by `wire` (length-preserving bijection), arrays ↔ `Bytes n` by `node`; `byteKeygen` returns `(pk, sk)`, Rust `(sk, pk)`;
every Rust result is `ok`. (v) the scheme's `sign` takes the public key only to evaluate `optRand`. (vi) the twelve advantages are assumptions about
the functions in the table of §2, not bounded here; no running time; single key; pure mode only (no pre-hash); Rust compiler, Aeneas, `sets.rs`
instantiation, side channels.

## 4. Random-oracle statement (`MLink/Security.lean`, generic in `S`)

`security_sha2 S e optRand pkSeedDist adv (hadv : adv.RomQueryBound qh qs) : strongUnforgeableAdvantage (ProbCompRuntime.rom (hashSpec S.prims.core))
adv ≤ securityBound S.vp.params (256 ^ S.vp.params.n) 2 1 qh qs`, `security_sha2_euf`, `romScheme_verify_eq`, `hprf_dom`, `not_hprf`, and the
conformance `romScheme_map_romAnswer_sha2 S : (romScheme … (Equiv.refl _) optRand pkSeedDist).map (simulateQ' (unifFwdAnswerImpl (romAnswer S.prims)))
= internalAlg S.vp S.prims optRand pkSeedDist`.

## 3a. The interface `api`, the checked signers, typed forms (`ME2E/Api.lean` generic; `ME2E/Api/Sha2_<set>.lean`, generated)

Counterpart of `security/E2E/Api.lean` (and of the typed `PureEndToEnd` of `security/E2E/External.lean`, `rust_keygen` / `rust_sign` /
`rust_verify` of `E2E/Main.lean`). Generator `scripts/gen_api_rom.py`: every statement is the single-set statement under textual renamings
(Rust names `slhdsa.api.f` → `slhdsa.sets.sha2_<set>.f`, `slhdsa.slh.slh_f` → `slhdsa.sets.sha2_<set>.slh_f`; sizes 16/32/48/64 → n/2n/3n/4n;
`Room`; `vp`, `prims`, codec, `node`, `secretKey`, `Link.decode*`, `*Bytes`, `Spec.KeyOk` at the set; `len`, `k`; forger `S` → `F`); the
generator asserts that undoing the renamings on the 128s output gives back the single-set text exactly (`check128s`), and `check.sh` step 0
re-runs both generators on a copy and diffs. Per set (namespace `ME2E.sha2_<set>`): `api_sign_eq`, `api_verify_eq` (unconditional, by unfolding:
the per-set `sign`/`verify` and `slh_sign`/`slh_verify` both call `slh::slh_sign`/`slh_verify`), `api_keygen_eq`, `api_sign_deterministic_eq`,
`api_keygen_bytes`, `api_sign_bytes`, `api_sign_deterministic_bytes`, `api_verify_bytes`, `api_pure_cores`, `ApiPureBytesEndToEnd` +
`api_pure_bytes_end_to_end`, `rust_keygen`, `rust_sign`, `rust_verify`, `PureEndToEnd` + `pure_end_to_end`, `ApiPureEndToEnd` +
`api_pure_end_to_end`, `api_pure_security`, `api_pure_security_linear`, `api_sign_checked_eq_sign`, `api_sign_deterministic_checked_eq`,
`api_keygen_checked_eq`, `keygen_internal_checked_eq`, `api_sign_checked_bytes`, `api_sign_deterministic_checked_bytes`, `api_checked_pure_cores`.
Generic (`ME2E/Api.lean`): `seeds_split`, `sk_split` (every `3n`/`4n`-byte array has exactly one block split: the block hypotheses restrict
nothing), `spec_slhSignChecked_eq p hv` (valid `p`, `Spec.KeyOk p sk` → checked Alg. 22 = Alg. 22), `secretKey S`, `skBytes_secretKey`.

Verbatim, SLH-DSA-SHA2-128s (`ME2E/Api/Sha2_128s.lean`; `api_pure_security` at line 396, `api_sign_checked_eq_sign` at line 528):

```lean
theorem api_pure_security (optRand : PublicKeyCore Sha2Set.s128s.prims.core → ProbComp Sha2Set.s128s.prims.Y)
    (pkSeedDist : ProbComp Sha2Set.s128s.prims.PkSeed) :
    ((∀ (seeds : Array U8 48#usize) (sk0 : Array U8 64#usize) (pk0 : Array U8 32#usize)
          (sk_seed sk_prf pk_seed : Array U8 16#usize),
        seeds.val = sk_seed.val ++ sk_prf.val ++ pk_seed.val →
        ∃ sk pk, slhdsa.sets.sha2_128s.keygen seeds sk0 pk0 = ok (sk, pk) ∧
          (wire pk.val, wire sk.val) =
            byteKeygen Sha2Set.s128s.vp Sha2Set.s128s.prims (codec Sha2Set.s128s) (node Sha2Set.s128s sk_seed) (node Sha2Set.s128s sk_prf) (node Sha2Set.s128s pk_seed)) ∧
      (∀ (m ctx : Slice U8) (sk : Array U8 64#usize) (addrnd : Array U8 16#usize),
        Room m.length 409 →
        ∃ r, slhdsa.sets.sha2_128s.sign m ctx sk addrnd = ok r ∧
          r.map (fun v => wire v.val) =
            byteSignPure Sha2Set.s128s.vp Sha2Set.s128s.prims (codec Sha2Set.s128s) (wire m.val) (wire ctx.val) (wire sk.val)
              (node Sha2Set.s128s addrnd)) ∧
      (∀ (m ctx : Slice U8) (sk : Array U8 64#usize)
          (sk_seed sk_prf pk_seed pk_root : Array U8 16#usize),
        sk.val = sk_seed.val ++ sk_prf.val ++ pk_seed.val ++ pk_root.val → Room m.length 409 →
        ∃ r, slhdsa.sets.sha2_128s.sign_deterministic m ctx sk = ok r ∧
          r.map (fun v => wire v.val) =
            byteSignPure Sha2Set.s128s.vp Sha2Set.s128s.prims (codec Sha2Set.s128s) (wire m.val) (wire ctx.val) (wire sk.val)
              (node Sha2Set.s128s pk_seed)) ∧
      (∀ (m sig ctx : Slice U8) (pk : Array U8 32#usize), Room m.length 409 →
        slhdsa.sets.sha2_128s.verify m sig ctx pk =
          ok (byteVerifyPure Sha2Set.s128s.vp Sha2Set.s128s.prims (codec Sha2Set.s128s) (wire m.val) (wire sig.val) (wire ctx.val)
            (wire pk.val)))) ∧
    (∀ F : SignatureAlg.StrongUnforgeableAdversary (pureBytesAlg Sha2Set.s128s.vp Sha2Set.s128s.prims (codec Sha2Set.s128s) optRand pkSeedDist),
      SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp F ≤ …twelve terms of rust_pure_security…) ∧
    ∀ A : SignatureAlg.UnforgeableAdversary (pureBytesAlg …), SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤ …
  -- (the bound parts are written out in the file; they are textually those of `rust_pure_security`, proof `(rust_pure_security …).2`)

theorem api_sign_checked_eq_sign (m ctx : Slice U8) (sk : Array U8 64#usize)
    (addrnd : Array U8 16#usize) (hm : Room m.length 409) (hk : Spec.KeyOk Spec.sha2_128s (bytes sk.val)) :
    slhdsa.sets.sha2_128s.sign_checked m ctx sk addrnd = slhdsa.sets.sha2_128s.sign m ctx sk addrnd ∧
      (ctx.length ≤ 255 → ∃ sig, slhdsa.sets.sha2_128s.sign m ctx sk addrnd = ok (some sig)) ∧
      (255 < ctx.length → slhdsa.sets.sha2_128s.sign m ctx sk addrnd = ok none)
```

`api_keygen_checked_eq`: for a key written by `keygen` (`keygen seeds sk0 pk0 = ok (sk, pk)`), for all `m ctx addrnd` with `Room m.length 409`,
both checked signers equal the plain ones (same `Result`) — the checked signer is the same signing oracle on honest keys. At n = 24, 32 the
same statements with 72/96/48/24-byte resp. 96/128/64/32-byte arrays and `Room m.length 561`.

## 4a. Random-oracle theorem for the context-string interface (`ME2E/PureRom.lean` generic; `ME2E/Rom/Sha2_<set>.lean`, generated)

Generalises `security/E2E/{PureRom,PureRomBytes}.lean` (GuardedRom, CodedRom are compiled in place). What is 128s-specific there: `Link.vp`,
`Link.prims`, `codec128s`, `Link.security_128s`, `Link.romScheme_map_romAnswer_128s` and the numeral `256 ^ 16`; everything else is generic in
VCVio's `ValidatedParams`/`Primitives`. VCVio's ROM theorem (`strongUnforgeableAdvantage_sha2_le`, used through `MLink.security_sha2`) needs only
`ApprovedAddressBounds`, which VCVio provides for every `FipsParameterSet` (`fipsApprovedAddressBounds`): **the ROM bound is available for all six
SHA-2 sets**, no exception. Generic in `S`: `pureRomScheme S`, `pureRomScheme_instantiation` (SHA-2-answered = `Reduction.externalAlg S.vp
S.prims`), `toInternalRom`, `pure_rom_advantage_le`, `toInternalRom_romQueryBound`, `pure_security_sha2`, `pure_security_sha2_euf`;
`pureBytesRomScheme S`, `pureBytesRomScheme_instantiation` (= `Reduction.pureBytesAlg S.vp S.prims (codec S)`), `pureBytesRomView`, `bytesToRom`,
`pure_bytes_rom_advantage_le`, `pure_bytes_security_sha2`, `pure_bytes_security_sha2_euf`. Per set: `pure_rom_security`, `api_pure_rom_security`,
`rust_pure_rom_security_bytes`, `api_pure_rom_security_bytes`. Verbatim, 128s (`ME2E/Rom/Sha2_128s.lean`, lines 41 and 81):

```lean
theorem pure_rom_security (optRand : PublicKeyCore Sha2Set.s128s.prims.core → ProbComp Sha2Set.s128s.prims.Y)
    (pkSeedDist : ProbComp Sha2Set.s128s.prims.PkSeed) :
    PureEndToEnd optRand pkSeedDist ∧
    (pureRomScheme Sha2Set.s128s optRand pkSeedDist).map (simulateQ' (unifFwdAnswerImpl (romAnswer Sha2Set.s128s.prims))) =
      externalAlg Sha2Set.s128s.vp Sha2Set.s128s.prims optRand pkSeedDist ∧
    (∀ (F : StrongUnforgeableAdversary (pureRomScheme Sha2Set.s128s optRand pkSeedDist)) (qh qs : ℕ),
      F.RomQueryBound qh qs →
      strongUnforgeableAdvantage (ProbCompRuntime.rom (hashSpec Sha2Set.s128s.prims.core)) F ≤
        securityBound Sha2Set.s128s.vp.params (256 ^ 16) 2 1 qh qs) ∧
    ∀ (A : UnforgeableAdversary (pureRomScheme Sha2Set.s128s optRand pkSeedDist)) (qh qs : ℕ),
      A.RomQueryBound qh qs →
      unforgeableAdvantage (ProbCompRuntime.rom (hashSpec Sha2Set.s128s.prims.core)) A ≤
        securityBound Sha2Set.s128s.vp.params (256 ^ 16) 2 1 qh qs

theorem rust_pure_rom_security_bytes (optRand : PublicKeyCore Sha2Set.s128s.prims.core → ProbComp Sha2Set.s128s.prims.Y)
    (pkSeedDist : ProbComp Sha2Set.s128s.prims.PkSeed) :
    ((∀ sk_seed sk_prf pk_seed : Array U8 16#usize,
        ∃ sk pk, slhdsa.sets.sha2_128s.slh_keygen_internal sk_seed sk_prf pk_seed = ok (sk, pk) ∧
          (wire pk.val, wire sk.val) =
            byteKeygen Sha2Set.s128s.vp Sha2Set.s128s.prims (codec Sha2Set.s128s) (node Sha2Set.s128s sk_seed) (node Sha2Set.s128s sk_prf) (node Sha2Set.s128s pk_seed)) ∧
      (∀ (m ctx : Slice U8) (sk : Array U8 64#usize) (addrnd : Array U8 16#usize),
        Room m.length 409 →
        ∃ r, slhdsa.sets.sha2_128s.slh_sign m ctx sk addrnd = ok r ∧
          r.map (fun v => wire v.val) =
            byteSignPure Sha2Set.s128s.vp Sha2Set.s128s.prims (codec Sha2Set.s128s) (wire m.val) (wire ctx.val) (wire sk.val)
              (node Sha2Set.s128s addrnd)) ∧
      (∀ (m sig ctx : Slice U8) (pk : Array U8 32#usize), Room m.length 409 →
        slhdsa.sets.sha2_128s.slh_verify m sig ctx pk =
          ok (byteVerifyPure Sha2Set.s128s.vp Sha2Set.s128s.prims (codec Sha2Set.s128s) (wire m.val) (wire sig.val) (wire ctx.val)
            (wire pk.val)))) ∧
    (pureBytesRomScheme Sha2Set.s128s optRand pkSeedDist).map
        (simulateQ' (unifFwdAnswerImpl (romAnswer Sha2Set.s128s.prims))) =
      pureBytesAlg Sha2Set.s128s.vp Sha2Set.s128s.prims (codec Sha2Set.s128s) optRand pkSeedDist ∧
    (∀ (F : StrongUnforgeableAdversary (pureBytesRomScheme Sha2Set.s128s optRand pkSeedDist)) (qh qs : ℕ),
      F.RomQueryBound qh qs →
      strongUnforgeableAdvantage (ProbCompRuntime.rom (hashSpec Sha2Set.s128s.prims.core)) F ≤
        securityBound Sha2Set.s128s.vp.params (256 ^ 16) 2 1 qh qs) ∧
    ∀ (A : UnforgeableAdversary (pureBytesRomScheme Sha2Set.s128s optRand pkSeedDist)) (qh qs : ℕ),
      A.RomQueryBound qh qs →
      unforgeableAdvantage (ProbCompRuntime.rom (hashSpec Sha2Set.s128s.prims.core)) A ≤
        securityBound Sha2Set.s128s.vp.params (256 ^ 16) 2 1 qh qs
```

`api_pure_rom_security` / `api_pure_rom_security_bytes`: the same with `ApiPureEndToEnd` / `ApiPureBytesEndToEnd` as the first conjunct. Other
sets: `256 ^ 24`, `256 ^ 32` at n = 24, 32, `Room m.length 561`. Same caveat as the single-set tree: nothing transfers the random-oracle bound to
the SHA-2 instantiation (that is the random-oracle methodology); the instantiation conjunct is an identity of programs.

## Per-set status

| | 128s | 128f | 192s | 192f | 256s | 256f |
|---|---|---|---|---|---|---|
| Link keygen/sign/verify (internal + pure, bytes), SHA-2 primitives | done | done | done | done | done | done |
| Reduction headlines, linear, det/hedged, resources with numerals | done | done | done | done | done | done |
| E2E (10 theorems), against the current `multi/rust` (portable build) | done | done | done | done | done | done |
| internal ROM bound + conformance (`MLink.security_sha2`) | done | done | done | done | done | done |
| `api` functions = cores; `api_pure_security(_linear)`; checked = plain on `KeyOk` keys; typed `PureEndToEnd` | done | done | done | done | done | done |
| pure-interface ROM theorem: typed, bytes, Rust and `api` forms | done | done | done | done | done | done |

## Not done / limitations

- Everything listed in `security/status/FINAL3.md` §7 carries over (advantages not bounded, no running time, single key, argued-only resource rows, …).
- Not ported: `security/Reduction/Gen/*` and `E2E/HeadlineGen`; `security/Ideal`; the old typed-value and ROM forms of `E2E/Main.lean` (`end_to_end`, `EndToEnd`) and superseded intermediate E2E forms; `stepPRFC_128s`, `skPrf_broken_128s_half`; per-set copies of single-adversary numeral lemmas (their content is in the fields of `final_resources_final_<set>`); a `romScheme_verify_eq_spec` wrapper (follows from `romScheme_verify_eq` + `verify_eq_typed`, not stated).
- Not ported from `security/E2E/Api.lean`: `api_pure_standard_model_security_split` (needs `E2E/FinalSplit`'s loose-cap typed headline, not ported) and `api_pure_securityG` (needs `Reduction/Gen`, not ported); `Ideal.api_ideal_security_closed_pure` (out of scope). Not ported from `PureRom.lean`/`PureRomBytes.lean`: nothing (all ten / ten declarations have counterparts; names `pure_security_128s(_euf)`, `pure_bytes_security_128s(_euf)` become the generic `pure_security_sha2 S`, `pure_bytes_security_sha2 S`).
- Differences from the single-set statements, all forced: Rust names (`sets.sha2_<set>.keygen` etc. instead of `api.keygen`, `slh.slh_*`); `Spec.KeyOk Spec.sha2_<set>` (the spec takes the parameter set); `secretKey Sha2Set.s128s sk`, `MLink.decodePk Sha2Set.s128s`, `MLink.skBytes Sha2Set.s128s` etc. for the single-set `secretKey sk`, `Link.decodePk`, `skBytes`; the forger variable is `F` (`S` is the set). `api_sign_eq`, `api_verify_eq` are proved by unfolding rather than `rfl`, same statements.
- The `api`/checked/ROM statements are about the default (portable) translation `multi/lean/Slhdsa/Funs.lean`; the `hw-sha2` build (`multi/lean-hw`) has no refinement proofs and is not covered (out of scope here).
- Per-set files of `MReduction` and `ME2E` are script-generated (`MReduction/gen`, `ME2E/gen`, `scripts/gen_api_rom.py`, outside the build): statements are explicit per set, proofs are one-line instances of the generic theorems.
- The "128s statement = old statement" check for `ME2E` is textual (generator assertion), for `MReduction` it is `rfl` (`Check128s.lean`). Package reports: `status/B.md`–`E.md`, `status/BRIEF.md`.

## Build and checks

`cd multi/security && export PATH=$HOME/.elan/bin:$PATH && lake build MLink MReduction ME2E` (dependencies VCVio/Mathlib/Aeneas prebuilt in `.tools`).
From scratch (`check.sh clean`, shared machine, 2026-11-22): "Build completed successfully (7792 jobs)", build step 106 s wall, whole script
1:50 wall, 495 s user CPU (includes `Reduction`, `Spec`, `Slhdsa`, `E2ERom`). `scripts/check.sh` = (0) both generators re-run on a copy of the
tree, output diffed against the checked-in files (this also runs their 128s textual checks) + (1) build + (2) grep for
`sorry`/`axiom`/`native_decide`/`bv_decide` outside comments (also in the two in-place `E2E/*Rom.lean`) + (3) shim diff + (4) `#print axioms` of
252 headline theorems (output kept in `status/axioms.txt`) + (5) per-set list; exits non-zero on failure. Last run ends:

```
== 4. #print axioms (our modules) ==
252 / 252 headline theorems reported
all within [propext, Classical.choice, Quot.sound]
...
CHECK PASSED
```
Sample:

```
'MLink.sha512_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'MReduction.slhdsa_sha2_256f_bytes_suf_cma_final' depends on axioms: [propext, Classical.choice, Quot.sound]
'ME2E.sha2_192f.rust_security' depends on axioms: [propext, Classical.choice, Quot.sound]
'ME2E.sha2_256f.rust_security_resources' depends on axioms: [propext, Classical.choice, Quot.sound]
```
(all 252 lines are this triple).
