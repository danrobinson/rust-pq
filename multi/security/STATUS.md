# multi/security — security of SLH-DSA-SHA2, all six parameter sets: status

Lean 4.36.0, Lake project `multi/security/`. Extends `security/` (SHA2-128s only) to SLH-DSA-SHA2-{128s,128f,192s,192f,256s,256f}. **State: closed.**
Everything below is proved for all six sets; no `sorry`, `axiom`, `native_decide`, `bv_decide`; nothing conditional. Nothing outside `multi/security/`
was modified (no file added to `security/`). No defect found in `multi/lean` or `multi/rust`. Re-run: `scripts/check.sh` (`scripts/check.sh clean` for
a from-scratch build).

## Layout

| library | source | content |
|---|---|---|
| `Spec`, `Slhdsa` | `multi/lean`, compiled in place (`srcDir`) | parameterised FIPS 205 spec; Rust extraction + refinement |
| `Reduction` | `security/Reduction/*.lean`, compiled in place, **unmodified** | generic standard-model reduction (65 modules; not `Gen/`) |
| `LinkSecurity` | `security/Link/Security.lean`, in place, unmodified | VCVio-only ROM file that `Reduction` imports |
| `Shim` | `shim/Link/{Basic,Hash,Verify}.lean`, `shim/Reduction/PrfDomainNonVacuity.lean` | see below |
| `MLink` (15 modules) | `MLink/` | Spec = VCVio scheme, one proof generic in `S : MLink.Sha2Set`; ROM statement |
| `MReduction` (8) | `MReduction/` | Reduction headlines, linear forms, corollaries, resources, audit at the six sets |
| `ME2E` (7) | `ME2E/` | Rust `sets.sha2_<set>.slh_*` = scheme cores; ten headline theorems per set |

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

Verbatim, `ME2E.sha2_192f.rust_security` (other sets: array sizes n, 2n, 4n; arities `len`, `k`; 128s is the old `E2E.rust_security` modulo Rust names
and `Room` slack — textual check in the generator):

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
m.length 304` (internal sign/verify), `561` (pure): `m.length + slack ≤ usize::MAX` and `< 2^61`; keygen unconditional; the scheme is total. (iii)
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

## Per-set status

| | 128s | 128f | 192s | 192f | 256s | 256f |
|---|---|---|---|---|---|---|
| Link keygen/sign/verify (internal + pure, bytes), SHA-2 primitives | done | done | done | done | done | done |
| Reduction headlines, linear, det/hedged, resources with numerals | done | done | done | done | done | done |
| E2E (10 theorems); ROM bound + conformance | done | done | done | done | done | done |

## Not done / limitations

- Everything listed in `security/status/FINAL3.md` §7 carries over (advantages not bounded, no running time, single key, argued-only resource rows, …).
- Not ported: `security/Reduction/Gen/*` and `E2E/HeadlineGen`; `security/Ideal`; the old typed-value and ROM forms of `E2E/Main.lean` (`end_to_end`, `EndToEnd`) and superseded intermediate E2E forms; `stepPRFC_128s`, `skPrf_broken_128s_half`; per-set copies of single-adversary numeral lemmas (their content is in the fields of `final_resources_final_<set>`); a `romScheme_verify_eq_spec` wrapper (follows from `romScheme_verify_eq` + `verify_eq_typed`, not stated).
- Per-set files of `MReduction` and `ME2E` are script-generated (`MReduction/gen`, `ME2E/gen`, outside the build): statements are explicit per set, proofs are one-line instances of the generic theorems.
- The "128s statement = old statement" check for `ME2E` is textual (generator assertion), for `MReduction` it is `rfl` (`Check128s.lean`). Package reports: `status/B.md`–`E.md`, `status/BRIEF.md`.

## Build and checks

`cd multi/security && export PATH=$HOME/.elan/bin:$PATH && lake build MLink MReduction ME2E` (dependencies VCVio/Mathlib/Aeneas prebuilt in `.tools`).
From scratch (`check.sh clean`, 36 cores, shared machine): "Build completed successfully (7732 jobs)", 81 s wall, 359 s user CPU (includes
`Reduction`, `Spec`, `Slhdsa`). `scripts/check.sh` = build + grep for `sorry`/`axiom`/`native_decide`/`bv_decide` outside comments + shim diff +
`#print axioms` of 129 headline theorems (output kept in `status/axioms.txt`) + per-set list; exits non-zero on failure. Sample:

```
'MLink.sha512_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'MReduction.slhdsa_sha2_256f_bytes_suf_cma_final' depends on axioms: [propext, Classical.choice, Quot.sound]
'ME2E.sha2_192f.rust_security' depends on axioms: [propext, Classical.choice, Quot.sound]
'ME2E.sha2_256f.rust_security_resources' depends on axioms: [propext, Classical.choice, Quot.sound]
```
(all 129 lines are this triple).
