# security — security of SLH-DSA-SHA2, all six parameter sets: status

Lean 4.36.0, Lake project `security/`. Security results for SLH-DSA-SHA2-{128s,128f,192s,192f,256s,256f}, attached to the Rust crate `../rust`
(portable build here; the `hw-sha2` build in `../security-hw`, which compiles these files against `../lean-hw`). **State: closed** (2026-11-22).
The 2026-11-22 report below describes what was proved for all six sets except the ideal-compression bound (§5, SLH-DSA-SHA2-128s only); no `sorry`, `axiom`,
`native_decide`, `bv_decide`; nothing conditional. Re-run: `scripts/check.sh` (`scripts/check.sh clean` for a from-scratch build).

**2026-11-23 update.** The [128f pure-byte theorems](MIdeal/Sha2_128f.lean) now give classical SUF-CMA and EUF-CMA bounds with both compression ports. Section 5 records the separate 128s Rust/API corollaries. [Quantum and shared-table results](../quantum/STATUS.md) track the six SHA-2 sets.

**History.** Until 2026-11-22 this directory held the single-set development (SLH-DSA-SHA2-128s: its own `Link`, `E2E`, `Reduction`, `Ideal`
over the single-set `Spec` of the single-set `lean/`), and the six-set libraries `MLink`, `MReduction`, `ME2E`, `MIdeal` lived in a
separate Lake project, `security` in the subdirectory `multi` of the six-set tree, which compiled `Reduction`, `Ideal` and three files of `E2E`/`Link` from here in place, with Spec-free
stand-ins for four `Link` modules. On 2026-11-22 the six-set tree replaced the single-set one: the stand-ins took the place of the
originals, the single-set files that need the single-set `Spec`/`Slhdsa` were deleted (list below), and the two projects became this one.
The single-set tree is git commit `26aa3d8`. No Lean file of `Reduction/` or `Ideal/` was modified except `Reduction/PrfDomainNonVacuity.lean`
(below); `Ideal.lean` lost its imports of the deleted `Ideal/Rust*.lean`. Statements and proofs of `MLink`, `MReduction`, `ME2E`, `MIdeal` are
unchanged (generated headers name the generators' new paths).

**2026-11-22, the closed ideal-compression bound for SLH-DSA-SHA2-128s (§5, `MIdeal`).** `MIdeal.sha2_128s.{rust_ideal_security_closed_tight8,
rust_ideal_security_closed_pure_tight8, api_ideal_security_closed_pure_tight8}` are the three single-set `Ideal/RustFinalClosedTight8.lean`
corollaries with their Rust-level conjuncts about `slhdsa.sets.sha2_128s.*` of `../lean`. **128s only.**

**2026-11-22 update (after the rewrite of the Rust crate / re-proof of `../lean`).** Before: `MLink`, `MReduction` and `ME2E.Basic` still built
against the new `../lean`; `ME2E.Sha2_128s` and `ME2E.Sha2_128f` did not (6 errors each): they called `slhdsa.sha2_128{s,f}.*_correct` with
`Room m.length 304 / 561`, whereas `../lean` now states the n = 16 sets with `Room m.length 152 / 409` (the single-set tree's constants). The
other four sets built unchanged (same names `slhdsa.sha2_<set>.*_correct`, `slhdsa.sets.sha2_<set>.slh_*`). Repair: the generator
(`ME2E/gen/gen.py`) takes the slack per set (152/409 for n = 16, 304/561 otherwise), so the 128s/128f headlines are now *stronger* than before
(weaker hypothesis) and their 128s statements are character-for-character the single-set `E2E.*` ones up to the renamings (textual check in the
generator; it no longer needs "modulo `Room`"). New: §3a (the `api` functions, typed end-to-end forms) and §4a (the
random-oracle theorem for the context-string interface, typed and byte level, Rust and `api` forms), for all six sets.

## Layout

Every library is a default target: `lake build` builds all of them (8205 jobs with the dependencies; about 4 minutes from scratch).

| library | source | content |
|---|---|---|
| `Spec`, `Slhdsa` | `../lean`, compiled in place (`srcDir`) | parameterised FIPS 205 spec; Rust extraction + refinement |
| `Link` (5 + root) | `Link/{Basic,Hash,Verify,Sha256,Security}.lean` | SLH-DSA-SHA2-128s parameters and decoders at VCVio's level (`Link.vp`, `Link.prims`, `Link.S128`, `Node`, `Dom`, `decodeSig`, `decodePk`), word packing (`be32`, `app4`), VCVio's random-oracle bound at 128s (`Link.security_128s`); no `Spec` |
| `Reduction` (107 + root) | `Reduction/**` | generic standard-model reduction, with its SHA2-128s instances, `Reduction/Open` (open-program forms, which `Ideal` realises) and `Reduction/Gen` (forgers over a general sampling spec) |
| `E2E` (2 + root) | `E2E/{GuardedRom,CodedRom}.lean` | scheme behind a partial message encoding / seen through encodings, over any oracle interface (no parameter set in them) |
| `Ideal` (154 + root) | `Ideal/**` | the ideal-compression analysis of SHA2-128s (games, realisers, `suf/euf_ideal_closed_tight8`, `…_pure_…`); `IDEAL_STATUS.md` |
| `MLink` (15) | `MLink/` | Spec = VCVio scheme, one proof generic in `S : MLink.Sha2Set`; ROM statement |
| `MReduction` (8) | `MReduction/` | Reduction headlines, linear forms, corollaries, resources, audit at the six sets |
| `ME2E` (21) | `ME2E/` | Rust `sets.sha2_<set>.slh_*` = scheme cores; ten headline theorems per set (`Sha2_<set>`); `api` + typed forms (`Api`, `Api/Sha2_<set>`); pure-interface ROM theorem (`PureRom`, `Rom/Sha2_<set>`) |
| `MIdeal` (1 + root) | `MIdeal/Sha2_128s.lean` | the closed ideal-model bound attached to `sets.sha2_128s.*` (§5) |

`Link`, `Reduction`, `E2E`, `Ideal` import nothing of `Spec`, `Slhdsa` or the `M*` libraries (checked by `scripts/check.sh` step 0c); the six-set
`Spec` = VCVio proofs are `MLink`. Every generic theorem and every `*_128s` theorem of `Reduction` is the single-set tree's source, and
`MReduction/Check128s.lean` shows ten of the `.s128s` statements are `rfl`-equal to them. Older documents: `REDUCTION_STATUS.md`,
`IDEAL_STATUS.md` and `status/*.md` describe the single-set development (`status/README.md`); `status/sets/` holds the six-set reports.

### The stand-ins, and what was deleted

`Reduction` states its SHA2-128s instances at `Link.vp`, `Link.prims` (24 modules), and `Ideal/Sha/Instantiate.lean` uses `Link.be32`,
`Link.app4`. In the single-set tree these came from `Link.Basic`, `Link.Hash`, `Link.Verify`, `Link.Sha256`, which also proved `Spec` = VCVio
against the single-set `Spec` (whose names clash with the parameterised `Spec`). They are now the Spec-free stand-ins that that project
used (its `shim/` directory): each keeps, with the same names and bodies, exactly the declarations of the original that do not
mention `Spec` (or the `Spec`-typed readings `sp`/`spA`); `Link.Hash` keeps none (it only imports `Link.Basic`), `Link.Verify` keeps
`decodeSig`, `decodePk`. `Reduction/PrfDomainNonVacuity.lean` is the original with one theorem, `Reduction.prf_128s_spec` (the PRF at 128s is
`Spec.PRF`), and its `#print axioms` line removed; its six-set replacement is `MReduction.prf_spec S`. **Fidelity, checked one last time before
the originals were deleted** (the same diffs that that project's `scripts/check.sh` step 3 ran, on the tree of commit `26aa3d8`, 2026-11-22):

| stand-in vs. original | lines added | lines removed | outcome |
|---|---|---|---|
| `Reduction/PrfDomainNonVacuity.lean` | 0 | 7 | as expected: `prf_128s_spec` (6 lines) and its `#print axioms` |
| `Link/Sha256.lean` (module docstring aside) | 0 | 251 | as expected; removed: `spA_get spA_length spA_push ssig0_eq ssig1_eq bsig0_eq bsig1_eq ch_eq maj_eq W_k W_iv blockAt_get expand_take readWord_eq loadSchedule_eq schedule_eq R round_eq runRounds_eq compress_eq push_loop u32be_eq u64be_eq pad_eq stateBytes_eq blocks_eq sha256_eq xor_loop xorConst_eq hmacKey0_eq hmacSha256_eq append_loop u32be_ofNat spA_extract mgf1_eq` (+ 3 `#print axioms`); no `Spec`/`sp`/`spA` left |
| `Link/Basic.lean` | 8 | 71 | added lines: the module docstring and three shortened doc comments; one `import Spec` removed; removed declarations `is sp cv spA nd sp_cv cv_sp sp_length cv_length sp_append sp_nil sp_take sp_drop sp_injective nd_length nd_injective spA_append spA_mk adr nds xmssBytes htBytes forsBytes sigBytes pkBytes` |
| `Link/Hash.lean` | 7 | 146 | added lines: `import Link.Basic` and the module docstring; removed: everything (`spec_sha256_length … Hmsg_eq`, the `Spec` = VCVio hash proofs) |
| `Link/Verify.lean` | 2 | 286 | added lines: `import Link.Hash` and the module title; kept `decodeSig`, `decodePk`; removed `ofFn_vec … slhVerify_eq` |

(Only the first two were part of the former check; the other three are recorded here for completeness.) Since then only the module docstrings
of the four `Link` stand-ins were reworded (they named the old layout); the declarations are unchanged. With the originals gone the diff step was
removed from `scripts/check.sh`; step 0c instead checks that `Link/` mentions no `Spec`/`sp`/`spA`. The originals are in git commit `26aa3d8`.

Deleted single-set files (all at commit `26aa3d8`): `Link/{Climb,Encoding,Fors,Hypertree,Keygen,Main,Sign,SignParts,Wots,Xmss}.lean` and the
originals of `Link/{Basic,Hash,Verify,Sha256}.lean`; `E2E/{Api,Bytes,External,Final,FinalSplit,Headline,HeadlineGen,Main,PureRom,PureRomBytes,
Reduction}.lean`; `Ideal/{Rust,RustFinal,RustFinalClosed,RustFinalClosedPure,RustFinalClosedPureApi,RustFinalClosedTight,RustFinalClosedTight2
… RustFinalClosedTight8}.lean` (13). `Reduction/Gen` is kept: it imports only `Reduction` modules and uses only `Link.vp`, `Link.prims`, so it
compiles over the stand-ins. What the deleted files proved and what replaces it: `../HANDOFF.md`, "What the single-set tree had that this tree
does not".

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
MGF1). `T_l` is only applied at lengths `len`, `k` (≠ 1). No Spec/VCVio discrepancy at any set. Details: `status/sets/B.md`, `status/sets/C.md`.

## 2. Reduction instances (`MReduction`; details and full numerals table: `status/sets/D.md`)

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
with `s128s`; games, adversaries, bound are those of `status/FINAL3.md` §1–§6 at `S.vp`, `S.prims`.

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

Key numerals (all Lean-proved; log2 approximations in `status/sets/D.md` computed outside Lean):

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
the other sets, as in `../lean/Slhdsa/Theorems.lean`; 128s is the old `E2E.rust_security` modulo Rust names — textual check in the generator).
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

## 3a. The interface `api`, typed forms (`ME2E/Api.lean` generic; `ME2E/Api/Sha2_<set>.lean`, generated)

Counterpart of the single-set `E2E/Api.lean` (git `26aa3d8`; and of the typed `PureEndToEnd` of its `E2E/External.lean`, `rust_keygen` / `rust_sign` /
`rust_verify` of `E2E/Main.lean`). Generator `scripts/gen_api_rom.py`: every statement is the single-set statement under textual renamings
(Rust names `slhdsa.api.f` → `slhdsa.sets.sha2_<set>.f`, `slhdsa.slh.slh_f` → `slhdsa.sets.sha2_<set>.slh_f`; sizes 16/32/48/64 → n/2n/3n/4n;
`Room`; `vp`, `prims`, codec, `node`, `secretKey`, `Link.decode*`, `*Bytes` at the set; `len`, `k`; forger `S` → `F`); the
generator asserts that undoing the renamings on the 128s output gives back the single-set text exactly (`check128s`), and `check.sh` step 0
re-runs both generators on a copy and diffs. Per set (namespace `ME2E.sha2_<set>`): `api_sign_eq`, `api_verify_eq` (unconditional, by unfolding:
the per-set `sign`/`verify` and `slh_sign`/`slh_verify` both call `slh::slh_sign`/`slh_verify`), `api_keygen_eq`, `api_sign_deterministic_eq`,
`api_keygen_bytes`, `api_sign_bytes`, `api_sign_deterministic_bytes`, `api_verify_bytes`, `api_pure_cores`, `ApiPureBytesEndToEnd` +
`api_pure_bytes_end_to_end`, `rust_keygen`, `rust_sign`, `rust_verify`, `PureEndToEnd` + `pure_end_to_end`, `ApiPureEndToEnd` +
`api_pure_end_to_end`, `api_pure_security`, `api_pure_security_linear`.
Generic (`ME2E/Api.lean`): `seeds_split`, `sk_split` (every `3n`/`4n`-byte array has exactly one block split: the block hypotheses restrict
nothing), `slhSign_tooLong`, `secretKey S`, `skBytes_secretKey`.

Verbatim, SLH-DSA-SHA2-128s (`ME2E/Api/Sha2_128s.lean`; `api_pure_security` at line 393):

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
```

At n = 24, 32 the same statements with 72/96/48/24-byte resp. 96/128/64/32-byte arrays and
`Room m.length 561`.

## 4a. Random-oracle theorem for the context-string interface (`ME2E/PureRom.lean` generic; `ME2E/Rom/Sha2_<set>.lean`, generated)

Generalises the single-set `E2E/{PureRom,PureRomBytes}.lean` (git `26aa3d8`; `E2E/GuardedRom`, `CodedRom` are kept here). What is 128s-specific there: `Link.vp`,
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

## 5. The closed ideal-compression bound, SLH-DSA-SHA2-128s only (`MIdeal/Sha2_128s.lean`, namespace `MIdeal.sha2_128s`)

Counterparts of `Ideal.rust_ideal_security_closed_tight8`, `Ideal.rust_ideal_security_closed_pure_tight8`,
`Ideal.api_ideal_security_closed_pure_tight8` (the single-set `Ideal/RustFinalClosedTight8.lean`, git `26aa3d8`; `status/TIGHT.md`, fourth session) for
the six-set tree's Rust functions: `rust_ideal_security_closed_tight8` (line 158; internal interface `slh_keygen_internal`,
`slh_sign_internal`, `slh_verify_internal`), `rust_ideal_security_closed_pure_tight8` (line 222; `slh_keygen_internal`, `slh_sign`,
`slh_verify`), `api_ideal_security_closed_pure_tight8` (line 274; `keygen`, `sign`, `sign_deterministic`, `verify`). Also `PureBytesEndToEnd`
(line 81, the six-set `E2E.PureBytesEndToEnd`: `pureBytesAlg` at `Sha2Set.s128s` is "sample, then apply the cores", complete, and
`slh_keygen_internal` / `slh_sign` / `slh_verify` are the cores) with `pure_bytes_end_to_end` (line 121), `pureBytesAlg_realCF` (line 138), and
the `rfl` bridges `vp_eq`, `prims_eq`, `codec_eq`, `bytesAlg_eq`, `pureBytesAlg_eq` (lines 59–68: `Sha2Set.s128s.vp = Link.vp`, `Sha2Set.s128s.prims =
Link.prims`, `codec Sha2Set.s128s = Reduction.codec128s`, and so `bytesAlg`/`pureBytesAlg` at the six-set names = at the single-set names).

**Textual identity.** `scripts/check_ideal128s.py` (check.sh step 0b) checks that each of the five statements (`PureBytesEndToEnd`,
`pureBytesAlg_realCF`, the three headlines) is the single-set statement of `security/` under these renamings only, whitespace aside:
`slhdsa.slh.slh_f` → `slhdsa.sets.sha2_128s.slh_f`, `slhdsa.api.f` → `slhdsa.sets.sha2_128s.f`; on the real-scheme side `vp prims codec128s`
and `Link.vp Link.prims Reduction.codec128s` → `Sha2Set.s128s.vp Sha2Set.s128s.prims (codec Sha2Set.s128s)`, `prims.Y` etc. →
`Sha2Set.s128s.prims.Y`; `node x` → `node Sha2Set.s128s x`; `Link.decodePk pk` → `MLink.decodePk Sha2Set.s128s pk`;
`E2E.(Api)PureBytesEndToEnd` → `PureBytesEndToEnd` / `ME2E.sha2_128s.ApiPureBytesEndToEnd`. The ideal-model game and the bound (conjunct 3)
are not touched by any renaming: they are the single-set text verbatim.

**How the scheme in the bound is the one the six-set Rust functions compute.** Conjunct 1 (from `ME2E.sha2_128s.rust_*_bytes` /
`api_pure_bytes_end_to_end`, i.e. `../lean`'s refinement theorems for `sets.sha2_128s.*` composed with `MLink`'s `Spec` = VCVio at
`Sha2Set.s128s`): the Rust functions never panic and are pointwise `byteKeygen` / `byteSign` / `byteVerify` (`byteSignPure` /
`byteVerifyPure`) at `Sha2Set.s128s.vp Sha2Set.s128s.prims (codec Sha2Set.s128s)`, the cores of `Reduction.bytesAlg` / `pureBytesAlg` at
those arguments. Conjunct 2: that very scheme (spelled at `Sha2Set.s128s`) is the scheme of the ideal-model game, `Reduction.bytesAlg Link.vp
(primsG (liftC g)) (codecG g) (optRandU oR g) ($ᵗ (Bytes 16))`, at the table `g = realCF` of the real SHA-256 compression function
(`Ideal.bytesAlg_realCF` / `pureBytesAlg_realCF`, via `Ideal.liftC_realCF : liftC realCF = VCVio.Algorithms.Sha2.compress`; the step from
`Link.vp Link.prims Reduction.codec128s` to the six-set spelling is definitional, the bridges above, as in `MReduction/Check128s.lean`).
Conjunct 3: `sufI`/`eufI` (`sufP`/`eufP`) are the SUF/EUF-CMA experiments of that game's scheme averaged over a uniformly random table `g`,
the forger's compression queries answered by `g`; bounded by `Ideal.suf_ideal_closed_tight8`, …, `Ideal.euf_ideal_pure_closed_tight8_2_64`
themselves.

Verbatim (line 158):

```lean
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
            ((2 : ℝ≥0∞) ^ 45)⁻¹ + ((2 : ℝ≥0∞) ^ 46)⁻¹ + ((2 : ℝ≥0∞) ^ 39)⁻¹))
```

`rust_ideal_security_closed_pure_tight8` (line 222) has conjunct 1 `PureBytesEndToEnd (fun pk => oR pk.pkSeed pk.pkRoot) ($ᵗ (Bytes 16))`
(about `slhdsa.sets.sha2_128s.{slh_keygen_internal, slh_sign, slh_verify}`, `Room m.length 409`), conjunct 2 `Reduction.pureBytesAlg Link.vp
(primsG (liftC realCF)) (codecG realCF) (optRandU oR realCF) ($ᵗ (Bytes 16)) = Reduction.pureBytesAlg Sha2Set.s128s.vp Sha2Set.s128s.prims
(codec Sha2Set.s128s) (fun pk => oR pk.pkSeed pk.pkRoot) ($ᵗ (Bytes 16))`, and conjunct 3 the single-set one verbatim: `∀ (S : ForgerP) (qf qs
ℓ : ℕ)`, query bounds `isPortQP`, `isSignQP`, `isLongQP ℓ`, `z.1.1.length ≤ ℓ`, `sufP`/`eufP`, and `ℓ + 257` in place of `ℓ` in the bound
and in the side conditions (`ℓ + 257 ≤ 2 ^ 26`); the same three points. `api_ideal_security_closed_pure_tight8` (line 274) has conjunct 1
`ME2E.sha2_128s.ApiPureBytesEndToEnd (fun pk => oR pk.pkSeed pk.pkRoot) ($ᵗ (Bytes 16))` (`keygen` on the three blocks of its seed string,
`sign`, `sign_deterministic`, `verify`) and conjuncts 2 and 3 of the pure statement (proof: `(rust_ideal_security_closed_pure_tight8 oR).2`).

**What it does not cover.** Everything `status/TIGHT.md` and `Ideal`'s own statements leave open carries over: conjunct 3 is
about the IDEAL-MODEL scheme (uniformly random 32-byte-state × 64-byte-block compression table) and says nothing about the real SHA-256
compression function; `opt_rand` is drawn by a table-independent `oR` from `(PK.seed, PK.root)`; `PK.seed` uniform; no running time, only query
counts; single key; pure mode only; messages ≤ `2^26` bytes. Conjunct 1 has the gaps (i)–(vi) of §3 (sampling not covered, `Room` bounds,
array sizes, `wire`/`node`, Rust compiler, Aeneas, side channels). **SLH-DSA-SHA2-128s only**: the ideal-model analysis is of SHA-256 with
16-byte outputs. It is written over `Link.vp` (n = 16, h = 63, d = 7, a = 12, k = 14) and over `primsG c`, which abstracts only the SHA-256
compression function, with every hash an `n = 16`-byte truncation of SHA-256 (MGF1-/HMAC-SHA-256 for `H_msg`/`PRF_msg`), and its
numerals (`QlinT8`, `QcAll` with the per-signature hash counts of 128s, `NAll`, the `2^128`/`2^256` denominators, the ITSR term with `k = 14`,
`a = 12`, the three points) are 128s numerals. Generalising to the other five sets would need: for 128f, re-instantiating the counting and
ITSR lemmas at its parameters (h = 66, d = 22, a = 6, k = 33: new per-signature counts, new `reuseSum` parameters, new numerals) — the
generic games and the SHA-256 model are reusable, but `Ideal/Inst/*128`, `Realize/*Count`, `ComposeFinal`/`FinalTight*` are stated at
`Link.vp`; for 192s/192f/256s/256f in addition a model with an ideal SHA-512 compression function (`H`, `T_l`, `H_msg`, `PRF_msg` use
SHA-512 there, `MReduction/Audit.lean`) next to the ideal SHA-256 one (F and PRF), `n = 24 / 32`-byte truncations (denominators `2^192`,
`2^256`), and the collection-oracle mixing caveat of §2 handled in the realisers.

Axioms (`check.sh` step 3): each of `MIdeal.sha2_128s.{rust_ideal_security_closed_tight8, rust_ideal_security_closed_pure_tight8,
api_ideal_security_closed_pure_tight8, pure_bytes_end_to_end, pureBytesAlg_realCF}` depends on `[propext, Classical.choice, Quot.sound]`.

## 5b. Forgers over a general sampling spec, SLH-DSA-SHA2-128s only (`ME2E/Gen128s.lean`, 2026-11-22)

Port of the single-set `E2E/HeadlineGen.lean` and of `E2E.api_pure_securityG` (git `26aa3d8`), made when the single-set tree was
removed: `ME2E.sha2_128s.{rust_securityG, rust_security_linearG, rust_pure_securityG, rust_pure_security_linearG,
rust_security_resourcesG, api_pure_securityG}`. Part (a) is part (a) of `rust_security` / `rust_pure_security` / `api_pure_cores` (the 128s Rust
functions are the byte-level cores); parts (b), (c) are `Reduction.Gen`'s 128s theorems for forgers whose private randomness is
`ds + unifSpec` (`ds` any oracle spec with an `AnswerMeasure` and finite answer types; right-hand advantages in `Reduction.Gen`'s wrapper
games, `status/GEN.md`). Each statement is the single-set text with the Rust names renamed and part (a)'s cores and `node` spelled at
`Sha2Set.s128s`; the forger types and bounds stay at `Link.vp`, `Link.prims`, `Reduction.codec128s` (`rfl`-equal). Textual check:
`scripts/check_ideal128s.py`. 128s only, because `Reduction/Gen` is stated at `Link.vp`.

## Per-set status

| | 128s | 128f | 192s | 192f | 256s | 256f |
|---|---|---|---|---|---|---|
| Link keygen/sign/verify (internal + pure, bytes), SHA-2 primitives | done | done | done | done | done | done |
| Reduction headlines, linear, det/hedged, resources with numerals | done | done | done | done | done | done |
| E2E (10 theorems), against the current `../rust` (portable build; `hw-sha2` build in `../security-hw`) | done | done | done | done | done | done |
| internal ROM bound + conformance (`MLink.security_sha2`) | done | done | done | done | done | done |
| `api` functions = cores; `api_pure_security(_linear)`; typed `PureEndToEnd` | done | done | done | done | done | done |
| pure-interface ROM theorem: typed, bytes, Rust and `api` forms | done | done | done | done | done | done |
| closed ideal-compression bound (`MIdeal`, §5): Rust internal, Rust pure, `api` | done | — | — | — | — | — |
| general-sampling-spec forgers (`ME2E/Gen128s`, §5b): Rust internal, pure, `api` | done | — | — | — | — | — |

## Not done / limitations

- Everything listed in `status/FINAL3.md` §7 carries over (advantages not bounded, no running time, single key, argued-only resource rows, …).
- Not ported to the other five sets: `Reduction/Gen/*` (compiled here, at `Link.vp`; attached to the 128s Rust functions in §5b); the single-set ideal-model Rust/API corollaries other than the three
  `…_tight8` ones (the single-set `Ideal/RustFinal*.lean`, earlier tightening stages; their bounds are all compiled here, in `Ideal`); the ideal-model bound at
  any set other than 128s (§5); the old typed-value and ROM forms of the single-set `E2E/Main.lean` (`end_to_end`, `EndToEnd`) and superseded intermediate E2E forms; `stepPRFC_128s`, `skPrf_broken_128s_half`; per-set copies of single-adversary numeral lemmas (their content is in the fields of `final_resources_final_<set>`); a `romScheme_verify_eq_spec` wrapper (follows from `romScheme_verify_eq` + `verify_eq_typed`, not stated).
- Not ported from the single-set `E2E/Api.lean`: `api_pure_standard_model_security_split` (needs `E2E/FinalSplit`'s loose-cap typed headline, not ported) (`api_pure_securityG` is ported for 128s, §5b); `Ideal.api_ideal_security_closed_pure` (superseded by its `_tight8` form, §5). Not ported from `PureRom.lean`/`PureRomBytes.lean`: nothing (all ten / ten declarations have counterparts; names `pure_security_128s(_euf)`, `pure_bytes_security_128s(_euf)` become the generic `pure_security_sha2 S`, `pure_bytes_security_sha2 S`).
- Differences from the single-set statements, all forced: Rust names (`sets.sha2_<set>.keygen` etc. instead of `api.keygen`, `slh.slh_*`); `Spec.KeyOk Spec.sha2_<set>` (the spec takes the parameter set); `secretKey Sha2Set.s128s sk`, `MLink.decodePk Sha2Set.s128s`, `MLink.skBytes Sha2Set.s128s` etc. for the single-set `secretKey sk`, `Link.decodePk`, `skBytes`; the forger variable is `F` (`S` is the set). `api_sign_eq`, `api_verify_eq` are proved by unfolding rather than `rfl`, same statements.
- The statements here are about the default (portable) translation `../lean/Slhdsa/Funs.lean`; the same files compiled against the `hw-sha2` translation (`../lean-hw`) give the same 232 headlines for that build (`../security-hw`).
- Per-set files of `MReduction` and `ME2E` are script-generated (`MReduction/gen`, `ME2E/gen`, `scripts/gen_api_rom.py`, outside the build): statements are explicit per set, proofs are one-line instances of the generic theorems.
- The "128s statement = old statement" check for `ME2E` is textual (generator assertion), for `MReduction` it is `rfl` (`Check128s.lean`). Package reports: `status/sets/B.md`–`E.md`, `status/sets/BRIEF.md`.

## Build and checks

`cd security && export PATH=$HOME/.elan/bin:$PATH && lake build` builds everything (dependencies VCVio/Mathlib/Aeneas prebuilt in `../.tools`;
"Build completed successfully (8205 jobs)", 4 min 16 s wall after the merge, when everything but the dependencies was rebuilt).
`scripts/check.sh` = (0) the ME2E generators (`ME2E/gen/gen.py`, `scripts/gen_api_rom.py`; their templates, the single-set tree's statements,
are read from git commit `26aa3d8`) and the MReduction generators (`MReduction/gen/{gen,gen_exp,gen_res}.py`) re-run on a copy of the tree, output
diffed against the checked-in files (this also runs the 128s textual checks of the ME2E generators) + (0b) `scripts/check_ideal128s.py`, the
MIdeal textual check (§5, against the same commit) + (0c) every root file (`Link.lean`, `Reduction.lean`, …) imports every module of its
directory; `Link`, `Reduction`, `E2E`, `Ideal` import nothing of `Spec`, `Slhdsa`, `M*`; `Link/` mentions no `Spec`/`sp`/`spA` + (1) `lake build`
+ (2) grep for `sorry`/`axiom`/`native_decide`/`bv_decide` outside comments in every source of the eight libraries + (3) `#print axioms` of 232
headline theorems (252 + the five of §5 + the six of `ME2E/Gen128s.lean`; output kept in `status/axioms.txt`) + (4) per-set list; exits non-zero on failure. (The former step 3,
the stand-in diffs, was removed with the originals; its last outcome is in "The stand-ins" above.) Last run: see `../HANDOFF.md`, "Checks".
`MReduction/gen/gen_sec.py` is not re-run: it was a scaffold for `MLink/Security.lean`, which was then finished by hand.

Sample of `status/axioms.txt`:

```
'MLink.sha512_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'MReduction.slhdsa_sha2_256f_bytes_suf_cma_final' depends on axioms: [propext, Classical.choice, Quot.sound]
'ME2E.sha2_192f.rust_security' depends on axioms: [propext, Classical.choice, Quot.sound]
'ME2E.sha2_256f.rust_security_resources' depends on axioms: [propext, Classical.choice, Quot.sound]
```
(all 232 lines are this triple).
