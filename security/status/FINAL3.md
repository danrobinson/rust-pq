# Standard-model security of SLH-DSA — final summary, phase 3

Lean 4.36.0, project `security/`. Everything below is proved and in the default `lake build` (targets `Link`, `E2E`, `Reduction`; 90 modules, 7702 jobs); no `sorry`, `axiom`, `native_decide`, `bv_decide`; nothing conditional except the non-cryptographic `Structural vp prims` (proved at SHA2-128s, `structural_128s`). Phase 3 adds, on top of `status/FINAL2.md` (all its theorems remain proved, none changed): byte-level schemes (W1), tight target caps (W2), direct resource lemmas with phase separation (W3), class TCR adversaries without structure recomputation (W5), the linear form (W7), and this integration (`Reduction/HeadlineFinal.lean`, `Reduction/ResourcesFinal.lean`, `E2E/Headline.lean`). Package reports: `status/W1.md`–`W7.md`. Details: `REDUCTION_STATUS.md`.

## 1. Final headline (verbatim; `Reduction/HeadlineFinal.lean`)

Context: `vp : ValidatedParams`, `prims : Primitives vp.params`, `codec : CoreWireCodec vp.params prims.core`; `optRand : PublicKeyCore prims.core → ProbComp prims.Y` and `pkSeedDist : ProbComp prims.PkSeed` **arbitrary**; classes `SampleableType` on `SkSeed`, `SkPrf`, `Y`; `DecidableEq` on `Y`, `PkSeed`, `AdrsKey`; `Inhabited Y`; `Fintype Y`. `BytesStrongForger … = SignatureAlg.StrongUnforgeableAdversary (bytesAlg vp prims codec optRand pkSeedDist)`, `PureBytesStrongForger …` likewise for `pureBytesAlg`.

```lean
noncomputable def boundFinalTight pkSeedDist B₁ B₂ B₃ D T C₁ C₂ C₃ C₄ B₆ B₇ B₈ : ℝ≥0∞ :=     -- TightCapsHeadline.lean
  (skPrfC vp prims).prfAdvantage B₁ + (msgPrf vp prims).prfAdvantage B₂ + KeyedHash.ITSRAdvantage B₃ +
    (SM_DT_DSPR_SourceFinalValidity.advantage D + 3 * SM_DT_TCR_SourceFinalValidity.advantage T) +
    (SM_DT_TCR_Advantage C₁ + SM_DT_TCR_Advantage C₂ + SM_DT_TCR_Advantage C₃ + SM_DT_TCR_Advantage C₄) +
    ((vp.params.w - 2 : ℕ) : ℝ≥0∞) * SM_DT_UD_Advantage B₆ + SM_DT_PRE_Advantage B₇ + SM_DT_TCR_Advantage B₈
  -- Cᵢ : SM_DT_TCR_Adversary (thashArityProblemT vp prims pkSeedDist n), n = 1, 2, vp.params.len, vp.params.k
  -- B₈ : SM_DT_TCR_Adversary (wotsTcrProblemT vp prims pkSeedDist);  D, T on forsDsprProblem, forsTcrProblem;  B₆, B₇ on wotsUdProblem, wotsPreProblem

theorem slhdsa_bytes_suf_cma_final (hS : Structural vp prims)
    (S : BytesStrongForger vp prims codec optRand pkSeedDist) :
    SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S ≤
      boundFinalTight pkSeedDist (bPrfWC sufCheck (bytesToTypedS S).toUnforgeableAdversary)
        (Lazy.bPrfMsgWL sufCheck (bytesToTypedS S).toUnforgeableAdversary)
        (Lazy.bItsrL (bytesToTypedS S).toUnforgeableAdversary)
        (toDspr (Lazy.bOpenPreS (bytesToTypedS S).toUnforgeableAdversary))
        (toTcr (Lazy.bOpenPreS (bytesToTypedS S).toUnforgeableAdversary))
        (bTcrArM 1 (bytesToTypedS S).toUnforgeableAdversary) (bTcrArM 2 (bytesToTypedS S).toUnforgeableAdversary)
        (bTcrArM vp.params.len (bytesToTypedS S).toUnforgeableAdversary)
        (bTcrArM vp.params.k (bytesToTypedS S).toUnforgeableAdversary)
        (rUd pkSeedDist (Lazy.bWotsS (bytesToTypedS S).toUnforgeableAdversary))
        (rPre pkSeedDist (Lazy.bWotsS (bytesToTypedS S).toUnforgeableAdversary))
        (rTcrT pkSeedDist (Lazy.bWotsS (bytesToTypedS S).toUnforgeableAdversary))

theorem slhdsa_pure_bytes_suf_cma_final (hS : Structural vp prims)
    (S : PureBytesStrongForger vp prims codec optRand pkSeedDist) :
    SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S ≤
      boundFinalTight pkSeedDist (bPrfWC sufCheck (toInternal (pureBytesToTyped S.toUnforgeableAdversary)))
        (Lazy.bPrfMsgWL sufCheck (toInternal (pureBytesToTyped S.toUnforgeableAdversary)))
        …   -- the same eleven further arguments as above with  toInternal (pureBytesToTyped S.toUnforgeableAdversary)
            -- in place of  (bytesToTypedS S).toUnforgeableAdversary  (written out in the file)
```

Scheme in the game (`Reduction/Bytes.lean`): `bytesAlg` — keys, messages, signatures are `List Byte`; keygen draws `PK.seed ← pkSeedDist`, `SK.seed`, `SK.prf` uniform, returns `byteKeygen`; sign parses `pk` (only to feed `optRand`), draws `opt_rand ← optRand pk`, returns `byteSign m sk opt_rand`; verify `= byteVerify m sig pk` (FIPS 205 Alg. 18–20 on wire encodings). `pureBytesAlg` — Alg. 21/22/24: messages `(M, ctx)`, signature `Option (List Byte)` (`none` iff `|ctx| > 255`, never accepted). `bytesToTypedS S` / `pureBytesToTyped` encode the key, run the forger once, one typed signing query per query, decode its output.

Variants, same file unless noted (all proved, same right-hand side shape):
- EUF: `slhdsa_bytes_euf_cma_final`, `slhdsa_pure_bytes_euf_cma_final` (`bPrfC`, `Lazy.bPrfMsgL`, forger `bytesToTyped A` / `toInternal (pureBytesToTyped A)`).
- Typed keys/signatures (`internalAlg`, `externalAlg`): `slhdsa_{suf,euf,pure_suf,pure_euf}_cma_final_memo` (`Reduction/TcrMemoHeadline.lean`); compact `∀`-forms (primed) with `betaSufFinalMemo` / `betaEufFinalMemo` (= the bound above as a function of the typed forger; `slhdsa_bytes_suf_cma_final_rhs : … = betaSufFinalMemo … := rfl`).
- SHA2-128s without hypothesis: `slhdsa_sha2_128s_{bytes,pure_bytes}_{suf,euf}_cma_final`, `slhdsa_sha2_128s_{suf,euf,pure_suf,pure_euf}_cma_final_memo`.
- Bounds are *equal* to the earlier ones: `betaSufFinalMemo_eq`, `…_eq_split` (`= betaSufFinalTight = betaSufFinalSplit`), because re-capping and memoising give equal experiments (`bTcrArST_experiment_eq`, `rTcrT_experiment_eq`, `bTcrArM_experiment_eq`).
- Older theorems (`_split`, `_tight`, unsplit `_final`, phase 1) remain proved.

## 2. Linear form (verbatim; SUF part of `E2E.rust_security_linear`, `E2E/Headline.lean`; `vp`, `prims` = `Link.vp`, `Link.prims`, `T := (bytesToTypedS S).toUnforgeableAdversary` abbreviates only this summary)

```lean
∀ S : SignatureAlg.StrongUnforgeableAdversary (bytesAlg vp prims codec128s optRand pkSeedDist),
  SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S +
      (prfIdealPr (bPrfWC sufCheck T) + msgIdealPr (bPrfMsgWL sufCheck T) +
        SM_DT_DSPR_SourceFinalValidity.SPProbability (toDspr (bOpenPreS T)) +
        ((vp.params.w - 2 : ℕ) : ℝ≥0∞) * SM_DT_UD_IdealSuccess (rUd pkSeedDist (bWotsS T))) ≤
    prfRealPr (bPrfWC sufCheck T) + msgRealPr (bPrfMsgWL sufCheck T) + KeyedHash.ITSRAdvantage (bItsrL T) +
    (SM_DT_DSPR_SourceFinalValidity.Success (toDspr (bOpenPreS T)) +
      3 * SM_DT_TCR_SourceFinalValidity.advantage (toTcr (bOpenPreS T))) +
    (SM_DT_TCR_Advantage (bTcrArM 1 T) + SM_DT_TCR_Advantage (bTcrArM 2 T) +
      SM_DT_TCR_Advantage (bTcrArM 35 T) + SM_DT_TCR_Advantage (bTcrArM 14 T)) +
    ((vp.params.w - 2 : ℕ) : ℝ≥0∞) * SM_DT_UD_RealSuccess (rUd pkSeedDist (bWotsS T)) +
    SM_DT_PRE_Advantage (rPre pkSeedDist (bWotsS T)) + SM_DT_TCR_Advantage (rTcrT (vp := vp) pkSeedDist (bWotsS T))
```

Legend (every term is `Pr[experiment = true]` of an explicit `ProbComp Bool`, `≤ 1`; no absolute value, no truncated subtraction): `prfRealPr B` / `prfIdealPr B` = PRF distinguisher `B` on `skPrfC` outputs `true` with the real function `(PK.seed, a) ↦ PRF(PK.seed, k, a)` / with a lazy random function; `msgRealPr`, `msgIdealPr` the same for PRF_msg; `SM_DT_UD_RealSuccess` / `SM_DT_UD_IdealSuccess` = SM-UD(F) experiment with real / uniform challenges; `SM_DT_DSPR_SourceFinalValidity.Success D` = DSPR experiment, `.SPProbability D` = same run, accept iff the selected target has a second preimage; the other eight terms are those of §1. Exact parts: `Adv = prfRealPr B₁`, `prfIdealPr B₁ = msgRealPr B₂`, `msgIdealPr B₂ = Pr[G2]` (equalities `prfRealPr_bPrfWC`, …); `wotsUD_telescope` is an exact identity. Generic names: `slhdsa_{suf,euf}_cma_final_linear(_explicit)`, `slhdsa_pure_{suf,euf}_cma_final_linear` (`Reduction/Linear.lean`), `slhdsa_{bytes,pure_bytes}_{suf,euf}_cma_linear(_128s)` (`Reduction/LinearBytes.lean`), `E2E.rust_pure_security_linear`. The absolute-value bound follows by cancelling the finite left bracket: `boundFinalTight_of_linear`, `slhdsa_*_memo_of_linear`.

## 3. Uniform seed, FIPS `opt_rand` (corollaries; `Reduction/HeadlineFinal.lean`)

The general theorems hold for arbitrary `pkSeedDist`; for a degenerate seed distribution they are statements about games with a known seed (true, but the assumptions are then implausible). Instances with `pkSeedDist := $ᵗ prims.PkSeed` (needs `SampleableType prims.PkSeed`) and
- deterministic: `optRand := fun pk => pure (toY pk.pkSeed)`, `toY : prims.PkSeed → prims.Y` a parameter; at 128s `toY := SLHDSA.Concrete.sha2RandomizerOfPkSeed Link.vp.params` (identity on `Bytes 16`, `detRand_128s … = s := rfl`), i.e. `opt_rand = PK.seed`;
- hedged: `optRand := fun _ => $ᵗ prims.Y`.

Names: `slhdsa_{,pure_}{,bytes_}{suf,euf}_cma_{deterministic,hedged}` (16, generic, hypothesis `hS`) and `slhdsa_sha2_128s_{,pure_}{,bytes_}{suf,euf}_cma_{deterministic,hedged}` (16, no hypothesis). Example, verbatim:

```lean
theorem slhdsa_sha2_128s_bytes_suf_cma_deterministic
    (S : BytesStrongForger Link.vp Link.prims codec128s
      (fun pk => (pure (SLHDSA.Concrete.sha2RandomizerOfPkSeed Link.vp.params pk.pkSeed) : ProbComp Link.prims.Y))
      ($ᵗ Link.prims.PkSeed)) :
    SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S ≤
      betaSufFinalMemo (bytesToTypedS S).toUnforgeableAdversary
theorem slhdsa_sha2_128s_pure_bytes_suf_cma_hedged
    (S : PureBytesStrongForger Link.vp Link.prims codec128s (fun _ => $ᵗ Link.prims.Y) ($ᵗ Link.prims.PkSeed)) :
    SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S ≤
      betaSufFinalMemo (toInternal (pureBytesToTyped S.toUnforgeableAdversary))
```
E2E forms (SUF ∧ EUF): `E2E.rust_security_deterministic`, `_hedged`, `E2E.rust_pure_security_deterministic`, `_hedged`.

## 4. Rust attachment (`E2E/Headline.lean`)

`E2E.rust_security optRand pkSeedDist` = (a) ∧ (b) ∧ (c); `E2E.rust_pure_security` likewise for `slh_sign`/`slh_verify` with `Room … 409`, `byteSignPure`, `byteVerifyPure`, `pureBytesAlg`.
(a) `∀ sk_seed sk_prf pk_seed, ∃ sk pk, slh_keygen_internal sk_seed sk_prf pk_seed = ok (sk, pk) ∧ (wire pk.val, wire sk.val) = byteKeygen vp prims codec128s (node sk_seed) (node sk_prf) (node pk_seed)`; `∀ m sk addrnd, Room m.length 152 → ∃ sig, slh_sign_internal m sk addrnd = ok sig ∧ wire sig.val = byteSign vp prims codec128s (wire m.val) (wire sk.val) (node addrnd)`; `∀ m sig pk, Room m.length 152 → slh_verify_internal m sig pk = ok (byteVerify vp prims codec128s (wire m.val) (wire sig.val) (wire pk.val))`.
(b) `∀ S : StrongUnforgeableAdversary (bytesAlg vp prims codec128s optRand pkSeedDist), Adv^SUF(S) ≤` the twelve terms of `boundFinalTight` written out (as §2's right side with `prfAdvantage`, `…DSPR….advantage`, `SM_DT_UD_Advantage`), at `(bytesToTypedS S).toUnforgeableAdversary`. (c) the same for EUF at `bytesToTyped A`.
Resources: `E2E.rust_security_resources`, `E2E.rust_pure_security_resources` (query bound of the typed forger ∧ `FinalResourcesFinal … (directCounts128s qs) (269824 + qs * 2007385 + 7857)`).

**Exact remaining gap between the scheme in the game and the Rust functions** (each item checked against the statements of (a) and `bytes_end_to_end`):
(i) Sampling: the scheme draws `PK.seed ← pkSeedDist`, `SK.seed`, `SK.prf` uniform, `opt_rand ← optRand pk`; the Rust functions take `sk_seed`, `sk_prf`, `pk_seed`, `addrnd` as arguments (universally quantified in (a)); no sampling code is covered (deterministic variant: the caller passes `addrnd = pk_seed`).
(ii) `Room m.length 152` (internal sign/verify) / `409` (external) on the Rust side (`m.length + slack ≤ usize::MAX` and `< 2^61`); keygen has no side condition; the scheme is total.
(iii) Rust keys are `[u8; 32]`, `[u8; 64]`; the scheme takes any byte strings: wrong-length pk ⇒ verify rejects, sign returns `[]`/`none`; wrong-length sk ⇒ `[]`/`none`; `[]`/`none` never accepted (`byteVerify_of_pk_length_ne`, `sign_bad_pk`, `byteSign_of_sk_length_ne`, `byteVerify_nil`). Every 32/64-byte string parses; no secret-key well-formedness check (the `PK.seed`, `PK.root` inside `sk` are used as they are). Such inputs do not arise in the games.
(iv) Representations: Aeneas `U8` lists ↔ `List UInt8` by `wire` (length-preserving bijection: `wire_injective`, `wire_surjective`); 16-byte arrays ↔ `Vector UInt8 16` by `node`; `byteKeygen` returns `(pk, sk)`, Rust `(sk, pk)`; every Rust result is `ok`.
(v) The scheme's `sign` takes the public key (only to evaluate `optRand`); Rust signing has no pk argument; in the games both copies of `PK.seed` come from `byteKeygen`. External: `none` for an over-long context is returned before sampling.
(vi) Outside: the twelve advantages are not bounded; no running time; single key; pure mode only (no pre-hash); Rust compiler, Aeneas extraction, side channels.

## 5. Games and caps (all draw `PK.seed` from `pkSeedDist`; definitions as in FINAL2 §Games; 128s numerals proved by `decide`/`rfl` on closed forms)

| game (problem) | cap in `_split` theorems | cap in the final theorems | 128s |
|---|---|---|---|
| PRF on `SkAdrs` (`skPrfC`), PRF_msg (`msgPrf`), ITSR (`itsrProblem`) | no cap | no cap | — |
| SM-DSPR(F), SM-TCR(F) at FORS leaves (`forsDsprProblem`, `forsTcrProblem`) | `2^h·k·2^a` | same (attained exactly) | `528905046081400263933952 ≈ 2^78.81` |
| SM-TCR(F) (`thashArityProblemT … 1`) | `tcrTargets` = `1062560399506556770327551 ≈ 2^79.81` | `arityTargets vp 1` | `533756792467910173399552 ≈ 2^78.82` |
| SM-TCR(H) (`… 2`) | `tcrTargets` | `arityTargets vp 2` | `528785142244921151848447 ≈ 2^78.81` |
| SM-TCR(T_len) (`… len`) | `tcrTargets` | `arityTargets vp len` | `9241421688590303744 ≈ 2^63.003` |
| SM-TCR(T_k) (`… k`) | `tcrTargets` | `arityTargets vp k` | `9223372036854775808 = 2^63` |
| SM-UD(F), SM-PRE(F) (`wotsUdProblem`, `wotsPreProblem`) | `#inst·len` | same (= proved bound) | `323449759100660631040 ≈ 2^68.13` |
| SM-TCR(F) on chains (`wotsTcrProblemT`) | `#inst·len·w` = `5175196145610570096640 ≈ 2^72.13` | `#inst·len·(w−1)` | `4851746386509909465600 ≈ 2^72.04` |

Class caps are attained in every run (`bTcrArM_targets_eq_cap`); UD/PRE/chain caps equal the best proved adversary-independent bound (attainment not proved). `thashArityProblemT_cap_128s`, `wotsTcrProblemT_cap_128s`; non-vacuity of the tight games: `thashArityT_trivial_adv_zero`, `thashArityColliderT_adv_one`, `wotsTcrT_trivial_adv_zero`, `wotsTcrColliderT_adv_one`.

## 6. Adversaries and resources (`Reduction/ResourcesFinal.lean`: `final_resources_final hS A qs hA : FinalResourcesFinal A qs (directCounts vp qs) (keygenHashes vp + qs * signHashes vp + (1 + verifyHashes vp * 2))`, `final_resources_final_external`, `final_resources_final_128s`)

`qs` = signing queries of the forger; 128s numerals; **F** = formal (field of the bundle), **A** = argued (counting argument in W3/W5, not a theorem).

| adversary | pre-seed oracle queries | post-seed own hash evaluations | fresh samples |
|---|---|---|---|
| `bPrfC`, `bPrfWC sufCheck` (single phase) | PRF queries `≤ 17920 + qs·182784` **F** | not modelled | none |
| `Lazy.bPrfMsgL/WL`, `Lazy.bItsrL` (single phase) | game queries `≤ qs` **F** | `≤ 269824 + qs·2007385` (final verification excluded) **F** | `≤ 17920 + qs·182784` **F** |
| `toDspr`/`toTcr (bOpenPreS A)` | targets exactly `528905046081400263933952`, collection 0 **F** | `≤ 269839 + qs·1950028`; `≤ 14·qs` local openings **F** | exactly `323449759100660631040 + 528905046081400263933952` **F** |
| `bTcrArM n A` (`n = 1, 2, 35, 14`) | targets exactly the cap (§5); targets + collection `= 1062560399506556770327551` **F** | `≤ 269824 + qs·2007385 + 7857` **F** (incl. verification of the forgery and collision test) | exactly `529228495840500924564992` **F** |
| `rUd (bWotsS A)` | challenges `≤ 323449759100660631040` **F**; collection `≤ 1062560399506556770328574` **A** | `≤ qs·121857 + 525` **F** + `wotsAnswer` tail `≤ 129714` **A** | inner exactly `528905046081400263933952` **F**; wrapper `1 + ≤ 323449759100660631040` **A** |
| `rPre (bWotsS A)` | challenges `≤ 323449759100660631040` **F**; collection **A** | `≤ qs·121857 + 560` **F** + tail **A** | as `rUd` |
| `rTcrT (bWotsS A)` | targets `≤ 4851746386509909465600` **F**; collection `≤ 1058032102879147521494014` **A** | `≤ qs·121857 + 16800` **F** + tail **A** | as `rUd` |
| `toInternal`, `bytesToTyped(S)`, `pureBytesToTyped(S)` | signing queries `≤ qs` **F** | none of their own | none |

Argued for all rows: phase-1 programs do no hashing of their own (inspection; a formal "zero" is not expressible in the open-program model); list work and the size of the state carried across the reveal are not counted; no lower bounds. Model of "own hash evaluations": the adversary's post-seed program is proved equal to the interpretation of an open program in which every `Thash`/`H_msg` evaluation is an oracle query, and those queries are bounded (`IsQueryBoundP`).

Definition-level check (`scratch/Final/FinalCheck.lean`, output `scratch/Final/FinalCheck.out`; follows definition bodies, never proofs): all twelve adversaries (`bPrfC`, `bPrfWC`, `sufCheck`, `Lazy.bPrfMsgL`, `Lazy.bPrfMsgWL`, `Lazy.bItsrL`, `Lazy.bOpenPreS`, `toDspr`, `toTcr`, `bTcrArM`, `Lazy.bWotsS`, `rUd`, `rPre`, `rTcrT`), their parts (`memoForge`, `findCollisionM`, `chkM`, `classOut`, `Lazy.bTcrS`, `TcrSplit.route`, `TightCaps.retype`, `rTcr`, …), the wrappers (`toInternal(S)`, `Guarded.reduce(S)`, `bytesToTyped(S)`, `pureBytesToTyped(S)`, `Coded.reduce(S)`, `bytesView`, `pureBytesView`, `codec128s`), the five byte-level cores and the open programs reach none of `Classical.choice`, `Classical.indefiniteDescription`, `Exists.choose`, `Classical.propDecidable`, `Fintype.equivFin`, `sampleTable`, `Tables.uniformTable`, `UniformSampler.sample`, `Fin.mOfFn`, `Fintype.mPi` ("flagged: []", 55 constants); controls flagged as expected (`bPrfMsg`, `bPrfMsgW`, `bTcr`, `bTcrAr`: `sampleTable`, `Fin.mOfFn`; `betaSufFinal`, `betaSufFinalSplit`, `betaSufFinalMemo`, `linRealSuf`: choice, being measures).

## 7. Limitations and things not done

1. The twelve right-hand advantages are not bounded: smallness for the SHA-256-based functions is an assumption. (The `Ideal` library of the other team is separate and not covered here.)
2. No running-time claim. Nine of twelve adversaries register `≈ 2^63`–`2^79` targets before the seed reveal regardless of `qs` (the SM games give the seed only to the second phase; as in HK22/EC). Post-seed hashing is now poly(`qs`) for all nine, but:
3. `bTcrArM` stores `(tweak, input)` pairs, not hash values, so the signatures for the forger are still hashed locally after the reveal (`qs·2007385` term) and `PK.root` is recomputed; an answer-storing variant (≈ `qs + 1 + 3928` hashes) is analysed in W5 but not formalised. Its state is `tcrTargets ≈ 2^79.81` pairs; lookups in it are list searches (not counted).
4. Argued only: collection-query and wrapper-sample counts of `rUd/rPre/rTcrT`, the `wotsAnswer` tail, hash counts of `bPrfC/bPrfWC`, absence of phase-1 hashing, all list work.
5. Fixed-index SM-UD adversaries are not given (only the fixed-index experiment `WotsUD.udFixed`; the headline uses the single adversary `rUd` with a uniform hybrid index and factor `w−2`). No linear forms of the older (`_split`, `_tight`) headlines. No loose-cap twin of `bTcrArM`.
6. TCR terms are per arity, not per address type: one `H` term for FORS and XMSS trees, and an extra `F` class term. SUF and EUF use different PRF/PRF_msg distinguishers. No lemma that a left side can be positive.
7. Single key. External: pure mode only. Byte-level and external transfers are `≤`. Uniform-seed corollaries are stated for the absolute-value form only (the linear theorems take arbitrary `pkSeedDist`, `optRand`, so they instantiate directly).
8. `skPrfC`'s domain is a superset of the honest addresses; SHA-256 is modelled past the 2^64-bit length limit. Rust side: §4 (i)–(vi).

## 8. Build and checks

`cd security && export PATH=$HOME/.elan/bin:$PATH && lake build Link E2E Reduction` — "Build completed successfully (7702 jobs)". Modules: 16 `Link`, 8 `E2E`, 66 `Reduction` (roots included). Timing on a 36-core machine: the other team's Lean jobs ran continuously, so our oleans in `.lake/build` were **not** deleted; measured instead (i) the integration build that recompiled 38 `Reduction` and 6 `E2E` modules: 45.4 s wall; (ii) a from-scratch compile of all 90 modules of the three libraries into a separate output directory (`lean -o`, `make -j36`, dependencies prebuilt, under the other team's concurrent load): 72.7 s wall, 202 s user CPU, no error, 569 `#print axioms` lines, none with `sorryAx`. Source grep: no `sorry`, `axiom `, `native_decide`, `bv_decide` in `Link/`, `E2E/`, `Reduction/` outside `#print axioms` lines and three comments saying "no `native_decide`" (`Link/Security.lean:136`, `Reduction/Resources.lean:13`, `Reduction/TightCaps.lean:28`).

```
'E2E.rust_security' depends on axioms: [propext, Classical.choice, Quot.sound]
'E2E.rust_pure_security' depends on axioms: [propext, Classical.choice, Quot.sound]
'E2E.rust_security_linear' depends on axioms: [propext, Classical.choice, Quot.sound]
'E2E.rust_pure_security_linear' depends on axioms: [propext, Classical.choice, Quot.sound]
'E2E.rust_security_deterministic' depends on axioms: [propext, Classical.choice, Quot.sound]
'E2E.rust_security_hedged' depends on axioms: [propext, Classical.choice, Quot.sound]
'E2E.rust_pure_security_deterministic' depends on axioms: [propext, Classical.choice, Quot.sound]
'E2E.rust_pure_security_hedged' depends on axioms: [propext, Classical.choice, Quot.sound]
'E2E.rust_security_resources' depends on axioms: [propext, Classical.choice, Quot.sound]
'E2E.rust_pure_security_resources' depends on axioms: [propext, Classical.choice, Quot.sound]
'Reduction.slhdsa_bytes_suf_cma_final' depends on axioms: [propext, Classical.choice, Quot.sound]
'Reduction.slhdsa_bytes_euf_cma_final' depends on axioms: [propext, Classical.choice, Quot.sound]
'Reduction.slhdsa_pure_bytes_suf_cma_final' depends on axioms: [propext, Classical.choice, Quot.sound]
'Reduction.slhdsa_pure_bytes_euf_cma_final' depends on axioms: [propext, Classical.choice, Quot.sound]
'Reduction.final_resources_final' depends on axioms: [propext, Classical.choice, Quot.sound]
'Reduction.final_resources_final_128s' depends on axioms: [propext, Classical.choice, Quot.sound]
```
(The four `slhdsa_sha2_128s_*bytes*_cma_final` theorems, the 32 `_deterministic` / `_hedged` corollaries, `final_resources_final_external`, and the W1–W7 theorems named above print the same three axioms; `findCollisionM_eq` prints `[propext, Quot.sound]`.)
