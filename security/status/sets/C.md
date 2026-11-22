# Package C (SIGN) — status

## Interface notes (read first, E2E package)
Interface published (`status/C-interface.ok`); everything is proved (no `sorry`), statements final.
One change after the marker was created (about a minute later, before this report):
`sign_eq_bytes` / `slhSign_eq_bytes` were restated from a `match decodeSk S (cv sk) with …` form to
the existential form below (a `match` in a statement is not syntactically the `match` inside
`Reduction.byteSign`/`byteSignPure`; the existential form rewrites cleanly). `skBytes`,
`keygen_eq`, `sign_eq`, `slhSign_eq` and the length lemmas never changed.

Differences from the mechanical substitution of security/Link (none weakening):
1. `xmssNode_eq` takes `z ≤ S.vp.params.hp`, `t < 2 ^ (S.vp.params.hp - z)`; `xmssSign_eq` takes
   `idx < 2 ^ S.vp.params.hp`; `forsNode_eq` takes `z ≤ S.vp.params.a`,
   `t < S.vp.params.k * 2 ^ (S.vp.params.a - z)`; `forsSign_eq` takes
   `md.length = S.vp.params.digestBytes`.
2. `wotsSk_dom` takes `i < 2 ^ 32` (was `i < 35`); `fors_sib (a i f j) (hj : j < a)` has the height
   explicit; former `private` helpers are public; duplicates of package B helpers were dropped
   (B's `wotsChain_dom`, `wotsPk_dom`, `xmssNode_dom`, `nds_ofFn`, `specChain_word3`, `chainSteps_eq`
   are used). New helpers: `skBytes_length`, `adr_wotsSk`, `adr_wotsChain`, `topLayer_baseDom`,
   `htRoot_eq`, `sib_lt`, `skBytes_block`, `cv_withContext`.
3. `signFrom_eq` is proved for every value of VCVio's `recoverFinal` flag
   (`GeneralHypertree.sign` passes `d == 1`, which is `false` on all six sets but is not needed).
4. New (not in security/Link; the old development had them in E2E/Bytes.lean for 128s):
   `encodeSk S`, `decodeSk S` (abbrevs at `sha2WireCodec S.vp.params`, `HEq` to
   `encode/decodeApprovedSecretKey S.fips`), `sp_encodeSecretKey`, `cv_skBytes`, `cv_sigBytes`,
   `cv_pkBytes`, `decodeSk_ok`, `decodeSk_skBytes`, and the byte forms below.

## Result (final)
`lake build MLink.Sign` green; no `sorry`/`axiom`/`native_decide`/`bv_decide` in
MLink/{Keygen,SignParts,Sign}.lean; `#print axioms` of every headline (ends of the three files) is
`[propext, Classical.choice, Quot.sound]`. One proof generic over `S : Sha2Set`; no per-set case
split (only B's/A's small numeric lemmas). `MLink.lean` got three appended import lines.

Main statements (`variable (S : Sha2Set)`):

    def skBytes (k : SecretKeyCore S.prims.core) : Spec.Bytes :=
      nd k.skSeed ++ nd k.skPrf ++ nd k.pkSeed ++ nd k.pkRoot
    theorem skBytes_length (k) : (skBytes S k).length = 4 * S.spec.n

    theorem keygen_eq (skSeed skPrf pkSeed : S.Node) :
        Spec.slhKeygenInternal S.spec (nd skSeed) (nd skPrf) (nd pkSeed) =
          (skBytes S (GeneralScheme.keygenInternal S.vp S.prims skSeed skPrf pkSeed).2,
           pkBytes S (GeneralScheme.keygenInternal S.vp S.prims skSeed skPrf pkSeed).1)

    theorem sign_eq (msg : Spec.Bytes) (sk : SecretKeyCore S.prims.core) (addrnd : S.Node) :
        Spec.slhSignInternal S.spec msg (skBytes S sk) (nd addrnd) =
          sigBytes S (GeneralScheme.signInternal S.vp S.prims (cv msg) sk addrnd)

    theorem slhSign_eq (msg ctx : Spec.Bytes) (sk : SecretKeyCore S.prims.core) (addrnd : S.Node) :
        Spec.slhSign S.spec msg ctx (skBytes S sk) (nd addrnd) =
          (External.signPureWithRandomizer S.vp S.prims (cv msg) (cv ctx) sk addrnd).toOption.map
            (sigBytes S)

Byte forms for E2E (`encodeSig S`/`encodePk S` are B's abbrevs):

    theorem keygen_eq_bytes (skSeed skPrf pkSeed : S.Node) :
        (cv (Spec.slhKeygenInternal S.spec (nd skSeed) (nd skPrf) (nd pkSeed)).2,
         cv (Spec.slhKeygenInternal S.spec (nd skSeed) (nd skPrf) (nd pkSeed)).1) =
          (encodePk S (GeneralScheme.keygenInternal S.vp S.prims skSeed skPrf pkSeed).1,
           encodeSk S (GeneralScheme.keygenInternal S.vp S.prims skSeed skPrf pkSeed).2)
      -- RHS is definitionally `Reduction.byteKeygen S.vp S.prims (sha2WireCodec S.vp.params) …`
    theorem sign_eq_enc (msg) (k) (addrnd) :
        cv (Spec.slhSignInternal S.spec msg (skBytes S k) (nd addrnd)) =
          encodeSig S (GeneralScheme.signInternal S.vp S.prims (cv msg) k addrnd)
    theorem slhSign_eq_enc (msg ctx) (k) (addrnd) :
        (Spec.slhSign S.spec msg ctx (skBytes S k) (nd addrnd)).map cv =
          (External.signPureWithRandomizer S.vp S.prims (cv msg) (cv ctx) k addrnd).toOption.map
            (encodeSig S)
    theorem sign_eq_bytes (msg sk : Spec.Bytes) (hs : sk.length = 4 * S.spec.n) (addrnd : S.Node) :
        ∃ k, decodeSk S (cv sk) = .ok k ∧ sk = skBytes S k ∧
          cv (Spec.slhSignInternal S.spec msg sk (nd addrnd)) =
            encodeSig S (GeneralScheme.signInternal S.vp S.prims (cv msg) k addrnd)
    theorem slhSign_eq_bytes (msg ctx sk : Spec.Bytes) (hs : sk.length = 4 * S.spec.n)
        (addrnd : S.Node) :
        ∃ k, decodeSk S (cv sk) = .ok k ∧ sk = skBytes S k ∧
          (Spec.slhSign S.spec msg ctx sk (nd addrnd)).map cv =
            (External.signPureWithRandomizer S.vp S.prims (cv msg) (cv ctx) k addrnd).toOption.map
              (encodeSig S)

Checked in a scratch file (not part of the project; MLink does not import Reduction): from these,

    (Spec.slhSign S.spec msg ctx sk (nd addrnd)).map cv =
      Reduction.byteSignPure S.vp S.prims (sha2WireCodec S.vp.params) (cv msg) (cv ctx) (cv sk) addrnd

follows by `obtain ⟨k, hk, -, h⟩ := slhSign_eq_bytes S msg ctx sk hs addrnd;
simp only [Reduction.byteSignPure, hk]; exact h`; likewise `Reduction.byteSign` from
`sign_eq_bytes`, and `keygen_eq_bytes S a b c` type-checks directly against `Reduction.byteKeygen`.

Component lemmas (same names as security/Link): `wotsPkGen_eq`, `xmssNode_eq`, `wotsSign_eq`,
`xmssSign_eq`, `forsSkGen_eq`, `forsNode_eq`, `forsSign_eq`, `htSign_eq`:

    theorem htSign_eq (msg sk pk : S.Node) (parts : DigestParts S.vp.params) :
        htBytes S (GeneralHypertree.sign S.vp S.prims msg sk pk parts) =
          Spec.htSign S.spec (nd msg) (nd sk) (nd pk) parts.idxTree.val parts.idxLeaf.val

## Things checked rather than assumed — no Spec/VCVio discrepancy found for any set
- Digest split in signing: via B's `splitDigest_md/_tree/_leaf` (generic, includes 256f's 8 tree
  bytes / 64-bit index and the sets with k·a not a multiple of 8) and `forsAdrs_dom`.
- `htSign` stepping: VCVio's `LayerPosition.next` (`tree / 2^h'`, low `h'` bits as next leaf) equals
  the spec's `tree >>> hp`, `tree % 2^hp` for symbolic `hp` (`S.hp_eq`); number of layers `d`
  (`S.d_eq`); every position is in `BaseDom` (`layerPosition_baseDom`: layer < d < 256,
  tree < 2^((d−1)·h') ≤ 2^64).
- Top-layer key-generation address `(d − 1, 0)`: `topLayer_baseDom`.
- FORS: leaf/secret index `i·2^a + idx < k·2^a ≤ 2^32`, node index at height z `< k·2^(a−z)`,
  heights `≤ a ≤ 14`; sibling formula `fors_sib` for symbolic `a`.
- WOTS: chain index `< len < 2^32`, steps `< w = 16`; `T_len` only at `len ≠ 1`
  (`Sha2Set.len_ne_one`); XMSS leaves `< 2^h' ≤ 2^9`.
- Secret key = four `n`-byte blocks for n ∈ {16,24,32} (`skBytes_block`, via `block_nds`).
- Context encoding `0x00 ‖ |ctx| ‖ ctx ‖ M` = `External.encodePureMessage` (`cv_withContext`);
  over-long context: `none` on both sides.

## Not done / caveats
- Nothing left open.
