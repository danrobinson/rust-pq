# Package B (VERIFY) — status

## Interface notes (read first, package C)
Interface published (`status/B-interface.ok`); statements below are final.
Differences from the mechanical substitution of security/Link (all forced, none weakening):

1. `decodeSig S`, `decodePk S` are *defined* as `SLHDSA.decodeSignature S.vp (sha2WireCodec S.vp.params)`
   / `decodePublicKey (sha2WireCodec S.vp.params)` (result types at `S.prims.core`), not literally as
   `decodeApprovedSignature S.fips`: for a variable `S`, `approvedPrimitives S.fips` is not
   definitionally `S.prims` (only propositionally, `Sha2Set.prims_eq_approved`), so the literal
   definition does not type-check against `GeneralScheme.verifyInternal S.vp S.prims`.
   `decodeSig_eq_approved : HEq (decodeSig S) (decodeApprovedSignature S.fips)` (same for `decodePk`),
   and at each concrete set the equality is `rfl` (twelve `example`s in Verify.lean).
   Likewise `encodeSig S`, `encodePk S` (new abbrevs) replace `encodeApprovedSignature S128`,
   `encodeApprovedPublicKey S128` in `sp_encodeSignature`, `sp_encodePublicKey`
   (`encodeSig_eq_approved`, `encodePk_eq_approved`).
2. Lengths: `sigBytes_length : (sigBytes S s).length = S.spec.sigBytes`, public key `2 * S.spec.n`,
   `forsIdx_eq`/`forsPkFromSig_eq` take `md.length = S.vp.params.digestBytes` (= `S.spec.mdBytes`,
   `Sha2Set.digestBytes_eq`), `xmssPkFromSig_eq` takes `idx < 2 ^ S.vp.params.hp`.
3. `nds_length {n} (l : List (Bytes n)) : (nds l).length = n * l.length` (Climb.lean; old Fors
   version had `16 * l.length`); `nds_length'` (Verify.lean, simp) is `ys.length * n`.
   `nds_ofFn`, `block_nds`, `nds_cons` live in Climb.lean (one copy each).
4. `wotsChain_dom` takes `i < 2 ^ 32`, `j < 2 ^ 32` (was `i < 35`, `j < 16`);
   `fors_parity (a i idx j) (hj : j < a)` has the height as an explicit argument;
   `forsBytes_drop` drops `i * ((S.vp.params.a + 1) * S.vp.params.n)`;
   `specChain_word3`, `checksum_foldl` take the parameter set / `w` explicitly;
   `htStep S`, `specHtRoot S`, `htGo S` take `S`; `specForsAdrs` is parameter-independent.
5. All former `private` helpers are public. New public helpers: `Sha2Set.len_ne_one`, `len_lt`,
   `len1_mul_lgw`, `spec_w`, `spec_len`, `hp_le`, `a_le`, `k_ne_one`, `fors_leaves_le`, `ka_le`,
   `layers_le`, `xmssSigBytes_eq`, `forsSigBytes_eq`, `m_split`; `forsTree_length`, `forsLeaf_lt`,
   `layerPosition_baseDom`, `forsAdrs_dom`, `splitDigest_md/_tree/_leaf`, `pkBytes_length`.

## Result (final)
`lake build MLink.Verify` green; no `sorry`/`axiom`/`native_decide`/`bv_decide` in
MLink/{Climb,Wots,Xmss,Fors,Hypertree,Verify}.lean; `#print axioms` of every headline is
`[propext, Classical.choice, Quot.sound]` (with package A's finished Hash.lean).
One proof generic over `S : Sha2Set`; no per-set case split except small numeric lemmas
(`cases S <;> decide`). No statement changed after the interface was published.

Main theorems (MLink/Verify.lean, `variable (S : Sha2Set)`):

    theorem verify_eq_typed (msg : Spec.Bytes) (s : GeneralScheme.SignatureCore S.vp S.prims.core)
        (k : PublicKeyCore S.prims.core) :
        Spec.slhVerifyInternal S.spec msg (sigBytes S s) (pkBytes S k) =
          GeneralScheme.verifyInternal S.vp S.prims (cv msg) s k

    theorem verify_eq (msg sig pk : Spec.Bytes) (hp : pk.length = 2 * S.spec.n) :
        Spec.slhVerifyInternal S.spec msg sig pk =
          match decodeSig S (cv sig), decodePk S (cv pk) with
          | .ok s, .ok k => GeneralScheme.verifyInternal S.vp S.prims (cv msg) s k
          | _, _ => false

    theorem verify_eq' (msg sig pk : Spec.Bytes) (hs : sig.length = S.spec.sigBytes)
        (hp : pk.length = 2 * S.spec.n) :
        ∃ s k, decodeSig S (cv sig) = .ok s ∧ decodePk S (cv pk) = .ok k ∧
          Spec.slhVerifyInternal S.spec msg sig pk =
            GeneralScheme.verifyInternal S.vp S.prims (cv msg) s k

    theorem slhVerify_eq (msg sig ctx pk : Spec.Bytes) (hp : pk.length = 2 * S.spec.n) :
        Spec.slhVerify S.spec msg sig ctx pk =
          match decodeSig S (cv sig), decodePk S (cv pk) with
          | .ok s, .ok k => External.verifyPure S.vp S.prims (cv msg) s (cv ctx) k
          | _, _ => false

plus `decodeSig_ok/_error`, `decodePk_ok`, `sp_encodeSignature`, `sp_encodePublicKey`,
`sigBytes_length`, `pkBytes_length`, `root_eq`, and the component lemmas `climb_eq`, `chain_eq`,
`wotsDigits_eq`, `wotsPkFromSig_eq`, `xmssPkFromSig_eq`, `forsIdx_eq`, `forsPkFromSig_eq`,
`recover_eq`.

## Things checked rather than assumed — no Spec/VCVio discrepancy found for any set
- WOTS digits (`wotsDigits_eq`): `Spec.wotsDigits` and VCVio's `WotsEncoding.fullDigits` have the
  same shape (shift `(8 − len2·lgw mod 8) mod 8`, width `⌈len2·lgw/8⌉`), so the proof is generic
  given `lgw_eq`, `len1_eq`, `len2_eq` (Nat.log vs Nat.log2, both 3), `w_eq` and
  `len1·lgw = 8n`. No dependence on Hash.lean (axioms `propext, Quot.sound`).
- `T_l` only at lengths `len ∈ {35,51,67}` (`Sha2Set.len_ne_one`) and `k ∈ {14,33,17,33,22,35}`
  (`Sha2Set.k_ne_one`), so the `ys.length ≠ 1` hypothesis of `Tl_eq` is always met.
- Digest split (`splitDigest_md/_tree/_leaf`): VCVio `digestBytes/treeIdxBytes/leafIdxBytes` and
  masks `2^(h−h')`, `2^h'` equal Spec's `mdBytes/treeBytes/leafBytes`, `2^(h − h/d)`, `2^(h/d)` on
  every set (including 256f: 8 tree bytes, mask 2^64; sets with k·a not a multiple of 8 —
  `forsIdx_eq` only needs `k·a ≤ 8·⌈k·a/8⌉`, `Sha2Set.ka_le`).
- Address domains: layer `< d < 256`; tree `< 2^((d−1−layer)·h') ≤ 2^64` (`Sha2Set.layers_le`,
  `layerPosition_baseDom`); digest tree index `< 2^(h−h') ≤ 2^64`, leaf `< 2^h' ≤ 2^9`
  (`forsAdrs_dom`); WOTS chain index `< len < 2^32`, hash index `< 16`; FORS leaf index
  `i·2^a + idx < k·2^a ≤ 2^32` (`Sha2Set.fors_leaves_le`, `forsLeaf_lt`), heights `≤ a ≤ 14`.

## Not done / caveats
- Nothing left open. The only deviation from the literal old statements is item 1 above
  (`decodeSig`/`decodePk`/`encodeSig`/`encodePk` typed at `S.prims` with `HEq`/`rfl` links to the
  `…Approved… S.fips` functions).
- Lemmas added outside the six old-file inventories are all in my own files (listed in item 5).
