#!/usr/bin/env python3
"""Generator of ME2E/Api/Sha2_<set>.lean and ME2E/Rom/Sha2_<set>.lean (six sets each).
Not part of the build; run from anywhere:  python3 -I security/scripts/gen_api_rom.py

Statements are taken textually from the single-set tree (git commit 26aa3d8: security/E2E/Api.lean, External.lean,
Main.lean, PureRom.lean, PureRomBytes.lean, all SHA2-128s) and transformed by `tr`: Rust function
names (`slhdsa.slh.slh_*` -> `slhdsa.sets.sha2_<set>.slh_*`, `slhdsa.api.*` ->
`slhdsa.sets.sha2_<set>.*`), array sizes (16/32/48/64 -> n/2n/3n/4n), `Room` slacks (152/409 for
n = 16, 304/561 otherwise, as in lean/Slhdsa/Theorems.lean), `vp`/`prims`/codec/`node`/
`secretKey`/`Link.decode*`/`*Bytes` spelled at the set, `Spec.KeyOk` at the set, `len`, `k`,
`256 ^ n`, the forger variable `S` -> `F`.  `check128s` asserts that undoing these renamings on
the generated 128s statements gives back the single-set statements character for character.
Proofs are written here (one-line instances of ME2E/Api.lean, ME2E/PureRom.lean and the
lean/ theorems).
"""
import re, os
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)                      # security/
# The single-set tree (SLH-DSA-SHA2-128s only), whose statements are the templates, is git commit
# 26aa3d8 of this repository; its files are read with `git show` (SLHDSA_REPO overrides the
# repository, for runs on a copy of the tree).
import subprocess
def old_file(rel):
    repo = os.environ.get('SLHDSA_REPO') or os.path.dirname(ROOT)
    return subprocess.run(['git', '-C', repo, 'show', '26aa3d8:' + rel],
                          check=True, capture_output=True, text=True).stdout
SRC = {f: old_file('security/E2E/' + f + '.lean')
       for f in ['Api', 'External', 'Main', 'PureRom', 'PureRomBytes']}
# name, ctor, n, k
SETS = [('128s', 's128s', 16, 14), ('128f', 's128f', 16, 33), ('192s', 's192s', 24, 17),
        ('192f', 's192f', 24, 33), ('256s', 's256s', 32, 22), ('256f', 's256f', 32, 35)]


def rooms(n):
    return (152, 409) if n == 16 else (304, 561)


def stmt(f, nm):
    m = re.search(r'^theorem ' + nm + r'\b(.*?) :=(?: by| rfl)?\n', SRC[f], re.S | re.M)
    assert m, nm
    return m.group(1)


def struct(f, nm):
    m = re.search(r'^structure ' + nm + r'\b(.*?)\n\n', SRC[f], re.S | re.M)
    assert m, nm
    return m.group(1)


def tr(b, name, ctor, n, k):
    ri, rp = rooms(n)
    b = re.sub(r'\bS\b', 'F', b)
    b = b.replace('slhdsa.slh.slh_', 'slhdsa.sets.sha2_%s.slh_' % name)
    b = b.replace('slhdsa.api.', 'slhdsa.sets.sha2_%s.' % name)
    b = re.sub(r'Array U8 (16|32|48|64)#usize',
               lambda mm: 'Array U8 %d#usize' % (int(mm.group(1)) // 16 * n), b)
    b = b.replace('Room m.length 152', 'Room m.length %d' % ri).replace('Room m.length 409', 'Room m.length %d' % rp)
    b = b.replace('(vp := vp)', '(vp := §.vp)')
    b = re.sub(r'(?<![.\w§])vp\b(?! :=)', '§.vp', b)
    b = re.sub(r'(?<![.\w])prims\b', '§.prims', b)
    b = b.replace('codec128s', '(codec §)')
    b = re.sub(r'\(node (\w+)\)', r'(node § \1)', b)
    b = b.replace('(secretKey sk)', '(secretKey § sk)')
    b = b.replace('Link.decodePk ', 'MLink.decodePk § ').replace('Link.decodeSig ', 'MLink.decodeSig § ')
    b = b.replace('skBytes (', 'MLink.skBytes § (').replace('pkBytes (', 'MLink.pkBytes § (')
    b = b.replace('.map sigBytes', '.map (MLink.sigBytes §)')
    b = b.replace('Spec.KeyOk (', 'Spec.KeyOk Spec.sha2_%s (' % name)
    b = b.replace('pureRomScheme optRand', 'pureRomScheme § optRand')
    b = b.replace('pureBytesRomScheme optRand', 'pureBytesRomScheme § optRand')
    b = b.replace('(256 ^ 16)', '(256 ^ %d)' % n)
    b = b.replace('bTcrArM 35 ', 'bTcrArM %d ' % (2 * n + 3)).replace('bTcrArM 14 ', 'bTcrArM %d ' % k)
    return b.replace('§', 'Sha2Set.' + ctor)


def untr128(u):
    u = u.replace('slhdsa.sets.sha2_128s.slh_', 'slhdsa.slh.slh_').replace('slhdsa.sets.sha2_128s.', 'slhdsa.api.')
    u = u.replace('(codec Sha2Set.s128s)', 'codec128s').replace('node Sha2Set.s128s ', 'node ')
    u = u.replace('secretKey Sha2Set.s128s ', 'secretKey ')
    u = u.replace('MLink.decodePk Sha2Set.s128s ', 'Link.decodePk ').replace('MLink.decodeSig Sha2Set.s128s ', 'Link.decodeSig ')
    u = u.replace('MLink.skBytes Sha2Set.s128s ', 'skBytes ').replace('MLink.pkBytes Sha2Set.s128s ', 'pkBytes ')
    u = u.replace('(MLink.sigBytes Sha2Set.s128s)', 'sigBytes')
    u = u.replace('Spec.KeyOk Spec.sha2_128s ', 'Spec.KeyOk ')
    u = u.replace('pureRomScheme Sha2Set.s128s ', 'pureRomScheme ').replace('pureBytesRomScheme Sha2Set.s128s ', 'pureBytesRomScheme ')
    return u.replace('Sha2Set.s128s.', '')


# (file of the single-set statement, name); order = order in the generated file
API_THMS = [('Api', 'api_sign_eq'), ('Api', 'api_verify_eq'), ('Api', 'api_keygen_eq'),
            ('Api', 'api_sign_deterministic_eq'), ('Api', 'api_keygen_bytes'), ('Api', 'api_sign_bytes'),
            ('Api', 'api_sign_deterministic_bytes'), ('Api', 'api_verify_bytes'), ('Api', 'api_pure_cores')]
TYPED_THMS = [('Main', 'rust_keygen'), ('Main', 'rust_sign'), ('Main', 'rust_verify')]
SEC_THMS = [('Api', 'api_pure_security'), ('Api', 'api_pure_security_linear')]
CHK_THMS = [('Api', 'api_sign_checked_eq_sign'), ('Api', 'api_sign_deterministic_checked_eq'),
            ('Api', 'api_keygen_checked_eq'), ('Api', 'keygen_internal_checked_eq'),
            ('Api', 'api_sign_checked_bytes'), ('Api', 'api_sign_deterministic_checked_bytes'),
            ('Api', 'api_checked_pure_cores')]
ROM_THMS = [('PureRom', 'pure_rom_security'), ('PureRom', 'api_pure_rom_security'),
            ('PureRomBytes', 'rust_pure_rom_security_bytes'), ('PureRomBytes', 'api_pure_rom_security_bytes')]
STRUCTS = [('Api', 'ApiPureBytesEndToEnd'), ('External', 'PureEndToEnd'), ('Api', 'ApiPureEndToEnd')]


def check128s():
    for f, nm in API_THMS + TYPED_THMS + SEC_THMS + CHK_THMS + ROM_THMS:
        g = tr(stmt(f, nm), '128s', 's128s', 16, 14)
        assert untr128(g) == re.sub(r'\bS\b', 'F', stmt(f, nm)), nm
    for f, nm in STRUCTS:
        g = tr(struct(f, nm), '128s', 's128s', 16, 14)
        assert untr128(g) == struct(f, nm), nm


check128s()


def proofs(P):
    s = P['set']
    L = 'slhdsa.sha2_%s.' % s
    R = 'slhdsa.sets.sha2_%s.' % s
    se = P['se']
    sp = 'Spec.sha2_%s' % s
    hN = '(show (%d#usize : Usize).val = %s.n by rfl)' % (P['n'], sp)
    return {
        'api_sign_eq': ' := by\n  unfold %ssign %sslh_sign slhdsa.api.sign; rfl' % (R, R),
        'api_verify_eq': ' :=\n  %sverify_eq m sig ctx pk' % L,
        'api_keygen_eq': ''' := by
  obtain ⟨sk', pk', h1, e1⟩ := %(L)sapi_keygen_correct seeds sk0 pk0
  obtain ⟨sk, pk, h2, e2⟩ := %(L)skeygen_correct sk_seed sk_prf pk_seed
  obtain ⟨b0, b1, b2⟩ := block_seeds %(sp)s %(hN)s seeds sk_seed sk_prf pk_seed hs
  rw [b0, b1, b2, ← e2, Prod.mk.injEq] at e1
  rw [h1, h2]
  congr 2
  · exact Aeneas.Std.Array.ext _ _ (slhdsa.ht_bytes_injective e1.1)
  · exact Aeneas.Std.Array.ext _ _ (slhdsa.ht_bytes_injective e1.2)''' % dict(L=L, sp=sp, hN=hN),
        'api_sign_deterministic_eq': ''' := by
  obtain ⟨r, h1, e1, -⟩ := %(L)sapi_sign_deterministic_correct m ctx sk hm
  obtain ⟨r', h2, e2⟩ := %(L)ssign_correct m ctx sk pk_seed hm
  rw [block_sk_pkSeed %(sp)s %(hN)s sk sk_seed sk_prf pk_seed pk_root hsk, ← e2] at e1
  rw [h1, h2, optVec_eq e1]''' % dict(L=L, sp=sp, hN=hN),
        'api_keygen_bytes': ''' := by
  rw [api_keygen_eq seeds sk0 pk0 sk_seed sk_prf pk_seed hs]
  exact rust_keygen_bytes sk_seed sk_prf pk_seed''',
        'api_sign_bytes': ''' := by
  rw [api_sign_eq]
  exact rust_sign_bytes m ctx sk addrnd hm''',
        'api_sign_deterministic_bytes': ''' := by
  rw [api_sign_deterministic_eq m ctx sk sk_seed sk_prf pk_seed pk_root hsk hm]
  exact rust_sign_bytes m ctx sk pk_seed hm''',
        'api_verify_bytes': ''' := by
  rw [api_verify_eq]
  exact rust_verify_bytes m sig ctx pk hm''',
        'api_pure_cores': ' :=\n  ⟨api_keygen_bytes, api_sign_bytes, api_sign_deterministic_bytes, api_verify_bytes⟩',
        'rust_keygen': ''' := by
  obtain ⟨sk, pk, h, hp⟩ := %(L)skeygen_correct sk_seed sk_prf pk_seed
  exact ⟨sk, pk, h, keygen_typed %(se)s rfl sk_seed sk_prf pk_seed sk.val pk.val hp⟩''' % dict(L=L, se=se),
        'rust_sign': ''' := by
  obtain ⟨r, h, hp⟩ := %(L)ssign_correct m ctx sk addrnd hm
  refine ⟨r, h, ?_⟩
  have e := signPure_typed %(se)s rfl rfl m.val ctx.val sk addrnd (r.map fun v => v.val)
    (by rw [Option.map_map]; exact hp)
  rw [Option.map_map] at e
  exact e''' % dict(L=L, se=se),
        'rust_verify': ''' := by
  rw [%(L)sverify_correct m sig ctx pk hm, show %(sp)s = %(se)s.spec from rfl,
    verifyPure_typed %(se)s m.val sig.val ctx.val pk.val pk.property]
  cases MLink.decodeSig %(se)s (cv (bytes sig.val)) <;> cases MLink.decodePk %(se)s (cv (bytes pk.val)) <;>
    rfl''' % dict(L=L, se=se, sp=sp),
        'api_pure_security': ' :=\n  ⟨api_pure_cores, (rust_pure_security optRand pkSeedDist).2⟩',
        'api_pure_security_linear': ' :=\n  ⟨api_pure_cores, (rust_pure_security_linear optRand pkSeedDist).2⟩',
        'api_sign_checked_eq_sign': ''' := by
  obtain ⟨r1, h1, e1⟩ := slhdsa.spec_imp_exists (%(L)ssign_checked_spec m ctx sk addrnd hm)
  obtain ⟨r2, h2, e2⟩ := %(L)sapi_sign_correct m ctx sk addrnd hm
  rw [spec_slhSignChecked_eq %(sp)s %(sp)s_valid _ _ _ _ hk, ← e2] at e1
  have heq : %(R)ssign_checked m ctx sk addrnd = %(R)ssign m ctx sk addrnd := by
    rw [h1, h2, optVec_eq e1]
  refine ⟨heq, fun hc => ?_, fun hc => ?_⟩
  · rw [← heq]
    exact %(L)sapi_sign_checked_complete m ctx sk addrnd hm hc hk
  · rw [slhSign_tooLong %(sp)s _ ctx _ _ hc, Option.map_eq_none_iff] at e2
    rw [h2, e2]''' % dict(L=L, R=R, sp=sp),
        'api_sign_deterministic_checked_eq': ''' := by
  obtain ⟨r1, h1, e1⟩ :=
    slhdsa.spec_imp_exists (%(L)ssign_deterministic_checked_spec m ctx sk hm)
  obtain ⟨r2, h2, e2, -⟩ := %(L)sapi_sign_deterministic_correct m ctx sk hm
  rw [spec_slhSignChecked_eq %(sp)s %(sp)s_valid _ _ _ _ hk, ← e2] at e1
  have heq : %(R)ssign_deterministic_checked m ctx sk =
      %(R)ssign_deterministic m ctx sk := by
    rw [h1, h2, optVec_eq e1]
  refine ⟨heq, fun hc => ?_, fun hc => ?_⟩
  · rw [← heq]
    exact %(L)sapi_sign_deterministic_checked_complete m ctx sk hm hc hk
  · rw [slhSign_tooLong %(sp)s _ ctx _ _ hc, Option.map_eq_none_iff] at e2
    rw [h2, e2]''' % dict(L=L, R=R, sp=sp),
        'api_keygen_checked_eq': ''' := by
  have hk := (%(L)sapi_keygen_keyOk seeds sk0 pk0 sk pk hkg).1
  exact fun m ctx addrnd hm =>
    ⟨api_sign_checked_eq_sign m ctx sk addrnd hm hk, api_sign_deterministic_checked_eq m ctx sk hm hk⟩''' % dict(L=L),
        'keygen_internal_checked_eq': ''' := by
  have hk := (%(L)skeygen_keyOk sk_seed sk_prf pk_seed sk pk hkg).1
  exact fun m ctx addrnd hm =>
    ⟨api_sign_checked_eq_sign m ctx sk addrnd hm hk, api_sign_deterministic_checked_eq m ctx sk hm hk⟩''' % dict(L=L),
        'api_sign_checked_bytes': ''' := by
  rw [(api_sign_checked_eq_sign m ctx sk addrnd hm hk).1]
  exact api_sign_bytes m ctx sk addrnd hm''',
        'api_sign_deterministic_checked_bytes': ''' := by
  rw [(api_sign_deterministic_checked_eq m ctx sk hm hk).1]
  exact api_sign_deterministic_bytes m ctx sk sk_seed sk_prf pk_seed pk_root hsk hm''',
        'api_checked_pure_cores': ' :=\n  ⟨api_sign_checked_bytes, api_sign_deterministic_checked_bytes⟩',
        'pure_rom_security': ''' :=
  ⟨pure_end_to_end optRand pkSeedDist, pureRomScheme_instantiation %(se)s optRand pkSeedDist,
    fun F _ _ hF => pure_security_sha2 %(se)s optRand pkSeedDist F hF,
    fun A _ _ hA => pure_security_sha2_euf %(se)s optRand pkSeedDist A hA⟩''' % dict(se=se),
        'api_pure_rom_security': ' :=\n  ⟨api_pure_end_to_end optRand pkSeedDist, (pure_rom_security optRand pkSeedDist).2⟩',
        'rust_pure_rom_security_bytes': ''' :=
  ⟨⟨rust_keygen_bytes, rust_sign_bytes, rust_verify_bytes⟩,
    pureBytesRomScheme_instantiation %(se)s optRand pkSeedDist,
    fun F _ _ hF => pure_bytes_security_sha2 %(se)s optRand pkSeedDist F hF,
    fun A _ _ hA => pure_bytes_security_sha2_euf %(se)s optRand pkSeedDist A hA⟩''' % dict(se=se),
        'api_pure_rom_security_bytes': ''' :=
  ⟨api_pure_bytes_end_to_end optRand pkSeedDist,
    (rust_pure_rom_security_bytes optRand pkSeedDist).2⟩''',
    }


STRUCT_PROOFS = {
    'ApiPureBytesEndToEnd': '''/-- `ApiPureBytesEndToEnd` holds for every `opt_rand` source and every `PK.seed` distribution. -/
theorem api_pure_bytes_end_to_end (optRand : PublicKeyCore %(se)s.prims.core → ProbComp %(se)s.prims.Y)
    (pkSeedDist : ProbComp %(se)s.prims.PkSeed) : ApiPureBytesEndToEnd optRand pkSeedDist :=
  have h := pure_bytes_scheme %(se)s optRand pkSeedDist
  { keygen_alg := h.keygen_alg
    keygen := api_keygen_bytes
    sign_alg := h.sign_alg
    sign_alg_tooLong := h.sign_alg_tooLong
    sign := api_sign_bytes
    sign_deterministic := api_sign_deterministic_bytes
    verify_alg := h.verify_alg
    verify := api_verify_bytes
    correct := h.correct }
''',
    'PureEndToEnd': '''/-- `PureEndToEnd` holds for every `opt_rand` source and every `PK.seed` distribution. -/
theorem pure_end_to_end (optRand : PublicKeyCore %(se)s.prims.core → ProbComp %(se)s.prims.Y)
    (pkSeedDist : ProbComp %(se)s.prims.PkSeed) : PureEndToEnd optRand pkSeedDist where
  keygen_alg := rfl
  keygen := rust_keygen
  sign_alg := fun pk sk message context h =>
    Reduction.externalAlg_sign %(se)s.vp %(se)s.prims optRand pkSeedDist pk sk message context h
  sign_alg_tooLong := fun pk sk message context h =>
    Reduction.externalAlg_sign_tooLong %(se)s.vp %(se)s.prims optRand pkSeedDist pk sk message context h
  sign := rust_sign
  verify := fun m sig ctx pk hm => by
    refine ⟨_, rust_verify m sig ctx pk hm, ?_⟩
    split
    · rename_i s k hs hk
      exact Reduction.externalAlg_verify_ok %(se)s.vp %(se)s.prims optRand pkSeedDist k _ _ s
    · simp_all
  correct := fun message context hc skSeed skPrf pkSeed addrnd =>
    Reduction.externalAlg_correct %(se)s.vp %(se)s.prims optRand pkSeedDist message context hc skSeed
      skPrf pkSeed addrnd
''',
    'ApiPureEndToEnd': '''/-- `ApiPureEndToEnd` holds for every `opt_rand` source and every `PK.seed` distribution. -/
theorem api_pure_end_to_end (optRand : PublicKeyCore %(se)s.prims.core → ProbComp %(se)s.prims.Y)
    (pkSeedDist : ProbComp %(se)s.prims.PkSeed) : ApiPureEndToEnd optRand pkSeedDist :=
  have h := pure_end_to_end optRand pkSeedDist
  { keygen_alg := h.keygen_alg
    keygen := fun seeds sk0 pk0 a b c hs => by
      rw [api_keygen_eq seeds sk0 pk0 a b c hs]
      exact rust_keygen a b c
    sign_alg := h.sign_alg
    sign_alg_tooLong := h.sign_alg_tooLong
    sign := fun m ctx sk addrnd hm => by
      rw [api_sign_eq]
      exact rust_sign m ctx sk addrnd hm
    sign_deterministic := fun m ctx sk a b c d hsk hm => by
      rw [api_sign_deterministic_eq m ctx sk a b c d hsk hm]
      exact rust_sign m ctx sk c hm
    verify := fun m sig ctx pk hm => by
      rw [api_verify_eq]
      exact h.verify m sig ctx pk hm
    correct := h.correct }
''',
}

DOC = {
    'api_sign_eq': '`sets::sha2_%(set)s::sign` is `sets::sha2_%(set)s::slh_sign` (both call `slh::slh_sign` on the key slice).',
    'api_verify_eq': '`sets::sha2_%(set)s::verify` is `sets::sha2_%(set)s::slh_verify`.',
    'api_keygen_eq': '**`keygen` is `slh_keygen_internal` on the three blocks of `seeds`**: for `seeds = SK.seed ‖ SK.prf ‖ PK.seed`, `keygen seeds sk0 pk0` returns the same pair of arrays as `slh_keygen_internal SK.seed SK.prf PK.seed`, whatever the buffers `sk0`, `pk0` held.',
    'api_sign_deterministic_eq': '**`sign_deterministic` is `slh_sign` with `addrnd := PK.seed`**: for `sk = SK.seed ‖ SK.prf ‖ PK.seed ‖ PK.root`, `sign_deterministic m ctx sk` returns the same as `slh_sign m ctx sk PK.seed`.',
    'api_keygen_bytes': '**Rust `keygen` = `byteKeygen`** on the three %(n)d-byte blocks of `seeds` (the buffers `sk0`, `pk0` are irrelevant).',
    'api_sign_bytes': '**Rust `sign` = `byteSignPure`** (FIPS 205 Alg. 22 with caller-supplied `addrnd`), pointwise.',
    'api_sign_deterministic_bytes': '**Rust `sign_deterministic` = `byteSignPure` with `addrnd := PK.seed`** (block 2 of the key read as a node; FIPS 205\'s deterministic variant).',
    'api_verify_bytes': '**Rust `verify` = `byteVerifyPure`** (FIPS 205 Alg. 24), pointwise.',
    'api_pure_cores': '**The interface functions are the deterministic cores of the byte-level external pure scheme** `Reduction.pureBytesAlg`: part (a) of `rust_pure_security` for `keygen`, `sign`, `sign_deterministic`, `verify`.',
    'rust_keygen': '**Rust `slh_keygen_internal` = VCVio\'s `keygenInternal`** (typed form): the Rust keys are the FIPS encodings of the key pair computed from the seeds read as nodes.',
    'rust_sign': '**Rust `slh_sign` = VCVio\'s `External.signPureWithRandomizer`** (typed form; `secretKey` reads the %(n4)d-byte key as a typed key, `skBytes_secretKey`): `none` exactly for VCVio\'s error value.',
    'rust_verify': '**Rust `slh_verify` = VCVio\'s `External.verifyPure`** on the values of VCVio\'s strict decoders (typed form).',
    'api_pure_security': '''**The Rust interface (`sets::sha2_%(set)s::{keygen, sign, sign_deterministic, verify}`) and the standard-model security of the scheme it computes (SLH-DSA-SHA2-%(set)s, external pure interface, FIPS 205 Alg. 21/22/24).**

`rust_pure_security` with part (a) about the interface functions: `keygen` (on the three %(n)d-byte blocks `SK.seed ‖ SK.prf ‖ PK.seed` of its %(n3)d-byte argument), `sign`, `sign_deterministic` (with `addrnd` the `PK.seed` block of the key) and `verify` never panic and are pointwise equal to `byteKeygen`, `byteSignPure`, `byteVerifyPure` under `Room m.length %(rp)d`.  Parts (b), (c) are those of `rust_pure_security`, unchanged, and so is the list (i)–(vi) of what lies between the scheme and the Rust code, with these additions: (i) `keygen` takes the three seeds as one %(n3)d-byte string (the caller samples it); a signing oracle served by `sign_deterministic` is the scheme at `optRand pk = pure pk.pkSeed` (`rust_pure_security_deterministic` for the uniform-`PK.seed` bound), using the `PK.seed` held in the *secret* key, which in the games is the one in the public key.''',
    'api_pure_security_linear': '**`api_pure_security` in linear (signed-pair) form** (legend: `rust_security_linear`).',
    'api_sign_checked_eq_sign': '**On a well-formed private key the checked hedged signer is the plain one**: `sign_checked` returns exactly what `sign` returns — `ok (some sig)` with the same `sig` for a context of at most 255 bytes, `ok none` for a longer one.  So a signing oracle served by `sign_checked` with a key satisfying `Spec.KeyOk` is the signing oracle served by `sign`.',
    'api_sign_deterministic_checked_eq': '**On a well-formed private key the checked deterministic signer is the plain one.**',
    'api_keygen_checked_eq': '**With a key written by `keygen`, the checked signers are the plain signers**, on every message under the `Room` bound, every context and every `addrnd`.',
    'keygen_internal_checked_eq': 'The same for a key written by `slh_keygen_internal`.',
    'api_sign_checked_bytes': '**Rust `sign_checked` = `byteSignPure` on well-formed keys.**',
    'api_sign_deterministic_checked_bytes': '**Rust `sign_deterministic_checked` = `byteSignPure` with `addrnd := PK.seed` on well-formed keys.**',
    'api_checked_pure_cores': '**The signing items of part (a), for the checked signers, on well-formed keys** (in particular every key written by `keygen`, `slhdsa.sha2_%(set)s.api_keygen_keyOk`).',
    'pure_rom_security': '''**The Rust external pure interface and its security in the random-oracle model (SLH-DSA-SHA2-%(set)s).**

1. `PureEndToEnd optRand pkSeedDist`: the Rust `slh_keygen_internal`, `slh_sign`, `slh_verify` never panic and compute the deterministic cores of `X = Reduction.externalAlg %(se)s.vp %(se)s.prims optRand pkSeedDist` on the FIPS byte encodings (under `Room m.length %(rp)d`), and `X` is correct.
2. `X` is `R = pureRomScheme %(se)s optRand pkSeedDist` with its three oracles answered by the SHA-2 functions of the set (`romAnswer`).
3. SUF-CMA: every strong forger against `R` with at most `qh` hash and `qs` signing queries has advantage at most `securityBound %(se)s.vp.params (256 ^ %(n)d) 2 1 qh qs` when the three oracles are independent random oracles (`ProbCompRuntime.rom`): VCVio's internal bound (`MLink.security_sha2`) at the same `qh`, `qs`.
4. EUF-CMA: the same for every chosen-message forger.

Nothing transfers the bound from `R` to `X` (the SHA-2 instantiation); that step is the random-oracle methodology.  The Rust code computes only the deterministic cores; sampling the seeds and `addrnd` is the caller's obligation.  Pure mode only.''',
    'api_pure_rom_security': '**The Rust interface and its security in the random-oracle model.**  `pure_rom_security` with `ApiPureEndToEnd` (the functions `keygen`, `sign`, `sign_deterministic`, `verify`) in place of `PureEndToEnd`.',
    'rust_pure_rom_security_bytes': '''**The Rust external pure interface and its random-oracle security, on byte strings (SLH-DSA-SHA2-%(set)s).**

(a) As in `rust_pure_security`: the Rust `slh_keygen_internal`, `slh_sign`, `slh_verify` never panic and are pointwise equal to `byteKeygen`, `byteSignPure`, `byteVerifyPure` (under `Room m.length %(rp)d`), the deterministic cores of `X = Reduction.pureBytesAlg %(se)s.vp %(se)s.prims (codec %(se)s) optRand pkSeedDist`.
(b) `X` is `pureBytesRomScheme %(se)s optRand pkSeedDist` with its three oracles answered by SHA-2.
(c) SUF-CMA, (d) EUF-CMA: every forger against `pureBytesRomScheme` making at most `qh` hash and `qs` signing queries has advantage at most `securityBound %(se)s.vp.params (256 ^ %(n)d) 2 1 qh qs`.

Not established: that the bound survives replacing the random oracles by SHA-2; sampling; pre-hash mode; side channels, the compiler, the Aeneas extraction.''',
    'api_pure_rom_security_bytes': '**The Rust interface and its random-oracle security, on byte strings.**  `rust_pure_rom_security_bytes` with part (a) replaced by `ApiPureBytesEndToEnd`.',
}
SDOC = {
    'ApiPureBytesEndToEnd': '**`PureBytesScheme` for the interface** (as the single-set `E2E/Api.lean`): the fields `keygen_alg`, `sign_alg`, `sign_alg_tooLong`, `verify_alg`, `correct` describe `X = pureBytesAlg …`; `keygen`, `sign`, `sign_deterministic`, `verify` say that the interface functions never panic and are pointwise equal to `byteKeygen`, `byteSignPure` (with `addrnd`, resp. with the `PK.seed` block of the key), `byteVerifyPure`.',
    'PureEndToEnd': '**The Rust external API computes the external pure scheme** `X = Reduction.externalAlg %(se)s.vp %(se)s.prims optRand pkSeedDist` (typed keys and signatures; as the single-set `E2E/External.lean`).',
    'ApiPureEndToEnd': '**`PureEndToEnd` for the interface**: `keygen` (on the three blocks of `seeds`), `sign`, `sign_deterministic` (randomness: the `PK.seed` block of the key) and `verify` in place of `slh_keygen_internal`, `slh_sign`, `slh_verify`.',
}

HDR_OPEN = '''namespace ME2E.sha2_%(set)s

open Aeneas Aeneas.Std Result
open SLHDSA SLHDSA.Concrete SLHDSA.Security OracleComp OracleSpec SignatureAlg ENNReal
open slhdsa (bytes Room)
open MLink (Sha2Set cv)
open MReduction (codec)
open Reduction (bPrfC bPrfWC sufCheck rUd rPre rTcrT toDspr toTcr toInternal bTcrArM externalAlg
  byteKeygen byteSign byteVerify byteSignPure byteVerifyPure bytesAlg pureBytesAlg bytesToTyped
  bytesToTypedS pureBytesToTyped prfRealPr prfIdealPr msgRealPr msgIdealPr)
open Reduction.Lazy (bPrfMsgL bPrfMsgWL bItsrL bOpenPreS bWotsS)
open TweakableHash
'''


def thm(nm, st, pf, P):
    return '/-- %s -/\ntheorem %s%s%s\n\n' % (DOC[nm] % P, nm, st, pf)


def gen(name, ctor, n, k):
    se = 'Sha2Set.' + ctor
    ri, rp = rooms(n)
    P = dict(set=name, se=se, n=n, n3=3 * n, n4=4 * n, ri=ri, rp=rp)
    pf = proofs(P)
    T = lambda f, nm: tr(stmt(f, nm), name, ctor, n, k)
    TS = lambda f, nm: tr(struct(f, nm), name, ctor, n, k)
    out = ['''import ME2E.Api
import ME2E.Sha2_%(set)s

/-!
# SLH-DSA-SHA2-%(set)s: the interface module `api`, the checked signers, typed end-to-end forms

GENERATED by `scripts/gen_api_rom.py` (statements: git `26aa3d8`'s `security/E2E/Api.lean`, `External.lean`,
`Main.lean` at SHA2-128s under the renamings listed there; proofs: `ME2E/Api.lean`,
`ME2E/Sha2_%(set)s.lean` and `lean/Slhdsa/{Theorems,ApiTheorems}.lean`).

Rust functions (Aeneas names `slhdsa.sets.sha2_%(set)s.*`, the per-set wrappers that the re-export
modules `sha2_%(set)s::api` and `sha2_%(set)s::encoding` expose): `keygen`, `sign`,
`sign_deterministic`, `verify`, `sign_checked`, `sign_deterministic_checked`, and the internal and
pure functions `slh_keygen_internal`, `slh_sign`, `slh_verify`.

1. **The interface functions are the scheme's cores**: `api_keygen_eq` (`keygen` = `slh_keygen_internal`
   on the three %(n)d-byte blocks of its %(n3)d-byte argument), `api_sign_eq`, `api_verify_eq`,
   `api_sign_deterministic_eq` (`addrnd` := block 2 of the key); `api_*_bytes`, `api_pure_cores`,
   `ApiPureBytesEndToEnd`; typed forms `rust_keygen`, `rust_sign`, `rust_verify`, `PureEndToEnd`,
   `ApiPureEndToEnd`.  `seeds_split`, `sk_split` (`ME2E/Api.lean`): the block hypotheses restrict
   nothing.
2. **Standard-model headlines for the interface**: `api_pure_security`, `api_pure_security_linear`
   (the bounds are those of `rust_pure_security`, `rust_pure_security_linear`).
3. **The checked signers on well-formed keys** (`Spec.KeyOk Spec.sha2_%(set)s`): `api_sign_checked_eq_sign`,
   `api_sign_deterministic_checked_eq`, `api_keygen_checked_eq`, `keygen_internal_checked_eq`,
   `api_sign_checked_bytes`, `api_sign_deterministic_checked_bytes`, `api_checked_pure_cores`.
-/

''' % P, HDR_OPEN % P, '\n/-! ### 1. The interface functions are the cores of the byte-level scheme -/\n\n']
    w = out.append
    for f, nm in API_THMS:
        w(thm(nm, T(f, nm), pf[nm], P))
    w('/-- %s -/\nstructure ApiPureBytesEndToEnd%s\n\n' % (SDOC['ApiPureBytesEndToEnd'] % P, TS('Api', 'ApiPureBytesEndToEnd')))
    w(STRUCT_PROOFS['ApiPureBytesEndToEnd'] % P + '\n')
    w('/-! ### Typed forms (`Reduction.externalAlg`) -/\n\n')
    for f, nm in TYPED_THMS:
        w(thm(nm, T(f, nm), pf[nm], P))
    w('/-- %s -/\nstructure PureEndToEnd%s\n\n' % (SDOC['PureEndToEnd'] % P, TS('External', 'PureEndToEnd')))
    w(STRUCT_PROOFS['PureEndToEnd'] % P + '\n')
    w('/-- %s -/\nstructure ApiPureEndToEnd%s\n\n' % (SDOC['ApiPureEndToEnd'] % P, TS('Api', 'ApiPureEndToEnd')))
    w(STRUCT_PROOFS['ApiPureEndToEnd'] % P + '\n')
    w('/-! ### 2. Headline forms for the interface -/\n\n')
    for f, nm in SEC_THMS:
        w(thm(nm, T(f, nm), pf[nm], P))
    w('/-! ### 3. The checked signers on well-formed keys -/\n\n')
    for f, nm in CHK_THMS:
        w(thm(nm, T(f, nm), pf[nm], P))
    w('end ME2E.sha2_%s\n\n' % name)
    names = [nm for _, nm in API_THMS] + ['api_pure_bytes_end_to_end'] + [nm for _, nm in TYPED_THMS] + \
        ['pure_end_to_end', 'api_pure_end_to_end'] + [nm for _, nm in SEC_THMS + CHK_THMS]
    for nm in names:
        w('#print axioms ME2E.sha2_%s.%s\n' % (name, nm))
    os.makedirs(os.path.join(ROOT, 'ME2E', 'Api'), exist_ok=True)
    open(os.path.join(ROOT, 'ME2E', 'Api', 'Sha2_%s.lean' % name), 'w').write(''.join(out))

    out = ['''import ME2E.Api.Sha2_%(set)s
import ME2E.PureRom

/-!
# SLH-DSA-SHA2-%(set)s: the random-oracle theorem for the context-string interface

GENERATED by `scripts/gen_api_rom.py` (statements: git `26aa3d8`'s `security/E2E/PureRom.lean`,
`PureRomBytes.lean` at SHA2-128s under the renamings listed there; proofs: `ME2E/PureRom.lean`).

* `pure_rom_security` (functions `slh_keygen_internal`, `slh_sign`, `slh_verify`; typed scheme
  `Reduction.externalAlg`), `api_pure_rom_security` (functions `keygen`, `sign`,
  `sign_deterministic`, `verify`);
* `rust_pure_rom_security_bytes`, `api_pure_rom_security_bytes`: the same on byte strings
  (`Reduction.pureBytesAlg`, the scheme of `rust_pure_security` / `api_pure_security`).

Bound: `securityBound %(se)s.vp.params (256 ^ %(n)d) 2 1 qh qs`, VCVio's internal bound
(`MLink.security_sha2 %(se)s`) at the same number `qh` of hash and `qs` of signing queries.
-/

''' % P, HDR_OPEN % P, '\n']
    w = out.append
    for f, nm in ROM_THMS:
        w(thm(nm, T(f, nm), pf[nm], P))
    w('end ME2E.sha2_%s\n\n' % name)
    for _, nm in ROM_THMS:
        w('#print axioms ME2E.sha2_%s.%s\n' % (name, nm))
    os.makedirs(os.path.join(ROOT, 'ME2E', 'Rom'), exist_ok=True)
    open(os.path.join(ROOT, 'ME2E', 'Rom', 'Sha2_%s.lean' % name), 'w').write(''.join(out))


for s in SETS:
    gen(*s)
open(os.path.join(ROOT, 'ME2E.lean'), 'w').write(
    'import ME2E.Basic\n' + ''.join('import ME2E.Sha2_%s\n' % s[0] for s in SETS) +
    'import ME2E.Api\nimport ME2E.PureRom\n' +
    ''.join('import ME2E.Api.Sha2_%s\n' % s[0] for s in SETS) +
    ''.join('import ME2E.Rom.Sha2_%s\n' % s[0] for s in SETS) +
    'import ME2E.Gen128s\n')
print('ok')
