#!/usr/bin/env python3
"""Generator of ME2E/Sha2_<set>.lean (six files).  Not part of the build.

The ten headline statements are taken textually from the single-set tree's security/E2E/Headline.lean
(SHA2-128s; git commit 26aa3d8) and
transformed by the substitutions in `tr` (Rust function names, array sizes, `Room` slacks,
`vp`/`prims`/codec, `len`, `k`, resource numerals).  `check128s` asserts that undoing the
substitutions on the generated 128s statements gives back the old statements (same `Room` slacks
152 / 409 as the old ones, since lean/ has them for n = 16), i.e. the 128s
statements have the shape of the old `E2E.*` modulo Rust function names and the
spelling of `vp`, `prims`, codec, `node`, forger variable.
Run: python3 ME2E/gen/gen.py   (from security/)
"""
import re, os
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
# The single-set tree (SLH-DSA-SHA2-128s only), whose statements are the templates, is git commit
# 26aa3d8 of this repository; its files are read with `git show` (SLHDSA_REPO overrides the
# repository, for runs on a copy of the tree).
import subprocess
def old_file(rel):
    repo = os.environ.get('SLHDSA_REPO') or os.path.dirname(ROOT)
    return subprocess.run(['git', '-C', repo, 'show', '26aa3d8:' + rel],
                          check=True, capture_output=True, text=True).stdout
RES = os.path.join(ROOT, 'MReduction', 'Resources.lean')
# name, ctor, n, h, d, hp, a, k, m, sigBytes
SETS = [('128s', 's128s', 16, 63, 7, 9, 12, 14, 30, 7856),
        ('128f', 's128f', 16, 66, 22, 3, 6, 33, 34, 17088),
        ('192s', 's192s', 24, 63, 7, 9, 14, 17, 39, 16224),
        ('192f', 's192f', 24, 66, 22, 3, 8, 33, 42, 35664),
        ('256s', 's256s', 32, 64, 8, 8, 14, 22, 47, 29792),
        ('256f', 's256f', 32, 68, 17, 4, 9, 35, 49, 49856)]
NAMES = ['rust_security', 'rust_pure_security', 'rust_security_linear', 'rust_pure_security_linear',
         'rust_security_deterministic', 'rust_security_hedged', 'rust_pure_security_deterministic',
         'rust_pure_security_hedged', 'rust_security_resources', 'rust_pure_security_resources']
old = old_file('security/E2E/Headline.lean')
res = open(RES).read()

def old_stmt(nm):
    m = re.search(r'^theorem ' + nm + r'\b(.*?) :=\n  ⟨', old, re.S | re.M)
    return m.group(1)

def phase2(name):
    m = re.search(r'FinalResourcesFinal A qs \(directCounts%s qs\) (\([0-9 +*qs]+\))' % name, res)
    return m.group(1)

def rooms(n):
    # Room slacks of lean/Slhdsa/Theorems.lean: 152 / 409 for n = 16 (as the single-set tree), 304 / 561 otherwise
    return (152, 409) if n == 16 else (304, 561)

def tr(stmt, name, ctor, n, k):
    se = 'Sha2Set.' + ctor
    ri, rp = rooms(n)
    b = re.sub(r'\bS\b', 'F', stmt)
    b = b.replace('slhdsa.slh.slh_', 'slhdsa.sets.sha2_%s.slh_' % name)
    b = re.sub(r'Array U8 (16|32|64)#usize',
               lambda mm: 'Array U8 %d#usize' % (int(mm.group(1)) // 16 * n), b)
    b = b.replace('Room m.length 152', 'Room m.length %d' % ri).replace('Room m.length 409', 'Room m.length %d' % rp)
    b = b.replace('(vp := vp)', '(vp := §.vp)')
    b = re.sub(r'(?<![.\w§])vp\b(?! :=)', '§.vp', b)
    b = re.sub(r'(?<![.\w])prims\b', '§.prims', b)
    b = b.replace('codec128s', '(codec §)')
    b = re.sub(r'\(node (\w+)\)', r'(node § \1)', b)
    b = b.replace('bTcrArM 35 ', 'bTcrArM %d ' % (2 * n + 3)).replace('bTcrArM 14 ', 'bTcrArM %d ' % k)
    b = b.replace('Reduction.Resources2.directCounts128s qs', 'MReduction.directCounts%s qs' % name)
    b = b.replace('(269824 + qs * 2007385 + 7857)', phase2(name))
    return b.replace('§', se)

def check128s():
    for nm in NAMES:
        g = tr(old_stmt(nm), '128s', 's128s', 16, 14)
        u = g.replace('slhdsa.sets.sha2_128s.slh_', 'slhdsa.slh.slh_')
        u = u.replace('(codec Sha2Set.s128s)', 'codec128s').replace('node Sha2Set.s128s ', 'node ')
        u = u.replace('Sha2Set.s128s.', '')
        u = u.replace('MReduction.directCounts128s qs', 'Reduction.Resources2.directCounts128s qs')
        assert u == re.sub(r'\bS\b', 'F', old_stmt(nm)), nm
check128s()

def hashes(n):
    if n == 16:
        return ("At this set (`n = 16`) all twelve terms are about SHA-256: `PRF`, `F`, `H`, `T_len`, `T_k` are\n"
                "    `Trunc_16(SHA-256(PK.seed ‖ 0^48 ‖ ADRSc ‖ ·))`, `PRF_msg` is HMAC-SHA-256, `H_msg` is MGF1-SHA-256 over\n"
                "    an inner SHA-256")
    return ("At this set (`n = %d`): `PRF` (term 1) and every `F` game (terms 4, 5: FORS-leaf DSPR/TCR; term 6:\n"
            "    class `1`; terms 10–12: WOTS+ UD/PRE/chain-TCR) are `Trunc_%d(SHA-256(PK.seed ‖ 0^%d ‖ ADRSc ‖ ·))`; the\n"
            "    class games `2` (`H`), `len` (`T_len`), `k` (`T_k`) (terms 7–9) are\n"
            "    `Trunc_%d(SHA-512(PK.seed ‖ 0^%d ‖ ADRSc ‖ ·))`; `PRF_msg` (term 2) is HMAC-SHA-512; ITSR (term 3) is about\n"
            "    `H_msg` = MGF1-SHA-512 over an inner SHA-512; the collection oracle of every SM game is the whole\n"
            "    `Thash` (both hash functions)") % (n, n, 64 - n, n, 128 - n)

def gen(name, ctor, n, h, d, hp, a, k, m, sig):
    se = 'Sha2Set.' + ctor
    ln = 2 * n + 3
    ri, rp = rooms(n)
    P = dict(ri=ri, rp=rp, name=name, se=se, n=n, n2=2 * n, n4=4 * n, sig=sig, len=ln, k=k, h=h, d=d, hp=hp, a=a, m=m,
             hashes=hashes(n), sha='SHA-256-based' if n == 16 else 'SHA-256- and SHA-512-based')
    st = {nm: tr(old_stmt(nm), name, ctor, n, k) for nm in NAMES}
    A3 = '''    ((∀ sk_seed'''
    out = []
    w = out.append
    w('''import ME2E.Basic
import MReduction.Headline
import MReduction.Linear
import MReduction.Resources

/-!
# SLH-DSA-SHA2-%(name)s: the Rust functions and the security of the scheme they compute

GENERATED by `ME2E/gen/gen.py` (statements: `security/E2E/Headline.lean` of git `26aa3d8` under the substitutions
listed there; proofs: `ME2E/Basic.lean` + `slhdsa.sha2_%(name)s.*_correct` + `MReduction`).

Parameters: `n = %(n)d`, `h = %(h)d`, `d = %(d)d`, `h' = %(hp)d`, `a = %(a)d`, `k = %(k)d`, `m = %(m)d`, `len = %(len)d`,
`w − 2 = 14`; seeds and `addrnd` `[u8; %(n)d]`, public key `[u8; %(n2)d]`, secret key `[u8; %(n4)d]`, signature
%(sig)d bytes.  Rust functions: `slhdsa::sets::sha2_%(name)s::{slh_keygen_internal, slh_sign_internal,
slh_verify_internal, slh_sign, slh_verify}` (Aeneas: `slhdsa.sets.sha2_%(name)s.*`).

* `rust_keygen_bytes`, `rust_sign_internal_bytes`, `rust_verify_internal_bytes`, `rust_sign_bytes`,
  `rust_verify_bytes`: the Rust functions are pointwise equal to the byte-level cores
  `Reduction.byteKeygen` / `byteSign` / `byteVerify` / `byteSignPure` / `byteVerifyPure` at
  `%(se)s.vp`, `%(se)s.prims`, `MReduction.codec %(se)s`;
* `bytes_end_to_end`, `pure_bytes_end_to_end`: the byte-level schemes are "sample, then apply the
  cores" (`ME2E.BytesScheme`, `ME2E.PureBytesScheme`) and the Rust functions are the cores;
* `rust_security`, `rust_pure_security` (twelve terms written out), `rust_security_linear`,
  `rust_pure_security_linear`, `rust_security_deterministic` / `_hedged`,
  `rust_pure_security_deterministic` / `_hedged`, `rust_security_resources`,
  `rust_pure_security_resources`.
-/

namespace ME2E.sha2_%(name)s

open Aeneas Aeneas.Std Result
open SLHDSA SLHDSA.Concrete SLHDSA.Security OracleComp OracleSpec SignatureAlg ENNReal
open slhdsa (bytes Room)
open MLink (Sha2Set)
open MReduction (codec)
open Reduction (bPrfC bPrfWC sufCheck rUd rPre rTcrT toDspr toTcr toInternal bTcrArM
  byteKeygen byteSign byteVerify byteSignPure byteVerifyPure bytesAlg pureBytesAlg bytesToTyped
  bytesToTypedS pureBytesToTyped prfRealPr prfIdealPr msgRealPr msgIdealPr)
open Reduction.Lazy (bPrfMsgL bPrfMsgWL bItsrL bOpenPreS bWotsS)
open TweakableHash

/-! ### The Rust functions are the byte-level cores -/

/-- **Rust `sha2_%(name)s::slh_keygen_internal` = `byteKeygen`** (FIPS 205 Alg. 18), pointwise: for
all three %(n)d-byte seeds the Rust function does not panic and returns arrays `(sk, pk)` whose
bytes are the pair `byteKeygen = (pk bytes, sk bytes)` at the seeds read as nodes. -/
theorem rust_keygen_bytes (sk_seed sk_prf pk_seed : Array U8 %(n)d#usize) :
    ∃ sk pk, slhdsa.sets.sha2_%(name)s.slh_keygen_internal sk_seed sk_prf pk_seed = ok (sk, pk) ∧
      (wire pk.val, wire sk.val) =
        byteKeygen %(se)s.vp %(se)s.prims (codec %(se)s) (node %(se)s sk_seed) (node %(se)s sk_prf)
          (node %(se)s pk_seed) := by
  obtain ⟨sk, pk, h, hp⟩ := slhdsa.sha2_%(name)s.keygen_correct sk_seed sk_prf pk_seed
  exact ⟨sk, pk, h, keygen_transfer %(se)s rfl sk_seed sk_prf pk_seed sk.val pk.val hp⟩

/-- **Rust `sha2_%(name)s::slh_sign_internal` = `byteSign`** (FIPS 205 Alg. 19 with
`opt_rand = addrnd`), pointwise: for every message under the `Room` bound, every %(n4)d-byte
secret-key array and every %(n)d-byte `addrnd`, the Rust function does not panic and the bytes of
the vector it returns are `byteSign` of the bytes of the message and of the secret key, and of
`addrnd` read as a node. -/
theorem rust_sign_internal_bytes (m : Slice U8) (sk : Array U8 %(n4)d#usize)
    (addrnd : Array U8 %(n)d#usize) (hm : Room m.length %(ri)d) :
    ∃ sig, slhdsa.sets.sha2_%(name)s.slh_sign_internal m sk addrnd = ok sig ∧
      wire sig.val =
        byteSign %(se)s.vp %(se)s.prims (codec %(se)s) (wire m.val) (wire sk.val)
          (node %(se)s addrnd) := by
  obtain ⟨sig, h, hp⟩ := slhdsa.sha2_%(name)s.sign_internal_correct m sk addrnd hm
  exact ⟨sig, h, sign_transfer %(se)s rfl m.val sk.val sig.val addrnd sk.property hp⟩

/-- The signature returned by the Rust `sha2_%(name)s::slh_sign_internal` has %(sig)d bytes. -/
theorem rust_sign_internal_length (m : Slice U8) (sk : Array U8 %(n4)d#usize)
    (addrnd : Array U8 %(n)d#usize) (hm : Room m.length %(ri)d) :
    ∃ sig, slhdsa.sets.sha2_%(name)s.slh_sign_internal m sk addrnd = ok sig ∧
      sig.val.length = %(sig)d := by
  obtain ⟨sig, h, hp⟩ := rust_sign_internal_bytes m sk addrnd hm
  refine ⟨sig, h, ?_⟩
  have e := congrArg List.length hp
  rw [wire_length] at e
  exact e.trans (byteSign_length %(se)s _ _ _ ((wire_length _).trans sk.property))

/-- **Rust `sha2_%(name)s::slh_verify_internal` = `byteVerify`** (FIPS 205 Alg. 20), pointwise: for
every message slice under the `Room` bound, every slice offered as a signature and every
%(n2)d-byte public-key array, the Rust function does not panic and returns `byteVerify` of the
bytes of its arguments. -/
theorem rust_verify_internal_bytes (m sig : Slice U8) (pk : Array U8 %(n2)d#usize)
    (hm : Room m.length %(ri)d) :
    slhdsa.sets.sha2_%(name)s.slh_verify_internal m sig pk =
      ok (byteVerify %(se)s.vp %(se)s.prims (codec %(se)s) (wire m.val) (wire sig.val)
        (wire pk.val)) := by
  rw [slhdsa.sha2_%(name)s.verify_internal_correct m sig pk hm]
  exact congrArg ok (verify_transfer %(se)s m.val sig.val pk.val pk.property)

/-- **Rust `sha2_%(name)s::slh_sign` = `byteSignPure`** (FIPS 205 Alg. 22 with caller-supplied
`addrnd`), pointwise: the Rust function does not panic; it returns `None` exactly when
`byteSignPure` is `none` (context longer than 255 bytes), and otherwise `Some` of a vector with
the bytes `byteSignPure` returns. -/
theorem rust_sign_bytes (m ctx : Slice U8) (sk : Array U8 %(n4)d#usize)
    (addrnd : Array U8 %(n)d#usize) (hm : Room m.length %(rp)d) :
    ∃ r, slhdsa.sets.sha2_%(name)s.slh_sign m ctx sk addrnd = ok r ∧
      r.map (fun v => wire v.val) =
        byteSignPure %(se)s.vp %(se)s.prims (codec %(se)s) (wire m.val) (wire ctx.val) (wire sk.val)
          (node %(se)s addrnd) := by
  obtain ⟨r, h, hp⟩ := slhdsa.sha2_%(name)s.sign_correct m ctx sk addrnd hm
  refine ⟨r, h, ?_⟩
  have e := signPure_transfer %(se)s rfl m.val ctx.val sk.val addrnd sk.property
    (r.map fun v => v.val) (by rw [Option.map_map]; exact hp)
  rw [Option.map_map] at e
  exact e

/-- **Rust `sha2_%(name)s::slh_verify` = `byteVerifyPure`** (FIPS 205 Alg. 24), pointwise. -/
theorem rust_verify_bytes (m sig ctx : Slice U8) (pk : Array U8 %(n2)d#usize)
    (hm : Room m.length %(rp)d) :
    slhdsa.sets.sha2_%(name)s.slh_verify m sig ctx pk =
      ok (byteVerifyPure %(se)s.vp %(se)s.prims (codec %(se)s) (wire m.val) (wire sig.val)
        (wire ctx.val) (wire pk.val)) := by
  rw [slhdsa.sha2_%(name)s.verify_correct m sig ctx pk hm]
  exact congrArg ok (verifyPure_transfer %(se)s m.val sig.val ctx.val pk.val pk.property)

/-- Numerals of the set: node, key and signature lengths in bytes, `len`, `k`, `w − 2`. -/
theorem numerals :
    %(se)s.vp.params.n = %(n)d ∧ %(se)s.vp.params.publicKeyBytes = %(n2)d ∧
      %(se)s.vp.params.secretKeyBytes = %(n4)d ∧ %(se)s.vp.params.signatureBytes = %(sig)d ∧
      %(se)s.vp.params.len = %(len)d ∧ %(se)s.vp.params.k = %(k)d ∧ %(se)s.vp.params.w - 2 = 14 := by
  decide

/-! ### Summary: the schemes and the Rust functions -/

/-- **The Rust internal functions are the deterministic cores of the byte-level scheme**
`B = Reduction.bytesAlg %(se)s.vp %(se)s.prims (codec %(se)s) optRand pkSeedDist`: `B` is
"sample, then apply `byteKeygen` / `byteSign` / `byteVerify`", returns `[]` when signing under a
public key that is not %(n2)d bytes, and is perfectly complete (`ME2E.BytesScheme`); and the Rust
`slh_keygen_internal`, `slh_sign_internal`, `slh_verify_internal` never panic and are pointwise
equal to these cores under the `Room` bound. -/
theorem bytes_end_to_end (optRand : PublicKeyCore %(se)s.prims.core → ProbComp %(se)s.prims.Y)
    (pkSeedDist : ProbComp %(se)s.prims.PkSeed) :
    BytesScheme %(se)s optRand pkSeedDist ∧
    (∀ sk_seed sk_prf pk_seed : Array U8 %(n)d#usize,
      ∃ sk pk, slhdsa.sets.sha2_%(name)s.slh_keygen_internal sk_seed sk_prf pk_seed = ok (sk, pk) ∧
        (wire pk.val, wire sk.val) =
          byteKeygen %(se)s.vp %(se)s.prims (codec %(se)s) (node %(se)s sk_seed)
            (node %(se)s sk_prf) (node %(se)s pk_seed)) ∧
    (∀ (m : Slice U8) (sk : Array U8 %(n4)d#usize) (addrnd : Array U8 %(n)d#usize),
      Room m.length %(ri)d →
      ∃ sig, slhdsa.sets.sha2_%(name)s.slh_sign_internal m sk addrnd = ok sig ∧
        wire sig.val =
          byteSign %(se)s.vp %(se)s.prims (codec %(se)s) (wire m.val) (wire sk.val)
            (node %(se)s addrnd)) ∧
    (∀ (m sig : Slice U8) (pk : Array U8 %(n2)d#usize), Room m.length %(ri)d →
      slhdsa.sets.sha2_%(name)s.slh_verify_internal m sig pk =
        ok (byteVerify %(se)s.vp %(se)s.prims (codec %(se)s) (wire m.val) (wire sig.val)
          (wire pk.val))) :=
  ⟨bytes_scheme %(se)s optRand pkSeedDist, rust_keygen_bytes, rust_sign_internal_bytes,
    rust_verify_internal_bytes⟩

/-- **The Rust public API functions are the deterministic cores of the byte-level external pure
scheme** `X = Reduction.pureBytesAlg %(se)s.vp %(se)s.prims (codec %(se)s) optRand pkSeedDist`
(`ME2E.PureBytesScheme`: sample, then apply `byteKeygen` / `byteSignPure` / `byteVerifyPure`;
`none` for a context longer than 255 bytes; complete for contexts of at most 255 bytes); the
Rust `slh_keygen_internal`, `slh_sign`, `slh_verify` never panic and are pointwise equal to these
cores under the `Room` bound (the Rust `Option` of `slh_sign` is the scheme's `Option`). -/
theorem pure_bytes_end_to_end
    (optRand : PublicKeyCore %(se)s.prims.core → ProbComp %(se)s.prims.Y)
    (pkSeedDist : ProbComp %(se)s.prims.PkSeed) :
    PureBytesScheme %(se)s optRand pkSeedDist ∧
    (∀ sk_seed sk_prf pk_seed : Array U8 %(n)d#usize,
      ∃ sk pk, slhdsa.sets.sha2_%(name)s.slh_keygen_internal sk_seed sk_prf pk_seed = ok (sk, pk) ∧
        (wire pk.val, wire sk.val) =
          byteKeygen %(se)s.vp %(se)s.prims (codec %(se)s) (node %(se)s sk_seed)
            (node %(se)s sk_prf) (node %(se)s pk_seed)) ∧
    (∀ (m ctx : Slice U8) (sk : Array U8 %(n4)d#usize) (addrnd : Array U8 %(n)d#usize),
      Room m.length %(rp)d →
      ∃ r, slhdsa.sets.sha2_%(name)s.slh_sign m ctx sk addrnd = ok r ∧
        r.map (fun v => wire v.val) =
          byteSignPure %(se)s.vp %(se)s.prims (codec %(se)s) (wire m.val) (wire ctx.val)
            (wire sk.val) (node %(se)s addrnd)) ∧
    (∀ (m sig ctx : Slice U8) (pk : Array U8 %(n2)d#usize), Room m.length %(rp)d →
      slhdsa.sets.sha2_%(name)s.slh_verify m sig ctx pk =
        ok (byteVerifyPure %(se)s.vp %(se)s.prims (codec %(se)s) (wire m.val) (wire sig.val)
          (wire ctx.val) (wire pk.val))) :=
  ⟨pure_bytes_scheme %(se)s optRand pkSeedDist, rust_keygen_bytes, rust_sign_bytes,
    rust_verify_bytes⟩

/-! ## Final statements -/
''' % P)
    doc = {}
    doc['rust_security'] = '''/-- **The Rust internal functions and the standard-model security of the scheme they compute
(SLH-DSA-SHA2-%(name)s, FIPS 205 Alg. 18–20) — final statement.**

Fix how `opt_rand` and `PK.seed` are sampled (`optRand`, `pkSeedDist`; arbitrary — for a
degenerate `pkSeedDist` the statement is about games with a known seed: still true, but the
assumptions are then implausible; see `rust_security_deterministic` / `_hedged` for uniform
`PK.seed`).  Let `B = Reduction.bytesAlg %(se)s.vp %(se)s.prims (codec %(se)s) optRand
pkSeedDist`, the signature scheme on byte strings with

  `B.keygen = do pkSeed ← pkSeedDist; skSeed ← $ᵗ; skPrf ← $ᵗ; pure (byteKeygen skSeed skPrf pkSeed)`,
  `B.sign pk sk m = do addrnd ← optRand (parsed pk); pure (byteSign m sk addrnd)`,
  `B.verify pk m sig = pure (byteVerify m sig pk)`

(`bytes_end_to_end` / `ME2E.bytes_scheme`: fields `keygen_alg`, `sign_alg`, `verify_alg`, and
perfect completeness `correct`).

(a) The Aeneas translations of the Rust `sets::sha2_%(name)s::slh_keygen_internal`,
    `slh_sign_internal`, `slh_verify_internal` never panic and are **pointwise equal** to
    `byteKeygen`, `byteSign`, `byteVerify`, for all inputs under the `Room` length bound.
(b) For **every** strong forger `F` against `B` — it receives the %(n2)d public-key bytes, has a
    signing oracle from message bytes to signature bytes, and wins if it outputs a message and a
    byte string that `byteVerify` accepts and that the oracle never returned for that message —
    the SUF-CMA advantage is at most the sum of twelve standard-model advantages:
    PRF on secret-key addresses, PRF_msg, ITSR, SM-DSPR(F) + 3·SM-TCR(F) at the FORS leaves,
    SM-TCR on `F`, `H`, `T_len`, `T_k` (arities `1`, `2`, `len = %(len)d`, `k = %(k)d`; each game capped
    at the exact number of calls of that function in the key structure), 14·SM-UD(F), SM-PRE(F),
    SM-TCR(F) on the WOTS+ chains (capped at `#inst·len·(w−1)`), each at an explicit adversary
    built from the typed forger `bytesToTypedS F` (one typed signing query per query of `F`).
    %(hashes)s (`MReduction/Audit.lean`).
(c) The same for every chosen-message forger `A` (EUF-CMA: the message was never queried).

Resources of the twelve adversaries: `rust_security_resources`.

**The remaining gap between "the scheme in the game" (`B`) and "the Rust functions"** — each
item checked against the statements of (a) and of `bytes_end_to_end`:

(i) *Sampling.*  `B.keygen` draws `PK.seed ← pkSeedDist` and `SK.seed`, `SK.prf` uniformly;
    `B.sign` draws `opt_rand ← optRand pk`.  The Rust functions take `sk_seed`, `sk_prf`,
    `pk_seed`, `addrnd` as *arguments* (quantified in (a)); no Rust code that samples them is
    covered.  The caller must supply them with the distributions of the game (for the
    deterministic variant: pass `addrnd = pk_seed`).
(ii) *Length bounds.*  The Rust equalities for signing and verification are under
    `Room m.length %(ri)d` (`m.length + %(ri)d ≤ usize::MAX` and `< 2^61`); key generation has no
    side condition; `B` is defined on all byte strings.
(iii) *Fixed-length arrays.*  The Rust public key is a `[u8; %(n2)d]`, the secret key a
    `[u8; %(n4)d]`, the returned signature a `Vec<u8>` of %(sig)d bytes
    (`rust_sign_internal_length`); `B` takes arbitrary byte strings.  On a public key that is
    not %(n2)d bytes `B.verify` rejects (`Reduction.byteVerify_of_pk_length_ne`) and `B.sign`
    returns `[]` (`ME2E.sign_bad_pk`); on a secret key that is not %(n4)d bytes `byteSign` returns
    `[]` (`Reduction.byteSign_of_sk_length_ne`); `[]` is never accepted
    (`Reduction.byteVerify_nil`); lengths: `numerals`.  Such inputs cannot be passed to the Rust
    functions and do not arise in the games (keys come from `B.keygen`).  Every %(n2)d-byte /
    %(n4)d-byte string parses (`ME2E.decodePk_wire`, `ME2E.decodeSk_wire`): no well-formedness of
    the secret key is checked — `byteSign` and the Rust signer use the `PK.seed`, `PK.root`
    stored in the secret key as they are.  The signature argument of the Rust verifier is a
    slice of any length, as in `B`.
(iv) *Byte representations.*  Rust bytes are Aeneas `U8`, the scheme's bytes Lean `UInt8`,
    identified by `wire = MLink.cv ∘ slhdsa.bytes`, a length-preserving bijection of lists
    (`ME2E.wire_length`, `wire_injective`, `wire_surjective`).  The %(n)d-byte seed and `addrnd`
    arrays are read as `Vector UInt8 %(n)d` by `node %(se)s` (`ME2E.nd_node`: same bytes),
    which is the carrier of `prims.SkSeed`, `prims.SkPrf`, `prims.PkSeed`, `prims.Y`.
    `byteKeygen` returns `(pk, sk)`, the Rust function `(sk, pk)`.  Every Rust `Result` is `ok`
    (no panic).
(v) *The public key in signing.*  `B.sign pk sk m` parses the public-key argument only to
    evaluate `optRand` on it; `slh_sign_internal` has no public-key argument.  In the games the
    two copies of `PK.seed` (in `pk` and in `sk`) agree, both coming from `byteKeygen`.
(vi) *Outside the statement.*  The twelve advantages on the right are not bounded (they are
    assumptions on the %(sha)s functions of FIPS 205 §11.2 at this set); no running-time claim
    (resources are counted in oracle queries, samples and hash evaluations; nine of the twelve
    adversaries walk the whole key structure); single key; the Rust compiler, the Aeneas
    extraction, the per-set instantiation `sets.rs` being the one extracted, and side
    channels. -/
''' % P
    doc['rust_pure_security'] = '''/-- **The Rust public API and the standard-model security of the scheme it computes
(SLH-DSA-SHA2-%(name)s, external pure interface, FIPS 205 Alg. 21/22/24) — final statement.**

Let `X = Reduction.pureBytesAlg %(se)s.vp %(se)s.prims (codec %(se)s) optRand pkSeedDist`:
messages are `(message, context)` pairs of byte strings, a signature is `Option (List UInt8)` —
the return type of the Rust `slh_sign`, `none` for a context longer than 255 bytes — with key
generation as in `rust_security`, `X.sign pk sk (M, ctx) = do addrnd ← optRand (parsed pk);
pure (byteSignPure M ctx sk addrnd)` for `|ctx| ≤ 255` and `pure none` (nothing sampled)
otherwise, `X.verify pk (M, ctx) (some sig) = pure (byteVerifyPure M sig ctx pk)`, `none`
rejected (`pure_bytes_end_to_end` / `ME2E.pure_bytes_scheme`; complete for contexts of at most
255 bytes).

(a) The Rust `sets::sha2_%(name)s::slh_keygen_internal`, `slh_sign`, `slh_verify` never panic and
    are pointwise equal to `byteKeygen`, `byteSignPure`, `byteVerifyPure` under
    `Room m.length %(rp)d` (the Rust `Option` of `slh_sign` is the scheme's `Option`).
(b) For every strong forger `F` against `X` — a forgery is `((message, context), some bytes)`
    accepted by `byteVerifyPure` and never returned for that pair; `none` is never accepted —
    the SUF-CMA advantage is at most the twelve advantages of `rust_security` (`len = %(len)d`,
    `k = %(k)d`, same hash functions), at the internal typed forger
    `toInternal (pureBytesToTyped F.toUnforgeableAdversary)` (at most one internal signing query
    per query of `F`; `Reduction.toInternal_pureBytesToTyped_queryBound`).
(c) The same for every chosen-message forger `A` (EUF-CMA).

The gap between `X` and the Rust functions is that of `rust_security`, items (i)–(vi), with
these changes: (ii) the `Room` slack is %(rp)d; (iii) `X.sign` returns `none` when the context is
over-long (before sampling; `byteSignPure` is `none` there for every `addrnd`,
`Reduction.byteSignPure_tooLong`) or the public key does not parse, and `byteSignPure` returns
`none` when the secret key is not %(n4)d bytes; contexts are slices on the Rust side and arbitrary
byte strings in `X`.  Pure mode only: the pre-hash interface (`HashSLH-DSA`) and mixed use of
one key in both modes are not covered. -/
''' % P
    doc['rust_security_linear'] = '''/-- **`rust_security` in linear (signed-pair) form** (SLH-DSA-SHA2-%(name)s).  Same scheme, same
games, same twelve adversaries; the four distinguishing advantages are replaced by their two
sides:

  `Adv + [Pr_ideal(PRF) + Pr_ideal(PRF_msg) + SPprob(DSPR) + 14·Pr_ideal(UD)]`
  `  ≤ Pr_real(PRF) + Pr_real(PRF_msg) + ITSR + (Succ(DSPR) + 3·TCR) + (four TCR) +`
  `      14·Pr_real(UD) + PRE + TCR`.

`prfRealPr B` / `prfIdealPr B`: probability that the PRF distinguisher `B` outputs `true` with
the real function resp. a lazy random function (`msgRealPr`, `msgIdealPr`: the same for
PRF_msg); `SM_DT_UD_RealSuccess` / `SM_DT_UD_IdealSuccess`: the SM-UD experiment in the real /
ideal world; `SM_DT_DSPR_SourceFinalValidity.Success` / `.SPProbability`: the DSPR experiment
and the second-preimage-existence experiment of the same adversary.  Every term is the
probability of `true` of an explicit experiment (`≤ 1`); there is no absolute value and no
truncated subtraction.  The absolute-value statement `rust_security` follows by cancelling the
finite left bracket (`Reduction.boundFinalTight_of_linear`). -/
''' % P
    doc['rust_pure_security_linear'] = '''/-- **`rust_pure_security` in linear (signed-pair) form** (SLH-DSA-SHA2-%(name)s; legend:
`rust_security_linear`). -/
''' % P
    def detdoc(iface, mode, ref):
        return ('''/-- **SUF-CMA and EUF-CMA of the byte-level scheme computed by the Rust code, SLH-DSA-SHA2-%(name)s,
''' + iface + ''';
uniform `PK.seed`; ''' + mode + '''.**  Instance of `''' + ref + '''` (b), (c), which hold for
arbitrary `pkSeedDist` and `optRand`; the bound `Reduction.betaSufFinalMemo` / `betaEufFinalMemo`
at the displayed typed forger is by definition the twelve terms written out in `''' + ref + '''`. -/
''') % P
    det = ('deterministic signing: `opt_rand = PK.seed` (`sha2RandomizerOfPkSeed` is the identity on\n'
           '`Bytes %(n)d`, `MReduction.detRand`)') % P
    hed = 'hedged signing: `opt_rand` uniform, fresh per signature'
    doc['rust_security_deterministic'] = detdoc('internal interface', det, 'rust_security')
    doc['rust_security_hedged'] = detdoc('internal interface', hed, 'rust_security')
    doc['rust_pure_security_deterministic'] = detdoc('external pure interface', det, 'rust_pure_security')
    doc['rust_pure_security_hedged'] = detdoc('external pure interface', hed, 'rust_pure_security')
    doc['rust_security_resources'] = '''/-- **Resources of the adversaries of `rust_security`** (SLH-DSA-SHA2-%(name)s): if the byte-level
forger makes at most `qs` signing queries (on every public key), so does the typed forger
`bytesToTyped A`, and the resource bundle `Reduction.FinalResourcesFinal` holds for it with the
numerals of this set (`MReduction.directCounts%(name)s`; table: `status/sets/D.md`,
`MReduction/Resources.lean`; the tight caps of the five re-capped games:
`MReduction.final_resources_final_%(name)s`).  For a strong forger `F` use
`A := F.toUnforgeableAdversary` (the same program;
`(bytesToTypedS F).toUnforgeableAdversary = bytesToTyped F.toUnforgeableAdversary` by `rfl`). -/
''' % P
    doc['rust_pure_security_resources'] = '''/-- **Resources of the adversaries of `rust_pure_security`** (SLH-DSA-SHA2-%(name)s). -/
''' % P
    M = 'MReduction.slhdsa_sha2_%s_' % name
    proof = {
        'rust_security': '''  ⟨⟨rust_keygen_bytes, rust_sign_internal_bytes, rust_verify_internal_bytes⟩,
    fun F => %sbytes_suf_cma_final optRand pkSeedDist F,
    fun A => %sbytes_euf_cma_final optRand pkSeedDist A⟩''' % (M, M),
        'rust_pure_security': '''  ⟨⟨rust_keygen_bytes, rust_sign_bytes, rust_verify_bytes⟩,
    fun F => %spure_bytes_suf_cma_final optRand pkSeedDist F,
    fun A => %spure_bytes_euf_cma_final optRand pkSeedDist A⟩''' % (M, M),
        'rust_security_linear': '''  ⟨⟨rust_keygen_bytes, rust_sign_internal_bytes, rust_verify_internal_bytes⟩,
    fun F => %sbytes_suf_cma_linear optRand pkSeedDist F,
    fun A => %sbytes_euf_cma_linear optRand pkSeedDist A⟩''' % (M, M),
        'rust_pure_security_linear': '''  ⟨⟨rust_keygen_bytes, rust_sign_bytes, rust_verify_bytes⟩,
    fun F => %spure_bytes_suf_cma_linear optRand pkSeedDist F,
    fun A => %spure_bytes_euf_cma_linear optRand pkSeedDist A⟩''' % (M, M),
        'rust_security_resources': '''  ⟨Reduction.bytesToTyped_queryBound A qs hA,
    (MReduction.final_resources_final_%s optRand pkSeedDist (bytesToTyped A) qs
      (Reduction.bytesToTyped_queryBound A qs hA)).1⟩''' % name,
        'rust_pure_security_resources': '''  ⟨Reduction.toInternal_pureBytesToTyped_queryBound A qs hA,
    (MReduction.final_resources_final_%s optRand pkSeedDist (toInternal (pureBytesToTyped A)) qs
      (Reduction.toInternal_pureBytesToTyped_queryBound A qs hA)).1⟩''' % name,
    }
    for pre, kind in [('rust_security', 'bytes'), ('rust_pure_security', 'pure_bytes')]:
        for mode in ['deterministic', 'hedged']:
            proof['%s_%s' % (pre, mode)] = '''  ⟨fun F => %s%s_suf_cma_%s F,
    fun A => %s%s_euf_cma_%s A⟩''' % (M, kind, mode, M, kind, mode)
    sections = {'rust_security_linear': '/-! ## Linear form -/\n\n',
                'rust_security_deterministic': '/-! ## Uniform `PK.seed`; deterministic and hedged `opt_rand` -/\n\n',
                'rust_security_resources': '/-! ## Resources -/\n\n'}
    for nm in NAMES:
        w('\n' + sections.get(nm, '') + doc[nm] + 'theorem ' + nm + st[nm] + ' :=\n' + proof[nm] + '\n')
    w('\nend ME2E.sha2_%s\n\n' % name)
    for nm in ['rust_keygen_bytes', 'rust_sign_internal_bytes', 'rust_sign_internal_length',
               'rust_verify_internal_bytes', 'rust_sign_bytes', 'rust_verify_bytes',
               'bytes_end_to_end', 'pure_bytes_end_to_end'] + NAMES:
        w('#print axioms ME2E.sha2_%s.%s\n' % (name, nm))
    open(os.path.join(ROOT, 'ME2E', 'Sha2_%s.lean' % name), 'w').write(''.join(out))

for s in SETS:
    gen(*s)
# ME2E.lean (the import list) is written by scripts/gen_api_rom.py.
print('ok')
