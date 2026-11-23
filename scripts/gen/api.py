import sys, re
import os
exec(open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'common.py')).read())
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
# The single-set tree's headline files are the templates; that tree is git commit 26aa3d8.
import subprocess
def old(path): return subprocess.run(['git', '-C', ROOT, 'show', '26aa3d8:' + path], check=True, capture_output=True, text=True).stdout
M = old('lean/Slhdsa/ApiTheorems.lean')
body = M[M.index('/-! ## (A) Exactness -/'):M.index('end slhdsa')]
# The single-set file also has theorems about functions this crate no longer has (removed on
# 2026-11-22; HANDOFF.md). Kept: the theorems named here, with their docstrings, in the
# template's order; the section headers are replaced by two new ones below.
KEEP = ['api_public_key_correct', 'keygen_keyOk', 'api_keygen_correct', 'block48_length',
        'api_keygen_keyOk', 'api_verify_correct', 'api_sign_correct', 'api_sign_deterministic_correct',
        'complete_internal', 'complete', 'api_complete_sign', 'api_complete_sign_deterministic']
def chunk_name(c):
    m = re.search(r'^theorem (\w+)', c, re.M)
    return m.group(1) if m else None
chunks = body.split('\n\n')
keep = [c for c in chunks if chunk_name(c) in KEEP]
assert [chunk_name(c) for c in keep] == KEEP, [chunk_name(c) for c in keep]
body = '\n\n'.join(keep) + '\n\n'
body = body.replace('theorem api_public_key_correct', '/-! ## Keys and the interface -/\n\ntheorem api_public_key_correct', 1)
body = body.replace('theorem complete_internal', '/-! ## Completeness: signatures made with a generated key verify -/\n\ntheorem complete_internal', 1)
names = re.findall(r'^theorem (\w+)', body, re.M)
names = [n for n in names if n not in ('ok_inj','bytes_length16','block48_length')]
t = body
i0 = t.index('theorem block48_length'); i1 = t.index('/-- Keys from `api.keygen` are well formed')
t = t[:i0] + t[i1:]
t = t.replace('rw [api.verify, verify_correct', 'rw [verify_eq, verify_correct')
# types
t = t.replace('Array U8 64#usize','Array U8 {SK}#usize').replace('Array U8 16#usize','Array U8 {N}#usize')
t = t.replace('Array U8 32#usize','Array U8 {PK}#usize').replace('Array U8 48#usize','Array U8 {SEED}#usize')
t = t.replace('Room m.length 152','Room m.length {SL}').replace('Room m.length 409','Room m.length {SLP}')
# rust functions
for a,b in [('slh.slh_verify_internal','sets.sha2_{S}.slh_verify_internal'),
            ('slh.slh_keygen_internal','sets.sha2_{S}.slh_keygen_internal'),
            ('slh.slh_sign_internal ','sets.sha2_{S}.slh_sign_internal '),
            ('slh.slh_sign ','sets.sha2_{S}.slh_sign '),
            ('slh.slh_verify ','sets.sha2_{S}.slh_verify '),
            ('api.sign_deterministic ','sets.sha2_{S}.sign_deterministic '),
            ('api.public_key','sets.sha2_{S}.public_key'),
            ('api.verify,','sets.sha2_{S}.verify,'),
            ('api.verify ','sets.sha2_{S}.verify '),
            ('api.keygen','sets.sha2_{S}.keygen'),
            ('api.sign ','sets.sha2_{S}.sign ')]:
    t = t.replace(a,b)
# spec functions with parameter
for f in ['slhSignInternal','slhSign','slhVerifyInternal','slhVerify',
          'skPk','KeyOk','block','slhKeygenInternal']:
    t = re.sub(r'Spec\.%s(?=[ \n])' % f, 'Spec.%s Spec.sha2_{S}' % f, t)
# spec lemmas (generic): add P hv
for f in ['slh_complete_internal','slh_complete','keygen_keyOk']:
    t = re.sub(r'Spec\.%s(?=[ \n])' % f, 'Spec.%s Spec.sha2_{S} Spec.sha2_{S}_valid' % f, t)
# local spec lemma names -> per-set
for f in ['api_public_key_spec','api_keygen_spec','api_sign_deterministic_spec']:
    g = {'api_public_key_spec':'public_key_spec',
         'api_keygen_spec':'keygen_spec','api_sign_deterministic_spec':'sign_deterministic_spec'}.get(f,f)
    t = re.sub(r'(?<![\w.])%s(?=[ \n])' % f, 'sha2_{S}.%s' % g, t)
# helpers
t = t.replace('three\n16-byte blocks','three\n{N}-byte blocks').replace('16-byte blocks','{N}-byte blocks')
t = t.replace('bytes_length16','bytes_lengthN').replace('block48_length','blockSeed_length')
HEAD = r'''import Slhdsa.Theorems
import Spec.Correctness
open Aeneas Aeneas.Std Result

/-!
# Results about the crate's interface, per parameter set

For each of the six sets, about the per-set functions of `sets.rs` (fixed-size
key types) and FIPS 205 at that set:

* the interface: `keygen` (Algorithm 21 on its three blocks of random bytes;
  the key it writes is well formed, `Spec.KeyOk`: the last block is the root
  that key generation derives from the first and third), `public_key`,
  `verify`, `sign` and `sign_deterministic`;
* completeness: with a key from key generation, the signatures of the internal,
  the pure and the interface signers verify.

`Spec.skPk p sk` is `sk.drop (2n)`, the public key `PK.seed ‖ PK.root` held in
a private key. The hypotheses `Room` are those of `Theorems.lean`. Generated
by a script from the single-set tree's file (the same statements and proofs,
at each set).
-/

namespace slhdsa

theorem ok_inj {α} {m : Result α} {r v : α} (h1 : m = ok r) (h2 : m = ok v) : r = v := by
  rw [h1] at h2; simpa using h2
'''
SETHEAD = r'''
/-! ## SLH-DSA-SHA2-{S} -/

namespace sha2_{S}

theorem bytes_lengthN (x : Array U8 {N}#usize) : (bytes x.val).length = Spec.sha2_{S}.n := by
  simp [Spec.sha2_{S}]

theorem verify_eq (m sig ctx : Slice U8) (pk : Array U8 {PK}#usize) :
    sets.sha2_{S}.verify m sig ctx pk = sets.sha2_{S}.slh_verify m sig ctx pk := by
  unfold sets.sha2_{S}.verify sets.sha2_{S}.slh_verify api.verify; rfl

theorem blockSeed_length (seeds : Array U8 {SEED}#usize) (i : Nat) (hi : i < 3) :
    (Spec.block Spec.sha2_{S} (bytes seeds.val) i).length = Spec.sha2_{S}.n := by
  simp [Spec.block, Spec.sha2_{S}]; omega

'''
out = HEAD
axs = ''
for s in sets():
    r = reps(*s)
    out += sub(SETHEAD, r) + sub(t, r) + '\nend sha2_{S}\n'.replace('{S}', s[0])
    for n in names: axs += '#print axioms slhdsa.sha2_%s.%s\n' % (s[0], n)
out += '\nend slhdsa\n\n' + axs
open(os.path.join(ROOT, 'lean/Slhdsa/ApiTheorems.lean'),'w').write(out)
print(len(names), names)
