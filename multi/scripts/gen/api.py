import sys, re
exec(open('/private/tmp/claude-501/-Users-danrobinson-Projects-formal-sig/aa936096-0075-48f4-b18f-ef8efe20006c/scratchpad/multi-proofs/gen/common.py').read())
M = open('/Users/danrobinson/Projects/formal-sig/lean/Slhdsa/ApiTheorems.lean').read()
body = M[M.index('/-! ## (A) Exactness -/'):M.index('end slhdsa')]
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
for a,b in [('slh.slh_sign_internal_checked','sets.sha2_{S}.slh_sign_internal_checked'),
            ('slh.slh_sign_checked','sets.sha2_{S}.slh_sign_checked'),
            ('slh.slh_verify_internal','sets.sha2_{S}.slh_verify_internal'),
            ('slh.slh_keygen_internal','sets.sha2_{S}.slh_keygen_internal'),
            ('slh.slh_sign_internal ','sets.sha2_{S}.slh_sign_internal '),
            ('slh.slh_sign ','sets.sha2_{S}.slh_sign '),
            ('slh.slh_verify ','sets.sha2_{S}.slh_verify '),
            ('api.sign_deterministic_checked','sets.sha2_{S}.sign_deterministic_checked'),
            ('api.sign_deterministic ','sets.sha2_{S}.sign_deterministic '),
            ('api.sign_checked','sets.sha2_{S}.sign_checked'),
            ('api.public_key','sets.sha2_{S}.public_key'),
            ('api.verify,','sets.sha2_{S}.verify,'),
            ('api.verify ','sets.sha2_{S}.verify '),
            ('api.keygen','sets.sha2_{S}.keygen'),
            ('api.sign ','sets.sha2_{S}.sign ')]:
    t = t.replace(a,b)
# spec functions with parameter
for f in ['slhSignInternalChecked','slhSignChecked','slhSignInternal','slhSign','slhVerifyInternal','slhVerify',
          'skPk','KeyOk','block','slhKeygenInternal']:
    t = re.sub(r'Spec\.%s(?=[ \n])' % f, 'Spec.%s Spec.sha2_{S}' % f, t)
# spec lemmas (generic): add P hv
for f in ['slhSignInternalChecked_sound','slhSignChecked_sound','slhSignInternalChecked_complete',
          'slhSignChecked_complete','slh_complete_internal','slh_complete','keygen_keyOk']:
    t = re.sub(r'Spec\.%s(?=[ \n])' % f, 'Spec.%s Spec.sha2_{S} Spec.sha2_{S}_valid' % f, t)
# local spec lemma names -> per-set
for f in ['slh_sign_internal_checked_spec','slh_sign_checked_spec','api_sign_deterministic_checked_spec',
          'api_public_key_spec','api_keygen_spec','api_sign_deterministic_spec']:
    g = {'api_sign_deterministic_checked_spec':'sign_deterministic_checked_spec','api_public_key_spec':'public_key_spec',
         'api_keygen_spec':'keygen_spec','api_sign_deterministic_spec':'sign_deterministic_spec'}.get(f,f)
    t = re.sub(r'(?<![\w.])%s(?=[ \n])' % f, 'sha2_{S}.%s' % g, t)
# helpers
t = t.replace('three\n16-byte blocks','three\n{N}-byte blocks').replace('16-byte blocks','{N}-byte blocks')
t = t.replace('bytes_length16','bytes_lengthN').replace('block48_length','blockSeed_length')
HEAD = r'''import Slhdsa.Theorems
import Spec.Correctness
open Aeneas Aeneas.Std Result

/-!
# Results about the checked signer and the crate's interface, per parameter set

For each of the six sets, the statements of the single-set tree's
`ApiTheorems.lean`, about the per-set functions of `sets.rs` (fixed-size key
types) and FIPS 205 at that set:

* (A) the checked signer never fails, and every signature it releases is the
  signature of FIPS 205 (the right-hand sides of `sign_internal_correct` and
  `sign_correct`);
* (B) every signature it releases verifies under the public key held in the
  private key, for every private key;
* (C) for a well-formed private key (`Spec.KeyOk`: the last block is the root
  that key generation derives from the first and third; in particular every
  key that key generation produced) it always releases a signature;
* (D) completeness: with a key from key generation, the signatures of the
  plain and the checked signers verify;
* (E) the rest of the interface: `keygen`, `public_key`, `verify`, and the
  plain `sign` and `sign_deterministic`.

`Spec.skPk p sk` is `sk.drop (2n)`, the public key `PK.seed ‖ PK.root` held in
a private key. The hypotheses `Room` are those of `Theorems.lean`. Generated
by a script from the single-set file (the same proofs, at each set).
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
open('/Users/danrobinson/Projects/formal-sig/multi/lean/Slhdsa/ApiTheorems.lean','w').write(out)
print(len(names), names)
