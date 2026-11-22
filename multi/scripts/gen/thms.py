import sys, re
SETS = [('128s',16,'SHA2_128S',7856),('128f',16,'SHA2_128F',17088),('192s',24,'SHA2_192S',16224),
        ('192f',24,'SHA2_192F',35664),('256s',32,'SHA2_256S',29792),('256f',32,'SHA2_256F',49856)]
only = sys.argv[1:]
def sets(): return [s for s in SETS if not only or s[0] in only]
def sub(t, rep):
    for k,v in rep.items(): t = t.replace('{'+k+'}', str(v))
    return t
def reps(S,N,SU,SIG):
    sl = 152 if N==16 else 304
    return dict(S=S,N=N,SU=SU,SK=4*N,PK=2*N,SEED=3*N,SL=sl,SLP=sl+257,SIG=SIG)

# ---------------- Theorems.lean ----------------
TH_HEAD = r'''import Slhdsa.Proofs.Sets
open Aeneas Aeneas.Std Result

/-!
# Main results

The Rust functions of the `slhdsa` crate (the optimised implementation in
`multi/rust`), as translated to Lean by Aeneas, never panic and compute
exactly the functions of the FIPS 205 transcription in `Spec/SlhDsa.lean`,
for each of SLH-DSA-SHA2-{128s,128f,192s,192f,256s,256f}.

`bytes` maps machine bytes to the specification's bytes. `Room len slack`
says a message of `len` bytes plus `slack` more fits in memory and its bit
length fits in SHA-256's 64-bit length field. The slack is 152 bytes for the
internal functions and 409 for the pure ones when `n = 16` (SHA-256
throughout; the same numbers as the single-set tree), and 304 / 561 when
`n = 24, 32` (SHA-512 for `H_msg` and `PRF_msg`).

* `slhdsa.sha2_128s.keygen_correct` … `slhdsa.sha2_256f.verify_correct`: five
  theorems per parameter set, about the functions with fixed-size key types
  in `sets.rs`. Their only hypothesis is `Room`.
* `slhdsa.generic.*`: the same five theorems about the generic functions of
  `slh.rs`, for any `params.Params` value `p` whose specification-level view
  satisfies `Spec.Params.Valid`, with `N = p.n` (`PN p N`). Those functions
  take slices, so the key lengths appear as hypotheses there.
-/

namespace slhdsa

/-- The Rust SHA-256 is SHA-256. -/
theorem sha256_correct (msg : Slice U8) (h : Room msg.length 72) :
    ∃ d, sha256.sha256 msg = ok d ∧ bytes d.val = Spec.sha256 (bytes msg.val) :=
  spec_imp_exists (sha256_spec msg h)

/-- The Rust SHA-512 is SHA-512. The hypothesis says only that the padded
message fits in memory. -/
theorem sha512_correct (msg : Slice U8) (h : msg.length + 144 ≤ Usize.max) :
    ∃ d, sha512.sha512 msg = ok d ∧ bytes d.val = Spec.sha512 (bytes msg.val) :=
  spec_imp_exists (sha512_spec msg h)

/-! ## The generic functions, for any valid parameter set -/

namespace generic

theorem keygen_correct {N : Usize} (p : params.Params) (hp : PN p N)
    (sk_seed sk_prf pk_seed : Array U8 N) (sk pk : Slice U8)
    (hsk : sk.length = 4 * N.val) (hpk : pk.length = 2 * N.val) :
    ∃ sk' pk', slh.slh_keygen_internal p sk_seed sk_prf pk_seed sk pk = ok (sk', pk') ∧
      (bytes sk'.val, bytes pk'.val) =
        Spec.slhKeygenInternal (paramsS p) (bytes sk_seed.val) (bytes sk_prf.val) (bytes pk_seed.val) := by
  obtain ⟨⟨sk', pk'⟩, h, hp, -⟩ :=
    spec_imp_exists (slh_keygen_internal_spec p hp sk_seed sk_prf pk_seed sk pk hsk hpk)
  exact ⟨sk', pk', h, hp⟩

theorem sign_internal_correct {N : Usize} (p : params.Params) (hp : PN p N)
    (m sk : Slice U8) (addrnd : Array U8 N) (hsk : sk.length = 4 * N.val)
    (hm : Room m.length (msgSlack N.val)) :
    ∃ sig, slh.slh_sign_internal p m sk addrnd = ok sig ∧
      bytes sig.val = Spec.slhSignInternal (paramsS p) (bytes m.val) (bytes sk.val) (bytes addrnd.val) := by
  obtain ⟨sig, h, hp, -⟩ := spec_imp_exists (slh_sign_internal_spec p hp m sk addrnd hsk hm)
  exact ⟨sig, h, hp⟩

/-- For every byte string `sig` offered as a signature. -/
theorem verify_internal_correct {N : Usize} (p : params.Params) (hp : PN p N)
    (m sig pk : Slice U8) (hpk : pk.length = 2 * N.val) (hm : Room m.length (msgSlack N.val)) :
    slh.slh_verify_internal N p m sig pk =
      ok (Spec.slhVerifyInternal (paramsS p) (bytes m.val) (bytes sig.val) (bytes pk.val)) := by
  obtain ⟨b, h, hp⟩ := spec_imp_exists (slh_verify_internal_spec p hp m sig pk hpk hm)
  rw [h, hp]

theorem sign_correct {N : Usize} (p : params.Params) (hp : PN p N)
    (m ctx sk : Slice U8) (addrnd : Array U8 N) (hsk : sk.length = 4 * N.val)
    (hm : Room m.length (msgSlack N.val + 257)) :
    ∃ r, slh.slh_sign p m ctx sk addrnd = ok r ∧
      r.map (fun v => bytes v.val) =
        Spec.slhSign (paramsS p) (bytes m.val) (bytes ctx.val) (bytes sk.val) (bytes addrnd.val) :=
  spec_imp_exists (slh_sign_spec p hp m ctx sk addrnd hsk hm)

theorem verify_correct {N : Usize} (p : params.Params) (hp : PN p N)
    (m sig ctx pk : Slice U8) (hpk : pk.length = 2 * N.val) (hm : Room m.length (msgSlack N.val + 257)) :
    slh.slh_verify N p m sig ctx pk =
      ok (Spec.slhVerify (paramsS p) (bytes m.val) (bytes sig.val) (bytes ctx.val) (bytes pk.val)) := by
  obtain ⟨b, h, hp⟩ := spec_imp_exists (slh_verify_spec p hp m sig ctx pk hpk hm)
  rw [h, hp]

end generic
'''
TH_SET = r'''
/-! ## SLH-DSA-SHA2-{S} -/

namespace sha2_{S}

/-- Key generation: for all seeds, the Rust `sha2_{S}::slh_keygen_internal`
returns the secret and public key of FIPS 205 Algorithm 18. -/
theorem keygen_correct (sk_seed sk_prf pk_seed : Array U8 {N}#usize) :
    ∃ sk pk, sets.sha2_{S}.slh_keygen_internal sk_seed sk_prf pk_seed = ok (sk, pk) ∧
      (bytes sk.val, bytes pk.val) =
        Spec.slhKeygenInternal Spec.sha2_{S} (bytes sk_seed.val) (bytes sk_prf.val)
          (bytes pk_seed.val) := by
  obtain ⟨⟨sk, pk⟩, h, hp⟩ :=
    spec_imp_exists (sha2_{S}.slh_keygen_internal_spec sk_seed sk_prf pk_seed)
  exact ⟨sk, pk, h, hp⟩

/-- Signing: the Rust `sha2_{S}::slh_sign_internal` returns the signature of
FIPS 205 Algorithm 19. -/
theorem sign_internal_correct (m : Slice U8) (sk : Array U8 {SK}#usize)
    (addrnd : Array U8 {N}#usize) (hm : Room m.length {SL}) :
    ∃ sig, sets.sha2_{S}.slh_sign_internal m sk addrnd = ok sig ∧
      bytes sig.val =
        Spec.slhSignInternal Spec.sha2_{S} (bytes m.val) (bytes sk.val) (bytes addrnd.val) :=
  spec_imp_exists (sha2_{S}.slh_sign_internal_spec m sk addrnd hm)

/-- Verification: the Rust `sha2_{S}::slh_verify_internal` returns the verdict
of FIPS 205 Algorithm 20, for every byte string offered as a signature. -/
theorem verify_internal_correct (m sig : Slice U8) (pk : Array U8 {PK}#usize)
    (hm : Room m.length {SL}) :
    sets.sha2_{S}.slh_verify_internal m sig pk =
      ok (Spec.slhVerifyInternal Spec.sha2_{S} (bytes m.val) (bytes sig.val) (bytes pk.val)) := by
  obtain ⟨b, h, hp⟩ := spec_imp_exists (sha2_{S}.slh_verify_internal_spec m sig pk hm)
  rw [h, hp]

/-- Pure signing with a context string (FIPS 205 Algorithm 22). -/
theorem sign_correct (m ctx : Slice U8) (sk : Array U8 {SK}#usize)
    (addrnd : Array U8 {N}#usize) (hm : Room m.length {SLP}) :
    ∃ r, sets.sha2_{S}.slh_sign m ctx sk addrnd = ok r ∧
      r.map (fun v => bytes v.val) =
        Spec.slhSign Spec.sha2_{S} (bytes m.val) (bytes ctx.val) (bytes sk.val)
          (bytes addrnd.val) :=
  spec_imp_exists (sha2_{S}.slh_sign_spec m ctx sk addrnd hm)

/-- Pure verification with a context string (FIPS 205 Algorithm 24). -/
theorem verify_correct (m sig ctx : Slice U8) (pk : Array U8 {PK}#usize)
    (hm : Room m.length {SLP}) :
    sets.sha2_{S}.slh_verify m sig ctx pk =
      ok (Spec.slhVerify Spec.sha2_{S} (bytes m.val) (bytes sig.val) (bytes ctx.val)
        (bytes pk.val)) := by
  obtain ⟨b, h, hp⟩ := spec_imp_exists (sha2_{S}.slh_verify_spec m sig ctx pk hm)
  rw [h, hp]

end sha2_{S}
'''
out = TH_HEAD
for s in sets(): out += sub(TH_SET, reps(*s))
out += '\nend slhdsa\n\n'
out += '#print axioms slhdsa.sha256_correct\n#print axioms slhdsa.sha512_correct\n'
for n in ['keygen_correct','sign_internal_correct','verify_internal_correct','sign_correct','verify_correct']:
    out += '#print axioms slhdsa.generic.%s\n' % n
for s in sets():
    for n in ['keygen_correct','sign_internal_correct','verify_internal_correct','sign_correct','verify_correct']:
        out += '#print axioms slhdsa.sha2_%s.%s\n' % (s[0], n)
open('/Users/danrobinson/Projects/formal-sig/multi/lean/Slhdsa/Theorems.lean','w').write(out)
