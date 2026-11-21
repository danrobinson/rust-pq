import Slhdsa
import Link

/-!
# End to end: the Rust code, FIPS 205, and the scheme of the security theorem

Three layers are composed here.

1. `Slhdsa` (`slhdsa.*_correct`): the Rust functions of the `slhdsa` crate, as translated to Lean by
   Aeneas, never panic and compute the functions of our FIPS 205 transcription `Spec` (under the
   `Room` bound on the message length).
2. `Link` (`Link.verify_eq`, `Link.keygen_eq`, `Link.sign_eq`, …): `Spec` computes the executable
   SLH-DSA-SHA2-128s algorithms of VCVio (`GeneralScheme.keygenInternal`, `signInternal`,
   `verifyInternal` at `Link.vp`, `Link.prims`) on VCVio's own FIPS wire encodings.
3. `Link.romScheme_map_romAnswer_128s`, `Link.security_128s`: those algorithms are the scheme
   `romScheme prims.core …` with its three oracles answered by the SHA-2 functions, and that scheme,
   *with random oracles*, satisfies an explicit SUF-CMA bound.

What is established is therefore an identity of programs from the Rust code up to the object that
the security theorem bounds, with its oracles instantiated.  What is **not** established, here or
anywhere in this development, is that this random-oracle bound holds for the SHA-256
instantiation: replacing
random oracles by SHA-256 / HMAC-SHA-256 / MGF1 is the usual random-oracle methodology, a heuristic
step and not a theorem.  Nor is anything said about the Rust compiler, the Aeneas translation
(trusted), side channels, or how the seeds and `addrnd` are generated.

(Separately, and without random oracles, `E2E/FinalSplit.lean` bounds the SUF-CMA / EUF-CMA
advantage against the same scheme `internalAlg vp prims …` by standard-model advantages against
the SHA-2-based functions; that is a different theorem, not a transfer of the bound above.)
-/

namespace E2E

open Aeneas Aeneas.Std Result
open SLHDSA SLHDSA.Concrete SLHDSA.Security OracleComp OracleSpec SignatureAlg
open slhdsa (bytes Room)
open Link (vp prims cv sp nd Node sigBytes pkBytes skBytes)

/-! ### Reading Rust byte arrays as VCVio's typed values -/

/-- Read specification bytes as a 16-byte VCVio node (missing bytes read as `0`; only used on
16-byte inputs, where it is the inverse of `Link.nd`, see `nd_nodeOfBytes`). -/
def nodeOfBytes (l : Spec.Bytes) : Node :=
  Vector.ofFn fun j : Fin 16 => UInt8.ofBitVec (l.getD j.val 0)

/-- On 16 bytes, `nodeOfBytes` inverts `Link.nd`. -/
theorem nd_nodeOfBytes (l : Spec.Bytes) (h : l.length = 16) : nd (nodeOfBytes l) = l := by
  apply List.ext_getElem
  · simp [h]
  · intro i h1 h2
    simp [nd, sp, nodeOfBytes, h2]

/-- A 16-byte Rust array read as a VCVio node (a seed, or `addrnd`). -/
def node (x : Array U8 16#usize) : Node := nodeOfBytes (bytes x.val)

/-- The node `node x` has exactly the bytes of `x`. -/
theorem nd_node (x : Array U8 16#usize) : nd (node x) = bytes x.val :=
  nd_nodeOfBytes _ (by simp)

/-- A 64-byte Rust secret-key array read as VCVio's typed secret key
`SK.seed ‖ SK.prf ‖ PK.seed ‖ PK.root` (FIPS 205 Figure 15). -/
def secretKey (sk : Array U8 64#usize) : SecretKeyCore prims.core :=
  { skSeed := nodeOfBytes ((bytes sk.val).take 16)
    skPrf := nodeOfBytes (((bytes sk.val).drop 16).take 16)
    pkSeed := nodeOfBytes (((bytes sk.val).drop 32).take 16)
    pkRoot := nodeOfBytes ((bytes sk.val).drop 48) }

/-- `secretKey sk` encodes back to exactly the 64 bytes of `sk`: every Rust secret-key array is
the FIPS encoding of a (unique) typed secret key. -/
theorem skBytes_secretKey (sk : Array U8 64#usize) : skBytes (secretKey sk) = bytes sk.val := by
  have h : (bytes sk.val).length = 64 := by simp
  show nd (nodeOfBytes _) ++ nd (nodeOfBytes _) ++ nd (nodeOfBytes _) ++ nd (nodeOfBytes _) = _
  rw [nd_nodeOfBytes _ (by simp [h]), nd_nodeOfBytes _ (by simp [h]),
    nd_nodeOfBytes _ (by simp [h]), nd_nodeOfBytes _ (by simp [h])]
  generalize bytes sk.val = l
  rw [show l.drop 32 = (l.drop 16).drop 16 by simp,
    show l.drop 48 = ((l.drop 16).drop 16).drop 16 by simp]
  simp only [List.append_assoc, List.take_append_drop]

/-! ### Verification -/

/-- **Rust internal verification = VCVio's executable verifier** (FIPS 205 Algorithm 20).
For every message under the `Room` bound (it fits in memory with 152 bytes to spare and is shorter
than `2^61` bytes), every byte slice offered as a signature and every public-key array, the Rust
`slh_verify_internal` does not panic and returns what VCVio's `GeneralScheme.verifyInternal` at
SLH-DSA-SHA2-128s returns on the values produced by VCVio's strict decoders; a signature that does
not decode (wrong length) is rejected.  The public key always decodes (`rust_verify_internal'`).

It does not say anything about security; it is a functional identity. -/
theorem rust_verify_internal (m sig : Slice U8) (pk : Array U8 32#usize)
    (hm : Room m.length 152) :
    slhdsa.slh.slh_verify_internal m sig pk =
      ok (match Link.decodeSig (cv (bytes sig.val)), Link.decodePk (cv (bytes pk.val)) with
          | .ok s, .ok k => GeneralScheme.verifyInternal vp prims (cv (bytes m.val)) s k
          | _, _ => false) := by
  rw [slhdsa.verify_internal_correct m sig pk hm, Link.verify_eq _ _ _ (by simp)]
  rfl

/-- The same with the decoded public key made explicit: the 32-byte Rust public key is the
encoding of a typed key `k`, and the verdict is `verifyInternal … s k` if the signature decodes to
`s`, and `false` otherwise. -/
theorem rust_verify_internal' (m sig : Slice U8) (pk : Array U8 32#usize)
    (hm : Room m.length 152) :
    ∃ k, Link.decodePk (cv (bytes pk.val)) = .ok k ∧ bytes pk.val = pkBytes k ∧
      slhdsa.slh.slh_verify_internal m sig pk =
        ok (match Link.decodeSig (cv (bytes sig.val)) with
            | .ok s => GeneralScheme.verifyInternal vp prims (cv (bytes m.val)) s k
            | .error _ => false) := by
  obtain ⟨k, hk, hpk⟩ := Link.decodePk_ok (bytes pk.val) (by simp)
  refine ⟨k, hk, hpk, ?_⟩
  rw [rust_verify_internal m sig pk hm, hk]
  cases Link.decodeSig (cv (bytes sig.val)) <;> rfl

/-- **Rust pure verification = VCVio's `External.verifyPure`** (FIPS 205 Algorithm 24, with a
context string).  Same reading as `rust_verify_internal`; the `Room` slack is 409 bytes because
the context prefix (up to 257 bytes) is prepended to the message.  An over-long context is
rejected on both sides. -/
theorem rust_verify (m sig ctx : Slice U8) (pk : Array U8 32#usize)
    (hm : Room m.length 409) :
    slhdsa.slh.slh_verify m sig ctx pk =
      ok (match Link.decodeSig (cv (bytes sig.val)), Link.decodePk (cv (bytes pk.val)) with
          | .ok s, .ok k =>
            External.verifyPure vp prims (cv (bytes m.val)) s (cv (bytes ctx.val)) k
          | _, _ => false) := by
  rw [slhdsa.verify_correct m sig ctx pk hm, Link.slhVerify_eq _ _ _ _ (by simp)]
  rfl

/-! ### Key generation and signing -/

/-- **Rust key generation = VCVio's `keygenInternal`** (FIPS 205 Algorithm 18).  For all three
16-byte seeds, the Rust `slh_keygen_internal` does not panic and returns the FIPS encodings
(`SK.seed ‖ SK.prf ‖ PK.seed ‖ PK.root` and `PK.seed ‖ PK.root`) of the key pair computed by
VCVio's `GeneralScheme.keygenInternal` from the seeds read as nodes.

Deterministic statement only: the seeds are inputs; nothing is said about how the caller samples
them. -/
theorem rust_keygen (sk_seed sk_prf pk_seed : Array U8 16#usize) :
    ∃ sk pk, slhdsa.slh.slh_keygen_internal sk_seed sk_prf pk_seed = ok (sk, pk) ∧
      bytes sk.val =
        skBytes (GeneralScheme.keygenInternal vp prims (node sk_seed) (node sk_prf)
          (node pk_seed)).2 ∧
      bytes pk.val =
        pkBytes (GeneralScheme.keygenInternal vp prims (node sk_seed) (node sk_prf)
          (node pk_seed)).1 := by
  obtain ⟨sk, pk, h, hp⟩ := slhdsa.keygen_correct sk_seed sk_prf pk_seed
  rw [← nd_node, ← nd_node, ← nd_node, Link.keygen_eq] at hp
  exact ⟨sk, pk, h, congrArg Prod.fst hp, congrArg Prod.snd hp⟩

/-- **Rust internal signing = VCVio's `signInternal`** (FIPS 205 Algorithm 19 with
`opt_rand = addrnd`).  For every message under the `Room` bound, every 64-byte secret-key array
(read as the typed key `secretKey sk`, whose encoding is `sk`, see `skBytes_secretKey`) and every
16-byte `addrnd`, the Rust `slh_sign_internal` does not panic and returns the FIPS encoding
`R ‖ SIG_FORS ‖ SIG_HT` of the signature computed by `GeneralScheme.signInternal`.

Deterministic statement only: `addrnd` is an input. No well-formedness of `sk` is assumed. -/
theorem rust_sign_internal (m : Slice U8) (sk : Array U8 64#usize) (addrnd : Array U8 16#usize)
    (hm : Room m.length 152) :
    ∃ sig, slhdsa.slh.slh_sign_internal m sk addrnd = ok sig ∧
      bytes sig.val =
        sigBytes (GeneralScheme.signInternal vp prims (cv (bytes m.val)) (secretKey sk)
          (node addrnd)) := by
  obtain ⟨sig, h, hp⟩ := slhdsa.sign_internal_correct m sk addrnd hm
  rw [← skBytes_secretKey, ← nd_node, Link.sign_eq] at hp
  exact ⟨sig, h, hp⟩

/-- The same for a Rust secret-key array given as the encoding of a typed key `k`. -/
theorem rust_sign_internal' (m : Slice U8) (sk : Array U8 64#usize) (addrnd : Array U8 16#usize)
    (k : SecretKeyCore prims.core) (hk : bytes sk.val = skBytes k) (hm : Room m.length 152) :
    ∃ sig, slhdsa.slh.slh_sign_internal m sk addrnd = ok sig ∧
      bytes sig.val =
        sigBytes (GeneralScheme.signInternal vp prims (cv (bytes m.val)) k (node addrnd)) := by
  obtain ⟨sig, h, hp⟩ := slhdsa.sign_internal_correct m sk addrnd hm
  rw [hk, ← nd_node, Link.sign_eq] at hp
  exact ⟨sig, h, hp⟩

/-- **Rust pure signing = VCVio's `External.signPureWithRandomizer`** (FIPS 205 Algorithm 22 with
caller-supplied randomness).  The Rust `slh_sign` does not panic; it returns `none` exactly when
VCVio's function returns an error (context longer than 255 bytes), and otherwise the FIPS encoding
of VCVio's signature. -/
theorem rust_sign (m ctx : Slice U8) (sk : Array U8 64#usize) (addrnd : Array U8 16#usize)
    (hm : Room m.length 409) :
    ∃ r, slhdsa.slh.slh_sign m ctx sk addrnd = ok r ∧
      r.map (fun v => bytes v.val) =
        (External.signPureWithRandomizer vp prims (cv (bytes m.val)) (cv (bytes ctx.val))
          (secretKey sk) (node addrnd)).toOption.map sigBytes := by
  obtain ⟨r, h, hp⟩ := slhdsa.sign_correct m ctx sk addrnd hm
  refine ⟨r, h, hp.trans ?_⟩
  generalize bytes m.val = msg
  generalize bytes ctx.val = c
  unfold Spec.slhSign External.signPureWithRandomizer
  by_cases hc : c.length > 255
  · rw [ite_eq_left hc]
    have hreq : External.encodePureMessage (cv c) (cv msg) =
        .error (.contextTooLong (cv c).length) := by
      unfold External.encodePureMessage External.encodeMessage
      rw [External.requireContext_eq_error _ (by rw [Link.cv_length]; exact hc)]; rfl
    rw [hreq]; rfl
  · rw [ite_eq_right hc, ← skBytes_secretKey, ← nd_node, Link.sign_eq]
    have hreq := External.encodePureMessage_eq_ok (cv c) (cv msg)
      (by rw [Link.cv_length]; omega)
    have hmm : cv (Spec.withContext msg c) = [0, UInt8.ofNat (cv c).length] ++ cv c ++ cv msg := by
      have h255 : c.length < 256 := by omega
      simp [Spec.withContext, Spec.toByte, cv, List.range_succ]
      rfl
    rw [hreq, hmm]; rfl

/-! ### Summary -/

/-- **End-to-end statement.**  Fix how `opt_rand` and `PK.seed` are sampled (`optRand`,
`pkSeedDist`; arbitrary).  Let `A = internalAlg vp prims optRand pkSeedDist` be FIPS 205
Algorithms 18–20 at SLH-DSA-SHA2-128s as a (probabilistic) signature scheme, and
`R = romScheme prims.core (Equiv.refl _) optRand pkSeedDist` the same scheme with the tweakable
hash, `H_msg` and `PRF_msg` as three oracles.

* `verify`: the Rust `slh_verify_internal` returns `b` such that `A.verify k M s = pure b` for the
  decoded signature `s` and key `k` (`b = false` if the signature has the wrong length).
* `keygen`, `keygen_alg`: `A.keygen` samples three seeds and returns `keygenInternal` of them; on
  given seeds the Rust `slh_keygen_internal` returns the encodings of that key pair.
* `sign`, `sign_alg`: `A.sign` samples `addrnd` from `optRand` and returns `signInternal`; on a
  given `addrnd` the Rust `slh_sign_internal` returns the encoding of that signature.
* `instantiation`: `A` is exactly `R` with its three oracles answered by the SHA-2 functions of
  FIPS 205 §11.2.1 (`romAnswer prims`), its uniform sampling untouched.
* `security`: every adversary against `R`, in the model where those three oracles are independent
  *random oracles*, making at most `qh` hash and `qs` signing queries, wins the SUF-CMA game with
  probability at most `securityBound vp.params (256 ^ 16) 2 1 qh qs`.

**What this does not say.**  The bound is about `R` with random oracles.  No theorem transfers it
to `A` (the SHA-256 instantiation the Rust code computes): that step is the random-oracle
methodology, a modelling assumption.  The Rust-level items are functional (input/output)
statements about the Aeneas translation of the Rust source, for messages satisfying `Room`
(length + 152 fits in `usize` and is below `2^61` bytes); the Rust code only computes the
deterministic cores, so the sampling of seeds and of `addrnd` (uniform secret seeds, `optRand`,
`pkSeedDist`) is the caller's obligation and is not verified.  Timing and other side channels,
the Rust compiler and the Aeneas extraction are outside the statement. -/
structure EndToEnd (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (pkSeedDist : ProbComp prims.PkSeed) : Prop where
  verify : ∀ (m sig : Slice U8) (pk : Array U8 32#usize), Room m.length 152 →
    ∃ b, slhdsa.slh.slh_verify_internal m sig pk = ok b ∧
      match Link.decodeSig (cv (bytes sig.val)), Link.decodePk (cv (bytes pk.val)) with
      | .ok s, .ok k =>
        (internalAlg vp prims optRand pkSeedDist).verify k (cv (bytes m.val)) s = pure b
      | _, _ => b = false
  keygen_alg : (internalAlg vp prims optRand pkSeedDist).keygen = do
    let pkSeed ← pkSeedDist
    let skSeed ← $ᵗ prims.SkSeed
    let skPrf ← $ᵗ prims.SkPrf
    pure (GeneralScheme.keygenInternal vp prims skSeed skPrf pkSeed)
  keygen : ∀ sk_seed sk_prf pk_seed : Array U8 16#usize,
    ∃ sk pk, slhdsa.slh.slh_keygen_internal sk_seed sk_prf pk_seed = ok (sk, pk) ∧
      bytes sk.val =
        skBytes (GeneralScheme.keygenInternal vp prims (node sk_seed) (node sk_prf)
          (node pk_seed)).2 ∧
      bytes pk.val =
        pkBytes (GeneralScheme.keygenInternal vp prims (node sk_seed) (node sk_prf)
          (node pk_seed)).1
  sign_alg : ∀ pk sk msg, (internalAlg vp prims optRand pkSeedDist).sign pk sk msg = do
    let addrnd ← optRand pk
    pure (GeneralScheme.signInternal vp prims msg sk addrnd)
  sign : ∀ (m : Slice U8) (sk : Array U8 64#usize) (addrnd : Array U8 16#usize),
    Room m.length 152 →
    ∃ sig, slhdsa.slh.slh_sign_internal m sk addrnd = ok sig ∧
      bytes sig.val =
        sigBytes (GeneralScheme.signInternal vp prims (cv (bytes m.val)) (secretKey sk)
          (node addrnd))
  instantiation :
    (romScheme (vp := vp) prims.core (Equiv.refl _) optRand pkSeedDist).map
        (simulateQ' (unifFwdAnswerImpl (romAnswer prims))) =
      internalAlg vp prims optRand pkSeedDist
  security : ∀ (adv : StrongUnforgeableAdversary
      (romScheme (vp := vp) prims.core (Equiv.refl _) optRand pkSeedDist)) (qh qs : ℕ),
    adv.RomQueryBound qh qs →
    strongUnforgeableAdvantage (ProbCompRuntime.rom (hashSpec prims.core)) adv ≤
      securityBound vp.params (256 ^ 16) 2 1 qh qs

/-- The verification item of `EndToEnd`, on its own (it does not depend on the key-generation and
signing links). -/
theorem verify_in_alg (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (pkSeedDist : ProbComp prims.PkSeed) (m sig : Slice U8) (pk : Array U8 32#usize)
    (hm : Room m.length 152) :
    ∃ b, slhdsa.slh.slh_verify_internal m sig pk = ok b ∧
      match Link.decodeSig (cv (bytes sig.val)), Link.decodePk (cv (bytes pk.val)) with
      | .ok s, .ok k =>
        (internalAlg vp prims optRand pkSeedDist).verify k (cv (bytes m.val)) s = pure b
      | _, _ => b = false := by
  refine ⟨_, rust_verify_internal m sig pk hm, ?_⟩
  split <;> first | rfl | simp_all

/-- **The end-to-end theorem**: `EndToEnd` holds for every `opt_rand` source and every `PK.seed`
distribution.  See `EndToEnd` for what each item says and, importantly, does not say: the
security bound is for the random-oracle scheme, and is related to the Rust code only through an
identity of programs after instantiating the oracles with SHA-2. -/
theorem end_to_end (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (pkSeedDist : ProbComp prims.PkSeed) : EndToEnd optRand pkSeedDist where
  verify := verify_in_alg optRand pkSeedDist
  keygen_alg := rfl
  keygen := rust_keygen
  sign_alg := fun _ _ _ => rfl
  sign := rust_sign_internal
  instantiation := Link.romScheme_map_romAnswer_128s optRand pkSeedDist
  security := fun adv _ _ hadv =>
    Link.security_128s (Equiv.refl _) optRand pkSeedDist adv hadv

/-- **The verification-only end-to-end theorem** (independent of the key-generation and signing
links): the Rust verifier computes the `verify` of the scheme `romScheme …` of the security theorem
run with its oracles answered by SHA-2, and that scheme, with random oracles, satisfies the
SUF-CMA bound.  Same caveat as `EndToEnd`: nothing transfers the bound to SHA-256. -/
theorem end_to_end_verify (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (pkSeedDist : ProbComp prims.PkSeed) :
    (∀ (m sig : Slice U8) (pk : Array U8 32#usize), Room m.length 152 →
      ∃ b, slhdsa.slh.slh_verify_internal m sig pk = ok b ∧
        match Link.decodeSig (cv (bytes sig.val)), Link.decodePk (cv (bytes pk.val)) with
        | .ok s, .ok k =>
          simulateQ (unifFwdAnswerImpl (romAnswer prims))
            ((romScheme (vp := vp) prims.core (Equiv.refl _) optRand pkSeedDist).verify k
              (cv (bytes m.val)) s) = (pure b : ProbComp Bool)
        | _, _ => b = false) ∧
    (∀ (adv : StrongUnforgeableAdversary
        (romScheme (vp := vp) prims.core (Equiv.refl _) optRand pkSeedDist)) (qh qs : ℕ),
      adv.RomQueryBound qh qs →
      strongUnforgeableAdvantage (ProbCompRuntime.rom (hashSpec prims.core)) adv ≤
        securityBound vp.params (256 ^ 16) 2 1 qh qs) := by
  refine ⟨fun m sig pk hm => ⟨_, rust_verify_internal m sig pk hm, ?_⟩,
    fun adv _ _ hadv => Link.security_128s (Equiv.refl _) optRand pkSeedDist adv hadv⟩
  split
  · exact Link.romScheme_verify_eq (Equiv.refl _) optRand pkSeedDist _ _ _
  · simp_all

end E2E

#print axioms E2E.nd_node
#print axioms E2E.skBytes_secretKey
#print axioms E2E.rust_verify_internal
#print axioms E2E.rust_verify_internal'
#print axioms E2E.rust_verify
#print axioms E2E.rust_keygen
#print axioms E2E.rust_sign_internal
#print axioms E2E.rust_sign_internal'
#print axioms E2E.rust_sign
#print axioms E2E.verify_in_alg
#print axioms E2E.end_to_end
#print axioms E2E.end_to_end_verify
