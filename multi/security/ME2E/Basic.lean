import Slhdsa
import MLink.Sign
import MReduction.Instances
import Reduction.Bytes

/-!
# End to end, generic part: `Spec` on byte strings = the byte-level cores of the scheme in the game

For every `S : MLink.Sha2Set` (the six SHA-2 parameter sets of FIPS 205):

* `wire`: Rust bytes (Aeneas `U8`) as the scheme's bytes (`UInt8`), a length-preserving bijection
  (`wire_length`, `wire_injective`, `wire_surjective`);
* `node S x`: an `n`-byte Rust array read as a VCVio node `Bytes S.vp.params.n` (`nd_node`);
* `keygen_transfer`, `sign_transfer`, `verify_transfer`, `signPure_transfer`,
  `verifyPure_transfer`: an output that equals `Spec.slhKeygenInternal S.spec` /
  `slhSignInternal` / `slhVerifyInternal` / `slhSign` / `slhVerify` on the `slhdsa.bytes` of the
  inputs equals `Reduction.byteKeygen S.vp S.prims (MReduction.codec S)` / `byteSign` /
  `byteVerify` / `byteSignPure` / `byteVerifyPure` on their `wire` bytes.  These are what the
  per-set files (`ME2E/Sha2_*.lean`) combine with the Rust refinement theorems
  `slhdsa.<set>.*_correct`;
* `BytesScheme`, `PureBytesScheme` (`bytes_scheme`, `pure_bytes_scheme`): the byte-level schemes
  `Reduction.bytesAlg` / `pureBytesAlg` at the set are "sample, then apply the cores"; behaviour
  on malformed keys; completeness.

One proof for all six sets; the only per-set inputs are the numeric facts of `MLink.Sha2Set`.
-/

namespace ME2E

open Aeneas Aeneas.Std Result
open SLHDSA SLHDSA.Concrete SLHDSA.Security OracleComp OracleSpec SignatureAlg ENNReal
open slhdsa (bytes Room)
open MLink (Sha2Set cv sp nd)
open MReduction (codec)
open Reduction (byteKeygen byteSign byteVerify byteSignPure byteVerifyPure bytesAlg pureBytesAlg)

/-! ### Byte representations -/

/-- The bytes of a Rust slice, array or vector (a list of Aeneas `U8`) as a list of Lean `UInt8`,
the byte type of the scheme: each `U8` is read through its bit-vector (`slhdsa.bytes`, then
`MLink.cv`).  A length-preserving bijection (`wire_length`, `wire_injective`,
`wire_surjective`). -/
def wire (l : List U8) : List SLHDSA.Byte := cv (bytes l)

@[simp] theorem wire_length (l : List U8) : (wire l).length = l.length := by simp [wire, bytes]

theorem wire_injective : Function.Injective wire := by
  intro a b h
  apply (slhdsa.bytes_inj a b).1
  have := congrArg sp h
  simpa [wire] using this

theorem wire_surjective : Function.Surjective wire := by
  intro l
  refine ⟨l.map fun b => (⟨b.toBitVec⟩ : U8), ?_⟩
  simp [wire, cv, bytes, Function.comp_def]

@[simp] theorem bytes_length (l : List U8) : (bytes l).length = l.length := by simp [bytes]

/-- Read specification bytes as an `n`-byte VCVio node (missing bytes read as `0`; only used on
`n`-byte inputs, where it is the inverse of `MLink.nd`, see `nd_nodeOfBytes`). -/
def nodeOfBytes (n : ℕ) (l : Spec.Bytes) : Bytes n :=
  Vector.ofFn fun j : Fin n => UInt8.ofBitVec (l.getD j.val 0)

/-- On `n` bytes, `nodeOfBytes n` inverts `MLink.nd`. -/
theorem nd_nodeOfBytes (n : ℕ) (l : Spec.Bytes) (h : l.length = n) : nd (nodeOfBytes n l) = l := by
  apply List.ext_getElem
  · simp [h]
  · intro i h1 h2
    simp [nd, sp, nodeOfBytes, h2]

variable (S : Sha2Set)

/-- A Rust byte array read as a node of the set `S` (a seed, or `addrnd`); meaningful for arrays
of `n = S.vp.params.n` bytes (`nd_node`), which is how it is used (`n = 16, 24, 32`). -/
def node {N : Usize} (x : Array U8 N) : S.Node := nodeOfBytes S.vp.params.n (bytes x.val)

/-- The node `node S x` has exactly the bytes of the `n`-byte array `x`. -/
theorem nd_node {N : Usize} (x : Array U8 N) (h : N.val = S.vp.params.n) :
    nd (node S x) = bytes x.val :=
  nd_nodeOfBytes _ _ (by rw [bytes_length, ← h]; exact x.property)

/-! ### `Spec` = the byte-level cores -/

/-- **Key generation**: a pair `(sk, pk)` that is `Spec.slhKeygenInternal S.spec` of three
`n`-byte seeds is, on wire bytes, `byteKeygen` (which returns `(pk, sk)`) at the seeds read as
nodes. -/
theorem keygen_transfer {N : Usize} (hN : N.val = S.vp.params.n)
    (sk_seed sk_prf pk_seed : Array U8 N) (sk pk : List U8)
    (h : (bytes sk, bytes pk) =
      Spec.slhKeygenInternal S.spec (bytes sk_seed.val) (bytes sk_prf.val) (bytes pk_seed.val)) :
    (wire pk, wire sk) =
      byteKeygen S.vp S.prims (codec S) (node S sk_seed) (node S sk_prf) (node S pk_seed) := by
  have e := MLink.keygen_eq_bytes S (node S sk_seed) (node S sk_prf) (node S pk_seed)
  rw [nd_node S _ hN, nd_node S _ hN, nd_node S _ hN, ← h] at e
  exact e

/-- **Internal signing**: for a `4n`-byte secret key and an `n`-byte `addrnd`, the wire bytes of
`Spec.slhSignInternal S.spec` are `byteSign`. -/
theorem sign_transfer {N : Usize} (hN : N.val = S.vp.params.n) (m sk sig : List U8)
    (addrnd : Array U8 N) (hsk : sk.length = 4 * S.spec.n)
    (h : bytes sig = Spec.slhSignInternal S.spec (bytes m) (bytes sk) (bytes addrnd.val)) :
    wire sig = byteSign S.vp S.prims (codec S) (wire m) (wire sk) (node S addrnd) := by
  obtain ⟨k, hk, -, e⟩ := MLink.sign_eq_bytes S (bytes m) (bytes sk) (by simpa using hsk)
    (node S addrnd)
  rw [nd_node S _ hN, ← h] at e
  have hk' : decodeSecretKey (codec S) (wire sk) = .ok k := hk
  simp only [byteSign, hk']
  exact e

/-- The signature returned by `byteSign` on a `4n`-byte secret key has `S.spec.sigBytes` bytes. -/
theorem byteSign_length (m sk : List SLHDSA.Byte) (addrnd : S.prims.Y)
    (hsk : sk.length = 4 * S.spec.n) :
    (byteSign S.vp S.prims (codec S) m sk addrnd).length = S.spec.sigBytes := by
  obtain ⟨k, hk, -⟩ := MLink.decodeSk_ok S (sp sk) (by simpa using hsk)
  rw [MLink.cv_sp] at hk
  have hk' : decodeSecretKey (codec S) sk = .ok k := hk
  simp only [byteSign, hk']
  rw [encodeSignature_length, S.signatureBytes_eq]

/-- **Internal verification**: for a `2n`-byte public key (and any byte strings as message and
signature), `Spec.slhVerifyInternal S.spec` is `byteVerify`. -/
theorem verify_transfer (m sig pk : List U8) (hpk : pk.length = 2 * S.spec.n) :
    Spec.slhVerifyInternal S.spec (bytes m) (bytes sig) (bytes pk) =
      byteVerify S.vp S.prims (codec S) (wire m) (wire sig) (wire pk) := by
  rw [MLink.verify_eq S _ _ _ (by simpa using hpk)]
  have e1 : decodeSignature S.vp (codec S) (wire sig) = MLink.decodeSig S (cv (bytes sig)) := rfl
  have e2 : decodePublicKey (codec S) (wire pk) = MLink.decodePk S (cv (bytes pk)) := rfl
  unfold byteVerify
  rw [e1, e2]
  cases MLink.decodeSig S (cv (bytes sig)) <;> cases MLink.decodePk S (cv (bytes pk)) <;> rfl

/-- **Pure signing**: for a `4n`-byte secret key and an `n`-byte `addrnd`, `Spec.slhSign S.spec`
is `byteSignPure` (`none` exactly for a context longer than 255 bytes). -/
theorem signPure_transfer {N : Usize} (hN : N.val = S.vp.params.n) (m ctx sk : List U8)
    (addrnd : Array U8 N) (hsk : sk.length = 4 * S.spec.n) (r : Option (List U8))
    (h : r.map bytes = Spec.slhSign S.spec (bytes m) (bytes ctx) (bytes sk) (bytes addrnd.val)) :
    r.map wire =
      byteSignPure S.vp S.prims (codec S) (wire m) (wire ctx) (wire sk) (node S addrnd) := by
  obtain ⟨k, hk, -, e⟩ := MLink.slhSign_eq_bytes S (bytes m) (bytes ctx) (bytes sk)
    (by simpa using hsk) (node S addrnd)
  rw [nd_node S _ hN, ← h] at e
  have hk' : decodeSecretKey (codec S) (wire sk) = .ok k := hk
  simp only [byteSignPure, hk']
  have h1 : r.map wire = (r.map bytes).map cv := by cases r <;> rfl
  rw [h1]
  exact e

/-- **Pure verification**: for a `2n`-byte public key, `Spec.slhVerify S.spec` is
`byteVerifyPure`. -/
theorem verifyPure_transfer (m sig ctx pk : List U8) (hpk : pk.length = 2 * S.spec.n) :
    Spec.slhVerify S.spec (bytes m) (bytes sig) (bytes ctx) (bytes pk) =
      byteVerifyPure S.vp S.prims (codec S) (wire m) (wire sig) (wire ctx) (wire pk) := by
  rw [MLink.slhVerify_eq S _ _ _ _ (by simpa using hpk)]
  have e1 : decodeSignature S.vp (codec S) (wire sig) = MLink.decodeSig S (cv (bytes sig)) := rfl
  have e2 : decodePublicKey (codec S) (wire pk) = MLink.decodePk S (cv (bytes pk)) := rfl
  unfold byteVerifyPure
  rw [e1, e2]
  cases MLink.decodeSig S (cv (bytes sig)) <;> cases MLink.decodePk S (cv (bytes pk)) <;> rfl

/-! ### Parsing of fixed-length keys -/

/-- Every `2n`-byte string is the wire encoding of a typed public key. -/
theorem decodePk_wire (pk : List U8) (hpk : pk.length = 2 * S.spec.n) :
    ∃ k, decodePublicKey (codec S) (wire pk) = .ok k :=
  let ⟨k, hk, _⟩ := MLink.decodePk_ok S (bytes pk) (by simpa using hpk)
  ⟨k, hk⟩

/-- Every `4n`-byte string is the wire encoding of a typed secret key (no well-formedness is
checked: the `PK.seed`, `PK.root` stored in it are used as they are). -/
theorem decodeSk_wire (sk : List U8) (hsk : sk.length = 4 * S.spec.n) :
    ∃ k, decodeSecretKey (codec S) (wire sk) = .ok k :=
  let ⟨k, hk, _⟩ := MLink.decodeSk_ok S (bytes sk) (by simpa using hsk)
  ⟨k, hk⟩

/-- Key and signature lengths of the set in the scheme's own terms (`2n`, `4n`, `sigBytes`). -/
theorem key_lengths :
    S.vp.params.publicKeyBytes = 2 * S.spec.n ∧ S.vp.params.secretKeyBytes = 4 * S.spec.n ∧
      S.vp.params.signatureBytes = S.spec.sigBytes :=
  ⟨by rw [Params.publicKeyBytes, S.n_eq], by rw [Params.secretKeyBytes, S.n_eq],
    S.signatureBytes_eq⟩

/-- The coefficient of the undetectability term is `14` at every set. -/
theorem w_sub_two : S.vp.params.w - 2 = 14 := by rw [S.w_sixteen]

/-! ### The byte-level schemes -/

/-- On a public key that is not `2n` bytes, signing in the byte-level scheme returns `[]`
(nothing is sampled). -/
theorem sign_bad_pk (optRand : PublicKeyCore S.prims.core → ProbComp S.prims.Y)
    (pkSeedDist : ProbComp S.prims.PkSeed) (pk sk m : List SLHDSA.Byte)
    (h : pk.length ≠ 2 * S.spec.n) :
    (bytesAlg S.vp S.prims (codec S) optRand pkSeedDist).sign pk sk m = pure [] := by
  have : decodePublicKey (codec S) pk =
      .error (.invalidLength S.vp.params.publicKeyBytes pk.length) :=
    WireCodec.decode_eq_error_of_length_ne _ _ (by rw [(key_lengths S).1]; exact h)
  simp only [bytesAlg, this]

/-- **The byte-level internal scheme `B = Reduction.bytesAlg S.vp S.prims (codec S) optRand
pkSeedDist`** (public keys, secret keys, messages, signatures: `List UInt8`) is "sample, then
apply `byteKeygen` / `byteSign` / `byteVerify`" (`keygen_alg`, `sign_alg`, `verify_alg`); on a
public key that is not `2n` bytes signing returns `[]` (`sign_alg_bad`); `B` is perfectly complete
(`correct`). -/
structure BytesScheme (optRand : PublicKeyCore S.prims.core → ProbComp S.prims.Y)
    (pkSeedDist : ProbComp S.prims.PkSeed) : Prop where
  keygen_alg : (bytesAlg S.vp S.prims (codec S) optRand pkSeedDist).keygen = do
    let pkSeed ← pkSeedDist
    let skSeed ← $ᵗ S.prims.SkSeed
    let skPrf ← $ᵗ S.prims.SkPrf
    pure (byteKeygen S.vp S.prims (codec S) skSeed skPrf pkSeed)
  sign_alg : ∀ (pk sk m : List SLHDSA.Byte) (k : PublicKeyCore S.prims.core),
    MLink.decodePk S pk = .ok k →
    (bytesAlg S.vp S.prims (codec S) optRand pkSeedDist).sign pk sk m = do
      let addrnd ← optRand k
      pure (byteSign S.vp S.prims (codec S) m sk addrnd)
  sign_alg_bad : ∀ (pk sk m : List SLHDSA.Byte), pk.length ≠ 2 * S.spec.n →
    (bytesAlg S.vp S.prims (codec S) optRand pkSeedDist).sign pk sk m = pure []
  verify_alg : ∀ pk m sig : List SLHDSA.Byte,
    (bytesAlg S.vp S.prims (codec S) optRand pkSeedDist).verify pk m sig =
      pure (byteVerify S.vp S.prims (codec S) m sig pk)
  correct : (bytesAlg S.vp S.prims (codec S) optRand pkSeedDist).PerfectlyComplete
    ProbCompRuntime.probComp

/-- `BytesScheme` holds at every set, for every `opt_rand` source and `PK.seed` distribution. -/
theorem bytes_scheme (optRand : PublicKeyCore S.prims.core → ProbComp S.prims.Y)
    (pkSeedDist : ProbComp S.prims.PkSeed) : BytesScheme S optRand pkSeedDist where
  keygen_alg := rfl
  sign_alg := fun pk sk m k hk => by
    have hk' : decodePublicKey (codec S) pk = .ok k := hk
    simp only [bytesAlg, hk']
  sign_alg_bad := sign_bad_pk S optRand pkSeedDist
  verify_alg := fun _ _ _ => rfl
  correct := Reduction.bytesAlg_perfectlyComplete optRand pkSeedDist

/-- **The byte-level external pure scheme `X = Reduction.pureBytesAlg S.vp S.prims (codec S)
optRand pkSeedDist`** (messages are `(message, context)` pairs of byte strings; signatures are
`Option (List UInt8)`) is "sample, then apply `byteKeygen` / `byteSignPure` / `byteVerifyPure`";
for a context longer than 255 bytes signing returns `none` without sampling, which is also the
value of `byteSignPure` on every `addrnd`; `none` is rejected; for contexts of at most 255 bytes
the keygen–sign–verify run accepts with probability 1. -/
structure PureBytesScheme (optRand : PublicKeyCore S.prims.core → ProbComp S.prims.Y)
    (pkSeedDist : ProbComp S.prims.PkSeed) : Prop where
  keygen_alg : (pureBytesAlg S.vp S.prims (codec S) optRand pkSeedDist).keygen = do
    let pkSeed ← pkSeedDist
    let skSeed ← $ᵗ S.prims.SkSeed
    let skPrf ← $ᵗ S.prims.SkPrf
    pure (byteKeygen S.vp S.prims (codec S) skSeed skPrf pkSeed)
  sign_alg : ∀ (pk sk m ctx : List SLHDSA.Byte) (k : PublicKeyCore S.prims.core),
    MLink.decodePk S pk = .ok k → ctx.length ≤ 255 →
    (pureBytesAlg S.vp S.prims (codec S) optRand pkSeedDist).sign pk sk (m, ctx) = do
      let addrnd ← optRand k
      pure (byteSignPure S.vp S.prims (codec S) m ctx sk addrnd)
  sign_alg_tooLong : ∀ (pk sk m ctx : List SLHDSA.Byte), 255 < ctx.length →
    (pureBytesAlg S.vp S.prims (codec S) optRand pkSeedDist).sign pk sk (m, ctx) = pure none ∧
      ∀ addrnd, byteSignPure S.vp S.prims (codec S) m ctx sk addrnd = none
  verify_alg : ∀ pk m ctx sig : List SLHDSA.Byte,
    (pureBytesAlg S.vp S.prims (codec S) optRand pkSeedDist).verify pk (m, ctx) (some sig) =
        pure (byteVerifyPure S.vp S.prims (codec S) m sig ctx pk) ∧
      (pureBytesAlg S.vp S.prims (codec S) optRand pkSeedDist).verify pk (m, ctx) none =
        pure false
  correct : ∀ m ctx : List SLHDSA.Byte, ctx.length ≤ 255 →
    ProbCompRuntime.probComp.evalDist (do
      let (pk, sk) ← (pureBytesAlg S.vp S.prims (codec S) optRand pkSeedDist).keygen
      let sig ← (pureBytesAlg S.vp S.prims (codec S) optRand pkSeedDist).sign pk sk (m, ctx)
      (pureBytesAlg S.vp S.prims (codec S) optRand pkSeedDist).verify pk (m, ctx) sig) {true} = 1

/-- `PureBytesScheme` holds at every set. -/
theorem pure_bytes_scheme (optRand : PublicKeyCore S.prims.core → ProbComp S.prims.Y)
    (pkSeedDist : ProbComp S.prims.PkSeed) : PureBytesScheme S optRand pkSeedDist where
  keygen_alg := rfl
  sign_alg := fun pk sk m ctx k hk hc => by
    have hk' : decodePublicKey (codec S) pk = .ok k := hk
    simp only [pureBytesAlg, hk', hc, ite_true]
  sign_alg_tooLong := fun pk sk m ctx hc => by
    refine ⟨?_, fun addrnd => Reduction.byteSignPure_tooLong m ctx sk addrnd hc⟩
    have : ¬ ctx.length ≤ 255 := by omega
    simp only [pureBytesAlg, this, ite_false]
  verify_alg := fun _ _ _ _ => ⟨rfl, rfl⟩
  correct := fun m ctx hc => Reduction.pureBytesAlg_complete optRand pkSeedDist m ctx hc

end ME2E

#print axioms ME2E.wire_injective
#print axioms ME2E.wire_surjective
#print axioms ME2E.nd_node
#print axioms ME2E.keygen_transfer
#print axioms ME2E.sign_transfer
#print axioms ME2E.byteSign_length
#print axioms ME2E.verify_transfer
#print axioms ME2E.signPure_transfer
#print axioms ME2E.verifyPure_transfer
#print axioms ME2E.decodePk_wire
#print axioms ME2E.decodeSk_wire
#print axioms ME2E.bytes_scheme
#print axioms ME2E.pure_bytes_scheme
