import HashSig.SLHDSA.Concrete.Codec
import HashSig.SLHDSA.GeneralScheme
import Spec

/-!
# Common vocabulary for linking `Spec` (FIPS 205, six SHA-2 parameter sets) to VCVio

`Spec` (compiled in place from `multi/lean`) is parameterised by `Spec.Params` and works on
`List (BitVec 8)`; VCVio is parameterised by `SLHDSA.Params` and works on `UInt8` lists / vectors /
`ByteArray`s.  `Sha2Set` enumerates the six SHA-2 parameter sets of FIPS 205 Table 2 and maps each
to its `Spec.Params` row (`Sha2Set.spec`) and to VCVio's `FipsParameterSet` (`Sha2Set.fips`).
Every linking lemma is stated for an arbitrary `S : Sha2Set` as "the `Spec` reading of the VCVio
value equals the `Spec` function at `S.spec` applied to the `Spec` readings of the VCVio inputs".
Numeric facts relating the two parameter records are proved by `cases S <;> decide`/`rfl`.
-/

namespace MLink

open SLHDSA SLHDSA.Concrete

/-- The six SHA-2 parameter sets of FIPS 205 (Table 2). -/
inductive Sha2Set where
  | s128s | s128f | s192s | s192f | s256s | s256f
deriving DecidableEq, Repr

namespace Sha2Set

/-- VCVio's name of the set. -/
def fips : Sha2Set → FipsParameterSet
  | s128s => .SLHDSA_SHA2_128s
  | s128f => .SLHDSA_SHA2_128f
  | s192s => .SLHDSA_SHA2_192s
  | s192f => .SLHDSA_SHA2_192f
  | s256s => .SLHDSA_SHA2_256s
  | s256f => .SLHDSA_SHA2_256f

/-- The row of Table 2 in our parameterised transcription. -/
def spec : Sha2Set → Spec.Params
  | s128s => Spec.sha2_128s
  | s128f => Spec.sha2_128f
  | s192s => Spec.sha2_192s
  | s192f => Spec.sha2_192f
  | s256s => Spec.sha2_256s
  | s256f => Spec.sha2_256f

/-- VCVio's validated parameters of the set. -/
abbrev vp (S : Sha2Set) : ValidatedParams := S.fips.validatedParams

/-- VCVio's executable FIPS SHA-2 primitive bundle at the set (`= approvedPrimitives S.fips`,
`prims_eq_approved`). -/
abbrev prims (S : Sha2Set) : Primitives S.vp.params := sha2Primitives S.vp.params

theorem prims_eq_approved (S : Sha2Set) : S.prims = approvedPrimitives S.fips := by
  cases S <;> rfl

/-- `n`-byte nodes of the bundle.  All of `S.prims.Y`, `S.prims.PkSeed`, `S.prims.SkSeed`,
`S.prims.SkPrf` are definitionally `S.Node`. -/
abbrev Node (S : Sha2Set) : Type := Bytes S.vp.params.n

example (S : Sha2Set) : S.prims.Y = S.Node := rfl
example (S : Sha2Set) : S.prims.PkSeed = S.Node := rfl
example (S : Sha2Set) : S.prims.SkSeed = S.Node := rfl
example (S : Sha2Set) : S.prims.SkPrf = S.Node := rfl

/-- The row is valid in the sense of `multi/lean` (the hypothesis of the Rust refinement). -/
theorem spec_valid (S : Sha2Set) : S.spec.Valid := by
  cases S
  exacts [Spec.sha2_128s_valid, Spec.sha2_128f_valid, Spec.sha2_192s_valid, Spec.sha2_192f_valid,
    Spec.sha2_256s_valid, Spec.sha2_256f_valid]

/-! ### The two parameter records agree (all by evaluation on the six sets) -/

theorem n_eq (S : Sha2Set) : S.vp.params.n = S.spec.n := by cases S <;> rfl
theorem h_eq (S : Sha2Set) : S.vp.params.h = S.spec.h := by cases S <;> rfl
theorem d_eq (S : Sha2Set) : S.vp.params.d = S.spec.d := by cases S <;> rfl
theorem hp_eq (S : Sha2Set) : S.vp.params.hp = S.spec.hp := by cases S <;> rfl
theorem a_eq (S : Sha2Set) : S.vp.params.a = S.spec.a := by cases S <;> rfl
theorem k_eq (S : Sha2Set) : S.vp.params.k = S.spec.k := by cases S <;> rfl
theorem lgw_eq (S : Sha2Set) : S.vp.params.lgw = S.spec.lgw := by cases S <;> rfl
theorem lgw_four (S : Sha2Set) : S.vp.params.lgw = 4 := by cases S <;> rfl
theorem w_eq (S : Sha2Set) : S.vp.params.w = S.spec.w := by cases S <;> rfl
theorem w_sixteen (S : Sha2Set) : S.vp.params.w = 16 := by cases S <;> rfl
theorem len1_eq (S : Sha2Set) : S.vp.params.len1 = S.spec.len1 := by cases S <;> rfl
theorem len2_eq (S : Sha2Set) : S.vp.params.len2 = S.spec.len2 := by cases S <;> decide
theorem len2_three (S : Sha2Set) : S.vp.params.len2 = 3 := by cases S <;> decide
theorem len_eq (S : Sha2Set) : S.vp.params.len = S.spec.len := by cases S <;> decide
theorem len_val (S : Sha2Set) : S.vp.params.len = 2 * S.vp.params.n + 3 := by cases S <;> decide
theorem m_eq (S : Sha2Set) : S.vp.params.m = S.spec.m := by cases S <;> decide
theorem digestBytes_eq (S : Sha2Set) : S.vp.params.digestBytes = S.spec.mdBytes := by
  cases S <;> rfl
theorem treeIdxBytes_eq (S : Sha2Set) : S.vp.params.treeIdxBytes = S.spec.treeBytes := by
  cases S <;> decide
theorem leafIdxBytes_eq (S : Sha2Set) : S.vp.params.leafIdxBytes = S.spec.leafBytes := by
  cases S <;> decide
theorem signatureBytes_eq (S : Sha2Set) : S.vp.params.signatureBytes = S.spec.sigBytes := by
  cases S <;> decide
theorem h_div_d (S : Sha2Set) : S.spec.h / S.spec.d = S.spec.hp := by cases S <;> decide
/-- `n ∈ {16, 24, 32}`; `n = 16` selects SHA-256 everywhere, otherwise SHA-512 for
`H`, `T_l`, `H_msg`, `PRF_msg`. -/
theorem n_cases (S : Sha2Set) :
    S.vp.params.n = 16 ∨ S.vp.params.n = 24 ∨ S.vp.params.n = 32 := by cases S <;> decide
/-- Every hypertree layer index fits one byte and every tree index fits eight bytes
(`h − h' ≤ 64`; equality at 256f). -/
theorem tree_bits_le (S : Sha2Set) : S.vp.params.h - S.vp.params.hp ≤ 64 := by cases S <;> decide
theorem d_lt (S : Sha2Set) : S.vp.params.d < 256 := by cases S <;> decide

end Sha2Set

/-! ### Byte readings -/

/-- Read VCVio bytes as spec bytes. -/
def sp (l : List UInt8) : Spec.Bytes := l.map UInt8.toBitVec
/-- Read spec bytes as VCVio bytes. -/
def cv (l : Spec.Bytes) : List UInt8 := l.map UInt8.ofBitVec
/-- Read a `ByteArray` as spec bytes. -/
def spA (b : ByteArray) : Spec.Bytes := sp b.data.toList
/-- Read a fixed-width byte vector (a node, a seed, a digest) as spec bytes. -/
def nd {n : ℕ} (y : Bytes n) : Spec.Bytes := sp y.toList

@[simp] theorem sp_cv (l : Spec.Bytes) : sp (cv l) = l := by
  simp [sp, cv, Function.comp_def]
@[simp] theorem cv_sp (l : List UInt8) : cv (sp l) = l := by
  simp [sp, cv, Function.comp_def]
@[simp] theorem sp_length (l : List UInt8) : (sp l).length = l.length := by simp [sp]
@[simp] theorem cv_length (l : Spec.Bytes) : (cv l).length = l.length := by simp [cv]
@[simp] theorem sp_append (a b : List UInt8) : sp (a ++ b) = sp a ++ sp b := by simp [sp]
@[simp] theorem sp_nil : sp [] = [] := rfl
@[simp] theorem sp_take (l : List UInt8) (k : Nat) : sp (l.take k) = (sp l).take k := by
  simp [sp, List.map_take]
@[simp] theorem sp_drop (l : List UInt8) (k : Nat) : sp (l.drop k) = (sp l).drop k := by
  simp [sp, List.map_drop]
theorem sp_injective : Function.Injective sp := fun a b h => by
  have := congrArg cv h; simpa using this
@[simp] theorem nd_length {n : ℕ} (y : Bytes n) : (nd y).length = n := by simp [nd]
theorem nd_injective {n : ℕ} : Function.Injective (nd (n := n)) := fun a b h => by
  have := sp_injective h
  exact Vector.toList_inj.mp this
@[simp] theorem spA_append (a b : ByteArray) : spA (a ++ b) = spA a ++ spA b := by
  simp [spA]
@[simp] theorem spA_mk (l : List UInt8) : spA (ByteArray.mk l.toArray) = sp l := rfl

/-- Field-wise reading of a VCVio address as a spec address. -/
def adr (a : SLHDSA.Adrs) : Spec.Adrs := ⟨a.layer, a.tree, a.type, a.word1, a.word2, a.word3⟩

/-- The checked SHA-2 `ADRSc` domain (`Sha2Address`): canonical, one-byte layer, eight-byte tree.
Outside it VCVio's `sha2AdrsKey` is a fallback key rather than the truncating compression of
`Spec.Adrs.compress`, so every hash-level lemma carries this hypothesis.  Parameter-independent. -/
def Dom (a : SLHDSA.Adrs) : Prop :=
  a.isCanonical = true ∧ Adrs.Fits 1 a.layer = true ∧ Adrs.Fits 8 a.tree = true

/-- A hypertree base address `(layer, tree)` in the SHA-2 domain. -/
def BaseDom (a : SLHDSA.Adrs) : Prop := a.layer < 256 ∧ a.tree < 2 ^ 64

/-! ### Flat byte readings of the typed signature components (FIPS 205 Fig. 17 order) -/

/-- Concatenated spec reading of a list of nodes. -/
def nds {n : ℕ} (ys : List (Bytes n)) : Spec.Bytes := ys.flatMap nd

variable (S : Sha2Set)

/-- `sig_WOTS ‖ AUTH`. -/
def xmssBytes (s : XmssSig S.vp.params S.prims) : Spec.Bytes :=
  nds s.wots.toList ++ nds s.auth.toList

/-- `SIG_HT`. -/
def htBytes (s : HtSigCore S.vp.params S.prims.core) : Spec.Bytes :=
  s.toList.flatMap (xmssBytes S)

/-- `SIG_FORS`: per tree, the revealed secret then the authentication path. -/
def forsBytes (s : ForsSigCore S.vp.params S.prims.core) : Spec.Bytes :=
  s.toList.flatMap fun t => nd t.sk ++ nds t.auth.toList

/-- `R ‖ SIG_FORS ‖ SIG_HT`. -/
def sigBytes (s : GeneralScheme.SignatureCore S.vp S.prims.core) : Spec.Bytes :=
  nd s.randomness ++ forsBytes S s.fors ++ htBytes S s.hypertree

/-- `PK.seed ‖ PK.root`. -/
def pkBytes (k : PublicKeyCore S.prims.core) : Spec.Bytes := nd k.pkSeed ++ nd k.pkRoot

end MLink
