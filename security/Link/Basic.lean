import HashSig.SLHDSA.Concrete.Codec
import HashSig.SLHDSA.GeneralScheme
import Spec

/-!
# Common vocabulary for linking `Spec` (our FIPS 205 transcription) to VCVio's SLH-DSA-SHA2-128s

`Spec` works on `List (BitVec 8)`; VCVio on `UInt8` lists / vectors / `ByteArray`s.  Every linking
lemma is stated as "the `Spec` reading of the VCVio value equals the `Spec` function applied to the
`Spec` readings of the VCVio inputs".
-/

namespace Link

open SLHDSA SLHDSA.Concrete

/-- The parameter set this development is about. -/
abbrev S128 : FipsParameterSet := .SLHDSA_SHA2_128s
/-- Its validated parameters (`n=16, h=63, d=7, h'=9, a=12, k=14, lg w=4`). -/
abbrev vp : ValidatedParams := S128.validatedParams
/-- VCVio's executable FIPS SHA-2 primitive bundle at SLH-DSA-SHA2-128s
(definitionally `approvedPrimitives S128`). -/
abbrev prims : Primitives vp.params := sha2Primitives vp.params

theorem prims_eq_approved : prims = approvedPrimitives S128 := rfl

/-- `n`-byte nodes of the bundle. All of `prims.Y`, `prims.PkSeed`, `prims.SkSeed`, `prims.SkPrf`
are definitionally `Node`. -/
abbrev Node : Type := Bytes 16

example : prims.Y = Node := rfl
example : prims.PkSeed = Node := rfl

/-- Read VCVio bytes as spec bytes. -/
def sp (l : List UInt8) : Spec.Bytes := l.map UInt8.toBitVec
/-- Read spec bytes as VCVio bytes. -/
def cv (l : Spec.Bytes) : List UInt8 := l.map UInt8.ofBitVec
/-- Read a `ByteArray` as spec bytes. -/
def spA (b : ByteArray) : Spec.Bytes := sp b.data.toList
/-- Read a node as spec bytes. -/
def nd (y : Node) : Spec.Bytes := sp y.toList

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
@[simp] theorem nd_length (y : Node) : (nd y).length = 16 := by simp [nd]
theorem nd_injective : Function.Injective nd := fun a b h => by
  have := sp_injective h
  exact Vector.toList_inj.mp this
@[simp] theorem spA_append (a b : ByteArray) : spA (a ++ b) = spA a ++ spA b := by
  simp [spA]
@[simp] theorem spA_mk (l : List UInt8) : spA (ByteArray.mk l.toArray) = sp l := rfl

/-- Field-wise reading of a VCVio address as a spec address. -/
def adr (a : SLHDSA.Adrs) : Spec.Adrs := ⟨a.layer, a.tree, a.type, a.word1, a.word2, a.word3⟩

/-- The checked SHA-2 `ADRSc` domain (`Sha2Address`): canonical, one-byte layer, eight-byte tree.
Outside it VCVio's `sha2AdrsKey` is a fallback key rather than the truncating compression of
`Spec.Adrs.compress`, so every hash-level lemma carries this hypothesis. -/
def Dom (a : SLHDSA.Adrs) : Prop :=
  a.isCanonical = true ∧ Adrs.Fits 1 a.layer = true ∧ Adrs.Fits 8 a.tree = true

/-- A hypertree base address `(layer, tree)` in the SHA-2 domain. -/
def BaseDom (a : SLHDSA.Adrs) : Prop := a.layer < 256 ∧ a.tree < 2 ^ 64

/-! ### Flat byte readings of the typed signature components (FIPS 205 Fig. 17 order) -/

/-- Concatenated spec reading of a list of nodes. -/
def nds (ys : List Node) : Spec.Bytes := ys.flatMap nd

/-- `sig_WOTS ‖ AUTH`. -/
def xmssBytes (s : XmssSig vp.params prims) : Spec.Bytes :=
  nds s.wots.toList ++ nds s.auth.toList

/-- `SIG_HT`. -/
def htBytes (s : HtSigCore vp.params prims.core) : Spec.Bytes := s.toList.flatMap xmssBytes

/-- `SIG_FORS`: per tree, the revealed secret then the authentication path. -/
def forsBytes (s : ForsSigCore vp.params prims.core) : Spec.Bytes :=
  s.toList.flatMap fun t => nd t.sk ++ nds t.auth.toList

/-- `R ‖ SIG_FORS ‖ SIG_HT`. -/
def sigBytes (s : GeneralScheme.SignatureCore vp prims.core) : Spec.Bytes :=
  nd s.randomness ++ forsBytes s.fors ++ htBytes s.hypertree

/-- `PK.seed ‖ PK.root`. -/
def pkBytes (k : PublicKeyCore prims.core) : Spec.Bytes := nd k.pkSeed ++ nd k.pkRoot

end Link
