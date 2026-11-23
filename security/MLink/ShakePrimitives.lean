import MLink.Encoding
import MReduction.Instances

/-! Concrete SHAKE256 functions for the byte-string security game.
The game calls the same Keccak sponge as the Rust refinement. The six constructors of
`Sha2Set` serve only as indices for the six shared parameter shapes. -/
namespace ShakeSecurity
open SLHDSA SLHDSA.Concrete MLink

def params (S : Sha2Set) : Spec.Params := { S.spec with family := .shake }

def hash (input : Spec.Bytes) (n : Nat) : Bytes n :=
  ⟨(cv (Spec.shake256 input n)).toArray, by simp [cv]⟩

@[simp] theorem nd_hash (input : Spec.Bytes) (n : Nat) :
    nd (hash input n) = Spec.shake256 input n := by simp [nd,hash]

theorem fullAddress (a : SLHDSA.Adrs) : nd a.toVector = (adr a).bytes := by
  change sp a.toBytes = _
  simp only [Adrs.toBytes, Adrs.toBytesBE, sp_append, toByte_eq, Spec.Adrs.bytes, adr]

def primitives (p : SLHDSA.Params) : Primitives p where
  PkSeed := Bytes p.n
  SkSeed := Bytes p.n
  SkPrf := Bytes p.n
  Y := Bytes p.n
  AdrsKey := Bytes 32
  adrsToKey := Adrs.toVector
  yToBytes := id
  Thash pk key ys := hash (nd pk ++ nd key ++ nds ys) p.n
  PRF pk sk a := hash (nd pk ++ nd a.toVector ++ nd sk) p.n
  PRFmsg sk rand msg := hash (nd sk ++ nd rand ++ sp msg) p.n
  Hmsg r pk root msg := hash (nd r ++ nd pk ++ nd root ++ sp msg) p.m

abbrev prims (S : Sha2Set) := primitives S.vp.params

def wireCodec (p : SLHDSA.Params) : CoreWireCodec p (primitives p).core where
  pkSeed := WireCodec.bytes p.n
  skSeed := WireCodec.bytes p.n
  skPrf := WireCodec.bytes p.n
  y := WireCodec.bytes p.n
  y_toBytes := fun _ => rfl

theorem byteLaws (p : SLHDSA.Params) : (primitives p).core.ByteLaws := ⟨fun _ _ h => h⟩

variable (S : Sha2Set)

/-- Byte laws, injective full addresses, and canonical address bounds. -/
theorem structural : Reduction.Structural S.vp (prims S) :=
  ⟨byteLaws _, Concrete.keyInjective_shakePrimitives _,
   (SLHDSA.Security.fipsApprovedAddressBounds S.fips).toCanonicalAddressBounds⟩

theorem F_eq (pk : S.Node) (a : Adrs) (_ : Dom a) (y : S.Node) :
    nd ((prims S).F pk a y) = Spec.F (params S) (nd pk) (adr a) (nd y) := by
  change nd (hash ((nd pk ++ nd a.toVector) ++ nds [y]) _) = _
  rw [nd_hash, fullAddress]
  simp only [S.n_eq, params, Spec.F, nds, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]

theorem H_eq (pk : S.Node) (a : Adrs) (_ : Dom a) (l r : S.Node) :
    nd ((prims S).H pk a l r) = Spec.H (params S) (nd pk) (adr a) (nd l ++ nd r) := by
  change nd (hash ((nd pk ++ nd a.toVector) ++ nds [l, r]) _) = _
  rw [nd_hash, fullAddress]
  simp only [S.n_eq, params, Spec.H, nds, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]

theorem Tl_eq (pk : S.Node) (a : Adrs) (_ : Dom a) (ys : List S.Node)
    (_ : ys.length ≠ 1) :
    nd ((prims S).Tl pk a ys) = Spec.T (params S) (nd pk) (adr a) (nds ys) := by
  change nd (hash ((nd pk ++ nd a.toVector) ++ nds ys) _) = _
  rw [nd_hash, fullAddress]
  simp only [S.n_eq, params, Spec.T, List.append_assoc]

theorem PRF_eq (pk sk : S.Node) (a : Adrs) (_ : Dom a) :
    nd ((prims S).PRF pk sk a) = Spec.PRF (params S) (nd pk) (nd sk) (adr a) := by
  change nd (hash _ _) = _
  simp [params, Spec.PRF, fullAddress, S.n_eq]

theorem PRFmsg_eq (sk rand : S.Node) (msg : List UInt8) :
    nd ((prims S).PRFmsg sk rand msg) = Spec.PRFmsg (params S) (nd sk) (nd rand) (sp msg) := by
  change nd (hash _ _) = _
  simp [params, Spec.PRFmsg, S.n_eq]

theorem Hmsg_eq (r pk root : S.Node) (msg : List UInt8) :
    nd ((prims S).Hmsg r pk root msg) = Spec.Hmsg (params S) (nd r) (nd pk) (nd root) (sp msg) := by
  change nd (hash _ _) = _
  simp [params, Spec.Hmsg, S.m_eq]

end ShakeSecurity
