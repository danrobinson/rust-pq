import Reduction.Open.Bundle
import Reduction.LinearBytes

/-!
# Transport between primitive bundles that differ only in `PRF` / `PRF_msg`

`prims.setPrf prf pm` is `prims` with the two secret-key functions replaced; carrier types,
`adrsToKey`, `yToBytes`, `Thash`, `H_msg` are those of `prims`, definitionally.  The types indexed
by the core bundle (`PublicKeyCore`, `SignatureCore`, `XmssSigCore`, `ForsTreeSigCore`) at the two
bundles are different types (the core contains `PRF`, `PRF_msg`), but their fields have the same
types; `trPk`, `trFors`, `trXmss`, `trSig` are the field-wise identity maps.

`krfl` closes `a = b` by `Eq.refl a`, the definitional equality being checked by the kernel only
(the elaborator does not unfold stuck `match` auxiliaries whose parameters differ).  No axiom.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security

namespace Ideal.Transport

/-- Close a goal `a = b` by `Eq.refl a`, checked by the kernel only. -/
elab "krfl" : tactic => Lean.Elab.Tactic.withMainContext do
  let g ← Lean.Elab.Tactic.getMainGoal
  let t ← Lean.instantiateMVars (← g.getType)
  let some (_, a, _) := t.eq? | throwError "krfl: not an equality"
  let pf ← Lean.Meta.mkEqRefl a
  g.assign pf
  Lean.Elab.Tactic.replaceMainGoal []

variable {p : Params}

/-- The core bundle with `PRF`, `PRF_msg` replaced. -/
@[reducible] def setPrfC (core : CorePrimitives p) (prf : core.PkSeed → core.SkSeed → Adrs → core.Y)
    (pm : core.SkPrf → core.Y → List Byte → core.Y) : CorePrimitives p where
  PkSeed := core.PkSeed
  SkSeed := core.SkSeed
  SkPrf := core.SkPrf
  Y := core.Y
  AdrsKey := core.AdrsKey
  adrsToKey := core.adrsToKey
  PRF := prf
  PRFmsg := pm
  yToBytes := core.yToBytes

/-- The bundle with `PRF`, `PRF_msg` replaced; everything else is that of `prims`. -/
@[reducible] def setPrf (prims : Primitives p) (prf : prims.PkSeed → prims.SkSeed → Adrs → prims.Y)
    (pm : prims.SkPrf → prims.Y → List Byte → prims.Y) : Primitives p where
  toCorePrimitives := setPrfC prims.core prf pm
  Thash := prims.Thash
  Hmsg := prims.Hmsg

theorem setPrf_self (prims : Primitives p) : setPrf prims prims.PRF prims.PRFmsg = prims := rfl

section Maps

variable (core : CorePrimitives p) (prf : core.PkSeed → core.SkSeed → Adrs → core.Y)
  (pm : core.SkPrf → core.Y → List Byte → core.Y)

/-- Field-wise identity on public keys. -/
def trPk (pk : PublicKeyCore core) : PublicKeyCore (setPrfC core prf pm) := ⟨pk.pkSeed, pk.pkRoot⟩

/-- Field-wise identity on FORS tree signatures. -/
def trFors (s : ForsTreeSigCore p core) : ForsTreeSigCore p (setPrfC core prf pm) := ⟨s.sk, s.auth⟩

/-- Field-wise identity on XMSS signatures. -/
def trXmss (s : XmssSigCore p core) : XmssSigCore p (setPrfC core prf pm) := ⟨s.wots, s.auth⟩

/-- Field-wise identity on signatures. -/
def trSig (s : SignatureCore p core) : SignatureCore p (setPrfC core prf pm) :=
  ⟨s.randomness, s.fors.map (trFors core prf pm), s.hypertree.map (trXmss core prf pm)⟩

@[simp] theorem trPk_pkSeed (pk : PublicKeyCore core) : (trPk core prf pm pk).pkSeed = pk.pkSeed := rfl
@[simp] theorem trPk_pkRoot (pk : PublicKeyCore core) : (trPk core prf pm pk).pkRoot = pk.pkRoot := rfl
@[simp] theorem trPk_mk (a : core.PkSeed) (b : core.Y) :
    trPk core prf pm ⟨a, b⟩ = ⟨a, b⟩ := rfl
@[simp] theorem trFors_sk (s : ForsTreeSigCore p core) : (trFors core prf pm s).sk = s.sk := rfl
@[simp] theorem trFors_auth (s : ForsTreeSigCore p core) : (trFors core prf pm s).auth = s.auth := rfl
@[simp] theorem trFors_mk (a : core.Y) (b : Vector core.Y p.a) :
    trFors core prf pm ⟨a, b⟩ = ⟨a, b⟩ := rfl
@[simp] theorem trXmss_wots (s : XmssSigCore p core) : (trXmss core prf pm s).wots = s.wots := rfl
@[simp] theorem trXmss_auth (s : XmssSigCore p core) : (trXmss core prf pm s).auth = s.auth := rfl
@[simp] theorem trXmss_mk (a : WotsSig p core) (b : Vector core.Y p.hp) :
    trXmss core prf pm ⟨a, b⟩ = ⟨a, b⟩ := rfl
@[simp] theorem trSig_randomness (s : SignatureCore p core) :
    (trSig core prf pm s).randomness = s.randomness := rfl
@[simp] theorem trSig_fors (s : SignatureCore p core) :
    (trSig core prf pm s).fors = s.fors.map (trFors core prf pm) := rfl
@[simp] theorem trSig_hypertree (s : SignatureCore p core) :
    (trSig core prf pm s).hypertree = s.hypertree.map (trXmss core prf pm) := rfl
@[simp] theorem trSig_mk (r : core.Y) (f : ForsSigCore p core) (h : HtSigCore p core) :
    trSig core prf pm ⟨r, f, h⟩ = ⟨r, f.map (trFors core prf pm), h.map (trXmss core prf pm)⟩ := rfl

theorem trPk_injective : Function.Injective (trPk core prf pm) := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ h
  cases h; rfl

theorem trFors_injective : Function.Injective (trFors core prf pm) := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ h
  cases h; rfl

theorem trXmss_injective : Function.Injective (trXmss core prf pm) := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ h
  cases h; rfl

end Maps

end Ideal.Transport
