import Spec.ArmInternalSigner
import Spec.AppleSha2Composition

namespace Spec.ArmInternalSigner.Sha2
open LinkedArm.Signer

def expected : Observation := ⟨sha2Schedule,[.r,.fors,.ht]⟩

/-- SHA-2 call contracts. Both FORS calls receive the digest prefix in this ABI.
    The local FORS equations include their internal digit conversion. -/
structure Callees (p : Params) (msg key random : Bytes) where
  r : Bytes
  dg : Bytes
  forest : Bytes
  root : Bytes
  layers : Layers
  keySize : key.length = 4*p.n
  randomSize : random.length = p.n
  rSize : r.length = p.n
  dgSize : dg.length = p.m
  forestSize : forest.length = p.forsSigBytes
  rootSize : root.length = p.n
  hashes : LinkedArm.Signer.Sha2.HashCalls p msg key random r dg
  fors : forest = forsRows p (base2b (dg.take p.mdBytes) p.a p.k) (Spec.block p key 0)
    (Spec.block p key 2) (nativeAddress p dg)
  recover : root = forsRoots p (base2b (dg.take p.mdBytes) p.a p.k) forest
    (Spec.block p key 2) (nativeAddress p dg)
  ht : LayerCalls p (Spec.block p key 0) (Spec.block p key 2)
    ([],root,nativeTree p dg,nativeLeaf p dg) layers
  htSize : (afterLayers p layers ([],root,nativeTree p dg,nativeLeaf p dg) p.d).1.length = htLen p

def materialize {p msg key random} (v : Callees p msg key random) (o : Observation) :=
  o.parts.flatMap fun part => match part with
    | .r => v.r
    | .fors => v.forest
    | .ht => (afterLayers p v.layers ([],v.root,nativeTree p v.dg,nativeLeaf p v.dg) p.d).1

def trace {im profile msg key random o} (actual : run im profile = some o)
    (certificate : run im profile = some expected) (row : im.p.mdBytes+im.p.treeBytes+im.p.leafBytes ≤ im.p.m)
    (v : Callees im.p msg key random) :
    LinkedArm.Signer.Sha2.Signature im.p msg key random (materialize v o) := by
  rw [certificate] at actual
  cases Option.some.inj actual
  obtain ⟨ht,hl⟩ := ArmSignCoordinates.interpretation im.p v.dg (v.dgSize ▸ row)
  have treeEq : nativeTree im.p v.dg = digestTree im.p v.dg := ht
  have leafEq : nativeLeaf im.p v.dg = digestLeaf im.p v.dg := hl
  have ad : nativeAddress im.p v.dg = forsAddress im.p v.dg := by
    simp only [nativeAddress,forsAddress,treeEq,leafEq]
  exact { r := v.r, digest := v.dg, hashes := v.hashes,
          digits := base2b (v.dg.take im.p.mdBytes) im.p.a im.p.k, decode := rfl,
          forsSig := v.forest, forsPk := v.root, forest := ad ▸ v.fors, recovery := ad ▸ v.recover,
          layers := v.layers, calls := by simpa only [treeEq,leafEq] using v.ht,
          output := by simp [materialize,expected,treeEq,leafEq] }
end Spec.ArmInternalSigner.Sha2
