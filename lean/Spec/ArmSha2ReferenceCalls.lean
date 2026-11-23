import Spec.ArmSha2InternalSigner

/-! Total reference callees for the Apple SHA-2 internal signing driver. -/
namespace LinkedArm.NativeSession
open Spec LinkedArm.Signer

def sha2Sets : List Params := [sha2_128s,sha2_128f,sha2_192s,sha2_192f,sha2_256s,sha2_256f]

private theorem props {p : Params} (row : p ∈ sha2Sets) :
    p.Valid ∧ p.family = .sha2 ∧ p.n ≤ (if p.n = 16 then 64 else 128) := by
  simp only [sha2Sets, List.mem_cons, List.not_mem_nil, or_false] at row
  rcases row with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by constructor <;> decide, by decide⟩

theorem sha2HmsgLength (p : Params) (family : p.family = .sha2) (r seed root msg : Bytes) :
    (Hmsg p r seed root msg).length = p.m := by
  simp only [Hmsg,family]
  split
  · unfold mgf1
    rw [List.length_take,length_flatMap_const _ 32 (fun _ => sha256_length _) _]
    omega
  · unfold mgf1
    rw [List.length_take,length_flatMap_const _ 64 (fun _ => sha512_length _) _]
    omega

/-- No signing-oracle premise. Every modeled callee value is computed from the
    correctly sized key and randomness plus the arbitrary original message. -/
def referenceSha2Signer {p : Params} (row : p ∈ sha2Sets) (msg key random : Bytes)
    (keySize : key.length = 4*p.n) (randomSize : random.length = p.n) :
    ArmInternalSigner.Sha2.Callees p msg key random := by
  obtain ⟨valid,family,fits⟩ := props row
  let r := PRFmsg p (block p key 1) random msg
  let dg := Hmsg p r (block p key 2) (block p key 3) msg
  let md := dg.take p.mdBytes
  let digits := base2b md p.a p.k
  let ad := ArmInternalSigner.nativeAddress p dg
  let forest := forsSign p md (block p key 0) (block p key 2) ad
  let root := forsRoots p digits forest (block p key 2) ad
  let init : LayerState := ([],root,ArmInternalSigner.nativeTree p dg,ArmInternalSigner.nativeLeaf p dg)
  let calls := referenceCalls p (block p key 0) (block p key 2) init
  refine { r, dg, forest, root, layers := referenceLayers p (block p key 0) (block p key 2) init,
           keySize, randomSize, rSize := PRFmsg_length p valid _ _ _, dgSize := sha2HmsgLength p family _ _ _ _,
           forestSize := forsSign_length p valid _ _ _ _, rootSize := T_length p valid _ _ _,
           hashes := Sha2.referenceHashes p msg key random family fits,
           fors := rfl, recover := rfl, ht := calls, htSize := ?_ }
  rw [layers_eq calls]
  exact htSign_length p valid _ _ _ _ _

/-- Evaluate the bytes actually selected by the successful driver when its local
    calls are implemented by the reference provider. The six linked entry
    certificates discharge `checked` for each of their four allocation profiles. -/
theorem referenceSha2Result {im : ArmInternalSigner.Image} {profile : Nat}
    (row : im.p ∈ sha2Sets)
    (checked : ArmInternalSigner.run im profile = some ArmInternalSigner.Sha2.expected)
    (msg key random : Bytes) (keySize : key.length = 4*im.p.n) (randomSize : random.length = im.p.n) :
    (ArmInternalSigner.run im profile).map (ArmInternalSigner.Sha2.materialize
      (referenceSha2Signer row msg key random keySize randomSize)) =
      some (slhSignInternal im.p msg key random) := by
  let v := referenceSha2Signer row msg key random keySize randomSize
  obtain ⟨valid,family,_⟩ := props row
  have t := ArmInternalSigner.Sha2.trace checked checked valid.m_eq.symm.le v
  rw [checked]
  exact congrArg some (t.eq_spec family)

#print axioms referenceSha2Signer
#print axioms referenceSha2Result
end LinkedArm.NativeSession
