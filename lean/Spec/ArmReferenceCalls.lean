import Spec.ArmInternalSigner
import Spec.ArmVerifyBody

/-! Total reference implementations of the local contracts for the measured SHAKE
    signing and verifying drivers. These witnesses express exactly which operations
    the native subroutines must refine for the composed machine-level result. -/
namespace LinkedArm.NativeSession
open Spec LinkedArm.Signer

private theorem props {p : Params} (row : p ∈ parameterSets) :
    p.Valid ∧ p.family = .shake ∧ p.n ≤ 136 ∧ p.m ≤ 136 := by
  simp only [parameterSets, List.mem_cons, List.not_mem_nil, or_false] at row
  rcases row with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by constructor <;> decide, by decide⟩

def referenceSigner {p : Params} (row : p ∈ parameterSets) (m sk rnd : Bytes)
    (keyLen : sk.length = 4*p.n) (rndLen : rnd.length = p.n) : ArmInternalSigner.Callees p m sk rnd := by
  let scratch : Scratch := fun _ _ => 0
  let a := (block p sk 1).foldl Keccak.feed Keccak.initial
  let b := rnd.foldl Keccak.feed a
  let r := sponge scratch (block p sk 1 ++ rnd ++ m) p.n
  let dg := sponge scratch (r ++ block p sk 2 ++ block p sk 3 ++ m) p.m
  let digits := base2b (dg.take p.mdBytes) p.a p.k
  let ad := ArmInternalSigner.nativeAddress p dg
  let forest := forsSign p (dg.take p.mdBytes) (block p sk 0) (block p sk 2) ad
  let root := forsRoots p digits forest (block p sk 2) ad
  let initial : LayerState := ([],root,ArmInternalSigner.nativeTree p dg,ArmInternalSigner.nativeLeaf p dg)
  let calls := referenceCalls p (block p sk 0) (block p sk 2) initial
  have valid := (props row).1
  refine {scratch := scratch, r := r, dg := dg, digits := digits, forest := forest, root := root,
          layers := referenceLayers p (block p sk 0) (block p sk 2) initial,
          keySize := keyLen, randomSize := rndLen, rSize := ?_, dgSize := ?_,
          forestSize := forsSign_length p valid _ _ _ _, rootSize := T_length p valid _ _ _,
          absorbed := fun | 0 => a | 1 => b | _ => m.foldl Keccak.feed b,
          absorbKey := rfl, absorbRandom := rfl, absorbMessage := rfl, finish := ?_,
          digest := rfl, decode := rfl, fors := rfl, recover := rfl, ht := calls, htSize := ?_}
  · change (LinkedArm.Digest.finish scratch _ p.n).length = p.n
    rw [LinkedArm.Digest.finish_eq _ _ _ (props row).2.2.1]
    exact Keccak.squeeze_length _ _ _
  · change (LinkedArm.Digest.finish scratch _ p.m).length = p.m
    rw [LinkedArm.Digest.finish_eq _ _ _ (props row).2.2.2]
    exact Keccak.squeeze_length _ _ _
  · simp [r,sponge,a,b,List.foldl_append]
  · rw [layers_eq calls]; exact htSign_length p valid _ _ _ _ _

private theorem xmssRecoverySize (p : Params) (hv : p.Valid) (i sig msg seed a) :
    (xmssPkFromSig p i sig msg seed a).length = p.n := by
  unfold xmssPkFromSig climb
  apply List.foldlRecOn (motive := fun (st : Bytes × Nat) => st.1.length = p.n)
  · exact T_length p hv _ _ _
  · intro st _ j _
    dsimp only
    split <;> exact H_length p hv _ _ _

private def recovered (p : Params) (sig pk dg : Bytes) : Nat → Bytes
  | 0 => forsRoots p (base2b (dg.take p.mdBytes) p.a p.k)
      ((sig.drop p.n).take p.forsSigBytes) (block p pk 0) (ArmVerifyBody.nativeAddress p dg)
  | j+1 => let pos := ArmVerifyBody.location p dg j
           xmssPkFromSig p pos.2 ((sig.drop (p.n+p.forsSigBytes+j*p.xmssSigBytes)).take p.xmssSigBytes)
             (recovered p sig pk dg j) (block p pk 0) {Adrs.zero with layer := j, tree := pos.1}

def referenceVerifier {p : Params} (row : p ∈ parameterSets) (m sig pk : Bytes)
    (sigLen : sig.length = p.sigBytes) (pkLen : pk.length = 2*p.n) : ArmVerifyBody.Callees p m sig pk := by
  let dg := Hmsg p (sig.take p.n) (block p pk 0) (block p pk 1) m
  have valid := (props row).1
  refine {digest := dg, digits := base2b (dg.take p.mdBytes) p.a p.k,
          roots := recovered p sig pk dg, sigSize := sigLen, keySize := pkLen,
          digestSize := ?_, rootSize := ?_, hash := rfl, decode := rfl, forest := rfl, layer := ?_}
  · simp [dg,Hmsg,(props row).2.1]
  · intro j _
    cases j with
    | zero => exact T_length p valid _ _ _
    | succ => exact xmssRecoverySize p valid _ _ _ _ _
  · intro j _
    exact referenceLayerRoot _ _ _ _ _ _

end LinkedArm.NativeSession
