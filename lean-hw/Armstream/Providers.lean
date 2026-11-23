import RcSlhSha2.Platforms

open Aeneas Aeneas.Std Result
namespace slhdsa.PlatformStream
open RcSlhSha2

/-- Marshal the locked backend's eight machine words back to the fixed-size
state returned by Rust's mutable block API. -/
def returned256 (words : List Spec.SHA256.Word) : Result (Array U32 8#usize) :=
  if h : words.length = 8 then ok (.from (words.map fun w => ⟨w⟩) (by simpa using h))
  else fail .panic

def returned512 (words : List Spec.SHA512.Word) : Result (Array U64 8#usize) :=
  if h : words.length = 8 then ok (.from (words.map fun w => ⟨w⟩) (by simpa using h))
  else fail .panic

theorem returned256_state (s : Array U32 8#usize) : returned256 (wv s.val) = ok s := by
  rw [returned256,dite_eq_left (by simp [wv])]
  congr 1
  apply Aeneas.Std.Array.ext _ _
  simp [wv,List.map_map,Function.comp_def]

theorem returned512_state (s : Array U64 8#usize) : returned512 (S512.wv s.val) = ok s := by
  rw [returned512,dite_eq_left (by simp [S512.wv])]
  congr 1
  apply Aeneas.Std.Array.ext _ _
  simp [S512.wv,List.map_map,Function.comp_def]

def provider256 (route : Provider) (s : Array U32 8#usize) (bs : Slice (Array U8 64#usize)) :=
  run256 route s bs >>= returned256

def provider512 (route : Provider) (s : Array U64 8#usize) (bs : Slice (Array U8 128#usize)) :=
  run512 route s bs >>= returned512

theorem provider256_eq (route : Provider) :
    provider256 route = ArmStreamRust.sha2.sha256.compress256 := by
  funext s bs
  obtain ⟨out,ret,words⟩ := spec_imp_exists (bulk256 s bs)
  obtain ⟨_,actual,rfl⟩ := spec_imp_exists (run256_spec route s bs)
  simp only [provider256,actual,bind_tc_eq,bind_ok,← words,returned256_state,ret]

theorem provider512_eq (route : Provider) :
    provider512 route = ArmStreamRust.sha2.sha512.compress512 := by
  funext s bs
  obtain ⟨out,ret,words⟩ := spec_imp_exists (bulk512 s bs)
  obtain ⟨_,actual,rfl⟩ := spec_imp_exists (run512_spec route s bs)
  simp only [provider512,actual,bind_tc_eq,bind_ok,← words,returned512_state,ret]

end slhdsa.PlatformStream

namespace ArmStreamBinding
open Lean Meta Elab Command

/-- Abstract exactly the block API call in the actual Aeneas declaration.
Reapplying the original block function is checked by definitional equality. -/
private def abstractBlock (driver block dest : Name) : MetaM Unit := do
  let .defnInfo old ← getConstInfo driver | throwError "expected a translated function: {driver}"
  unless old.value.getUsedConstants.contains block do
    throwError "expected {driver} to invoke {block}"
  withLocalDeclD `compress (← inferType (mkConst block)) fun f => do
    let value ← mkLambdaFVars #[f] (old.value.replace fun
      | .const n _ => if n == block then some f else none
      | _ => none)
    let type ← mkForallFVars #[f] old.type
    addDecl <| .defnDecl { old with «name» := dest, type := type, value := value, all := [dest] }

run_cmd liftTermElabM do
  abstractBlock `ArmStreamRust.sha256.sha256_from `ArmStreamRust.sha2.sha256.compress256
    `ArmStreamBinding.continue256
  abstractBlock `ArmStreamRust.sha512.sha512_from `ArmStreamRust.sha2.sha512.compress512
    `ArmStreamBinding.continue512
  abstractBlock `ArmStreamRust.sha512.compress `ArmStreamRust.sha2.sha512.compress512
    `ArmStreamBinding.single512

open slhdsa.PlatformStream slhdsa.RcSlhSha2

theorem continue256_bound (route : Provider) :
    continue256 (provider256 route) = ArmStreamRust.sha256.sha256_from := by rw [provider256_eq]; rfl

theorem continue512_bound (route : Provider) :
    continue512 (provider512 route) = ArmStreamRust.sha512.sha512_from := by rw [provider512_eq]; rfl

theorem single512_bound (route : Provider) :
    single512 (provider512 route) = ArmStreamRust.sha512.compress := by rw [provider512_eq]; rfl

end ArmStreamBinding
