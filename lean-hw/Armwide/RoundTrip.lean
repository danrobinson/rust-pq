import Armwide.PublicSignature
open Aeneas Aeneas.Std Result
open slhdsa
namespace NativeArmApi
noncomputable section

/-- The verifier consumes the very vector returned by the selected public signer.
The key buffers may contain arbitrary data on entry. -/
def RoundTrip {S K V N : Usize} (P : Spec.Params) (slack : Nat)
    (gen : Array U8 S → Array U8 K → Array U8 V → Result (Array U8 K × Array U8 V))
    (sign : Slice U8 → Slice U8 → Array U8 K → Array U8 N → Result (Option (alloc.vec.Vec U8)))
    (det : Slice U8 → Slice U8 → Array U8 K → Result (Option (alloc.vec.Vec U8)))
    (verify : Slice U8 → Slice U8 → Slice U8 → Array U8 V → Result Bool) : Prop :=
  ∀ seeds sk0 pk0 m ctx rnd (deterministic : Bool), Room m.length slack → ctx.length ≤ 255 →
    ∃ sk pk sig, gen seeds sk0 pk0 = ok (sk,pk) ∧
      (if deterministic then det m ctx sk else sign m ctx sk rnd) = ok (some sig) ∧
      verify m sig.deref ctx pk = ok true ∧
      (bytes sk.val,bytes pk.val) = Spec.slhKeygenInternal P (Spec.block P (bytes seeds.val) 0)
        (Spec.block P (bytes seeds.val) 1) (Spec.block P (bytes seeds.val) 2) ∧
      some (bytes sig.val) = Spec.slhSign P (bytes m.val) (bytes ctx.val) (bytes sk.val)
        (if deterministic then Spec.block P (bytes sk.val) 2 else bytes rnd.val)

open slhdsa.Armwide.Public.Dispatcher (Cpu)
open slhdsa.Armwide.Keygen (Features)
variable [Cpu] [Features]

open Lean Elab Command in
run_cmd do
  for s in profiles do
    let id := fun n => mkIdent n
    let k := `ArmKeys.slhdsa.sets ++ s
    let sdk := `ArmSdk.AppleContext.SegmentedSdk.slhdsa.sets ++ s
    let proof := `ArmSdk.AppleContext.SegmentedSdk.slhdsa ++ s
    let session := `ArmSession.slhdsa ++ s
    let slack := Syntax.mkNumLit (if s == `sha2_128s || s == `sha2_128f then "409" else "561")
    elabCommand (← `(theorem $(id (s ++ `roundTrip)) :
        RoundTrip $(id (`Spec ++ s)) $slack $(id (k ++ `keygen)) $(id (sdk ++ `sign))
          $(id (sdk ++ `sign_deterministic)) $(id (sdk ++ `verify)) := by
      intro seeds sk0 pk0 m ctx rnd deterministic room valid
      obtain ⟨⟨sk,pk⟩,generated,keys⟩ := spec_imp_exists
        ($(id (`ArmKeys.slhdsa ++ s ++ `keygen_spec)) seeds sk0 pk0)
      cases deterministic with
      | false =>
        obtain ⟨sig,signed,verified⟩ := $(id (session ++ `api_complete_sign))
          seeds sk0 pk0 sk pk generated m ctx rnd room valid
        obtain ⟨v,hv,eqn⟩ := spec_imp_exists ($(id (proof ++ `sign_spec)) m ctx sk rnd room)
        rw [signed] at hv
        simp only [ok.injEq] at hv
        subst v
        exact ⟨sk,pk,sig,generated,signed,verified,keys,eqn⟩
      | true =>
        obtain ⟨sig,signed,verified⟩ := $(id (session ++ `api_complete_sign_deterministic))
          seeds sk0 pk0 sk pk generated m ctx room valid
        obtain ⟨v,hv,eqn⟩ := spec_imp_exists ($(id (proof ++ `sign_deterministic_spec)) m ctx sk room)
        rw [signed] at hv
        simp only [ok.injEq] at hv
        subst v
        exact ⟨sk,pk,sig,generated,signed,verified,keys,eqn⟩))

end
end NativeArmApi
