import HashSig.SLHDSA.SHAKE128s.Statement.Theorems.StrongUnforgeability

/-! Classical SHAKE-128s with encoded public and secret keys in VCVio's
deterministic pure-mode signature game over a shared byte random oracle. -/
namespace Reduction.ShakeClassicalLifetime
open SLHDSA SLHDSA.Concrete SLHDSA.SHAKE128s OracleComp OracleSpec
noncomputable section

private abbrev codec := shakeWireCodec FIPS205.params.params
abbrev Answer := FIPS205.Answer
abbrev WireBytes := List UInt8

def byteScheme : Game.ExternalScheme Answer WireBytes WireBytes where
  keygen := Prod.map (encodeSecretKey codec) (encodePublicKey codec) <$> FIPS205.scheme.keygen
  sign sk request := match decodeSecretKey codec sk with
    | .ok key => FIPS205.scheme.sign key request
    | .error _ => pure none
  verify pk request signature := match decodePublicKey codec pk with
    | .ok key => FIPS205.scheme.verify key request signature
    | .error _ => pure false

private theorem sameWorld {α : Type} (p : OracleComp (Game.World Answer) α) :
    simulateQ (Bridge.relabel (Equiv.refl Answer)) p = p := by
  induction p using OracleComp.inductionOn with
  | pure => simp
  | query_bind i k ih =>
    rcases i with n|x <;> simp [simulateQ_bind,Bridge.relabel,ih]

/-- SUF-CMA with at most 2^64 signing queries. Work charges the adversary's
own hash calls, its signing requests and the hash calls of final verification. -/
theorem strong_lifetime : Game.HasSecurityBits byteScheme Game.adversaryWork 127 := by
  let b : Bridge.SchemeBridge (Equiv.refl Answer) FIPS205.scheme byteScheme := {
    pk := encodePublicKey codec
    sk := encodeSecretKey codec
    sign := fun sk req => by simp [sameWorld,byteScheme]
    verify := fun pk req sig => by simp [sameWorld,byteScheme]
    keygen := by
      apply Bridge.keygen_of_map_eq
      simp only [sameWorld]
      rfl }
  apply Bridge.hasSecurityBits_of_bridge b _ slhDsa_sufCma_127
  simp

end
end Reduction.ShakeClassicalLifetime
#print axioms Reduction.ShakeClassicalLifetime.strong_lifetime
