import HashSig.SLHDSA.SHAKE128s.Statement.Theorems.StrongUnforgeability

/-! Classical SHAKE-128s with encoded public and secret keys in VCVio's
pure-mode signature game. Signing uses the public seed as optional randomness.
All parties share an initially empty random-oracle table with independent
uniform 30-byte answers at fresh byte-string inputs. Success probability
averages over this table, key generation and adversarial randomness. -/
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

/-- At the full signing limit, success probability at least one half requires a
worst-case work budget of at least 2^126 in the classical shared-oracle game.
The budget bounds the sum of signing requests, adversarial hash calls and
verification hash calls with probability one. -/
theorem half_success_work (A : Game.Adversary Answer WireBytes) (q : ℕ) (hq : 1 ≤ q)
    (signings : Game.WithinSigningLimit byteScheme A)
    (work : (Game.securityGame byteScheme).HasQueryBound () Game.adversaryWork A q)
    (success : 1 / 2 ≤ (Game.securityGame byteScheme).advantage () A) : 2^126 ≤ q := by
  have bound := success.trans (strong_lifetime q hq A signings work)
  rw [ENNReal.le_div_iff_mul_le (by norm_num) (by norm_num)] at bound
  have realBound := (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).2 bound
  rw [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat,
    ENNReal.toReal_natCast, ENNReal.toReal_natCast] at realBound
  norm_num at realBound ⊢
  exact_mod_cast realBound

end
end Reduction.ShakeClassicalLifetime
#print axioms Reduction.ShakeClassicalLifetime.strong_lifetime
#print axioms Reduction.ShakeClassicalLifetime.half_success_work
