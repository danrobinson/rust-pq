import Integration.SlhDsaCompressionHmacSignature

namespace Reduction.Compression.Hmac256
open MLink Ideal SLHDSA OracleComp OracleSpec PQ.Interactive Quantum

private theorem doubleCharge {X Y E α ι : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    [AddCommGroup Y] [Fintype E] [DecidableEq E] {sp : OracleSpec ι} {old new : sp.Domain → ℕ}
    {M : (X → Y) → QOC (WS X Y E) sp α} {q : ℕ} (h : PUE old M q)
    (he : ∀ i, new i ≤ 2 * old i) : PUE new M (2*q) := by
  induction h with
  | pure a q => exact PUE.pure a _
  | instr j k q _ ih => exact PUE.instr j k _ ih
  | port k q _ ih => exact (PUE.port k _ ih).mono (by omega)
  | query t k q _ ih => exact (PUE.query t k _ ih).mono (by have := he t; omega)
  | eval x k q _ ih => exact (PUE.eval x k _ ih).mono (by omega)

def charge (S : Sha2Set) : (PRFScheme.PRFOracleSpec (S.Node × List Byte) S.Node).Domain → ℕ
  | .inl _ => 0
  | .inr (_,m) => (m.length + 24)/64 + 2

/-- The signer charges key generation, port calls, signed messages and final
verification. Each SHA-256 continuation costs at most twice its SHA-512 block allowance. -/
theorem signature_cost (S : Sha2Set) (rand : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node)
    {E : Type} [Fintype E] [DecidableEq E] (F : PortForger Input Output E)
    (c : Caps) (q qs : ℕ) (hq : ∀ pk, CountBound isPort (F.main pk) q)
    (hs : ∀ pk, CountBound isSign (F.main pk) qs) (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    PUE (charge S) (HmacKey.machine S (carrier S) rand seeds F) (2 * HmacKey.budget S c.ml q qs) := by
  apply doubleCharge (HmacKey.machine_cost S (carrier S) rand seeds F c q qs hq hs hc)
  rintro (n|⟨r,m⟩)
  · exact Nat.zero_le _
  · simp only [charge,HmacKey.messageCharge]
    omega

end Reduction.Compression.Hmac256
#print axioms Reduction.Compression.Hmac256.signature_cost
