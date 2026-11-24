import Integration.SlhDsaShakeApiCost
import Integration.SlhDsaCompressionPrfInterp

namespace Reduction.ShakeApi.Sk
open MLink SLHDSA SLHDSA.Security OracleComp OracleSpec PQ.Interactive Quantum Open
variable (S : Sha2Set) (N : ℕ) (base : Xof S)
local notation "P₀" => primitives S base
local notation "Spec" => PSpec P₀ (S.Node × Adrs)

/-- Fixed replies on the secret-oracle interface. Both other interfaces read the same raw XOF. -/
def handler (answer : S.Node × Adrs → S.Node) (H : RawTable S N) : QueryImpl Spec ProbComp
  | .inl n => liftM (unifSpec.query n)
  | .inr (.inl d) => pure (answer d)
  | .inr (.inr (.inl t)) => pure (hashPort S N base H t)
  | .inr (.inr (.inr (k,r,m))) => pure ((primitives S (extend H)).PRFmsg k r m)

private theorem cost {α : Type} (answer : S.Node × Adrs → S.Node) (P : OracleComp Spec α) (q p : ℕ)
    (hh : IsQueryBoundP P (fun t => hkind t = .hash) q)
    (hp : IsQueryBoundP P (fun t => hkind t = .prfmsg) p) :
    EvalCost (fun H => simulateQ (handler S N base answer H) P) (q+p) := by
  let visits (t : (Spec).Domain) := hkind t = .hash ∨ hkind t = .prfmsg
  refine EvalCost.simulateQ _ (fun t => if visits t then 1 else 0) ?_ P _ (wCount_of_isQueryBoundP _ P _ (hh.or hp))
  rintro (n|d|t|⟨k,r,m⟩)
  · exact EvalCost.const _
  · exact EvalCost.const _
  · exact hash_cost S N base t
  · exact prfmsg_cost S N k r m

theorem key_cost (a : S.Node × Adrs → S.Node) (pk : S.Node) :
    EvalCost (fun H => simulateQ (handler S N base a H) (openKeygenP (vp := S.vp) P₀ pk))
      (Lazy.keygenHashes S.vp) := by
  rw [← Nat.add_zero (Lazy.keygenHashes S.vp)]
  apply cost
  · exact (openKeygenP_kindBound (vp := S.vp) (prims := P₀) .hash pk).mono
      (by simpa [hind] using Lazy.keygenB_hash (vp := S.vp))
  · exact (openKeygenP_kindBound (vp := S.vp) (prims := P₀) .prfmsg pk).mono
      (by change Lazy.keygenB S.vp 0 0 ≤ 0; cases S <;> decide)

theorem sign_cost (a : S.Node × Adrs → S.Node) (r : PublicKeyCore (P₀).core → ProbComp S.Node)
    (pk : PublicKeyCore (P₀).core) (sk : S.Node) (m : List SLHDSA.Byte) :
    EvalCost (fun H => simulateQ (handler S N base a H) (openSignP (vp := S.vp) r pk sk m))
      (Lazy.signHashes S.vp + 1) := by
  apply cost
  · exact (openSignP_kindBound (vp := S.vp) (prims := P₀) (optRand := r) .hash (by decide) pk sk m).mono
      (by simpa [hind] using Lazy.signB_hash (vp := S.vp))
  · exact (openSignP_kindBound (vp := S.vp) (prims := P₀) (optRand := r) .prfmsg (by decide) pk sk m).mono
      (by change 1 + Lazy.signB S.vp 0 0 ≤ 1; cases S <;> decide)

theorem check_cost (pk : PublicKeyCore (P₀).core)
    (z : List SLHDSA.Byte × GeneralScheme.SignatureCore S.vp (P₀).core) (log : SigLog S.vp P₀) :
    EvalCost (fun H => simulateQ (fun t => pure (hashPort S N base H t) : QueryImpl _ ProbComp)
      (sufCheckOpen pk z log)) (1 + Resources2.verifyHashes S.vp) := by
  apply EvalCost.simulateQ _ (fun _ => 1) (hash_cost S N base)
  simpa only [ite_true] using wCount_of_isQueryBoundP (fun _ => True) _ _ (sufCheckOpen_bound pk z log)

end Reduction.ShakeApi.Sk
#print axioms Reduction.ShakeApi.Sk.key_cost
#print axioms Reduction.ShakeApi.Sk.sign_cost
#print axioms Reduction.ShakeApi.Sk.check_cost
