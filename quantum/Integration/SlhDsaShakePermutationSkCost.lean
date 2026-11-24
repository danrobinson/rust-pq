import Integration.SlhDsaShakePermutationSkSecurity
import Integration.SlhDsaShakePermutationXof
import Integration.SlhDsaShakeApiSkBound

/-! Cost of the native SK.PRF reduction's remaining honest operations in
queries to the same public permutation. Its secret-address oracle is free
after fixing its answers, as required by PrfAnswerCost. -/
namespace Reduction.ShakePermutation.SkCost
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
open Classical MLink SLHDSA SLHDSA.Security OracleComp OracleSpec PQ.Interactive Quantum Open
open ShakeApi (Input RawTable Xof)
variable (S : Sha2Set) (N : ℕ)
def table (H : Port → Words) := ShakeApi.restrict S N (answer S (forward H))

theorem read_cost {A : Type} (cap : N ≤ ShakeApi.rawCap S 67 65536) (xs : List SLHDSA.Byte)
    (decode : Bytes S.vp.params.m → A) :
    EvalCost (fun H => (pure (decode (ShakeApi.extend (table S N H) xs)) : ProbComp A)) 483 := by
  by_cases small : xs.length ≤ N
  · have step := (benchmark_answer_cost S xs (small.trans cap)).map decode
    simpa only [table,ShakeApi.extend_restrict _ _ _ xs small,map_pure] using step
  · simpa only [ShakeApi.extend,dite_eq_right small] using (EvalCost.const (X:=Port) (Y:=Words)
      (pure (decode default) : ProbComp A)).mono (Nat.zero_le 483)

variable (base : Xof S)
local notation "P₀" => ShakeApi.primitives S base
local notation "Spec" => PSpec P₀ (S.Node × Adrs)

theorem hash_cost (cap : N ≤ ShakeApi.rawCap S 67 65536) (t : (publicHashSpec (P₀).core).Domain) :
    EvalCost (fun H => (pure (ShakeApi.hashPort S N base (table S N H) t) : ProbComp _)) 483 := by
  cases t with
  | thash pk a xs => exact read_cost S N cap _ (prefixBytes S.vp.params.n)
  | hmsg r pk root m => exact read_cost S N cap _ id

private theorem scale {I A : Type} {sp : OracleSpec I} (w : I → ℕ) (p : OracleComp sp A)
    (a k : ℕ) (hc : WCount w p a) : WCount (fun i => k * w i) p (k*a) := by
  induction p using OracleComp.inductionOn generalizing a with
  | pure x => trivial
  | query_bind t f ih =>
    rw [wCount_query_bind] at hc ⊢
    refine ⟨Nat.mul_le_mul_left k hc.1,fun u => ?_⟩
    simpa only [Nat.mul_sub] using ih u (a-w t) (hc.2 u)

private theorem component {A : Type} (fixed : S.Node × Adrs → S.Node) (p : OracleComp Spec A)
    (cap : N ≤ ShakeApi.rawCap S 67 65536) (q r : ℕ)
    (hh : IsQueryBoundP p (fun t => hkind t = .hash) q)
    (hp : IsQueryBoundP p (fun t => hkind t = .prfmsg) r) :
    EvalCost (fun H => simulateQ (ShakeApi.Sk.handler S N base fixed (table S N H)) p) (483*(q+r)) := by
  let visit (t : (Spec).Domain) := hkind t = .hash ∨ hkind t = .prfmsg
  let w (t : (Spec).Domain) := if visit t then 1 else 0
  refine EvalCost.simulateQ _ _ ?_ p _ (scale w p (q+r) 483 (wCount_of_isQueryBoundP _ p _ (hh.or hp)))
  rintro (n|d|t|⟨k,r,m⟩)
  · exact EvalCost.const _
  · exact EvalCost.const _
  · exact hash_cost S N base cap t
  · exact read_cost S N cap _ (prefixBytes S.vp.params.n)

theorem key_cost (fixed : S.Node × Adrs → S.Node) (pk : S.Node) (cap : N ≤ ShakeApi.rawCap S 67 65536) :
    EvalCost (fun H => simulateQ (ShakeApi.Sk.handler S N base fixed (table S N H))
      (openKeygenP (vp := S.vp) P₀ pk)) (483*Lazy.keygenHashes S.vp) := by
  apply component S N base fixed _ cap (Lazy.keygenHashes S.vp) 0
  · exact (openKeygenP_kindBound (vp:=S.vp) (prims:=P₀) .hash pk).mono
      (by simpa [hind] using Lazy.keygenB_hash (vp:=S.vp))
  · exact (openKeygenP_kindBound (vp:=S.vp) (prims:=P₀) .prfmsg pk).mono
      (by change Lazy.keygenB S.vp 0 0 ≤ 0; cases S <;> decide)

theorem sign_cost (fixed : S.Node × Adrs → S.Node) (r : PublicKeyCore (P₀).core → ProbComp S.Node)
    (pk : PublicKeyCore (P₀).core) (sk : S.Node) (m : List SLHDSA.Byte) (cap : N ≤ ShakeApi.rawCap S 67 65536) :
    EvalCost (fun H => simulateQ (ShakeApi.Sk.handler S N base fixed (table S N H))
      (openSignP (vp:=S.vp) r pk sk m)) (483*(Lazy.signHashes S.vp+1)) := by
  apply component S N base fixed _ cap
  · exact (openSignP_kindBound (vp:=S.vp) (prims:=P₀) (optRand:=r) .hash (by decide) pk sk m).mono
      (by simpa [hind] using Lazy.signB_hash (vp:=S.vp))
  · exact (openSignP_kindBound (vp:=S.vp) (prims:=P₀) (optRand:=r) .prfmsg (by decide) pk sk m).mono
      (by change 1+Lazy.signB S.vp 0 0 ≤ 1; cases S <;> decide)

theorem check_cost (pk : PublicKeyCore (P₀).core) (z : List SLHDSA.Byte × GeneralScheme.SignatureCore S.vp (P₀).core)
    (log : SigLog S.vp P₀) (cap : N ≤ ShakeApi.rawCap S 67 65536) :
    EvalCost (fun H => simulateQ (fun t => pure (ShakeApi.hashPort S N base (table S N H) t) : QueryImpl _ ProbComp)
      (sufCheckOpen pk z log)) (483*(1+Resources2.verifyHashes S.vp)) := by
  apply EvalCost.simulateQ _ (fun _ => 483) (hash_cost S N base cap)
  simpa only [ite_true,Nat.mul_one] using scale (fun _ => 1) _ _ 483
    (wCount_of_isQueryBoundP (fun _ => True) _ _ (sufCheckOpen_bound pk z log))

end Reduction.ShakePermutation.SkCost
#print axioms Reduction.ShakePermutation.SkCost.check_cost
