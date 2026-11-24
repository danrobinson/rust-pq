import Integration.SlhDsaCompressionForsSign
import Ideal.Realize.PrfCount

namespace Reduction.Compression.SkGame
open MLink Ideal SLHDSA SLHDSA.Security OracleComp OracleSpec PQ.Interactive PQ.QROM Quantum Open
variable (S : Sha2Set) (f : RandFns S.vp.params)
local notation "P₀" => randPrims f
local notation "Spec" => PSpec P₀ (S.Node × Adrs)

def handler (answer : S.Node × Adrs → S.Node) (H : Input → Output) : QueryImpl Spec ProbComp
  | .inl n => liftM (unifSpec.query n)
  | .inr (.inl d) => pure (answer d)
  | .inr (.inr (.inl t)) => pure (hashPort S f H t)
  | .inr (.inr (.inr (k,r,m))) => pure ((tablePrimitives (tablesOf H) S.vp.params).PRFmsg k r m)

def weight : (Spec).Domain → ℕ
  | .inr (.inr (.inl t)) => hashCalls S f t
  | .inr (.inr (.inr (_,_,m))) => msgPrfCalls S m.length
  | _ => 0

theorem simulate_cost (answer : S.Node × Adrs → S.Node) {α : Type} (P : OracleComp Spec α)
    (q : ℕ) (hq : WCount (weight S f) P q) :
    EvalCost (fun H => simulateQ (handler S f answer H) P) q := by
  refine EvalCost.simulateQ _ (weight S f) ?_ P q hq
  rintro (n | d | t | ⟨k,r,m⟩)
  · exact EvalCost.const _
  · exact EvalCost.const _
  · exact hashPort_cost S f t
  · exact msgPrf_cost S k r m

private theorem core_count {α : Type} (P : OracleComp Spec α) (q B : ℕ)
    (hh : IsQueryBoundP P (fun t => hkind t = .hash) q)
    (hp : IsQueryBoundP P (fun t => hkind t = .prfmsg) 0)
    (hc : IsQueryBoundP P (fun t => B < weight S f t) 0) : WCount (weight S f) P (q*B) := by
  refine cappedCount _ (fun t => hkind t = .hash ∨ hkind t = .prfmsg) _ ?_ _ _ ?_ hc
  · rintro (n|d|t|m) hn <;> first | rfl | exact (hn (Or.inl rfl)).elim | exact (hn (Or.inr rfl)).elim
  · exact hh.or hp

theorem keygen_count (pk : S.Node) :
    WCount (weight S f) (openKeygenP (vp := S.vp) P₀ pk)
      (Lazy.keygenHashes S.vp * signMax S 0) := by
  apply core_count
  · exact (openKeygenP_kindBound (vp := S.vp) (prims := P₀) .hash pk).mono (by simpa [hind] using Lazy.keygenB_hash (vp := S.vp))
  · apply Realize.Prf.np_openKeygenP <;> intros <;> simp [hkind]
  · apply Realize.Prf.np_openKeygenP
    · intro a; exact Nat.not_lt_zero _
    · intro key xs hx
      change ¬signMax S 0 < thashCalls S xs.length
      rcases hx with h|h|h|h <;> rw [h] <;> unfold signMax keygenMax <;> omega

theorem signCore_count (pk root r : S.Node) (m : List Byte) :
    WCount (weight S f) (openSignCoreP (vp := S.vp) P₀ m pk root r)
      (Lazy.signHashes S.vp * signMax S m.length) := by
  apply core_count
  · exact (openSignCoreP_kindBound (vp := S.vp) (prims := P₀) .hash m pk root r).mono (by simpa [hind] using Lazy.signB_hash (vp := S.vp))
  · apply Realize.Prf.openSignCoreP_bound
    · intro; simp [hkind]
    · intros; simp [hkind]
    · exact (isQueryBoundP_query_iff _ _ _).2 (fun h => by cases h)
  · apply Realize.Prf.openSignCoreP_bound
    · intro; exact Nat.not_lt_zero _
    · intro key xs hx
      change ¬signMax S m.length < thashCalls S xs.length
      rcases hx with h|h|h|h <;> rw [h] <;> unfold signMax keygenMax <;> omega
    · exact (isQueryBoundP_query_iff _ _ _).2 fun h => False.elim ((not_lt_of_ge (le_max_right ..)) h)

theorem sign_cost (answer : S.Node × Adrs → S.Node) (rand : PublicKeyCore (P₀).core → ProbComp S.Node)
    (pk : PublicKeyCore (P₀).core) (skPrf : S.Node) (m : List Byte) :
    EvalCost (fun H => simulateQ (handler S f answer H) (openSignP (vp := S.vp) rand pk skPrf m))
      (msgPrfCalls S m.length + Lazy.signHashes S.vp * signMax S m.length) := by
  apply simulate_cost
  have sample : WCount (weight S f) (liftM (rand pk) : OracleComp Spec _) 0 := by
    apply core_count (q := 0) (B := 0)
    · exact liftM_kindBound .hash (by decide) _
    · exact liftM_kindBound .prfmsg (by decide) _
    · apply IsQueryBoundP.of_imp _ (isQueryBoundP_liftM_isRight _)
      rintro (n|t) ht
      · exact False.elim (Nat.not_lt_zero _ ht)
      · rfl
  unfold openSignP
  have h := WCount.bind sample (fun r =>
    WCount.bind (wCount_liftM_query (weight S f) (.inr (.inr (.inr (skPrf,r,m))))
      (le_refl (msgPrfCalls S m.length))) (signCore_count S f pk.pkSeed pk.pkRoot · m))
  rw [Nat.zero_add] at h
  kexact h

theorem check_cost (pk : PublicKeyCore (P₀).core)
    (z : List Byte × GeneralScheme.SignatureCore S.vp (P₀).core) (log : SigLog S.vp P₀) :
    EvalCost (fun H => simulateQ (fun t => pure (hashPort S f H t) : QueryImpl _ ProbComp)
      (sufCheckOpen pk z log)) ((1 + Resources2.verifyHashes S.vp) * signMax S z.1.length) := by
  apply EvalCost.simulateQ _ (hashCalls S f) (hashPort_cost S f)
  refine cappedCount _ (fun _ => True) _ (fun _ h => (h trivial).elim) _ _ (sufCheckOpen_bound pk z log) ?_
  apply Realize.Prf.sufCheckOpen_ph
  · intro key xs hx
    change ¬signMax S z.1.length < thashCalls S xs.length
    rcases hx with h|h|h|h <;> rw [h] <;> unfold signMax keygenMax <;> omega
  · exact (isQueryBoundP_query_iff _ _ _).2 fun h => False.elim ((not_lt_of_ge (le_max_right ..)) h)

end Reduction.Compression.SkGame
#print axioms Reduction.Compression.SkGame.keygen_count
#print axioms Reduction.Compression.SkGame.signCore_count
#print axioms Reduction.Compression.SkGame.sign_cost
#print axioms Reduction.Compression.SkGame.check_cost
