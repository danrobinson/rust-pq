import Integration.SlhDsaShakePermutationFixSignature
import Integration.SlhDsaShakeSetPrecision

namespace Reduction.ShakePermutation.Fix.Machine
open MLink SLHDSA SLHDSA.Security Quantum PQ.Interactive OracleComp OracleSpec ENNReal Classical
open scoped ComplexOrder

def signingCost : ℕ ⊕ Msg → Bool
  | .inl _ => false
  | .inr _ => true

def signedCap (c : Caps) : ℕ ⊕ Msg → Prop
  | .inl _ => True
  | .inr mc => mc.1.length + mc.2.length + 2 ≤ c.ml

private theorem count_transfer {i α : Type} {s : OracleSpec i} (p q : i → Prop)
    [dp : DecidablePred p] [dq : DecidablePred q] (h : p = q) (a : OracleComp s α) (n : ℕ) :
    CountBound p a n → CountBound q a n := by
  subst q
  cases Subsingleton.elim dp dq
  exact id

variable (S : Sha2Set) (N L : ℕ) {T : ℕ} {U : Type} [Fintype U] [DecidableEq U]
variable (A : Access (ShakeApi.Input N) (Bytes S.vp.params.m)) (base : ShakeApi.Input N)
variable (F : Forger U T) (r : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node)

/-- Security of a simulator with a private completion, arbitrary intermediate
quantum instruments, and up to eight corrected-table reads per benchmark
permutation call. The signing oracle is the byte-level SHAKE API. -/
theorem corrected_signature_precise (c : Caps) (msg : c.ml = 65536) (fit : 65536+3*S.vp.params.n ≤ N)
    (hl : L ≤ 483) (hq : ∀ pk, CountBound (fun i => mark true (fun _ => false) i = true) (F.main pk) (8*2^40))
    (hs : ∀ pk, CountBound (fun i => mark false signingCost i = true) (F.main pk) 1)
    (hc : ∀ pk, AllQueries (allowed (signedCap c)) (capOut c) (F.main pk)) :
    let action := fun H => idealForger A L F H (ShakeApi.scheme S r seeds (ShakeApi.extend H))
    SetOracle.uniformMean (fun H => qStrongUnforgeableAdvantage (action H)) ≤ ((2:ℝ≥0∞)^(8*S.vp.params.n-119))⁻¹ ∧
    SetOracle.uniformMean (fun H => qUnforgeableAdvantage (action H)) ≤ ((2:ℝ≥0∞)^(8*S.vp.params.n-119))⁻¹ := by
  intro action
  let base : ShakeApi.Input N := BList.ofList [] (by simp)
  let G := rawForger A L base F
  have number : (8*L+4)*(8*2^40) ≤ (8*483+4)*(8*2^40) := by omega
  have ports (pk) : CountBound isPort (G.main pk) ((8*483+4)*(8*2^40)) := by
    apply count_mono _ _ number
    apply count_transfer (fun i => mark true (fun _ => false) i = true) _ ?_
    · exact raw_count A L base true _ _ _ (hq pk)
    · funext i
      rcases i with _ | _ | _ <;> simp [isPort]
  have signs (pk) : CountBound isSign (G.main pk) 1 := by
    apply count_transfer (fun i => mark false signingCost i = true) _ ?_
    · exact raw_count A L base false _ _ _ (hs pk)
    · funext i
      rcases i with _ | _ | _ | _ <;> simp [isSign,signingCost]
  have cap (pk) : AllQueries (capIdx c) (capOut c) (G.main pk) := by
    have eq : (capIdx c : FIdx (ShakeApi.Input N) (Bytes S.vp.params.m) (Access.Scratch T U) → Prop) = allowed (signedCap c) := by
      funext i
      rcases i with _ | _ | _ | _ <;> rfl
    rw [eq]
    exact raw_cap A L base _ _ _ (hc pk)
  obtain ⟨bs,be⟩ := ShakeXof.signature_queries (Q := ShakeXof.expandedQueries) S N r seeds G (by decide) c msg fit ports signs cap
  have b := And.intro (bs.trans (ShakeXof.precision S).2) (be.trans (ShakeXof.precision S).2)
  have strong (H : ShakeApi.RawTable S N) :
      qStrongUnforgeableAdvantage (action H) = qStrongUnforgeableAdvantage (ShakeApi.rawForger S N r seeds G H) := by
    unfold qStrongUnforgeableAdvantage qStrongUnforgeableExperiment
    symm
    apply signature_weight
  have regular (H : ShakeApi.RawTable S N) :
      qUnforgeableAdvantage (action H) = qUnforgeableAdvantage (ShakeApi.rawForger S N r seeds G H) := by
    unfold qUnforgeableAdvantage qUnforgeableExperiment
    symm
    apply signature_weight
  simpa only [strong,regular] using b

theorem corrected_signature (c : Caps) (msg : c.ml = 65536) (fit : 65536+3*S.vp.params.n ≤ N)
    (hl : L ≤ 483) (hq : ∀ pk, CountBound (fun i => mark true (fun _ => false) i = true) (F.main pk) (8*2^40))
    (hs : ∀ pk, CountBound (fun i => mark false signingCost i = true) (F.main pk) 1)
    (hc : ∀ pk, AllQueries (allowed (signedCap c)) (capOut c) (F.main pk)) :
    let action := fun H => idealForger A L F H (ShakeApi.scheme S r seeds (ShakeApi.extend H))
    SetOracle.uniformMean (fun H => qStrongUnforgeableAdvantage (action H)) ≤ ((2:ℝ≥0∞)^7)⁻¹ ∧
    SetOracle.uniformMean (fun H => qUnforgeableAdvantage (action H)) ≤ ((2:ℝ≥0∞)^7)⁻¹ := by
  have e := corrected_signature_precise S N L A F r seeds c msg fit hl hq hs hc
  have le : ((2:ℝ≥0∞)^(8*S.vp.params.n-119))⁻¹ ≤ ((2:ℝ≥0∞)^7)⁻¹ := by
    apply ENNReal.inv_le_inv.mpr
    exact pow_le_pow_right₀ (by norm_num) (by cases S <;> decide)
  exact ⟨e.1.trans le,e.2.trans le⟩

end Reduction.ShakePermutation.Fix.Machine
#print axioms Reduction.ShakePermutation.Fix.Machine.corrected_signature
