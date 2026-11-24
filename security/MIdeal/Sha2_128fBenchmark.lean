import MIdeal.Sha2_128f
import Ideal.Inst.ItsrNumeric

namespace MIdeal.Sha2_128f
open Ideal Ideal.Realize MLink SLHDSA SLHDSA.Security OracleComp OracleSpec Reduction Reduction.Open ENNReal
open Class128f (vp)
attribute [local irreducible] reuseSum tcrTargets wotsInsts Lazy.sparseTable Lazy.structSecIdx
set_option maxRecDepth 1500
set_option exponentiation.threshold 512

theorem reuse_128f (n m c : ℕ) (hn : n ≤ 2 ^ m) (hm : m ≤ 66)
    (hc : 2 * m + 123 + c ≤ 264) :
    reuseSum 66 6 33 n ≤ ((2 : ℝ≥0∞) ^ c)⁻¹ := by
  set ρ : ℝ≥0∞ := (n : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ 66)⁻¹ with hρdef
  have hρ : ρ ≤ 1 := by
    have h1 : (n : ℝ≥0∞) ≤ 2 ^ 66 := by
      exact_mod_cast hn.trans (Nat.pow_le_pow_right (by norm_num) hm)
    calc ρ ≤ 2 ^ 66 * ((2 : ℝ≥0∞) ^ 66)⁻¹ := mul_le_mul h1 le_rfl zero_le zero_le
      _ = 1 := ENNReal.mul_inv_cancel (by positivity) (by simp)
  have hP : ∏ i ∈ Finset.range 33, ((i : ℝ≥0∞) + ρ) ≤ ((8683317618811886495518194401280000000 : ℕ) : ℝ≥0∞) * ρ := by
    rw [Finset.prod_range_succ']
    refine mul_le_mul ?_ (by simp) zero_le zero_le
    calc ∏ i ∈ Finset.range 32, (((i + 1 : ℕ) : ℝ≥0∞) + ρ)
        ≤ ∏ i ∈ Finset.range 32, (((i + 1 : ℕ) : ℝ≥0∞) + 1) :=
          Finset.prod_le_prod (fun i _ => add_le_add le_rfl hρ)
      _ = ((∏ i ∈ Finset.range 32, (i + 2) : ℕ) : ℝ≥0∞) := by
          push_cast; exact Finset.prod_congr rfl (fun i _ => by ring)
      _ = ((8683317618811886495518194401280000000 : ℕ) : ℝ≥0∞) := by congr 1
  calc reuseSum 66 6 33 n
      ≤ n * (((2 : ℝ≥0∞) ^ 6)⁻¹) ^ 33 * ∏ i ∈ Finset.range 33, ((i : ℝ≥0∞) + ρ) :=
        reuseSum_le_prod _ _ _ _
    _ ≤ n * ((2 : ℝ≥0∞) ^ 198)⁻¹ * (((8683317618811886495518194401280000000 : ℕ) : ℝ≥0∞) * ρ) := by
        rw [← ENNReal.inv_pow, ← pow_mul]; exact mul_le_mul le_rfl hP zero_le zero_le
    _ = ((n * n * 8683317618811886495518194401280000000 : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ 264)⁻¹ := by
        rw [hρdef, show (264 : ℕ) = 198 + 66 from rfl, pow_add,
          ENNReal.mul_inv (by simp) (by simp)]
        push_cast; ring
    _ ≤ ((2 : ℝ≥0∞) ^ c)⁻¹ := natMul_inv_pow_le _ _ _ (by
        calc n * n * 8683317618811886495518194401280000000 * 2 ^ c ≤ 2 ^ m * 2 ^ m * 2 ^ 123 * 2 ^ c := by
              gcongr; norm_num
          _ = 2 ^ (2 * m + 123 + c) := by ring
          _ ≤ 2 ^ 264 := Nat.pow_le_pow_right (by norm_num) hc)


private abbrev q : ℕ := 2^40
private abbrev qs : ℕ := 2^20
private abbrev L : ℕ := 4096
private noncomputable abbrev ε : ℝ≥0∞ := ((2 : ℝ≥0∞)^56)⁻¹

private theorem twoTerms {x y : ℝ≥0∞} (hx : x ≤ ε) (hy : y ≤ ε) : x+y ≤ 2*ε :=
  (add_le_add hx hy).trans_eq (two_mul ε).symm

private theorem skNum : Secret128f.loss q qs L ≤ 2*ε := by
  unfold Secret128f.loss
  simp only [div_eq_mul_inv]
  apply twoTerms <;> apply natMul_inv_pow_le <;> decide

private theorem msgNum : Msg128f.loss q qs L ≤ 2*ε := by
  unfold Msg128f.loss
  simp only [div_eq_mul_inv]
  apply twoTerms
  · rw [show (2:ℝ≥0∞) = (↑(2:ℕ):ℝ≥0∞) from rfl, ← Nat.cast_mul]
    apply natMul_inv_pow_le
    decide
  · apply natMul_inv_pow_le; decide

private theorem itsrNum : Itsr128f.loss q qs L ≤ 2*ε := by
  unfold Itsr128f.loss
  apply twoTerms
  · apply reuse_128f _ 42 56 <;> decide
  · apply natMul_inv_pow_le; decide

private theorem dsprNum : Fors128f.dsprLoss ≤ ε := by
  unfold Fors128f.dsprLoss
  apply natMul_inv_pow_le; decide

private theorem forsNum : Fors128f.tcrLoss q qs L ≤ 2*ε := by
  unfold Fors128f.tcrLoss
  apply twoTerms <;> apply natMul_inv_pow_le <;> decide

private theorem preNum : Wots128f.preLoss q qs L ≤ 2*ε := by
  unfold Wots128f.preLoss
  apply twoTerms
  · rw [show (2:ℝ≥0∞) = (↑(2:ℕ):ℝ≥0∞) from rfl, ← Nat.cast_mul]
    apply natMul_inv_pow_le; decide
  · apply natMul_inv_pow_le; decide

private theorem wotsNum : Wots128f.tcrLoss q qs L ≤ 2*ε := by
  unfold Wots128f.tcrLoss
  apply twoTerms <;> apply natMul_inv_pow_le <;> decide

private theorem udNum : Wots128f.udLoss q qs L ≤ 2*ε := by
  unfold Wots128f.udLoss
  apply twoTerms <;> apply natMul_inv_pow_le <;> decide

private noncomputable def clsValue (n t Q : ℕ) : ℝ≥0∞ :=
  let b := (22+16*n+8)/64
  let w := (22+16*35+8)/64
  (Q + 2*b + 4 : ℕ) * ((2:ℝ≥0∞)^128)⁻¹ +
    (18 * tcrMultiQ 0 t t w Q b ^ 2 + (t+t)*(1+2*max b w)+1 : ℕ) * ((2:ℝ≥0∞)^256)⁻¹

private theorem classNum (ar : ℕ) (ha : ar = 1 ∨ ar = 2 ∨ ar = vp.params.len ∨ ar = vp.params.k) :
    Class128f.classLoss ar q qs L ≤ 2*ε := by
  let Q := Class128f.forgeBudget q qs L
  have eval : Class128f.classLoss ar q qs L = clsValue ar (tcrTargets vp) Q := rfl
  have he := congrArg (fun t => clsValue ar t Q) MReduction.tcrTargets_128f_val
  refine (eval.trans he).le.trans ?_
  unfold clsValue
  rcases ha with rfl|rfl|rfl|rfl <;> apply twoTerms <;> apply natMul_inv_pow_le <;> decide

theorem benchmark_loss : loss (2^40) (2^20) 4096 ≤ ((2:ℝ≥0∞)^50)⁻¹ := by
  unfold loss
  have steps : (vp.params.w-2 : ℕ) = 14 := by decide
  rw [steps]
  calc
    _ ≤ (2*ε) + (2*ε) + (2*ε) + (ε + 3*(2*ε)) + ((2*ε)+(2*ε)+(2*ε)+(2*ε)) +
          (↑(14:ℕ) : ℝ≥0∞)*(2*ε) + (2*ε) + (2*ε) := by
      have hclass := add_le_add (add_le_add (add_le_add (classNum 1 (Or.inl rfl)) (classNum 2 (Or.inr (Or.inl rfl))))
        (classNum vp.params.len (Or.inr (Or.inr (Or.inl rfl))))) (classNum vp.params.k (Or.inr (Or.inr (Or.inr rfl))))
      exact add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add skNum msgNum) itsrNum)
        (add_le_add dsprNum (mul_le_mul le_rfl forsNum zero_le zero_le))) hclass) (mul_le_mul le_rfl udNum zero_le zero_le)) preNum) wotsNum
    _ = (53:ℕ)*ε := by push_cast; ring
    _ ≤ _ := natMul_inv_pow_le 53 56 50 (by decide)
/-- At most 2⁴⁰ SHA-256 port queries, 2²⁰ signing queries, and 4096-byte
messages, with unrestricted access to the independent SHA-512 table. -/
theorem benchmark (rand : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) (seeds : ProbComp (Bytes 16))
    (A : PureCompression.Forger)
    (hq : ∀ pk, IsQueryBoundP (A.main pk) (fun i => PureCompression.retained isPortQP i = true) (2^40))
    (hs : ∀ pk, IsQueryBoundP (A.main pk) (fun i => PureCompression.retained isSignQP i = true) (2^20))
    (hl : ∀ pk, IsQueryBoundP (A.main pk) (fun i => PureCompression.retained (isLongQP 4096) i = true) 0)
    (ho : ∀ pk z, z ∈ support (A.main pk) → z.1.1.length ≤ 4096) :
    PureCompression.average (fun g => SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp
      (PureCompression.strong Sha2Set.s128f rand seeds A g)) ≤ ((2:ℝ≥0∞)^50)⁻¹ ∧
    PureCompression.average (fun g => SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp
      (PureCompression.strong Sha2Set.s128f rand seeds A g).toUnforgeableAdversary) ≤ ((2:ℝ≥0∞)^50)⁻¹ := by
  have hcap : 4*Fors128f.budget (2^40) (2^20) 4096 ≤ 2^128 := by decide
  exact ⟨(suf rand seeds A _ _ _ hq hs hl ho hcap).trans benchmark_loss,
    (euf rand seeds A _ _ _ hq hs hl ho hcap).trans benchmark_loss⟩

end MIdeal.Sha2_128f
#print axioms MIdeal.Sha2_128f.benchmark_loss

#print axioms MIdeal.Sha2_128f.benchmark
