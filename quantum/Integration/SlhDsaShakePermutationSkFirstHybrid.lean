import Integration.SlhDsaShakePermutationSkSignature
import Integration.SlhDsaSetEuf

/-! The first numerical term discharged in the strong unforgeability
reduction for the actual two-way shared permutation experiment. -/
namespace Reduction.ShakePermutation.SkCost
open Classical MLink SLHDSA SLHDSA.Security Quantum OracleComp OracleSpec PQ.Interactive PQ.QROM QMsg ENNReal SetOracle
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option allowUnsafeReducibility true in
attribute [local reducible] ShakeSecurity.primitives
variable (S : Sha2Set) (rand : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node)
    {E : Type} [Fintype E] [DecidableEq E] (F : PortForger Port Words E)
local notation "N" => ShakeApi.rawCap S 67 65536
local notation "P" => fun π : Permutation => ShakeApi.primitives S (ShakeApi.extend (table S N (oracle π)))
local notation "B" => fun π : Permutation => qPureBytesToInternal (capped S rand seeds F N π)
local notation "I" => fun π : Permutation => qPrfIdealPr (qbPrfMsgWL sufCheck (B π)) F.ρ₀
local notation "R" => fun π : Permutation => qPrfRealPr (msgPrf S.vp (P π)) (qbPrfMsgWL sufCheck (B π)) F.ρ₀

private theorem sk_same (π : Permutation) : skPrfC S.vp (P π) = skPrfC S.vp (primitives (lanes π) S.vp.params) := by
  unfold skPrfC
  congr 1
  funext k d
  let xs := d.1.toList ++ d.2.val.toVector.toList ++ k.toList
  change prefixBytes S.vp.params.n (ShakeApi.extend (table S N (oracle π)) xs) =
    hash (lanes π) (nd d.1 ++ nd d.2.val.toVector ++ nd k) S.vp.params.n
  have len : xs.length ≤ N := by
    simp only [xs,List.length_append,Vector.length_toList]
    cases S <;> decide +kernel
  rw [table,ShakeApi.extend_restrict _ _ _ _ len,hash_prefix]
  simp only [xs,sp_append]
  rfl

private theorem cancel {s i b r c e : ℝ≥0∞} (fin : i ≠ ⊤) (lin : s + (i+b) ≤ r+c) (sk : r ≤ i+e) :
    s+b ≤ c+e := by
  apply (ENNReal.add_le_add_iff_right fin).mp
  calc
    s+b+i = s+(i+b) := by ac_rfl
    _ ≤ (i+e)+c := lin.trans (add_le_add sk le_rfl)
    _ = c+e+i := by ac_rfl

/-- All terms still to be bounded appear on the two linear sides. SK.PRF
has been cancelled, with a loss of at most 2⁻⁴². The original signature
experiment and its forward/inverse port appear on the left. -/
theorem after_sk (c : Caps) (msg : c.ml = 65536)
    (hq : ∀ pk, CountBound isPort (F.main pk) (2^40))
    (hs : ∀ pk, CountBound isSign (F.main pk) 1)
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    strongAdvantage S rand seeds F + uniformMean (fun π => qLinearIdealSide (B π) 0 (I π)) ≤
      uniformMean (fun π => qLinearRealSide (B π) 0 (R π)) + ((2:ℝ≥0∞)^42)⁻¹ := by
  let I₁ := fun π : Permutation => qPrfIdealPr (machine S N rand seeds F (oracle π)) F.ρ₀
  let R₁ := fun π : Permutation => qPrfRealPr (skPrfC S.vp (primitives (lanes π) S.vp.params))
      (machine S N rand seeds F (oracle π)) F.ρ₀
  have real (π : Permutation) : qLinRealSuf (B π) = R₁ π + qLinearRealSide (B π) 0 (R π) := by
    let t := fun (curve : PRFScheme S.Node (S.Node × SkAdrs S.vp) S.Node) => qPrfRealPr curve (machine S N rand seeds F (oracle π)) F.ρ₀ +
        qLinearRealSide (B π) 0 (R π)
    have start : qLinRealSuf (B π) = t (skPrfC S.vp (P π)) := by
      simp only [t,qLinRealSuf,qLinearRealSide,zero_add,add_assoc]
      rfl
    exact start.trans (congrArg t (sk_same S π))
  have ideal (π : Permutation) : qLinIdealSuf (B π) = I₁ π + qLinearIdealSide (B π) 0 (I π) := by
    simp only [qLinIdealSuf,qLinearIdealSide,zero_add,I₁,add_assoc]
    rfl
  have law := avg_of_pointwise (unifW Permutation) _ _ _ (linear_reduction S rand seeds F N c (by rw [msg]) hc)
  have h : strongAdvantage S rand seeds F + uniformMean (fun π => qLinIdealSuf (B π)) ≤
      uniformMean (fun π => qLinRealSuf (B π)) := law
  simp_rw [real,ideal] at h
  have plus (a b : Permutation → ℝ≥0∞) : uniformMean (fun π => a π + b π) = uniformMean a + uniformMean b := by
    simp only [uniformMean,mul_add,Finset.sum_add_distrib]
  rw [plus,plus] at h
  have bound : uniformMean R₁ ≤ uniformMean I₁ + ((2:ℝ≥0∞)^42)⁻¹ := signature_component S rand seeds F hq hs
  have fin : uniformMean I₁ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top
    (ShakeXof.mean_le_const (fun π : Permutation => qPrfIdealPr_le_one' _ F.posSemidef F.trace_eq_one))
  exact cancel fin h bound

theorem euf_after_sk (c : Caps) (msg : c.ml = 65536)
    (hq : ∀ pk, CountBound isPort (F.main pk) (2^40))
    (hs : ∀ pk, CountBound isSign (F.main pk) 1)
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    advantage S rand seeds F + uniformMean (fun π => qLinearIdealSide (B π) 0 (I π)) ≤
      uniformMean (fun π => qLinearRealSide (B π) 0 (R π)) + ((2:ℝ≥0∞)^42)⁻¹ := by
  have euf : advantage S rand seeds F ≤ strongAdvantage S rand seeds F :=
    Finset.sum_le_sum (fun π _ => mul_le_mul' le_rfl (quantum_euf_le_suf (experiment S rand seeds F π)))
  exact (add_le_add euf le_rfl).trans (after_sk S rand seeds F c msg hq hs hc)

end Reduction.ShakePermutation.SkCost
#print axioms Reduction.ShakePermutation.SkCost.after_sk
