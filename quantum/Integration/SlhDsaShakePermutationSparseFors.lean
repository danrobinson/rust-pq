import Integration.SlhDsaShakePermutationSparseTcr
import Integration.SlhDsaShakeXofFors

namespace Reduction.ShakePermutation.SparsePort.Fors
open SetOracle Classical MLink SLHDSA TweakableHash OracleSpec OracleComp PQ.Interactive PQ.QROM Quantum ENNReal
open scoped ComplexOrder
noncomputable section
set_option maxRecDepth 12000
variable (S : Sha2Set)
abbrev Row := Bytes 32 × S.Node

def singleton : Row S ↪ Arity.Row S 1 where
  toFun j := (j.1,⟨[j.2],rfl⟩)
  inj' := by rintro ⟨t,x⟩ ⟨u,y⟩ h; simpa using h

def address (pk : S.Node) := (singleton S).trans (Arity.input S 1 pk (by decide))

def eval (pk : S.Node) (H : Port → Words) (F : Row S → S.Node)
    (p : S.Node) (t : Bytes 32) (m : S.Node) : S.Node :=
  if p = pk then F (t,m) else (primitives (lanes (fun w => H (false,w))) S.vp.params).Thash p t [m]

theorem exact_eval (pk : S.Node) (π : Permutation) :
    eval S pk (oracle π) (exactTable (SkFormat.split S) (address S pk) π) =
      fun p t m => (primitives (lanes π) S.vp.params).Thash p t [m] := by
  funext p t m
  by_cases eq : p = pk
  · subst p
    rw [eval,ite_eq_left rfl]
    exact (Arity.hash_eq S 1 pk (by decide) π (singleton S (t,m))).symm
  · rw [eval,ite_eq_right eq]; rfl

variable (seeds : ProbComp S.Node) {E : Type} [Fintype E] [DecidableEq E]
abbrev Base := ShakeXof.baseProblem S seeds
abbrev Work := ArityGame.Work E
variable (A : QTcrFV_Adversary (Work (E := E)) (Base S seeds))
variable (forge : (Port → Words) → A.State → S.Node → Closed (Work (E := E)) (ℕ × S.Node))

def player (H : Port → Words) (f : S.Node → Bytes 32 → S.Node → S.Node) :
    QTcrFV_Adversary (Work (E := E)) (fvWithEval (Base S seeds) f) where
  State := A.State
  choose := A.choose
  forge := forge H
  ρ₀ := A.ρ₀
  posSemidef := A.posSemidef
  trace_eq_one := A.trace_eq_one

def loss (q : ℕ) : ℝ≥0∞ := (2*((3*q : ℕ):ℝ≥0∞)+1)^2/Fintype.card S.Node +
  (((2:ℝ≥0∞)^63)⁻¹ + ((2:ℝ≥0∞)^384)⁻¹)

theorem fixed (pk : S.Node) (q : ℕ)
    (cost : ∀ st, PUE (spec := unifSpec) cnt0 (fun H => forge H st pk) q) :
    uniformMean (fun π => tcrFvInner (player S seeds A forge (oracle π)
      (fun p t m => (primitives (lanes π) S.vp.params).Thash p t [m])) pk) ≤ loss S q := by
  let e := SkFormat.split S
  let a := address S pk
  let base : Row S := (default,default)
  let W := fun H F => tcrFvInner (player S seeds A forge H (eval S pk H F)) pk
  have fit := (Fintype.card_le_of_embedding (singleton S)).trans (Arity.row_bits S 1 (by decide))
  have suffix : 2^1344 ≤ Fintype.card (SkFormat.Suffix S) := by rw [SkFormat.card_suffix]; cases S <;> decide +kernel
  have real (π : Permutation) : tcrFvInner (player S seeds A forge (oracle π)
      (fun p t m => (primitives (lanes π) S.vp.params).Thash p t [m])) pk =
      W (oracle π) (exactTable e a π) := by
    unfold W
    rw [exact_eval]
  simp_rw [real]
  apply (transfer e a base fit suffix W (fun H F => qWeight_le_one _ _ A.posSemidef A.trace_eq_one)).trans
  apply add_le_add _ le_rfl
  apply ShakeXof.mean_le_const
  intro π
  have swap {X Y : Type} [Fintype X] [Fintype Y] (g : X → Y → ℝ≥0∞) :
      uniformMean (fun x => uniformMean (g x)) = uniformMean (fun y => uniformMean (fun x => g x y)) := by
    unfold uniformMean
    simp only [Finset.mul_sum]; rw [Finset.sum_comm]; simp only [mul_left_comm]
  rw [swap]
  apply ShakeXof.mean_le_const
  intro s
  let H := simulatedPort e a π s base
  apply tcrFv_row_avg_le (Base S seeds) pk (fun R => eval S pk (H R) R)
    (fun R t m => ite_eq_left rfl) A.choose (fun R st => forge (H R) st pk) A.ρ₀ (3*q)
  intro st
  obtain ⟨ρ,he⟩ := exists_subState (A := (Port × Words) × E) A.ρ₀ A.posSemidef A.trace_eq_one
  obtain ⟨M,hM⟩ := (cost st).exists_model ρ
  exact ⟨publicModel e a π s base M,fun R ev _ => (hM _ ev).trans (by rw [he])⟩

theorem bound (q : ℕ) (cost : ∀ st pk, PUE (spec := unifSpec) cnt0 (fun H => forge H st pk) q) :
    uniformMean (fun π => qTcrFV_Advantage (player S seeds A forge (oracle π)
      (fun p t m => (primitives (lanes π) S.vp.params).Thash p t [m])) ) ≤ loss S q := by
  simp only [qTcrFV_Advantage_eq_tsum]
  change uniformMean (fun π => ∑' pk, PQ.Interactive.prob seeds (· = pk) * _) ≤ _
  rw [ShakeXof.mean_seed]
  calc _ ≤ ∑' pk, PQ.Interactive.prob seeds (· = pk) * loss S q :=
          tsum_le_tsum fun pk => mul_le_mul' le_rfl (fixed S seeds A forge pk q (fun st => cost st pk))
       _ = (∑' pk, PQ.Interactive.prob seeds (· = pk)) * loss S q := ENNReal.tsum_mul_right
       _ ≤ _ := (mul_le_mul' (tsum_prob_eq_le_one _) le_rfl).trans (one_mul _).le

end
end Reduction.ShakePermutation.SparsePort.Fors
#print axioms Reduction.ShakePermutation.SparsePort.Fors.bound
