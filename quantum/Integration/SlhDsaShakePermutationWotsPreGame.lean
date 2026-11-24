import Integration.SlhDsaShakePermutationWotsPreSelect
import Integration.SlhDsaShakePermutationSparseNumbers

namespace Reduction.ShakePermutation.SparsePort.Wots.Pre
open Classical MLink SLHDSA SLHDSA.Security OracleComp OracleSpec PQ.Interactive PQ.QROM Quantum ENNReal TweakableHash SetOracle Phase
open scoped ComplexOrder
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
variable (S : Sha2Set) (seeds : ProbComp S.Node) {E : Type} [Fintype E] [DecidableEq E]
local notation "Work" => WS Port Words E
variable (A : QSM_DT_PRE_Adversary (WS Port Words E) (ShakeXof.basePre S seeds))
variable (invert : (Port → Words) → A.State → S.Node → Closed (WS Port Words E) (ℕ × S.Node))

def adversary (π : Permutation) : QSM_DT_PRE_Adversary Work (game S seeds (fun _ => π)) where
  State := A.State
  choose := A.choose
  invert := invert (oracle π)
  ρ₀ := A.ρ₀
  posSemidef := A.posSemidef
  trace_eq_one := A.trace_eq_one
theorem qrun {D L V : Type} [Fintype V] (f : Bytes 32 → Words → Words)
    (sel : Select.Prog D) (post : D → Closed V L) (ρ : Matrix V V ℂ) (E' : L → Prop) [DecidablePred E'] :
    qWeight E' (liftU (simulateQ (Select.close f) sel) >>= post) ρ =
      Phase.run f (fun x => qWeight E' (post x) ρ) sel := by
  induction sel using OracleComp.inductionOn with
  | pure x => simp only [simulateQ_pure,liftU_pure,pure_bind]; rfl
  | query_bind i k ih =>
    simp only [simulateQ_bind,simulateQ_spec_query]
    rcases i with n|⟨d,w⟩
    · change qWeight E' (liftU (liftM (unifSpec.query n) >>= _) >>= post) ρ = _
      rw [liftU_query_bind,bind_assoc,qWeight_unif_bind]
      change _ = uniformMean (fun x : Fin (n+1) => Phase.run f _ (k x))
      simp only [← ih,uniformMean,unifW,Fintype.card_fin,Nat.cast_add,Nat.cast_one,← Finset.mul_sum]
    · change qWeight E' (liftU (pure (f d w) >>= _) >>= post) ρ = _
      rw [pure_bind]
      exact ih _


def finish (F : Row S → S.Node) (log : List (Bytes 32 × S.Node)) (jm : ℕ × S.Node) : ProbComp Bool :=
  match log[jm.1]? with
  | none => pure false
  | some tx => pure (decide (F (tx.1,jm.2) = F tx))

def test (pk : S.Node) (H : Port → Words) (F : Row S → S.Node) (r : A.State × History S) :=
  qWeight (· = true) (invert H r.1 pk >>= fun jm => liftU (finish S F r.2.1 jm)) A.ρ₀

private theorem normalized (pk : S.Node) (f : Bytes 32 → Words → Words) (H : Port → Words)
    (F : Row S → S.Node) :
    qWeight (· = true) (liftU ((simulateQ (SM_DT_PRE_oracles (game S seeds f) pk) A.choose).run ([],[])) >>= fun r =>
      invert H r.1 pk >>= fun jm => liftU (finish S F r.2.1 jm)) A.ρ₀ =
      Phase.run f (test S seeds A invert pk H F) (prog S pk A.choose ([],[])) := by
  rw [close_prog S seeds pk f A.choose ([],[]),qrun]; rfl

private theorem model (q : ℕ) (pk : S.Node) (st : A.State)
    (cost : PUE (spec:=unifSpec) cnt0 (fun H => invert H st pk) q) :
    ∃ N : HybridModel Port Words (ℕ × S.Node) q, ∀ H (ev : ℕ × S.Node → Prop) [DecidablePred ev],
      N.prob H ev = qWeight ev (invert H st pk) A.ρ₀ := by
  obtain ⟨ρ,he⟩ := exists_subState (A := (Port × Words) × E) A.ρ₀ A.posSemidef A.trace_eq_one
  obtain ⟨N,hN⟩ := cost.exists_model ρ
  exact ⟨N,fun H ev _ => (hN H ev).trans (by rw [he])⟩

def random_loss (q : ℕ) : ℝ≥0∞ :=
  (2*((3*q : ℕ):ℝ≥0∞)+1)^2 * ((Fintype.card S.Node : ℝ≥0∞)⁻¹ + (Fintype.card S.Node : ℝ≥0∞)⁻¹)

private theorem ideal_bound (pk : S.Node) (π : Permutation) (s : Row S → SkFormat.Suffix S)
    (base : Row S) (q : ℕ) (hq : ∀ st, PUE (spec:=unifSpec) cnt0 (fun H => invert H st pk) q) :
    uniformMean (fun F : Row S → S.Node => Phase.ideal (SkFormat.split S) (input S pk) base Prod.fst
      (prog S pk A.choose ([],[])) (test S seeds A invert pk) π (F,s)) ≤ random_loss S q := by
  let a := input S pk
  let f (R : Row S → S.Node) := shadow (SkFormat.split S) a π s Prod.fst R
  let H (R : Row S → S.Node) := simulatedPort (SkFormat.split S) a π s base R
  let th (R : Row S → S.Node) (p : S.Node) (d : Bytes 32) (m : S.Node) := Wots.value S (f R) p d [m]
  let ce (R : Row S → S.Node) (_ : Unit) (p : S.Node) (d : Bytes 32) (xs : List S.Node) := Wots.value S (f R) p d xs
  have leaf : ∀ R d m, th R pk d m = R (d,m) := value_leaf S pk π s
  have b := pre_row_avg_le (ShakeXof.basePre S seeds) pk th leaf ce
    (fun R G _ d xs he => value_local S pk π s R G d xs he) A.choose
    (fun R st => invert (H R) st pk) A.ρ₀ (3*q) (fun st => by
      obtain ⟨N,hN⟩ := model S seeds A invert q pk st (hq st)
      exact ⟨publicModel (SkFormat.split S) a π s base N,fun R ev _ => hN _ _⟩)
  apply le_trans (le_of_eq _) b
  apply Finset.sum_congr rfl
  intro R _
  apply congrArg (fun u => unifW _ R * u)
  simp_rw [leaf]
  kexact (normalized S seeds A invert pk (f R) (H R) R).symm

private theorem actual_eq (pk : S.Node) (π : Permutation) :
    preInner (adversary S seeds A invert π) pk =
      Phase.actual (SkFormat.split S) (input S pk) (prog S pk A.choose ([],[])) (test S seeds A invert pk) π := by
  let F := exactTable (SkFormat.split S) (input S pk) π
  have leaf (d : Bytes 32) (m : S.Node) : Wots.value S (fun _ => π) pk d [m] = F (d,m) := by
    rw [Wots.value,ite_eq_left (one_fits _ _ _ _),Select.value_actual]
    exact Arity.hash_eq S 1 pk (by decide) π (asArity S (d,m))
  refine Eq.trans ?_ (normalized S seeds A invert pk (fun _ => π) (oracle π) F)
  unfold preInner
  apply congrArg (fun h : Closed Work Bool => qWeight (· = true) h A.ρ₀)
  apply bind_congr
  intro r
  apply bind_congr
  intro jm
  unfold finish
  cases e : r.2.1[jm.1]? with
  | none => rfl
  | some tx =>
    exact congrArg (fun b => (liftU (pure b : ProbComp Bool) : Closed Work Bool))
      (congrArg₂ (fun l r => decide (l = r)) (leaf tx.1 jm.2) (leaf tx.1 tx.2))

def loss (q Q : ℕ) : ℝ≥0∞ :=
  random_loss S q + (Q*Classic.forestPenalty Rate Words Q + Q*((Fintype.card (Row S):ℝ≥0∞)/Fintype.card Words)) +
    (((2:ℝ≥0∞)^63)⁻¹+((2:ℝ≥0∞)^384)⁻¹)

private theorem swap {X Y : Type} [Fintype X] [Fintype Y] (g : X → Y → ℝ≥0∞) :
    uniformMean (fun x => uniformMean (g x)) = uniformMean (fun y => uniformMean (fun x => g x y)) := by
  unfold uniformMean; simp only [Finset.mul_sum]; rw [Finset.sum_comm]; simp only [mul_left_comm]

theorem fixed (pk : S.Node) (q Q : ℕ)
    (hq : ∀ st, PUE (spec:=unifSpec) cnt0 (fun H => invert H st pk) q)
    (count : CountBound (fun i => i.isRight = true) (simulateQ Phase.erase (prog S pk A.choose ([],[]))) Q) :
    uniformMean (fun π => preInner (adversary S seeds A invert π) pk) ≤ loss S q Q := by
  let base : Row S := default
  have zcap : 2^1344 ≤ Fintype.card (SkFormat.Suffix S) := by rw [SkFormat.card_suffix]; cases S <;> decide +kernel
  have jcap : Fintype.card (Row S) ≤ 2^768 := (Fintype.card_le_of_embedding (asArity S)).trans (Arity.row_bits S 1 (by decide))
  have lim (H : Port → Words) (F : Row S → S.Node) (r : A.State × History S) : test S seeds A invert pk H F r ≤ 1 :=
    qWeight_le_one _ _ A.posSemidef A.trace_eq_one
  simp_rw [actual_eq S seeds A invert pk]
  apply (phase_transfer (SkFormat.split S) (input S pk) base Prod.fst _ _ jcap zcap (valid_prog _ _ _ _) lim Q count).trans
  apply add_le_add (add_le_add _ le_rfl) le_rfl
  apply ShakeXof.mean_le_const
  intro π
  rw [swap]
  exact ShakeXof.mean_le_const (fun s => ideal_bound S seeds A invert pk π s base q hq)

theorem bound (q Q : ℕ)
    (hq : ∀ st pk, PUE (spec:=unifSpec) cnt0 (fun H => invert H st pk) q)
    (count : ∀ pk, CountBound (fun i => i.isRight = true) (simulateQ Phase.erase (prog S pk A.choose ([],[]))) Q) :
    uniformMean (fun π => qSM_DT_PRE_Advantage (adversary S seeds A invert π)) ≤ loss S q Q := by
  simp only [qSM_DT_PRE_Advantage_eq_tsum]
  change uniformMean (fun π => ∑' pk, PQ.Interactive.prob seeds (· = pk) * preInner (adversary S seeds A invert π) pk) ≤ _
  rw [ShakeXof.mean_seed]
  calc _ ≤ ∑' pk, PQ.Interactive.prob seeds (· = pk) * loss S q Q :=
          tsum_le_tsum fun pk => mul_le_mul' le_rfl (fixed S seeds A invert pk q Q (fun st => hq st pk) (count pk))
       _ = (∑' pk, PQ.Interactive.prob seeds (· = pk)) * loss S q Q := ENNReal.tsum_mul_right
       _ ≤ _ := (mul_le_mul' (tsum_prob_eq_le_one _) le_rfl).trans (one_mul _).le

end
end Reduction.ShakePermutation.SparsePort.Wots.Pre
#print axioms Reduction.ShakePermutation.SparsePort.Wots.Pre.bound
