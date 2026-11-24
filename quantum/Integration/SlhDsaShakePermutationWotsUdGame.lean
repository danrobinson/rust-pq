import Integration.SlhDsaShakePermutationWotsUdSelect
import Integration.SlhDsaShakePermutationWotsPreGame
import Integration.SlhDsaShakePermutationSparseDecision
import Integration.SlhDsaShakePermutationSparseReverse

namespace Reduction.ShakePermutation.SparsePort.Wots.Ud
open SetOracle Classical PQ.Interactive PQ.QROM Quantum ENNReal MLink SLHDSA TweakableHash Phase
noncomputable section
set_option maxRecDepth 12000
set_option maxHeartbeats 2000000
variable (S : Sha2Set) (seeds : ProbComp S.Node) {E : Type} [Fintype E] [DecidableEq E]
local notation "Work" => WS Port Words E
variable (A : QSM_DT_UD_Adversary (WS Port Words E) (ShakeXof.baseUd S seeds))
variable (dist : (Port → Words) → A.State → S.Node → Closed (WS Port Words E) Bool)
variable (pk : S.Node)
local notation "a" => input S pk
local notation "e" => SkFormat.split S
local notation "b" => (default : Row S)

def adversary (π : Permutation) : QSM_DT_UD_Adversary Work (game S seeds (fun _ => π)) where
  State := A.State
  pick := A.pick
  distinguish := dist (oracle π)
  ρ₀ := A.ρ₀
  posSemidef := A.posSemidef
  trace_eq_one := A.trace_eq_one

local notation "P" => fun w => prog S w pk A.pick ([],[])
def test (H : Port → Words) (_F : Row S → S.Node) (r : A.State × History S) := qWeight (· = true) (dist H r.1 pk) A.ρ₀
local notation "W" => test S seeds A dist pk

theorem normalized (w : SM_DT_UD_World) (f : Bytes 32 → Words → Words) (H : Port → Words) (F : Row S → S.Node) :
    qWeight (· = true) (liftU ((simulateQ (SM_DT_UD_oracles w (game S seeds f) pk) A.pick).run ([],[])) >>=
      fun r => dist H r.1 pk) A.ρ₀ = Phase.run f (W H F) (P w) := by
  rw [close_prog S w seeds pk f A.pick ([],[]),Pre.qrun]; rfl

def randomLoss (q : ℕ) := ENNReal.ofReal (8*((12*q:ℕ):ℝ)^2 / Fintype.card S.Node)
theorem ideal (π : Permutation) (s : Row S → SkFormat.Suffix S) (q : ℕ)
    (hq : ∀ st, PUE (spec := unifSpec) cnt0 (fun H => dist H st pk) q) :
    uniformMean (fun F : Row S → S.Node => Phase.ideal e a b Prod.fst (P .real) W π (F,s)) ≤
    uniformMean (fun F : Row S → S.Node => Phase.ideal e a b Prod.fst (P .ideal) W π (F,s)) + randomLoss S q := by
  let f := shadow e a π s Prod.fst
  let H := simulatedPort e a π s b
  let th := fun (R : Row S → S.Node) (p : S.Node) (d : Bytes 32) (m : S.Node) => Wots.value S (f R) p d [m]
  let ce := fun (R : Row S → S.Node) (_ : Unit) (p : S.Node) (d : Bytes 32) (xs : List S.Node) => Wots.value S (f R) p d xs
  have ht (st : A.State) : ∃ v : (Row S → S.Node) → ℝ≥0∞, Tight.TightAvgBound (fun R => (v R).toReal) (12*q) ∧
      ∀ R, v R = qWeight (· = true) (dist (H R) st pk) A.ρ₀ := by
    obtain ⟨m,hm,he⟩ := Lift.lift_machine e a π s b (hq st)
    let M := Workspace.state (Y := S.Node) b A.ρ₀
    obtain ⟨ρ,eq⟩ := exists_subState (A := Workspace.W (Row S) S.Node Work) M (Workspace.state_pos b A.ρ₀ A.posSemidef)
      ((Workspace.state_trace b A.ρ₀).trans A.trace_eq_one)
    obtain ⟨x,hx,hxw⟩ := hm.exists_prog_qprob
    exact ⟨_,Tight.qprob_tightAvgBound LocalSig.Interp.instruments x ρ _ hx (fun p => p.2 = true),
      fun R => (hxw (· = true) R ρ).trans (by rw [← eq]; exact he R _ _)⟩
  have key := ud_row_avg_le (ShakeXof.baseUd S seeds) pk th (value_leaf S pk π s) ce
    (fun R G _ d xs he => value_local S pk π s R G d xs he) rfl rfl A.pick (fun R st => dist (H R) st pk)
    A.ρ₀ A.posSemidef A.trace_eq_one (12*q) ht
  refine le_trans (le_of_eq ?_) (key.trans (le_of_eq ?_))
  · exact Finset.sum_congr rfl fun R _ => congrArg (unifW _ R * ·) (normalized S seeds A dist pk .real (f R) (H R) R).symm
  · exact congrArg₂ (· + ·) (Finset.sum_congr rfl fun R _ => congrArg (unifW _ R * ·) (normalized S seeds A dist pk .ideal (f R) (H R) R)) rfl

def penalty (Q : ℕ) : ℝ≥0∞ := Q * Classic.forestPenalty Rate Words Q + Q*((Fintype.card (Row S):ℝ≥0∞)/Fintype.card Words) + switchLoss
def loss (q Q : ℕ) := randomLoss S q + (penalty S Q + penalty S Q)
theorem fixed (q Q : ℕ) (hq : ∀ st, PUE (spec := unifSpec) cnt0 (fun H => dist H st pk) q)
    (hc : ∀ w, CountBound (fun i => i.isRight = true) (simulateQ Phase.erase (P w)) Q) :
    uniformMean (fun π => udInner .real (adversary S seeds A dist π) pk) ≤
    uniformMean (fun π => udInner .ideal (adversary S seeds A dist π) pk) + loss S q Q := by
  have fit := (Fintype.card_le_of_embedding (asArity S)).trans (Arity.row_bits S 1 (by decide))
  have suf : 2^1344 ≤ Fintype.card (SkFormat.Suffix S) := by rw [SkFormat.card_suffix]; cases S <;> decide +kernel
  have lim : ∀ H F r, W H F r ≤ 1 := fun _ _ _ => qWeight_le_one _ _ A.posSemidef A.trace_eq_one
  let r := fun w => uniformMean (Phase.actual e a (P w) W)
  let i := fun w => uniformMean (fun π : Permutation => uniformMean (fun F : Row S → S.Node =>
    uniformMean (fun s : Row S → SkFormat.Suffix S => Phase.ideal e a b Prod.fst (P w) W π (F,s))))
  have nat (w : SM_DT_UD_World) : uniformMean (fun π => udInner w (adversary S seeds A dist π) pk) = r w :=
    congrArg uniformMean (funext fun π => normalized S seeds A dist pk w (fun _ => π) (oracle π) _)
  have fw : r .real ≤ i .real + penalty S Q := by
    simpa only [r,i,penalty,switchLoss,add_assoc] using
      phase_transfer e a b Prod.fst (P .real) W fit suf (valid_prog S .real pk _ _) lim Q (hc .real)
  have rv : i .ideal ≤ r .ideal + penalty S Q := by
    simpa only [r,i,penalty,switchLoss,add_assoc] using
      phase_reverse e a b Prod.fst (P .ideal) W fit suf (valid_prog S .ideal pk _ _) lim Q (hc .ideal)
  have swap {X Y : Type} [Fintype X] [Fintype Y] (g : X → Y → ℝ≥0∞) :
      uniformMean (fun x => uniformMean (g x)) = uniformMean (fun y => uniformMean (fun x => g x y)) := by
    unfold uniformMean; simp only [Finset.mul_sum]; rw [Finset.sum_comm]; simp only [mul_left_comm]
  have mid : i .real ≤ i .ideal + randomLoss S q := by
    apply avg_shift
    intro π
    rw [swap,swap (fun (F : Row S → S.Node) (s : Row S → SkFormat.Suffix S) => Phase.ideal e a b Prod.fst (P .ideal) W π (F,s))]
    exact avg_shift _ _ _ (fun s => ideal S seeds A dist pk π s q hq)
  rw [nat,nat]
  exact (fw.trans (add_le_add (mid.trans (add_le_add rv le_rfl)) le_rfl)).trans_eq
    (by unfold loss; rw [add_assoc,add_assoc,add_left_comm (penalty S Q) (randomLoss S q)])

end
end Reduction.ShakePermutation.SparsePort.Wots.Ud
#print axioms Reduction.ShakePermutation.SparsePort.Wots.Ud.fixed
