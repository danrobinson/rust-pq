import Integration.SlhDsaShakePermutationItsrCircuit
import Integration.SlhDsaShakePermutationSparseLift

namespace Reduction.ShakePermutation.ItsrCircuit
open Classical Quantum Fix Fix.Circuit ItsrLabel SparsePort PQ.Interactive OracleSpec OracleComp
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 1200000
variable {E α : Type} [Fintype E] [DecidableEq E]
local notation "U" => WS Port Words E
local notation "New" => WS Addr Words (Mem U)
local notation "prepared" => SparsePort.Workspace.state (Y := Words) base

private theorem move_general {X Y : Type} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y] [AddCommGroup Y]
    (b : X) (c : Circuit X Y (SparsePort.Aux Y U)) (H : X → Y) (g : Port → Words)
    (law : ∀ (u : U), c.run H ((b,0),(0,u)) = ((b,0),(0,SparsePort.Lift.add (g (SparsePort.Lift.select u)) u)))
    (ρ : Matrix U U ℂ) :
    transport (c.run H) (SparsePort.Workspace.state b ρ) =
      SparsePort.Workspace.state b ((portInstr g).branch 0 ρ) := by
  let z := ((Circuit.port (Z := E)).run g).prodCongr (Equiv.refl Unit)
  have old : (portInstr g).branch 0 ρ = MatrixMap.conj (basisMatrix z) ρ := by rw [port_branch,conj_basisMatrix_equiv]; rfl
  rw [old]
  unfold SparsePort.Workspace.state
  rw [transport_embedding,← LinearMap.comp_apply,← MatrixMap.conj_mul,← basisMatrix_comp]
  apply congrArg (fun f => MatrixMap.conj (basisMatrix f) ρ)
  funext u
  unfold SparsePort.Workspace.embed
  rw [law]
  rfl

private theorem eval_three {X Y Z W : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
    [Fintype W] [DecidableEq W] (i : X) (j : Y → X) (k : Y → Y → X) (out : Y → Y → Y → Z)
    (f : Z → (X → Y) → Closed (WS X Y W) α) (q : ℕ) (hf : ∀ z, PUE (spec := unifSpec) cnt0 (f z) q) :
    PUE (spec := unifSpec) cnt0 (fun H => let a := H i; let b := H (j a); f (out a b (H (k a b))) H) (q+3) :=
  PUE.eval i _ _ (fun a => PUE.eval (j a) _ _ (fun b => PUE.eval (k a b) _ _ (fun _ => hf _)))

private theorem eval_cost (π : Permutation) (p : Port) (q : ℕ) (f : Words → Table → Closed New α)
    (hf : ∀ z, PUE (spec := unifSpec) cnt0 (f z) q) :
    PUE (spec := unifSpec) cnt0 (fun H => f (oracle (perm π H) p) H) (q+3) := by
  obtain ⟨d,w⟩ := p
  cases d with
  | false =>
    let u := fun a : Words => π (ShakePermutation.mask (fun _ => capOf a) w)
    let z := fun a b : Words => ShakePermutation.mask (fun _ => capOf b) (u a)
    exact eval_three (ItsrLabel.mask false (rateOf w)) (fun a => ItsrLabel.mask true (rateOf (u a)))
      (fun a b => tailHead (capOf (z a b))) (fun a b c => shear (fun _ => rateOf c) (z a b)) f q hf
  | true =>
    let u := fun a : Words => shear (fun _ => rateOf a) w
    let z := fun a b : Words => π.symm (ShakePermutation.mask (fun _ => capOf b) (u a))
    exact eval_three (tailHead (capOf w)) (fun a => ItsrLabel.mask true (rateOf (u a)))
      (fun a b => ItsrLabel.mask false (rateOf (z a b))) (fun a b c => ShakePermutation.mask (fun _ => capOf c) (z a b)) f q hf

theorem lift_machine (π : Permutation) {m : (Port → Words) → Closed U α} {q : ℕ}
    (hm : PUE (spec := unifSpec) cnt0 m q) :
    ∃ m' : Table → Closed New α, PUE (spec := unifSpec) cnt0 m' (16*q) ∧
    ∀ H ev [DecidablePred ev] (M : Matrix U U ℂ), qWeight ev (m' H) (prepared M) = qWeight ev (m (oracle (perm π H))) M := by
  induction hm with
  | pure x q => exact ⟨_,PUE.pure x _,fun H ev _ M => by simp only [qWeight_pure,SparsePort.Workspace.state_trace]⟩
  | instr j k q _ ih =>
    choose f hf he using ih
    refine ⟨_,PUE.instr (SparsePort.Workspace.liftIdx (X := Addr) (Y := Words) (framedIdx j)) f _ hf,?_⟩
    intro H ev _ M
    rw [qWeight_instr_bind,qWeight_instr_bind]
    exact Finset.sum_congr rfl fun i _ => (congrArg _ (SparsePort.Workspace.lift_branch base (framedIdx j) i M)).trans (he i H ev _)
  | port k q _ ih =>
    obtain ⟨f,hf,he⟩ := ih
    let c := nativePort (SparsePort.Lift.select (E := E)) π SparsePort.Lift.add
    have co : c.cost = 16 := public_cost ..
    refine ⟨compute c f,(compute_cost c f _ hf).mono (by rw [co]; omega),?_⟩
    intro H ev _ M
    rw [compute_weight]
    apply (congrArg (qWeight ev (f H)) (move_general base c H (oracle (perm π H)) (public_run SparsePort.Lift.select π H SparsePort.Lift.add (fun _ _ => rfl)) M)).trans
    rw [he,qWeight_instr_bind]
    change _ = ∑ i : Fin 1, qWeight ev (k (oracle (perm π H))) ((portInstr (oracle (perm π H))).branch i M)
    rw [Fin.sum_univ_one]
  | query n k q _ ih =>
    choose f hf he using ih
    exact ⟨_,PUE.query n f _ hf,fun H ev _ M => by simp only [qWeight_unif_bind,he]⟩
  | eval p k q _ ih =>
    choose f hf he using ih
    exact ⟨_,(eval_cost π p _ f hf).mono (by omega),fun H ev _ M => he _ H ev M⟩

end
end Reduction.ShakePermutation.ItsrCircuit
#print axioms Reduction.ShakePermutation.ItsrCircuit.lift_machine
