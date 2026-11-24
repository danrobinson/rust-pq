import Integration.SlhDsaShakePermutationSparsePrefix
import Integration.SlhDsaShakePermutationSparseModel

namespace Reduction.ShakePermutation.SparsePort.Lift
open Fix Fix.Circuit Classical PQ.Interactive Quantum Matrix OracleSpec OracleComp
noncomputable section
variable {J Y Z E α : Type} [Fintype J] [DecidableEq J] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
  [DecidableEq Z] [Fintype E] [DecidableEq E]
variable (e : Words ≃ Y × Z) (a : J ↪ Words) (π : Permutation) (s : J → Z) (b : J)
local notation "U" => WS Port Words E
def select (u : U) : Port := u.1.1.1
def add (w : Words) : Equiv.Perm U :=
  (((Equiv.refl Port).prodCongr (Equiv.addRight w)).prodCongr (Equiv.refl E)).prodCongr (Equiv.refl Unit)
def access := circuit e a π s b (select (E := E)) add (fun _ _ => rfl)
local notation "H" => simulatedPort e a π s b
local notation "state" => Workspace.state (Y := Y) b

theorem move (F : J → Y) (M : Matrix U U ℂ) :
    transport ((access (E := E) e a π s b).run F) (state M) =
      state ((portInstr (H F)).branch 0 M) := by
  let z := ((Circuit.port (Z := E)).run (H F)).prodCongr (Equiv.refl Unit)
  have old : (portInstr (H F)).branch 0 M = MatrixMap.conj (basisMatrix z) M := by
    rw [port_branch,conj_basisMatrix_equiv]
    rfl
  rw [old]
  unfold Workspace.state
  rw [transport_embedding,← LinearMap.comp_apply,← MatrixMap.conj_mul,← basisMatrix_comp]
  apply congrArg (fun f => MatrixMap.conj (basisMatrix f) M)
  funext u
  unfold Workspace.embed
  rw [show (access (E := E) e a π s b).run F ((b,0),(0,u)) =
    ((b,0),(0,add (H F (select u)) u)) from circuit_run e a π s b select add _ F u]
  rfl

local notation "New" => WS J Y (Aux Y U)

theorem lift_machine {m : (Port → Words) → Closed U α} {q : ℕ}
    (hm : PUE (spec := unifSpec) cnt0 m q) :
    ∃ m' : (J → Y) → Closed New α, PUE (spec := unifSpec) cnt0 m' (12*q) ∧
    ∀ F ev [DecidablePred ev] (M : Matrix U U ℂ), qWeight ev (m' F) (state M) = qWeight ev (m (H F)) M := by
  induction hm with
  | pure x q =>
    exact ⟨_,PUE.pure x _,fun F ev _ M => by simp only [qWeight_pure,Workspace.state_trace]⟩
  | instr j k q _ ih =>
    choose f hf he using ih
    refine ⟨_,PUE.instr (Workspace.liftIdx (X := J) (Y := Y) (framedIdx j)) f _ hf,?_⟩
    intro F ev _ M
    rw [qWeight_instr_bind,qWeight_instr_bind]
    exact Finset.sum_congr rfl fun i _ => (congrArg _ (Workspace.lift_branch b (framedIdx j) i M)).trans (he i F ev _)
  | port k q _ ih =>
    obtain ⟨f,hf,he⟩ := ih
    let c := access (E := E) e a π s b
    have co : c.cost = 12 := circuit_cost ..
    refine ⟨compute c f,(compute_cost c f _ hf).mono (by rw [co]; omega),?_⟩
    intro F ev _ M
    rw [compute_weight,move,he,qWeight_instr_bind]
    change _ = ∑ i : Fin 1, qWeight ev (k (H F)) ((portInstr (H F)).branch i M)
    rw [Fin.sum_univ_one]
  | query n k q _ ih =>
    choose f hf he using ih
    refine ⟨_,PUE.query n f _ hf,?_⟩
    intro F ev _ M
    simp only [qWeight_unif_bind,he]
  | eval p k q _ ih =>
    choose f hf he using ih
    let sel := fun i : Fin 3 => (slot e a π s p i).getD b
    let get := fun u v w : Y => eval e a π s p ![u,v,w]
    have h3 (u v : Y) := PUE.eval (sel 2) (fun w => f (get u v w)) _ (fun w => hf _)
    have h2 (u : Y) := PUE.eval (sel 1) _ _ (h3 u)
    have h1 := PUE.eval (sel 0) _ _ h2
    refine ⟨_,h1.mono (by omega),?_⟩
    intro F ev _ M
    apply (he _ F ev M).trans
    have eq : ![F (sel 0),F (sel 1),F (sel 2)] = value e a π s F b p := by
      funext i; fin_cases i <;> rfl
    simp only [get,eq,simulatedPort]

end
end Reduction.ShakePermutation.SparsePort.Lift
#print axioms Reduction.ShakePermutation.SparsePort.Lift.lift_machine
