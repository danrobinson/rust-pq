import Kmixedperm.Funs
import Keccakasm.Registers
import Slhdsa.Proofs.Keccak
open Aeneas Aeneas.Std Result ControlFlow Spec.Keccak
namespace slhdsa.Kmixedperm
open KeccakRegisters KmixedpermRust
open KmixedpermRust.shake256.parallel
abbrev Row := mixed.V
abbrev Rows := Array Row 25#usize
instance : Inhabited Row := ⟨⟨fun _ => 0,0#u64⟩⟩
def atLane (x : Row) (j : Fin 3) : Lane :=
  if h : j.val<2 then x.pair ⟨j.val,h⟩ else x.scalar.bv
def lane (s : Rows) (j : Fin 3) : State :=
  _root_.Array.ofFn (n := 25) (fun i => atLane s.val[i.val]! j)
def view (m : Matrix 3#usize) (j : Fin 3) : State :=
  _root_.Array.ofFn (n := 25) fun i => m.val[i.val]!.val[j.val]!.bv

theorem pack (s : Matrix 3#usize) :
    core.array.from_fn 25#usize mixed.permute.closure.Insts.CoreOpsFunctionFnMutTupleUsizeV s
      ⦃ out => ∀ j, lane out j = view s j ⦄ := by
  apply WP.spec_mono (core.array.from_fn.spec_stateless_getElem! 25#usize _ _
    (fun i (v : Row) => ∀ j : Fin 3, atLane v j = s.val[i]!.val[j.val]!.bv) ?_)
  · intro out h j
    unfold lane view
    congr 1
    funext i
    simpa only [Array.getElem!_Nat_eq] using h i.val i.isLt j
  intro i hi
  unfold mixed.permute.closure.Insts.CoreOpsFunctionFnMutTupleUsizeV
  simp only [mixed.permute.closure.Insts.CoreOpsFunctionFnMutTupleUsizeV.call_mut,bind_tc_eq]
  step as ⟨row,hr⟩
  step as ⟨lo,hl⟩
  simp only [core.core_arch.arm_shared.neon.generated.vcreate_u64,bind_ok]
  step as ⟨hiWord,hh⟩
  simp only [core.core_arch.arm_shared.neon.generated.vcreate_u64,core.core_arch.arm_shared.neon.generated.vcombine_u64,bind_ok]
  step as ⟨scalar,hs⟩
  intro j
  fin_cases j <;> simp [atLane,hl,hh,hs,hr,Array.getElem!_Nat_eq,getElem!_pos,hi,
    getElem?_pos s.val i.val (by simpa using hi)]
end slhdsa.Kmixedperm
