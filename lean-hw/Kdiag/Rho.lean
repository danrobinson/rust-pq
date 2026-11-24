import Kdiag.Permute
open Aeneas Aeneas.Std Result
namespace slhdsa.Kdiag
open KdiagRust.shake256.stream_x86
def rotation (diag : Bool) (i j : Nat) : Nat :=
  if j < 5 then ROT.val[if diag then (j+i)%5 else i]!.val[j]!.val else 0

theorem rotate_spec (diag : Bool) (i : Usize) (hi : i.val<5) (x d : Reg) :
    rho diag i x d ⦃ v => ∀ j, v j = ((x j) ^^^ (d j)).rotateLeft (rotation diag i.val j.val % 64) ⦄ := by
  unfold rho
  have build := core.array.from_fn.spec_stateless_getElem! 8#usize
    (rho.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64 diag i) ()
    (fun n (w : U64) => w.val=rotation diag i.val n) (by
      intro n hn
      unfold rho.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64
      simp only [rho.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut]
      by_cases active : n.val<5
      · have yes : n<5#usize := active
        cases diag
        · simp only [yes,Bool.false_eq_true,ite_true,ite_false,bind_tc_eq,bind_ok]
          step as ⟨row,hr⟩
          step as ⟨w,hw⟩
          simp [rotation,active,hw,hr,getElem!_pos,hi]
        · simp only [yes,ite_true,bind_tc_eq,bind_ok]
          step as ⟨off,ho⟩
          all_goals try scalar_tac
          step as ⟨idx,hidx⟩
          step as ⟨row,hr⟩
          step as ⟨w,hw⟩
          simp [rotation,active,hw,hr,getElem!_pos,hidx,ho,Nat.mod_lt _ (by decide : 0<5)]
      · have no : ¬ n<5#usize := active
        simp [no,rotation,active])
  apply WP.spec_bind build
  intro a h
  simp only [KdiagRust.core.intrinsics.transmute,KdiagRust.core.core_arch.x86.avx512f._mm512_xor_si512,
    KavxRust.core.core_arch.x86.avx512f._mm512_xor_si512,KdiagRust.core.core_arch.x86.avx512f._mm512_rolv_epi64,
    bind_ok,step_simps]
  intro j
  have e := h j.val j.isLt
  simp only [Array.getElem!_Nat_eq] at e
  exact congrArg (fun n => ((x j) ^^^ (d j)).rotateLeft (n%64)) e
end slhdsa.Kdiag
