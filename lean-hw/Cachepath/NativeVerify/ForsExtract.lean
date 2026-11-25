import Cachepath.NativeVerify.WotsOutput
import Cachepath.NativeVerify.ForsProgram
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.NativeVerify.Fors
open ShakeBatch
variable [machine : Machine]

theorem extract_range {N : Usize} (s : Matrix machine.width) (lane n : Usize)
    (start : Array U8 N) (count : n.val=N.val/8) (alignment : N.val%8=0)
    (window : N.val/8 ≤ 25) (valid : lane.val<machine.width.val) :
    recover_loop0_loop5_loop0 ⟨0#usize,n⟩ s lane start ⦃ out => ∀ b < N.val,
      out.val[b]! = stateByte s lane.val (b/8) (b%8) ⦄ := by
  have eq (j : Usize) : (0#usize+j : Result Usize) = ok j := by
    obtain ⟨v,hv,h⟩ := spec_imp_exists (@UScalar.add_spec _ (0#usize) j (by scalar_tac))
    exact hv.trans (congrArg ok (UScalar.eq_of_val_eq (by simpa using h)))
  have body (it : Range) (a : Array U8 N) :
      recover_loop0_loop5_loop0.body s lane it a = Wots.extract_lane_loop.body s 0#usize lane it a := by
    unfold recover_loop0_loop5_loop0.body Wots.extract_lane_loop.body
    simp only [eq,bind_ok]
    rfl
  have result := Wots.extract_range s 0#usize lane n start count alignment (by simpa) valid
  unfold recover_loop0_loop5_loop0
  simp_rw [body]
  unfold Wots.extract_lane_loop at result
  simpa only [Nat.zero_add, UScalar.ofNatCore_val_eq] using result

end slhdsa.NativeVerify.Fors
