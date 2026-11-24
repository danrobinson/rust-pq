import X86key.Leaf
import Slhdsa.Proofs.Slh
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.Key

theorem seed_spec {N : Usize} (hN : NOk N) (pk : Array U8 N) :
    X86KeyRust.hash.seed_ctx pk ⦃ r => r.pk_seed = pk ∧ SeedOk (seedOf r) ⦄ := by
  unfold X86KeyRust.hash.seed_ctx
  simp only [X86KeyRust.sha256.compress,X86KeyRust.sha512.compress,lift,bind_tc_eq,bind_ok,
    ← show TreeHashRust.sha256.compress = X86RemainderRust.sha256.compress from rfl,
    ← show TreeHashRust.sha512.compress = X86RemainderRust.sha512.compress from rfl,TreeHash.block256,TreeHash.block512,
    show X86KeyRust.sha256.H0=sha256.H0 by with_unfolding_all rfl,
    show X86KeyRust.sha512.H0=sha512.H0 by with_unfolding_all rfl]

  have hN32 := hN.le32
  have hpl : pk.val.length = N.val := by simp
  step*
  · refine ⟨?_, fun _ => ?_⟩
    · change wv state.val = _
      rw [state_post, Array.val_to_slice, s_post2, s2_post, Array.val_to_slice,
        H0_eq, Array.repeat_val, setSlice_rep _ _ _ (by simp; omega), hpl, List.drop_zero,
        List.take_of_length_le (by simp; omega)]
      simp [bytes_replicate,seedOf,Wots.Wide.coreSeed,X86KeyRust.wideSeed]
    · change S512.wv state5121.val = _
      rw [state5121_post, Array.val_to_slice, s4_post2, s6_post,
        Array.val_to_slice, S512.H0_eq, Array.repeat_val, setSlice_rep _ _ _ (by simp; omega), hpl,
        List.drop_zero, List.take_of_length_le (by simp; omega)]
      simp [bytes_replicate,seedOf,Wots.Wide.coreSeed,X86KeyRust.wideSeed]
  · refine ⟨?_, fun h => ?_⟩
    · change wv state.val = _
      rw [state_post, Array.val_to_slice, s_post2, s2_post, Array.val_to_slice,
        H0_eq, Array.repeat_val, setSlice_rep _ _ _ (by simp; omega), hpl, List.drop_zero,
        List.take_of_length_le (by simp; omega)]
      simp [bytes_replicate,seedOf,Wots.Wide.coreSeed,X86KeyRust.wideSeed]
    · exfalso; apply h; scalar_tac

end slhdsa.X86.Key
