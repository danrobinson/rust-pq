import Wotswide.Funs
import X86remainder.Proof
import Slhdsa.Proofs.Hash
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.Wots.Wide
theorem digest256 (buf : Array U8 640#usize) (total : Usize) (S0 : List Spec.SHA256.Word)
    (st : Array U32 8#usize) (off : Usize) (ht : total.val % 64 = 0) (htle : total.val ≤ 640)
    (hoff : off.val % 64 = 0) (hle : off.val ≤ total.val)
    (hinv : wv st.val = (List.range (off.val / 64)).foldl
      (fun st k => Spec.SHA256.compress st (Spec.SHA256.blockAt (bytes buf.val) k)) S0) :
    WotsWideRust.hash.thash_values_loop1 buf total st off ⦃ r =>
      wv r.val = hashFrom S0 ((bytes buf.val).take total.val) ⦄ := by
  unfold WotsWideRust.hash.thash_values_loop1
  apply loop.spec_decr_nat
    (measure := fun (q : Array U32 8#usize × Usize) => total.val - q.2.val)
    (inv := fun q => q.2.val % 64 = 0 ∧ q.2.val ≤ total.val ∧
      wv q.1.val = (List.range (q.2.val / 64)).foldl
        (fun st k => Spec.SHA256.compress st (Spec.SHA256.blockAt (bytes buf.val) k)) S0)
  · rintro ⟨st, off⟩ ⟨hoff, hle, hinv⟩
    simp only [WotsWideRust.hash.thash_values_loop1.body]
    simp only at hoff hle hinv
    split
    · rename_i hlt
      have h64 : off.val + 64 ≤ total.val := by scalar_tac
      step as ⟨s,s_post⟩
      step with Stream.single256 st s off (by simp [s_post]; omega) as ⟨st1,st1_post⟩
      step as ⟨off1,off1_post⟩
      refine ⟨by scalar_tac, by scalar_tac, ?_, by scalar_tac⟩
      have e : off1.val / 64 = off.val / 64 + 1 := by scalar_tac
      have e2 : 64 * (off.val / 64) = off.val := by omega
      rw [e, List.range_succ, List.foldl_append, ← hinv, st1_post, s_post]
      simp [Spec.SHA256.blockAt, e2]
    · rename_i hge
      have : off.val = total.val := by scalar_tac
      simp only [step_simps]
      rw [this] at hinv
      rw [hinv, hashFrom_take _ _ _ ht (by simp; omega)]
  · exact ⟨hoff, hle, hinv⟩

theorem digest512 (buf : Array U8 2304#usize) (total : Usize) (S0 : List Spec.SHA512.Word)
    (st : Array U64 8#usize) (off : Usize) (ht : total.val % 128 = 0) (htle : total.val ≤ 2304)
    (hoff : off.val % 128 = 0) (hle : off.val ≤ total.val)
    (hinv : S512.wv st.val = (List.range (off.val / 128)).foldl
      (fun st k => Spec.SHA512.compress st (Spec.SHA512.blockAt (bytes buf.val) k)) S0) :
    WotsWideRust.hash.thash_values_loop3 buf total st off ⦃ r =>
      S512.wv r.val = S512.hashFrom S0 ((bytes buf.val).take total.val) ⦄ := by
  unfold WotsWideRust.hash.thash_values_loop3
  apply loop.spec_decr_nat
    (measure := fun (q : Array U64 8#usize × Usize) => total.val - q.2.val)
    (inv := fun q => q.2.val % 128 = 0 ∧ q.2.val ≤ total.val ∧
      S512.wv q.1.val = (List.range (q.2.val / 128)).foldl
        (fun st k => Spec.SHA512.compress st (Spec.SHA512.blockAt (bytes buf.val) k)) S0)
  · rintro ⟨st, off⟩ ⟨hoff, hle, hinv⟩
    simp only [WotsWideRust.hash.thash_values_loop3.body]
    simp only at hoff hle hinv
    split
    · rename_i hlt
      have h128 : off.val + 128 ≤ total.val := by scalar_tac
      step as ⟨s,s_post⟩
      step with Stream.single512 st s off (by simp [s_post]; omega) as ⟨st1,st1_post⟩
      step as ⟨off1,off1_post⟩
      refine ⟨by scalar_tac, by scalar_tac, ?_, by scalar_tac⟩
      have e : off1.val / 128 = off.val / 128 + 1 := by scalar_tac
      have e2 : 128 * (off.val / 128) = off.val := by omega
      rw [e, List.range_succ, List.foldl_append, ← hinv, st1_post, s_post]
      simp [Spec.SHA512.blockAt, e2]
    · rename_i hge
      have : off.val = total.val := by scalar_tac
      simp only [step_simps]
      rw [this] at hinv
      rw [hinv, hashFrom512_take _ _ _ ht (by simp; omega)]
  · exact ⟨hoff, hle, hinv⟩

end slhdsa.X86.Wots.Wide
