import Wots.Batch
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.Wots
open Spec.SHA256

def laneBlock (w : Words) (j : Fin 16) := Leaf.blockOf (chainWords w j)

theorem prepare_spec (w : Words) (two iv : Hash)
    (ht : Trace two (fun j => schedule (laneBlock w j)) (laneState iv) 2) :
    prepare w two ⦃ pre x c d => Trace pre (fun j => schedule (laneBlock w j)) (laneState iv) 4 ∧
      x = w.val[2]! ∧ c.bv = K[2]! ∧ d.bv = K[3]! ⦄ := by
  unfold prepare
  step as ⟨x,hx⟩
  step as ⟨c,hc⟩
  have cOK : c.bv = K[2]! := by rw [hc]; unfold WotsRust.sha256.K K; decide
  step with Leaf.trace_round two x c (laneBlock w) (laneState iv) 2 (by decide) cOK
    (fun j => by rw [laneBlock,Leaf.word_blockOf _ _ (by decide),hx,← getElem!_pos]; rfl) ht as ⟨a,ha⟩
  step as ⟨y,hy⟩
  step as ⟨d,hd⟩
  have dOK : d.bv = K[3]! := by rw [hd]; unfold WotsRust.sha256.K K; decide
  step with Leaf.trace_round a y d (laneBlock w) (laneState iv) 3 (by decide) dOK
    (fun j => by rw [laneBlock,Leaf.word_blockOf _ _ (by decide),hy,← getElem!_pos]; rfl) ha as ⟨pre,hpre⟩
  exact ⟨hpre,by rw [hx,← getElem!_pos],cOK,dOK⟩

theorem switch_spec (w : Words) (two iv : Hash) (change : Reg) (c d : U32)
    (ht : Trace two (fun j => schedule (laneBlock w j)) (laneState iv) 2)
    (hc : c.bv = K[2]!) (hd : d.bv = K[3]!) :
    switchPrefix w two w.val[2]! change c d ⦃ v pre =>
      (∀ k < 16, ∀ j : Fin 16, v.val[k]! j = Leaf.withType (chainWords w j) (change j) k) ∧
      Trace pre (fun j => schedule (laneBlock v j)) (laneState iv) 4 ⦄ := by
  unfold switchPrefix
  simp only [WotsRust.core.core_arch.x86.avx512f._mm512_xor_si512,
    LeafRust.core.core_arch.x86.avx512f._mm512_xor_si512,bind_ok]
  step as ⟨v,hv⟩
  have value (k : Nat) (_ : k < 16) (j : Fin 16) :
      v.val[k]! j = Leaf.withType (chainWords w j) (change j) k := by
    rw [hv,Array.set_val_eq,show (2#usize).val = 2 by rfl]
    by_cases h : k=2
    · subst k; rw [Avx2.setSame _ _ _ (by simp)]; rfl
    · rw [Avx2.setOther _ _ _ _ (Ne.symm h)]; simp [Leaf.withType,h,chainWords]
  have ht' : Trace two (fun j => schedule (laneBlock v j)) (laneState iv) 2 := by
    apply Leaf.transfer_prefix (by decide) _ ht
    intro j k hk
    simp only [laneBlock,Leaf.word_blockOf _ _ (by omega : k<16)]
    unfold chainWords
    rw [value _ (by omega),Leaf.withType,if_neg (by omega)]
    rfl
  step as ⟨x,hx⟩
  step with Leaf.trace_round two x c (laneBlock v) (laneState iv) 2 (by decide) hc
    (fun j => by rw [laneBlock,Leaf.word_blockOf _ _ (by decide),hx,← getElem!_pos]; rfl) ht' as ⟨a,ha⟩
  step as ⟨y,hy⟩
  step with Leaf.trace_round a y d (laneBlock v) (laneState iv) 3 (by decide) hd
    (fun j => by rw [laneBlock,Leaf.word_blockOf _ _ (by decide),hy,← getElem!_pos]; rfl) ha as ⟨pre,hpre⟩
  exact ⟨value,hpre⟩

end slhdsa.X86.Wots
