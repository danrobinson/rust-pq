import Chainavx2.Step
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.Avx2.Chain
open ChainAvx2Rust.sha256.x86.avx2

def AtStep (N off : Usize) (starts : Slice U32) (iv : EightRegs) (lengths : Array U32 8#usize)
    (before current : Batch) (t : Nat) := ∀ j : Fin 8,
  let first := starts.val[off.val+j.val]!.val
  bytes current.val[j.val]!.val = runBlock N.val (X86.stateWords (laneState iv j))
    (bytes before.val[j.val]!.val) first (first+min t lengths.val[j.val]!.val)

theorem batch_steps_spec (N off : Usize) (starts : Slice U32) (iv : EightRegs) (lengths : Array U32 8#usize)
    (stop : U32) (batch : Batch) (hn : N.val ≤ 32) (hs : off.val+8 ≤ starts.length)
    (safe : ∀ j < 8, starts.val[off.val+j]!.val + lengths.val[j]!.val ≤ U32.max) :
    chains_loop0_loop1 N ⟨0#u32,stop⟩ starts iv batch off lengths ⦃ r =>
      AtStep N off starts iv lengths batch r stop.val ⦄ := by
  unfold chains_loop0_loop1
  apply loop.spec_decr_nat (measure := fun p : core.ops.range.Range U32 × Batch => stop.val-p.1.start.val)
    (inv := fun p => p.1.end = stop ∧ p.1.start.val ≤ stop.val ∧ AtStep N off starts iv lengths batch p.2 p.1.start.val)
  · rintro ⟨it,rows⟩ ⟨he,hi,inv⟩
    simp only at he hi inv
    by_cases lt : it.start.val < it.end.val
    · apply WP.spec_mono (step_spec N off starts iv lengths it rows hn lt hs
        (fun j hj active => by have := safe j hj; omega))
      rintro _ ⟨next,r,rfl,hsucc,hend,bytesEq⟩
      simp only
      refine ⟨⟨hend.trans he,by rw [he] at lt; omega,fun j => ?_⟩,by rw [he] at lt; omega⟩
      dsimp only
      have old := inv j
      dsimp only at old
      rw [bytesEq j,hsucc]
      by_cases live : it.start.val < lengths.val[j.val]!.val
      · rw [if_pos live,Nat.min_eq_left (by omega),runBlock_succ,old,Nat.min_eq_left (by omega)]
      · rw [if_neg live,Nat.min_eq_right (by omega),old,Nat.min_eq_right (by omega)]
    · unfold chains_loop0_loop1.body
      step with core.iter.range.IteratorRange.next_U32_none_spec it (by omega) as ⟨o,next,ho,_⟩
      simp only [ho,step_simps]
      have eq : it.start.val = stop.val := by rw [he] at lt; omega
      exact eq ▸ inv
  · simp [AtStep,runBlock]
end slhdsa.Avx2.Chain
