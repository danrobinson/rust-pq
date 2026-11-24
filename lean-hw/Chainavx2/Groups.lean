import Chainavx2.Batch
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.Avx2.Chain
open ChainAvx2Rust.sha256.x86.avx2

abbrev Groups := Slice Batch

theorem finished_spec (N off : Usize) (starts ends : Slice U32) (iv : EightRegs) (lengths : Array U32 8#usize)
    (stop : U32) (batch : Batch) (hn : N.val ≤ 32) (hs : off.val+8 ≤ starts.length)
    (ranges : ∀ j < 8, lengths.val[j]!.val = ends.val[off.val+j]!.val-starts.val[off.val+j]!.val)
    (longest : ∀ j : Fin 8, lengths.val[j.val]!.val ≤ stop.val) :
    chains_loop0_loop1 N ⟨0#u32,stop⟩ starts iv batch off lengths ⦃ r =>
      ∀ j : Fin 8, bytes r.val[j.val]!.val = runBlock N.val (X86.stateWords (laneState iv j))
        (bytes batch.val[j.val]!.val) starts.val[off.val+j.val]!.val ends.val[off.val+j.val]!.val ⦄ := by
  apply WP.spec_mono (batch_steps_spec N off starts iv lengths stop batch hn hs ?_)
  · intro r h j
    have eq := h j
    dsimp only at eq
    rw [eq,Nat.min_eq_right (longest j),ranges j.val j.isLt]
    unfold runBlock
    rw [show starts.val[off.val+j.val]!.val + (ends.val[off.val+j.val]!.val - starts.val[off.val+j.val]!.val) -
        starts.val[off.val+j.val]!.val = ends.val[off.val+j.val]!.val - starts.val[off.val+j.val]!.val by omega]
  · intro j hj
    rw [ranges j hj]
    have a := starts.val[off.val+j]!.hmax
    have b := ends.val[off.val+j]!.hmax
    change _ < 4294967296 at a b
    rw [U32.max_eq]
    omega

def GroupPrefix (N : Usize) (iv : EightRegs) (starts ends : Slice U32) (before after : Groups) (count : Nat) :=
  after.length = before.length ∧ ∀ g < before.length, ∀ j : Fin 8, bytes after.val[g]!.val[j.val]!.val =
    if g < count then runBlock N.val (X86.stateWords (laneState iv j)) (bytes before.val[g]!.val[j.val]!.val)
      starts.val[8*g+j.val]!.val ends.val[8*g+j.val]!.val else bytes before.val[g]!.val[j.val]!.val

theorem groups_spec (N : Usize) (iv : EightRegs) (starts ends : Slice U32) (groups : Groups)
    (hn : N.val ≤ 32) (hs : 8*groups.length ≤ starts.length) (he : 8*groups.length ≤ ends.length) :
    chains_loop0 N ⟨0#usize,groups.len⟩ starts ends iv groups ⦃ r =>
      GroupPrefix N iv starts ends groups r groups.length ⦄ := by
  unfold chains_loop0
  apply loop.spec_decr_nat (measure := fun p : core.ops.range.Range Usize × Groups => groups.length-p.1.start.val)
    (inv := fun p => p.1.end.val = groups.length ∧ p.1.start.val ≤ groups.length ∧
      GroupPrefix N iv starts ends groups p.2 p.1.start.val)
  · rintro ⟨it,buf⟩ ⟨hend,hi,len,old⟩
    simp only at hend hi len old
    unfold chains_loop0.body
    by_cases lt : it.start.val < it.end.val
    · have small : it.start.val < groups.length := by omega
      have hbuf : it.start.val < buf.length := by omega
      step with core.iter.range.IteratorRange.next_Usize_some_spec it lt as ⟨o,next,ho,hnext,heq⟩
      simp only [ho]
      step as ⟨batch,back,hbatch,hback⟩
      have bound := starts.property
      step as ⟨off,hoff⟩
      have offEq : off.val = 8*it.start.val := by omega
      step with range_lengths_spec N off starts ends (by omega) (by omega) as ⟨lens,ranges⟩
      step with longest_spec lens as ⟨stop,maximum⟩
      step with finished_spec N off starts ends iv lens stop batch hn (by omega) ranges
        ((maximum stop.val).mp (by omega)) as ⟨r,done⟩
      simp only [step_simps,hback,GroupPrefix,Slice.set_val_eq]
      refine ⟨by rw [heq,hend],by omega,by simpa using len,?_,by omega⟩
      intro g hg j
      by_cases same : g = it.start.val
      · subst g
        rw [Avx2.setSame _ _ _ hbuf,if_pos (by omega)]
        have prev := old it.start.val small j
        rw [if_neg (Nat.lt_irrefl _)] at prev
        rw [done j,hbatch,← getElem!_pos,prev,offEq]
      · rw [Avx2.setOther _ _ _ _ (Ne.symm same),old g hg]
        have eq : g < next.start.val ↔ g < it.start.val := by omega
        simp only [eq]
    · step with core.iter.range.IteratorRange.next_Usize_none_spec it (by omega) as ⟨o,next,ho,_⟩
      simp only [ho,step_simps]
      have eq : it.start.val = groups.length := by omega
      exact ⟨len,eq ▸ old⟩
  · simp [GroupPrefix]
end slhdsa.Avx2.Chain
