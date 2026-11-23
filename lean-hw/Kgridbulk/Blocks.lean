import Kgridbulk.Rate
import Kapplebulk.Blocks
open Aeneas Aeneas.Std Result ControlFlow Spec.Keccak
namespace slhdsa.Kgridbulk
open KgridbulkRust KgridbulkRust.shake256.stream_x86

def flatState (grid : Kdiag.Grid) : State :=
  _root_.Array.ofFn (n := 25) fun i => grid.val[i.val/5]! ⟨i.val%5,by omega⟩

private theorem readBlock (a : Kdiag.Grid) (b : Slice U8) (size : b.length=136) :
    injectBlock a b ⦃ out => flatState out = ratePrefix (flatState a) b.val 17 ⦄ := by
  apply WP.spec_mono (injectBlock_spec a b size)
  intro out eq
  apply ext25 _ _ (by simp [flatState]) (by simp [ratePrefix])
  intro k hk
  simpa (disch := omega) only [flatState,ratePrefix,ofFnAt] using eq ⟨k,hk⟩

theorem blocks (it : core.slice.iter.ChunksExact U8) (a : Kdiag.Grid)
    (size : ∀ c ∈ it.chunks, c.length=136)
    (perm : ∀ g : Kdiag.Grid, absorb_loop0_loop1 ⟨⟨0#usize,24#usize⟩,2#usize⟩ g
      ⦃ out => flatState out = permute (flatState g) ⦄) :
    absorb_loop0 it a ⦃ out => (flatState out,0) =
      (Kapplebulk.inputBytes it.chunks).foldl feed (flatState a,0) ⦄ := by
  unfold absorb_loop0
  apply loop.spec_decr_nat
    (measure := fun (p : core.slice.iter.ChunksExact U8 × Kdiag.Grid) => p.1.chunks.length)
    (inv := fun p => (∀ c ∈ p.1.chunks, c.length=136) ∧
      (Kapplebulk.inputBytes p.1.chunks).foldl feed (flatState p.2,0) =
        (Kapplebulk.inputBytes it.chunks).foldl feed (flatState a,0))
  · rintro ⟨cur,state⟩ ⟨lens,same⟩
    simp only at lens same ⊢
    unfold absorb_loop0.body core.slice.iter.IteratorChunksExact.next
    cases h : cur.chunks with
    | nil => simpa [h,Kapplebulk.inputBytes,step_simps] using same
    | cons c tail =>
      have sz := lens c (by simp [h])
      obtain ⟨injected,op,cells⟩ := spec_imp_exists (readBlock state c sz)
      obtain ⟨after,rounds,permuted⟩ := spec_imp_exists (perm injected)
      simp only [bind_ok]
      have advance := feed_block (flatState state) c.val (by simp [flatState]) sz
      rw [← cells,← permuted] at advance
      have grouped {α : Type} (k : Kdiag.Grid → Result α) :
          (do let g ← injectBlock state c; k g) = k injected := by rw [op,bind_ok]
      simp only [injectBlock,lastRow,Std.bind_assoc] at grouped
      apply Eq.mpr (congrArg (fun m => WP.spec m _) (grouped (fun g => do
        let it ← core.iter.traits.iterator.Iterator.step_by.trait_default
          (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize) ⟨0#usize,24#usize⟩ 2#usize
        let v ← absorb_loop0_loop1 it g
        ok (cont ((⟨tail,cur.remainder⟩ : core.slice.iter.ChunksExact U8),v)))))
      simp only [core.iter.traits.iterator.Iterator.step_by.trait_default,
        core.iter.traits.iterator.Iterator.step_by.default,show (2#usize).val ≠ 0 by decide,
        ite_false,bind_ok,rounds,step_simps]
      refine ⟨fun x hx => lens x (by simp [h,hx]),?_,by simp [h]⟩
      simp only [h,Kapplebulk.inputBytes,List.flatMap_cons,List.foldl_append] at same
      simpa only [Kapplebulk.inputBytes,advance] using same
  · exact ⟨size,rfl⟩
end slhdsa.Kgridbulk
