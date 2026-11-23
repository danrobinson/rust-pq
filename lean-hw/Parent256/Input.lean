import Parent256.Funs
import Leaf256.Input
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.Parent
open TreeRust.sha256.x86.avx512

def addressOf (a : TreeRust.address.Adrs) : address.Adrs :=
  ⟨a.layer,a.tree,a.typ,a.keypair,a.word2,a.word3⟩

theorem pair_block (a : TreeRust.address.Adrs) (l r : Array U8 16#usize) :
    TreeRust.hash.pair_block a l r ⦃ b =>
      bytes b.val = padFrom 64 ((adrsS (addressOf a)).compress ++ (bytes l.val ++ bytes r.val)) ⦄ :=
  pair_block_spec (addressOf a) l r

theorem words_spec (N : Usize) (b : Array U8 64#usize) :
    core.array.from_fn 16#usize (fors_parents.closure.Insts.CoreOpsFunctionFnMutTupleUsize__m512i N) b
      ⦃ w => ∀ k, k < 16 → ∀ j : Fin 16, w.val[k]! j = Spec.SHA256.word (bytes b.val) (4*k) ⦄ :=
  Leaf.words_spec N b

theorem initial_spec (N : Usize) (st : Array U32 8#usize) :
    core.array.Array.map (fors_parents.closure_1.Insts.CoreOpsFunctionFnMutTupleU32__m512i N) st ()
      ⦃ a => ∀ i, i < 8 → ∀ j : Fin 16, a.val[i]! j = st.val[i]!.bv ⦄ :=
  Leaf.initial_spec N st

private theorem constants : ∀ i : Fin 64, (TreeRust.sha256.K.val[i.val]!).bv = Spec.SHA256.K[i.val]! := by
  unfold TreeRust.sha256.K Spec.SHA256.K
  decide

theorem first_four (iv : Array Reg 8#usize) (w : Array Reg 16#usize) (blocks : Fin 16 → Spec.Bytes)
    (hw : ∀ k, k < 16 → ∀ j, w.val[k]! j = Spec.SHA256.word (blocks j) (4*k)) :
    fors_parents_loop0 ⟨0#usize,4#usize⟩ w iv ⦃ s =>
      Trace s (fun j => Spec.SHA256.schedule (blocks j)) (laneState iv) 4 ⦄ := by
  unfold fors_parents_loop0
  apply loop.spec_decr_nat (measure := fun p : core.ops.range.Range Usize × Array Reg 8#usize => 4-p.1.start.val)
    (inv := fun p => p.1.end = 4#usize ∧ p.1.start.val ≤ 4 ∧
      Trace p.2 (fun j => Spec.SHA256.schedule (blocks j)) (laneState iv) p.1.start.val)
  · rintro ⟨it,s⟩ ⟨he,hi,ht⟩
    simp only at he hi ht
    unfold fors_parents_loop0.body
    by_cases hlt : it.start.val < it.end.val
    · have hsmall : it.start.val < 4 := by rw [he] at hlt; exact hlt
      step with core.iter.range.IteratorRange.next_Usize_some_spec it hlt as ⟨opt,nxt,hopt,hn,hen⟩
      simp only [hopt]
      step as ⟨v,hv⟩
      step as ⟨c,hc⟩
      have hconst := constants ⟨it.start.val,by omega⟩
      step with round_spec s v c (fun j => Spec.SHA256.schedule (blocks j)) it.start.val
        (by simpa only [hc,← getElem!_pos] using hconst)
        (fun j => by rw [hv, ← getElem!_pos, hw _ (by omega), slhdsa.schedule_lt16 _ _ (by omega)]) as ⟨s',hs⟩
      refine ⟨hen.trans he, by omega, fun j => ?_, by omega⟩
      rw [hs,ht,hn,List.range_succ,List.foldl_append]; rfl
    · step with core.iter.range.IteratorRange.next_Usize_none_spec it (by omega) as ⟨opt,nxt,hopt,hn⟩
      simp only [hopt,step_simps]
      have h : it.start.val = 4 := by rw [he] at hlt; change ¬it.start.val < 4 at hlt; omega
      exact h ▸ ht
  · simp [Trace]

end slhdsa.X86.Parent
