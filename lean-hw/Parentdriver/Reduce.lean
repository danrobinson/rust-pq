import Parentdriver.Tree
import Parentdriver.Kernel
open Aeneas Aeneas.Std Result
namespace slhdsa.PlatformParent.Driver

def parentAt {N : Usize} (p : Spec.Params) (pk : Spec.Bytes) (a : address.Adrs) (first : U32)
    (v : Nodes N) (k : Nat) := Spec.H p pk (treeAddress a (first.val+k)) (children v k)

/-- Earlier output rows may overlap children already read. Unconsumed children retain their original bytes. -/
def Reduced {N : Usize} (p : Spec.Params) (pk : Spec.Bytes) (a : address.Adrs) (first : U32)
    (orig v : Nodes N) (done : Nat) := v.length = orig.length ∧ ∀ k, k < orig.length →
      if k < done then nodeBytes v k = parentAt p pk a first orig k else v.val[k]! = orig.val[k]!

private abbrev Iter := core.iter.adapters.step_by.StepBy (core.ops.range.Range Usize)

theorem tree_batches_spec {G N : Usize} (K : Kernel G) (p : Spec.Params) (pk : Spec.Bytes)
    (a : address.Adrs) (s : Array U64 8#usize) (first : U32) (v : Nodes N) (last : Usize)
    (shape : N.val = 24 ∨ N.val = 32) (good : Correct (N := N) K p pk s) (hg : 0 < G.val)
    (multiple : last.val % G.val = 0) (hv : 2*last.val ≤ v.length) (hi : first.val+last.val ≤ 2^32) :
    treeBatches K ⟨⟨0#usize,last⟩,G⟩ s a first v ⦃ r => Reduced p pk a first v r last.val ⦄ := by
  unfold treeBatches
  apply loop.spec_decr_nat (measure := fun q : Iter × Nodes N => last.val-q.1.iter.start.val)
    (inv := fun q => q.1.iter.end = last ∧ q.1.step_by = G ∧ q.1.iter.start.val ≤ last.val ∧
      q.1.iter.start.val%G.val = 0 ∧ Reduced p pk a first v q.2 q.1.iter.start.val)
  · rintro ⟨it,buf⟩ ⟨he,hs,hb,hm,hlen,hr⟩
    simp only at he hs hb hm hlen hr
    unfold treeBatchStep
    by_cases hlt : it.iter.start.val < it.iter.end.val
    · have hlt' : it.iter.start.val < last.val := he ▸ hlt
      have finish : it.iter.start.val + G.val ≤ last.val := by
        obtain ⟨u,hu⟩ := Nat.dvd_of_mod_eq_zero hm
        obtain ⟨w,hw⟩ := Nat.dvd_of_mod_eq_zero multiple
        have h : u < w := Nat.lt_of_mul_lt_mul_left (hu ▸ hw ▸ hlt')
        rw [hu,hw,← Nat.mul_succ]
        exact Nat.mul_le_mul_left _ h
      step with core.iter.adapters.step_by.IteratorStepBy.next_Range_Usize_some_spec it hlt
        (hs ▸ hg) (by rw [he,hs]; exact finish) as ⟨opt,nxt,hopt,hn,hen,hstride⟩
      simp only [hopt]
      step with tree_blocks_spec (G := G) a first buf it.iter.start shape (by omega) (by omega) as ⟨blocks,hblocks⟩
      step as ⟨stop,hstop⟩
      step as ⟨dst,back,hdst,hdlen,hback⟩
      let addr := fun k => treeAddress a (first.val+it.iter.start.val+k)
      let data := fun k => children buf (it.iter.start.val+k)
      have data_len (k) : (data k).length = 2*N.val := by simp [data,children,nodeBytes]; omega
      step with good blocks dst addr data (by omega) (fun k _ => data_len k) hblocks as ⟨result,hl,hash⟩
      have advance : nxt.iter.start.val = it.iter.start.val + G.val := by rw [hn,hs]
      refine ⟨hen.trans he,hstride.trans hs,by omega,by rw [advance,Nat.add_mod]; simp [hm],⟨?_,?_⟩,by omega⟩
      · simp only [Slice.length,hback,Slice.setSlice!_val,List.length_setSlice!]; exact hlen
      · intro k hk
        by_cases early : k < it.iter.start.val
        · simp only [if_pos (show k < nxt.iter.start.val by omega),nodeBytes,hback,Slice.setSlice!_val,List.getElem!_setSlice!_prefix _ _ _ _ early]
          have old := hr k hk
          simpa only [if_pos early,nodeBytes] using old
        · by_cases active : k < nxt.iter.start.val
          · simp only [if_pos active,nodeBytes,hback,Slice.setSlice!_val]
            rw [List.getElem!_setSlice!_middle _ _ _ _ (by change it.iter.start.val ≤ k ∧ k-it.iter.start.val < result.length ∧ k < buf.length; omega)]
            rw [hash _ (by omega)]
            simp only [addr,data,parentAt,children,nodeBytes]
            have idx : it.iter.start.val + (k-it.iter.start.val) = k := by omega
            have add : first.val+it.iter.start.val+(k-it.iter.start.val) = first.val+k := by omega
            rw [idx,add]
            have lc := hr (2*k) (by omega)
            have rc := hr (2*k+1) (by omega)
            rw [if_neg (show ¬2*k < it.iter.start.val by omega)] at lc
            rw [if_neg (show ¬2*k+1 < it.iter.start.val by omega)] at rc
            rw [lc,rc]
          · simp only [if_neg active,hback,Slice.setSlice!_val]
            rw [List.getElem!_setSlice!_suffix _ _ _ _ (by change it.iter.start.val+result.length ≤ k; omega)]
            simpa only [if_neg early] using hr k hk
    · step with core.iter.adapters.step_by.IteratorStepBy.next_Range_Usize_none_spec it (by omega) as ⟨opt,nxt,hopt,hend⟩
      simp only [hopt,step_simps]
      have endeq : it.iter.start.val = last.val := by rw [he] at hlt; omega
      exact ⟨hlen,endeq ▸ hr⟩
  · simp [Reduced]

end slhdsa.PlatformParent.Driver
