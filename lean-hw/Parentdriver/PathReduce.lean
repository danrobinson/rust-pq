import Parentdriver.Path
open Aeneas Aeneas.Std Result
namespace slhdsa.PlatformParent.Driver

def pathParent {N : Usize} (p : Spec.Params) (pk : Spec.Bytes) (a : address.Adrs) (v : Nodes N)
    (idx : Slice U32) (sig : Slice U8) (h off i : Nat) :=
  Spec.H p pk (pathAddress a idx.val[i]!) (pathData v idx sig h off i)

def Paths {N : Usize} (p : Spec.Params) (pk : Spec.Bytes) (a : address.Adrs) (v : Nodes N)
    (idx : Slice U32) (sig : Slice U8) (h off t : Nat) (buf : Nodes N) (cur : Slice U32) :=
  IndexRange idx cur 0 t ∧ buf.length = v.length ∧ ∀ i, i < v.length →
    if i < t then nodeBytes buf i = pathParent p pk a v idx sig h off i else buf.val[i]! = v.val[i]!

private theorem index_append (original current result : Slice U32) (j g : Nat)
    (before : IndexRange original current 0 j) (update : IndexRange current result j g) :
    IndexRange original result 0 (j+g) := by
  obtain ⟨hc,hb⟩ := before
  obtain ⟨hr,hu⟩ := update
  refine ⟨hr.trans hc,fun i hi => ?_⟩
  rw [hu _ (by omega),hb _ hi]
  simp only [Nat.zero_le,true_and,Nat.zero_add]
  split_ifs <;> first | rfl | omega

private abbrev PathIter := core.iter.adapters.step_by.StepBy (core.ops.range.Range Usize)

theorem path_batches_spec {G N : Usize} (K : Kernel G) (p : Spec.Params) (pk : Spec.Bytes)
    (a : address.Adrs) (s : Array U64 8#usize) (v : Nodes N) (idx : Slice U32) (sig : Slice U8)
    (h off last : Usize) (shape : N.val = 24 ∨ N.val = 32) (good : Correct (N := N) K p pk s)
    (hg : 0 < G.val) (multiple : last.val%G.val = 0) (hv : last.val ≤ v.length) (hi : v.length ≤ idx.length)
    (hh : h.val+1 ≤ Usize.max) (bounds : SigBounds N.val h.val off.val v.length sig) :
    pathBatches K ⟨⟨0#usize,last⟩,G⟩ s a v idx sig h off ⦃ r ix =>
      Paths p pk a v idx sig h.val off.val last.val r ix ⦄ := by
  unfold pathBatches
  apply loop.spec_decr_nat (measure := fun q : PathIter × Nodes N × Slice U32 => last.val-q.1.iter.start.val)
    (inv := fun q => q.1.iter.end = last ∧ q.1.step_by = G ∧ q.1.iter.start.val ≤ last.val ∧
      q.1.iter.start.val%G.val = 0 ∧ Paths p pk a v idx sig h.val off.val q.1.iter.start.val q.2.1 q.2.2)
  · rintro ⟨it,buf,cur⟩ ⟨he,hs,hbound,hm,⟨hc,hidx⟩,hlen,hrows⟩
    simp only at he hs hbound hm hc hidx hlen hrows
    unfold pathBatchStep
    by_cases hlt : it.iter.start.val < it.iter.end.val
    · have hlt' : it.iter.start.val < last.val := he ▸ hlt
      have finish : it.iter.start.val + G.val ≤ last.val := by
        obtain ⟨u,hu⟩ := Nat.dvd_of_mod_eq_zero hm
        obtain ⟨w,hw⟩ := Nat.dvd_of_mod_eq_zero multiple
        have lt : u < w := Nat.lt_of_mul_lt_mul_left (hu ▸ hw ▸ hlt')
        rw [hu,hw,← Nat.mul_succ]
        exact Nat.mul_le_mul_left _ lt
      step with core.iter.adapters.step_by.IteratorStepBy.next_Range_Usize_some_spec it hlt
        (hs ▸ hg) (by rw [he,hs]; exact finish) as ⟨opt,nxt,hopt,hn,hen,hstride⟩
      simp only [hopt]
      step with path_blocks_spec (G := G) a buf cur sig h off it.iter.start shape (by omega) (by omega) hh
        (hlen.symm ▸ bounds) as ⟨ix,blocks,hix,hblocks⟩
      step as ⟨stop,hstop⟩
      step as ⟨dst,back,hdst,hdlen,hback⟩
      let addr := fun k => pathAddress a cur.val[it.iter.start.val+k]!
      let data := fun k => pathData buf cur sig h.val off.val (it.iter.start.val+k)
      have dlen (k) (hk : k < G.val) : (data k).length = 2*N.val := by
        have bnd := bounds (it.iter.start.val+k) (by omega)
        have length : (sibling sig N.val h.val off.val (it.iter.start.val+k)).length = N.val := by
          simp [sibling,bytes,List.slice,Slice.length] at *; omega
        unfold data pathData
        split <;> simp [nodeBytes,length] <;> omega
      step with good blocks dst addr data (by omega) dlen hblocks as ⟨result,hl,hash⟩
      have advance : nxt.iter.start.val = it.iter.start.val+G.val := by rw [hn,hs]
      refine ⟨hen.trans he,hstride.trans hs,by omega,by rw [advance,Nat.add_mod]; simp [hm],
        ⟨?_,?_,?_⟩,by omega⟩
      · rw [advance]
        exact index_append idx cur ix it.iter.start.val G.val ⟨hc,hidx⟩ hix
      · simp only [Slice.length,hback,Slice.setSlice!_val,List.length_setSlice!]; exact hlen
      · intro k hk
        by_cases old : k < it.iter.start.val
        · simp only [if_pos (show k < nxt.iter.start.val by omega),nodeBytes,hback,Slice.setSlice!_val,
            List.getElem!_setSlice!_prefix _ _ _ _ old]
          simpa only [if_pos old,nodeBytes] using hrows k hk
        · by_cases active : k < nxt.iter.start.val
          · simp only [if_pos active,nodeBytes,hback,Slice.setSlice!_val]
            rw [List.getElem!_setSlice!_middle _ _ _ _ (by
              change it.iter.start.val ≤ k ∧ k-it.iter.start.val < result.length ∧ k < buf.length; omega)]
            rw [hash _ (by omega)]
            have isame := hidx k (by omega)
            simp only [Nat.zero_le,true_and,Nat.zero_add,if_neg old] at isame
            have same := hrows k hk
            simp only [if_neg old] at same
            simp only [addr,data,show it.iter.start.val+(k-it.iter.start.val) = k by omega,
              pathParent,pathData,nodeBytes,isame,same]
          · simp only [if_neg active,hback,Slice.setSlice!_val]
            rw [List.getElem!_setSlice!_suffix _ _ _ _ (by change it.iter.start.val+result.length ≤ k; omega)]
            simpa only [if_neg old] using hrows k hk
    · step with core.iter.adapters.step_by.IteratorStepBy.next_Range_Usize_none_spec it (by omega) as ⟨opt,nxt,hopt,hend⟩
      simp only [hopt,step_simps]
      have eq : it.iter.start.val = last.val := by rw [he] at hlt; omega
      exact ⟨⟨hc,eq ▸ hidx⟩,hlen,eq ▸ hrows⟩
  · simp [Paths,IndexRange]

end slhdsa.PlatformParent.Driver
