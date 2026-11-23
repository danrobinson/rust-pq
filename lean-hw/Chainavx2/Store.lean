import Chainavx2.Digest
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.Avx2.Chain
open ChainAvx2Rust.sha256.x86.avx2

def writePrefix (b : Spec.Bytes) (N : Nat) (digest : DigestWords) (lane : Nat) : Nat → Spec.Bytes
  | 0 => b
  | k+1 => storeWord (writePrefix b N digest lane k) k (min 4 (N-4*k)) digest.val[k]!.val[lane]!

theorem write_prefix_spec (N limit lane : Usize) (batch : Batch) (digest : DigestWords)
    (hn : N.val ≤ 32) (hl : lane.val < 8) (budget : ∀ k < limit.val, 4*k < N.val) :
    chains_loop0_loop1_loop1_loop0 N ⟨0#usize,limit⟩ batch digest lane ⦃ r =>
      (∀ j, j ≠ lane.val → r.val[j]! = batch.val[j]!) ∧
      bytes r.val[lane.val]!.val = writePrefix (bytes batch.val[lane.val]!.val) N.val digest lane.val limit.val ⦄ := by
  unfold chains_loop0_loop1_loop1_loop0
  apply loop.spec_decr_nat (measure := fun p : core.ops.range.Range Usize × Batch => limit.val-p.1.start.val)
    (inv := fun p => p.1.end = limit ∧ p.1.start.val ≤ limit.val ∧
      (∀ j, j ≠ lane.val → p.2.val[j]! = batch.val[j]!) ∧ bytes p.2.val[lane.val]!.val =
        writePrefix (bytes batch.val[lane.val]!.val) N.val digest lane.val p.1.start.val)
  · rintro ⟨it,rows⟩ ⟨he,hi,old,atLane⟩
    simp only at he hi old atLane
    by_cases lt : it.start.val < it.end.val
    · have left : it.start.val < limit.val := he ▸ lt
      apply WP.spec_mono (word_store_spec N lane it rows digest hn hl lt (budget _ left))
      rintro _ ⟨next,r,rfl,hs,hend,other,written⟩
      simp only
      exact ⟨⟨hend.trans he,by omega,fun j hj => (other j hj).trans (old j hj),
        by rw [written,atLane,hs,writePrefix]⟩,by omega⟩
    · unfold chains_loop0_loop1_loop1_loop0.body
      step with core.iter.range.IteratorRange.next_Usize_none_spec it (by omega) as ⟨o,next,ho,_⟩
      simp only [ho,step_simps]
      have eq : it.start.val = limit.val := by rw [he] at lt; omega
      exact ⟨old,eq ▸ atLane⟩
  · simp [writePrefix]

theorem stores_spec (N : Usize) (batch : Batch) (lengths : Array U32 8#usize)
    (step : U32) (digest : DigestWords) (hn : N.val ≤ 32) :
    chains_loop0_loop1_loop1 N ⟨0#usize,8#usize⟩ batch lengths step digest ⦃ r =>
      ∀ j < 8, bytes r.val[j]!.val = if step.val < lengths.val[j]!.val then
        writePrefix (bytes batch.val[j]!.val) N.val digest j ((N.val+3)/4) else bytes batch.val[j]!.val ⦄ := by
  unfold chains_loop0_loop1_loop1
  apply loop.spec_decr_nat (measure := fun p : core.ops.range.Range Usize × Batch => 8-p.1.start.val)
    (inv := fun p => p.1.end.val = 8 ∧ p.1.start.val ≤ 8 ∧ ∀ j < 8, bytes p.2.val[j]!.val =
      if j < p.1.start.val ∧ step.val < lengths.val[j]!.val then
        writePrefix (bytes batch.val[j]!.val) N.val digest j ((N.val+3)/4) else bytes batch.val[j]!.val)
  · rintro ⟨it,rows⟩ ⟨he,hi,inv⟩
    simp only at he hi inv
    unfold chains_loop0_loop1_loop1.body
    by_cases lt : it.start.val < it.end.val
    · have h8 : it.start.val < 8 := by omega
      step with core.iter.range.IteratorRange.next_Usize_some_spec it lt as ⟨o,next,ho,hs,hend⟩
      simp only [ho]
      step as ⟨len,hl⟩
      have hl' : len = lengths.val[it.start.val]! := by rw [hl,getElem!_pos]
      by_cases live : step < len
      · simp only [if_pos live]
        step with core.num.Usize.div_ceil.spec_bounds N 4#usize (by decide) as ⟨words,lo,up⟩
        let limit := core.cmp.impls.OrdUsize.min words 8#usize
        have count : limit.val = (N.val+3)/4 := by
          change (if 8#usize < words then 8#usize else words).val = _
          change N.val ≤ words.val*4 at lo
          change words.val*4 < N.val+4 at up
          split <;> scalar_tac
        simp only [lift,bind_ok]
        step with write_prefix_spec N limit it.start rows digest hn h8 (fun k hk => by rw [count] at hk; omega) as ⟨r,other,here⟩
        refine ⟨by rw [hend,he],by omega,?_,by omega⟩
        intro j hj
        by_cases same : j = it.start.val
        · subst j
          have active : step.val < lengths.val[it.start.val]!.val := hl' ▸ live
          rw [here,inv _ h8,count]
          simp only [active,show it.start.val < next.start.val by omega,Nat.lt_irrefl,and_self,false_and,ite_true,ite_false]
        · rw [other _ same,inv j hj]
          have eq : j < next.start.val ↔ j < it.start.val := by omega
          simp only [eq]
      · simp only [if_neg live,step_simps]
        refine ⟨by rw [hend,he],by omega,?_,by omega⟩
        intro j hj
        rw [inv j hj]
        by_cases same : j = it.start.val
        · subst j
          have inactive : ¬ step.val < lengths.val[it.start.val]!.val := hl' ▸ live
          simp only [inactive,and_false,ite_false]
        · have eq : j < next.start.val ↔ j < it.start.val := by omega
          simp only [eq]
    · step with core.iter.range.IteratorRange.next_Usize_none_spec it (by omega) as ⟨o,next,ho,_⟩
      simp only [ho,step_simps]
      intro j hj
      simpa only [show j < it.start.val by omega,true_and] using inv j hj
  · simp
end slhdsa.Avx2.Chain
