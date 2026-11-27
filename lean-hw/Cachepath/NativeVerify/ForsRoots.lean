import Cachepath.NativeVerify.ForsClimb
import Cachepath.NativeVerify.ForsDigest
import Cachepath.NativeVerify.ForsIndices
import Cachepath.NativeVerify.ForsLeafHash

open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.NativeVerify.Fors
open ShakeBatch
set_option linter.concreteInstances false
set_option maxHeartbeats 1800000
variable [machine : Machine] [accelerator : ActiveKernel machine] [stream : Stream] [ok : StreamCorrect]

private abbrev Steps := core.iter.adapters.step_by.StepBy (core.ops.range.Range Usize)

theorem all_roots {N : Usize} (p : params.Params) (hp : PN p N) (sig : Slice U8)
    (len : sig.length=p.k.val*(1+p.a.val)*N.val) (seed : Array U8 N) (a : address.Adrs)
    (permutes : ActiveCorrect machine accelerator.run) (enabled : 0<machine.width.val)
    (choices : Slice U32) (count : choices.length=p.k.val)
    (index : ∀ j < choices.length, choices.val[j]!.val < 2^p.a.val)
    (n offset short pair stride : Usize) (str : stride.val=p.a.val+1) (nv : n.val=N.val/8)
    (off : offset.val=n.val+4) (sh : short.val=offset.val+n.val) (pa : pair.val=offset.val+2*n.val)
    (sw aw : Array U64 4#usize) (seeds : ∀ k<n.val, sw.val[k]!.bv=inputWord seed.val k)
    (addr : ∀ k<4, aw.val[k]!.bv=addressWord a k)
    (state : stream.State) (matrix : Matrix machine.width) (base : Spec.Bytes) (prior : ok.Absorbed state base)
    (it : Steps) (width : it.step_by=machine.width) (init : it.iter=⟨0#usize,choices.len⟩) :
    recover_loop0 N it p.a choices sig n offset short pair stride sw aw state matrix ⦃ out =>
      ok.Absorbed out (base ++ (List.range p.k.val).flatMap (forsRoot (Shake.params p) (bytes sig.val)
        (bytes seed.val) (adrsS a) (nats choices.val))) ⦄ := by
  let root := forsRoot (Shake.params p) (bytes sig.val) (bytes seed.val) (adrsS a) (nats choices.val)
  have small := hp.le32
  have aligned := aligned_hash hp
  have positive : 0<N.val := by rcases hp.nok with h|h|h <;> omega
  have hk : choices.length ≤ 35 := count.symm ▸ hp.valid.k_le
  unfold recover_loop0
  apply loop.spec_decr_nat (measure := fun q : Steps × stream.State × Matrix machine.width => choices.length-q.1.iter.start.val)
    (inv := fun q => q.1.iter.end.val=choices.length ∧ q.1.step_by=machine.width ∧
      q.1.iter.start.val≤choices.length ∧ ok.Absorbed q.2.1 (base ++ (List.range q.1.iter.start.val).flatMap root))
  · rintro ⟨iter,pk,st⟩ ⟨he,hs,hi,old⟩
    dsimp only at he hs hi old ⊢
    rw [split_batch]
    step with core.iter.adapters.step_by.IteratorStepBy.next_Range_Usize_spec iter (by rw [hs];exact enabled)
      as ⟨o,next,splitNext,endEq,widthEq⟩
    by_cases more : iter.iter.start.val < iter.iter.end.val
    · simp only [ite_eq_left more] at splitNext
      obtain ⟨tag,advance⟩ := splitNext
      simp only [tag]
      step as ⟨rem,rv⟩
      simp only [lift,bind_ok]
      let active := core.cmp.impls.OrdUsize.min rem machine.width
      have av : active.val=min (choices.length-iter.iter.start.val) machine.width.val := by
        simp [active,core.cmp.impls.OrdUsize.min_val,rv]
      have fits : iter.iter.start.val+active.val≤choices.length := by omega
      have live : active.val≤machine.width.val := by omega
      have same : next.iter.start.val=iter.iter.start.val+active.val := by rw [advance,hs,he,av];omega
      have capacity : (iter.iter.start.val+active.val)*stride.val*N.val≤sig.length := by
        rw [len,show 1+p.a.val=stride.val by omega]
        exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (fits.trans_eq count))
      step with indices_spec p hp choices iter.iter.start active _ hk fits live index as ⟨ix,selected⟩
      step with leaf_fips seed a sig n offset short stride sw aw iter.iter.start active ix st (by omega) off sh
        (by omega) live (by omega) capacity positive seeds addr permutes as ⟨leaves,leaf⟩
      have level : Level p sig seed a (nats choices.val) iter.iter.start active 0 ix leaves := by
        intro l hl
        have present : iter.iter.start.val+l < choices.length := by omega
        have sel := selected l hl
        have natAt := fors_nats_getElem! choices.val (iter.iter.start.val+l) present
        rw [← getElem!_pos] at natAt
        have indexEq : ix.val[l]!.val=(iter.iter.start.val+l)*2^p.a.val+(nats choices.val)[iter.iter.start.val+l]! := by rw [sel,natAt]
        refine ⟨?_,indexEq,?_⟩
        · simp only [forsClimbAt,List.range_zero,List.foldl_nil,forsLeaf]
          rw [leaf l hl]
          simp only [Spec.F,Shake.params,paramsS_n,paramsS_a,hp.n_eq,Spec.block,bytes_take,bytes_drop,str,
            adrsS,indexEq,List.append_assoc]
          rfl
        · simpa only [Shake.params,paramsS_a,Nat.sub_zero,Nat.pow_zero,Nat.div_one] using indexEq
      step with all_levels p hp seed a sig (nats choices.val) n offset pair stride iter.iter.start active sw aw leaves ix
        nv off pa live str capacity seeds addr permutes level as ⟨roots,value⟩
      step with append_batch roots n active pk _ old nv aligned small live as ⟨out,has⟩
      have rootsEq : (List.range active.val).flatMap (fun l => Spec.Keccak.squeeze (ShakeBatch.lane roots l) 0 N.val) =
          (List.range active.val).flatMap (fun l => root (iter.iter.start.val+l)) := by
        rw [List.flatMap_def,List.flatMap_def]
        apply congrArg List.flatten
        apply List.map_congr_left
        intro l hl
        exact value l (List.mem_range.mp hl)
      rw [rootsEq,List.append_assoc] at has
      have joined : (List.range (iter.iter.start.val+active.val)).flatMap root =
          (List.range iter.iter.start.val).flatMap root ++ (List.range active.val).flatMap (fun l => root (iter.iter.start.val+l)) := by
        rw [List.range_add,List.flatMap_append,List.flatMap_map]
      refine ⟨by rw [endEq,he],widthEq.trans hs,by omega,?_,by omega⟩
      simpa only [same,joined] using has
    · simp only [ite_eq_right more] at splitNext
      simp only [splitNext.1,step_simps]
      have eq : iter.iter.start.val=p.k.val := by omega
      simpa only [eq] using old
  · simp [init,width,prior]

end slhdsa.NativeVerify.Fors
