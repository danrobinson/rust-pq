import Cachepath.WotsFusedPrf
import Cachepath.WotsFusedAbsorb
open Aeneas Aeneas.Std Result ControlFlow slhdsa.ShakeBatch
namespace slhdsa.cache.builder.nativeShake.Vector.Fused
set_option linter.concreteInstances false
variable [machine : Machine]

theorem ofProgramEq {α : Type} {f g : Result α} {P : α → Prop}
    (eq : f = g) (proof : g ⦃ x => P x ⦄) : f ⦃ x => P x ⦄ := eq ▸ proof

theorem all_chains {N : Usize} (p : params.Params) (hp : PN p N) (count offset last : Usize)
    (countEq : count.val=N.val/8) (off : offset.val=N.val/8+4) (bound : last.val<2^32)
    (seed sk : Array U8 N) (prfA hashA : Array address.Adrs machine.width)
    (pk prf input : Matrix machine.width) (pos : Usize) (rate : pos.val<17)
    (prfGood : PrfStable seed sk prfA prf) (hashGood : Stable seed hashA input)
    (permutes : PermutationCorrect) :
    generate_loop0 count ⟨0#usize,last⟩ offset pk pos prf input ⦃ out =>
      out.2.val < 17 ∧ ∀ j<machine.width.val, (ShakeBatch.lane out.1 j,8*out.2.val) =
        ((List.range last.val).flatMap (tip p sk seed prfA.val[j]! hashA.val[j]!)).foldl
          Spec.Keccak.feed (ShakeBatch.lane pk j,8*pos.val) ⦄ := by
  let prefixAt := fun n j => ((List.range n).flatMap (tip p sk seed prfA.val[j]! hashA.val[j]!)).foldl
    Spec.Keccak.feed (ShakeBatch.lane pk j,8*pos.val)
  unfold generate_loop0
  apply loop.spec_decr_nat (measure := fun q => last.val-q.1.start.val)
    (inv := fun q => q.1.end=last ∧ q.1.start.val ≤ last.val ∧
      PrfStable seed sk prfA q.2.2.2.1 ∧ Stable seed hashA q.2.2.2.2 ∧
      q.2.2.1.val < 17 ∧ ∀ j<machine.width.val, (ShakeBatch.lane q.2.1 j,8*q.2.2.1.val) = prefixAt q.1.start.val j)
  · rintro ⟨it,acc,whereAt,prf0,hash0⟩ ⟨stop,le,hprf,hhash,r,has⟩
    simp only at stop le hprf hhash r has
    unfold generate_loop0.body
    by_cases live : it.start.val < it.end.val
    · step with core.iter.range.IteratorRange.next_Usize_some_spec it live as ⟨who,next,tag,idx,ends⟩
      simp only [tag]
      let go : Result (ControlFlow (Range × Matrix machine.width × Usize × Matrix machine.width × Matrix machine.width) (Matrix machine.width × Usize)) := do
        let (prf1,hash1,hashed) ← inner count offset it.start prf0 hash0
        let (acc1,pos1) ← consume count hashed acc whereAt
        ok (cont (next,acc1,pos1,prf1,hash1))
      apply ofProgramEq (g := go)
      · dsimp only [go,inner,consume]
        simp only [uncurry,bind_tc_eq,Std.bind_assoc,bind_ok]
        repeat' congr 1
      dsimp only [go]
      step with inner_spec p hp count offset it.start countEq off (by rw [stop] at live;omega)
        sk seed prfA hashA prf0 hash0 hprf hhash permutes as ⟨prf1,hash1,hashed,hprf1,hhash1,htip⟩
      step with consume_spec p hp count countEq hashed acc whereAt r permutes _ htip as ⟨acc1,pos1,wide,out⟩
      rw [stop] at live
      refine ⟨ends.trans stop,by omega,hprf1,hhash1,wide,?_,by omega⟩
      intro j hj
      rw [out j hj,has j hj,idx]
      simp [prefixAt,List.range_succ,List.foldl_append]
    · obtain ⟨⟨_,_⟩,no,hn,_⟩ := spec_imp_exists (core.iter.range.IteratorRange.next_Usize_none_spec it (by omega))
      simp only [no,hn,step_simps]
      refine ⟨r,?_⟩
      intro j hj
      rw [stop] at live
      simpa [prefixAt,show it.start.val=last.val by omega] using has j hj
  · simp only [prefixAt,List.range_zero,List.flatMap_nil,List.foldl_nil]
    exact ⟨trivial,Nat.zero_le _,prfGood,hashGood,rate,fun _ _ => rfl⟩

end slhdsa.cache.builder.nativeShake.Vector.Fused
