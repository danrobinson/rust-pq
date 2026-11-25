import Armwide.Xmss.ParentsProgram

open Aeneas Aeneas.Std Result
namespace slhdsa.ArmXmss
abbrev Nodes (N : Usize) := Array (Array U8 N) 16#usize

def parent {N} (p : params.Params) (seed : hash.Seed N) (a : address.Adrs)
    (first : U32) (roots : Nodes N) (j : Nat) :=
  Spec.H (paramsS p) (bytes seed.pk_seed.val) {(adrsS a) with word3 := first.val+j}
    (bytes roots.val[2*j]!.val ++ bytes roots.val[2*j+1]!.val)

/-- The real scalar remainder after the paired SHA-512 parent kernel. The
already-written prefix and every remaining child refer to the pre-pass roots. -/
theorem remainder {N} (p : params.Params) (hp : PN p N) (seed : hash.Seed N)
    (hs : SeedOk seed) (a : address.Adrs) (first : U32) (roots current : Nodes N)
    (done n : Usize) (doneBound : done.val≤n.val) (size : n.val≤8)
    (room : first.val+n.val≤2^32)
    (earlier : ∀ j<done.val, bytes current.val[j]!.val=parent p seed a first roots j)
    (later : ∀ j, 2*done.val≤j → j<16 → current.val[j]! = roots.val[j]!) :
    xmss.arm.batch_root_512_loop0_loop0 ⟨done,n⟩ seed.pk_seed seed.state seed.state512
      current a first ⦃ out => ∀ j<n.val, bytes out.val[j]!.val=parent p seed a first roots j ⦄ := by
  unfold xmss.arm.batch_root_512_loop0_loop0
  apply loop.spec_decr_nat (measure := fun q : core.ops.range.Range Usize × Nodes N => n.val-q.1.start.val)
    (inv := fun q => q.1.end=n ∧ q.1.start.val≤n.val ∧
      (∀ j<q.1.start.val, bytes q.2.val[j]!.val=parent p seed a first roots j) ∧
      (∀ j, 2*q.1.start.val≤j → j<16 → q.2.val[j]! = roots.val[j]!))
  · rintro ⟨it,current⟩ ⟨he,bound,earlier,later⟩
    simp only at he bound earlier later
    unfold xmss.arm.batch_root_512_loop0_loop0.body
    by_cases more : it.start.val<n.val
    · step with core.iter.range.IteratorRange.next_Usize_some_spec it (by rwa [he]) as ⟨opt,next,item,inc,last⟩
      simp only [item]
      simp only [lift,bind_ok]
      have castVal : (UScalar.cast .U32 it.start).val=it.start.val := by scalar_tac
      step as ⟨idx,indexVal⟩
      simp only [slhdsa.address.Adrs.with_word3,bind_ok]
      step as ⟨leftIdx,leftVal⟩
      step as ⟨left,readLeft⟩
      step as ⟨rightIdx,rightVal⟩
      step as ⟨right,readRight⟩
      step with slhdsa.hash2_spec p hp _ hs as ⟨node,nodeVal⟩
      step as ⟨out,write⟩
      refine ⟨last.trans he,by omega,?_,?_,by omega⟩
      · intro j hj
        rw [write,Array.set_val_eq]
        by_cases eq : it.start.val=j
        · subst j
          simp (disch := scalar_tac) [getElem!_pos] at readLeft readRight ⊢
          have l := later (2*it.start.val) (by omega) (by omega)
          have r := later (2*it.start.val+1) (by omega) (by omega)
          simp (disch := scalar_tac) [getElem!_pos] at l r
          rw [nodeVal]
          unfold parent
          congr 1
          · change {adrsS a with word3 := idx.val} = _
            rw [indexVal,castVal]
          · have leftEq : left = roots.val[2*it.start.val]! := by
              simpa (disch := scalar_tac) only [getElem!_pos,leftVal,l] using readLeft
            have rightEq : right = roots.val[2*it.start.val+1]! := by
              simpa (disch := scalar_tac) only [getElem!_pos,rightVal,leftVal,r] using readRight
            rw [leftEq,rightEq]
        · simpa (disch := scalar_tac) [getElem!_pos,List.getElem_set,eq] using earlier j (by omega)
      · intro j hj endPos
        rw [write,Array.set_val_eq]
        have ne : it.start.val≠j := by omega
        simpa (disch := scalar_tac) [getElem!_pos,List.getElem_set,ne] using later j (by omega) endPos
    · step with core.iter.range.IteratorRange.next_Usize_none_spec it (by rw [he]; omega) as ⟨opt,next,item,_⟩
      simp only [item,step_simps]
      exact fun j hj => earlier j (by omega)
  · exact ⟨rfl,doneBound,earlier,later⟩
end slhdsa.ArmXmss
