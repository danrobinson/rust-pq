import Xmssroot.Funs
import Treehash.Proof
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.XmssRoot
set_option maxRecDepth 8192
open XmssRootRust (parentSeed parentAddr)
abbrev Nodes (N : Usize) := Array (Array U8 N) 16#usize
def addressOf (a : XmssRootRust.address.Adrs) := adrsS (TreeHash.addr (parentAddr a))
def parent {N} (p : params.Params) (seed : XmssRootRust.hash.Seed N) (a : XmssRootRust.address.Adrs)
    (first level : U32) (roots : Nodes N) (j : Nat) :=
  Spec.H (paramsS p) (bytes seed.pk_seed.val) {(addressOf a) with word3 := (first.val >>> level.val)+j}
    (bytes roots.val[2*j]!.val ++ bytes roots.val[2*j+1]!.val)

theorem reduceLevel {N} (p : params.Params) (hp : PN p N) (seed : XmssRootRust.hash.Seed N)
    (hs : SeedOk (TreeHash.seedOf (parentSeed seed))) (a : XmssRootRust.address.Adrs)
    (first level : U32) (roots : Nodes N) (n : Usize) (size : n.val≤8)
    (shift : level.val<32) (room : (first.val >>> level.val)+n.val≤2^32) :
    XmssRootRust.xmss.wide.batch_root_loop0_loop0 ⟨0#usize,n⟩ seed first roots level a ⦃ out =>
      ∀ j<n.val, bytes out.val[j]!.val=parent p seed a first level roots j ⦄ := by
  unfold XmssRootRust.xmss.wide.batch_root_loop0_loop0
  apply loop.spec_decr_nat (measure := fun q : core.ops.range.Range Usize × Nodes N => n.val-q.1.start.val)
    (inv := fun q => q.1.end=n ∧ q.1.start.val≤n.val ∧
      (∀ j<q.1.start.val, bytes q.2.val[j]!.val=parent p seed a first level roots j) ∧
      (∀ j, q.1.start.val≤j → j<16 → q.2.val[j]! = roots.val[j]!))
  · rintro ⟨it,current⟩ ⟨he,bound,earlier,later⟩
    simp only at he bound earlier later
    unfold XmssRootRust.xmss.wide.batch_root_loop0_loop0.body
    by_cases more : it.start.val<n.val
    · step with core.iter.range.IteratorRange.next_Usize_some_spec it (by rwa [he]) as ⟨opt,next,item,inc,last⟩
      simp only [item]
      step as ⟨base,baseVal⟩
      simp only [lift,bind_tc_eq,bind_ok]
      have castVal : (UScalar.cast .U32 it.start).val=it.start.val := by scalar_tac
      step as ⟨idx,indexVal⟩
      simp only [XmssRootRust.address.Adrs.with_word3,bind_ok]
      step as ⟨leftIdx,leftVal⟩
      step as ⟨left,readLeft⟩
      step as ⟨rightIdx,rightVal⟩
      step as ⟨right,readRight⟩
      unfold XmssRootRust.xmss.hash2
      step with TreeHash.hash2_fips p hp _ hs as ⟨node,nodeVal⟩
      step as ⟨out,write⟩
      refine ⟨last.trans he,by omega,?_,?_,by omega⟩
      · intro j hj
        rw [write,Array.set_val_eq]
        by_cases eq : it.start.val=j
        · subst j
          simp (disch := scalar_tac) [getElem!_pos,List.getElem_set] at readLeft readRight ⊢
          have l := later (2*it.start.val) (by omega) (by omega)
          have r := later (2*it.start.val+1) (by omega) (by omega)
          simp (disch := scalar_tac) [getElem!_pos] at l r
          rw [nodeVal]
          unfold parent
          congr 1
          · change {addressOf a with word3 := idx.val} = _
            rw [indexVal,baseVal,castVal]
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
  · exact ⟨rfl,by simp,by simp,fun _ _ _ => rfl⟩
end slhdsa.X86.XmssRoot
