import Xmssroot.Tree
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.XmssRoot
abbrev Levels := core.ops.range.RangeInclusive U32

theorem reduceTree {N} (p : params.Params) (hp : PN p N) (seed : XmssRootRust.hash.Seed N)
    (hs : SeedOk (TreeHash.seedOf (XmssRootRust.parentSeed seed))) (sk : Array U8 N)
    (a : XmssRootRust.address.Adrs) (idx : Nat) (height first : U32) (count : Usize)
    (roots : Nodes N) (positive : 0<height.val) (small : height.val≤4)
    (base : first.val=idx*2^height.val) (size : count.val=2^height.val)
    (prior : levelSpec p seed sk a idx height.val 0 roots) (limit : (idx+1)*2^height.val≤2^32) :
    XmssRootRust.xmss.wide.batch_root_loop0 ⟨1#u32,height,false⟩ seed a first count roots ⦃ out =>
      levelSpec p seed sk a idx height.val height.val out ⦄ := by
  unfold XmssRootRust.xmss.wide.batch_root_loop0
  apply loop.spec_decr_nat
    (measure := fun q : Levels × Nodes N => if q.1.exhausted then 0 else height.val+1-q.1.start.val)
    (inv := fun q => ∃ k, k≤height.val ∧ q.1.end=height ∧
      (if q.1.exhausted then k=height.val else q.1.start.val=k+1 ∧ k<height.val) ∧
      levelSpec p seed sk a idx height.val k q.2)
  · rintro ⟨it,current⟩ ⟨k,bound,last,status,previous⟩
    simp only at last status previous ⊢
    unfold XmssRootRust.xmss.wide.batch_root_loop0.body
    step as ⟨opt,next,iteration⟩
    by_cases stopped : it.exhausted=true
    · simp [stopped] at status iteration
      simp only [iteration.1,step_simps]
      exact status ▸ previous
    · have live : it.exhausted=false := by simpa using stopped
      simp only [live,Bool.false_eq_true,ite_false] at status
      obtain ⟨level,active⟩ := status
      have valid : ¬ it.end.val < it.start.val := by rw [last,level]; omega
      simp only [live,Bool.false_eq_true,false_or,if_neg valid] at iteration
      have item : opt=some it.start := by split at iteration <;> exact iteration.1
      simp only [item,XmssRootRust.address.Adrs.with_type,XmssRootRust.address.Adrs.with_word2,bind_ok]
      step as ⟨n,amount⟩
      · rcases System.Platform.numBits_eq with h|h <;> rw [h] <;> omega
      have nval : n.val=2^(height.val-(k+1)) := by
        rw [amount,size,level,Nat.shiftRight_eq_div_pow]
        rw (occs := .pos [1]) [show height.val=(height.val-(k+1))+(k+1) by omega]
        simp [Nat.pow_add]
      step with nextLevel p hp seed hs sk a idx height.val k first it.start n current small active base level nval previous limit as ⟨out,done⟩
      split at iteration
      · rename_i more
        obtain ⟨_,inc,finish,remains⟩ := iteration
        simp only [step_simps,remains,live,Bool.false_eq_true,ite_false]
        exact ⟨⟨k+1,by omega,finish.trans last,by omega,by rw [last] at more; omega,done⟩,by omega⟩
      · rename_i equal
        obtain ⟨_,_,finish,ends⟩ := iteration
        simp only [step_simps,ends,live,Bool.false_eq_true,ite_false,ite_true]
        exact ⟨⟨k+1,by omega,finish.trans last,by rw [last] at equal; omega,done⟩,by omega⟩
  · exact ⟨0,by omega,rfl,⟨by rfl,positive⟩,prior⟩
end slhdsa.X86.XmssRoot
