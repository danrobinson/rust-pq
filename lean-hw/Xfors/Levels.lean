import Xfors.Tree
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.Fors
abbrev Levels := core.ops.range.RangeInclusive U32

theorem reduceTree {N} (p : params.Params) (hp : PN p N) (seed : XForsRust.hash.Seed N)
    (hs : SeedOk (TreeHash.seedOf (XForsRust.scalarSeed seed))) (sk : Array U8 N)
    (a : XForsRust.address.Adrs) (idx height : U32) (count : Usize)
    (roots : Nodes N) (positive : 0<height.val) (small : height.val≤7)
    (size : count.val=2^height.val)
    (prior : levelSpec p seed sk a idx.val height.val 0 roots) (limit : (idx.val+1)*2^height.val≤2^32)
    (cpu : GatherRust.avx512Available=true) :
    XForsRust.fors.wide.subtree_loop0 ⟨1#u32,height,false⟩ idx height seed.pk_seed seed.state seed.state512 a count roots ⦃ out =>
      levelSpec p seed sk a idx.val height.val height.val out ⦄ := by
  unfold XForsRust.fors.wide.subtree_loop0
  apply loop.spec_decr_nat
    (measure := fun q : Levels × Nodes N => if q.1.exhausted then 0 else height.val+1-q.1.start.val)
    (inv := fun q => ∃ k, k≤height.val ∧ q.1.end=height ∧
      (if q.1.exhausted then k=height.val else q.1.start.val=k+1 ∧ k<height.val) ∧
      levelSpec p seed sk a idx.val height.val k q.2)
  · rintro ⟨it,current⟩ ⟨k,bound,last,status,previous⟩
    simp only at last status previous ⊢
    unfold XForsRust.fors.wide.subtree_loop0.body
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
      simp only [item]
      step as ⟨shift,diff⟩
      step as ⟨first,offset⟩
      have short : shift.val<32 := by omega
      have base : first.val=idx.val*2^(height.val-(k+1)) := by
        rw [offset,Nat.shiftLeft_eq,U32.size_eq,diff,level]
        apply Nat.mod_eq_of_lt
        have positive := Nat.two_pow_pos height.val
        have room : idx.val*2^height.val<2^32 := by rw [Nat.add_one_mul] at limit; omega
        exact lt_of_le_of_lt (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _))) room
      simp only [XForsRust.address.Adrs.with_word2,bind_ok]
      step as ⟨n,amount⟩
      · rcases System.Platform.numBits_eq with h|h <;> rw [h] <;> omega
      have nval : n.val=2^(height.val-(k+1)) := by
        rw [amount,size,level,Nat.shiftRight_eq_div_pow]
        rw (occs := .pos [1]) [show height.val=(height.val-(k+1))+(k+1) by omega]
        simp [Nat.pow_add]
      have nsmall : n.val≤64 := by rw [nval]; exact Nat.pow_le_pow_right (by decide : 0<2) (show height.val-(k+1)≤6 by omega)
      have room : first.val+n.val≤2^32 := by
        rw [base,nval,← Nat.add_one_mul]
        exact le_trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _))) limit
      let adr := {a with word2:=it.start}
      change (do let (arr,start) ← vectorParents seed adr first current n
                 let out ← XForsRust.fors.wide.subtree_loop0_loop0 ⟨start,n⟩ seed.pk_seed seed.state seed.state512 arr first adr
                 ok (ControlFlow.cont (next,out))) ⦃ r => _ ⦄
      step with vector_spec p hp seed hs adr first current n nsmall room cpu as ⟨arr,start,nb,written,intact⟩
      step with nextLevel p hp seed hs sk a idx.val height.val k first it.start n start current arr small active base level nval previous limit nb written intact as ⟨out,done⟩
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
end slhdsa.X86.Fors
