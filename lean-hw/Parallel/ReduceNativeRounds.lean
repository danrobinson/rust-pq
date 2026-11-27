import Parallel.ReduceNativeLevel
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.ParallelReduceNative
variable [family : Family]

def Layer {N} (node : Nat → Nat → Spec.Bytes) (root height k : Nat) (v : Rows N) :=
  v.length=2^(height-k) ∧ ∀ j<v.length, bytes v.val[j]!.val=node k (root*2^(height-k)+j)

theorem rounds {N} (seed : family.Seed N) (a : address.Adrs) (root height start : U32) (sub : Nat)
    (node : Nat → Nat → Spec.Bytes) (rows : Rows N)
    (hash : ∀ (h idx : U32) (l r : Array U8 N), 0<h.val →
      bytes l.val=node (h.val-1) (2*idx.val) → bytes r.val=node (h.val-1) (2*idx.val+1) →
      family.hash seed {a with word2:=h,word3:=idx} l r ⦃ out => bytes out.val=node h.val idx.val ⦄)
    (bound : (root.val+1)*2^(height.val-sub)≤2^32) (short : height.val-sub<32)
    (low : sub≤height.val) (next : start.val=sub+1) (ready : Layer node root.val height.val sub rows) :
    reduce_tree_loop0 ⟨start,height,false⟩ seed a root height rows ⦃ out => Layer node root.val height.val height.val out ⦄ := by
  unfold reduce_tree_loop0
  apply loop.spec_decr_nat
    (measure := fun q : core.ops.range.RangeInclusive U32 × Rows N => if q.1.exhausted then 0 else height.val+1-q.1.start.val)
    (inv := fun q => ∃ k, sub≤k ∧ k≤height.val ∧ q.1.end=height ∧
      (if q.1.exhausted then k=height.val else q.1.start.val=k+1) ∧ Layer node root.val height.val k q.2)
  · rintro ⟨it,current⟩ ⟨k,above,le,last,status,previous⟩
    simp only at last status previous ⊢
    unfold reduce_tree_loop0.body
    step as ⟨opt,nextIt,iteration⟩
    by_cases stopped : it.exhausted=true
    · simp [stopped] at status iteration
      simp only [iteration.1,step_simps]
      exact status ▸ previous
    · have live : it.exhausted=false := by simpa using stopped
      simp only [live,Bool.false_eq_true,ite_false] at status
      by_cases empty : it.end.val < it.start.val
      · simp [live,empty] at iteration
        simp only [iteration.1,step_simps]
        have eq : k=height.val := by rw [last] at empty;omega
        exact eq ▸ previous
      · simp only [live,Bool.false_eq_true,false_or,if_neg empty] at iteration
        have item : opt=some it.start := by split at iteration <;> exact iteration.1
        simp only [item]
        have active : k<height.val := by rw [last] at empty;omega
        let width := 2^(height.val-(k+1))
        have twice : 2^(height.val-k)=2*width := by
          rw [show height.val-k=(height.val-(k+1))+1 by omega,Nat.pow_succ,Nat.mul_comm]
        have exp : height.val-(k+1)≤height.val-sub := by omega
        have lim : (root.val+1)*width≤2^32 :=
          le_trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) exp)) bound
        have initial := previous.1
        have before := previous.2
        rw [twice] at initial before
        step as ⟨shift,diff⟩
        step with U32.ShiftLeft_spec root shift (by omega) as ⟨first,offset,_⟩
        have base : first.val=root.val*width := by
          rw [offset,Nat.shiftLeft_eq,U32.size_eq,diff,status]
          apply Nat.mod_eq_of_lt
          have pos : 0<width := Nat.two_pow_pos _
          change root.val*width<4294967296
          rw [Nat.add_one_mul] at lim;omega
        step as ⟨n,amount⟩
        have size : n.val=width := by
          rw [amount,alloc.vec.Vec.len_val,initial];omega
        have room : first.val+n.val≤2^32 := by rw [base,size,←Nat.add_one_mul];exact lim
        let parent := fun j => node (k+1) (root.val*width+j)
        have corr (i : Nat) (hi : i<n.val) (idx : U32) (index : idx.val=first.val+i) :
            family.hash seed {a with word2:=it.start,word3:=idx} current.val[2*i]! current.val[2*i+1]!
              ⦃ out => bytes out.val=parent i ⦄ := by
          have li := before (2*i) (by omega)
          have ri := before (2*i+1) (by omega)
          rw [base] at index
          have left : 2*idx.val=root.val*(2*width)+2*i := by rw [index];ring
          have right : 2*idx.val+1=root.val*(2*width)+(2*i+1) := by omega
          apply WP.spec_mono (hash it.start idx _ _ (by omega) (by simpa [status,left] using li) (by simpa [status,right] using ri))
          intro out value;simpa [parent,status,index] using value
        step with level_spec seed a it.start first current n (by omega) room parent corr as ⟨parents,plen,values⟩
        unfold truncate
        simp only [bind_ok]
        have result : Layer node root.val height.val (k+1) (alloc.vec.Vec.from (parents.val.take n.val) (by simp)) := by
          constructor
          · simp only [alloc.vec.Vec.length,alloc.vec.Vec.from_val]
            rw [List.length_take]; change min n.val parents.length=width;omega
          · intro j hj
            simp only [alloc.vec.Vec.length,alloc.vec.Vec.from_val] at hj
            have valid : j<n.val := lt_of_lt_of_le hj (List.length_take_le ..)
            simp only [alloc.vec.Vec.from_val]
            rw [List.getElem!_take_of_lt _ _ _ valid];exact values _ valid
        split at iteration
        · rename_i more
          obtain ⟨_,inc,finish,remains⟩ := iteration
          simp only [step_simps,remains,live,Bool.false_eq_true,ite_false]
          exact ⟨⟨k+1,by omega,by omega,finish.trans last,by omega,result⟩,by omega⟩
        · rename_i equal
          obtain ⟨_,_,finish,ends⟩ := iteration
          simp only [step_simps,ends,live,Bool.false_eq_true,ite_false,ite_true]
          exact ⟨⟨k+1,by omega,by omega,finish.trans last,by rw [last] at equal;omega,result⟩,by omega⟩
  · exact ⟨sub,by omega,low,rfl,next,ready⟩
end slhdsa.ParallelReduceNative
