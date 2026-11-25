import Armwide.ForsTree.Program

open Aeneas Aeneas.Std Result
namespace slhdsa.ArmForsTree
open ArmXmss

def level {N} (p : params.Params) (seed : hash.Seed N) (sk : Array U8 N)
    (a : address.Adrs) (idx height k : Nat) (nodes : Nodes N 128#usize) :=
  ∀ j<2^(height-k), bytes nodes.val[j]!.val=Spec.forsNode (paramsS p) (bytes sk.val)
    (idx*2^(height-k)+j) k (bytes seed.pk_seed.val) (adrsS a)

private theorem advance {N} (p : params.Params) (seed : hash.Seed N) (sk : Array U8 N)
    (a : address.Adrs) (idx h k : Nat) (first step : U32) (nodes out : Nodes N 128#usize)
    (active : k<h) (pos : first.val=idx*2^(h-(k+1))) (next : step.val=k+1)
    (previous : level p seed sk a idx h k nodes)
    (parents : ∀ j<2^(h-(k+1)), bytes out.val[j]!.val=parent p seed {a with word2:=step} first nodes j) :
    level p seed sk a idx h (k+1) out := by
  intro j hj
  rw [parents j hj]
  have spread : 2^(h-k)=2*2^(h-(k+1)) := by
    rw [show h-k=(h-(k+1))+1 by omega,Nat.pow_succ,Nat.mul_comm]
  have l : 2*j<2^(h-k) := by omega
  have r : 2*j+1<2^(h-k) := by omega
  simp only [parent,previous _ l,previous _ r,Spec.forsNode,pos,next]
  have lidx : idx*2^(h-k)+2*j=2*(idx*2^(h-(k+1))+j) := by rw [spread];ring
  have ridx : idx*2^(h-k)+(2*j+1)=2*(idx*2^(h-(k+1))+j)+1 := by omega
  rw [lidx,ridx]
  simp [adrsS,pos,next]

theorem reduceSmall  (p : params.Params) (hp : PN p 16#usize) (seed : hash.Seed 16#usize)
    (hs : SeedOk seed) (sk : Array U8 16#usize) (a : address.Adrs)
    (idx height : U32) (n : Usize) (roots : Nodes 16#usize 128#usize)
    (small : height.val≤7) (size : n.val=2^height.val)
    (prior : level p seed sk a idx.val height.val 0 roots) (limit : (idx.val+1)*2^height.val≤2^32) :
    fors.arm.subtree_loop0 ⟨1#u32,height,false⟩ idx height seed.state a n roots ⦃ out =>
      level p seed sk a idx.val height.val height.val out ⦄ := by
  unfold fors.arm.subtree_loop0
  apply loop.spec_decr_nat
    (measure := fun q : Levels × Nodes 16#usize 128#usize => if q.1.exhausted then 0 else height.val+1-q.1.start.val)
    (inv := fun q => ∃ k, k≤height.val ∧ q.1.end=height ∧
      (if q.1.exhausted then k=height.val else q.1.start.val=k+1) ∧
      level p seed sk a idx.val height.val k q.2)
  · rintro ⟨it,current⟩ ⟨k,bound,last,status,previous⟩
    simp only at last status previous ⊢
    unfold fors.arm.subtree_loop0.body
    step as ⟨opt,next,iteration⟩
    by_cases stopped : it.exhausted=true
    · simp [stopped] at status iteration
      simp only [iteration.1,step_simps]
      exact status ▸ previous
    · have live : it.exhausted=false := by simpa using stopped
      simp only [live,Bool.false_eq_true,ite_false] at status
      by_cases finished : it.end.val < it.start.val
      · simp [live,finished] at iteration
        simp only [iteration.1,step_simps]
        have eq : k=height.val := by rw [last,status] at finished;omega
        exact eq ▸ previous
      · have active : k<height.val := by rw [last,status] at finished;omega
        simp only [live,Bool.false_eq_true,false_or,ite_eq_right finished] at iteration
        have item : opt=some it.start := by split at iteration <;> exact iteration.1
        simp only [item]
        step as ⟨diff,diffVal⟩
        step as ⟨first,firstVal⟩
        have power : 2^(height.val-(k+1))≤2^height.val :=
          Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)
        have pos : first.val=idx.val*2^(height.val-(k+1)) := by
          rw [firstVal,Nat.shiftLeft_eq,diffVal,status,U32.size_eq,Nat.mod_eq_of_lt]
          have := Nat.mul_le_mul_left (idx.val+1) power
          rw [Nat.add_one_mul] at this
          have := Nat.two_pow_pos (height.val-(k+1));omega
        simp only [address.Adrs.with_word2,bind_ok,lift,Array.to_slice_mut]
        step as ⟨count,countVal⟩
        · rcases System.Platform.numBits_eq with b|b <;> rw [b] <;> omega
        have val : count.val=2^(height.val-(k+1)) := by
          rw [countVal,size,status,Nat.shiftRight_eq_div_pow]
          rw (occs := .pos [1]) [show height.val=(height.val-(k+1))+(k+1) by omega]
          simp [Nat.pow_add]
        have room : first.val+count.val≤2^32 := by
          rw [pos,val,← Nat.add_one_mul]
          exact (Nat.mul_le_mul_left _ power).trans limit
        have cap : count.val≤64 := by
          rw [val]; exact Nat.pow_le_pow_right (by decide) (show height.val-(k+1)≤6 by omega)
        simp [lift,Array.to_slice_mut,Array.to_slice,Array.from_slice,smallSliceAt,bind_ok]
        have parents := small_level p hp seed hs {a with word2:=it.start}
          (by change it.start.val<65536;omega) first current count (by change count.val≤128;omega)
        have done := advance p seed sk a idx.val height.val k first it.start current _ active pos status previous
          (fun j hj => parents j (by omega))
        split at iteration
        · obtain ⟨_,inc,finish,remains⟩ := iteration
          simp only [step_simps,remains,live,Bool.false_eq_true,ite_false]
          exact ⟨⟨k+1,by omega,finish.trans last,by omega,done⟩,by omega⟩
        · obtain ⟨_,_,finish,ends⟩ := iteration
          simp only [step_simps,ends,live,Bool.false_eq_true,ite_false,ite_true]
          exact ⟨⟨k+1,by omega,finish.trans last,by rw [last] at *;omega,done⟩,by omega⟩
  · exact ⟨0,by omega,rfl,rfl,prior⟩

theorem reduceWide {N} (p : params.Params) (hp : PN p N) (seed : hash.Seed N)
    (hs : SeedOk seed) (wide : N.val=24 ∨ N.val=32) (enabled : Bool) (sk : Array U8 N) (a : address.Adrs)
    (idx height : U32) (n : Usize) (roots : Nodes N 128#usize)
    (small : height.val≤7) (size : n.val=2^height.val)
    (prior : level p seed sk a idx.val height.val 0 roots) (limit : (idx.val+1)*2^height.val≤2^32) :
    fors.arm.subtree_loop1 enabled ⟨1#u32,height,false⟩ idx height seed.pk_seed seed.state seed.state512 a n roots ⦃ out =>
      level p seed sk a idx.val height.val height.val out ⦄ := by
  unfold fors.arm.subtree_loop1
  apply loop.spec_decr_nat
    (measure := fun q : Levels × Nodes N 128#usize => if q.1.exhausted then 0 else height.val+1-q.1.start.val)
    (inv := fun q => ∃ k, k≤height.val ∧ q.1.end=height ∧
      (if q.1.exhausted then k=height.val else q.1.start.val=k+1) ∧
      level p seed sk a idx.val height.val k q.2)
  · rintro ⟨it,current⟩ ⟨k,bound,last,status,previous⟩
    simp only at last status previous ⊢
    unfold fors.arm.subtree_loop1.body
    step as ⟨opt,next,iteration⟩
    by_cases stopped : it.exhausted=true
    · simp [stopped] at status iteration
      simp only [iteration.1,step_simps]
      exact status ▸ previous
    · have live : it.exhausted=false := by simpa using stopped
      simp only [live,Bool.false_eq_true,ite_false] at status
      by_cases finished : it.end.val < it.start.val
      · simp [live,finished] at iteration
        simp only [iteration.1,step_simps]
        have eq : k=height.val := by rw [last,status] at finished;omega
        exact eq ▸ previous
      · have active : k<height.val := by rw [last,status] at finished;omega
        simp only [live,Bool.false_eq_true,false_or,ite_eq_right finished] at iteration
        have item : opt=some it.start := by split at iteration <;> exact iteration.1
        simp only [item]
        step as ⟨diff,diffVal⟩
        step as ⟨first,firstVal⟩
        have power : 2^(height.val-(k+1))≤2^height.val :=
          Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)
        have pos : first.val=idx.val*2^(height.val-(k+1)) := by
          rw [firstVal,Nat.shiftLeft_eq,diffVal,status,U32.size_eq,Nat.mod_eq_of_lt]
          have := Nat.mul_le_mul_left (idx.val+1) power
          rw [Nat.add_one_mul] at this
          have := Nat.two_pow_pos (height.val-(k+1));omega
        simp only [address.Adrs.with_word2,bind_ok,lift,Array.to_slice_mut]
        step as ⟨count,countVal⟩
        · rcases System.Platform.numBits_eq with b|b <;> rw [b] <;> omega
        have val : count.val=2^(height.val-(k+1)) := by
          rw [countVal,size,status,Nat.shiftRight_eq_div_pow]
          rw (occs := .pos [1]) [show height.val=(height.val-(k+1))+(k+1) by omega]
          simp [Nat.pow_add]
        have room : first.val+count.val≤2^32 := by
          rw [pos,val,← Nat.add_one_mul]
          exact (Nat.mul_le_mul_left _ power).trans limit
        have cap : count.val≤64 := by
          rw [val]; exact Nat.pow_le_pow_right (by decide) (show height.val-(k+1)≤6 by omega)
        simp [lift,Array.to_slice_mut,Array.to_slice,Array.from_slice,parentSliceAt,bind_ok]
        rw [show fors.arm.subtree_loop1_loop0 _ seed.pk_seed seed.state seed.state512 _ first _ = _ from
          shared_tail _ seed _ first _]
        step with full_level p hp seed hs wide enabled _ first current count
          (by change 2*count.val≤128;omega) (by decide) room as ⟨out,parents⟩
        have done := advance p seed sk a idx.val height.val k first it.start current out active pos status previous
          (fun j hj => parents j (by omega))
        split at iteration
        · obtain ⟨_,inc,finish,remains⟩ := iteration
          simp only [step_simps,remains,live,Bool.false_eq_true,ite_false]
          exact ⟨⟨k+1,by omega,finish.trans last,by omega,done⟩,by omega⟩
        · obtain ⟨_,_,finish,ends⟩ := iteration
          simp only [step_simps,ends,live,Bool.false_eq_true,ite_false,ite_true]
          exact ⟨⟨k+1,by omega,finish.trans last,by rw [last] at *;omega,done⟩,by omega⟩
  · exact ⟨0,by omega,rfl,rfl,prior⟩

end slhdsa.ArmForsTree
