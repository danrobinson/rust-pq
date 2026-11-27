import Buffered.ForsHorizontal.Carry
import Buffered.ForsHorizontal.Leaves
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.ForsHorizontal
open ShakeBatch NativeVerify
open Buffered
set_option maxHeartbeats 850000
variable [kernel : Fused.Kernel]
local instance : Machine := Fused.machine kernel

theorem blocks {N : Usize} (p : params.Params) (hp : PN p N) (sk seed : Array U8 N) (a tree : address.Adrs)
    (root : Nat) (z : Usize) (num first : U32) (buf : Buffer N) (len : Lengths) (cur : Cursors)
    (addrs : Scratch) (left right : Rows8 N) (lo : 3≤z.val) (hi : z.val≤14) (room : (root+1)*2^z.val≤1048576)
    (batches : num.val=2^(z.val-3)) (offset : first.val=root*2^z.val)
    (domain : adrsS tree=adrsS a)
    (initial : Grid (fors p sk seed a) root z.val (produced 0) buf len cur)
    (domainLeaf : Domain a) (perm : ActiveCorrect (Fused.machine kernel) kernel.active) :
    subtree_loop1 ⟨0#u32,num⟩ sk seed a.layer a.tree a.typ a.keypair a.word2 a.word3 z tree buf len cur first addrs left right ⦃ v =>
      Grid (fors p sk seed a) root z.val (produced num.val) v.1 v.2.1 v.2.2.1 ⦄ := by
  have numCap : num.val≤2048 := batches ▸ Nat.pow_le_pow_right (by decide) (show z.val-3≤11 by omega)
  have total : 8*num.val=2^z.val := by rw [batches,show z.val=(z.val-3)+3 by omega] <;> simp [Nat.pow_add,Nat.mul_comm]
  unfold subtree_loop1
  apply loop.spec_decr_nat (measure:=fun s : (core.ops.range.Range U32) × StreamState N => num.val-s.1.start.val)
    (inv:=fun s => s.1.end=num ∧ s.1.start.val≤num.val ∧ Grid (fors p sk seed a) root z.val
      (produced s.1.start.val) s.2.1 s.2.2.1 s.2.2.2.1)
  · rintro ⟨it,buf,len,cur,as',ls,rs⟩ ⟨last,le,grid⟩
    simp only at last le grid ⊢
    unfold subtree_loop1.body
    by_cases more : it.start.val<num.val
    · step with core.iter.range.IteratorRange.next_U32_some_spec it (by rw [last];exact more) as ⟨_,next,tag,inc,ends⟩
      simp only [tag]
      have leafCap : first.val+it.start.val*8+8≤1048576 := by rw [Nat.add_mul,Nat.one_mul,←offset,←total] at room;omega
      step as ⟨delta,deltaEq⟩
      step as ⟨start,startEq⟩
      step with indices_spec N start (by omega) as ⟨ids,idVals⟩
      step with NativeVerify.ForsFused.leaf_correct kernel.active perm p hp sk seed a ids 8#usize domainLeaf (le_refl _) as ⟨rows,values⟩
      have rowValues (j : Nat) (live : j<8) : bytes rows.val[j]!.val = fors p sk seed a 0 (start.val+j) := by
        rw [values j live,idVals j live];rfl
      have rowLen : rows.val.length=8 := rows.property
      step as ⟨dst,getDst⟩
      rw [←getElem!_pos] at getDst
      have dv : dst.val=waiting (produced it.start.val) 0 := getDst ▸ grid.count 0 (by omega)
      obtain ⟨limit,balanced⟩ := block_stats it.start.val
      step as ⟨oldRow,restore,got,save⟩
      step as ⟨stop,sv⟩
      step as ⟨part,put,rv,rl,write⟩
      try simp only [lift,bind_ok]
      step as ⟨copy,copied⟩
      step as ⟨newLen,newLenEq⟩
      all_goals try scalar_tac
      all_goals try (simp [sv] at *;omega)
      let out := restore (put copy)
      have store : Stored buf out 0 dst.val 8 rows := by
        dsimp only [out];rw [save]
        apply stored_cells_at _ _ _ _ _ _ (by decide) (by omega) (by decide)
        have cut : rows.val.take 8 = rows.val := List.take_of_length_le (le_of_eq rowLen)
        rw [write,copied,Array.val_to_slice,got,←getElem!_pos]
        exact congrArg (fun xs => buf.val[0]!.val.setSlice! dst.val xs) cut.symm
      have pushed : Grid (fors p sk seed a) root z.val (carryCount it.start.val 0) out newLen cur := by
        apply grid.appendLeaves balanced (start_leaf _) _ _ (fun k hk => carry_room _ _ _ (by omega) (by omega) (by omega))
        · intro k kz
          rw [newLenEq,set_value _ _ _ _ (by decide)]
          by_cases zero : k=0
          · subst k;simp;rw [sv,getDst,←getElem!_pos]
          · simp only [show (0#usize).val=0 from rfl,if_neg zero]
        · intro k kz j small
          have index : start.val=levelBase root z.val 0+produced it.start.val 0 := by
            simp [levelBase,produced,offset,startEq,deltaEq,Nat.mul_comm]
          simpa only [dv,index,fors] using stored_bytes store _ rowValues k j
      step with carry p hp sk seed a tree root it.start.val z out newLen cur as' ls rs lo hi room (batches ▸ more)
        domain pushed perm as ⟨v,l2,c2,a2,l3,r3,done⟩
      exact ⟨ends.trans last,by omega,by simpa only [inc] using done,by omega⟩
    · obtain ⟨⟨_,_⟩,none,tag,_⟩ := spec_imp_exists (core.iter.range.IteratorRange.next_U32_none_spec it (by rw [last];omega))
      simp [none,tag,show it.start.val=num.val by omega] at grid ⊢
      exact grid
  · exact ⟨rfl,by simp,initial⟩
end slhdsa.ForsHorizontal
