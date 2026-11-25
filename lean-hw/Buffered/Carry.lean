import Buffered.Transfer
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.Buffered
open ShakeBatch NativeVerify
variable [kernel : Kernel]
set_option linter.concreteInstances false
set_option maxHeartbeats 1100000

abbrev Scratch := Array address.Adrs 8#usize
abbrev StreamState (N : Usize) := Buffer N × Lengths × Cursors × Scratch × Rows8 N × Rows8 N

private theorem lengthFrame (len : Lengths) (h u stop : Usize)
    (fit : h.val<16) (upper : u.val=h.val+1) (sv : stop.val=len.val[u.val]!.val+8) (k : Nat) :
    ((len.set h 0#usize).set u stop).val[k]!.val =
      if k=h.val then 0 else if k=h.val+1 then len.val[k]!.val+8 else len.val[k]!.val := by
  rw [set_value _ _ _ _ (by change u.val<17;omega)]
  by_cases hit : k=u.val
  · subst k; simp [upper,sv,show h.val+1≠h.val by omega]
  · rw [if_neg hit,set_value _ _ _ _ (by change h.val<17;omega)]
    by_cases empty : k=h.val
    · simp [empty]
    · simp [empty,show k≠h.val+1 by omega]

private theorem cursorFrame (cur : Cursors) (u : Usize) (v : U32) (k : Nat)
    (fit : u.val<17) (bump : v.val=cur.val[u.val]!.val+8) :
    (cur.set u v).val[k]!.val=if k=u.val then cur.val[k]!.val+8 else cur.val[k]!.val := by
  rw [set_value _ _ _ _ fit]
  by_cases hit : k=u.val <;> simp [hit,bump]

theorem carry {N : Usize} (p : params.Params) (hp : PN p N) (sk seed : Array U8 N) (a tree : address.Adrs)
    (root b : Nat) (z : Usize) (buf : Buffer N) (len : Lengths) (cur : Cursors) (addrs : Scratch) (left right : Rows8 N)
    (lo : 3≤z.val) (hi : z.val≤9) (room : (root+1)*2^z.val≤512) (inside : b<2^(z.val-3))
    (domain : adrsS tree=(adrsS a).setTypeAndClear Spec.TREE)
    (initial : Grid (xmss p sk seed a) root z.val (carryCount b 0) buf len cur)
    (perm : ActiveCorrect (machine kernel) kernel.active) :
    subtree_loop2_loop0 ⟨0#usize,z⟩ seed tree buf len cur addrs left right ⦃ v =>
      Grid (xmss p sk seed a) root z.val (produced (b+1)) v.1 v.2.1 v.2.2.1 ⦄ := by
  have num : 2^(z.val-3)≤64 := Nat.pow_le_pow_right (by decide) (show z.val-3≤6 by omega)
  have hb : b<64 := lt_of_lt_of_le inside num
  unfold subtree_loop2_loop0
  apply loop.spec_decr_nat (measure:=fun s : core.ops.range.Range Usize × StreamState N => z.val-s.1.start.val)
    (inv:=fun s => s.1.«end»=z ∧ s.1.start.val≤z.val ∧
      Grid (xmss p sk seed a) root z.val (carryCount b s.1.start.val) s.2.1 s.2.2.1 s.2.2.2.1)
  · rintro ⟨it,buf,len,cur,addrs,left,right⟩ ⟨last,le,grid⟩
    simp only at last le grid ⊢
    unfold subtree_loop2_loop0.body
    by_cases live : it.start.val<z.val
    · step with core.iter.range.IteratorRange.next_Usize_some_spec it (by rw [last];exact live) as ⟨_,next,tag,inc,ends⟩
      simp only [tag]
      let h := it.start.val
      let c := carryCount b h
      change Grid (xmss p sk seed a) root z.val c buf len cur at grid
      have hz : h<z.val := live
      obtain ⟨bound,space,balanced,upper⟩ := carry_stats b h hb (by omega)
      change waiting c h≤16 at bound
      change waiting c (h+1)≤8 at space
      step as ⟨cnt,read⟩
      rw [←getElem!_pos] at read
      have cntOk : cnt.val=waiting c h := read ▸ grid.count h le
      split
      · rename_i stop
        simp only [step_simps]
        apply grid.congr_made
        intro k hk
        exact carry_stop b h k hb (by omega) (by omega) (by change waiting c h<16;change cnt.val<16 at stop;omega)
      · rename_i recurse
        have full : waiting c h=16 := by change ¬cnt.val<16 at recurse;omega
        step as ⟨succ,sv⟩
        have sh : succ.val=h+1 := sv
        have sz : succ.val≤z.val := by omega
        step as ⟨base,br⟩
        rw [←getElem!_pos] at br
        have bv : base.val=nextBase root z.val c (h+1) := by rw [br,←sh]; exact grid.index _ sz
        have rootCap : levelBase root z.val (h+1)≤512 := by
          have power := Nat.pow_le_pow_right (by decide : 0<2) (Nat.sub_le z.val (h+1))
          unfold levelBase
          exact ((Nat.mul_le_mul_left root power).trans (Nat.mul_le_mul_right _ (Nat.le_succ root))).trans room
        have computed := carry_bound b h (h+1)
        change c (h+1)≤8*(b+1) at computed
        have baseCap : base.val≤1024 := by simp [nextBase] at bv;omega
        let lvl := UScalar.cast .U32 succ
        have lvlVal : lvl.val=h+1 := by dsimp [lvl];scalar_tac
        simp only [lift,bind_ok]
        step as ⟨row,rowRead⟩
        rw [←getElem!_pos] at rowRead
        step with carry_gather 8#usize tree addrs left right base lvl row (by decide) (by change base.val+8 ≤ 2^32;omega) as ⟨as',ls,rs,gather⟩
        step with hashed_gather p hp seed tree 8#usize base lvl row as' ls rs (by decide) gather perm as ⟨parents,hashes⟩
        have plen : parents.val.length=8 := parents.property
        have rows (j : Nat) (hj : j<8) : bytes parents.val[j]!.val=xmss p sk seed a (h+1) (nextBase root z.val c (h+1)+j) := by
          rw [hashes j hj,rowRead,bv,lvlVal]
          exact hashed_node p sk seed a tree grid h j hz (by omega) domain
        step as ⟨reset,resetEq⟩
        step as ⟨dest,destEq⟩
        have destH : dest.val=h+1 := destEq
        step as ⟨dst,dstEq⟩
        rw [←getElem!_pos] at dstEq
        have dstOk : dst.val=waiting c (h+1) := by
          rw [dstEq,resetEq,set_value len it.start 0#usize dest.val (by change it.start.val<17;omega),if_neg (by omega),←destH]
          exact grid.count _ (by omega)
        step as ⟨oldRow,restore,got,save⟩
        step as ⟨stop,stopVal⟩
        step as ⟨part,put,rv,rl,write⟩
        try simp only [lift,bind_ok]
        step as ⟨copy,copied⟩
        · have rhs : parents.to_slice.length=8 := by
            simp only [Slice.length,Array.val_to_slice]
            exact plen
          rw [rl,stopVal,rhs];omega
        step as ⟨newLen,newLenEq⟩
        step as ⟨num,numEq⟩
        step as ⟨newCur,newCurEq⟩
        all_goals try scalar_tac
        all_goals try (simp [stopVal] at *;omega)
        let out := restore (put copy)
        have store : Stored buf out dest.val dst.val 8 parents := by
          dsimp only [out]
          rw [save]
          apply stored_cells _ _ _ _ _ _ (by omega) (by omega) (by decide)
          have cut : parents.val.take 8 = parents.val := List.take_of_length_le (le_of_eq plen)
          rw [write,copied,Array.val_to_slice,got,←getElem!_pos]
          exact congrArg (fun xs => buf.val[dest.val]!.val.setSlice! dst.val xs) cut.symm
        have updated : Grid (xmss p sk seed a) root z.val (carryCount b (h+1)) out newLen newCur := by
          apply grid.merge h 8 hz full balanced upper (fun k => carry_next b h k full hb (by omega))
          · intro k kz
            rw [newLenEq,resetEq]
            apply lengthFrame len it.start dest stop (by omega) destH
            rw [stopVal,dstOk,grid.count dest.val (by omega),destH]
          · intro k kz
            rw [newCurEq,←destH]
            apply cursorFrame _ _ _ k (by omega)
            rw [numEq,br]
            have eq : succ=dest := UScalar.eq_of_val_eq (sh.trans destH.symm)
            rw [eq]
          · intro k kz j small
            simpa only [destH,dstOk] using stored_bytes store _ rows k j
          · intro k kz;exact carry_room b (h+1) k hb (by omega) (by omega)
        exact ⟨ends.trans last,by omega,by simpa only [inc] using updated,by omega⟩
    · obtain ⟨⟨_,_⟩,none,tag,_⟩ := spec_imp_exists (core.iter.range.IteratorRange.next_Usize_none_spec it (by rw [last];omega))
      simp only [none,bind_ok,tag,step_simps]
      apply grid.congr_made
      intro k hk
      rw [show it.start.val=z.val by omega]
      exact carry_end z.val b k lo hi inside hk
  · exact ⟨rfl,by simp,initial⟩
end slhdsa.Buffered
