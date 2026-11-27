import Buffered.Transfer
import Buffered.FlushTransfer
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.Buffered
open ShakeBatch NativeVerify
set_option maxHeartbeats 650000
variable [kernel : Kernel]

theorem flush {N : Usize} (p : params.Params) (hp : PN p N) (sk seed : Array U8 N) (a tree : address.Adrs)
    (root : Nat) (z : Usize) (buf : Buffer N) (len : Lengths) (cur : Cursors)
    (addrs : Array address.Adrs 8#usize) (left right : Rows8 N) (lo : 3≤z.val) (hi : z.val≤9)
    (room : (root+1)*2^z.val≤512) (domain : adrsS tree=(adrsS a).setTypeAndClear Spec.TREE)
    (initial : Grid (xmss p sk seed a) root z.val (produced (2^(z.val-3))) buf len cur)
    (perm : ActiveCorrect (machine kernel) kernel.active) :
    subtree_loop3 ⟨0#usize,z⟩ seed tree buf len cur addrs left right ⦃ out =>
      cellBytes out z.val 0=xmss p sk seed a z.val root ⦄ := by
  unfold subtree_loop3
  apply loop.spec_decr_nat (measure:=fun s : (core.ops.range.Range Usize) × Buffer N × Lengths × Cursors ×
    (Array address.Adrs 8#usize) × Rows8 N × Rows8 N => z.val-s.1.start.val)
    (inv:=fun s=> s.1.end=z ∧ s.1.start.val≤z.val ∧
      Grid (xmss p sk seed a) root z.val (flushCount z.val s.1.start.val) s.2.1 s.2.2.1 s.2.2.2.1)
  · rintro ⟨it,buf,len,cur,as',ls,rs⟩ ⟨last,le,grid⟩
    simp only at last le grid ⊢
    by_cases more : it.start.val<z.val
    · let h := it.start.val
      let c := flushCount z.val h
      obtain ⟨even,small,space,balanced,upper,bounded⟩ := flush_stats z.val h lo hi more
      change waiting c h % 2=0 at even
      change waiting c h≤16 at small
      change waiting c (h+1)+waiting c h/2≤16 at space
      change c (h+1)≤512 at bounded
      let n := waiting c h/2
      have full : waiting c h=2*n := by dsimp [n];omega
      have baseCap : levelBase root z.val (h+1)≤512 := by
        have power := Nat.pow_le_pow_right (by decide : 0<2) (Nat.sub_le z.val (h+1))
        exact ((Nat.mul_le_mul_left root power).trans (Nat.mul_le_mul_right _ (Nat.le_succ root))).trans room
      apply WP.spec_mono (flush_transfer p hp seed tree it buf len cur as' ls rs n (waiting c (h+1))
        (nextBase root z.val c (h+1)) (by rw [last];exact more) (by omega)
        ((grid.count h le).trans full) (grid.count _ more) (grid.index _ more) (by omega) space
        (by simp [nextBase];omega) perm)
      rintro (⟨next,out,len',cur',_,_,_⟩ | answer) post
      swap
      · exact False.elim post
      obtain ⟨inc,ends,post⟩ := post
      have update : Grid (xmss p sk seed a) root z.val (flushCount z.val (h+1)) out len' cur' := by
        apply grid.merge h n more full balanced upper (fun k => flush_next z.val h k lo hi more)
        · exact fun k _ => post.lengths k
        · exact fun k _ => post.cursor k
        · intro k kz j live
          change bytes out.val[k]!.val[j]!.val=_
          rw [post.cells]
          split_ifs with hit
          · exact hashed_node p sk seed a tree grid h (j-waiting c (h+1)) more (by change 2*(j-waiting c (h+1))+1 < waiting c h;omega) domain
          · rfl
        · intro k kz;exact flush_room z.val (h+1) k lo hi more kz
      exact ⟨⟨ends.trans last,by change next.start.val ≤ z.val;omega,by simpa only [inc] using update⟩,by simp only;omega⟩
    · have stop : it.start.val=z.val := by omega
      unfold subtree_loop3.body
      obtain ⟨⟨_,_⟩,none,tag,_⟩ := spec_imp_exists (core.iter.range.IteratorRange.next_Usize_none_spec it (by rw [last];omega))
      simp only [none,bind_ok,tag,step_simps]
      rw [stop] at grid
      obtain ⟨one,done⟩ := finish_stats z.val lo hi
      have got := grid.cell z.val (le_refl _) 0 (by omega)
      simpa [rowBase,done,levelBase] using got
  · refine ⟨rfl,by simp,initial.congr_made ?_⟩
    intro k hk;exact (flush_start z.val k lo hi).symm
end slhdsa.Buffered
