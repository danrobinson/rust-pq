import Parentdriver.Dispatch
open Aeneas Aeneas.Std Result
namespace slhdsa.PlatformParent.Driver

def siblingStart (n height offset i : Nat) := n*(i*(height+1)+1+offset)
def sibling (sig : Slice U8) (n height offset i : Nat) :=
  bytes (sig.val.slice (siblingStart n height offset i) (siblingStart n height offset i+n))
def nextIndex (position : U32) : U32 := ⟨position.bv >>> 1⟩
def pathAddress (a : address.Adrs) (position : U32) := treeAddress a (nextIndex position).val
def pathData {N : Usize} (v : Nodes N) (idx : Slice U32) (sig : Slice U8) (height offset i : Nat) :=
  let sib := sibling sig N.val height offset i
  if idx.val[i]!.val % 2 = 0 then nodeBytes v i ++ sib else sib ++ nodeBytes v i

def SigBounds (n h off count : Nat) (sig : Slice U8) :=
  ∀ i, i < count → siblingStart n h off i + n ≤ sig.length

private theorem parity (x : U32) : ((x &&& 1#u32) = 0#u32) ↔ x.val%2 = 0 := by
  rw [UScalar.eq_equiv_bv_eq]
  change x.bv &&& 1#32 = 0#32 ↔ x.bv.toNat%2 = 0
  rw [← BitVec.toNat_inj]
  simp [BitVec.toNat_and,Nat.and_one_is_mod]

def IndexRange (orig cur : Slice U32) (start t : Nat) :=
  cur.length = orig.length ∧ ∀ i, i < orig.length → cur.val[i]! =
    if start ≤ i ∧ i < start+t then nextIndex orig.val[i]! else orig.val[i]!

private def BatchReady {G : Usize} (bs : Blocks G) (used : Nat) (expected : Nat → Spec.Bytes) :=
  ∀ k, k < G.val → if k < used then bytes bs.val[k]!.val = expected k else bs.val[k]! = zeroBlock

theorem path_blocks_spec {N G : Usize} (a : address.Adrs) (v : Nodes N) (indices : Slice U32)
    (sig : Slice U8) (height offset j : Usize)
    (shape : N.val = 24 ∨ N.val = 32) (hv : j.val+G.val ≤ v.length)
    (hi : v.length ≤ indices.length) (hh : height.val+1 ≤ Usize.max)
    (hbnd : SigBounds N.val height.val offset.val v.length sig) :
    pathBlocks ⟨0#usize,G⟩ a v indices sig height offset j (Array.repeat G zeroBlock) ⦃ idx bs =>
      IndexRange indices idx j.val G.val ∧ ∀ k, k < G.val → bytes bs.val[k]!.val =
        padded (pathAddress a indices.val[j.val+k]!) (pathData v indices sig height.val offset.val (j.val+k)) ⦄ := by
  let expected := fun k => padded (pathAddress a indices.val[j.val+k]!) (pathData v indices sig height.val offset.val (j.val+k))
  unfold pathBlocks
  apply loop.spec_decr_nat (measure := fun p : core.ops.range.Range Usize × Slice U32 × Blocks G => G.val-p.1.start.val)
    (inv := fun p => p.1.end = G ∧ p.1.start.val ≤ G.val ∧ IndexRange indices p.2.1 j.val p.1.start.val ∧
      BatchReady p.2.2 p.1.start.val expected)
  · rintro ⟨it,idx,bs⟩ ⟨he,ht,⟨hlen,hidx⟩,hbs⟩
    simp only at he ht hlen hidx hbs
    unfold pathBlockStep
    by_cases hlt : it.start.val < it.end.val
    · have hl : it.start.val < G.val := he ▸ hlt
      step with core.iter.range.IteratorRange.next_Usize_some_spec it hlt as ⟨opt,nxt,hopt,hn,hen⟩
      simp only [hopt]
      step as ⟨blk,back,hblk,hback⟩
      step as ⟨i,hip⟩
      step as ⟨pos,hp⟩
      step as ⟨par,hpar⟩
      step as ⟨idx1,hm⟩
      have hsig := hbnd i.val (by omega)
      unfold siblingStart at hsig
      have lower : i.val*(height.val+1)+1+offset.val ≤ N.val*(i.val*(height.val+1)+1+offset.val) :=
        Nat.le_mul_of_pos_left _ (by omega)
      have hmax := sig.len.hmax
      step as ⟨h1,hh1⟩
      step as ⟨h2,hh2⟩
      step as ⟨h3,hh3⟩
      step as ⟨h4,hh4⟩
      step as ⟨start,hstart⟩
      step as ⟨stop,hstop⟩
      step as ⟨sib,hsib,hslen⟩
      step as ⟨row,hrow⟩
      step as ⟨node,hnode⟩
      step as ⟨bit,hbit⟩
      have hpos : pos = indices.val[i.val]! := by
        rw [hp,← getElem!_pos,hidx _ (by omega),if_neg (by omega)]
      have hpar' : par = nextIndex pos := by apply U32.bv_eq_imp_eq; assumption
      have heven : bit = 0#u32 ↔ pos.val%2=0 := by
        have e : bit = pos &&& 1#u32 := UScalar.eq_of_val_eq hbit
        rw [e,parity]
      have hilen : idx1.length = idx.length := by simp [hm,Slice.length,Slice.set_val_eq]
      have idxnext : IndexRange indices idx1 j.val nxt.start.val := by
        refine ⟨hilen.trans hlen,fun k hk => ?_⟩
        rw [hm,Slice.set_val_eq]
        by_cases eq : k = i.val
        · subst k
          rw [getElem!_pos _ _ (by simpa [Slice.length] using (show i.val < idx.length by omega)),List.getElem_set_self,
            if_pos (by omega),hpar',hpos]
        · simp only [List.getElem!_eq_getElem?_getD,List.getElem?_set_ne (Ne.symm eq)]
          simpa only [List.getElem!_eq_getElem?_getD,
            show (j.val ≤ k ∧ k < j.val+nxt.start.val) ↔ (j.val ≤ k ∧ k < j.val+it.start.val) by omega] using hidx k hk
      have hinit := hbs it.start.val hl
      simp only [if_neg (Nat.lt_irrefl _)] at hinit
      have hzero : blk = zeroBlock := by rw [hblk,← getElem!_pos,hinit]
      have sb : bytes sib.val = sibling sig N.val height.val offset.val i.val := by
        simp only [sibling,siblingStart,hsib,hstop,hstart,hh1,hh2,hh3,hh4]
      have nb : bytes node.val = nodeBytes v i.val := by simp only [hnode,Array.val_to_slice,hrow,← getElem!_pos,nodeBytes]
      let lr := if pos.val%2=0 then (node,sib) else (sib,node)
      have ordered : (if bit = 0#u32 then ok (node,sib) else ok (sib,node) : Result _) = ok lr := by
        by_cases b : bit = 0#u32
        · simp [b,lr,heven.mp b]
        · simp [b,lr,heven.not.mp b]
      have sizes : lr.1.length = N.val ∧ lr.2.length = N.val := by
        unfold lr; split <;> simp [hnode,hslen,hstop]
      have dat : bytes lr.1.val ++ bytes lr.2.val = pathData v indices sig height.val offset.val i.val := by
        simp only [lr,pathData,← hpos]; split <;> simp [nb,sb]
      obtain ⟨l,r,heq⟩ : ∃ l r, lr = (l,r) := ⟨lr.1,lr.2,rfl⟩
      rw [ordered,heq]
      simp only [bind_ok]
      rw [heq] at sizes dat
      step as ⟨p1,hp1⟩
      step as ⟨a1,ha1⟩
      rw [hzero]
      step with make_block_spec N a1 l r shape sizes.1 sizes.2 as ⟨b1,hb1⟩
      have pval : p1 = nextIndex pos := by
        rw [hp1,← getElem!_pos,idxnext.2 _ (by omega),if_pos (by omega),← hpos]
      refine ⟨hen.trans he,by omega,idxnext,fun k hk => ?_,by omega⟩
      rw [hback,Array.set_val_eq]
      by_cases here : k = it.start.val
      · subst k
        rw [if_pos (show it.start.val < nxt.start.val by omega),getElem!_pos _ _ (by simpa using hl),List.getElem_set_self,hb1]
        simp only [expected,padded,← hip,ha1,adrsS,pathAddress,treeAddress,pval,hpos,List.append_assoc,dat]
      · simp only [List.getElem!_eq_getElem?_getD,List.getElem?_set_ne (Ne.symm here)]
        simpa only [List.getElem!_eq_getElem?_getD,show (k < nxt.start.val) ↔ k < it.start.val by omega] using hbs k hk
    · step with core.iter.range.IteratorRange.next_Usize_none_spec it (by omega) as ⟨opt,nxt,hopt,hn⟩
      simp only [hopt,step_simps]
      have eq : it.start.val = G.val := by rw [he] at hlt; omega
      exact ⟨eq ▸ And.intro hlen hidx,fun k hk => by simpa only [if_pos (show k < it.start.val by omega)] using hbs k hk⟩
  · refine ⟨rfl,by simp,⟨rfl,by simp⟩,fun k hk => ?_⟩
    simp [Array.repeat_val,getElem!_pos,hk]

end slhdsa.PlatformParent.Driver
