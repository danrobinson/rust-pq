import Parentdriver.Targets
open Aeneas Aeneas.Std Result
namespace slhdsa.PlatformParent.Driver

def treeAddress (a : address.Adrs) (idx : Nat) := {adrsS a with word3 := idx}
def nodeBytes {N : Usize} (v : Nodes N) (i : Nat) := bytes v.val[i]!.val
def children {N : Usize} (v : Nodes N) (i : Nat) := nodeBytes v (2*i) ++ nodeBytes v (2*i+1)

def padded (a : Spec.Adrs) (data : Spec.Bytes) := S512.padFrom 128 (a.compress ++ data)
abbrev zeroBlock := Array.repeat 128#usize 0#u8

private def Prepared {G : Usize} (blocks : Blocks G) (used : Nat) (expected : Nat → Spec.Bytes) :=
  ∀ k, k < G.val → if k < used then bytes blocks.val[k]!.val = expected k
                                 else blocks.val[k]! = zeroBlock

theorem tree_blocks_spec {N G : Usize} (a : address.Adrs) (first : U32) (v : Nodes N) (j : Usize)
    (shape : N.val = 24 ∨ N.val = 32) (hv : 2*(j.val+G.val) ≤ v.length)
    (haddr : first.val + j.val + G.val ≤ 2^32) :
    treeBlocks ⟨0#usize,G⟩ a first v j (Array.repeat G zeroBlock) ⦃ blocks =>
      ∀ k, k < G.val → bytes blocks.val[k]!.val =
        padded (treeAddress a (first.val+j.val+k)) (children v (j.val+k)) ⦄ := by
  let expected := fun k => padded (treeAddress a (first.val+j.val+k)) (children v (j.val+k))
  unfold treeBlocks
  apply loop.spec_decr_nat (measure := fun p : core.ops.range.Range Usize × Blocks G => G.val-p.1.start.val)
    (inv := fun p => p.1.end = G ∧ p.1.start.val ≤ G.val ∧ Prepared p.2 p.1.start.val expected)
  · rintro ⟨it,b⟩ ⟨he,hi,hb⟩
    simp only at he hi hb
    unfold treeBlockStep
    by_cases hlt : it.start.val < it.end.val
    · have hl : it.start.val < G.val := he ▸ hlt
      step with core.iter.range.IteratorRange.next_Usize_some_spec it hlt as ⟨opt,nxt,hopt,hn,hen⟩
      simp only [hopt]
      step as ⟨blk,back,hblk,hback⟩
      step as ⟨idx,hidx⟩
      step as ⟨word,hword⟩
      have hcast : word.val = idx.val := by
        rw [hword,UScalar.cast_val_mod_pow_of_inBounds_eq _ _ (by change idx.val < 2^32; omega)]
      step as ⟨adr,hadr⟩
      step as ⟨a',ha⟩
      step as ⟨l,lh⟩
      step as ⟨left,hleft⟩
      step as ⟨ls,hls⟩
      step as ⟨r,rh⟩
      step as ⟨right,hright⟩
      step as ⟨rs,hrs⟩
      have zero := hb it.start.val hl
      simp only [if_neg (Nat.lt_irrefl _)] at zero
      have bzero : blk = zeroBlock := by rw [hblk, ← getElem!_pos, zero]
      rw [bzero]
      step with make_block_spec N a' ls rs shape (by simp [hls]) (by simp [hrs]) as ⟨b',hp⟩
      refine ⟨hen.trans he,by omega,fun k hk => ?_,by omega⟩
      rw [hback,Array.set_val_eq]
      by_cases here : k = it.start.val
      · subst k
        simp only [if_pos (show it.start.val < nxt.start.val by omega)]
        rw [getElem!_pos _ _ (by simpa using hl), List.getElem_set_self,hp]
        simp only [expected,padded,treeAddress,children,nodeBytes,ha,adrsS,hadr,hcast,hidx,
          hls,hrs,Array.val_to_slice,hleft,hright,← getElem!_pos,lh,rh,Nat.add_assoc,List.append_assoc]
      · simp only [List.getElem!_eq_getElem?_getD,List.getElem?_set_ne (Ne.symm here)]
        simpa only [List.getElem!_eq_getElem?_getD,show (k < nxt.start.val) ↔ k < it.start.val by omega] using hb k hk
    · step with core.iter.range.IteratorRange.next_Usize_none_spec it (by omega) as ⟨opt,nxt,hopt,hn⟩
      simp only [hopt,step_simps]
      intro k hk
      have h : k < it.start.val := by rw [he] at hlt; change ¬it.start.val < G.val at hlt; omega
      simpa only [if_pos h] using hb k hk
  · refine ⟨rfl,by simp,fun k hk => ?_⟩
    simp [Array.repeat_val,getElem!_pos, hk]

end slhdsa.PlatformParent.Driver
