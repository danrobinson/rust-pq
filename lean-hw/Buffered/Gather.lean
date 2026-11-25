import Buffered.Program
import Shakebatch.Range
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.Buffered
open ShakeBatch NativeVerify

def Gathered {N : Usize} (count : Nat) (tree : address.Adrs) (base lvl : U32) (row : Row16 N)
    (addrs : Array address.Adrs 8#usize) (left right : Rows8 N) : Prop :=
  ∀ k < count, adrsS addrs.val[k]! = {adrsS tree with word2:=lvl.val,word3:=base.val+k} ∧
    left.val[k]! = row.val[2*k]! ∧ right.val[k]! = row.val[2*k+1]!

theorem carry_gather {N : Usize} (count : Usize) (tree : address.Adrs)
    (addrs : Array address.Adrs 8#usize) (left right : Rows8 N) (base lvl : U32) (row : Row16 N)
    (fit : count.val≤8) (words : base.val+count.val≤2^32) :
    subtree_loop2_loop0_loop0 ⟨0#usize,count⟩ tree addrs left right base lvl row ⦃ as' ls rs =>
      Gathered count.val tree base lvl row as' ls rs ⦄ := by
  unfold subtree_loop2_loop0_loop0
  apply loop.spec_decr_nat
    (measure := fun q : core.ops.range.Range Usize × Array address.Adrs 8#usize × Rows8 N × Rows8 N => count.val-q.1.start.val)
    (inv := fun q => q.1.end=count ∧ q.1.start.val≤count.val ∧ Gathered q.1.start.val tree base lvl row q.2.1 q.2.2.1 q.2.2.2)
  · rintro ⟨it,avs,ls,rs⟩ ⟨stop,limit,prior⟩
    simp only at stop limit prior ⊢
    unfold subtree_loop2_loop0_loop0.body
    by_cases more : it.start.val<count.val
    · step with core.iter.range.IteratorRange.next_Usize_some_spec it (by rw [stop];exact more) as ⟨_,next,tag,inc,last⟩
      simp only [tag]
      step as ⟨a,level⟩
      simp only [lift,bind_ok]
      have cast : (UScalar.cast .U32 it.start).val=it.start.val := by scalar_tac
      step as ⟨word,wv⟩
      step as ⟨addr,idx⟩
      step as ⟨avs',ua⟩
      step as ⟨la,lv⟩
      step as ⟨lval,lg⟩
      step as ⟨ls',ul⟩
      step as ⟨ra,rv⟩
      step as ⟨rval,rg⟩
      step as ⟨rs',ur⟩
      refine ⟨last.trans stop,by omega,?_,by omega⟩
      intro k hk
      rw [ua,ul,ur,Array.set_val_eq,Array.set_val_eq,Array.set_val_eq]
      by_cases same : k=it.start.val
      · subst k
        rw [setSame _ _ _ (by simp;omega),setSame _ _ _ (by simp;omega),setSame _ _ _ (by simp;omega)]
        rw [idx,level,lg,rg,← getElem!_pos,← getElem!_pos]
        simp [adrsS,wv,cast,lv,rv]
      · rw [setOther _ _ _ _ (Ne.symm same),setOther _ _ _ _ (Ne.symm same),setOther _ _ _ _ (Ne.symm same)]
        exact prior k (by omega)
    · step with core.iter.range.IteratorRange.next_Usize_none_spec it (by rw [stop];omega) as ⟨_,_,tag,_⟩
      simp only [tag,step_simps]
      exact (show it.start.val=count.val by omega) ▸ prior
  · exact ⟨rfl,Nat.zero_le _,by intro k live;change k<0 at live;omega⟩

theorem flush_gather {N : Usize} (count : Usize) (tree : address.Adrs)
    (addrs : Array address.Adrs 8#usize) (left right : Rows8 N) (base lvl : U32) (row : Row16 N)
    (fit : count.val≤8) (words : base.val+count.val≤2^32) :
    subtree_loop3_loop0 ⟨0#usize,count⟩ tree addrs left right base lvl row ⦃ as' ls rs =>
      Gathered count.val tree base lvl row as' ls rs ⦄ :=
  carry_gather count tree addrs left right base lvl row fit words

variable [kernel : Kernel]
local instance gatherMachine : Machine := machine kernel

/-- Each active Keccak parent combines exactly its two neighboring cells in the
immutable sixteen-row snapshot, using the parent height and absolute index. -/
theorem hashed_gather {N : Usize} (p : params.Params) (hp : PN p N) (seed : Array U8 N)
    (tree : address.Adrs) (count : Usize) (base lvl : U32) (row : Row16 N)
    (addrs : Array address.Adrs 8#usize) (left right : Rows8 N) (live : count.val≤8)
    (gathered : Gathered count.val tree base lvl row addrs left right)
    (perm : ActiveCorrect (machine kernel) kernel.active) :
    ActiveHash.pair_active kernel.active seed addrs left right count ⦃ out => ∀ k < count.val,
      bytes out.val[k]!.val = Spec.H (Shake.params p) (bytes seed.val)
        {adrsS tree with word2:=lvl.val,word3:=base.val+k}
        (bytes row.val[2*k]!.val ++ bytes row.val[2*k+1]!.val) ⦄ := by
  apply WP.spec_mono (@ActiveHash.pair_fips (machine kernel) kernel.active N seed addrs left right count live perm hp.le32 (aligned_hash hp))
  intro out hashes k hk
  obtain ⟨a,l,r⟩ := gathered k hk
  rw [←a,←l,←r]
  have fact := hashes k hk
  simp only [Spec.H,Shake.params,paramsS_n,hp.n_eq,List.append_assoc] at fact ⊢
  with_unfolding_all exact fact

end slhdsa.Buffered
