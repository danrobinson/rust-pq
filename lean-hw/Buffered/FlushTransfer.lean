import Buffered.Store
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.Buffered
open ShakeBatch NativeVerify
set_option maxRecDepth 12000
set_option maxHeartbeats 1000000
set_option linter.concreteInstances false

def parentBytes {N : Usize} (p : params.Params) (seed : Array U8 N) (tree : address.Adrs)
    (buf : Stack N) (h base j : Nat) := Spec.H (Shake.params p) (bytes seed.val)
  {adrsS tree with word2:=h+1,word3:=base+j}
  (bytes buf.val[h]!.val[2*j]!.val ++ bytes buf.val[h]!.val[2*j+1]!.val)

structure FlushFacts {N : Usize} (p : params.Params) (seed : Array U8 N) (tree : address.Adrs)
    (buf out : Stack N) (len len' : Array Usize 17#usize) (cur cur' : Array U32 17#usize)
    (h n dst base : Nat) : Prop where
  lengths : ∀ k, len'.val[k]!.val = if k=h then 0 else if k=h+1 then len.val[k]!.val+n else len.val[k]!.val
  cursor : ∀ k, cur'.val[k]!.val = if k=h+1 then cur.val[k]!.val+n else cur.val[k]!.val
  cells : ∀ k j, bytes out.val[k]!.val[j]!.val =
    if k=h+1 ∧ dst≤j ∧ j<dst+n then parentBytes p seed tree buf h base (j-dst)
    else bytes buf.val[k]!.val[j]!.val

private theorem readSet {α} [Inhabited α] {K : Usize} (a : Array α K) (i : Usize) (v : α)
    (bound : i.val<K.val) (j : Nat) : (a.set i v).val[j]! = if j=i.val then v else a.val[j]! := by
  rw [Array.set_val_eq]
  by_cases e : j=i.val
  · subst j; rw [setSame _ _ _ (by simpa using bound),if_pos rfl]
  · rw [setOther _ _ _ _ (Ne.symm e),if_neg e]

private theorem lengthFrame (len : Array Usize 17#usize) (h upper after : Usize) (n : Nat)
    (hi : h.val<16) (up : upper.val=h.val+1) (v : after.val=len.val[upper.val]!.val+n) (k : Nat) :
    ((len.set upper after).set h 0#usize).val[k]!.val =
    if k=h.val then 0 else if k=h.val+1 then len.val[k]!.val+n else len.val[k]!.val := by
  rw [readSet _ _ _ (by change h.val<17;omega)]
  by_cases e : k=h.val
  · simp [e]
  · simp only [if_neg e]
    rw [readSet _ _ _ (by change upper.val<17;omega)]
    by_cases f : k=upper.val
    · subst k; simp [up,v]
    · simp [f,show k≠h.val+1 by omega]

private theorem cursorFrame (cur : Array U32 17#usize) (h upper : Usize) (after : U32) (n : Nat)
    (hi : h.val<16) (up : upper.val=h.val+1) (v : after.val=cur.val[upper.val]!.val+n) (k : Nat) :
    (cur.set upper after).val[k]!.val =
    if k=h.val+1 then cur.val[k]!.val+n else cur.val[k]!.val := by
  rw [readSet _ _ _ (by change upper.val<17;omega)]
  by_cases f : k=upper.val
  · subst k; simp [up,v]
  · simp [f,show k≠h.val+1 by omega]

variable [kernel : Kernel]
theorem flush_transfer {N : Usize} (p : params.Params) (hp : PN p N) (seed : Array U8 N)
    (tree : address.Adrs) (it : core.ops.range.Range Usize) (buf : Stack N)
    (len : Array Usize 17#usize) (cur : Array U32 17#usize) (addrs : Array address.Adrs 8#usize)
    (left right : Rows8 N) (n dst base : Nat)
    (more : it.start.val < it.end.val) (hi : it.start.val<16)
    (child : len.val[it.start.val]!.val=2*n) (dest : len.val[it.start.val+1]!.val=dst)
    (index : cur.val[it.start.val+1]!.val=base) (live : n≤8) (fit : dst+n≤16)
    (words : base+n<2^32) (perm : ActiveCorrect (machine kernel) kernel.active) :
    subtree_loop3.body seed tree it buf len cur addrs left right ⦃ res => match res with
      | .done _ => False
      | .cont (next,out,len',cur',_,_,_) => next.start.val=it.start.val+1 ∧ next.end=it.end ∧
        FlushFacts p seed tree buf out len len' cur cur' it.start.val n dst base ⦄ := by
  unfold subtree_loop3.body
  step with core.iter.range.IteratorRange.next_Usize_some_spec it more as ⟨_,next,tag,inc,last⟩
  simp only [tag]
  step as ⟨num,read⟩
  rw [←getElem!_pos] at read
  step as ⟨count,cv⟩
  have cn : count.val=n := by rw [cv,read,child]; change 2*n/2=n; omega
  split
  · rename_i zero
    have n0 : n=0 := by rw [←cn,zero];rfl
    rw [n0] at child ⊢
    simp only [step_simps]
    refine ⟨inc,last,⟨?_,?_,?_⟩⟩
    · intro k; split
      · rename_i same;rw [same];exact child
      · split <;> rfl
    · intro k; simp
    · intro k j; simp only [Nat.add_zero];split <;> first | rfl | omega
  · step as ⟨upper,up⟩
    step as ⟨b,bv⟩
    rw [←getElem!_pos] at bv
    have id : b.val=base := by rw [bv,up,index]
    simp only [lift,bind_ok]
    have level : (UScalar.cast .U32 upper).val=upper.val := UScalar.cast_val_mod_pow_of_inBounds_eq _ _ (by change _ < 2^32;omega)
    split
    · rename_i single
      have n1 : n=1 := by rw [←cn,single];rfl
      rw [n1] at child fit words ⊢
      step as ⟨adr,aw⟩
      step as ⟨parent,pw⟩
      step as ⟨row,rv⟩
      step as ⟨l,lv⟩
      step as ⟨r,rr⟩
      step with Shake.pair_spec seed parent l r as ⟨value,hash⟩
      step as ⟨pos,pv⟩
      rw [←getElem!_pos] at pv
      have posval : pos.val=dst := by rw [pv,up,dest]
      step as ⟨old,restore,get,save⟩
      step as ⟨output,put⟩
      step as ⟨stop,sv⟩
      step as ⟨newLen,ln⟩
      step as ⟨after,av⟩
      step as ⟨newCur,cu⟩
      step as ⟨zeroed,zr⟩
      try simp only [step_simps]
      refine ⟨inc,last,⟨?_,?_,?_⟩⟩
      · rw [zr,ln];exact lengthFrame len it.start upper stop 1 hi up (by rw [sv,pv]) 
      · rw [cu];exact cursorFrame cur it.start upper after 1 hi up (by rw [av,bv])
      · have val : bytes value.val = parentBytes p seed tree buf it.start.val base 0 := by
          rw [lv,rr,←getElem!_pos,←getElem!_pos,rv,←getElem!_pos,pw,aw] at hash
          simp only [parentBytes,Spec.H,Shake.params,paramsS_n,hp.n_eq,List.append_assoc,Nat.add_zero,Nat.mul_zero]
          simpa [adrsS,level,up,id,List.append_assoc] using hash
        intro k j
        rw [save,readSet _ _ _ (by change upper.val<17;omega)]
        by_cases same : k=upper.val
        · subst k; rw [if_pos rfl,put,readSet _ _ _ (by change pos.val<16;omega)]
          by_cases hit : j=pos.val
          · subst j; simp [up,posval,val]
          · rw [if_neg hit,if_neg (by omega),get,←getElem!_pos]
        · rw [if_neg same,if_neg (by omega)]
    · step as ⟨row,rv⟩
      rw [←getElem!_pos] at rv
      step with flush_gather count tree addrs left right b (UScalar.cast .U32 upper) row (by omega) (by omega) as ⟨a,l,r,g⟩
      step with hashed_gather p hp seed tree count b (UScalar.cast .U32 upper) row a l r (by omega) g perm as ⟨parents,hash⟩
      step as ⟨u,uv⟩
      step as ⟨pos,pv⟩
      rw [←getElem!_pos] at pv
      have posval : pos.val=dst := by rw [pv,uv,dest]
      step as ⟨old,restore,get,save⟩
      step as ⟨stop,sv⟩
      step as ⟨part,put,_,plen,write⟩
      step as ⟨s,take,taken⟩
      · simpa using cn ▸ live
      step as ⟨out,copy⟩
      · omega
      step as ⟨newLen,ln⟩
      try simp only [lift,bind_ok]
      have cast : (UScalar.cast .U32 count).val=count.val := UScalar.cast_val_mod_pow_of_inBounds_eq _ _ (by change _ < 2^32;omega)
      step as ⟨after,av⟩
      step as ⟨newCur,cu⟩
      step as ⟨zeroed,zr⟩
      try simp only [step_simps]
      refine ⟨inc,last,⟨?_,?_,?_⟩⟩
      · rw [zr,ln];exact lengthFrame len it.start u stop n hi uv (by rw [sv,pv,cn])
      · rw [cu];exact cursorFrame cur it.start u after n hi uv (by rw [av,bv,up,uv,cast,cn])
      · rw [save]
        have cells := stored_cells buf u pos.val n parents (put out) (by omega) (by omega) live (by
          rw [write,copy,take,get,←getElem!_pos];simp only [List.slice,Array.val_to_slice,List.drop_zero,Nat.sub_zero,cn];with_unfolding_all rfl)
        intro k j
        rw [cells k j]
        by_cases hit : k=it.start.val+1 ∧ dst≤j ∧ j<dst+n
        · rw [if_pos hit,if_pos (by simpa [uv,posval] using hit)]
          have eq := hash (j-dst) (by omega)
          simp only [parentBytes,level,up,id,rv,posval] at eq ⊢
          with_unfolding_all exact eq
        · rw [if_neg hit,if_neg (by simpa [uv,posval] using hit)]
end slhdsa.Buffered
