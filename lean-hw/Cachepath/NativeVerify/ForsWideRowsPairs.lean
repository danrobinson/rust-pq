import Cachepath.NativeVerify.ForsWideRowsStore
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.NativeVerify.ForsWideRows
open ShakeBatch
set_option maxHeartbeats 1600000
set_option linter.concreteInstances false

def PairsAt {N : Usize} (tree : address.Adrs) (level : U32) (indices : Slice U32) (children : Slice (Array U8 N))
    (i n : Nat) (as' : Array address.Adrs 8#usize) (ls rs : Array (Array U8 N) 8#usize) :=
  ∀ j < n, adrsS as'.val[j]! = {adrsS tree with word2:=level.val,word3:=indices.val[i+j]!.val} ∧
    ls.val[j]! = children.val[2*(i+j)]! ∧ rs.val[j]! = children.val[2*(i+j)+1]!

theorem gather {N : Usize} (tree : address.Adrs) (level : U32) (indices : Slice U32) (children : Slice (Array U8 N))
    (i active : Usize) (as' : Array address.Adrs 8#usize) (ls rs : Array (Array U8 N) 8#usize)
    (live : active.val ≤ 8) (fit : i.val+active.val ≤ indices.length) (size : 2*indices.length ≤ children.length) :
    pairs_loop0_loop0 ⟨0#usize,active⟩ tree level indices children as' ls rs i ⦃ a l r =>
      PairsAt tree level indices children i.val active.val a l r ⦄ := by
  unfold pairs_loop0_loop0
  have limit := children.property
  apply loop.spec_decr_nat (measure := fun q : core.ops.range.Range Usize × Array address.Adrs 8#usize ×
    Array (Array U8 N) 8#usize × Array (Array U8 N) 8#usize => active.val-q.1.start.val)
    (inv := fun q => q.1.end=active ∧ q.1.start.val ≤ active.val ∧ PairsAt tree level indices children i.val q.1.start.val q.2.1 q.2.2.1 q.2.2.2)
  · rintro ⟨it,adds,ll,rr⟩ ⟨stop,le,prior⟩
    simp only at stop le prior ⊢
    unfold pairs_loop0_loop0.body
    by_cases more : it.start.val < active.val
    · step with core.iter.range.IteratorRange.next_Usize_some_spec it (by rw [stop];exact more) as ⟨_,next,tag,inc,ends⟩
      simp only [tag]
      step as ⟨adr,levelEq⟩
      step as ⟨pos,pv⟩
      step as ⟨id,idv⟩
      step as ⟨parent,iv⟩
      step as ⟨newA,wa⟩
      step as ⟨j,jv⟩
      step as ⟨l,lv⟩
      step as ⟨newL,wl⟩
      step as ⟨k,kv⟩
      step as ⟨t,tv⟩
      step as ⟨r,rv⟩
      step as ⟨newR,wr⟩
      refine ⟨ends.trans stop,by omega,?_,by omega⟩
      intro u hu
      rw [wa,wl,wr,Array.set_val_eq,Array.set_val_eq,Array.set_val_eq]
      by_cases same : u=it.start.val
      · subst u
        rw [setSame _ _ _ (by simp;omega),setSame _ _ _ (by simp;omega),setSame _ _ _ (by simp;omega),
          iv,levelEq,idv,lv,rv,←getElem!_pos,←getElem!_pos,←getElem!_pos]
        simp only [adrsS,pv,jv,kv,tv]
        exact ⟨True.intro,True.intro,True.intro⟩
      · rw [setOther _ _ _ _ (Ne.symm same),setOther _ _ _ _ (Ne.symm same),setOther _ _ _ _ (Ne.symm same)]
        exact prior u (by omega)
    · step with core.iter.range.IteratorRange.next_Usize_none_spec it (by rw [stop];omega) as ⟨_,_,tag,_⟩
      simp only [tag,step_simps]
      exact (show it.start.val=active.val by omega) ▸ prior
  · exact ⟨rfl,Nat.zero_le _,by intro l hl;change l < 0 at hl;omega⟩

def parentRow {N : Usize} (p : params.Params) (seed : Array U8 N) (tree : address.Adrs) (level : U32)
    (indices : Slice U32) (children : Slice (Array U8 N)) (i : Nat) :=
  Spec.H (Shake.params p) (bytes seed.val) {adrsS tree with word2:=level.val,word3:=indices.val[i]!.val}
    (bytes children.val[2*i]!.val ++ bytes children.val[2*i+1]!.val)

variable [kernel : Fused.Kernel]
local instance rowsPairsMachine : Machine := Fused.machine kernel

theorem pairs_spec {N : Usize} (p : params.Params) (hp : PN p N) (seed : Array U8 N) (tree : address.Adrs)
    (level : U32) (indices : Slice U32) (children out : Slice (Array U8 N)) (length : out.length=indices.length)
    (enough : 2*indices.length ≤ children.length) (perm : ActiveCorrect (Fused.machine kernel) kernel.active) :
    pairs seed tree level indices children out ⦃ result => Filled (parentRow p seed tree level indices children)
      indices.length indices.length result ⦄ := by
  let target := parentRow p seed tree level indices children
  unfold pairs pairs_loop0
  apply loop.spec_decr_nat (measure := fun q : Slice (Array U8 N) × Array address.Adrs 8#usize ×
    Array (Array U8 N) 8#usize × Array (Array U8 N) 8#usize × Usize => indices.length-q.2.2.2.2.val)
    (inv := fun q => q.2.2.2.2.val ≤ indices.length ∧ Filled target indices.length q.2.2.2.2.val q.1)
  · rintro ⟨buf,adds,ll,rr,i⟩ ⟨inside,old⟩
    simp only at inside old ⊢
    unfold pairs_loop0.body
    dsimp only
    split
    · rename_i more
      have shorter : i.val < indices.length := more
      step as ⟨left,leftVal⟩
      simp only [lift,bind_ok]
      let active := core.cmp.impls.OrdUsize.min left 8#usize
      have count : active.val=min (indices.length-i.val) 8 := (min_count _).trans (by rw [leftVal];rfl)
      have size : active.val ≤ 8 := by omega
      have inc : 0 < active.val := by omega
      have fit : i.val+active.val ≤ indices.length := by omega
      step with gather tree level indices children i active adds ll rr size fit enough as ⟨aa,ls,rs,g⟩
      step with @ActiveHash.pair_fips (Fused.machine kernel) kernel.active N seed aa ls rs active size perm
        hp.le32 (aligned_hash hp) as ⟨rows,hashed⟩
      have vals (j : Nat) (hj : j < active.val) : bytes rows.val[j]!.val=target (i.val+j) := by
        obtain ⟨adr,l,r⟩ := g j hj
        have hash := hashed j hj
        rw [adr,l,r] at hash
        simp only [target,parentRow,Spec.H,Shake.params,paramsS_n,hp.n_eq,List.append_assoc] at hash ⊢
        with_unfolding_all exact hash
      step as ⟨stop,sv⟩
      change stop.val=i.val+active.val at sv
      erw [←writeBind buf i stop active rows (fun buf' => ok (cont (buf',aa,ls,rs,stop)))]
      step with write_rows buf i stop active rows target indices.length old sv (by omega) size vals as ⟨result,updated⟩
      exact ⟨by omega,updated,by omega⟩
    · rename_i stop
      simp only [step_simps]
      exact (show i.val=indices.length by change ¬ i.val < indices.length at stop;omega) ▸ old
  · exact ⟨Nat.zero_le _,length,by intro j hj;change j < 0 at hj;omega⟩
end slhdsa.NativeVerify.ForsWideRows
