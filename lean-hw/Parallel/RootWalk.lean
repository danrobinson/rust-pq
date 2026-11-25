import Parallel.RootWalkProgram
import Parallel.SigningSlots
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.ParallelRootWalk
open ParallelFused.Slots
set_option maxHeartbeats 1500000

def HashLaw {N : Usize} (P : Spec.Params) (hash : Hash N) :=
  ∀ seed a left right, hash seed a left right ⦃ out =>
    bytes out.val=Spec.H P (bytes seed.val) (adrsS a) (bytes left.val++bytes right.val) ⦄

theorem walk_spec {N : Usize} (p : params.Params) (P : Spec.Params) (hhp : P.hp=p.hp.val)
    (hash : Hash N) (law : HashLaw P hash) (j hp : Usize) (height : hp.val=p.hp.val)
    (a : Spec.Adrs) (treeAddr : address.Adrs) (domain : adrsS treeAddr=a.setTypeAndClear Spec.TREE)
    (idx : U32) (leaf : Array U8 N) (auth : alloc.vec.Vec (Array U8 N)) (seed : Array U8 N)
    (room : (j.val+1)*hp.val≤auth.length) :
    root_walk hash p j hp treeAddr idx leaf auth seed ⦃ r => bytes r.val =
      (climb P (bytes seed.val) a j.val (fun k => bytes auth.val[k]!.val) (bytes leaf.val) idx.val p.hp.val).1 ⦄ := by
  let run := climb P (bytes seed.val) a j.val (fun k => bytes auth.val[k]!.val) (bytes leaf.val) idx.val
  unfold root_walk root_walk_loop
  apply loop.spec_decr_nat (measure := fun q : core.ops.range.Range U32 × Array U8 N × U32 => p.hp.val-q.1.start.val)
    (inv := fun q => q.1.end=p.hp ∧ q.1.start.val≤p.hp.val ∧ (bytes q.2.1.val,q.2.2.val)=run q.1.start.val)
  · rintro ⟨it,node,i⟩ ⟨endAt,bound,prior⟩
    simp only at endAt bound prior ⊢
    unfold root_walk_loop.body
    by_cases more : it.start.val < p.hp.val
    · step with core.iter.range.IteratorRange.next_U32_some_spec it (by rw [endAt];exact more) as ⟨_,next,tag,inc,ends⟩
      simp only [tag]
      have cast : (UScalar.cast .Usize it.start).val=it.start.val := by scalar_tac
      have cap : auth.length≤Usize.max := by simp
      rw [Nat.add_mul,Nat.one_mul] at room
      step as ⟨base,bv⟩
      simp only [lift,bind_ok]
      step as ⟨pos,pv⟩
      step as ⟨sibling,sibEq⟩
      step as ⟨parent,parentEq,_⟩
      step as ⟨level,lv⟩
      step as ⟨first,fv⟩
      step as ⟨addr,av⟩
      all_goals try scalar_tac
      have par : parent.val=i.val/2 := by rw [parentEq];simp [Nat.shiftRight_eq_div_pow]
      have adr : adrsS addr={a.setTypeAndClear Spec.TREE with word2:=it.start.val+1,word3:=i.val/2} := by
        simp [av,fv,adrsS,lv,par,←domain]
      have s : sibling=auth.val[j.val*P.hp+it.start.val]! := by
        rw [←getElem!_pos] at sibEq
        simpa only [pv,bv,cast,height,hhp] using sibEq
      have bit : (i &&& 1#u32).val=i.val%2 := by simp [UScalar.val_and,Nat.and_one_is_mod]
      try simp only [lift,bind_ok]
      by_cases even : i.val%2=0
      · have test : i &&& 1#u32=0#u32 := UScalar.eq_of_val_eq (bit.trans even)
        simp only [test,ite_true]
        step with law seed addr node sibling as ⟨out,hashed⟩
        refine ⟨ends.trans endAt,by omega,?_,by omega⟩
        simp only [inc,run,climb_succ,←prior,even,ite_true,hashed,adr,s,par]
      · have test : i &&& 1#u32≠0#u32 := by intro eq;rw [eq] at bit;exact even bit.symm
        simp only [test,ite_false]
        step with law seed addr sibling node as ⟨out,hashed⟩
        refine ⟨ends.trans endAt,by omega,?_,by omega⟩
        simp only [inc,run,climb_succ,←prior,even,ite_false,hashed,adr,s,par]
    · step with core.iter.range.IteratorRange.next_U32_none_spec it (by rw [endAt];omega) as ⟨_,_,tag,_⟩
      simp only [tag,step_simps]
      exact (show it.start.val=p.hp.val by omega) ▸ congrArg Prod.fst prior
  · exact ⟨rfl,by simp,rfl⟩

theorem root_spec {N : Usize} (p : params.Params) (P : Spec.Params) (hhp : P.hp=p.hp.val)
    (hash : Hash N) (law : HashLaw P hash) (j hp : Usize) (height : hp.val=p.hp.val)
    (a : Spec.Adrs) (treeAddr : address.Adrs) (domain : adrsS treeAddr=a.setTypeAndClear Spec.TREE)
    (idx : U32) (leaf : Array U8 N) (auth : alloc.vec.Vec (Array U8 N)) (seed : Array U8 N)
    (room : (j.val+1)*hp.val≤auth.length) (sk : Spec.Bytes) (bounded : idx.val<2^P.hp)
    (base : bytes leaf.val=Spec.xmssNode P sk idx.val 0 (bytes seed.val) a)
    (siblings : ∀ h<P.hp, bytes auth.val[j.val*P.hp+h]!.val=
      Spec.xmssNode P sk ((idx.val/2^h)^^^1) h (bytes seed.val) a) :
    root_walk hash p j hp treeAddr idx leaf auth seed ⦃ r =>
      bytes r.val=Spec.xmssNode P sk 0 P.hp (bytes seed.val) a ⦄ := by
  apply WP.spec_mono (walk_spec p P hhp hash law j hp height a treeAddr domain idx leaf auth seed room)
  intro r hr
  rw [←hhp,climbed P sk (bytes seed.val) a j.val idx.val _ _ base siblings P.hp (by omega),
    Nat.div_eq_of_lt bounded] at hr
  exact hr

abbrev shake_root {N : Usize} (p : params.Params) (hp : PN p N) :=
  @root_spec N p (Shake.params p) rfl (@shake.xmss.hash2 N) (Shake.hash2_spec p hp)

end slhdsa.ParallelRootWalk
