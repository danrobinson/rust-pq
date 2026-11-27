import Parallel.RootTableProgram
import Parallel.TicketLayers
import Shakebatch.Range
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.ParallelRootWalk
open ParallelSigning ParallelFused ParallelXmssTicket
set_option maxHeartbeats 1600000
set_option linter.concreteInstances false
variable [engine : Engine]

def PublishedLeaves {N : Usize} (P : Spec.Params) (sk pk : Spec.Bytes) (tree leaf : Nat)
    (count : Nat) (leaves : alloc.vec.Vec (Option (Array U8 N))) :=
  count≤leaves.length ∧ ∀ j<count, ∃ row, leaves.val[j]! = some row ∧
    bytes row.val=Spec.xmssNode P sk (loc P.hp tree leaf j).2 0 pk (addr j (loc P.hp tree leaf j).1)

def PublishedAuth {N : Usize} (P : Spec.Params) (sk pk : Spec.Bytes) (tree leaf count : Nat)
    (auth : alloc.vec.Vec (Array U8 N)) :=
  count*P.hp≤auth.length ∧ ∀ j<count, ∀ h<P.hp, bytes auth.val[j*P.hp+h]!.val =
    Spec.xmssNode P sk (((loc P.hp tree leaf j).2/2^h)^^^1) h pk (addr j (loc P.hp tree leaf j).1)

def Roots {N : Usize} (expected : Nat → Spec.Bytes) (count : Nat) (r : alloc.vec.Vec (Array U8 N)) :=
  r.length=count ∧ ∀ j<count, bytes r.val[j]!.val=expected j

theorem table_spec {N : Usize} (p : params.Params) (hp : PN p N) (d width : Usize)
    (sig : alloc.vec.Vec U8) (md : Slice U8) (seed : Array U8 N) (a : address.Adrs)
    (layers : Layers) (leaves : alloc.vec.Vec (Option (Array U8 N))) (count : Usize)
    (auth : alloc.vec.Vec (Array U8 N)) (sk : Spec.Bytes) (tree leaf : Nat)
    (shape : width.val=p.hp.val) (num : count.val+1=p.d.val) (leafBound : leaf<2^p.hp.val)
    (layout : LayerTable p.hp.val tree leaf p.d.val layers)
    (live : PublishedLeaves (Shake.params p) sk (bytes seed.val) tree leaf count.val leaves)
    (siblings : PublishedAuth (Shake.params p) sk (bytes seed.val) tree leaf count.val auth)
    (hash : HashLaw (Shake.params p) (@Engine.hash engine N))
    (first : engine.recover p sig.deref md seed a ⦃ row => bytes row.val=
      Spec.forsPkFromSig (Shake.params p) (bytes sig.val) (bytes md.val) (bytes seed.val) (adrsS a) ⦄) :
    all_roots p d width sig md seed a layers leaves count auth ⦃ out => Roots
      (message (Shake.params p) (Spec.forsPkFromSig (Shake.params p) (bytes sig.val) (bytes md.val)
        (bytes seed.val) (adrsS a)) sk (bytes seed.val) tree leaf) p.d.val out ⦄ := by
  let P := Shake.params p
  let expect := message P (Spec.forsPkFromSig P (bytes sig.val) (bytes md.val) (bytes seed.val) (adrsS a))
    sk (bytes seed.val) tree leaf
  unfold all_roots
  step with first as ⟨start,base⟩
  step with alloc.vec.Vec.push_spec (alloc.vec.Vec.with_capacity (Array U8 N) d) start (by change 0<Usize.max;scalar_tac) as ⟨init,pushed⟩
  unfold all_roots_loop0
  rw [←num]
  apply ShakeBatch.range_fold (all_roots_loop0.body p width seed layers leaves auth) count init (fun k r => Roots expect (k+1) r)
  · have initVal : init.val=[start] := pushed
    refine ⟨by change init.val.length=_;rw [initVal];rfl,?_⟩
    intro j hj
    obtain rfl : j=0 := by omega
    simpa [initVal,expect,message,P] using base
  · intro it roots stop more prior
    have within : it.start.val<p.d.val := by omega
    have hl := layout.1
    have pos := layout.2 _ within
    have keys := live.1
    obtain ⟨key,there,keyBytes⟩ := live.2 _ more
    have room := (Nat.mul_le_mul_right width.val more)
    have slots := siblings.1
    change count.val*p.hp.val≤auth.length at slots
    have enough : (it.start.val+1)*width.val≤auth.length := room.trans (shape ▸ slots)
    unfold all_roots_loop0.body
    step with core.iter.range.IteratorRange.next_Usize_some_spec it (by rw [stop];exact more) as ⟨_,next,tag,inc,ends⟩
    simp only [tag]
    step as ⟨addr,index,read⟩
    step as ⟨treeAddr,_,ad⟩
    step as ⟨ol,get⟩
    all_goals try scalar_tac
    rw [←getElem!_pos] at read get
    simp only [ParallelSignJoin.readCell,bind_ok,get,there,core.option.Option.expect,ofOption]
    let locAt := loc p.hp.val tree leaf it.start.val
    have ai : adrsS addr=ParallelSigning.addr it.start.val locAt.1 := by simpa [←read] using congrArg Prod.fst pos
    have ii : index.val=locAt.2 := by simpa [←read] using congrArg Prod.snd pos
    have domain : adrsS treeAddr=(ParallelSigning.addr it.start.val locAt.1).setTypeAndClear Spec.TREE := by
      rw [←ai];simp [ad,adrsS,Spec.Adrs.setTypeAndClear,Spec.TREE,address.TREE]
    have indexBound : index.val<2^P.hp := by
      rw [ii]; dsimp [locAt,P];cases it.start.val with
      | zero => exact leafBound
      | succ j => exact Nat.mod_lt _ (Nat.two_pow_pos _)
    have root := root_spec p P rfl engine.hash hash it.start width shape _ treeAddr domain index key auth seed
      enough sk indexBound (by simpa only [ii,locAt,P,Shake.params,paramsS_hp] using keyBytes) (fun h hh => by simpa only [ii,locAt,P,Shake.params,paramsS_hp] using siblings.2 _ more h hh)
    change all_roots_loop0_loop0 ⟨0#u32,p.hp⟩ width seed auth it.start treeAddr key index ⦃ _ ⦄ at root
    step with root as ⟨node,nodeEq⟩
    have len : roots.val.length=it.start.val+1 := prior.1
    step with alloc.vec.Vec.push_spec roots node (by scalar_tac) as ⟨out,saved⟩
    refine ⟨next,out,rfl,ends.trans stop,inc,?_,?_⟩
    · change out.val.length=_
      simp only [saved,List.length_append,List.length_cons,List.length_nil,len,inc]
    · intro j hj
      rw [saved]
      by_cases previous : j<roots.val.length
      · rw [List.getElem!_append_left _ _ _ previous]
        exact prior.2 _ (len ▸ previous)
      · have eq : j=roots.val.length := by omega
        subst j
        simpa [len,expect,message,P,locAt,Shake.params,paramsS_hp] using nodeEq
  · intro it roots atEnd stop
    obtain ⟨⟨_,_⟩,run,tag,_⟩ := spec_imp_exists (core.iter.range.IteratorRange.next_Usize_none_spec it (by rw [stop];omega))
    simp only [all_roots_loop0.body,run,bind_ok,tag];rfl
end slhdsa.ParallelRootWalk
