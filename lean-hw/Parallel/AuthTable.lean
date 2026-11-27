import Parallel.AuthTableRow
import Parallel.RootTable
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.ParallelAuthTable
open ParallelSigning ShakeBatch
set_option maxHeartbeats 1000000

deriving instance Inhabited for XmssAuthMeta

abbrev Slots (N : Usize) := alloc.vec.Vec (Option (Array U8 N))
abbrev Values (N : Usize) := alloc.vec.Vec (Array U8 N)

def Prefix {N : Usize} (f : Nat → Spec.Bytes) (n : Nat) (rows : Values N) :=
  rows.length=n ∧ ∀ k<n, bytes rows.val[k]!.val=f k

private theorem extend_prefix {N : Usize} (f : Nat → Spec.Bytes) (n : Nat) (rows out : Values N) (row : Array U8 N)
    (old : Prefix f n rows) (append : out.val=rows.val++[row]) (value : bytes row.val=f n) : Prefix f (n+1) out := by
  have len : rows.val.length=n := old.1
  refine ⟨by change out.val.length=_;simp [append,len],?_⟩
  intro k hk
  by_cases last : k=n
  · subst k;rw [append,←len];simpa [len] using value
  · have inside : k<rows.val.length := by omega
    rw [append, getElem!_pos _ _ (by simp;omega),List.getElem_append_left inside,←getElem!_pos]
    exact old.2 _ (by omega)

structure Inputs {N : Usize} (p : params.Params) (sk : Spec.Bytes) (seed : Array U8 N) (d width : Usize)
    (layers : alloc.vec.Vec (address.Adrs × U32)) (metadata : alloc.vec.Vec XmssAuthMeta)
    (slots : Slots N) (base : Nat → Spec.Adrs) (f : Nat → Spec.Bytes) : Prop where
  layersFit : d.val≤layers.length
  metadataFit : d.val*width.val≤metadata.length
  layersAt : ∀ j<d.val, adrsS layers.val[j]!.1=base j
  chunks : ∀ j<d.val, ∀ h<width.val, Chunks p sk seed (base j) metadata.val[j*width.val+h]! slots
  node : ∀ j<d.val, ∀ h<width.val,
    let m := metadata.val[j*width.val+h]!
    Spec.xmssNode (Shake.params p) sk m.root_idx.val m.height.val (bytes seed.val) (base j)=f (j*width.val+h)

private theorem inner {N : Usize} (p : params.Params) (hp : PN p N) (sk : Spec.Bytes) (seed : Array U8 N)
    (d width : Usize) (layers : alloc.vec.Vec (address.Adrs × U32)) (metadata : alloc.vec.Vec XmssAuthMeta)
    (slots : Slots N) (base : Nat → Spec.Adrs) (f : Nat → Spec.Bytes)
    (inputs : Inputs p sk seed d width layers metadata slots base f) (j : Usize) (live : j.val<d.val)
    (a : address.Adrs) (tag : adrsS a=(base j.val).setTypeAndClear Spec.TREE) (rows : Values N)
    (prior : Prefix f (j.val*width.val) rows) :
    auth_table_loop0_loop0 ⟨0#usize,width⟩ width metadata slots seed rows j a ⦃ out => Prefix f ((j.val+1)*width.val) out ⦄ := by
  unfold auth_table_loop0_loop0
  rw [Nat.succ_mul]
  apply range_fold (auth_table_loop0_loop0.body width metadata slots seed j a) width rows
    (fun h => Prefix f (j.val*width.val+h)) (by simpa using prior)
  · intro it cur stop more ready
    have total := inputs.metadataFit
    have cap : metadata.length≤Usize.max := by scalar_tac
    have nextPos := Nat.mul_le_mul_right width.val live
    rw [Nat.succ_mul] at nextPos
    have within : j.val*width.val+it.start.val < metadata.length := by omega
    unfold auth_table_loop0_loop0.body
    step with core.iter.range.IteratorRange.next_Usize_some_spec it (by simpa [stop] using more) as ⟨_,next,tagNext,inc,ends⟩
    simp only [tagNext]
    step as ⟨offset,ov⟩
    step as ⟨index,iv⟩
    step as ⟨m,get⟩
    rw [←getElem!_pos,iv,ov] at get
    step with read_spec p hp sk seed _ a tag m slots (get ▸ inputs.chunks j.val live it.start.val more) as ⟨v,val⟩
    have len := ready.1
    step with alloc.vec.Vec.push_spec cur v (by scalar_tac) as ⟨out,app⟩
    refine ⟨next,out,rfl,ends.trans stop,inc,?_⟩
    rw [inc,←Nat.add_assoc]
    exact extend_prefix f _ cur out v ready app (val.trans (get ▸ inputs.node j.val live it.start.val more))
  · intro it cur last stop
    obtain ⟨next,no⟩ := ForsDriver.range_done it _ stop last
    simp [auth_table_loop0_loop0.body,no]

theorem table_spec {N : Usize} (p : params.Params) (hp : PN p N) (sk : Spec.Bytes) (seed : Array U8 N)
    (d width : Usize) (layers : alloc.vec.Vec (address.Adrs × U32)) (metadata : alloc.vec.Vec XmssAuthMeta)
    (slots : Slots N) (base : Nat → Spec.Adrs) (f : Nat → Spec.Bytes) (inputs : Inputs p sk seed d width layers metadata slots base f) :
    auth_table d width layers metadata slots seed ⦃ out => Prefix f (d.val*width.val) out ⦄ := by
  have cap : metadata.length≤Usize.max := by scalar_tac
  have fit := inputs.metadataFit
  unfold auth_table
  step as ⟨n,nv⟩
  unfold auth_table_loop0
  apply range_fold (auth_table_loop0.body width layers metadata slots seed) d _
    (fun j => Prefix f (j*width.val)) (by constructor <;> simp [alloc.vec.Vec.with_capacity])
  · intro it cur stop more ready
    have count := inputs.layersFit
    unfold auth_table_loop0.body
    step with core.iter.range.IteratorRange.next_Usize_some_spec it (by simpa [stop] using more) as ⟨_,next,tagNext,inc,ends⟩
    simp only [tagNext]
    step as ⟨addr,index,read⟩
    rw [←getElem!_pos] at read
    have loc : adrsS addr=base it.start.val := by rw [←inputs.layersAt _ more,←read]
    step as ⟨a,typ,addrEq⟩
    have tag : adrsS a=(base it.start.val).setTypeAndClear Spec.TREE := by
      simp [←loc,addrEq,adrsS,Spec.Adrs.setTypeAndClear,Spec.TREE,address.TREE]
    step with inner p hp sk seed d width layers metadata slots base f inputs it.start more a tag cur ready as ⟨out,result⟩
    exact ⟨next,out,rfl,ends.trans stop,inc,inc ▸ result⟩
  · intro it cur last stop
    obtain ⟨next,no⟩ := ForsDriver.range_done it _ stop last
    simp [auth_table_loop0.body,no]

/-- The finished physical authentication vector used by the layer-root computation. -/
theorem published_auth {N : Usize} (p : params.Params) (hp : PN p N) (sk : Spec.Bytes) (seed : Array U8 N)
    (tree leaf : Nat) (d width : Usize) (layers : alloc.vec.Vec (address.Adrs × U32)) (metadata : alloc.vec.Vec XmssAuthMeta)
    (slots : Slots N) (height : width.val=(Shake.params p).hp)
    (layout : ParallelXmssTicket.LayerTable width.val tree leaf d.val layers) (fit : d.val*width.val≤metadata.length)
    (fields : ∀ j<d.val, ∀ h<width.val,
      let m := metadata.val[j*width.val+h]!
      m.root_idx.val=ParallelXmssTicket.root (loc width.val tree leaf j).2 h ∧ m.height.val=h ∧
      Chunks p sk seed (addr j (loc width.val tree leaf j).1) m slots) :
    auth_table d width layers metadata slots seed ⦃ out =>
      ParallelRootWalk.PublishedAuth (Shake.params p) sk (bytes seed.val) tree leaf d.val out ⦄ := by
  let f := fun (q : Nat) =>
    let j := q/width.val
    let h := q%width.val
    Spec.xmssNode (Shake.params p) sk (ParallelXmssTicket.root (loc width.val tree leaf j).2 h)
      h (bytes seed.val) (addr j (loc width.val tree leaf j).1)
  have decode (j h : Nat) (inner : h<width.val) : (j*width.val+h)/width.val=j ∧ (j*width.val+h)%width.val=h := by
    have pos : 0<width.val := by omega
    constructor
    · rw [Nat.add_comm,Nat.add_mul_div_right _ _ pos,Nat.div_eq_of_lt inner,Nat.zero_add]
    · simp [Nat.add_mod,Nat.mod_eq_of_lt inner]
  have options : Inputs p sk seed d width layers metadata slots (fun j => addr j (loc width.val tree leaf j).1) f :=
    ⟨layout.1.ge,fit,fun j live => congrArg Prod.fst (layout.2 j live),fun j live h sub => (fields j live h sub).2.2,by
      intro j live h sub
      obtain ⟨root,depth,_⟩ := fields j live h sub
      simp only [f,(decode j h sub).1,(decode j h sub).2,root,depth]⟩
  apply WP.spec_mono (table_spec p hp sk seed d width layers metadata slots _ f options)
  intro out finished
  unfold ParallelRootWalk.PublishedAuth
  rw [←height]
  refine ⟨finished.1.ge,?_⟩
  intro j live h sub
  have room := Nat.mul_le_mul_right width.val live
  rw [Nat.succ_mul] at room
  have got := finished.2 (j*width.val+h) (by omega)
  simpa only [f,(decode j h sub).1,(decode j h sub).2,ParallelXmssTicket.root] using got

end slhdsa.ParallelAuthTable
