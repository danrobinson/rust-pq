import Parallel.AuthTableProgram
import Parallel.XmssPlan
open Aeneas Aeneas.Std Result
namespace slhdsa.ParallelAuthTable
set_option maxHeartbeats 1000000
open ParallelReduceNative

theorem address_clear (p : Spec.Params) (sk pk : Spec.Bytes) (a : Spec.Adrs) (i h : Nat) :
    Spec.xmssNode p sk i h pk (a.setTypeAndClear Spec.TREE)=Spec.xmssNode p sk i h pk a := by
  induction h generalizing i with
  | zero => rfl
  | succ h ih => simp only [Spec.xmssNode,ih];rfl

/-- For each slot this states only which worker chunk was published there. -/
structure Chunks {N : Usize} (p : params.Params) (sk : Spec.Bytes) (seed : Array U8 N)
    (base : Spec.Adrs) (m : XmssAuthMeta) (slots : alloc.vec.Vec (Option (Array U8 N))) : Prop where
  bounded : m.split.val≤m.height.val
  height : m.height.val≤9
  fits : m.slot_start.val+2^m.split.val≤slots.length
  root : (m.root_idx.val+1)*2^m.split.val≤2^32
  cell : ∀ c<2^m.split.val, ∃ row, slots.val[m.slot_start.val+c]! = some row ∧
    bytes row.val=Spec.xmssNode (Shake.params p) sk (m.root_idx.val*2^m.split.val+c)
      (m.height.val-m.split.val) (bytes seed.val) base

private theorem layer_of_cells {N : Usize} (p : params.Params) (sk : Spec.Bytes) (seed : Array U8 N)
    (base : Spec.Adrs) (m : XmssAuthMeta) (slots : alloc.vec.Vec (Option (Array U8 N)))
    (pub : Chunks p sk seed base m slots) (s : Slice (Option (Array U8 N)))
    (slice : s.val=List.slice m.slot_start.val (m.slot_start.val+2^m.split.val) slots.val)
    (len : s.length=2^m.split.val) :
    ∃ rows : Rows N, s.val=rows.val.map some ∧
      Layer (fun h i => Spec.xmssNode (Shake.params p) sk i h (bytes seed.val) base)
        m.root_idx.val m.height.val (m.height.val-m.split.val) rows := by
  let rows := alloc.vec.Vec.from (s.val.map (fun v => v.getD default)) (by simp)
  have lenVal : s.val.length=2^m.split.val := len
  have rowsEq : rows.val=s.val.map (fun v => v.getD default) := alloc.vec.Vec.from_val ..
  have size : rows.length=2^m.split.val := by simpa [rows,alloc.vec.Vec.length,Slice.length] using len
  have element (c : Nat) (inside : c<2^m.split.val) :
      ∃ row, s.val[c]! = some row ∧ bytes row.val=Spec.xmssNode (Shake.params p) sk
        (m.root_idx.val*2^m.split.val+c) (m.height.val-m.split.val) (bytes seed.val) base := by
    obtain ⟨v,eq,val⟩ := pub.cell c inside
    have fit : m.slot_start.val+2^m.split.val≤slots.val.length := pub.fits
    have hs : c<s.val.length := by rwa [lenVal]
    refine ⟨v,?_,val⟩
    rw [getElem!_pos s.val c hs]
    simp only [slice]
    rw [List.getElem_slice m.slot_start.val (m.slot_start.val+2^m.split.val) c slots.val ⟨fit,by omega⟩]
    rwa [←getElem!_pos slots.val]
  have read (c : Nat) (inside : c<2^m.split.val) : rows.val[c]! = s.val[c]!.getD default := by
    have hs : c<s.val.length := by rwa [lenVal]
    rw [rowsEq,getElem!_pos _ c (by simpa using hs),List.getElem_map,getElem!_pos s.val c hs]
  have depth : m.height.val-(m.height.val-m.split.val)=m.split.val := by have := pub.bounded;omega
  refine ⟨rows,?_,?_⟩
  · apply List.ext_getElem (by simp [rowsEq])
    intro c hc hc'
    obtain ⟨v,get,_⟩ := element c (lenVal ▸ hc)
    rw [List.getElem_map,←getElem!_pos,←getElem!_pos,read c (lenVal ▸ hc),get]
    rfl
  · rw [Layer,depth]
    refine ⟨size,?_⟩
    intro c hc
    obtain ⟨v,get,val⟩ := element c (size ▸ hc)
    rw [read c (size ▸ hc),get];exact val

theorem read_spec {N : Usize} (p : params.Params) (hp : PN p N) (sk : Spec.Bytes) (seed : Array U8 N)
    (base : Spec.Adrs) (treeAddr : address.Adrs) (tag : adrsS treeAddr=base.setTypeAndClear Spec.TREE)
    (m : XmssAuthMeta) (slots : alloc.vec.Vec (Option (Array U8 N))) (pub : Chunks p sk seed base m slots) :
    read_node slots seed treeAddr m ⦃ row => bytes row.val=Spec.xmssNode (Shake.params p) sk m.root_idx.val m.height.val (bytes seed.val) base ⦄ := by
  have cap : slots.length≤Usize.max := by scalar_tac
  have fits := pub.fits
  have height := pub.height
  have low := pub.bounded
  unfold read_node
  by_cases zero : m.split=0#u32
  · simp only [zero,ite_true]
    obtain ⟨row,get,val⟩ := pub.cell 0 (by positivity)
    simp only [zero,show (0#u32).val=0 by rfl,pow_zero,Nat.add_zero,Nat.mul_one,Nat.sub_zero] at get val fits
    step as ⟨slot,read⟩
    rw [←getElem!_pos,get] at read
    simp [read,ParallelSignJoin.readCell,core.option.Option.expect,ofOption,lift,val]
  · simp only [zero,ite_false]
    have power : 2^m.split.val≤512 := Nat.pow_le_pow_right (by decide : 0<2) (show m.split.val≤9 by omega)
    have bits : m.split.val<Usize.numBits := by have hw := System.Platform.numBits_eq; scalar_tac
    step as ⟨count,cv,_⟩
    all_goals try scalar_tac
    have countVal : count.val=2^m.split.val := by rw [cv,Nat.one_shiftLeft,Nat.mod_eq_of_lt];scalar_tac
    step as ⟨stop,sv⟩
    step as ⟨s,slice,len⟩
    step as ⟨sub,subv⟩
    have typed : (adrsS treeAddr).setTypeAndClear Spec.TREE=adrsS treeAddr := by rw [tag];rfl
    obtain ⟨rows,stored,layer⟩ := layer_of_cells p sk seed base m slots pub s
      (by simpa [sv,countVal] using slice) (by simpa [sv,countVal] using len)
    have depth : m.height.val-sub.val=m.split.val := by omega
    have mapped := fun i h => address_clear (Shake.params p) sk (bytes seed.val) base i h
    step with shake_xmss p hp seed sk treeAddr typed m.root_idx sub m.height s rows
      (depth ▸ pub.root) (by omega) (by omega) (by omega) stored
      (by simpa only [tag,mapped,subv,Layer] using layer) as ⟨row,eq⟩
    simpa [tag,mapped] using eq

end slhdsa.ParallelAuthTable
