import Parallel.ForsMergeProgram
open Aeneas Aeneas.Std Result
namespace slhdsa.ParallelForsMerge

theorem merge_spec {N : Usize} (p : params.Params) (hp : PN p N) (m : Meta)
    (slots : alloc.vec.Vec (Option (Array U8 N))) (seed : Array U8 N) (sk : Spec.Bytes)
    (a : address.Adrs) (stride : Usize) (tree : m.tree.val<p.k.val) (field : m.height.val<p.a.val)
    (shape : stride.val=1+p.a.val) (low : m.sub_h.val≤m.height.val)
    (count : m.chunks.val=2^(m.height.val-m.sub_h.val)) (fits : m.slot_start.val+m.chunks.val≤slots.length)
    (room : (m.root_idx.val+1)*2^(m.height.val-m.sub_h.val)≤2^32)
    (stored : ∀ c<m.chunks.val, ∃ v, slots.val[m.slot_start.val+c]! = some v ∧
      bytes v.val=Spec.forsNode (Shake.params p) sk (m.root_idx.val*m.chunks.val+c)
        m.sub_h.val (bytes seed.val) (adrsS a)) :
    merge_fors m slots seed a stride ⦃ (dest,r) => dest.val=m.tree.val*(1+p.a.val)+1+m.height.val ∧
      bytes r.val=Spec.forsNode (Shake.params p) sk m.root_idx.val m.height.val (bytes seed.val) (adrsS a) ⦄ := by
  unfold merge_fors
  have cap : slots.length≤Usize.max := by simp
  have h : p.a.val≤14 := hp.valid.a_le
  have k : p.k.val≤35 := hp.valid.k_le
  step as ⟨stop,stopEq⟩
  step as ⟨rows,take,size⟩
  all_goals try scalar_tac
  have n : rows.length=m.chunks.val := by omega
  let node := fun z i => Spec.forsNode (Shake.params p) sk i z (bytes seed.val) (adrsS a)
  obtain ⟨filled,data,given⟩ := ParallelReduceNative.published_layer rows node m.root_idx.val m.height.val
    m.sub_h.val (n.trans count) (by
      intro c hc
      have small : c<m.chunks.val := n ▸ hc
      obtain ⟨v,cell,val⟩ := stored c small
      refine ⟨v,?_,by simpa [node,←count] using val⟩
      rw [take,List.getElem!_slice]
      · exact cell
      · change stop.val≤slots.val.length ∧ m.slot_start.val+c<stop.val
        exact ⟨stopEq ▸ fits,by omega⟩)
  step with ParallelReduceNative.shake_fors p hp seed sk a m.root_idx m.sub_h m.height rows filled
    room (by omega) low (by omega) data given as ⟨result,value⟩
  simp only [lift,bind_ok]
  have tc : (UScalar.cast .Usize m.tree).val=m.tree.val := by scalar_tac
  have hc : (UScalar.cast .Usize m.height).val=m.height.val := by scalar_tac
  have upper := Nat.mul_le_mul (show m.tree.val≤35 by omega) (show stride.val≤15 by omega)
  step as ⟨base,bv⟩
  step as ⟨off,ov⟩
  try simp only [lift,bind_ok]
  step as ⟨out,eq⟩
  all_goals first | exact ⟨by rw [eq,ov,bv,tc,hc,shape],value⟩ | scalar_tac

end slhdsa.ParallelForsMerge
