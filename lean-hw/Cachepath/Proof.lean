import Cachepath.Funs
import Slhdsa.Proofs.Hash

open Aeneas Aeneas.Std Result
namespace slhdsa.cache

theorem root {N : Usize} (tree : Slice (Array U8 N)) (positive : 0 < tree.length) :
    tree_root tree ⦃ r => r = tree.val[tree.length-1]! ⦄ := by
  unfold tree_root
  step*
  simp_all [getElem!_pos]

private theorem small_pow (m : Nat) (hm : m ≤ 10) : 2^m < Usize.size := by
  have h : 2^m ≤ 2^10 := Nat.pow_le_pow_right (by decide) hm
  scalar_tac

@[step] theorem offset (hp h : U32) (levels : hp.val ≤ 9) (inside : h.val ≤ hp.val) :
    level_offset hp h ⦃ r => r.val = 2^(hp.val+1) - 2^(hp.val+1-h.val) ⦄ := by
  have bits := System.Platform.numBits_eq
  unfold level_offset
  step as ⟨a,ha⟩
  step as ⟨b,hb⟩
  · scalar_tac
  step as ⟨c,hc⟩
  step as ⟨d,hd⟩
  · scalar_tac
  have hb' : b.val = 2^(hp.val+1) := by
    rw [hb, ha]
    rw [Nat.one_shiftLeft, Nat.mod_eq_of_lt (small_pow _ (by omega))]
  have hd' : d.val = 2^(hp.val+1-h.val) := by
    rw [hd,hc,ha]
    rw [Nat.one_shiftLeft, Nat.mod_eq_of_lt (small_pow _ (by omega))]
  have le : d.val ≤ b.val := by rw [hd',hb']; exact Nat.pow_le_pow_right (by decide) (by omega)
  step*

def pathIndex (hp leaf h : Nat) := 2^(hp+1) - 2^(hp+1-h) + ((leaf >>> h) ^^^ 1)

private theorem inTree {hp leaf h : Nat} (valid : leaf < 2^hp) (live : h < hp) :
    pathIndex hp leaf h < 2^(hp+1)-1 := by
  have split : 2^hp = 2^(hp-h)*2^h := by rw [← Nat.pow_add, Nat.sub_add_cancel (by omega)]
  have lo := (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos h)).2 (split ▸ valid)
  have one : 1 < 2^(hp-h) := lt_of_lt_of_le (by decide : 1 < 2^1)
    (Nat.pow_le_pow_right (by decide) (by omega))
  have sib := Nat.xor_lt_two_pow lo one
  have cap : 2^(hp-h) ≤ 2^hp := Nat.pow_le_pow_right (by decide) (by omega)
  have add : hp+1-h = hp-h+1 := by omega
  simp only [pathIndex, Nat.shiftRight_eq_div_pow, add, pow_succ]
  omega

/-- Every appended byte comes from its FIPS authentication sibling in
a level-contiguous tree. The caller's existing output is preserved. -/
theorem path {N : Usize} (tree : Slice (Array U8 N)) (hp leaf : U32) (out : alloc.vec.Vec U8)
    (levels : hp.val ≤ 9) (valid : leaf.val < 2^hp.val)
    (size : tree.length = 2^(hp.val+1)-1)
    (room : out.length + hp.val * N.val ≤ Usize.max) :
    append_auth_path tree hp leaf out ⦃ r => r.val = out.val ++ (List.range hp.val).flatMap
      (fun h => tree.val[pathIndex hp.val leaf.val h]!.val) ⦄ := by
  let row := fun h => tree.val[pathIndex hp.val leaf.val h]!.val
  unfold append_auth_path append_auth_path_loop
  apply loop.spec_decr_nat (measure := fun q : core.ops.range.Range U32 × alloc.vec.Vec U8 =>
      hp.val - q.1.start.val)
    (inv := fun q => q.1.end = hp ∧ q.1.start.val ≤ hp.val ∧
      q.2.length = out.length + q.1.start.val*N.val ∧
      q.2.val = out.val ++ (List.range q.1.start.val).flatMap row)
  · rintro ⟨it,current⟩ ⟨last,bound,length,emitted⟩
    simp only at last bound length emitted
    unfold append_auth_path_loop.body
    by_cases more : it.start.val < hp.val
    · step with core.iter.range.IteratorRange.next_UScalar_some_spec
          (cloneInst := core.clone.CloneU32) (partialOrdInst := core.cmp.PartialOrdU32)
          (fun _ => rfl) (fun _ _ => rfl) it (by rwa [last]) as ⟨o,next,item,inc,stop⟩
      simp only [item]
      step as ⟨shifted,shift⟩
      simp only [lift,bind_ok]
      step with offset hp it.start levels (by omega) as ⟨base,baseEq⟩
      have flip : (UScalar.cast .Usize (shifted ^^^ 1#u32)).val =
          ((leaf.val >>> it.start.val) ^^^ 1) := by
        rw [U32.cast_Usize_val_eq,UScalar.val_xor,shift]; rfl
      have fits := inTree valid more
      have index : base.val + (UScalar.cast .Usize (shifted ^^^ 1#u32)).val =
          pathIndex hp.val leaf.val it.start.val := by rw [baseEq,flip]; rfl
      step as ⟨off,offEq⟩
      step as ⟨node,nodeEq⟩
      have advance := Nat.mul_le_mul_right N.val (show it.start.val+1 ≤ hp.val by omega)
      rw [Nat.succ_mul] at advance
      step with slhdsa.extend_from_slice_u8_spec current (Array.to_slice node) (by rw [Array.length_to_slice]; omega)
        as ⟨new,appended⟩
      have added : new.length = current.length + N.val := by
        simpa [Array.val_to_slice] using congrArg List.length appended
      refine ⟨stop.trans last,by omega,by rw [inc,Nat.succ_mul]; omega,?_,by omega⟩
      rw [appended, Array.val_to_slice, emitted, inc, List.range_succ, List.flatMap_append]
      simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc]
      congr 1
      have inBounds : off.val < tree.val.length := by
        change off.val < tree.length
        omega
      simp only [row, ← index, ← offEq, getElem!_pos tree.val off.val inBounds, nodeEq]
    · step with core.iter.range.IteratorRange.next_UScalar_none_spec
          (partialOrdInst := core.cmp.PartialOrdU32) (fun _ _ => rfl) it (by rw [last]; omega)
          as ⟨o,next,item,_⟩
      simp only [item,step_simps]
      have eq : it.start.val = hp.val := by omega
      simpa [row,eq] using emitted
  · simp [row]

/-- A cached XMSS tree satisfies its construction contract when each row
stores Algorithm 9 nodes for the same seeds, layer and tree address. -/
def TreeContents {N : Usize} (tree : Slice (Array U8 N)) (p : Spec.Params)
    (sk pk : Spec.Bytes) (adrs : Spec.Adrs) : Prop :=
  ∀ h ≤ p.hp, ∀ i < 2^(p.hp-h),
    bytes tree.val[2^(p.hp+1) - 2^(p.hp+1-h) + i]!.val = Spec.xmssNode p sk i h pk adrs

theorem cached_xmss {N : Usize} (tree : Slice (Array U8 N)) (hp leaf : U32)
    (out : alloc.vec.Vec U8) (p : Spec.Params) (m sk pk : Spec.Bytes) (adrs : Spec.Adrs)
    (levels : hp.val ≤ 9) (sameHeight : hp.val = p.hp) (valid : leaf.val < 2^hp.val)
    (size : tree.length = 2^(hp.val+1)-1) (room : out.length + hp.val*N.val ≤ Usize.max)
    (stored : TreeContents tree p sk pk adrs) (sig : bytes out.val =
      Spec.wotsSign p m sk pk { adrs.setTypeAndClear Spec.WOTS_HASH with keypair := leaf.val }) :
    append_auth_path tree hp leaf out ⦃ r => bytes r.val = Spec.xmssSign p m sk leaf.val pk adrs ⦄ := by
  apply WP.spec_mono (path tree hp leaf out levels valid size room)
  intro r result
  rw [result,bytes_append,sig,Spec.xmssSign]
  congr 1
  simp only [bytes,List.map_flatMap, sameHeight]
  apply List.flatMap_congr
  intro h mem
  have live := List.mem_range.mp mem
  have split : 2^p.hp = 2^(p.hp-h)*2^h := by rw [← Nat.pow_add,Nat.sub_add_cancel (by omega)]
  have sel : leaf.val < 2^(p.hp-h)*2^h := by rwa [← split, ← sameHeight]
  have digit := (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos h)).2 sel
  have one : 1 < 2^(p.hp-h) := lt_of_lt_of_le (by decide : 1 < 2^1)
    (Nat.pow_le_pow_right (by decide) (by omega))
  simpa [pathIndex, Nat.shiftRight_eq_div_pow, bytes] using
    stored h (by omega) _ (Nat.xor_lt_two_pow digit one)

end slhdsa.cache
