import Kgridbulk.Rounds
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.Kgridbulk
open KgridbulkRust KgridbulkRust.shake256.stream_x86

private theorem bytePtr (s : Slice U8) : core.slice.Slice.as_ptr s = ok ⟨s.val,0⟩ := by
  unfold core.slice.Slice.as_ptr ChainWideRust.core.slice.Slice.as_ptr
  change ok (⟨s.val.flatMap (fun x => [x]),0⟩ : GatherRust.ReadPtr U8) = _
  simp

private theorem addBytes (xs : List U8) (off : Usize) (h : off.val≤xs.length) :
    core.ptr.const_ptr.RawPtrConstT.add (⟨xs,0⟩ : GatherRust.ReadPtr U8) off = ok ⟨xs,off.val⟩ := by
  unfold core.ptr.const_ptr.RawPtrConstT.add ChainWideRust.core.ptr.const_ptr.RawPtrConstT.add
  change (if 0 + off.val*1 ≤ xs.length then _ else _) = _
  simp [h,show ChainWideRust.MemoryElement.width U8=1 by rfl]

private theorem afterUpdate (a : Kdiag.Grid) (i : Usize) (row : Row) (r : Nat) (hr : r<5) :
    (a.set i row).val[r]! = if i.val=r then row else a.val[r]! := by
  rw [Array.set_val_eq,getElem!_pos _ _ (by simp;omega),List.getElem_set,getElem!_pos a.val r (by simpa using hr)]

/-- The first three rows consume fifteen complete little-endian input words. -/
theorem firstRows (a : Kdiag.Grid) (block : Slice U8) (size : block.length=136) :
    absorb_loop0_loop0 ⟨0#usize,3#usize⟩ a block ⦃ out => ∀ r : Nat, r<5 → ∀ j : Fin 8, j.val<5 →
      out.val[r]! j = if r<3 then a.val[r]! j ^^^ wordAt block.val (40*r+8*j.val) else a.val[r]! j ⦄ := by
  unfold absorb_loop0_loop0
  apply loop.spec_decr_nat
    (measure := fun (p : core.ops.range.Range Usize × Kdiag.Grid) => 3-p.1.start.val)
    (inv := fun p => p.1.end=3#usize ∧ p.1.start.val≤3 ∧ ∀ r : Nat, r<5 → ∀ j : Fin 8, j.val<5 →
      p.2.val[r]! j = if r < p.1.start.val then a.val[r]! j ^^^ wordAt block.val (40*r+8*j.val) else a.val[r]! j)
  · rintro ⟨it,st⟩ ⟨he,hb,prior⟩
    simp only at he hb prior ⊢
    unfold absorb_loop0_loop0.body
    by_cases more : it.start.val<3
    · obtain ⟨⟨o,nxt⟩,read,ho,hn,he'⟩ := spec_imp_exists
        (core.iter.range.IteratorRange.next_Usize_some_spec it (by rw [he];exact more))
      subst o
      rw [read]
      simp only [bind_ok]
      step as ⟨row,hrow⟩
      rw [bytePtr]
      simp only [bind_ok]
      step as ⟨off,hoff⟩
      have bo : off.val+40≤block.val.length := by change _ ≤ block.length; rw [size];scalar_tac
      rw [addBytes _ _ (by omega)]
      simp only [bind_ok,core.ptr.const_ptr.RawPtrConstT.cast,GatherRust.core.ptr.const_ptr.RawPtrConstT.cast]
      rw [loadFive _ (by exact bo)]
      simp only [bind_ok,core.core_arch.x86.avx512f._mm512_xor_si512,
        KavxRust.core.core_arch.x86.avx512f._mm512_xor_si512]
      step as ⟨out,ho⟩
      refine ⟨he'.trans he,by omega,?_,by omega⟩
      intro r hr j hj
      rw [ho,afterUpdate _ _ _ _ hr]
      by_cases same : it.start.val=r
      · subst r
        simp only [ite_self,ite_true,hj,if_pos (show it.start.val<nxt.start.val by omega),hrow]
        have old := prior it.start.val (by omega) j hj
        simp only [Nat.lt_irrefl,ite_false] at old
        have inBounds : it.start.val < st.val.length := by simpa using hr
        rw [getElem!_pos st.val it.start.val inBounds] at old
        rw [old,hoff]
      · rw [if_neg same,prior r hr j hj]
        by_cases before : r < it.start.val <;> simp [before,show (r<nxt.start.val) ↔ r < it.start.val by omega]
    · step with core.iter.range.IteratorRange.next_Usize_none_spec it (by rw [he];exact Nat.not_lt.mp more) as ⟨o,_,ho,_⟩
      simp only [ho,step_simps]
      simpa only [show it.start.val=3 by omega] using prior
  · exact ⟨rfl,Nat.zero_le _,by simp⟩
/-- The last rate row reads two words. Its remaining active state words are preserved. -/
def lastRow (grid : Kdiag.Grid) (block : Slice U8) : Result Kdiag.Grid := do
  let row ← grid.index_usize 3#usize
  let raw ← core.slice.Slice.as_ptr block
  let endPtr ← core.ptr.const_ptr.RawPtrConstT.add raw 120#usize
  let cast ← core.ptr.const_ptr.RawPtrConstT.cast I64 endPtr
  let tail ← core.core_arch.x86.avx512f._mm512_maskz_loadu_epi64 3#u8 cast
  let result ← core.core_arch.x86.avx512f._mm512_xor_si512 row tail
  grid.update 3#usize result

theorem lastRow_spec (grid : Kdiag.Grid) (block : Slice U8) (size : block.length=136) :
    lastRow grid block ⦃ out => ∀ r : Nat, r<5 → ∀ j : Fin 8,
      out.val[r]! j = if r=3 ∧ j.val<2 then grid.val[r]! j ^^^ wordAt block.val (120+8*j.val)
        else grid.val[r]! j ⦄ := by
  unfold lastRow
  step as ⟨row,hrow⟩
  rw [bytePtr]
  simp only [bind_ok]
  rw [addBytes _ _ (by change 120 ≤ block.length;omega)]
  simp only [bind_ok,core.ptr.const_ptr.RawPtrConstT.cast,GatherRust.core.ptr.const_ptr.RawPtrConstT.cast]
  rw [loadTwo _ (by change 120+16 ≤ block.length;omega)]
  simp only [bind_ok,core.core_arch.x86.avx512f._mm512_xor_si512,KavxRust.core.core_arch.x86.avx512f._mm512_xor_si512]
  step as ⟨out,ho⟩
  rename_i r hr j
  rw [ho,afterUpdate _ _ _ _ hr]
  by_cases same : r=3
  · subst r
    rw [hrow]
    have bound : 3 < grid.val.length := by simp
    rw [getElem!_pos grid.val 3 bound]
    by_cases small : j.val<2 <;> simp [small]
  · simp [same,Ne.symm same]
end slhdsa.Kgridbulk
