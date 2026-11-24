import Chainwrite.Chunk
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.X86.Chain
open ChainWriteRust.sha256.x86.avx512

abbrev Iter := core.iter.adapters.step_by.StepBy (core.ops.range.Range Usize)
abbrev Hash := Array Store.Reg512 8#usize

def digestPart (s : Hash) (j : Fin 16) (offset width : Nat) : Spec.Bytes :=
  (List.range width).map (fun k => Store.digestByte s j (offset+k))

private theorem words (N : Usize) (s : Hash) (o : Usize) (ho : o.val ≤ 16) :
    core.array.from_fn 4#usize (write_finished.closure.Insts.CoreOpsFunctionFnMutTupleUsize__m512i N)
      (s,o,Store.control) ⦃ a => ∀ k, k < 4 → ∀ j, a.val[k]! j = Store.reverse32 (s.val[o.val/4+k]! j) ⦄ :=
  Store.words N s o ho

theorem group_spec (N : Usize) (hash : Hash) (batch : Rows) (mask : U16) (it : Iter)
    (he : it.iter.end = N) (hs : it.step_by = 16#usize)
    (ho : it.iter.start.val ≤ 16) (align : it.iter.start.val % 16 = 0)
    (hlt : it.iter.start.val < N.val) (hn : N.val ≤ 32) (hb : Covers mask batch.length) :
    write_finished_loop1.body N hash Store.control mask it batch ⦃ flow => ∃ nxt out,
      flow = cont (nxt,out) ∧ nxt.iter.start.val = min (it.iter.start.val+16) N.val ∧
      nxt.iter.end = N ∧ nxt.step_by = 16#usize ∧ out.length = batch.length ∧
      ∀ k < batch.length, bytes out.val[k]!.val = if active : mask.bv.getLsbD k then
        let off := it.iter.start.val
        let width := min (N.val-off) 16
        let old := bytes batch.val[k]!.val
        old.take (22+off) ++ digestPart hash ⟨k,by
          by_contra! h
          exact Bool.noConfusion ((BitVec.getLsbD_of_ge mask.bv k h).symm.trans active)⟩ off width ++ old.drop (22+off+width)
        else bytes batch.val[k]!.val ⦄ := by
  unfold write_finished_loop1.body
  step with Store.next it (he ▸ hlt) hs as ⟨opt,nxt,hopt,hnx,hend,hstep⟩
  simp only [hopt]
  step with words N hash it.iter.start ho as ⟨a,hw⟩
  step as ⟨a0,ha0⟩
  step as ⟨a1,ha1⟩
  step as ⟨a2,ha2⟩
  step as ⟨a3,ha3⟩
  step with Store.transpose_rows_spec a0 a1 a2 a3 as ⟨rows,hrow⟩
  step as ⟨diff,hdiff⟩
  step as ⟨width,hwidth⟩
  have wid : width.val = min (N.val-it.iter.start.val) 16 := by simp [hwidth,hdiff]
  step with write_chunk_spec batch rows mask it.iter.start width hb (by omega) (by omega) as ⟨out,hlen,hout⟩
  refine ⟨_,_,rfl,he ▸ hnx,hend.trans he,hstep.trans hs,hlen,?_⟩
  intro k hk
  rw [hout k hk]
  split <;> rename_i active
  · unfold putChunk
    rw [wid]
    congr 2
    apply List.ext_getElem
    · simp [bytes,digestPart]
    · intro t ht _
      have bound : t < min (N.val-it.iter.start.val) 16 := by simpa [bytes] using ht
      have lt16 : t < 16 := by omega
      have lane : k < 16 := by by_contra! h; exact Bool.noConfusion ((BitVec.getLsbD_of_ge mask.bv k h).symm.trans active)
      have eq := hrow ⟨k,lane⟩ ⟨t,lt16⟩
      simp only [Store.rowAt,ha0,ha1,ha2,ha3,← getElem!_pos] at eq
      rw [Store.choose _ (by omega),hw _ (by omega),Store.reversed_byte] at eq
      simp only [bytes,List.getElem_take,List.getElem_map,digestPart,List.getElem_range,Store.digestByte]
      have hlen16 : t < rows.val[k%4]!.val[k/4]!.val.length := by simpa using lt16
      simpa only [getElem!_pos (rows.val[k%4]!.val[k/4]!.val) t hlen16,show (it.iter.start.val+t)/4 = it.iter.start.val/4+t/4 by omega,
        show (it.iter.start.val+t)%4 = t%4 by omega] using eq
  · rfl
end slhdsa.X86.Chain
