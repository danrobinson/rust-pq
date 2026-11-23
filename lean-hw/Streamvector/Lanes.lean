import Streamvector.Initial
import Streamscalar.Ordered
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.Stream
set_option maxRecDepth 24000
set_option maxHeartbeats 8000000

private theorem readAt {α : Type} [Inhabited α] {n : Usize} (a : Array α n) (i : Usize) (h : i.val < n.val) :
    a.index_usize i = ok a.val[i.val]! := by
  obtain ⟨x,op,val⟩ := spec_imp_exists (Array.index_usize_spec a i (by simpa using h))
  rw [op,val,getElem!_pos]

private theorem indexAdd (a b : Usize) (h : a.val+b.val ≤ 80) :
    a+b = ok (UScalar.ofNat (a.val+b.val) (by change _ ≤ 4294967295; omega) : Usize) := by
  obtain ⟨v,eq,val⟩ := spec_imp_exists (Usize.add_spec (x := a) (y := b) (by scalar_tac))
  rw [eq]; congr 1; exact UScalar.eq_of_val_eq val

theorem lane256 (st : Array U32 8#usize) (table : Array (Array U32 16#usize) 64#usize)
    (blocks : Array (Array U8 64#usize) 16#usize) (rows : ordered256 table blocks 64)
    (it next : core.ops.range.Range Usize) (lane : Usize) (bound : lane.val < 16)
    (more : core.iter.range.IteratorRange.next core.iter.range.StepUsize it = ok (some lane,next)) :
    StreamVectorRust.sha256.stream.prescheduled_loop0_loop1.body table it st ⦃ flow => ∃ out,
      flow = ControlFlow.cont (next,out) ∧
      slhdsa.wv out.val = Spec.SHA256.compress (slhdsa.wv st.val) (bytes blocks.val[lane.val]!.val) ⦄ := by
  unfold StreamVectorRust.sha256.stream.prescheduled_loop0_loop1.body
  rw [more]
  simp only [bind_ok]
  simp (config := {maxSteps := 500000}) (disch := decide) only [indexAdd,bind_ok]
  simp (config := {maxSteps := 500000}) (disch := first | exact bound | decide) only [readAt,bind_ok,StreamVectorRust.sha256.stream.round]
  have readLane (row : Array U32 16#usize) : row.index_usize lane ⦃ x => x = row.val[lane.val]! ⦄ := by
    rw [readAt row lane bound]; exact (WP.spec_ok _).mpr rfl
  have start : state256 st = rounds256 0 (bytes blocks.val[lane.val]!.val) st := rfl
  have advance (v : Array U32 8#usize) {i : Nat}
      (prev : state256 v = rounds256 i (bytes blocks.val[lane.val]!.val) st) (lt : i < 64) :=
    ordered_round256 i lane.val st v table blocks lt bound rows prev
  iterate 64
    refine WP.spec_bind (readLane _) ?_
    rintro value rfl
    refine WP.spec_bind (advance _ (by assumption) (by decide)) ?_
    intro v hv
  apply WP.spec_bind (feed256_fips st _ _ (by assumption))
  intro out hash
  exact (WP.spec_ok _).mpr ⟨out,rfl,hash⟩

theorem lane512 (st : Array U64 8#usize) (table : Array (Array U64 8#usize) 80#usize)
    (blocks : Array (Array U8 128#usize) 8#usize) (rows : ordered512 table blocks 80)
    (it next : core.ops.range.Range Usize) (lane : Usize) (bound : lane.val < 8)
    (more : core.iter.range.IteratorRange.next core.iter.range.StepUsize it = ok (some lane,next)) :
    StreamVectorRust.sha512.stream.prescheduled_loop0_loop1.body table it st ⦃ flow => ∃ out,
      flow = ControlFlow.cont (next,out) ∧
      slhdsa.S512.wv out.val = Spec.SHA512.compress (slhdsa.S512.wv st.val) (bytes blocks.val[lane.val]!.val) ⦄ := by
  unfold StreamVectorRust.sha512.stream.prescheduled_loop0_loop1.body
  rw [more]
  simp only [bind_ok]
  simp (config := {maxSteps := 500000}) (disch := decide) only [indexAdd,bind_ok]
  simp (config := {maxSteps := 500000}) (disch := first | exact bound | decide) only [readAt,bind_ok,StreamVectorRust.sha512.stream.round]
  have readLane (row : Array U64 8#usize) : row.index_usize lane ⦃ x => x = row.val[lane.val]! ⦄ := by
    rw [readAt row lane bound]; exact (WP.spec_ok _).mpr rfl
  have start : state512 st = rounds512 0 (bytes blocks.val[lane.val]!.val) st := rfl
  have advance (v : Array U64 8#usize) {i : Nat}
      (prev : state512 v = rounds512 i (bytes blocks.val[lane.val]!.val) st) (lt : i < 80) :=
    ordered_round512 i lane.val st v table blocks lt bound rows prev
  iterate 80
    refine WP.spec_bind (readLane _) ?_
    rintro value rfl
    refine WP.spec_bind (advance _ (by assumption) (by decide)) ?_
    intro v hv
  apply WP.spec_bind (feed512_fips st _ _ (by assumption))
  intro out hash
  exact (WP.spec_ok _).mpr ⟨out,rfl,hash⟩

end slhdsa.X86.Stream
