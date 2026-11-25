import Cachepath.BuilderLayout
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.cache.builder

abbrev Range := core.ops.range.Range Usize
abbrev Inclusive := core.ops.range.RangeInclusive U32

def rangeBody {α} (write : Usize → α → Result α) (s : Range × α) :
    Result (ControlFlow (Range × α) α) := do
  let (o,next) ← core.iter.range.IteratorRange.next core.iter.range.StepUsize s.1
  match o with
  | none => ok (.done s.2)
  | some i => let out ← write i s.2; ok (.cont (next,out))

theorem row {α} (write : Usize → α → Result α) (I : Nat → α → Prop) (limit : Usize)
    (stepOk : ∀ i x, i.val < limit.val → I i.val x → write i x ⦃ y => I (i.val+1) y ⦄)
    (initial : α) (hi : I 0 initial) :
    loop (rangeBody write) (⟨0#usize,limit⟩,initial) ⦃ x => I limit.val x ⦄ := by
  apply loop.spec_decr_nat (measure := fun (q : Range × α) => limit.val - q.1.start.val)
    (inv := fun q => q.1.end = limit ∧ q.1.start.val ≤ limit.val ∧ I q.1.start.val q.2)
  · rintro ⟨it,x⟩ ⟨stop,bound,h⟩
    simp only at stop bound h
    unfold rangeBody
    by_cases live : it.start.val < limit.val
    · step with core.iter.range.IteratorRange.next_UScalar_some_spec
        (cloneInst := core.clone.CloneUsize) (partialOrdInst := core.cmp.PartialOrdUsize)
        (fun _ => rfl) (fun _ _ => rfl) it (by rwa [stop]) as ⟨o,it',item,inc,len⟩
      simp only [item]
      step with stepOk it.start x live h as ⟨x',hx'⟩
      exact ⟨len.trans stop,by omega,inc ▸ hx',by omega⟩
    · step with core.iter.range.IteratorRange.next_UScalar_none_spec
        (partialOrdInst := core.cmp.PartialOrdUsize) (fun _ _ => rfl) it (by rw [stop]; omega)
        as ⟨o,it',item,_⟩
      simpa only [item,step_simps,show it.start.val = limit.val by omega] using h
  · exact ⟨rfl,by simp,hi⟩

def inclusiveBody {α} (write : U32 → α → Result α) (s : Inclusive × α) :
    Result (ControlFlow (Inclusive × α) α) := do
  let (o,next) ← core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator.next
    core.iter.range.StepU32 s.1
  match o with
  | none => ok (.done s.2)
  | some z => let v ← write z s.2; ok (.cont (next,v))

theorem levels {α} (write : U32 → α → Result α) (I : Nat → α → Prop) (limit : U32)
    (nz : 0 < limit.val)
    (stepOk : ∀ z x, 0 < z.val → z.val ≤ limit.val → I z.val x → write z x ⦃ y => I (z.val+1) y ⦄)
    (it : Inclusive) (start : it.start = 1#u32) (stop : it.«end» = limit) (fresh : it.exhausted = false)
    (initial : α) (hi : I 1 initial) :
    loop (inclusiveBody write) (it,initial) ⦃ x => I (limit.val+1) x ⦄ := by
  let cursor (r : Inclusive) := if r.exhausted then limit.val+1 else r.start.val
  apply loop.spec_decr_nat (measure := fun (q : Inclusive × α) => limit.val+1 - cursor q.1)
    (inv := fun q => q.1.end = limit ∧ 0 < q.1.start.val ∧ q.1.start.val ≤ limit.val ∧ I (cursor q.1) q.2)
  · rintro ⟨r,x⟩ ⟨stop,pos,bound,h⟩
    simp only at stop pos bound h
    unfold inclusiveBody
    step as ⟨o,next,hnext⟩
    cases he : r.exhausted
    · have live : ¬ (r.exhausted = true ∨ r.end.val < r.start.val) := by simp [he,stop,show ¬limit.val < r.start.val by omega]
      simp only [live,↓reduceIte] at hnext
      have startI : I r.start.val x := by simpa [cursor,he] using h
      by_cases more : r.start.val < r.end.val
      · simp only [more,↓reduceIte] at hnext
        obtain ⟨item,inc,stop',fresh'⟩ := hnext
        simp only [item]
        step with stepOk _ _ pos bound startI as ⟨y,hy⟩
        simp only [cursor,he,fresh',Bool.false_eq_true,↓reduceIte]
        exact ⟨stop'.trans stop,by omega,by rw [stop] at more; omega,inc ▸ hy,by omega⟩
      · simp only [more,↓reduceIte] at hnext
        obtain ⟨item,same,stop',end'⟩ := hnext
        simp only [item]
        step with stepOk _ _ pos bound startI as ⟨y,hy⟩
        have last : r.start.val = limit.val := by rw [stop] at more; omega
        simp only [cursor,he,end',↓reduceIte,Bool.false_eq_true,same,last,Nat.sub_self]
        exact ⟨stop'.trans stop, nz, Nat.le_refl _,last ▸ hy,by omega⟩
    · simp only [he,true_or,↓reduceIte] at hnext
      simpa only [hnext.1,step_simps] using (show I (limit.val+1) x by simpa [cursor,he] using h)
  · simp [cursor,start,stop,fresh,show 1 ≤ limit.val by omega,hi]

end slhdsa.cache.builder
