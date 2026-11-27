import ForsDriver.Fields
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.ForsDriver
open ShakeBatch
set_option maxHeartbeats 800000

private def columnBody {N : Usize} (stride : Usize) (rows : Array (Array U8 N) 35#usize)
    (offset : Result Usize) (it : Range) (sig : Buffer) :
    Result (ControlFlow (Range × Buffer) Buffer) := do
  let (o,next) ← core.iter.range.IteratorRange.next core.iter.range.StepUsize it
  match o with
  | none => ok (done sig)
  | some tree =>
    let base ← tree * stride
    let delta ← offset
    let pos ← base + delta
    let stop ← pos + N
    let (dst,back) ← alloc.vec.Vec.index_mut (core.slice.index.SliceIndexRangeUsizeSlice U8)
      sig {start:=pos,«end»:=stop}
    let row ← Array.index_usize rows tree
    let src ← lift (Array.to_slice row)
    let copied ← core.slice.Slice.copy_from_slice core.marker.CopyU8 dst src
    ok (cont (next,back copied))

private theorem column {N : Usize} (k stride : Usize) (sig : Buffer)
    (rows : Array (Array U8 N) 35#usize) (value : Nat → Nat → Spec.Bytes) (levels col : Nat)
    (hk : k.val≤35) (shape : stride.val=levels*N.val) (hz : col<levels)
    (old : Fields N.val k.val levels stride.val value (fun _ z => z<col) sig)
    (correct : ∀ t<k.val, bytes rows.val[t]!.val=value t col)
    (offset : Result Usize) (delta : Usize) (run : offset=ok delta) (dv : delta.val=col*N.val) :
    loop (fun q : Range × Buffer => columnBody stride rows offset q.1 q.2) (⟨0#usize,k⟩,sig)
      ⦃ out => Fields N.val k.val levels stride.val value (fun _ z => z≤col) out ⦄ := by
  let P := fun (i : Nat) (cur : Buffer) => Fields N.val k.val levels stride.val value
    (fun t z => z<col ∨ t < i ∧ z=col) cur
  apply WP.spec_mono (P₀ := fun out => P k.val out) ?_ (by
    intro out h
    exact Fields.mono h (by intros; omega))
  apply range_fold (columnBody stride rows offset) k sig P
  · exact old.mono (by simp)
  · intro it cur he hi prior
    have len := prior.1
    have max : cur.length≤Usize.max := by simp
    have block := Nat.mul_le_mul_right stride.val hi
    rw [Nat.succ_mul] at block
    have within := Nat.mul_le_mul_right N.val hz
    rw [Nat.succ_mul,←shape] at within
    unfold columnBody
    step with core.iter.range.IteratorRange.next_Usize_some_spec it (he.symm ▸ hi) as ⟨o,nxt,ho,hn,hend⟩
    simp only [ho,run,bind_ok]
    step as ⟨base,bv⟩
    step as ⟨pos,pv⟩
    step as ⟨stop,sv⟩
    step as ⟨dst,back,data,length,save⟩
    step as ⟨row,get⟩
    simp only [lift,bind_ok]
    step as ⟨w,cp⟩
    all_goals try scalar_tac
    refine ⟨nxt,_,rfl,hend.trans he,hn,?_⟩
    apply Fields.store value _ _ cur _ rows.val[it.start.val]! it.start.val col hi hz shape prior
    · rw [save,cp,Array.val_to_slice,get,←getElem!_pos]
      simp only [alloc.vec.Vec.setSlice!,alloc.vec.Vec.val,Slice.setSlice!_val,pv,bv,dv]
    · exact correct _ hi
    · intros; omega
  · intro it cur atEnd he
    obtain ⟨⟨o,nxt⟩,run,none,_⟩ := spec_imp_exists
      (core.iter.range.IteratorRange.next_Usize_none_spec it (by rw [he];omega))
    simp only [columnBody,run,bind_ok,none]
    rfl


theorem column1 {N : Usize} (k stride : Usize) (sig : Buffer)
    (rows : Array (Array U8 N) 35#usize) (value : Nat → Nat → Spec.Bytes) (levels : Nat)
    (hk : k.val≤35) (shape : stride.val=levels*N.val) (hz : 1<levels)
    (old : Fields N.val k.val levels stride.val value (fun _ z => z<1) sig)
    (correct : ∀ t<k.val, bytes rows.val[t]!.val=value t 1) :
    sign_loop3 ⟨0#usize,k⟩ stride sig rows ⦃ out =>
      Fields N.val k.val levels stride.val value (fun _ z => z≤1) out ⦄ := by
  have body : sign_loop3.body stride rows = columnBody stride rows (ok N) := by
    funext it cur
    unfold sign_loop3.body columnBody
    congr 1
    funext pair
    rcases pair with ⟨o,nxt⟩
    cases o with
    | none => rfl
    | some t =>
      dsimp only
      congr 1
      funext base
      simp only [bind_ok]
      funext next
      cases base <;> rfl
  unfold sign_loop3
  rw [body]
  exact column k stride sig rows value levels 1 hk shape hz old correct (ok N) N rfl (by simp)

theorem column2 {N : Usize} (k stride : Usize) (sig : Buffer)
    (rows : Array (Array U8 N) 35#usize) (value : Nat → Nat → Spec.Bytes) (levels : Nat)
    (hk : k.val≤35) (shape : stride.val=levels*N.val) (hz : 2<levels)
    (old : Fields N.val k.val levels stride.val value (fun _ z => z<2) sig)
    (correct : ∀ t<k.val, bytes rows.val[t]!.val=value t 2) :
    sign_loop5 ⟨0#usize,k⟩ stride sig rows ⦃ out =>
      Fields N.val k.val levels stride.val value (fun _ z => z≤2) out ⦄ := by
  have room := Nat.mul_le_mul_right N.val (show 2≤levels by omega)
  rw [←shape] at room
  have spec : 2#usize * N ⦃ d => d.val=2*N.val ⦄ := by step <;> scalar_tac
  obtain ⟨d,run,dv⟩ := spec_imp_exists spec
  exact column k stride sig rows value levels 2 hk shape hz old correct _ d run dv

theorem column3 {N : Usize} (k stride : Usize) (sig : Buffer)
    (rows : Array (Array U8 N) 35#usize) (value : Nat → Nat → Spec.Bytes) (levels : Nat)
    (hk : k.val≤35) (shape : stride.val=levels*N.val) (hz : 3<levels)
    (old : Fields N.val k.val levels stride.val value (fun _ z => z<3) sig)
    (correct : ∀ t<k.val, bytes rows.val[t]!.val=value t 3) :
    sign_loop7 ⟨0#usize,k⟩ stride sig rows ⦃ out =>
      Fields N.val k.val levels stride.val value (fun _ z => z≤3) out ⦄ := by
  have room := Nat.mul_le_mul_right N.val (show 3≤levels by omega)
  rw [←shape] at room
  have spec : 3#usize * N ⦃ d => d.val=3*N.val ⦄ := by step <;> scalar_tac
  obtain ⟨d,run,dv⟩ := spec_imp_exists spec
  exact column k stride sig rows value levels 3 hk shape hz old correct _ d run dv

end slhdsa.ForsDriver
