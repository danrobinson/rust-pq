import ForsDriver.Program
import Shakebatch.Sibling
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.ForsDriver
open ShakeBatch

/-- Absolute index of the sibling root in the concatenated FORS forest. -/
def sibling (choices : Slice U32) (a : U32) (tree height : Nat) : Nat :=
  ((tree * 2^a.val + choices.val[tree]!.val) / 2^height) ^^^ 1

theorem sibling_local (choices : Slice U32) (a : U32) (tree height : Nat) (below : height<a.val) :
    sibling choices a tree height =
      tree*2^(a.val-height) + ((choices.val[tree]!.val/2^height) ^^^ 1) :=
  sibling_eq tree choices.val[tree]!.val a.val height below

private def readAbsolute (choices : Slice U32) (a : U32) (t : Usize) : Result U32 := do
  let i ← lift (UScalar.cast .U32 t)
  let shifted ← i <<< a
  let digit ← Slice.index_usize choices t
  shifted + digit

private theorem read_absolute (choices : Slice U32) (a : U32) (t : Usize) (ha : a.val≤14)
    (ht : t.val<choices.length) (size : choices.length≤35) (hd : choices.val[t.val]!.val<2^a.val) :
    ∃ x, readAbsolute choices a t=ok x ∧ x.val=t.val*2^a.val+choices.val[t.val]!.val ∧ x.val<2^20 := by
  obtain ⟨sh,bound⟩ := fors_shl_arith _ _ ha (by omega : t.val<35)
  suffices spec : readAbsolute choices a t ⦃ x => x.val=t.val*2^a.val+choices.val[t.val]!.val ∧ x.val<2^20 ⦄ by
    obtain ⟨x,run,post⟩ := spec_imp_exists spec
    exact ⟨x,run,post⟩
  unfold readAbsolute
  simp only [lift,bind_ok]
  have cast : (UScalar.cast .U32 t).val=t.val := cast_u32_usize_val _ (by omega)
  step with U32.ShiftLeft_spec (UScalar.cast .U32 t) a (by omega) as ⟨shifted,eq,_⟩
  have sv : shifted.val=t.val*2^a.val := by rw [eq,cast]; simpa [U32.size,U32.numBits] using sh
  step as ⟨digit,read⟩
  have xv : digit.val=choices.val[t.val]!.val := by rw [read,←getElem!_pos]
  step as ⟨x,add⟩
  exact ⟨by omega,by omega⟩

private theorem read_bind {α : Type} (choices : Slice U32) (a : U32) (t : Usize) {x : U32}
    (run : readAbsolute choices a t=ok x) (f : U32 → Result α) :
    (do let i ← lift (UScalar.cast .U32 t); let shifted ← i <<< a; let digit ← Slice.index_usize choices t
        let result ← shifted + digit; f result) = f x := by
  have joined := congrArg (fun r : Result U32 => r >>= f) run
  simpa only [readAbsolute,Std.bind_assoc,bind_tc_eq,bind_ok] using joined

private theorem range_done (it : Range) (k : Usize) (stop : it.end=k) (last : it.start.val=k.val) :
    ∃ next, core.iter.range.IteratorRange.next core.iter.range.StepUsize it=ok (none,next) := by
  obtain ⟨⟨_,n⟩,run,no,_⟩ := spec_imp_exists (core.iter.range.IteratorRange.next_Usize_none_spec it (by rw [stop,last]))
  exact ⟨n,by simpa [no] using run⟩

theorem level_zero (choices : Slice U32) (a : U32) (idx : Array U32 35#usize)
    (ha : a.val≤14) (size : choices.length≤35) (digits : ∀ i<choices.length, choices.val[i]!.val<2^a.val) :
    sign_loop2 ⟨0#usize,Slice.len choices⟩ choices a idx ⦃ out =>
      ∀ t<choices.length, out.val[t]!.val=sibling choices a t 0 ⦄ := by
  unfold sign_loop2
  apply range_fold (sign_loop2.body choices a) (Slice.len choices) idx
    (fun n rows => ∀ t<n, rows.val[t]!.val=sibling choices a t 0) (by simp)
  · intro it rows stop live prior
    change it.start.val < choices.length at live
    unfold sign_loop2.body
    step with core.iter.range.IteratorRange.next_Usize_some_spec it (by simpa [stop] using live) as ⟨_,next,tag,inc,ends⟩
    simp only [tag]
    obtain ⟨x,run,xv,small⟩ := read_absolute choices a it.start ha live size (digits _ live)
    rw [read_bind choices a it.start run];simp only [bind_ok,lift]
    step as ⟨out,put⟩
    refine ⟨next,out,rfl,ends.trans stop,inc,?_⟩
    intro j hj
    rw [put,Array.set_val_eq]
    by_cases eq : j=it.start.val
    · subst j
      rw [setSame _ _ _ (by simp;omega)]
      simp [sibling,UScalar.val_xor,xv]
    · rw [setOther _ _ _ _ (Ne.symm eq),prior j (by omega)]
  · intro it rows last stop
    obtain ⟨n,no⟩ := range_done it _ stop last
    simp [sign_loop2.body,no]

private def Singles (rows : Array U32 35#usize) (endAt : Nat) (f : Nat → Nat) :=
  ∀ t<endAt, rows.val[t]!.val=f t
private def Children {L : Usize} (rows : Array U32 L) (count width : Nat) (f : Nat → Nat) :=
  ∀ t<count, ∀ c<width, rows.val[width*t+c]!.val=width*f t+c

private def putPair (sib : U32) (t : Usize) (rows : Array U32 70#usize) (nodes : Array U32 35#usize) :
    Result (Array U32 70#usize × Array U32 35#usize) := do
  let ns ← nodes.update t sib
  let left ← 2#u32 * sib
  let off ← 2#usize * t
  let one ← rows.update off left
  let right ← left + 1#u32
  let last ← off + 1#usize
  let both ← one.update last right
  ok (both,ns)

private theorem put_pair (sib : U32) (t : Usize) (rows : Array U32 70#usize) (nodes : Array U32 35#usize)
    (f : Nat → Nat) (value : sib.val=f t.val) (small : sib.val<2^20) (room : t.val<35)
    (groups : Children rows t.val 2 f) (singles : Singles nodes t.val f) :
    ∃ both ns, putPair sib t rows nodes=ok (both,ns) ∧ Children both (t.val+1) 2 f ∧ Singles ns (t.val+1) f := by
  suffices spec : putPair sib t rows nodes ⦃ r => Children r.1 (t.val+1) 2 f ∧ Singles r.2 (t.val+1) f ⦄ by
    obtain ⟨⟨both,ns⟩,run,ok⟩ := spec_imp_exists spec
    exact ⟨both,ns,run,ok⟩
  unfold putPair
  step as ⟨ns,nset⟩
  step as ⟨left,lval⟩
  step as ⟨off,oval⟩
  step as ⟨one,wleft⟩
  step as ⟨right,rval⟩
  step as ⟨last,lidx⟩
  step as ⟨both,wright⟩
  constructor
  · intro i hi c hc
    rw [wright,Array.set_val_eq]
    by_cases eq : i=t.val
    · subst i
      interval_cases c
      · rw [setOther _ _ _ _ (by omega),wleft,Array.set_val_eq,show 2*t.val+0=off.val by omega,
            setSame _ _ _ (by simp;omega)]
        omega
      · rw [show 2*t.val+1=last.val by omega,setSame _ _ _ (by simp;omega)]
        omega
    · rw [setOther _ _ _ _ (by omega),wleft,Array.set_val_eq,setOther _ _ _ _ (by omega)]
      exact groups i (by omega) c hc
  · intro i hi
    rw [nset,Array.set_val_eq]
    by_cases eq : i=t.val
    · subst i;rw [setSame _ _ _ (by simp;omega),value]
    · rw [setOther _ _ _ _ (Ne.symm eq),singles i (by omega)]

private theorem pair_bind {α : Type} (sib : U32) (t : Usize) (rows : Array U32 70#usize)
    (nodes : Array U32 35#usize) {both ns} (run : putPair sib t rows nodes=ok (both,ns))
    (f : Array U32 70#usize → Array U32 35#usize → Result α) :
    (do let ns ← nodes.update t sib; let left ← 2#u32 * sib; let off ← 2#usize * t
        let one ← rows.update off left; let right ← left + 1#u32; let last ← off + 1#usize
        let both ← one.update last right; f both ns) = f both ns := by
  have h := congrArg (fun r => r >>= fun q => f q.1 q.2) run
  simpa only [putPair,Std.bind_assoc,bind_tc_eq,bind_ok] using h

theorem level_one (choices : Slice U32) (a : U32) (rows : Array U32 70#usize) (nodes : Array U32 35#usize)
    (ha : a.val≤14) (size : choices.length≤35) (digits : ∀ i<choices.length, choices.val[i]!.val<2^a.val) :
    sign_loop4 ⟨0#usize,Slice.len choices⟩ choices a rows nodes ⦃ out =>
      (∀ t<choices.length, ∀ c<2, out.1.val[2*t+c]!.val=2*sibling choices a t 1+c) ∧
      ∀ t<choices.length, out.2.val[t]!.val=sibling choices a t 1 ⦄ := by
  unfold sign_loop4
  let f := fun t => sibling choices a t 1
  apply range_fold (fun it (q : _ × _) => sign_loop4.body choices a it q.1 q.2) (Slice.len choices) (rows,nodes)
    (fun n q => Children q.1 n 2 f ∧ Singles q.2 n f) (by simp [Children,Singles])
  · rintro it ⟨rows,nodes⟩ stop live ⟨prev,ns⟩
    change it.start.val < choices.length at live
    unfold sign_loop4.body
    step with core.iter.range.IteratorRange.next_Usize_some_spec it (by simpa [stop] using live) as ⟨_,next,tag,inc,ends⟩
    simp only [tag]
    obtain ⟨x,run,xv,small⟩ := read_absolute choices a it.start ha live size (digits _ live)
    rw [read_bind choices a it.start run]
    step as ⟨y,shift,_⟩
    simp only [lift,bind_ok]
    let sib := y ^^^ 1#u32
    have eq : sib.val=f it.start.val := by simp [sib,f,sibling,UScalar.val_xor,shift,xv,Nat.shiftRight_eq_div_pow]
    have bound : sib.val<2^20 := by
      apply Nat.xor_lt_two_pow (n:=20) _ (by decide : 1<2^20)
      simp [shift,Nat.shiftRight_eq_div_pow]; omega
    obtain ⟨both,ns',put,groups,singles⟩ := put_pair sib it.start rows nodes f eq bound (by omega) prev ns
    rw [pair_bind sib it.start rows nodes put]
    simp only [step_simps]
    exact ⟨next,(both,ns'),rfl,ends.trans stop,inc,by simpa [inc] using groups,by simpa [inc] using singles⟩
  · rintro it ⟨r,n⟩ last stop
    obtain ⟨_,no⟩ := range_done it _ stop last
    simp [sign_loop4.body,no]

private theorem four_children (rows : Array U32 140#usize) (t : Usize) (sib : U32) (f : Nat → Nat)
    (value : sib.val=f t.val) (small : sib.val<2^20) (room : t.val<35) (prev : Children rows t.val 4 f) :
    sign_loop6_loop0 ⟨0#usize,4#usize⟩ rows t sib ⦃ out => Children out (t.val+1) 4 f ⦄ := by
  unfold sign_loop6_loop0
  apply WP.spec_mono (P₀ := fun out => Children out t.val 4 f ∧
    ∀ c<4, out.val[4*t.val+c]!.val=4*f t.val+c)
  · apply range_fold (sign_loop6_loop0.body t sib) 4#usize rows (fun n out =>
      Children out t.val 4 f ∧ ∀ c<n, out.val[4*t.val+c]!.val=4*f t.val+c) (by exact ⟨prev,by simp⟩)
    · rintro it old stop live ⟨earlier,partialRow⟩
      change it.start.val<4 at live
      unfold sign_loop6_loop0.body
      step with core.iter.range.IteratorRange.next_Usize_some_spec it (by simpa [stop] using live) as ⟨_,next,tag,inc,ends⟩
      simp only [tag]
      step as ⟨beginning,bv⟩
      simp only [lift,bind_ok]
      have cast : (UScalar.cast .U32 it.start).val=it.start.val := cast_u32_usize_val _ (by omega)
      step as ⟨val,ev⟩
      step as ⟨offset,off⟩
      step as ⟨pos,pv⟩
      step as ⟨out,put⟩
      refine ⟨next,out,rfl,ends.trans stop,inc,?_,?_⟩
      · intro j hj c hc
        rw [put,Array.set_val_eq,setOther _ _ _ _ (by omega),earlier j hj c hc]
      · intro c hc
        rw [put,Array.set_val_eq]
        by_cases eq : c=it.start.val
        · subst c
          rw [show 4*t.val+it.start.val=pos.val by omega,setSame _ _ _ (by simp;omega)]
          omega
        · rw [setOther _ _ _ _ (by omega),partialRow c (by omega)]
    · intro it old last stop
      obtain ⟨_,no⟩ := range_done it _ stop last
      simp [sign_loop6_loop0.body,no]
  · rintro out ⟨earlier,last⟩ i hi c hc
    by_cases eq : i=t.val
    · subst i;exact last c hc
    · exact earlier i (by omega) c hc

theorem level_two (choices : Slice U32) (a : U32) (rows : Array U32 140#usize) (mid : Array U32 70#usize)
    (nodes : Array U32 35#usize) (ha : a.val≤14) (size : choices.length≤35)
    (digits : ∀ i<choices.length, choices.val[i]!.val<2^a.val) :
    sign_loop6 ⟨0#usize,Slice.len choices⟩ choices a rows mid nodes ⦃ out =>
      (∀ t<choices.length, ∀ c<4, out.1.val[4*t+c]!.val=4*sibling choices a t 2+c) ∧
      (∀ t<choices.length, ∀ c<2, out.2.1.val[2*t+c]!.val=2*sibling choices a t 2+c) ∧
      ∀ t<choices.length, out.2.2.val[t]!.val=sibling choices a t 2 ⦄ := by
  unfold sign_loop6
  let f := fun t => sibling choices a t 2
  apply range_fold (fun it (q : _ × _ × _) => sign_loop6.body choices a it q.1 q.2.1 q.2.2) (Slice.len choices) (rows,mid,nodes)
    (fun n q => Children q.1 n 4 f ∧ Children q.2.1 n 2 f ∧ Singles q.2.2 n f) (by simp [Children,Singles])
  · rintro it ⟨rows,mid,nodes⟩ stop live ⟨prev,groups,singles⟩
    change it.start.val < choices.length at live
    unfold sign_loop6.body
    step with core.iter.range.IteratorRange.next_Usize_some_spec it (by simpa [stop] using live) as ⟨_,next,tag,inc,ends⟩
    simp only [tag]
    obtain ⟨x,run,xv,small⟩ := read_absolute choices a it.start ha live size (digits _ live)
    rw [read_bind choices a it.start run]
    step as ⟨y,shift,_⟩
    simp only [lift,bind_ok]
    let sib := y ^^^ 1#u32
    have eq : sib.val=f it.start.val := by simp [sib,f,sibling,UScalar.val_xor,shift,xv,Nat.shiftRight_eq_div_pow]
    have bound : sib.val<2^20 := by
      apply Nat.xor_lt_two_pow (n:=20) _ (by decide : 1<2^20)
      simp [shift,Nat.shiftRight_eq_div_pow]; omega
    obtain ⟨mid',ns',put,midRows,nsRows⟩ := put_pair sib it.start mid nodes f eq bound (by omega) groups singles
    rw [pair_bind sib it.start mid nodes put]
    step with four_children rows it.start sib f eq bound (by omega) prev as ⟨out,children⟩
    exact ⟨next,(out,mid',ns'),rfl,ends.trans stop,inc,by simpa [inc] using children,by simpa [inc] using midRows,by simpa [inc] using nsRows⟩
  · rintro it ⟨r,m,n⟩ last stop
    obtain ⟨_,no⟩ := range_done it _ stop last
    simp [sign_loop6.body,no]

end slhdsa.ForsDriver
