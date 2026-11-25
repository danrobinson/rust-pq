import Cachepath.ParallelFill
import Cachepath.ParallelFillProgram
open Aeneas Aeneas.Std Result
namespace slhdsa.cache.builder.workers.fill

theorem runtimePlan_spec (n threads : Usize) (cap : n.val≤512) :
    runtimePlan n threads ⦃ result => result.map (fun (c,k) => (c.val,k.val))=plan n.val threads.val ⦄ := by
  unfold runtimePlan plan
  by_cases short : n<16#usize
  · have h : n.val<16 := short
    simp [short,h,WP.spec_ok]
  have h : ¬ n.val<16 := short
  simp only [ite_eq_right short,ite_eq_right h]
  step as ⟨q,div⟩
  simp only [lift,bind_ok]
  let w := core.cmp.impls.OrdUsize.min threads q
  have wval : w.val=min threads.val (n.val/4) := by
    change (if q.val<threads.val then q else threads).val=_
    split <;> omega
  by_cases few : w<2#usize
  · have h : min threads.val (n.val/4)<2 := by rw [← wval];exact few
    simp [show core.cmp.impls.OrdUsize.min threads q < 2#usize from few,h,WP.spec_ok]
  have h' : ¬min threads.val (n.val/4)<2 := by rw [← wval];exact few
  simp only [show ¬ core.cmp.impls.OrdUsize.min threads q < 2#usize from few,↓reduceIte,ite_eq_right h']
  have wcap : w.val≤128 := by omega
  have wp : 2≤w.val := Nat.le_of_not_gt few
  change (do let v ← w * 4#usize; let u ← n / v
             let c := core.cmp.impls.OrdUsize.max u 4#usize
             let x ← n+c; let y ← x-1#usize; let k ← y/c; ok (some (c,k))) ⦃ _ => _ ⦄
  step as ⟨v,mul⟩
  step as ⟨u,quo⟩
  let c := core.cmp.impls.OrdUsize.max u 4#usize
  have cv : c.val = max u.val 4 := by
    change (if 4<u.val then u else 4#usize).val=_
    have four : (4#usize).val=4 := rfl
    split <;> omega
  have ud := Nat.div_le_self n.val v.val
  have cl : c.val≤512 := by omega
  have cp : 4≤c.val := by omega
  change (do let x ← n+c; let y ← x-1#usize; let k ← y/c; ok (some (c,k))) ⦃ _ => _ ⦄
  step as ⟨x,sum⟩
  step as ⟨y,sub⟩
  step as ⟨k,quot⟩
  simp [quot,sub,sum,cv,quo,mul,wval]

def runtimeAttempt {N : Usize} (threads n : Usize) (out : nativeShake.Rows N)
    (batch : Nat → Nat → Result (List (Array U8 N))) : Result (Bool × nativeShake.Rows N) := do
  let selected ← runtimePlan n threads
  match selected with
  | none => ok (false,out)
  | some (c,k) =>
    let rows ← assemble c.val (fun id => batch (id*c.val) (min (id*c.val+c.val) n.val-id*c.val)) out k.val
    ok (true,rows)

theorem runtimeAttempt_eq {N : Usize} (threads n : Usize) (out : nativeShake.Rows N)
    (batch : Nat → Nat → Result (List (Array U8 N))) (cap : n.val≤512) :
    runtimeAttempt threads n out batch = attempt threads.val n.val out batch := by
  obtain ⟨result,run,p⟩ := spec_imp_exists (runtimePlan_spec n threads cap)
  unfold runtimeAttempt attempt
  rw [run,bind_ok,← p]
  cases result with
  | none => rfl
  | some pair => cases pair; rfl

end slhdsa.cache.builder.workers.fill
