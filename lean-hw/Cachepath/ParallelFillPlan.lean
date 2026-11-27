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

/-- Connect the representative used by the public constructor to the complete
worker ledger. Each real batch may be published in any order. The result
after reading all OnceLocks is the same bit-for-bit slice and success flag. -/
theorem runtime_join {N : Usize} (threads n c k : Usize) (out : nativeShake.Rows N)
    (batch : Nat → Nat → Result (List (Array U8 N)))
    (selected : runtimePlan n threads = ok (some (c,k)))
    (successful : ∀ id<k.val, ∃ data, batch (id*c.val) (min (id*c.val+c.val) n.val-id*c.val)=ok data) :
    ∃ payload : Nat → List (Array U8 N),
      (∀ id<k.val, batch (id*c.val) (min (id*c.val+c.val) n.val-id*c.val)=ok (payload id)) ∧
      ∀ cells, ParallelCached.Run k.val (fun id => [(id,payload id)]) k.val [] cells →
        (do let rows ← assemble c.val (fun i => match cells i with
                | some v => ok v | none => fail .panic) out k.val
            ok (true, rows)) = runtimeAttempt threads n out batch := by
  classical
  let payload (id : Nat) := if h : id<k.val then (successful id h).choose else []
  have values (id : Nat) (h : id<k.val) :
      batch (id*c.val) (min (id*c.val+c.val) n.val-id*c.val)=ok (payload id) := by
    simpa only [payload,dite_eq_left h] using (successful id h).choose_spec
  refine ⟨payload,values,?_⟩
  intro cells run
  unfold runtimeAttempt
  rw [selected,bind_ok]
  simp only
  exact congrArg (fun computation : Result (nativeShake.Rows N) => do
      let rows ← computation
      ok (true,rows))
    (assemble_join c.val k.val (fun id => batch (id*c.val) (min (id*c.val+c.val) n.val-id*c.val)) payload out run values)

end slhdsa.cache.builder.workers.fill
