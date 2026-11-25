import Armwide.RecoveryControl
import Armwide.RecoveryFrame
namespace slhdsa.Armwide.Recovery
open WotsRefill
def budget (ls : List RecoverLane) (q : List Nat) := q.length*16+(ls.map (·.left)).sum

theorem budget_measure (ls : List RecoverLane) (q : List Nat) : budget ls q = recoverMeasure ls q := by
  have fold (xs : List RecoverLane) (i : Nat) :
      xs.foldl (fun acc l => acc+l.left) i = i+(xs.map (·.left)).sum := by
    induction xs generalizing i with
    | nil => simp
    | cons l rest ih => simp [ih,Nat.add_assoc]
  simp [budget,recoverMeasure,recoverSumLeft,fold]

private theorem retire_limits {O : Type} (write : O → Nat → Spec.Bytes → O) (sig : Nat → Spec.Bytes)
    (d : Nat → Nat) (ls : List RecoverLane) (q : List Nat) (out : O) (queued : ∀ c∈q,d c<15) :
    let r := retire write sig d ls q out
    budget r.1 r.2.1≤budget ls q ∧ (∀ l∈r.1,0<l.left) ∧ (∀ c∈r.2.1,d c<15) := by
  induction ls generalizing q out with
  | nil => simpa [retire] using queued
  | cons l ls ih =>
    unfold retire
    split
    · cases q with
      | nil =>
        obtain ⟨b,g,h⟩ := ih [] (write out l.chain l.x) queued
        simp only [budget,List.map_cons,List.sum_cons,List.length_nil] at b ⊢
        exact ⟨by omega,g,h⟩
      | cons c rest =>
        obtain ⟨b,g,h⟩ := ih rest (write out l.chain l.x) (fun i hi => queued i (List.mem_cons_of_mem _ hi))
        have hc := queued c List.mem_cons_self
        generalize eqn : retire write sig d ls rest (write out l.chain l.x) = result at b g h ⊢
        obtain ⟨new,more,val⟩ := result
        simp only [budget,List.map_cons,List.sum_cons,List.length_cons,Nat.succ_mul,fresh] at b ⊢
        simp only [eqn]
        refine ⟨by omega,?_,h⟩
        intro x hx;rcases List.mem_cons.mp hx with rfl|mem
        · dsimp;omega
        · exact g _ mem
    · obtain ⟨b,g,h⟩ := ih q out queued
      generalize eqn : retire write sig d ls q out = result at b g h ⊢
      obtain ⟨new,more,val⟩ := result
      simp only [budget,List.map_cons,List.sum_cons] at b ⊢
      refine ⟨by omega,?_,h⟩
      intro x hx;rcases List.mem_cons.mp hx with rfl|mem
      · omega
      · exact g _ mem

private theorem advanced_budget (n st a k ls q) (positive : 0<k) (nonempty : ls≠[])
    (live : ∀ l∈ls,0<l.left) : budget (advance n st a k ls) q < budget ls q := by
  have counts : ((advance n st a k ls).map (·.left))=ls.map (fun l => l.left-k) := by
    apply List.ext_getElem (by simp [advance])
    intro i hi hj;simp [advance]
  have weak (xs : List RecoverLane) : (xs.map (fun l => l.left-k)).sum≤(xs.map (·.left)).sum := by
    induction xs with
    | nil => rfl
    | cons x rest ih => simp only [List.map_cons,List.sum_cons];omega
  unfold budget
  rw [counts]
  obtain ⟨l,t,rfl⟩ := List.exists_cons_of_ne_nil nonempty
  have h := live l List.mem_cons_self
  have b := weak t
  simp only [List.map_cons,List.sum_cons]; omega

/-- Mirrors the production loop guards and records whether execution reaches an empty
active set before exhausting the structural recursion budget. -/
def drained {O : Type} (write : O → Nat → Spec.Bytes → O) (n : Nat) (st : List Spec.SHA256.Word)
    (a : Spec.Adrs) (sig : Nat → Spec.Bytes) (d : Nat → Nat)
    (ls : List RecoverLane) (q : List Nat) (out : O) : Nat → Bool
  | 0 => false
  | fuel+1 =>
    if ls.length=4 then
      let result := retire write sig d (advance n st a (minLeft ls) ls) q out
      drained write n st a sig d result.1 result.2.1 result.2.2 fuel
    else if ls.length>0 then
      let result := retire write sig d (advance n st a 1 ls) [] out
      drained write n st a sig d result.1 q result.2.2 fuel
    else true

theorem drained_before_exhaustion {O : Type} (write : O → Nat → Spec.Bytes → O)
    (n st a sig d ls q) (out : O) (fuel : Nat)
    (live : ∀ l∈ls,0<l.left) (waits : ∀ c∈q,d c<15) (time : budget ls q<fuel) :
    drained write n st a sig d ls q out fuel=true := by
  induction fuel generalizing ls q out with
  | zero => omega
  | succ fuel ih =>
    unfold drained
    split
    · rename_i four
      have ne : ls≠[] := by intro eq;simp [eq] at four
      have pos (xs : List RecoverLane) (nonempty : xs≠[]) (good : ∀ l∈xs,0<l.left) : 0<minLeft xs := by
        induction xs with
        | nil => contradiction
        | cons h t ht =>
          cases t with
          | nil => exact good h (by simp)
          | cons x r =>
            exact Nat.lt_min.mpr ⟨good h (by simp),ht (by simp) (fun z hz => good z (List.mem_cons_of_mem _ hz))⟩
      have b := advanced_budget n st a (minLeft ls) ls q (pos ls ne live) ne live
      obtain ⟨lower,al,qs⟩ := retire_limits write sig d (advance n st a (minLeft ls) ls) q out waits
      let r := retire write sig d (advance n st a (minLeft ls) ls) q out
      apply ih r.1 r.2.1 r.2.2 al qs
      exact Nat.lt_of_le_of_lt lower (by omega)
    · split
      · rename_i some
        have ne : ls≠[] := by intro eq;simp [eq] at some
        have b := advanced_budget n st a 1 ls [] (by decide) ne live
        obtain ⟨lower,al,_⟩ := retire_limits write sig d (advance n st a 1 ls) [] out (by simp)
        let r := retire write sig d (advance n st a 1 ls) [] out
        apply ih r.1 q r.2.2 al waits
        dsimp only [r]
        unfold budget at lower b time ⊢;simp only [List.length_nil,Nat.zero_mul,Nat.zero_add] at lower b
        omega
      · rfl

/-- The exact budget chosen by `completeRows` covers the compiled hot and tail
loops for any sorted order of chains selected by the production bucket sort. -/
theorem complete_drains (n st a sig d) (ord : List Nat) (buf : Spec.Bytes)
    (waits : ∀ i∈ord,d i<15) :
    let active := (ord.take 4).map (fresh sig d)
    let queue := ord.drop 4
    drained (writeAt n) n st a sig d active queue buf (recoverMeasure active queue+1)=true := by
  apply drained_before_exhaustion
  · intro l mem
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp mem
    have h := waits j (List.mem_of_mem_take hj)
    dsimp [fresh];omega
  · intro c hc;exact waits c (List.mem_of_mem_drop hc)
  · rw [budget_measure];omega

end slhdsa.Armwide.Recovery
