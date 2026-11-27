import Armwide.FusedNative
namespace slhdsa.Armwide.Transitions
open WotsRefill Spec.SHA256
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000

variable {α β : Type} (w : Writer α) (v : Writer β) (f : α → β) (P : Spec.Bytes → Prop)
  (writes : ∀ o c x, P x → v (f o) c x = f (w o c x))

include writes

private theorem fold_writes {γ : Type} (l : List γ) (c : γ → Nat) (x : γ → Spec.Bytes) (o : α) (payload : ∀ e ∈ l, P (x e)) :
    l.foldl (fun acc e => v acc (c e) (x e)) (f o) =
      f (l.foldl (fun acc e => w acc (c e) (x e)) o) := by
  induction l generalizing o with
  | nil => rfl
  | cons h t ih =>
    rw [List.foldl_cons,List.foldl_cons,writes _ _ _ (payload h (by simp))]
    exact ih _ (fun e h => payload e (by simp [h]))

def map3 {γ δ : Type} (f : α → β) (t : γ × δ × α) := (t.1,t.2.1,f t.2.2)

private theorem update_sim (sk : Spec.Bytes) (d : Nat → Nat) (shared : Bool) (k : Nat)
    (r : Stepping) (q : List Nat) (o : α) (good : P r.digest) :
    transitionWith v sk d shared k r q (f o) = map3 f (transitionWith w sk d shared k r q o) := by
  simp only [transitionWith,map3,Prod.mk.injEq,true_and]
  exact fold_writes w v f P writes _ _ _ _ (fun _ _ => good)

private theorem uncompacted_sim (sk : Spec.Bytes) (d : Nat → Nat) (shared : Bool) (k : Nat)
    (ls : List Stepping) (q : List Nat) (o : α) (good : ∀ r ∈ ls, P r.digest) :
    uncompactedWith v sk d shared k ls q (f o) = map3 f (uncompactedWith w sk d shared k ls q o) := by
  induction ls generalizing q o with
  | nil => rfl
  | cons l ls ih =>
    simp only [uncompactedWith,update_sim w v f P writes _ _ _ _ l _ o (good _ (by simp)),map3,
      ih _ _ (fun r h => good r (by simp [h]))]

private theorem compact_sim (sk : Spec.Bytes) (d : Nat → Nat) (shared : Bool) (k : Nat)
    (ls : List Stepping) (q : List Nat) (o : α) (good : ∀ r ∈ ls, P r.digest) :
    compactWithWriter v sk d shared k ls q (f o) = map3 f (compactWithWriter w sk d shared k ls q o) := by
  unfold compactWithWriter
  rw [uncompacted_sim w v f P writes _ _ _ _ _ _ _ good]
  rfl

omit writes in
private theorem steps_good (n : Nat) (st : List Word) (a : Spec.Adrs) (ls : List SignLane) (m : Mode)
    (all : ∀ regs, P (outputDigest n regs)) : ∀ r ∈ steps n st a ls m, P r.digest := by
  intro r h
  obtain ⟨i,hi,e⟩ := List.mem_iff_getElem.mp h
  rw [←e]
  simp only [steps,List.getElem_ofFn]
  apply all

private theorem tail_sim (n : Nat) (st : List Word) (a : Spec.Adrs) (ls : List SignLane) (o : α) (all : ∀ regs, P (outputDigest n regs)) :
    tailWith v n st a ls (f o) = ((tailWith w n st a ls o).1,f (tailWith w n st a ls o).2) := by
  simp only [tailWith,tailWithWriter,Prod.mk.injEq,true_and]
  apply fold_writes w v f P writes
  intro e h
  rw [active_step] at h
  simp only [blueprint] at h
  split at h
  · obtain ⟨i,member,equal⟩ := List.mem_map.mp h
    have bound := List.mem_range.mp (List.mem_filter.mp member).1
    subst e
    apply steps_good P _ _ _ _ _ all
    rw [getElem!_pos _ _ (by simpa only [steps,List.length_ofFn,chooseMixed,lanes,width] using bound)]
    exact List.getElem_mem ..
  · contradiction

private theorem full_sim (n : Nat) (st : List Word) (sk : Spec.Bytes) (a : Spec.Adrs) (d : Nat → Nat)
    (ls : List SignLane) (q : List Nat) (o : α) (all : ∀ regs, P (outputDigest n regs)) :
    fourWith v n st sk a d ls q (f o) = map3 f (fourWith w n st sk a d ls q o) := by
  unfold fourWith
  split <;> apply compact_sim w v f P writes <;> exact steps_good P _ _ _ _ _ all

/-- Running the register scheduler with any signature storage representation. -/
def writeRun {α : Type} (writer : Writer α) (n : Nat) (st : List Word) (sk : Spec.Bytes)
    (a : Spec.Adrs) (d : Nat → Nat) (ls : List SignLane) (q : List Nat) (o : α) : Nat → α
  | 0 => o
  | fuel+1 =>
    if ls.length=4 then
      let (ls',q',o') := fourWith writer n st sk a d ls q o
      writeRun writer n st sk a d ls' q' o' fuel
    else if 0 < ls.length then
      let (ls',o') := tailWith writer n st a ls o
      writeRun writer n st sk a d ls' q o' fuel
    else o

theorem writes_sim_on (n : Nat) (st : List Word) (sk : Spec.Bytes) (a : Spec.Adrs) (d : Nat → Nat)
    (ls : List SignLane) (q : List Nat) (o : α) (fuel : Nat) (all : ∀ regs, P (outputDigest n regs)) :
    writeRun v n st sk a d ls q (f o) fuel = f (writeRun w n st sk a d ls q o fuel) := by
  induction fuel generalizing ls q o with
  | zero => rfl
  | succ k ih =>
    simp only [writeRun]
    split
    · rw [full_sim w v f P writes _ _ _ _ _ _ _ _ all]
      exact ih .. 
    · split
      · rw [tail_sim w v f P writes _ _ _ _ _ all]
        exact ih ..
      · rfl

omit writes

theorem writes_sim (agree : ∀ o c x, v (f o) c x = f (w o c x)) (n : Nat) (st : List Word) (sk : Spec.Bytes)
    (a : Spec.Adrs) (d : Nat → Nat) (ls : List SignLane) (q : List Nat) (o : α) (fuel : Nat) :
    writeRun v n st sk a d ls q (f o) fuel = f (writeRun w n st sk a d ls q o fuel) :=
  writes_sim_on w v f (fun _ => True) (fun o c x _ => agree o c x) n st sk a d ls q o fuel (fun _ => trivial)

theorem writes_table (n : Nat) (st : List Word) (sk : Spec.Bytes) (a : Spec.Adrs) (d : Nat → Nat)
    (ls : List SignLane) (q : List Nat) (o : Nat → Spec.Bytes) (fuel : Nat) :
    writeRun setOut n st sk a d ls q o fuel = signRunUsing (four n st sk a d) (tail n st a) ls q o fuel := by
  induction fuel generalizing ls q o with
  | zero => rfl
  | succ k ih =>
    simp only [writeRun,signRunUsing,four,tail]
    split
    · apply ih
    · split
      · apply ih
      · rfl

end slhdsa.Armwide.Transitions
