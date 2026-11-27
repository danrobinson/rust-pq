import Parallel.PoolLease
namespace ParallelPool.Lease
open Borrow

/-- A topological ranking of the pool's program-order and synchronization edges.
It establishes irreflexivity without assuming a synchronized physical clock. -/
private def rank : Event → Nat
  | .claim e | .idleBefore e _ => 16*e
  | .initialize e => 16*e+1
  | .reset e | .park e _ => 16*e+2
  | .publish e _ => 16*e+3
  | .acquire e _ => 16*e+4
  | .copyJob e _ => 16*e+5
  | .useClosure e _ => 16*e+6
  | .idleAfter e _ => 16*e+7
  | .decrement e _ => 16*e+8
  | .join e => 16*e+9
  | .clear e => 16*e+10
  | .release e => 16*e+11
  | .endBorrow e => 16*e+12

private theorem forward {epochs} {a b} (ordered : HB epochs a b) : rank a < rank b := by
  induction ordered with
  | single edge => cases edge <;> simp [rank] <;> omega
  | trans _ _ ab bc => omega

inductive Write where
  | install (epoch : Nat)
  | clear (epoch : Nat)
  deriving DecidableEq

def Write.event : Write → Event
  | .install e => .initialize e
  | .clear e => .clear e

/-- The ordinary non-atomic job read observes a visible side effect. None
denotes the pool's initially empty cell. This is the external memory rule;
it mentions no preferred dispatch or closure identity. -/
def Visible (epochs : (e : Nat) → Epoch e) (read : Event) : Option Write → Prop
  | none => ∀ write : Write, ¬HB epochs write.event read
  | some source => HB epochs source.event read ∧
      ∀ middle : Write, HB epochs source.event middle.event → ¬HB epochs middle.event read

private theorem older_write {epochs : (e : Nat) → Epoch e} (co : Coherent epochs)
    {i e} (older : i<e) (clear : Bool) :
    HB epochs (if clear then Event.clear i else .initialize i) (.initialize e) := by
  let op : CellAccess := if clear then .clear else .initialize
  have order := job_cell_race_free epochs co i e op .initialize (by cases clear <;> trivial)
    (by trivial) (by intro eq; have := congrArg Prod.fst eq; simp at this;omega) (Or.inr rfl)
  rcases order with yes|no
  · cases clear <;> exact yes
  · have bad := forward no
    cases clear <;> simp [op,rank,CellAccess.event] at bad <;> omega

theorem visible_source (epochs : (e : Nat) → Epoch e) (co : Coherent epochs) (e w : Nat)
    (assigned : w < (epochs e).workers) (source : Option Write)
    (seen : Visible epochs (.copyJob e w) source) : source=some (.install e) := by
  have own := (borrow_lifetime epochs co e w assigned).1
  cases source with
  | none => exact False.elim (seen (.install e) own)
  | some source =>
    obtain ⟨before,latest⟩ := seen
    have age := forward before
    cases source with
    | install i =>
      by_cases earlier : i<e
      · exact False.elim (latest (.install e) (older_write co earlier false) own)
      · simp [Write.event,rank] at age
        congr 2
        omega
    | clear i =>
      simp [Write.event,rank] at age
      exact False.elim (latest (.install e) (older_write co (by omega : i<e) true) own)

def fromCell (p : Program) (object : Nat → Object) : Option Write → Option Value
  | some (.install e) => invoke p (object e)
  | _ => none

/-- The ordinary cell read cannot see the initial None, a clear, or a stale
job even when the caller reuses the same address for a different closure. -/
theorem dispatched_closure (epochs : (e : Nat) → Epoch e) (co : Coherent epochs)
    (object : Nat → Object) (e w : Nat) (assigned : w < (epochs e).workers)
    (source : Option Write) (seen : Visible epochs (.copyJob e w) source) (later : Nat) :
    fromCell production object source=some (.called (object e)) ∧
    HB epochs (.useClosure e w) (.endBorrow e) ∧ HB epochs (.useClosure e w) (.initialize (e+later+1)) := by
  rw [visible_source epochs co e w assigned source seen]
  exact ⟨exact_object _,(borrow_lifetime epochs co e w assigned).2.2,reuse epochs co e w assigned later⟩

end ParallelPool.Lease
