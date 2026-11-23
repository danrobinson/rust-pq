import Wots.Ownership
import Mathlib.Algebra.Order.BigOperators.Group.Finset
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.Wots

def laneWork (mask : U16) (counter : Reg) (j : Fin 16) :=
  if enabled mask j then 15 - (counter j).toNat else 0

/-- An advance of the queue cursor outweighs even sixteen newly loaded lanes. -/
def remainingWork (work pos : Usize) (mask : U16) (counter : Reg) :=
  241 * (work.val-pos.val) + Finset.univ.sum (laneWork mask counter)

private theorem lanes_bound (mask : U16) (counter : Reg) :
    Finset.univ.sum (laneWork mask counter) ≤ 240 := by
  calc
    _ ≤ Finset.univ.sum (fun _ : Fin 16 => 15) := by
      apply Finset.sum_le_sum
      intro j _
      unfold laneWork
      split <;> omega
    _ = 240 := by simp

private theorem bit_witness {m : U16} (on : m ≠ 0#u16) : ∃ j, enabled m j = true := by
  have nz : m.bv ≠ 0 := by
    intro e; apply on; apply UScalar.eq_of_val_eq; exact congrArg BitVec.toNat e
  exact ⟨⟨_,BitVec.ctz_lt_iff_ne_zero.mpr nz⟩,BitVec.getLsbD_true_ctz_of_ne_zero nz⟩

theorem no_refill {digits order ix st active pos ix' st' mask next assigned}
    (fill : mapped digits order ix st active pos (ix',st',mask,next,assigned))
    (same : next.val = pos.val) : mask = active ∧ assigned = 0#u16 := by
  obtain ⟨job,_,_,lanes⟩ := fill
  have off (j) : enabled assigned j = false ∧ enabled mask j = enabled active j := by
    have h := lanes j
    cases e : job j with
    | none => rw [e] at h; exact ⟨h.1,h.2.1⟩
    | some q => rw [e] at h; have := h.1; have := h.2.1; omega
  constructor
  · apply UScalar.eq_of_val_eq
    apply congrArg BitVec.toNat
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    exact (off ⟨k,hk⟩).2
  · by_contra h
    obtain ⟨j,on⟩ := bit_witness h
    simp_all [off j]

/-- The scheduler guard, refill postcondition, and hardware completion mask imply
strict descent. If the cursor stays put, at least one live counter advances. -/
theorem recovery_descent {digits order ix st active pos ix' st' mask next assigned}
    (fill : mapped digits order ix st active pos (ix',st',mask,next,assigned))
    (work : Usize) (cap : next.val ≤ work.val)
    (stop : mask = core.num.U16.MAX ∨ next = work) (guard : active ≠ 0#u16 ∨ pos < work)
    (before loaded after : Reg) (survivors : U16)
    (keep : assigned = 0#u16 → loaded = before)
    (valid : ∀ j, enabled active j = true → (before j).toNat < 15)
    (inc : ∀ j, after j = loaded j + 1)
    (bits : ∀ j, enabled survivors j = true ↔ enabled mask j = true ∧ after j ≠ 15) :
    remainingWork work next survivors after < remainingWork work pos active before := by
  by_cases eq : next.val = pos.val
  · obtain ⟨maskEq,zero⟩ := no_refill fill eq
    subst mask
    have loadedEq := keep zero
    subst loaded
    have on : active ≠ 0#u16 := by
      rcases guard with on|pending
      · exact on
      · rcases stop with full|done
        · rw [full]; decide
        · change pos.val < work.val at pending
          subst next; omega
    obtain ⟨live,yes⟩ := bit_witness on
    have step (j) (yes : enabled active j = true) :
        laneWork survivors after j < laneWork active before j := by
      have small := valid j yes
      have add : (after j).toNat = (before j).toNat + 1 := by
        rw [inc,BitVec.toNat_add]; change (_ + 1) % (2^32) = _
        apply Nat.mod_eq_of_lt; omega
      simp only [laneWork,yes,ite_true]
      split <;> omega
    unfold remainingWork
    rw [eq]
    apply Nat.add_lt_add_left
    apply Finset.sum_lt_sum
    · intro j _
      cases h : enabled active j with
      | true => exact Nat.le_of_lt (step j h)
      | false =>
        have off : enabled survivors j = false := by
          cases hs : enabled survivors j with
          | false => rfl
          | true => have := ((bits j).mp hs).1; simp_all
        simp [laneWork,h,off]
    · exact ⟨live,Finset.mem_univ _,step live yes⟩
  · have le := fill.choose_spec.1
    have h := lanes_bound survivors after
    unfold remainingWork
    omega

end slhdsa.X86.Wots
