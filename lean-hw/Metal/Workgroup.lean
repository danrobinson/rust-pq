import Std

/-! The per-lane checker extracts the shared-memory accesses and ordered
barrier sites of each production kernel. This module composes its local
postconditions across all lanes of a threadgroup. Memory barriers have the
Metal threadgroup scope. Each dispatch has its own threadgroup allocation. -/
namespace Metal.Workgroup

structure Access where
  phase : Nat
  lane : Nat
  word : Nat
  write : Bool

/-- At phase 2k, active lanes publish one node each. At 2k+1, lanes
consume words from precisely that initialized prefix. -/
def Allowed (width active : Nat) (a : Access) : Prop :=
  if a.write then a.phase % 2 = 0 ∧ a.word / width = a.lane ∧ a.lane < active
  else a.phase % 2 = 1 ∧ a.word / width < active

theorem no_conflict {width active : Nat} {a b : Access}
    (ha : Allowed width active a) (hb : Allowed width active b)
    (together : a.phase = b.phase) (sameWord : a.word = b.word)
    (different : a.lane ≠ b.lane) : a.write = false ∧ b.write = false := by
  cases aw : a.write <;> cases bw : b.write <;>
    simp_all [Allowed]

/-- The checker requires every active lane to fill every word of its node at
the preceding barrier. Consequently every permitted read has a producer at
the *immediately preceding level*, including reads of authentication nodes. -/
theorem preceding_write {width active k word : Nat} (hw : 0 < width)
    (written : Nat → Nat → Nat → Prop)
    (complete : ∀ lane < active, ∀ i < width, written (2*k) lane (lane*width+i))
    (inside : word / width < active) :
    written (2*k) (word/width) word := by
  have h := complete (word / width) inside (word % width) (Nat.mod_lt _ hw)
  rwa [Nat.mul_comm (word/width) width, Nat.div_add_mod] at h

/-- All lanes compare each barrier to the same static site for its position;
equality of lengths alone would also admit lanes waiting at different sites. -/
def barrierSite (phase : Nat) :=
  if phase = 0 then 0 else if phase % 2 = 1 then 1 else 2

theorem uniform_barriers {a b : List Nat} {n : Nat}
    (ha : a.length = n) (hb : b.length = n)
    (siteA : ∀ i (inside : i < a.length), a[i] = barrierSite i)
    (siteB : ∀ i (inside : i < b.length), b[i] = barrierSite i) : a = b := by
  apply List.ext_getElem (ha.trans hb.symm)
  intro i ia ib
  exact (siteA i ia).trans (siteB i ib).symm

/-- The host lays out outputs in disjoint fixed-stride slices. These indices
also represent tree records, per-layer records and digest-sized blocks. -/
theorem separate_slots {width x y i j : Nat} (hi : i < width) (hj : j < width)
    (same : x*width+i = y*width+j) : x = y ∧ i = j := by
  by_cases h : x = y
  · subst y; exact ⟨rfl, by omega⟩
  · rcases Nat.lt_or_gt_of_ne h with lt | gt
    · have := Nat.mul_le_mul_right width (Nat.succ_le_of_lt lt)
      rw [Nat.succ_mul] at this; omega
    · have := Nat.mul_le_mul_right width (Nat.succ_le_of_lt gt)
      rw [Nat.succ_mul] at this; omega

end Metal.Workgroup
