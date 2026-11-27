import Cachepath.Constructor
open Aeneas Aeneas.Std Result
open slhdsa.cache.endtoend
namespace slhdsa.cache.builder

def width (H z : Nat) := 2^(H-z)

theorem next {H z : Nat} (hz : z ≤ H) :
    levelOff H (z+1) = levelOff H z + width H z := by
  have a : H+1-z = (H-z)+1 := by omega
  have b : H+1-(z+1) = H-z := by omega
  have c : 2^((H-z)+1) ≤ 2^(H+1) := Nat.pow_le_pow_right (by decide) (by omega)
  simp only [levelOff,width,a,b,pow_succ] at *
  omega

theorem off_mono (H : Nat) {z y : Nat} (le : z ≤ y) : levelOff H z ≤ levelOff H y :=
  Nat.sub_le_sub_left (Nat.pow_le_pow_right (by decide) (by omega)) _

theorem row_bound {H z i : Nat} (hz : z ≤ H) (hi : i < width H z) :
    levelOff H z + i < treeSize H := by
  have endOff : levelOff H (H+1) = treeSize H := by simp [levelOff,treeSize]
  have := off_mono H (show z+1 ≤ H+1 by omega)
  rw [endOff,next hz] at this
  omega

private theorem unique_row {H z i y j : Nat} (hz : z ≤ H) (hy : y ≤ H)
    (hi : i < width H z) (hj : j < width H y)
    (eq : levelOff H z + i = levelOff H y + j) : z = y ∧ i = j := by
  rcases lt_trichotomy z y with h|h|h
  · have := off_mono H (show z+1 ≤ y by omega)
    rw [next hz] at this
    omega
  · subst y; omega
  · have := off_mono H (show y+1 ≤ z by omega)
    rw [next hy] at this
    omega

/-- The expected byte string at a flat-buffer position. The proof of uniqueness
uses the actual level_offset formula, including the transition into the root row. -/
noncomputable def expected (H : Nat) (node : Nat → Nat → Spec.Bytes) (slot : Nat) : Spec.Bytes :=
  open Classical in
  if h : ∃ coord : Nat × Nat, coord.1 ≤ H ∧ coord.2 < width H coord.1 ∧
      levelOff H coord.1 + coord.2 = slot then node h.choose.1 h.choose.2 else []

theorem expected_at (node : Nat → Nat → Spec.Bytes) {H z i : Nat} (hz : z ≤ H)
    (hi : i < width H z) :
    expected H node (levelOff H z + i) = node z i := by
  classical
  unfold expected
  split
  · rename_i h
    obtain ⟨hz',hi',eq⟩ := h.choose_spec
    obtain ⟨a,b⟩ := unique_row hz' hz hi' hi eq
    rw [a,b]
  · rename_i h
    exact (h ⟨(z,i),hz,hi,rfl⟩).elim

abbrev Nodes (N : Usize) := alloc.vec.Vec (Array U8 N)
def Prefix {N : Usize} (v : Nodes N) (f : Nat → Spec.Bytes) (k : Nat) :=
  ∀ j < k, bytes v.val[j]!.val = f j

theorem set_prefix {N : Usize} {v : Nodes N} {f : Nat → Spec.Bytes} {k : Usize}
    {b : Array U8 N} (bound : k.val < v.length) (prev : Prefix v f k.val)
    (fresh : bytes b.val = f k.val) : Prefix (v.set k b) f (k.val+1) := by
  intro j hj
  have hj' : j < v.val.length := by change k.val < v.val.length at bound; omega
  rw [alloc.vec.Vec.set_val_eq]
  rw [getElem!_pos _ _ (by simpa using hj'), List.getElem_set]
  split
  · rename_i eq; subst j; exact fresh
  · have old := prev j (by omega)
    simpa only [getElem!_pos v.val j hj'] using old

theorem contents {N : Usize} {v : Nodes N} (p : Spec.Params) (sk pk : Spec.Bytes)
    (a : Spec.Adrs) (complete : Prefix v
      (expected p.hp (fun z i => Spec.xmssNode p sk i z pk a)) (treeSize p.hp)) :
    Built (alloc.vec.Vec.deref v) p sk pk a := by
  have correct (z i : Nat) (hz : z ≤ p.hp) (hi : i < width p.hp z) :
      cachedNode (alloc.vec.Vec.deref v) p.hp z i = Spec.xmssNode p sk i z pk a := by
    have := complete _ (row_bound hz hi)
    rw [expected_at _ hz hi] at this
    simpa [cachedNode,vec_deref_val, levelOff] using this
  constructor
  · intro i hi
    exact correct 0 i (by omega) (by simpa [width] using hi)
  · intro z hz i hi
    have w : width p.hp z = width p.hp (z+1) * 2 := by
      simp only [width]
      rw [show p.hp - z = (p.hp - (z+1)) + 1 by omega,pow_succ]
    change i < width p.hp (z+1) at hi
    rw [correct (z+1) i (by omega) hi,Spec.xmssNode,
      correct z (2*i) (by omega) (by omega),correct z (2*i+1) (by omega) (by omega)]

end slhdsa.cache.builder
