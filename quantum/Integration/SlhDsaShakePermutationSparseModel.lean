import Integration.SlhDsaShakePermutationSparsePort
import PQ.QROM.HybridPullback
import PQ.Interactive.QromBridgeEvalProg

/-! Pulling a port query through a bounded number of public, deterministic
cell selectors also pulls back its quantum query mass. This covers the
actual closed machine and charges three cells per full permutation query. -/
namespace Reduction.ShakePermutation.SparsePort
open Classical PQ.QROM PQ.Interactive ENNReal Quantum
open scoped Kronecker
noncomputable section
variable {X Y J R Leaf : Type} [Fintype X] [DecidableEq X] [DecidableEq Y]
  [Fintype J] [DecidableEq J] [DecidableEq R] {q : ℕ}
variable (M : HybridModel X Y Leaf q) (embed : J ↪ X) (map : (J → R) → X → Y) (rows : X → Finset J)

private def charge (G : J → R) (j : J) := ∑ x, if j ∈ rows x then M.mass (map G) x else 0

omit [DecidableEq X] [DecidableEq R] in
private theorem total (d : ℕ) (lim : ∀ x, (rows x).card ≤ d) (G : J → R) :
    ∑ j, charge M map rows G j ≤ d*q := by
  unfold charge
  rw [Finset.sum_comm,← Nat.cast_mul]
  calc
    _ = ∑ x, ((rows x).card : ℝ≥0∞) * M.mass (map G) x := by
      apply Finset.sum_congr rfl
      intro x _
      rw [← Finset.sum_filter]
      simp [nsmul_eq_mul]
    _ ≤ ∑ x, (d : ℝ≥0∞) * M.mass (map G) x :=
      Finset.sum_le_sum fun x _ => mul_le_mul' (Nat.cast_le.mpr (lim x)) le_rfl
    _ ≤ _ := by rw [← Finset.mul_sum,Nat.cast_mul]; exact mul_le_mul' le_rfl (M.mass_sum_le _)

omit [DecidableEq X] in
private theorem diff (locality : ∀ H G x, map H x ≠ map G x → ∃ j ∈ rows x, H j ≠ G j) (H G : J → R) :
    ∑ x ∈ Finset.univ.filter (fun x => map H x ≠ map G x), M.mass (map G) x ≤
      ∑ j ∈ Finset.univ.filter (fun j => H j ≠ G j), charge M map rows G j := by
  unfold charge
  rw [Finset.sum_comm,Finset.sum_filter]
  apply Finset.sum_le_sum
  intro x _
  split_ifs with h
  · obtain ⟨j,hj,ne⟩ := locality H G x h
    have m := Finset.single_le_sum (f := fun k => if k ∈ rows x then M.mass (map G) x else 0)
      (fun _ _ => zero_le) (show j ∈ Finset.univ.filter (fun k => H k ≠ G k) from Finset.mem_filter.mpr ⟨Finset.mem_univ j,ne⟩)
    simpa only [ite_eq_left hj] using m
  · exact zero_le

/-- Hybrid model for an oracle rebuilt from at most d ideal table cells
per public input, with dependence allowed on the entire public input. -/
def model (d : ℕ) (hd : 1 ≤ d) (lim : ∀ x, (rows x).card ≤ d)
    (locality : ∀ H G x, map H x ≠ map G x → ∃ j ∈ rows x, H j ≠ G j) : HybridModel J R Leaf (d*q) where
  prob H := M.prob (map H)
  prob_mono H := M.prob_mono (map H)
  prob_sub H := (M.pullback embed (fun _ : J → R => map H) (by intros; contradiction)).prob_sub H
  prob_sum_le H := (M.pullback embed (fun _ : J → R => map H) (by intros; contradiction)).prob_sum_le H
  mass := charge M map rows
  mass_sum_le H := by rw [Nat.cast_mul]; exact total M map rows d lim H
  hybrid H G E := by
    apply (M.hybrid (map H) (map G) E).trans
    gcongr
    · exact_mod_cast (show q ≤ d*q by simpa using Nat.mul_le_mul_right q hd)
    · exact diff M map rows locality H G
  hybrid' H G E := by
    apply (M.hybrid' (map H) (map G) E).trans
    gcongr
    · exact_mod_cast (show q ≤ d*q by simpa using Nat.mul_le_mul_right q hd)
    · exact diff M map rows locality H G

variable {Z : Type} [DecidableEq Z]
variable (e : Words ≃ R × Z) (a : J ↪ Words) (π : Permutation) (suffix : J → Z) (base : J)

def simulatedPort (F : J → R) (p : Port) := eval e a π suffix p (value e a π suffix F base p)

def publicModel (N : HybridModel Port Words Leaf q) : HybridModel J R Leaf (3*q) :=
  let sel (p : Port) (i : Fin 3) := (slot e a π suffix p i).getD base
  model N (a.trans ⟨fun w => (false,w),fun _ _ eq => congrArg Prod.snd eq⟩)
    (simulatedPort e a π suffix base) (fun p => Finset.univ.image (sel p)) 3 (by decide)
    (fun p => Finset.card_image_le.trans_eq (Fintype.card_fin 3)) (by
      intro H G p ne
      by_contra! same
      apply ne
      apply congrArg (eval e a π suffix p)
      exact funext (fun i => same _ (Finset.mem_image_of_mem (sel p) (Finset.mem_univ i))))

theorem publicModel_prob (N : HybridModel Port Words Leaf q) (F : J → R) (E : Leaf → Prop) :
    (publicModel e a π suffix base N).prob F E = N.prob (simulatedPort e a π suffix base F) E := rfl

end
end Reduction.ShakePermutation.SparsePort
#print axioms Reduction.ShakePermutation.SparsePort.publicModel
