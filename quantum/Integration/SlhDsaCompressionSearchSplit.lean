import Integration.SlhDsaCompressionPreimage

namespace Reduction.Compression
open MLink Ideal SLHDSA OracleComp OracleSpec PQ.Interactive Quantum ENNReal
open SetOracle (uniformMean)
open scoped ComplexOrder

private def reportedCell : Option HmacKey.Evidence → HmacKey.InputCell
  | some (.inl u) => u
  | _ => default

private def reportedPair : Option HmacKey.Evidence → Option (ClassCollision.Cell × ClassCollision.Cell)
  | some (.inr p) => some p
  | _ => none

private def reportedPre (g : CompressionTables) (i : Chain512) : Option HmacKey.Evidence → Prop
  | some (.inl u) => g.2 u = i
  | _ => False

variable (S : Sha2Set) {E : Type} [Fintype E] [DecidableEq E]
local notation "Work" => WS Input Output E

private theorem split_weight (g : CompressionTables) (i : Chain512)
    (X : Closed Work (Option HmacKey.Evidence)) (ρ : Matrix Work Work ℂ) :
    @qWeight _ _ _ (searchWin S g i) (Classical.decPred _) X ρ ≤
    qWeight (fun z => g.2 (reportedCell z) = i) X ρ +
    @qWeight _ _ _ (ClassCollision.collision S g) (Classical.decPred _) (reportedPair <$> X) ρ := by
  classical
  let P := reportedPre g i
  let C := fun z => ClassCollision.collision S g (reportedPair z)
  have disj : ∀ z, P z → ¬ C z := by
    rintro (_ | u | p) <;> simp [P,C,reportedPre,reportedPair,ClassCollision.collision]
  have incl : ∀ z, P z → g.2 (reportedCell z) = i := by
    rintro (_ | u | p) <;> simp [P,reportedPre,reportedCell]
  have eq : ∀ z, searchWin S g i z ↔ P z ∨ C z := by
    rintro (_ | u | ⟨u,v⟩) <;> simp [searchWin,P,C,reportedPre,reportedPair,ClassCollision.collision]
  rw [qWeight_map]
  calc
    _ = qWeight (fun z => P z ∨ C z) X ρ := qWeight_congr_ev eq _ _
    _ = _ := qWeight_or disj X ρ
    _ ≤ _ := add_le_add (qWeight_mono incl X ρ) le_rfl

private theorem swap_mean {X Y : Type} [Fintype X] [Fintype Y] (f : X → Y → ℝ≥0∞) :
    uniformMean (fun x => uniformMean (f x)) = uniformMean (fun y => uniformMean (fun x => f x y)) := by
  simp only [uniformMean,unifW, ← Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm, mul_comm (Fintype.card X : ℝ≥0∞)⁻¹]

/-- It suffices to bound prefix collisions of a target-independent public-port
machine. Revealing an independent full chaining state costs a Grover preimage term. -/
theorem search_le_of_prefix (ρ : Matrix Work Work ℂ) (hp : ρ.PosSemidef) (ht : ρ.trace = 1)
    (q : ℕ) (ε : ℝ≥0∞)
    (hprefix : ∀ M : (Input → Output) → Closed Work (Option (ClassCollision.Cell × ClassCollision.Cell)),
      PUE (spec := unifSpec) cnt0 M q → uniformMean (fun g : CompressionTables =>
        @qWeight _ _ _ (ClassCollision.collision S g) (Classical.decPred _) (M (oracle g)) ρ) ≤ ε) :
    searchRisk S ρ q ≤ (2*(q:ℝ≥0∞)+1)^2 / 2^512 + ε := by
  classical
  apply iSup_le
  intro A
  let p := fun (g : CompressionTables) (i : Chain512) =>
    qWeight (fun z => g.2 (reportedCell z) = i) (A.val i (oracle g)) ρ
  let c := fun (g : CompressionTables) (i : Chain512) =>
    @qWeight _ _ _ (ClassCollision.collision S g) (Classical.decPred _) (reportedPair <$> A.val i (oracle g)) ρ
  have pre : uniformMean (fun g => uniformMean (p g)) ≤ _ :=
    preimage_shared A.val (fun _ => reportedCell) ρ hp ht q A.property
  have col : uniformMean (fun g => uniformMean (c g)) ≤ ε := by
    rw [swap_mean c]
    calc
      _ ≤ ∑ i : Chain512, unifW _ i * ε := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul' le_rfl (hprefix (fun H => reportedPair <$> A.val i H) (PUE.map _ (A.property i)))
      _ = _ := by rw [← Finset.sum_mul, sum_unifW, one_mul]
  apply le_trans _ (add_le_add pre col)
  simp only [uniformMean, ← Finset.sum_add_distrib, ← mul_add]
  exact Finset.sum_le_sum fun g _ => mul_le_mul' le_rfl (Finset.sum_le_sum fun i _ =>
    mul_le_mul' le_rfl (split_weight S g i _ ρ))

end Reduction.Compression
#print axioms Reduction.Compression.search_le_of_prefix
