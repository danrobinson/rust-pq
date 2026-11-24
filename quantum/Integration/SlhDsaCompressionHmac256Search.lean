import Integration.SlhDsaCompressionHmac256Preimage
import Integration.SlhDsaCompressionHmac256Monitor
import Integration.SlhDsaCompressionLeftPrefix

namespace Reduction.Compression.Hmac256
open MLink Ideal SLHDSA OracleComp OracleSpec PQ.Interactive Quantum ENNReal
open Recording.Compile
open SetOracle (uniformMean)
open scoped ComplexOrder

private def cell : Option Evidence → InputCell
  | some (.inl u) => u
  | _ => default

private def pair : Option Evidence → Option (InputCell × InputCell)
  | some (.inr uv) => some uv
  | _ => none

variable {E : Type} [Fintype E] [DecidableEq E]
local notation "Work" => WS Input Output E

private theorem split_weight (g : CompressionTables) (i : St) (X : Closed Work (Option Evidence))
    (ρ : Matrix Work Work ℂ) :
    qWeight (fun z => acceptsEvidence g i z = true) X ρ ≤
      qWeight (fun z => g.1 (cell z) = i) X ρ +
      @qWeight _ _ _ (fun z => LeftPort.wins id g (pair z)) (Classical.decPred _) X ρ := by
  classical
  let P : Option Evidence → Prop
    | some (.inl u) => g.1 u = i
    | _ => False
  let C := fun z => LeftPort.wins id g (pair z)
  have disj : ∀ z, P z → ¬ C z := by rintro (_ | u | ⟨u,v⟩) <;> simp [P,C,pair,LeftPort.wins]
  have incl : ∀ z, P z → g.1 (cell z) = i := by rintro (_ | u | ⟨u,v⟩) <;> simp [P,cell]
  have he : ∀ z, acceptsEvidence g i z = true ↔ P z ∨ C z := by
    rintro (_ | u | ⟨u,v⟩) <;> simp [acceptsEvidence,P,C,pair,LeftPort.wins]
  calc _ = qWeight (fun z => P z ∨ C z) X ρ := qWeight_congr_ev he _ _
       _ = _ := qWeight_or disj X ρ
       _ ≤ _ := add_le_add (qWeight_mono incl X ρ) le_rfl

private theorem switch {X Y : Type} [Fintype X] [Fintype Y] (f : X → Y → ℝ≥0∞) :
    uniformMean (fun x => uniformMean (f x)) = uniformMean (fun y => uniformMean (fun x => f x y)) := by
  simp only [uniformMean,unifW, ← Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm,mul_comm (Fintype.card X : ℝ≥0∞)⁻¹]

/-- The monitored inner digest collides only if a machine extracts a preimage of
its independently sampled chaining state or a collision in the full SHA-256 output. -/
theorem inner_search (A : (Input → Output) → QOC Work (PRFScheme.PRFOracleSpec (Bytes 16 × List Byte) (Bytes 16)) Bool)
    (ρ : Matrix Work Work ℂ) (hp : ρ.PosSemidef) (ht : ρ.trace = 1) (q : ℕ) (hq : PUE messageCharge A q) :
    let B := q+(q+q)
    uniformMean (fun g : CompressionTables => uniformMean (fun i => digestCollisionPr A ρ g i)) ≤
      (2*(B:ℝ≥0∞)+1)^2 / 2^256 + 16*((B:ℝ≥0∞)+1)^3/2^256 := by
  classical
  intro B
  let M := fun i => evidenceMachine A i q
  have bc (i) := evidence_budget A i q hq
  let p := fun (g : CompressionTables) (i : St) => qWeight (fun z => g.1 (cell z) = i) (M i (oracle g)) ρ
  let c := fun (g : CompressionTables) (i : St) => qWeight (fun z => LeftPort.wins id g (pair z)) (M i (oracle g)) ρ
  have pre : uniformMean (fun g => uniformMean (p g)) ≤ _ := preimage_shared M (fun _ => cell) ρ hp ht B bc
  have col : uniformMean (fun g => uniformMean (c g)) ≤ 16*((B:ℝ≥0∞)+1)^3/2^256 := by
    rw [switch c]
    calc _ ≤ ∑ i : St, unifW _ i * (16*((B:ℝ≥0∞)+1)^3/2^256) := by
           apply Finset.sum_le_sum
           intro i _
           exact mul_le_mul' le_rfl (LeftPort.search id 256 (fun s => (LeftPort.id_fraction s).le) (M i) pair B
             (bc i) ρ hp ht)
         _ = _ := by rw [← Finset.sum_mul,sum_unifW,one_mul]
  apply le_trans _ (add_le_add pre col)
  simp only [uniformMean, ← Finset.sum_add_distrib, ← mul_add]
  exact Finset.sum_le_sum fun g _ => mul_le_mul' le_rfl (Finset.sum_le_sum fun i _ =>
    mul_le_mul' le_rfl ((evidence_success A g i q hq ρ).trans (split_weight g i _ ρ)))

end Reduction.Compression.Hmac256
#print axioms Reduction.Compression.Hmac256.inner_search
