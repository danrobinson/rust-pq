import Integration.SlhDsaCompressionHmacOuter

namespace Reduction.Compression.HmacKey
open MLink Ideal SLHDSA OracleComp OracleSpec PQ.Interactive Quantum ENNReal
open scoped Kronecker

private noncomputable def mean {X : Type} [Fintype X] (f : X → ℝ≥0∞) :=
  (Fintype.card X : ℝ≥0∞)⁻¹ * ∑ x, f x

private theorem mean_sum {X : Type} [Fintype X] (f : X → ℝ≥0∞) :
    mean f = ∑ x, unifW _ x * f x := Finset.mul_sum ..

private theorem mean_comm {X Y : Type} [Fintype X] [Fintype Y] (f : X → Y → ℝ≥0∞) :
    mean (fun x => mean (f x)) = mean (fun y => mean (fun x => f x y)) := by
  simp only [mean, ← Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm, mul_comm (Fintype.card X : ℝ≥0∞)⁻¹]

private theorem mean_bound {X : Type} [Fintype X] [Nonempty X] {f g : X → ℝ≥0∞} {e : ℝ≥0∞}
    (h : ∀ x, f x ≤ g x + e) : mean f ≤ mean g + e := by
  simp only [mean_sum]
  apply le_trans (Finset.sum_le_sum fun x _ => mul_le_mul' (a := unifW _ x) le_rfl (h x))
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, sum_unifW, one_mul, le_refl]

private theorem bool_mean {X : Type} [Fintype X] (f : (Bool → X) → ℝ≥0∞) :
    mean f = mean (fun i => mean (fun o => f (fun b => if b then o else i))) := by
  let e : X × X ≃ (Bool → X) :=
    ⟨fun p b => if b then p.2 else p.1, fun v => (v false,v true), fun _ => rfl,
      fun v => funext fun b => by cases b <;> rfl⟩
  have hc := (Fintype.card_congr e).symm
  unfold mean
  rw [hc, Fintype.card_prod, Nat.cast_mul, ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _))
    (Or.inl (ENNReal.natCast_ne_top _)), ← Equiv.sum_comp e f, Fintype.sum_prod_type]
  rw [← Finset.mul_sum, mul_assoc]
  rfl

variable (S : Sha2Set) {E : Type} [Fintype E] [DecidableEq E]
local notation "Work" => WS Input Output E

/-- Reduce the real wide-set message PRF to a private random function evaluated on
the inner digest. Repeated digests receive the same answer. Both shared compression
tables remain public throughout the two game hops. -/
theorem wide_hmac_to_inner (hw : S.vp.params.n ≠ 16)
    (A : (Input → Output) → QOC Work (PRFScheme.PRFOracleSpec (S.Node × List Byte) S.Node) Bool)
    (q : ℕ) (hA : PUE (messageCharge S) A q) (ρ : SubState ((Input × Output) × E)) :
    let M := ρ.matrix ⊗ₖ (SubState.basis ()).matrix
    (∑ g : CompressionTables, unifW _ g * qPrfRealPr (msgPrf S.vp (randPrims (functions S g))) (A (oracle g)) M) ≤
    (∑ g : CompressionTables, unifW _ g *
      ((Fintype.card Chain512 : ℝ≥0∞)⁻¹ * ∑ i : Chain512,
       (Fintype.card (Chain512 → Chain512) : ℝ≥0∞)⁻¹ * ∑ f : Chain512 → Chain512,
         qWeight (· = true) (ansRun (fun d => truncate S (f (innerDigest S g i d))) (A (oracle g))) M)) +
    ENNReal.ofReal (8*(q:ℝ)^2 / 2^512) + ENNReal.ofReal (8*(q:ℝ)^2 / 2^(8*S.vp.params.n)) := by
  intro M
  let work := fun g st => qWeight (· = true) (messageRun S A st (oracle g)) M
  let rest := fun g i => mean fun (f : Chain512 → Chain512) => qWeight (· = true)
    (ansRun (fun d => truncate S (f (innerDigest S g i d))) (A (oracle g))) M
  have h := wide_message_hop S hw A q hA ρ
  have first : mean (fun g => mean (work g)) =
      mean (fun i => mean (fun g => mean (fun o => work g (fun b => if b then o else i)))) := by
    simp_rw [bool_mean (work _)]
    exact mean_comm _
  have second (i) : mean (fun g => mean (fun o => work g (fun b => if b then o else i))) ≤
      mean (fun g => rest g i) + ENNReal.ofReal (8*(q:ℝ)^2 / 2^512) := by
    rw [mean_sum (fun g => mean _), mean_sum (fun g => rest g i)]
    exact wide_outer_message_hop S A i q hA ρ
  have last := mean_bound second
  rw [← first, ← mean_comm rest, mean_sum (fun g => mean (work g)), mean_sum (fun g => mean (rest g))] at last
  exact h.trans (add_le_add_left last _)

end Reduction.Compression.HmacKey
#print axioms Reduction.Compression.HmacKey.wide_hmac_to_inner
