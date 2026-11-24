import Integration.SlhDsaCompressionWotsSmallFirst
import Integration.SlhDsaCompressionWotsSmallPre
import Integration.SlhDsaCompressionWotsSmallTcr
import Integration.SlhDsaCompressionWotsSmallUd

namespace Reduction.Compression.Wots256
open Ideal Ideal.HP SLHDSA MLink TweakableHash OracleComp OracleSpec PQ.Interactive PQ.QROM Quantum ENNReal
open scoped ComplexOrder
open HiddenWeight (mean)
variable {E σ : Type} [Fintype E] [DecidableEq E]
local notation "W" => WS Input Output E

/-- Exchange the seed draw and the left table, retaining an independent right table
accessible coherently throughout the adversary. -/
theorem productMean {X Y Z : Type} [Fintype X] [Fintype Y] [SampleableType X] [SampleableType Y]
    (seeds : ProbComp Z) (f : X × Y → Z → ℝ≥0∞) :
    SetOracle.uniformMean (fun t => mean seeds (f t)) = mean ($ᵗ Y) (fun y =>
      mean seeds (fun z => mean ($ᵗ X) (fun x => f (x,y) z))) := by
  have h : SetOracle.uniformMean (fun t => mean seeds (f t)) = mean ($ᵗ Y) (fun y =>
      mean ($ᵗ X) (fun x => mean seeds (f (x,y)))) := by
    simp only [explicitMean,SetOracle.uniformMean,Fintype.sum_prod_type,unifW,Finset.mul_sum,Fintype.card_prod,
      Nat.cast_mul,ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl (ENNReal.natCast_ne_top _)),mul_assoc]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => mul_left_comm ..
  exact h.trans (congrArg (mean ($ᵗ Y)) (funext fun y => HiddenWeight.mean_switch ($ᵗ X) seeds (fun x => f (x,y))))

private theorem mean_le_add {X : Type} (p : ProbComp X) (f g : X → ℝ≥0∞) (b : ℝ≥0∞)
    (h : ∀ x, f x ≤ g x + b) : mean p f ≤ mean p g + b :=
  (HiddenWeight.mean_mono p h).trans ((HiddenWeight.mean_add p g (fun _ => b)).le.trans
    (add_le_add le_rfl (mean_cap p _ b (fun _ => le_rfl))))

noncomputable def preValue (seeds : ProbComp Node) (n : ℕ)
    (choose : OracleComp (PreSpecG (preP seeds n (fun _ => IV128))) σ)
    (M : (Input → Output) → σ → Node → Closed W (ℕ × Node)) (ρ : Matrix W W ℂ)
    (t : CompressionTables) (pk : Node) :=
  mean ((simulateQ (SM_DT_PRE_oracles ((family seeds n).preProb id Function.injective_id t.1) pk) choose).run ([],[]))
    (preScore pk t M ρ)

theorem pre_measure (seeds : ProbComp Node) (n : ℕ)
    (choose : OracleComp (PreSpecG (preP seeds n (fun _ => IV128))) σ)
    (M : (Input → Output) → σ → Node → Closed W (ℕ × Node)) (ρ : Matrix W W ℂ) (t : CompressionTables) (pk : Node) :
    preValue seeds n choose M ρ t pk =
    mean (simulateQ (ans₁ t.1 (keyedChain IV128 sb128 t.1 pk)) (preProg₁ id (preFirst seeds n choose))) (preScore pk t M ρ) := by
  let A := preFirst seeds n choose
  let c := keyedChain IV128 sb128 t.1 pk
  have rr := simulateQ_run_simulateQ_eq_of_step (instImpl t.1) _ (preGameM (family seeds n) id) (ans₁ t.1 c)
    (Ideal.pre_step (F := family seeds n) id Function.injective_id t.1 pk) A.choose ([],[])
  have e : simulateQ (instImpl t.1) A.choose = choose :=
    Realize.instImpl_emb t.1 choose
  rw [e] at rr
  exact congrArg (fun o => mean o (preScore pk t M ρ)) rr

theorem pre_average (seeds : ProbComp Node) (n : ℕ) (choose : OracleComp (PreSpecG (preP seeds n (fun _ => IV128))) σ)
    (M : (Input → Output) → σ → Node → Closed W (ℕ × Node)) (ρ : Matrix W W ℂ) (hp : ρ.PosSemidef) (ht : ρ.trace = 1)
    (C L q : ℕ) (hq : ∀ st pk, PUE (spec := unifSpec) cnt0 (fun H => M H st pk) q)
    (h0 : IsQueryBoundP (preProg₁ id (preFirst seeds n choose)) (fun i => isPub i = true) 0)
    (hC : IsQueryBoundP (preProg₁ id (preFirst seeds n choose)) (fun i => isChain i = true) C)
    (hL : AllQueriesSatisfy (preProg₁ id (preFirst seeds n choose)) (chainLenLe L)) :
    SetOracle.uniformMean (fun t => mean seeds (preValue seeds n choose M ρ t)) ≤ (2*(q:ℝ≥0∞)+1)^2 * ((Fintype.card Node:ℝ≥0∞)⁻¹ + (Fintype.card Node:ℝ≥0∞)⁻¹) + phaseLoss C L := by
  rw [productMean]
  apply mean_cap
  intro h
  have b := pre_bound seeds n (preFirst seeds n choose) h M ρ hp ht C L q hq h0 hC hL
  simpa only [pre_measure] using b

noncomputable def tcrValue (seeds : ProbComp Node) (n : ℕ)
    (choose : OracleComp (TcrSpec (tcrP seeds n (fun _ => IV128))) σ)
    (M : (Input → Output) → σ → Node → Closed W (ℕ × Node)) (ρ : Matrix W W ℂ)
    (t : CompressionTables) (pk : Node) :=
  mean ((simulateQ (SM_DT_TCR_oracles ((family seeds n).tcrProb t.1) pk) choose).run ([],[]))
    (tcrScore pk t M ρ)

theorem tcr_measure (seeds : ProbComp Node) (n : ℕ)
    (choose : OracleComp (TcrSpec (tcrP seeds n (fun _ => IV128))) σ)
    (M : (Input → Output) → σ → Node → Closed W (ℕ × Node)) (ρ : Matrix W W ℂ) (t : CompressionTables) (pk : Node) :
    tcrValue seeds n choose M ρ t pk =
    mean (simulateQ (ans₁ t.1 (keyedChain IV128 sb128 t.1 pk)) (tcrProg₁ (tcrFirst seeds n choose))) (tcrScore pk t M ρ) := by
  let A := tcrFirst seeds n choose
  let c := keyedChain IV128 sb128 t.1 pk
  have rr := simulateQ_run_simulateQ_eq_of_step (instImpl t.1) _ (tcrGameM (family seeds n)) (ans₁ t.1 c)
    (Ideal.tcr_step (F := family seeds n)  t.1 pk) A.choose ([],[])
  have e : simulateQ (instImpl t.1) A.choose = choose :=
    Realize.instImpl_emb t.1 choose
  rw [e] at rr
  exact congrArg (fun o => mean o (tcrScore pk t M ρ)) rr

theorem tcr_average (seeds : ProbComp Node) (n : ℕ) (choose : OracleComp (TcrSpec (tcrP seeds n (fun _ => IV128))) σ)
    (M : (Input → Output) → σ → Node → Closed W (ℕ × Node)) (ρ : Matrix W W ℂ) (hp : ρ.PosSemidef) (ht : ρ.trace = 1)
    (C L q : ℕ) (hq : ∀ st pk, PUE (spec := unifSpec) cnt0 (fun H => M H st pk) q)
    (h0 : IsQueryBoundP (tcrProg₁ (tcrFirst seeds n choose)) (fun i => isPub i = true) 0)
    (hC : IsQueryBoundP (tcrProg₁ (tcrFirst seeds n choose)) (fun i => isChain i = true) C)
    (hL : AllQueriesSatisfy (tcrProg₁ (tcrFirst seeds n choose)) (chainLenLe L)) :
    SetOracle.uniformMean (fun t => mean seeds (tcrValue seeds n choose M ρ t)) ≤ (2*(q:ℝ≥0∞)+1)^2 / (Fintype.card Node:ℝ≥0∞) + phaseLoss C L := by
  rw [productMean]
  apply mean_cap
  intro h
  have b := tcr_bound seeds n (tcrFirst seeds n choose) h M ρ hp ht C L q hq h0 hC hL
  simpa only [tcr_measure] using b

noncomputable def udValue (world : SM_DT_UD_World) (seeds : ProbComp Node) (n : ℕ)
    (choose : OracleComp (UdSpecG (udP seeds n (fun _ => IV128))) σ)
    (M : (Input → Output) → σ → Node → Closed W Bool) (ρ : Matrix W W ℂ)
    (t : CompressionTables) (pk : Node) :=
  mean ((simulateQ (SM_DT_UD_oracles world ((family seeds n).udProb id Function.injective_id t.1) pk) choose).run ([],[]))
    (udScore pk t M ρ)

theorem ud_measure (world : SM_DT_UD_World) (seeds : ProbComp Node) (n : ℕ)
    (choose : OracleComp (UdSpecG (udP seeds n (fun _ => IV128))) σ)
    (M : (Input → Output) → σ → Node → Closed W Bool) (ρ : Matrix W W ℂ) (t : CompressionTables) (pk : Node) :
    udValue world seeds n choose M ρ t pk =
    mean (simulateQ (ans₁ t.1 (keyedChain IV128 sb128 t.1 pk)) (udProg₁ world id (udFirst seeds n choose))) (udScore pk t M ρ) := by
  let A := udFirst seeds n choose
  let c := keyedChain IV128 sb128 t.1 pk
  have rr := simulateQ_run_simulateQ_eq_of_step (instImpl t.1) _ (udGameM (family seeds n) world id) (ans₁ t.1 c)
    (Ideal.ud_step (F := family seeds n) world id Function.injective_id t.1 pk) A.pick ([],[])
  have e : simulateQ (instImpl t.1) A.pick = choose :=
    Realize.instImpl_emb t.1 choose
  rw [e] at rr
  exact congrArg (fun o => mean o (udScore pk t M ρ)) rr

theorem ud_average (seeds : ProbComp Node) (n : ℕ) (choose : OracleComp (UdSpecG (udP seeds n (fun _ => IV128))) σ)
    (M : (Input → Output) → σ → Node → Closed W Bool) (ρ : Matrix W W ℂ) (hp : ρ.PosSemidef) (ht : ρ.trace = 1)
    (C L q : ℕ) (hq : ∀ st pk, PUE (spec := unifSpec) cnt0 (fun H => M H st pk) q)
    (h0 : ∀ world, IsQueryBoundP (udProg₁ world id (udFirst seeds n choose)) (fun i => isPub i = true) 0)
    (hC : ∀ world, IsQueryBoundP (udProg₁ world id (udFirst seeds n choose)) (fun i => isChain i = true) C)
    (hL : ∀ world, AllQueriesSatisfy (udProg₁ world id (udFirst seeds n choose)) (chainLenLe L)) :
    SetOracle.uniformMean (fun t => mean seeds (udValue .real seeds n choose M ρ t)) ≤ SetOracle.uniformMean (fun t => mean seeds (udValue .ideal seeds n choose M ρ t)) + (ENNReal.ofReal (8*(q:ℝ)^2/Fintype.card Node) + 2*phaseLoss C L) := by
  rw [productMean,productMean]
  apply mean_le_add
  intro h
  have b := ud_bound seeds n (udFirst seeds n choose) h M ρ hp ht C L q hq h0 hC hL
  simpa only [ud_measure] using b

end Reduction.Compression.Wots256
#print axioms Reduction.Compression.Wots256.pre_average
#print axioms Reduction.Compression.Wots256.tcr_average
#print axioms Reduction.Compression.Wots256.ud_average
