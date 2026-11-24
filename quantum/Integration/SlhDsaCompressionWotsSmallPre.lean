import Integration.SlhDsaCompressionWotsSmallHop

namespace Reduction.Compression.Wots256
open Ideal Ideal.HP SLHDSA MLink TweakableHash OracleComp OracleSpec PQ.Interactive PQ.QROM Quantum ENNReal
open scoped ComplexOrder
open HiddenWeight (mean)
variable {E σ : Type} [Fintype E] [DecidableEq E]
local notation "W" => WS Input Output E
abbrev TracePre (σ : Type) := σ × SM_DT_PRE_State (Bytes 22) Node

noncomputable def preScore (pk : Node) (g : CompressionTables) (M : (Input → Output) → σ → Node → Closed W (ℕ × Node))
    (ρ : Matrix W W ℂ) (r : TracePre σ) :=
  qWeight (· = true) (M (oracle g) r.1 pk >>= fun jm => liftU (match r.2.1[jm.1]? with
    | none => pure false
    | some tx => pure (decide (out16 (keyedChain IV128 sb128 g.1 pk (tblocks tx.1 [jm.2])) =
        out16 (keyedChain IV128 sb128 g.1 pk (tblocks tx.1 [tx.2])))))) ρ

theorem preScore_row (pk : Node) (cv : St) (g : CF St Blk) (h : CF Chain512 Block512) (T : Table) (R : Row)
    (M : (Input → Output) → σ → Node → Closed W (ℕ × Node)) (ρ : Matrix W W ℂ) (r : TracePre σ) :
    preScore pk (full pk cv g h (put T R)) M ρ r =
    qWeight (· = true) (M (oracle (full pk cv g h (put T R))) r.1 pk >>= fun jm => liftU (match r.2.1[jm.1]? with
      | none => pure false
      | some tx => pure (decide (collection g (put T R) tx.1 [jm.2] = collection g (put T R) tx.1 [tx.2])))) ρ := by
  unfold preScore
  simp only [full,publicLeaf,leaf]

theorem pre_row (seeds : ProbComp Node) (n : ℕ) (pk : Node) (cv : St) (g : CF St Blk)
    (h : CF Chain512 Block512) (T : Table) (choose : OracleComp (PreSpecG (preP seeds n (fun _ => cv))) σ)
    (M : (Input → Output) → σ → Node → Closed W (ℕ × Node)) (ρ : Matrix W W ℂ) (hp : ρ.PosSemidef) (ht : ρ.trace = 1)
    (q : ℕ) (hq : ∀ st, PUE (spec := unifSpec) cnt0 (fun H => M H st pk) q) :
    mean ($ᵗ Row) (fun R => mean
      ((simulateQ (SM_DT_PRE_oracles (preP seeds n (chainI g (put T R))) pk) choose).run ([],[]))
      (preScore pk (full pk cv g h (put T R)) M ρ)) ≤
      (2*(q:ℝ≥0∞)+1)^2 * ((Fintype.card Node:ℝ≥0∞)⁻¹ + (Fintype.card Node:ℝ≥0∞)⁻¹) := by
  let P := preP seeds n (fun _ => cv)
  let th := fun (R : Row) (_ : Node) (a : Bytes 22) (m : Node) => collection g (put T R) a [m]
  let ce := fun (R : Row) (_ : Unit) (_ : Node) (a : Bytes 22) (xs : List Node) => collection g (put T R) a xs
  have b := pre_row_avg_le P pk th (fun R a m => leaf g T R a m) ce
    (fun R U _ a xs ha => collection_local g T R U a xs ha) choose
    (fun R st => M (oracle (full pk cv g h (put T R))) st pk) ρ q
    (fun st => rowModel pk cv g h T _ ρ hp ht q (hq st))
  rw [explicitMean]
  unfold SetOracle.uniformMean unifW
  simp only [wq_qWeight_liftU_bind_tsum] at b
  simp only [mean,preScore_row]
  dsimp only [P,preP,WotsPhase.chainPre,WotsPhase.chainCollection,preWithEval,family,FWots128T,th,ce,collection,id_eq] at b ⊢
  kexact b

/-- A full shared-port PRE bound for the two-phase WOTS experiment with a classical choice
phase and an arbitrary quantum second phase. -/
theorem pre_bound (seeds : ProbComp Node) (n : ℕ) (A : PreAdv (family seeds n) Node)
    (h : CF Chain512 Block512) (M : (Input → Output) → A.State → Node → Closed W (ℕ × Node))
    (ρ : Matrix W W ℂ) (hp : ρ.PosSemidef) (ht : ρ.trace = 1)
    (C L q : ℕ) (hq : ∀ st pk, PUE (spec := unifSpec) cnt0 (fun H => M H st pk) q)
    (h0 : IsQueryBoundP (preProg₁ id A) (fun i => isPub i = true) 0)
    (hC : IsQueryBoundP (preProg₁ id A) (fun i => isChain i = true) C)
    (hL : AllQueriesSatisfy (preProg₁ id A) (chainLenLe L)) :
    mean seeds (fun pk => mean ($ᵗ (CF St Blk)) (fun g =>
      mean (simulateQ (ans₁ g (keyedChain IV128 sb128 g pk)) (preProg₁ id A)) (preScore pk (g,h) M ρ))) ≤
      (2*(q:ℝ≥0∞)+1)^2 * ((Fintype.card Node:ℝ≥0∞)⁻¹ + (Fintype.card Node:ℝ≥0∞)⁻¹) + phaseLoss C L := by
  apply phase_hop seeds (preProg₁ id A) (fun pk g => preScore pk (g,h) M ρ)
    (fun pk g st => qWeight_le_one _ _ hp ht) C L h0 hC hL
  intro pk cv g T
  have b := pre_row seeds n pk cv g h T (simulateQ (instImpl g) A.choose) M ρ hp ht q (fun st => hq st pk)
  have rr (R : Row) := WotsPhase.pre_run id Function.injective_id A g (chainI g (put T R)) pk
  apply le_trans _ b
  apply le_of_eq
  apply congrArg (mean ($ᵗ Row))
  funext R
  exact congrArg (fun o => mean o (preScore pk (full pk cv g h (put T R)) M ρ)) (rr R).symm

end Reduction.Compression.Wots256
#print axioms Reduction.Compression.Wots256.pre_bound
