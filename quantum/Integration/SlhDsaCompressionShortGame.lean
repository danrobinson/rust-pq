import Integration.SlhDsaCompressionShortRow

namespace Reduction.Compression.ShortBlocks
open Ideal Ideal.HP SLHDSA MLink TweakableHash OracleComp OracleSpec PQ.Interactive PQ.QROM Quantum ENNReal
open scoped ComplexOrder
open HiddenWeight (mean)
open Wots256 (Node Table full collection explicitMean phaseLoss mean_cap productMean)
local instance shortMsgFinite (ar : ℕ) : Fintype (Msg ar) := inferInstanceAs (Fintype (List.Vector Node ar))
variable {ar : ℕ} (ha : ar ≤ 2)
variable {E σ : Type} [Fintype E] [DecidableEq E]
local notation "W" => WS Input Output E
abbrev TraceTcr (σ : Type) (ar : ℕ) := σ × SM_DT_TCR_State (Bytes 22) (Msg ar)

noncomputable def tcrScore (pk : Node) (g : CompressionTables) (M : (Input → Output) → σ → Node → Closed W (ℕ × Msg ar))
    (ρ : Matrix W W ℂ) (r : TraceTcr σ ar) :=
  qWeight (· = true) (M (oracle g) r.1 pk >>= fun jm => match r.2.1[jm.1]? with
    | none => pure false
    | some tx => pure (decide (jm.2 ≠ tx.2 ∧ out16 (keyedChain IV128 sb128 g.1 pk (tblocks tx.1 jm.2.val)) =
        out16 (keyedChain IV128 sb128 g.1 pk (tblocks tx.1 tx.2.val))))) ρ

include ha in
theorem tcrScore_row (pk : Node) (cv : St) (g : CF St Blk) (h : CF Chain512 Block512) (T : Table) (R : Row ar)
    (M : (Input → Output) → σ → Node → Closed W (ℕ × Msg ar)) (ρ : Matrix W W ℂ) (r : TraceTcr σ ar) :
    tcrScore pk (full pk cv g h (put T R)) M ρ r =
    qWeight (· = true) (M (oracle (full pk cv g h (put T R))) r.1 pk >>= fun jm => match r.2.1[jm.1]? with
      | none => pure false
      | some tx => pure (decide (jm.2 ≠ tx.2 ∧ Wots256.collection g (put T R) tx.1 jm.2.val = Wots256.collection g (put T R) tx.1 tx.2.val))) ρ := by
  unfold tcrScore
  simp only [full,publicLeaf ha,leaf ha]

include ha in
theorem tcr_row (seeds : ProbComp Node) (n : ℕ) (pk : Node) (cv : St) (g : CF St Blk)
    (h : CF Chain512 Block512) (T : Table) (choose : OracleComp (TcrSpec (tcrP seeds ar n (fun _ => cv))) σ)
    (M : (Input → Output) → σ → Node → Closed W (ℕ × Msg ar)) (ρ : Matrix W W ℂ) (hp : ρ.PosSemidef) (ht : ρ.trace = 1)
    (q : ℕ) (hq : ∀ st, PUE (spec := unifSpec) cnt0 (fun H => M H st pk) q) :
    mean ($ᵗ (Row ar)) (fun R => mean
      ((simulateQ (SM_DT_TCR_oracles (tcrP seeds ar n (chainI g (put T R))) pk) choose).run ([],[]))
      (tcrScore pk (full pk cv g h (put T R)) M ρ)) ≤
      (2*(q:ℝ≥0∞)+1)^2 / (Fintype.card Node:ℝ≥0∞) := by
  let P := tcrP seeds ar n (fun _ => cv)
  let th := fun (R : Row ar) (_ : Node) (a : Bytes 22) (m : Msg ar) => Wots256.collection g (put T R) a m.val
  let ce := fun (R : Row ar) (_ : Unit) (_ : Node) (a : Bytes 22) (xs : List Node) => Wots256.collection g (put T R) a xs
  have b := tcr_row_avg_le P pk th (fun R a m => leaf ha g T R a m) ce
    (fun R U _ a xs ha => localCollection g T R U a xs ha) choose
    (fun R st => M (oracle (full pk cv g h (put T R))) st pk) ρ q
    (fun st => model ha pk cv g h T _ ρ hp ht q (hq st))
  rw [explicitMean]
  unfold SetOracle.uniformMean unifW
  simp only [wq_qWeight_liftU_bind_tsum] at b
  simp only [mean,tcrScore_row ha]
  dsimp only [P,tcrP,WotsPhase.chainTcr,WotsPhase.chainCollection,tcrWithEval,family,th,ce,Wots256.collection,id_eq] at b ⊢
  kexact b

include ha in
/-- For a one-block target, the recorded tweak selects a single private-row target.
The linear hidden-row loss charges the entire choosing phase. -/
theorem tcr_bound (seeds : ProbComp Node) (n : ℕ) (A : TcrAdv (family seeds ar n))
    (h : CF Chain512 Block512) (M : (Input → Output) → A.State → Node → Closed W (ℕ × Msg ar))
    (ρ : Matrix W W ℂ) (hp : ρ.PosSemidef) (ht : ρ.trace = 1)
    (C L q : ℕ) (hq : ∀ st pk, PUE (spec := unifSpec) cnt0 (fun H => M H st pk) q)
    (h0 : IsQueryBoundP (tcrProg₁ A) (fun i => isPub i = true) 0)
    (hC : IsQueryBoundP (tcrProg₁ A) (fun i => isChain i = true) C)
    (hL : AllQueriesSatisfy (tcrProg₁ A) (chainLenLe L)) :
    mean seeds (fun pk => mean ($ᵗ (CF St Blk)) (fun g =>
      mean (simulateQ (ans₁ g (keyedChain IV128 sb128 g pk)) (tcrProg₁ A)) (tcrScore pk (g,h) M ρ))) ≤
      (2*(q:ℝ≥0∞)+1)^2 / (Fintype.card Node:ℝ≥0∞) + phaseLoss C L := by
  have hop := HiddenWeight.hiddenPrefix IV128 sb128 (tcrProg₁ A) seeds sb128_injective 1
    (fun _ => prEvent_le_one _) 0 C L h0 hC hL (fun pk g => tcrScore pk (g,h) M ρ) (fun _ _ _ => qWeight_le_one _ _ hp ht)
  apply hop.trans (add_le_add ?_ ?_)
  rotate_left
  · simp only [Nat.cast_zero,zero_mul,zero_add,phaseLoss,div_eq_mul_inv]
    rw [card_St]
    norm_num
  apply mean_cap; intro pk
  apply mean_cap; intro cv
  apply mean_cap; intro g
  rw [resample ha]
  apply mean_cap; intro T
  have b := tcr_row ha seeds n pk cv g h T (simulateQ (instImpl g) A.choose) M ρ hp ht q (fun st => hq st pk)
  have rr (R : Row ar) := WotsPhase.tcr_run A g (chainI g (put T R)) pk
  apply le_trans _ b
  apply le_of_eq
  apply congrArg (mean ($ᵗ (Row ar)))
  funext R
  exact congrArg (fun o => mean o (tcrScore pk (full pk cv g h (put T R)) M ρ)) (rr R).symm

end Reduction.Compression.ShortBlocks
#print axioms Reduction.Compression.ShortBlocks.tcr_bound
