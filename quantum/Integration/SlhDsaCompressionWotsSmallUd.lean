import Integration.SlhDsaCompressionWotsSmallHop

namespace Reduction.Compression.Wots256
open Ideal Ideal.HP SLHDSA MLink TweakableHash OracleComp OracleSpec PQ.Interactive PQ.QROM Quantum ENNReal
open scoped ComplexOrder
open HiddenWeight (mean)
variable {E σ : Type} [Fintype E] [DecidableEq E]
local notation "W" => WS Input Output E

abbrev TraceUd (σ : Type) := σ × SM_DT_UD_State (Bytes 22)
noncomputable def udScore (pk : Node) (g : CompressionTables) (M : (Input → Output) → σ → Node → Closed W Bool)
    (ρ : Matrix W W ℂ) (r : TraceUd σ) := qWeight (· = true) (M (oracle g) r.1 pk) ρ

theorem ud_row (seeds : ProbComp Node) (n : ℕ) (pk : Node) (cv : St) (g : CF St Blk)
    (h : CF Chain512 Block512) (T : Table) (pick : OracleComp (UdSpecG (udP seeds n (fun _ => cv))) σ)
    (M : (Input → Output) → σ → Node → Closed W Bool) (ρ : Matrix W W ℂ) (hp : ρ.PosSemidef) (ht : ρ.trace = 1)
    (q : ℕ) (hq : ∀ st, PUE (spec := unifSpec) cnt0 (fun H => M H st pk) q) :
    let success := fun (world : SM_DT_UD_World) => mean ($ᵗ Row) (fun R => mean
      ((simulateQ (SM_DT_UD_oracles world (udP seeds n (chainI g (put T R))) pk) pick).run ([],[]))
      (udScore pk (full pk cv g h (put T R)) M ρ))
    success .real ≤ success .ideal + ENNReal.ofReal (8*(q:ℝ)^2/Fintype.card Node) := by
  let P := udP seeds n (fun _ => cv)
  let th := fun (R : Row) (_ : Node) (a : Bytes 22) (m : Node) => collection g (put T R) a [m]
  let ce := fun (R : Row) (_ : Unit) (_ : Node) (a : Bytes 22) (xs : List Node) => collection g (put T R) a xs
  have b := ud_row_avg_le P pk th (fun R a m => leaf g T R a m) ce
    (fun R U _ a xs ha => collection_local g T R U a xs ha) rfl rfl pick
    (fun R st => M (oracle (full pk cv g h (put T R))) st pk) ρ hp ht q
    (fun st => rowTight pk cv g h T _ ρ hp ht q (hq st))
  dsimp only
  rw [explicitMean,explicitMean]
  unfold SetOracle.uniformMean unifW
  simp only [mean,udScore]
  simp only [wq_qWeight_liftU_bind_tsum] at b
  dsimp only [P,udP,WotsPhase.chainUd,WotsPhase.chainCollection,udWithEval,family,FWots128T,th,ce,collection,id_eq] at b ⊢
  kexact b

private theorem mean_slack {X : Type} (p : ProbComp X) (f g : X → ℝ≥0∞) (b : ℝ≥0∞)
    (h : ∀ x, f x ≤ g x + b) : mean p f ≤ mean p g + b :=
  (HiddenWeight.mean_mono p h).trans ((HiddenWeight.mean_add p g (fun _ => b)).le.trans
    (add_le_add le_rfl (mean_cap p _ b (fun _ => le_rfl))))

theorem ud_bound (seeds : ProbComp Node) (n : ℕ) (A : UdAdv (family seeds n))
    (h : CF Chain512 Block512) (M : (Input → Output) → A.State → Node → Closed W Bool)
    (ρ : Matrix W W ℂ) (hp : ρ.PosSemidef) (ht : ρ.trace = 1)
    (C L q : ℕ) (hq : ∀ st pk, PUE (spec := unifSpec) cnt0 (fun H => M H st pk) q)
    (h0 : ∀ world, IsQueryBoundP (udProg₁ world id A) (fun i => isPub i = true) 0)
    (hC : ∀ world, IsQueryBoundP (udProg₁ world id A) (fun i => isChain i = true) C)
    (hL : ∀ world, AllQueriesSatisfy (udProg₁ world id A) (chainLenLe L)) :
    let success := fun world => mean seeds (fun pk => mean ($ᵗ (CF St Blk)) (fun g =>
      mean (simulateQ (ans₁ g (keyedChain IV128 sb128 g pk)) (udProg₁ world id A)) (udScore pk (g,h) M ρ)))
    success .real ≤ success .ideal + (ENNReal.ofReal (8*(q:ℝ)^2/Fintype.card Node) + 2*phaseLoss C L) := by
  let score := fun pk g => udScore pk (g,h) M ρ
  let hidden := fun world => mean seeds (fun pk => mean ($ᵗ St) fun cv => mean ($ᵗ (CF St Blk)) fun g => mean ($ᵗ Table) fun T =>
    mean (simulateQ (ans₁ g (chainI g T)) (udProg₁ world id A)) (score pk (gstar IV128 (sb128 pk) cv g T)))
  let real := fun world => mean seeds (fun pk => mean ($ᵗ (CF St Blk)) fun g =>
    mean (simulateQ (ans₁ g (keyedChain IV128 sb128 g pk)) (udProg₁ world id A)) (score pk g))
  let b := ENNReal.ofReal (8*(q:ℝ)^2/Fintype.card Node)
  have hw : ∀ pk g r, score pk g r ≤ 1 := fun _ _ _ => qWeight_le_one _ _ hp ht
  have first : real .real ≤ hidden .real + phaseLoss C L := by
    have b := HiddenWeight.hiddenPrefix IV128 sb128 (udProg₁ .real id A) seeds sb128_injective 1
      (fun _ => prEvent_le_one _) 0 C L (h0 _) (hC _) (hL _) score hw
    simpa only [real,hidden,phaseLoss,Nat.cast_zero,zero_mul,mul_zero,zero_add,div_eq_mul_inv,card_St,Nat.cast_pow,Nat.cast_ofNat] using b
  have last : hidden .ideal ≤ real .ideal + phaseLoss C L := by
    have b := HiddenWeight.hiddenPrefix_reverse IV128 sb128 (udProg₁ .ideal id A) seeds sb128_injective 1
      (fun _ => prEvent_le_one _) 0 C L (h0 _) (hC _) (hL _) score hw
    simpa only [real,hidden,phaseLoss,Nat.cast_zero,zero_mul,mul_zero,zero_add,div_eq_mul_inv,card_St,Nat.cast_pow,Nat.cast_ofNat] using b
  have middle : hidden .real ≤ hidden .ideal + b := by
    apply mean_slack; intro pk
    apply mean_slack; intro cv
    apply mean_slack; intro g
    rw [resample,resample (fun T => mean (simulateQ (ans₁ g (chainI g T)) (udProg₁ .ideal id A)) _)]
    apply mean_slack; intro T
    have rr (world : SM_DT_UD_World) (R : Row) := WotsPhase.ud_run world id Function.injective_id A g (chainI g (put T R)) pk
    have v := ud_row seeds n pk cv g h T (simulateQ (instImpl g) A.pick) M ρ hp ht q (fun st => hq st pk)
    let val := fun world => mean ($ᵗ Row) (fun R => mean
      ((simulateQ (SM_DT_UD_oracles world (udP seeds n (chainI g (put T R))) pk)
        (simulateQ (instImpl g) A.pick)).run ([],[])) (udScore pk (full pk cv g h (put T R)) M ρ))
    have he (world : SM_DT_UD_World) : val world = mean ($ᵗ Row) (fun R => mean
        (simulateQ (ans₁ g (chainI g (put T R))) (udProg₁ world id A)) (score pk (gstar IV128 (sb128 pk) cv g (put T R)))) := by
      apply congrArg (mean ($ᵗ Row))
      funext R
      exact congrArg (fun o => mean o (udScore pk (full pk cv g h (put T R)) M ρ)) (rr world R)
    exact (he .real).symm.le.trans (v.trans_eq (congrArg (· + b) (he .ideal)))
  change real .real ≤ real .ideal + (b + 2*phaseLoss C L)
  calc real .real ≤ hidden .real + phaseLoss C L := first
       _ ≤ (real .ideal + phaseLoss C L + b) + phaseLoss C L :=
         add_le_add (middle.trans (add_le_add last le_rfl)) le_rfl
       _ = _ := by simp only [two_mul]; ac_rfl

end Reduction.Compression.Wots256
#print axioms Reduction.Compression.Wots256.ud_bound
