import Integration.SlhDsaCompressionShortGame

namespace Reduction.Compression.ShortBlocks
open Ideal Ideal.HP SLHDSA MLink TweakableHash OracleComp OracleSpec PQ.Interactive PQ.QROM Quantum ENNReal
open scoped ComplexOrder
open HiddenWeight (mean)
open Wots256 (Node Table full collection explicitMean phaseLoss mean_cap productMean Hash chainHash)
variable {ar : ℕ} (ha : ar ≤ 2)
variable {E σ : Type} [Fintype E] [DecidableEq E]
local notation "W" => WS Input Output E

noncomputable def tcrValue (seeds : ProbComp Node) (n : ℕ)
    (choose : OracleComp (TcrSpec (tcrP seeds ar n (fun _ => IV128))) σ)
    (M : (Input → Output) → σ → Node → Closed W (ℕ × Msg ar)) (ρ : Matrix W W ℂ)
    (t : CompressionTables) (pk : Node) :=
  mean ((simulateQ (SM_DT_TCR_oracles ((family seeds ar n).tcrProb t.1) pk) choose).run ([],[]))
    (tcrScore pk t M ρ)

theorem tcr_measure (seeds : ProbComp Node) (n : ℕ)
    (choose : OracleComp (TcrSpec (tcrP seeds ar n (fun _ => IV128))) σ)
    (M : (Input → Output) → σ → Node → Closed W (ℕ × Msg ar)) (ρ : Matrix W W ℂ) (t : CompressionTables) (pk : Node) :
    tcrValue seeds n choose M ρ t pk =
    mean (simulateQ (ans₁ t.1 (keyedChain IV128 sb128 t.1 pk)) (tcrProg₁ (classFirst seeds ar n choose))) (tcrScore pk t M ρ) := by
  let A := classFirst seeds ar n choose
  let c := keyedChain IV128 sb128 t.1 pk
  have rr := simulateQ_run_simulateQ_eq_of_step (instImpl t.1) _ (tcrGameM (family seeds ar n)) (ans₁ t.1 c)
    (Ideal.tcr_step (F := family seeds ar n)  t.1 pk) A.choose ([],[])
  have e : simulateQ (instImpl t.1) A.choose = choose :=
    Realize.instImpl_emb t.1 choose
  rw [e] at rr
  exact congrArg (fun o => mean o (tcrScore pk t M ρ)) rr

include ha in
theorem tcr_average (seeds : ProbComp Node) (n : ℕ) (choose : OracleComp (TcrSpec (tcrP seeds ar n (fun _ => IV128))) σ)
    (M : (Input → Output) → σ → Node → Closed W (ℕ × Msg ar)) (ρ : Matrix W W ℂ) (hp : ρ.PosSemidef) (ht : ρ.trace = 1)
    (C L q : ℕ) (hq : ∀ st pk, PUE (spec := unifSpec) cnt0 (fun H => M H st pk) q)
    (h0 : IsQueryBoundP (tcrProg₁ (classFirst seeds ar n choose)) (fun i => isPub i = true) 0)
    (hC : IsQueryBoundP (tcrProg₁ (classFirst seeds ar n choose)) (fun i => isChain i = true) C)
    (hL : AllQueriesSatisfy (tcrProg₁ (classFirst seeds ar n choose)) (chainLenLe L)) :
    SetOracle.uniformMean (fun t => mean seeds (tcrValue seeds n choose M ρ t)) ≤ (2*(q:ℝ≥0∞)+1)^2 / (Fintype.card Node:ℝ≥0∞) + phaseLoss C L := by
  rw [productMean]
  apply mean_cap
  intro h
  have b := tcr_bound ha seeds n (classFirst seeds ar n choose) h M ρ hp ht C L q hq h0 hC hL
  simpa only [tcr_measure] using b

noncomputable def tcrNative (ar : ℕ) (seeds : ProbComp Node) (n : ℕ) (hash : Hash) : SM_DT_TCR_Problem Unit Node (Bytes 22) (Msg ar) Node where
  th := ⟨seeds,fun pk a m => hash pk a m.val⟩
  thColl := ⟨fun _ => List Node,fun _ => hash⟩
  numTargets := n

theorem tcr_native (seeds : ProbComp Node) (n : ℕ)
    (choose : OracleComp (TcrSpec (tcrP seeds ar n (fun _ => IV128))) σ)
    (M : (Input → Output) → σ → Node → Closed W (ℕ × Msg ar)) (ρ : Matrix W W ℂ) (hp : ρ.PosSemidef) (ht : ρ.trace = 1)
    (t : CompressionTables) (pk : Node) (hash : Hash) (hh : hash = chainHash t.1) :
    tcrInner (⟨σ,choose,M (oracle t),ρ,hp,ht⟩ : QSM_DT_TCR_Adversary W (tcrNative ar seeds n hash)) pk =
      tcrValue seeds n choose M ρ t pk := by
  subst hash
  unfold tcrInner tcrValue tcrScore mean
  rw [wq_qWeight_liftU_bind_tsum]
  dsimp only [tcrNative,chainHash,THFam.tcrProb,THFam.evalT,THFam.evalC,THFam.coll,family,id_eq]
  qm_kernel_rfl

end Reduction.Compression.ShortBlocks
#print axioms Reduction.Compression.ShortBlocks.tcr_average
#print axioms Reduction.Compression.ShortBlocks.tcr_native
