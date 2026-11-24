import MIdeal.SingletonHash
import Ideal.Games.TcrBridge

namespace MIdeal.SingletonTcr
open Ideal Ideal.HP MLink SLHDSA OracleComp OracleSpec TweakableHash ENNReal SingletonHash
variable (S : Sha2Set) (M : Type)

abbrev History := SM_DT_TCR_State (Bytes 22) M
abbrev Game := SM_DT_TCR_challengeSpec (Bytes 22) M S.Node +
  (((_ : Unit) × Bytes 22 × List S.Node) →ₒ Option S.Node)
abbrev Port := unifSpec + (hS St Blk + Game S M)

structure Adversary where
  State : Type
  choose : OracleComp (Port S M) State
  forge : State → S.Node → Reader (ℕ × M)

structure Member where
  cap : ℕ
  message : M → S.Node
  inputs : M → List S.Node
  inputs_eq : ∀ m, inputs m = [message m]
  message_injective : Function.Injective message

variable {M} (F : Member S M)

local instance (g : CompressionTables) : DecidableEq (tablePrimitives g S.vp.params).AdrsKey :=
  inferInstanceAs (DecidableEq (Bytes 22))
local instance (g : CompressionTables) : DecidableEq (tablePrimitives g S.vp.params).Y :=
  inferInstanceAs (DecidableEq S.Node)


def problem (g : CompressionTables) (seeds : ProbComp S.Node) :
    SM_DT_TCR_Problem Unit S.Node (Bytes 22) M S.Node where
  th := { seedGen := seeds, eval := fun pk t m => (tablePrimitives g S.vp.params).Thash pk t (F.inputs m) }
  thColl := { Msg := fun _ => List S.Node, eval := fun _ => (tablePrimitives g S.vp.params).Thash }
  numTargets := F.cap

def atTables (g : CompressionTables) (seeds : ProbComp S.Node) (A : Adversary S M) :
    SM_DT_TCR_Adversary (problem S F g seeds) where
  State := A.State
  choose := simulateQ (instImpl g.1) A.choose
  forge := fun st pk => simulateQ (ansImpl (spec := hS St Blk) g.1) (A.forge st pk)

def chooseImpl (g512 : CF Chain512 Block512) (pk : S.Node) :
    QueryImpl (Port S M) (StateT (History M) Reader) := fun
  | .inl n => liftM ((unifSpec + hS St Blk).query (.inl n))
  | .inr (.inl t) => liftM ((unifSpec + hS St Blk).query (.inr t))
  | .inr (.inr (.inl tm)) => StateT.mk fun (qs,tw) =>
      if F.cap ≤ qs.length ∨ ¬ TweakFresh Prod.fst qs tw tm.1 then
        pure (none,(qs,tw))
      else do
        let h ← readF S pk tm.1 (F.message tm.2)
        return (some h,(qs ++ [tm],tw))
  | .inr (.inr (.inr t)) => StateT.mk fun (qs,tw) =>
      if TweakReserved (Q := Bytes 22 × M) Prod.fst qs t.2.1 then pure (none,(qs,tw))
      else do
        let h ← readCollection S g512 pk t.2.1 t.2.2
        return (some h,(qs,tw ++ [t.2.1]))

theorem chooseStep (g : CompressionTables) (seeds : ProbComp S.Node) (pk : S.Node) (hw : S.vp.params.n ≠ 16)
    (i : (Port S M).Domain) (s : History M) :
    (simulateQ (SM_DT_TCR_oracles (problem S F g seeds) pk) (instImpl g.1 i)).run s =
    simulateQ (ansImpl (spec := hS St Blk) g.1) ((chooseImpl S F g.2 pk i).run s) := by
  rcases i with n|q|tm|t
  · refine (congrArg (fun z => StateT.run z s)
      (simulateQ_spec_query (SM_DT_TCR_oracles (problem S F g seeds) pk) (.inl n))).trans ?_
    simp [SM_DT_TCR_oracles, chooseImpl, ansImpl, unifFwdAnswerImpl]
  · refine (congrArg (fun z => StateT.run z s)
      (simulateQ_pure (SM_DT_TCR_oracles (problem S F g seeds) pk) (g.1 q))).trans ?_
    rfl
  · refine (congrArg (fun z => StateT.run z s)
      (simulateQ_spec_query (SM_DT_TCR_oracles (problem S F g seeds) pk) (.inr (.inl tm)))).trans ?_
    obtain ⟨qs,tw⟩ := s
    change (SM_DT_TCR_challengeOracle (problem S F g seeds) pk tm).run (qs,tw) = _
    by_cases h : F.cap ≤ qs.length ∨ ¬ TweakFresh Prod.fst qs tw tm.1 <;>
      simp [SM_DT_TCR_challengeOracle, problem, chooseImpl, h, readF_eval S g, collection_eval S g hw, F.inputs_eq, value] <;> rfl
  · refine (congrArg (fun z => StateT.run z s)
      (simulateQ_spec_query (SM_DT_TCR_oracles (problem S F g seeds) pk) (.inr (.inr t)))).trans ?_
    obtain ⟨qs,tw⟩ := s
    change (collectionOracle (Q := Bytes 22 × M) Prod.fst (problem S F g seeds).thColl pk t).run (qs,tw) = _
    by_cases h : TweakReserved (Q := Bytes 22 × M) Prod.fst qs t.2.1 <;>
      simp [collectionOracle, problem, chooseImpl, h, readF_eval S g, collection_eval S g hw, F.inputs_eq, value] <;> rfl


def pickPair (g512 : CF Chain512 Block512) (seeds : ProbComp S.Node) (A : Adversary S M) :
    Reader (Candidate S) := do
  let pk ← liftM seeds
  let (st,qs,_) ← (simulateQ (chooseImpl S F g512 pk) A.choose).run ([],[])
  let (j,m) ← A.forge st pk
  match qs[j]? with
  | none =>
    return (pk,Vector.replicate 22 0,F.message m,F.message m)
  | some (t,m₀) => return (pk,t,F.message m,F.message m₀)

variable [DecidableEq M]

theorem experiment_eq (g : CompressionTables) (seeds : ProbComp S.Node) (A : Adversary S M)
    (hw : S.vp.params.n ≠ 16) :
    SM_DT_TCR_Experiment (atTables S F g seeds A) =
      (simulateQ (ansImpl (spec := hS St Blk) g.1) (pickPair S F g.2 seeds A) >>= fun p =>
        pure (decide (p.2.2.1 ≠ p.2.2.2 ∧ value S g p.1 p.2.1 p.2.2.1 = value S g p.1 p.2.1 p.2.2.2))) := by
  unfold SM_DT_TCR_Experiment pickPair atTables
  simp only [simulateQ_bind, bind_assoc]
  rw [simulateQ_ansImpl_liftM]
  change (seeds >>= _) = _
  apply bind_congr
  intro pk
  refine (congrArg (· >>= _) (simulateQ_run_simulateQ_eq_of_step _ _ _ _ (chooseStep S F g seeds pk hw) A.choose ([],[]))).trans ?_
  apply bind_congr
  rintro ⟨st,qs,tw⟩
  apply bind_congr
  rintro ⟨j,m⟩
  cases h : qs[j]? with
  | none => simp
  | some tm =>
    obtain ⟨t,m₀⟩ := tm
    simp only [simulateQ_pure, pure_bind]
    change pure (decide (m ≠ m₀ ∧ (tablePrimitives g S.vp.params).Thash pk t (F.inputs m) =
      (tablePrimitives g S.vp.params).Thash pk t (F.inputs m₀))) =
      pure (decide (F.message m ≠ F.message m₀ ∧ value S g pk t (F.message m) = value S g pk t (F.message m₀)))
    refine congrArg pure (decide_eq_decide.mpr ?_)
    apply and_congr F.message_injective.ne_iff.symm
    rw [F.inputs_eq m, F.inputs_eq m₀]
    rfl

theorem chooseStep_bound (g512 : CF Chain512 Block512) (pk : S.Node) (i : (Port S M).Domain) (s : History M) :
    IsQueryBoundP ((chooseImpl S F g512 pk i).run s) (fun z => z.isRight = true) (if i.isRight then 2 else 0) := by
  obtain ⟨qs,tw⟩ := s
  rcases i with n|q|tm|t
  · simp [chooseImpl]
  · simp [chooseImpl]
  · simp only [chooseImpl, StateT.run_mk, Sum.isRight_inr, ite_true]
    split
    · simp
    · simpa [bind_pure_comp, isQueryBoundP_map_iff] using (readF_bound S pk tm.1 (F.message tm.2))
  · simp only [chooseImpl, StateT.run_mk, Sum.isRight_inr, ite_true]
    split
    · simp
    · simpa [bind_pure_comp, isQueryBoundP_map_iff] using (collection_bound S g512 pk t.2.1 t.2.2)

theorem bound (g512 : CF Chain512 Block512) (seeds : ProbComp S.Node) (hw : S.vp.params.n ≠ 16)
    (A : Adversary S M) (q₁ q₂ : ℕ)
    (hq : IsQueryBoundP A.choose (fun i => i.isRight = true) q₁)
    (hf : ∀ st pk, IsQueryBoundP (A.forge st pk) (fun i => i.isRight = true) q₂) :
    prT ($ᵗ (CF St Blk) >>= fun g => SM_DT_TCR_Experiment (atTables S F (g,g512) seeds A)) ≤
      (((q₁*2+q₂+3)^2 : ℕ) : ℝ≥0∞) * ((2:ℝ≥0∞)^(8*S.vp.params.n))⁻¹ := by
  simp_rw [experiment_eq S F _ seeds A hw]
  apply SingletonHash.bound S g512 _ (q₁*2+q₂)
  unfold pickPair
  refine (isQueryBoundP_bind (m := q₁*2+q₂) (isQueryBoundP_liftM_isRight seeds) (fun pk _ => ?_)).mono (by simp)
  apply isQueryBoundP_bind (hq.simulateQ_run_of_step_le
    (fun t ht s => by simpa [ht] using chooseStep_bound S F g512 pk t s)
    (fun t ht s => by simpa [ht] using chooseStep_bound S F g512 pk t s) ([],[]))
  rintro ⟨st,qs,tw⟩ _
  refine (isQueryBoundP_bind (m := 0) (hf st pk) ?_).mono (by omega)
  rintro ⟨j,m⟩ _
  dsimp only
  split <;> simp


def chain : Member S S.Node where
  cap := Reduction.wotsStepTargetsT S.vp
  message := id
  inputs := fun m => [m]
  inputs_eq := fun _ => rfl
  message_injective := Function.injective_id

abbrev Single := {xs : List S.Node // xs.length = 1}

def classOne : Member S (Single S) where
  cap := Reduction.arityTargets S.vp 1
  message := oneNode S
  inputs := Subtype.val
  inputs_eq := oneNode_eq S
  message_injective := fun x y h => Subtype.ext ((oneNode_eq S x).trans ((congrArg (fun a => [a]) h).trans (oneNode_eq S y).symm))

theorem chain_problem (g : CompressionTables) (seeds : ProbComp S.Node) :
    problem S (chain S) g seeds = Reduction.wotsTcrProblemT S.vp (tablePrimitives g S.vp.params) seeds := rfl

theorem class_problem (g : CompressionTables) (seeds : ProbComp S.Node) :
    problem S (classOne S) g seeds = Reduction.thashArityProblemT S.vp (tablePrimitives g S.vp.params) seeds 1 := rfl

theorem mixed_bound (seeds : ProbComp S.Node) (hw : S.vp.params.n ≠ 16)
    (A : CF Chain512 Block512 → Adversary S M) (q₁ q₂ : ℕ)
    (hq : ∀ d, IsQueryBoundP (A d).choose (fun i => i.isRight = true) q₁)
    (hf : ∀ d st pk, IsQueryBoundP ((A d).forge st pk) (fun i => i.isRight = true) q₂) :
    prT (do
      let d ← $ᵗ (CF Chain512 Block512)
      let g ← $ᵗ (CF St Blk)
      SM_DT_TCR_Experiment (atTables S F (g,d) seeds (A d))) ≤
      (((q₁*2+q₂+3)^2 : ℕ) : ℝ≥0∞) * ((2:ℝ≥0∞)^(8*S.vp.params.n))⁻¹ :=
  prT_bind_le_of_forall_le _ _ fun d _ => bound S F d seeds hw (A d) q₁ q₂ (hq d) (hf d)
def wotsAdversary (g : CompressionTables) (seeds : ProbComp S.Node) (A : Adversary S S.Node) :
    SM_DT_TCR_Adversary (Reduction.wotsTcrProblemT S.vp (tablePrimitives g S.vp.params) seeds) :=
  atTables S (chain S) g seeds A

theorem wots_bound (seeds : ProbComp S.Node) (hw : S.vp.params.n ≠ 16)
    (A : CF Chain512 Block512 → Adversary S S.Node) (q₁ q₂ : ℕ)
    (hq : ∀ d, IsQueryBoundP (A d).choose (fun i => i.isRight = true) q₁)
    (hf : ∀ d st pk, IsQueryBoundP ((A d).forge st pk) (fun i => i.isRight = true) q₂) :
    prT (do
      let d ← $ᵗ (CF Chain512 Block512)
      let g ← $ᵗ (CF St Blk)
      SM_DT_TCR_Experiment (wotsAdversary S (g,d) seeds (A d))) ≤
      (((q₁*2+q₂+3)^2 : ℕ) : ℝ≥0∞) * ((2:ℝ≥0∞)^(8*S.vp.params.n))⁻¹ :=
  mixed_bound S (chain S) seeds hw A q₁ q₂ hq hf

def arityOneAdversary (g : CompressionTables) (seeds : ProbComp S.Node) (A : Adversary S (Single S)) :
    SM_DT_TCR_Adversary (Reduction.thashArityProblemT S.vp (tablePrimitives g S.vp.params) seeds 1) :=
  atTables S (classOne S) g seeds A

theorem arityOne_bound (seeds : ProbComp S.Node) (hw : S.vp.params.n ≠ 16)
    (A : CF Chain512 Block512 → Adversary S (Single S)) (q₁ q₂ : ℕ)
    (hq : ∀ d, IsQueryBoundP (A d).choose (fun i => i.isRight = true) q₁)
    (hf : ∀ d st pk, IsQueryBoundP ((A d).forge st pk) (fun i => i.isRight = true) q₂) :
    prT (do
      let d ← $ᵗ (CF Chain512 Block512)
      let g ← $ᵗ (CF St Blk)
      SM_DT_TCR_Experiment (arityOneAdversary S (g,d) seeds (A d))) ≤
      (((q₁*2+q₂+3)^2 : ℕ) : ℝ≥0∞) * ((2:ℝ≥0∞)^(8*S.vp.params.n))⁻¹ :=
  mixed_bound S (classOne S) seeds hw A q₁ q₂ hq hf

end MIdeal.SingletonTcr
