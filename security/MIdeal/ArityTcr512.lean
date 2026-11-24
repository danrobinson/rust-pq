import MIdeal.ThashReader
import Ideal.Games.TcrBridge

namespace MIdeal.Sha512.ArityTcr
open Ideal Ideal.HP MLink SLHDSA OracleComp OracleSpec TweakableHash ENNReal
variable (S : Sha2Set) (arity : ℕ)

abbrev Msg := {xs : List S.Node // xs.length = arity}
abbrev History := SM_DT_TCR_State (Bytes 22) (Msg S arity)
abbrev Game := SM_DT_TCR_challengeSpec (Bytes 22) (Msg S arity) S.Node +
  (((_ : Unit) × Bytes 22 × List S.Node) →ₒ Option S.Node)
abbrev Port := unifSpec + (hS Chain512 Block512 + Game S arity)

structure Adversary where
  State : Type
  choose : OracleComp (Port S arity) State
  forge : State → S.Node → SHAReader (ℕ × Msg S arity)

local instance (g : CompressionTables) : DecidableEq (tablePrimitives g S.vp.params).AdrsKey :=
  inferInstanceAs (DecidableEq (Bytes 22))
local instance (g : CompressionTables) : DecidableEq (tablePrimitives g S.vp.params).Y :=
  inferInstanceAs (DecidableEq S.Node)

attribute [local irreducible] Reduction.arityTargets

def problem (g : CompressionTables) (seeds : ProbComp S.Node) :
    SM_DT_TCR_Problem Unit S.Node (Bytes 22) (Msg S arity) S.Node where
  th := { seedGen := seeds, eval := fun pk t m => (tablePrimitives g S.vp.params).Thash pk t m.val }
  thColl := { Msg := fun _ => List S.Node, eval := fun _ => (tablePrimitives g S.vp.params).Thash }
  numTargets := Reduction.arityTargets S.vp arity

theorem problem_eq (g : CompressionTables) (seeds : ProbComp S.Node) :
    problem S arity g seeds = Reduction.thashArityProblemT S.vp (tablePrimitives g S.vp.params) seeds arity := rfl

def atTables (g : CompressionTables) (seeds : ProbComp S.Node) (A : Adversary S arity) :
    SM_DT_TCR_Adversary (problem S arity g seeds) where
  State := A.State
  choose := simulateQ (instImpl g.2) A.choose
  forge := fun st pk => simulateQ (ansImpl (spec := hS Chain512 Block512) g.2) (A.forge st pk)

def chooseImpl (g256 : CF St Blk) (pk : S.Node) :
    QueryImpl (Port S arity) (StateT (History S arity) SHAReader) := fun
  | .inl n => liftM ((unifSpec + hS Chain512 Block512).query (.inl n))
  | .inr (.inl t) => liftM ((unifSpec + hS Chain512 Block512).query (.inr t))
  | .inr (.inr (.inl tm)) => StateT.mk fun (qs,tw) =>
      if Reduction.arityTargets S.vp arity ≤ qs.length ∨ ¬ TweakFresh Prod.fst qs tw tm.1 then
        pure (none,(qs,tw))
      else do
        let h ← readThash S g256 pk tm.1 tm.2.val
        return (some h,(qs ++ [tm],tw))
  | .inr (.inr (.inr t)) => StateT.mk fun (qs,tw) =>
      if TweakReserved (Q := Bytes 22 × Msg S arity) Prod.fst qs t.2.1 then pure (none,(qs,tw))
      else do
        let h ← readThash S g256 pk t.2.1 t.2.2
        return (some h,(qs,tw ++ [t.2.1]))

theorem chooseStep (g : CompressionTables) (seeds : ProbComp S.Node) (pk : S.Node) (hw : S.vp.params.n ≠ 16)
    (i : (Port S arity).Domain) (s : History S arity) :
    (simulateQ (SM_DT_TCR_oracles (problem S arity g seeds) pk) (instImpl g.2 i)).run s =
    simulateQ (ansImpl (spec := hS Chain512 Block512) g.2) ((chooseImpl S arity g.1 pk i).run s) := by
  rcases i with n|q|tm|t
  · refine (congrArg (fun z => StateT.run z s)
      (simulateQ_spec_query (SM_DT_TCR_oracles (problem S arity g seeds) pk) (.inl n))).trans ?_
    simp [SM_DT_TCR_oracles, chooseImpl, ansImpl, unifFwdAnswerImpl]
  · refine (congrArg (fun z => StateT.run z s)
      (simulateQ_pure (SM_DT_TCR_oracles (problem S arity g seeds) pk) (g.2 q))).trans ?_
    rfl
  · refine (congrArg (fun z => StateT.run z s)
      (simulateQ_spec_query (SM_DT_TCR_oracles (problem S arity g seeds) pk) (.inr (.inl tm)))).trans ?_
    obtain ⟨qs,tw⟩ := s
    change (SM_DT_TCR_challengeOracle (problem S arity g seeds) pk tm).run (qs,tw) = _
    by_cases h : Reduction.arityTargets S.vp arity ≤ qs.length ∨ ¬ TweakFresh Prod.fst qs tw tm.1 <;>
      simp [SM_DT_TCR_challengeOracle, problem, chooseImpl, h, readThash_eval S g hw] <;> rfl
  · refine (congrArg (fun z => StateT.run z s)
      (simulateQ_spec_query (SM_DT_TCR_oracles (problem S arity g seeds) pk) (.inr (.inr t)))).trans ?_
    obtain ⟨qs,tw⟩ := s
    change (collectionOracle (Q := Bytes 22 × Msg S arity) Prod.fst (problem S arity g seeds).thColl pk t).run (qs,tw) = _
    by_cases h : TweakReserved (Q := Bytes 22 × Msg S arity) Prod.fst qs t.2.1 <;>
      simp [collectionOracle, problem, chooseImpl, h, readThash_eval S g hw] <;> rfl


def pickPair (g256 : CF St Blk) (seeds : ProbComp S.Node) (A : Adversary S arity) :
    SHAReader (HashInput S arity × HashInput S arity) := do
  let pk ← liftM seeds
  let (st,qs,_) ← (simulateQ (chooseImpl S arity g256 pk) A.choose).run ([],[])
  let (j,m) ← A.forge st pk
  match qs[j]? with
  | none =>
    let x := (pk,Vector.replicate 22 0,m)
    return (x,x)
  | some (t,m₀) => return ((pk,t,m),(pk,t,m₀))

theorem experiment_eq (g : CompressionTables) (seeds : ProbComp S.Node) (A : Adversary S arity)
    (hw : S.vp.params.n ≠ 16) :
    SM_DT_TCR_Experiment (atTables S arity g seeds A) =
      (simulateQ (ansImpl (spec := hS Chain512 Block512) g.2) (pickPair S arity g.1 seeds A) >>= fun p =>
        pure (decide (p.1 ≠ p.2 ∧ value S g p.1 = value S g p.2))) := by
  unfold SM_DT_TCR_Experiment pickPair atTables
  simp only [simulateQ_bind, bind_assoc]
  rw [simulateQ_ansImpl_liftM]
  change (seeds >>= _) = _
  apply bind_congr
  intro pk
  refine (congrArg (· >>= _) (simulateQ_run_simulateQ_eq_of_step _ _ _ _ (chooseStep S arity g seeds pk hw) A.choose ([],[]))).trans ?_
  apply bind_congr
  rintro ⟨st,qs,tw⟩
  apply bind_congr
  rintro ⟨j,m⟩
  cases h : qs[j]? with
  | none => simp
  | some tm =>
    obtain ⟨t,m₀⟩ := tm
    simp only [simulateQ_pure, pure_bind]
    change pure (decide (m ≠ m₀ ∧ _)) = pure (decide (((pk,t,m) : HashInput S arity) ≠ (pk,t,m₀) ∧ _))
    have he : (((pk,t,m) : HashInput S arity) ≠ (pk,t,m₀)) ↔ m ≠ m₀ := by
      constructor
      · intro hn eq; exact hn (by rw [eq])
      · intro hn eq; exact hn (Prod.mk.inj (Prod.mk.inj eq).2).2
    simp only [he]
    rfl

theorem bound (g256 : CF St Blk) (seeds : ProbComp S.Node) (hw : S.vp.params.n ≠ 16)
    (hm : arity ≠ 1) (A : Adversary S arity) (q : ℕ)
    (hq : IsQueryBoundP (pickPair S arity g256 seeds A) (fun i => i.isRight = true) q) :
    prT ($ᵗ (CF Chain512 Block512) >>= fun g =>
      SM_DT_TCR_Experiment (atTables S arity (g256,g) seeds A)) ≤
      (((q + 2*((38+S.vp.params.n*arity)/128+2))^2 : ℕ) : ℝ≥0∞) * ((2:ℝ≥0∞)^(8*S.vp.params.n))⁻¹ := by
  simp_rw [experiment_eq S arity _ seeds A hw]
  exact collision_bound S g256 hw arity q hm _ hq

def stepCost : (Port S arity).Domain → ℕ
  | .inl _ => 0
  | .inr (.inl _) => 1
  | .inr (.inr (.inl _)) => thashCost S arity
  | .inr (.inr (.inr t)) => thashCost S t.2.2.length

theorem step_bound (g256 : CF St Blk) (pk : S.Node) (i : (Port S arity).Domain) (s : History S arity) :
    IsQueryBoundP ((chooseImpl S arity g256 pk i).run s) (fun z => z.isRight = true) (stepCost S arity i) := by
  obtain ⟨qs,tw⟩ := s
  rcases i with n|q|tm|t
  · simp [chooseImpl, stepCost]
  · simp [chooseImpl, stepCost]
  · simp only [chooseImpl, stepCost, StateT.run_mk]
    split
    · simp
    · simpa [bind_pure_comp, isQueryBoundP_map_iff, tm.2.property] using (readThash_bound S g256 pk tm.1 tm.2.val)
  · simp only [chooseImpl, stepCost, StateT.run_mk]
    split
    · simp
    · simpa [bind_pure_comp, isQueryBoundP_map_iff] using (readThash_bound S g256 pk t.2.1 t.2.2)

theorem choose_bound {α : Type} (g256 : CF St Blk) (pk : S.Node) (P : OracleComp (Port S arity) α)
    (q B : ℕ) (hq : IsQueryBoundP P (fun i => i.isRight = true) q)
    (hB : AllQueriesSatisfy P (fun i => stepCost S arity i ≤ B)) (s : History S arity) :
    IsQueryBoundP ((simulateQ (chooseImpl S arity g256 pk) P).run s) (fun i => i.isRight = true) (q*B) := by
  induction P using OracleComp.inductionOn generalizing q s with
  | pure x => simp
  | query_bind t f ih =>
    rw [isQueryBoundP_query_bind_iff] at hq
    rw [allQueriesSatisfy_query_bind_iff] at hB
    rw [simulateQ_query_bind, StateT.run_bind]
    simp only [OracleQuery.input_query, OracleQuery.cont_query, monadLift_self, id_eq]
    cases t with
    | inl n =>
      simpa [stepCost] using isQueryBoundP_bind (step_bound S arity g256 pk (.inl n) s)
        (fun x _ => ih x.1 q (by simpa using hq.2 x.1) (hB.2 x.1) x.2)
    | inr i =>
      have pos : 0 < q := hq.1.resolve_left (by simp)
      have cost : B + (q-1)*B = q*B := by
        cases q <;> simp_all [Nat.succ_mul, Nat.add_comm]
      rw [← cost]
      exact isQueryBoundP_bind ((step_bound S arity g256 pk (.inr i) s).mono hB.1)
        (fun x _ => ih x.1 (q-1) (by simpa using hq.2 x.1) (hB.2 x.1) x.2)


def actualAdversary (g : CompressionTables) (seeds : ProbComp S.Node) (A : Adversary S arity) :
    SM_DT_TCR_Adversary (Reduction.thashArityProblemT S.vp (tablePrimitives g S.vp.params) seeds arity) :=
  atTables S arity g seeds A

theorem arity_bound (g256 : CF St Blk) (seeds : ProbComp S.Node) (hw : S.vp.params.n ≠ 16)
    (hm : arity ≠ 1) (A : Adversary S arity) (q₁ B q₂ : ℕ)
    (hq : IsQueryBoundP A.choose (fun i => i.isRight = true) q₁)
    (hB : AllQueriesSatisfy A.choose (fun i => stepCost S arity i ≤ B))
    (hf : ∀ st pk, IsQueryBoundP (A.forge st pk) (fun i => i.isRight = true) q₂) :
    prT ($ᵗ (CF Chain512 Block512) >>= fun g =>
      SM_DT_TCR_Experiment (actualAdversary S arity (g256,g) seeds A)) ≤
      (((q₁*B+q₂ + 2*((38+S.vp.params.n*arity)/128+2))^2 : ℕ) : ℝ≥0∞) * ((2:ℝ≥0∞)^(8*S.vp.params.n))⁻¹ := by
  apply bound S arity g256 seeds hw hm A (q₁*B+q₂)
  unfold pickPair
  refine (isQueryBoundP_bind (m := q₁*B+q₂) (isQueryBoundP_liftM_isRight seeds) (fun pk _ => ?_)).mono (by simp)
  apply isQueryBoundP_bind (choose_bound S arity g256 pk A.choose q₁ B hq hB ([],[]))
  rintro ⟨st,qs,tw⟩ _
  refine (isQueryBoundP_bind (m := 0) (hf st pk) ?_).mono (by omega)
  rintro ⟨j,m⟩ _
  dsimp only
  split <;> simp


/-- Average over independent SHA-256 and SHA-512 compression tables. The
adversary may depend on the entire SHA-256 table before either phase. -/
theorem mixed_bound (seeds : ProbComp S.Node) (hw : S.vp.params.n ≠ 16) (hm : arity ≠ 1)
    (A : CF St Blk → Adversary S arity) (q₁ B q₂ : ℕ)
    (hq : ∀ c, IsQueryBoundP (A c).choose (fun i => i.isRight = true) q₁)
    (hB : ∀ c, AllQueriesSatisfy (A c).choose (fun i => stepCost S arity i ≤ B))
    (hf : ∀ c st pk, IsQueryBoundP ((A c).forge st pk) (fun i => i.isRight = true) q₂) :
    prT (do
      let c ← $ᵗ (CF St Blk)
      let g ← $ᵗ (CF Chain512 Block512)
      SM_DT_TCR_Experiment (actualAdversary S arity (c,g) seeds (A c))) ≤
      (((q₁*B+q₂ + 2*((38+S.vp.params.n*arity)/128+2))^2 : ℕ) : ℝ≥0∞) * ((2:ℝ≥0∞)^(8*S.vp.params.n))⁻¹ :=
  prT_bind_le_of_forall_le _ _ (fun c _ => arity_bound S arity c seeds hw hm (A c) q₁ B q₂ (hq c) (hB c) (hf c))

end MIdeal.Sha512.ArityTcr
