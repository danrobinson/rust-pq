import PQ.QROM.ExactTcr
import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTTCR
import VCVio.Quantum.Oracle.Classical

/-!
# Fidelity of the exact SM-DT-TCR game to VCVio's `SM_DT_TCR_Experiment`

`tcrExp` (`PQ/QROM/ExactTcr.lean`) restates VCVio's SM-DT-TCR game for a uniformly random
tweakable hash and quantum adversaries.  This file proves that, restricted to classical
(coin-free) adversaries, it IS VCVio's game at a uniformly random tweakable hash.

* `fidProblem cap Th : SM_DT_TCR_Problem Unit Sd Tw Msg Y`: VCVio's problem with
  `th.eval P t m = Th (P, (t, m))`, `th.seedGen = $ᵗ Sd`, `numTargets = cap`, and the collection
  the one-member family whose member is the same function (this is the collection of the exact
  game; for other collections see `PQ/QROM/ExactGenColl.lean`).
* `FidAdv Sd Tw Msg Y`: a classical two-phase adversary that reaches the hash only through
  classical queries: `choose : OracleComp (hash + (challenge + collection)) State`,
  `forge : State → Sd → OracleComp hash (ℕ × Msg)`.  It has no private coins.
* `FidAdv.honest cap A Th : SM_DT_TCR_Adversary (fidProblem cap Th)`: the adversary of VCVio's
  game obtained by answering the hash queries of `A` with `Th` (`simulateQ`).
* `fidEmb n A.choose`, `fidPh2 A.forge`: the embedding into the exact game.  Hash queries become
  basis-state quantum queries on the port of the phase (`fidQuery`: prepare `|x, 0⟩`, call,
  measure); challenge and collection queries become the classical requests of the `IAdv`; the
  classical state is the classical output of phase 1, on the trivial register.  `n` bounds the
  number of requests; requests beyond `n` are answered `none` by the embedding itself (this
  never happens under the hypothesis `hb` below).

## Results

* `fid_chal_step`, `fid_coll_step`: the challenger `tcrCh` of the exact game simulates VCVio's
  `SM_DT_TCR_challengeOracle` and `collectionOracle` step by step (answers, rejections, cap,
  tweak freshness, state), under the state correspondence `fidSt s = (s.chal, s.coll.map fst)`.
* `fid_tcrExp_eq`: for every adversary with at most `n` challenge/collection queries on every
  path, `tcrExp (embedding) = avg_Th SM_DT_TCR_Advantage (A.honest cap Th)`.
* `fid_tcr_classical_le`: hence `tcr_exact_le` is a bound on VCVio's advantage, averaged over
  the random hash: at most `q₁` hash queries in `choose` and `q₂` in `forge` give
  `avg_Th SM_DT_TCR_Advantage ≤ (√((2q₂+1)²/|Y|) + 2q₁/√|Sd|)²`.

Adversaries with a uniform coin drawn at the start of the first phase are covered in
`PQ/QROM/FidelityCoin.lean`.  Not covered: coins sampled adaptively (unboundedly many) during
`choose`, and coins of `forge` (VCVio's `SM_DT_TCR_Adversary` type allows both).
-/

open OracleComp OracleSpec TweakableHash ENNReal Quantum Matrix
open scoped Kronecker ComplexOrder

set_option linter.unusedSectionVars false

universe w w₂

namespace PQ.QROM
variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]

/-- A classical query `t` on port `b` of the two-port hash oracle. -/
noncomputable def fidQuery (b : Bool) (t : X) :
    QComp (qrom2Spec X Y) (QReg.of Unit) (QReg.of Unit) Y :=
  (QComp.act (B := QReg.of (X × Y))
      (DSubInstrument.classical (B := fun _ ↦ X × Y) (fun _ : Unit ↦ ())
        (fun _ ↦ (t, (0 : Y))))).bind fun _ ↦
    (QuantumComp₂.query (L := LocalSig.instruments) (spec := qrom2Spec X Y) b (QReg.of Unit)
        (Equiv.prodPUnit (X × Y)).symm).bind fun _ ↦
      QComp.act (A := QReg.of ((X × Y) × Unit))
        (DSubInstrument.classical (B := fun _ ↦ Unit) (fun m : (X × Y) × Unit ↦ m.1.2) (fun _ ↦ ()))

theorem fid_step_single (G : Bool → X → Y) (b : Bool) (m : X × Y) (d : Unit) :
    (((twoRuntime G).step b)).branch () (Matrix.single (m, d) (m, d) 1) =
      Matrix.single ((m.1, m.2 + G b m.1), d) ((m.1, m.2 + G b m.1), d) 1 := by
  have h := congrArg SubState.matrix (post_oracleQuery_basis (G b) m)
  rw [DSubInstrument.matrix_post, SubState.matrix_basis, SubState.matrix_basis] at h
  show ((oracleQuery (G b)).frame Unit).branch () _ = _
  rw [DSubInstrument.branch_frame_single, h, Matrix.single_kronecker_single, one_mul]

theorem fid_run_query (G : Bool → X → Y) (b : Bool) (t : X) (d : Unit) (y : Y) :
    ((twoRuntime G).run₂ .instruments (fidQuery b t)).branch y (Matrix.single ((), d) ((), d) 1) =
      if G b t = y then Matrix.single ((), d) ((), d) 1 else 0 := by
  rw [fidQuery, QuantumRuntime.run₂_act_bind, DSubInstrument.branch_bind_unit,
    LinearMap.comp_apply, DSubInstrument.branch_frame_single, DSubInstrument.branch_classical_basis]
  simp only [↓reduceDIte, cast_eq]
  rw [Matrix.single_kronecker_single, one_mul, QuantumRuntime.run₂_query_bind,
    DSubInstrument.branch_bind_unit, LinearMap.comp_apply, QuantumRuntime.queryStep_branch_apply,
    SubInstrument.branch_relabel, SubInstrument.branch_relabel, conj_basisMatrix_equiv_single]
  simp only [QuantumRuntime.queryEquivIn_apply, Equiv.prodPUnit_symm_apply]
  rw [DSubInstrument.branch_frame_single, fid_step_single, Matrix.single_kronecker_single, one_mul,
    conj_basisMatrix_equiv_single, QuantumRuntime.run₂_act, SubInstrument.bind_pure]
  simp only [QuantumRuntime.queryEquivOut_apply]
  rw [DSubInstrument.branch_frame_single, DSubInstrument.branch_classical_basis]
  by_cases h : G b t = y <;> simp [h, Matrix.single_kronecker_single]


theorem fid_run_query_self (G : Bool → X → Y) (b : Bool) (t : X) :
    ((twoRuntime G).run₂ .instruments (fidQuery b t)).branch (G b t)
      (Matrix.single ((), ()) ((), ()) 1) = Matrix.single ((), ()) ((), ()) 1 := by
  rw [fid_run_query]; simp

theorem fid_run_query_ne (G : Bool → X → Y) (b : Bool) (t : X) {y : Y} (hy : y ≠ G b t) :
    ((twoRuntime G).run₂ .instruments (fidQuery b t)).branch y
      (Matrix.single ((), ()) ((), ()) 1) = 0 := by
  rw [fid_run_query]; simp [Ne.symm hy]

/-! ## Sequencing after a fixed-register program -/
section D
variable {spec : QuantumOracleSpec.{0, 0}} {L : LocalSig.{1, 0}} {A B : QReg} {α : Type}
  {W : QReg → Type w}

/-- Continue after a fixed-register program with a general program. -/
def fidBind (x : QuantumComp L spec (QuantumComp₂.Leaf B α) A) (k : α → QuantumComp L spec W B) :
    QuantumComp L spec W A :=
  QuantumComp.bind x fun _ p ↦ p.casesOn fun h a ↦ h ▸ k a

theorem fid_run_fidBind (R : QuantumRuntime spec) (I : L.Interp)
    (x : QuantumComp L spec (QuantumComp₂.Leaf B α) A) (k : α → QuantumComp L spec W B) (c : Σ u, W u)
    (σ : Matrix (A × R.D) (A × R.D) ℂ) :
    (R.run I (fidBind x k)).branch c σ =
      ∑' a, (R.run I (k a)).branch c ((R.run₂ I (B := B) (α := α) x).branch a σ) := by
  unfold fidBind
  rw [QuantumRuntime.run_bind, DSubInstrument.branch_bind_apply,
    ← (QuantumComp₂.leafEquiv B α).tsum_eq]
  rfl

theorem fid_run_fidBind_det (R : QuantumRuntime spec) (I : L.Interp)
    (x : QuantumComp L spec (QuantumComp₂.Leaf B α) A) (k : α → QuantumComp L spec W B) (c : Σ u, W u)
    (σ : Matrix (A × R.D) (A × R.D) ℂ) (σ' : Matrix (B × R.D) (B × R.D) ℂ) (a₀ : α)
    (h₀ : (R.run₂ I (B := B) (α := α) x).branch a₀ σ = σ') (h : ∀ a, a ≠ a₀ → (R.run₂ I (B := B) (α := α) x).branch a σ = 0) :
    (R.run I (fidBind x k)).branch c σ = (R.run I (k a₀)).branch c σ' := by
  rw [fid_run_fidBind, tsum_eq_single a₀ fun a ha ↦ by rw [h a ha, map_zero], h₀]

theorem fidBind_isQueryBound {x : QuantumComp L spec (QuantumComp₂.Leaf B α) A} {k : α → QuantumComp L spec W B}
    {b₁ b₂ : spec.Port → ℕ} (hx : x.IsQueryBound b₁) (hk : ∀ a, (k a).IsQueryBound b₂) :
    (fidBind x k).IsQueryBound (b₁ + b₂) :=
  QuantumComp.IsQueryBound.bind hx fun _ p ↦ by
    obtain ⟨rfl, a⟩ := p
    exact hk a

theorem fidBind_bind {W₂ : QReg → Type w₂} (x : QuantumComp L spec (QuantumComp₂.Leaf B α) A)
    (k : α → QuantumComp L spec W B) (l : ∀ u, W u → QuantumComp L spec W₂ u) :
    (fidBind x k).bind l = fidBind x fun a ↦ (k a).bind l := by
  unfold fidBind
  rw [QuantumComp.bind_assoc]
  congr 1
  funext u p
  obtain ⟨rfl, a⟩ := p
  rfl
end D


/-! ## Classical adversaries -/

variable {Sd Tw Msg : Type}

/-- The classical hash-query oracle. -/
abbrev fidHashSpec (Sd Tw Msg Y : Type) : OracleSpec (Dom Sd Tw Msg) := Dom Sd Tw Msg →ₒ Y
/-- The collection oracle's signature for the one-member collection (VCVio's `collectionSpec`). -/
abbrev fidCollSpec (Tw Msg Y : Type) : OracleSpec ((_ : Unit) × Tw × Msg) := _ →ₒ Option Y
/-- The oracles of a classical first phase: hash, challenge, collection. -/
abbrev fidSpec (Sd Tw Msg Y : Type) :=
  fidHashSpec Sd Tw Msg Y + (SM_DT_TCR_challengeSpec Tw Msg Y + fidCollSpec Tw Msg Y)

/-- A classical (coin-free) two-phase SM-DT-TCR adversary that reaches the hash only through
classical queries. -/
structure FidAdv (Sd Tw Msg Y : Type) where
  State : Type
  choose : OracleComp (fidSpec Sd Tw Msg Y) State
  forge : State → Sd → OracleComp (fidHashSpec Sd Tw Msg Y) (ℕ × Msg)

/-- VCVio's SM-DT-TCR problem for the hash `Th`: uniform seed, cap `cap`, and the collection
whose one member is the same function. -/
def fidProblem [SampleableType Sd] (cap : ℕ) (Th : Dom Sd Tw Msg → Y) :
    SM_DT_TCR_Problem Unit Sd Tw Msg Y where
  th := ⟨$ᵗ Sd, fun P t m ↦ Th (P, (t, m))⟩
  thColl := ⟨fun _ ↦ Msg, fun _ P t m ↦ Th (P, (t, m))⟩
  numTargets := cap

/-- Answer hash queries with `Th`; pass challenge and collection queries on. -/
def fidInst [SampleableType Sd] (cap : ℕ) (Th : Dom Sd Tw Msg → Y) :
    QueryImpl (fidSpec Sd Tw Msg Y) (OracleComp (unifSpec +
      (SM_DT_TCR_challengeSpec Tw Msg Y + collectionSpec (fidProblem cap Th).thColl))) :=
  fun t ↦ match t with
    | .inl q => pure (Th q)
    | .inr r => liftM (OracleSpec.query (spec := unifSpec +
      (SM_DT_TCR_challengeSpec Tw Msg Y + collectionSpec (fidProblem cap Th).thColl)) (.inr r))

/-- The adversary of VCVio's game at the hash `Th`. -/
def FidAdv.honest [SampleableType Sd] (cap : ℕ) (a : FidAdv Sd Tw Msg Y)
    (Th : Dom Sd Tw Msg → Y) : SM_DT_TCR_Adversary (fidProblem cap Th) where
  State := a.State
  choose := simulateQ (fidInst cap Th) a.choose
  forge st P := simulateQ (fun q ↦ (pure (Th q) : ProbComp Y)) (a.forge st P)

/-- The request of the exact game for a challenge / collection query. -/
def fidReq : (Tw × Msg) ⊕ ((_ : Unit) × Tw × Msg) → (Tw × Msg) ⊕ (Tw × Msg)
  | .inl tm => .inl tm
  | .inr q => .inr q.2

section Emb
variable [Fintype Sd] [DecidableEq Sd] [Fintype Tw] [DecidableEq Tw] [Fintype Msg]
  [DecidableEq Msg]

/-- Classical output of phase 1, on the trivial register. -/
abbrev FidOut (State : Type) : QReg → Type := QuantumComp₂.Leaf (QReg.of Unit) State

/-- Interactive adversaries of the exact game with classical output `State`. -/
abbrev FidIAdv (Sd Tw Msg Y : Type) [Fintype Sd] [DecidableEq Sd] [Fintype Tw] [DecidableEq Tw]
    [Fintype Msg] [DecidableEq Msg] [Fintype Y] [DecidableEq Y] (State : Type) (n : ℕ)
    (u : QReg) :=
  IAdv LocalSig.instruments.{0} (qrom2Spec (Dom Sd Tw Msg) Y) ((Tw × Msg) ⊕ (Tw × Msg)) (Option Y)
    (FidOut State) n u

/-- The leaves of a segment: a final output or a request with its continuations. -/
abbrev FidLeaf (Sd Tw Msg Y : Type) [Fintype Sd] [DecidableEq Sd] [Fintype Tw] [DecidableEq Tw]
    [Fintype Msg] [DecidableEq Msg] [Fintype Y] [DecidableEq Y] (State : Type) (n : ℕ)
    (u : QReg) :=
  FidOut State u ⊕ (((Tw × Msg) ⊕ (Tw × Msg)) × (Option Y → FidIAdv Sd Tw Msg Y State n u))

/-- The segment type of an interactive adversary with `n + 1` requests. -/
abbrev FidSeg (Sd Tw Msg Y : Type) [Fintype Sd] [DecidableEq Sd] [Fintype Tw] [DecidableEq Tw]
    [Fintype Msg] [DecidableEq Msg] [Fintype Y] [DecidableEq Y] (State : Type) (n : ℕ) :=
  QuantumComp LocalSig.instruments.{0} (qrom2Spec (Dom Sd Tw Msg) Y)
    (FidLeaf Sd Tw Msg Y State n) (QReg.of Unit)

/-- **The embedding of a classical first phase** into the exact game, with at most `n`
requests: hash queries become basis-state quantum queries on port `false`; challenge and
collection queries become requests (answered `none` by the embedding beyond `n` requests). -/
noncomputable def fidEmb {State : Type} :
    (n : ℕ) → OracleComp (fidSpec Sd Tw Msg Y) State → FidIAdv Sd Tw Msg Y State n (QReg.of Unit)
  | 0 => OracleComp.construct (C := fun _ ↦ FidIAdv Sd Tw Msg Y State 0 (QReg.of Unit))
      (fun a ↦ QuantumComp.pure ⟨rfl, a⟩)
      (fun t _ ih ↦ match t, ih with
        | .inl q, ih => fidBind (fidQuery false q) ih
        | .inr (.inl _), ih => ih none
        | .inr (.inr _), ih => ih none)
  | n + 1 => OracleComp.construct (C := fun _ ↦ FidSeg Sd Tw Msg Y State n)
      (fun a ↦ QuantumComp.pure (.inl ⟨rfl, a⟩))
      (fun t k ih ↦ match t, k, ih with
        | .inl q, _, ih => fidBind (W := FidLeaf Sd Tw Msg Y State n) (fidQuery false q) ih
        | .inr (.inl tm), k, _ =>
          QuantumComp.pure (.inr (.inl tm, fun resp ↦ fidEmb n (k resp)))
        | .inr (.inr q), k, _ =>
          QuantumComp.pure (.inr (.inr q.2, fun resp ↦ fidEmb n (k resp))))

/-- **The embedding of a classical second phase**: hash queries become basis-state quantum
queries on port `true`. -/
noncomputable def fidPh2 {State : Type} (forge : State → Sd → OracleComp (fidHashSpec Sd Tw Msg Y) (ℕ × Msg))
    (P : Sd) (u : QReg) (o : FidOut State u) :
    QuantumComp LocalSig.instruments.{0} (qrom2Spec (Dom Sd Tw Msg) Y) (fun _ ↦ ℕ × Msg) u :=
  o.casesOn fun h st ↦ h ▸ ((forge st P).toQuantumAt (fun q ↦ fidQuery true q)).forgetReg

end Emb

section Sim
variable [Fintype Sd] [DecidableEq Sd] [Fintype Tw] [DecidableEq Tw] [Fintype Msg]
  [DecidableEq Msg] [SampleableType Sd]

/-- VCVio's game state for the histories of the exact game. -/
def fidSt (s : TcrState Tw Msg) : SM_DT_TCR_State Tw Msg := (s.chal, s.coll.map Prod.fst)

theorem fid_chal_step (cap : ℕ) (Th : Dom Sd Tw Msg → Y) (P : Sd) (tm : Tw × Msg)
    (s : TcrState Tw Msg) :
    (SM_DT_TCR_challengeOracle (fidProblem cap Th) P tm).run (fidSt s) =
      pure ((tcrCh cap (rowOf Th P) (.inl tm) s).1,
        fidSt (tcrCh cap (rowOf Th P) (.inl tm) s).2) := by
  simp only [tcrCh]
  split_ifs with h
  · have : cap ≤ s.chal.length ∨
        ¬ TweakFresh Prod.fst s.chal (s.coll.map Prod.fst) tm.1 := by
      rcases h with h | h | h
      · exact Or.inl h
      · right
        rintro ⟨h1, -⟩
        obtain ⟨e, he, heq⟩ := List.mem_map.1 h
        exact h1 ⟨e, he, heq⟩
      · exact Or.inr fun h' ↦ h'.2 h
    simp [SM_DT_TCR_challengeOracle, fidSt, fidProblem, this]
  · have : ¬ (cap ≤ s.chal.length ∨
        ¬ TweakFresh Prod.fst s.chal (s.coll.map Prod.fst) tm.1) := by
      rintro (h' | h')
      · exact h (Or.inl h')
      · refine h' ⟨?_, fun hc ↦ h (Or.inr (Or.inr hc))⟩
        rintro ⟨e, he, heq⟩
        exact h (Or.inr (Or.inl (List.mem_map.2 ⟨e, he, heq⟩)))
    simp [SM_DT_TCR_challengeOracle, fidSt, fidProblem, this, rowOf]

theorem fid_coll_step (cap : ℕ) (Th : Dom Sd Tw Msg → Y) (P : Sd)
    (q : (_ : Unit) × Tw × Msg) (s : TcrState Tw Msg) :
    (collectionOracle (Q := Tw × Msg) Prod.fst (fidProblem cap Th).thColl P q).run (fidSt s) =
      pure ((tcrCh cap (rowOf Th P) (.inr q.2) s).1,
        fidSt (tcrCh cap (rowOf Th P) (.inr q.2) s).2) := by
  simp only [tcrCh]
  split_ifs with h
  · have : TweakReserved Prod.fst s.chal q.2.1 := by
      obtain ⟨e, he, heq⟩ := List.mem_map.1 h
      exact ⟨e, he, heq⟩
    simp [collectionOracle, fidSt, this]
  · have : ¬ TweakReserved Prod.fst s.chal q.2.1 := by
      rintro ⟨e, he, heq⟩
      exact h (List.mem_map.2 ⟨e, he, heq⟩)
    simp [collectionOracle, fidSt, this, fidProblem, rowOf]


/-- The basis state of the trivial program and runtime registers. -/
noncomputable abbrev fidσ : Matrix (Unit × Unit) (Unit × Unit) ℂ := Matrix.single ((), ()) ((), ()) 1

/-- The predicate "is a challenge or collection query". -/
abbrev fidIsReq {ι κ : Type} (t : ι ⊕ κ) : Prop := t.isRight = true

theorem fid_sim (cap : ℕ) (Th : Dom Sd Tw Msg → Y) (P : Sd) {State : Type} (n : ℕ)
    (oa : OracleComp (fidSpec Sd Tw Msg Y) State) (s : TcrState Tw Msg)
    (hb : IsQueryBoundP oa fidIsReq n) :
    ∃ (a : State) (s' : TcrState Tw Msg),
      (simulateQ (SM_DT_TCR_oracles (fidProblem cap Th) P)
        (simulateQ (fidInst cap Th) oa)).run (fidSt s) = pure (a, fidSt s') ∧
      ∀ {W₂ : QReg → Type} (K : ∀ u, FidOut State u → TcrState Tw Msg →
          QuantumComp LocalSig.instruments.{0} (qrom2Spec (Dom Sd Tw Msg) Y) W₂ u)
        (c : Σ u, W₂ u),
        ((twoRuntime fun _ ↦ Th).run .instruments
          (IAdv.flat (tcrCh cap (rowOf Th P)) K n s (fidEmb n oa))).branch c fidσ =
        ((twoRuntime fun _ ↦ Th).run .instruments (K (QReg.of Unit) ⟨rfl, a⟩ s')).branch c
          fidσ := by
  induction n generalizing oa s with
  | zero =>
    induction oa using OracleComp.inductionOn with
    | pure a => exact ⟨a, s, rfl, fun K c ↦ rfl⟩
    | query_bind t k ih =>
      rw [isQueryBoundP_query_bind_iff] at hb
      rcases t with q | tm | q
      · obtain ⟨a, s', h1, h2⟩ := ih (Th q) (hb.2 (Th q))
        refine ⟨a, s', ?_, fun K c ↦ ?_⟩
        · rw [simulateQ_bind, simulateQ_spec_query]
          simpa [fidInst] using h1
        · have e : IAdv.flat (tcrCh cap (rowOf Th P)) K 0 s
              (fidEmb 0 (liftM (OracleSpec.query (spec := fidSpec Sd Tw Msg Y) (.inl q)) >>= k)) =
              fidBind (fidQuery false q) fun y ↦
                IAdv.flat (tcrCh cap (rowOf Th P)) K 0 s (fidEmb 0 (k y)) :=
            fidBind_bind (fidQuery false q) (fun y ↦ fidEmb 0 (k y)) _
          rw [e]
          exact (fid_run_fidBind_det (twoRuntime fun _ ↦ Th) .instruments _ _ c _ _ (Th q)
            (fid_run_query_self _ _ _) (fun y hy ↦ fid_run_query_ne _ _ _ hy)).trans (h2 K c)
      · exact absurd hb.1 (by simp [fidIsReq])
      · exact absurd hb.1 (by simp [fidIsReq])
  | succ n ihn =>
    induction oa using OracleComp.inductionOn generalizing s with
    | pure a => exact ⟨a, s, rfl, fun K c ↦ rfl⟩
    | query_bind t k ih =>
      rw [isQueryBoundP_query_bind_iff] at hb
      rcases t with q | tm | q
      · obtain ⟨a, s', h1, h2⟩ := ih (Th q) s (hb.2 (Th q))
        refine ⟨a, s', ?_, fun K c ↦ ?_⟩
        · rw [simulateQ_bind, simulateQ_spec_query]
          simpa [fidInst] using h1
        · have e : IAdv.flat (tcrCh cap (rowOf Th P)) K (n + 1) s
              (fidEmb (n + 1)
                (liftM (OracleSpec.query (spec := fidSpec Sd Tw Msg Y) (.inl q)) >>= k)) =
              fidBind (fidQuery false q) fun y ↦
                IAdv.flat (tcrCh cap (rowOf Th P)) K (n + 1) s (fidEmb (n + 1) (k y)) :=
            fidBind_bind (fidQuery false q) (fun y ↦ fidEmb (n + 1) (k y)) _
          rw [e]
          exact (fid_run_fidBind_det (twoRuntime fun _ ↦ Th) .instruments _ _ c _ _ (Th q)
            (fid_run_query_self _ _ _) (fun y hy ↦ fid_run_query_ne _ _ _ hy)).trans (h2 K c)
      · obtain ⟨a, s', h1, h2⟩ := ihn (k (tcrCh cap (rowOf Th P) (.inl tm) s).1)
          (tcrCh cap (rowOf Th P) (.inl tm) s).2 (hb.2 _)
        refine ⟨a, s', ?_, fun K c ↦ h2 K c⟩
        rw [simulateQ_bind, simulateQ_spec_query]
        simp only [fidInst]
        rw [simulateQ_bind, simulateQ_spec_query]
        rw [StateT.run_bind]
        refine Eq.trans (congrArg (· >>= _) (fid_chal_step cap Th P tm s)) ?_
        rw [pure_bind]
        exact h1
      · obtain ⟨a, s', h1, h2⟩ := ihn (k (tcrCh cap (rowOf Th P) (.inr q.2) s).1)
          (tcrCh cap (rowOf Th P) (.inr q.2) s).2 (hb.2 _)
        refine ⟨a, s', ?_, fun K c ↦ h2 K c⟩
        rw [simulateQ_bind, simulateQ_spec_query]
        simp only [fidInst]
        rw [simulateQ_bind, simulateQ_spec_query]
        rw [StateT.run_bind]
        refine Eq.trans (congrArg (· >>= _) (fid_coll_step cap Th P q s)) ?_
        rw [pure_bind]
        exact h1


/-- Against the oracle unitaries, the program of a classical hash-only algorithm, started on
the basis state, reports the value of the algorithm with weight one. -/
theorem fid_run_toQuantumAt {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    [AddCommGroup Y] {α : Type} (G : Bool → X → Y) (b : Bool)
    (oa : OracleComp (X →ₒ Y) α) (r : α) :
    (((twoRuntime G).run₂ .instruments (oa.toQuantumAt fun q ↦ fidQuery b q)).branch r fidσ =
        fidσ ∧ r = evalWithAnswerFn (QueryImpl.ofFn (G b)) oa) ∨
      (((twoRuntime G).run₂ .instruments (oa.toQuantumAt fun q ↦ fidQuery b q)).branch r fidσ =
        0 ∧ r ≠ evalWithAnswerFn (QueryImpl.ofFn (G b)) oa) := by
  classical
  induction oa using OracleComp.inductionOn with
  | pure x =>
    rw [OracleComp.toQuantumAt_pure, QuantumRuntime.run₂_pure, evalWithAnswerFn_pure]
    by_cases h : r = x
    · subst h
      left
      simp
    · right
      exact ⟨by simp [SubInstrument.branch_pure_of_ne h], h⟩
  | query_bind t k ih =>
    have e : (((twoRuntime G).run₂ .instruments
        ((liftM ((X →ₒ Y).query t) >>= k).toQuantumAt fun q ↦ fidQuery b q)).branch r) fidσ =
        (((twoRuntime G).run₂ .instruments ((k (G b t)).toQuantumAt fun q ↦ fidQuery b q)).branch
          r) fidσ := by
      rw [OracleComp.toQuantumAt_query_bind, QuantumRuntime.run₂_bind,
        DSubInstrument.branch_bind_apply, tsum_eq_single (G b t) fun y hy ↦ by
          rw [fid_run_query_ne G b t hy, map_zero], fid_run_query_self]
    rw [e, evalWithAnswerFn_bind, evalWithAnswerFn_liftM_query]
    exact ih (G b t)


theorem fid_joint_basis : joint (A := QReg.of Unit) (SubState.basis ()) = fidσ := by
  unfold joint
  rw [SubState.matrix_basis, Matrix.single_kronecker_single, one_mul]

theorem fid_forgetReg {α : Type}
    (x : QComp (qrom2Spec (Dom Sd Tw Msg) Y) (QReg.of Unit) (QReg.of Unit) α) :
    x.forgetReg = fidBind (W := fun _ ↦ α) x fun r ↦ QuantumComp.pure r := by
  unfold QuantumComp₂.forgetReg fidBind
  congr 1
  funext u p
  obtain ⟨rfl, a⟩ := p
  rfl

/-- The exact game with the embedded classical adversary, at the seed `P` and the hash `Th`:
the winning indicator of the classical run. -/
theorem fid_realProb (cap : ℕ) (Th : Dom Sd Tw Msg → Y) (P : Sd) (A : FidAdv Sd Tw Msg Y) (n : ℕ)
    (hb : IsQueryBoundP A.choose fidIsReq n) :
    ∃ (st : A.State) (s' : TcrState Tw Msg),
      (simulateQ (SM_DT_TCR_oracles (fidProblem cap Th) P)
        (simulateQ (fidInst cap Th) A.choose)).run ([], []) = pure (st, fidSt s') ∧
      realProb .instruments (A := QReg.of Unit) (SubState.basis ()) (tcrCh cap) tcrInit n (fidEmb n A.choose)
        (fidPh2 A.forge) tcrWin P Th =
      ind (tcrWin (rowOf Th P) (evalWithAnswerFn (QueryImpl.ofFn Th) (A.forge st P)) s') := by
  obtain ⟨st, s', h1, h2⟩ := fid_sim cap Th P n A.choose tcrInit hb
  refine ⟨st, s', h1, ?_⟩
  unfold realProb composite leafProb
  rw [fid_joint_basis]
  simp only [h2]
  have hps : (fidσ : Matrix (Unit × Unit) (Unit × Unit) ℂ).PosSemidef := by
    rw [← fid_joint_basis]; exact joint_posSemidef _
  refine (leafProb_phase2K (twoRuntime fun _ ↦ Th) .instruments (fidPh2 A.forge) P (QReg.of Unit)
    ⟨rfl, st⟩ s' hps (tcrWin (rowOf Th P))).trans ?_
  have e : fidPh2 A.forge P (QReg.of Unit) ⟨rfl, st⟩ =
      fidBind (W := fun _ ↦ ℕ × Msg) ((A.forge st P).toQuantumAt fun q ↦ fidQuery true q)
        fun r ↦ QuantumComp.pure r := fid_forgetReg _
  unfold leafProb
  rw [e]
  have hbr : ∀ c, ((twoRuntime fun _ ↦ Th).run .instruments
      (fidBind (W := fun _ ↦ ℕ × Msg) ((A.forge st P).toQuantumAt fun q ↦ fidQuery true q)
        fun r ↦ QuantumComp.pure r)).branch c fidσ =
      ((twoRuntime fun _ ↦ Th).run .instruments (QuantumComp.pure (X := fun _ ↦ ℕ × Msg)
        (evalWithAnswerFn (QueryImpl.ofFn Th) (A.forge st P)))).branch c fidσ := fun c ↦ by
    refine fid_run_fidBind_det (twoRuntime fun _ ↦ Th) .instruments _ _ c _ _ _ ?_ fun r hr ↦ ?_
    · rcases fid_run_toQuantumAt (fun _ ↦ Th) true (A.forge st P)
        (evalWithAnswerFn (QueryImpl.ofFn Th) (A.forge st P)) with h | h
      · exact h.1
      · exact absurd rfl h.2
    · rcases fid_run_toQuantumAt (fun _ ↦ Th) true (A.forge st P) r with h | h
      · exact absurd h.2 hr
      · exact h.1
  simp only [hbr]
  have hp := leafProb_pure (R := twoRuntime fun _ ↦ Th) (I := LocalSig.Interp.instruments.{0})
    (W := fun _ ↦ ℕ × Msg) (A := QReg.of Unit)
    (evalWithAnswerFn (QueryImpl.ofFn Th) (A.forge st P)) fidσ
    (fun p ↦ tcrWin (rowOf Th P) p.2 s')
  unfold leafProb at hp
  have ht : (fidσ : Matrix (Unit × Unit) (Unit × Unit) ℂ).trace = 1 :=
    Matrix.trace_single_eq_same _ _
  refine hp.trans ?_
  rw [ht, Complex.one_re, ENNReal.ofReal_one, one_mul]


theorem fid_simulateQ_pure {α : Type} (Th : Dom Sd Tw Msg → Y)
    (oa : OracleComp (fidHashSpec Sd Tw Msg Y) α) :
    simulateQ (fun q ↦ (pure (Th q) : ProbComp Y)) oa =
      pure (evalWithAnswerFn (QueryImpl.ofFn Th) oa) := by
  induction oa using OracleComp.inductionOn with
  | pure x => rfl
  | query_bind t k ih =>
    rw [simulateQ_bind, simulateQ_spec_query, pure_bind, ih, evalWithAnswerFn_bind,
      evalWithAnswerFn_liftM_query]
    rfl

open Classical in
theorem fid_uniform_bool (g : Sd → Bool) :
    𝒟[(do let P ← $ᵗ Sd; pure (g P) : ProbComp Bool)] {true} =
      avg fun P ↦ ind (g P = true) := by
  have e : (do let P ← $ᵗ Sd; pure (g P) : ProbComp Bool) = g <$> ($ᵗ Sd) := by
    rw [map_eq_bind_pure_comp]; rfl
  rw [e, ← prEvent_eq_evalDist_singleton, prEvent_map, SampleableType.prEvent_uniformSample]
  unfold avg
  rw [Finset.card_filter, Nat.cast_sum, div_eq_mul_inv, Finset.sum_mul]
  refine Finset.sum_congr rfl fun P _ ↦ ?_
  beta_reduce
  by_cases h : g P = true
  · rw [ind_of_true h]; simp [h]
  · rw [ind_of_false h]; simp [h]

open Classical in
/-- VCVio's SM-DT-TCR advantage of the honest classical adversary at the hash `Th` is the
average over the seed of the exact game's winning probability at `Th`. -/
theorem fid_advantage (cap : ℕ) (Th : Dom Sd Tw Msg → Y) (A : FidAdv Sd Tw Msg Y) (n : ℕ)
    (hb : IsQueryBoundP A.choose fidIsReq n) :
    SM_DT_TCR_Advantage (A.honest cap Th) =
      avg fun P : Sd ↦ realProb .instruments (A := QReg.of Unit) (SubState.basis ()) (tcrCh cap)
        tcrInit n (fidEmb n A.choose) (fidPh2 A.forge) tcrWin P Th := by
  choose st s' h1 h2 using fun P ↦ fid_realProb cap Th P A n hb
  have hexp : SM_DT_TCR_Experiment (A.honest cap Th) = (do
      let P ← $ᵗ Sd
      pure (decide (tcrWin (rowOf Th P)
        (evalWithAnswerFn (QueryImpl.ofFn Th) (A.forge (st P) P)) (s' P))) : ProbComp Bool) := by
    unfold SM_DT_TCR_Experiment
    refine bind_congr fun P ↦ ?_
    have h1' := h1 P
    simp only [FidAdv.honest] at h1' ⊢
    rw [h1', pure_bind]
    simp only [fidSt]
    rw [fid_simulateQ_pure, pure_bind]
    rcases hg : (s' P).chal[(evalWithAnswerFn (QueryImpl.ofFn Th) (A.forge (st P) P)).1]? with
      _ | ⟨t, mj⟩
    · simp [tcrWin, hg]
    · refine congrArg pure ?_
      rw [Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff]
      simp [tcrWin, hg, fidProblem, rowOf]
  unfold SM_DT_TCR_Advantage
  rw [hexp, fid_uniform_bool]
  exact avg_congr fun P ↦ by rw [h2 P]; simp


/-- **Fidelity of the exact SM-DT-TCR game.** -/
theorem fid_tcrExp_eq (cap : ℕ) (A : FidAdv Sd Tw Msg Y) (n : ℕ)
    (hb : IsQueryBoundP A.choose fidIsReq n) :
    tcrExp .instruments (A := QReg.of Unit) (SubState.basis ()) cap n (fidEmb n A.choose)
        (fidPh2 A.forge) =
      avg fun Th : Dom Sd Tw Msg → Y ↦ SM_DT_TCR_Advantage (A.honest cap Th) := by
  unfold tcrExp twoPhaseExp
  rw [avg_comm]
  exact avg_congr fun Th ↦ (fid_advantage cap Th A n hb).symm

/-- The predicate "is a hash query". -/
abbrev fidIsHash {ι κ : Type} (t : ι ⊕ κ) : Prop := t.isLeft = true

theorem fid_isQueryBound_query (b : Bool) (t : Dom Sd Tw Msg) {bd : Bool → ℕ} (h : 0 < bd b) :
    (fidQuery (Y := Y) b t).IsQueryBound bd := by
  rw [fidQuery, QComp.isQueryBound_act_bind_iff]
  intro _
  refine (QuantumComp₂.isQueryBound_bind (b₁ := bd) (b₂ := 0) ?_
    fun _ ↦ QComp.isQueryBound_act _ _).mono (add_zero _).le
  exact (QuantumComp₂.isQueryBound_query_iff _ _ _ _).mpr h

theorem fid_emb_isQueryBound {State : Type} (n : ℕ)
    (oa : OracleComp (fidSpec Sd Tw Msg Y) State) (q : ℕ) (hq : IsQueryBoundP oa fidIsHash q) :
    IAdv.IsQueryBound n (fidEmb n oa) (firstBudget q) := by
  intro St ch s
  induction n generalizing oa s q with
  | zero =>
    induction oa using OracleComp.inductionOn generalizing q with
    | pure a => exact QuantumComp.isQueryBound_pure _ _
    | query_bind t k ih =>
      rw [isQueryBoundP_query_bind_iff] at hq
      rcases t with t | tm | t
      · have e : IAdv.flat ch (IAdv.stop (L := LocalSig.instruments.{0})
            (spec := qrom2Spec (Dom Sd Tw Msg) Y)) 0 s
            (fidEmb 0 (liftM (OracleSpec.query (spec := fidSpec Sd Tw Msg Y) (.inl t)) >>= k)) =
            fidBind (fidQuery false t) fun y : Y ↦ IAdv.flat ch (IAdv.stop
              (L := LocalSig.instruments.{0}) (spec := qrom2Spec (Dom Sd Tw Msg) Y)) 0 s
                (fidEmb 0 (k y)) :=
          fidBind_bind (fidQuery false t) (fun y : Y ↦ fidEmb 0 (k y)) _
        rw [e]
        have hq0 : 0 < q := by simpa [fidIsHash] using hq.1
        refine (fidBind_isQueryBound (b₁ := firstBudget 1) (b₂ := firstBudget (q - 1))
          (fid_isQueryBound_query false t (by simp [firstBudget])) fun y : Y ↦ ih y (q := q - 1)
            (by simpa [fidIsHash] using hq.2 y)).mono fun i ↦ ?_
        cases i
        · simp [firstBudget]; omega
        · simp [firstBudget]
      · exact ih none (q := q) (by simpa [fidIsHash] using hq.2 none)
      · exact ih none (q := q) (by simpa [fidIsHash] using hq.2 none)
  | succ n ihn =>
    induction oa using OracleComp.inductionOn generalizing q s with
    | pure a => exact QuantumComp.isQueryBound_pure _ _
    | query_bind t k ih =>
      rw [isQueryBoundP_query_bind_iff] at hq
      rcases t with t | tm | t
      · have e : IAdv.flat ch (IAdv.stop (L := LocalSig.instruments.{0})
            (spec := qrom2Spec (Dom Sd Tw Msg) Y)) (n + 1) s
            (fidEmb (n + 1)
              (liftM (OracleSpec.query (spec := fidSpec Sd Tw Msg Y) (.inl t)) >>= k)) =
            fidBind (fidQuery false t) fun y : Y ↦ IAdv.flat ch (IAdv.stop
              (L := LocalSig.instruments.{0}) (spec := qrom2Spec (Dom Sd Tw Msg) Y)) (n + 1) s
                (fidEmb (n + 1) (k y)) :=
          fidBind_bind (fidQuery false t) (fun y : Y ↦ fidEmb (n + 1) (k y)) _
        rw [e]
        have hq0 : 0 < q := by simpa [fidIsHash] using hq.1
        refine (fidBind_isQueryBound (b₁ := firstBudget 1) (b₂ := firstBudget (q - 1))
          (fid_isQueryBound_query false t (by simp [firstBudget])) fun y : Y ↦ ih y (s := s) (q := q - 1)
            (by simpa [fidIsHash] using hq.2 y)).mono fun i ↦ ?_
        cases i
        · simp [firstBudget]; omega
        · simp [firstBudget]
      · exact ihn (oa := k (ch (.inl tm) s).1) (s := (ch (.inl tm) s).2) (q := q)
          (by simpa [fidIsHash] using hq.2 _)
      · exact ihn (oa := k (ch (.inr t.2) s).1) (s := (ch (.inr t.2) s).2) (q := q)
          (by simpa [fidIsHash] using hq.2 _)

theorem fid_ph2_isQueryBound {State : Type}
    (forge : State → Sd → OracleComp (fidHashSpec Sd Tw Msg Y) (ℕ × Msg)) (q : ℕ)
    (hq : ∀ st P, IsTotalQueryBound (forge st P) q) (P : Sd) (u : QReg) (o : FidOut State u) :
    (fidPh2 forge P u o).IsQueryBound (secondBudget q) := by
  obtain ⟨rfl, st⟩ := o
  refine (QuantumComp₂.isQueryBound_forgetReg (OracleComp.isQueryBound_toQuantumAt
    (b := secondBudget 1) (fun t ↦ fid_isQueryBound_query true t (by simp [secondBudget]))
    (hq st P))).mono fun i ↦ ?_
  cases i <;> simp [secondBudget]

/-- VCVio's SM-DT-TCR advantage, bound. -/
theorem fid_tcr_classical_le [Inhabited Tw] (cap : ℕ) (A : FidAdv Sd Tw Msg Y) (n q₁ q₂ : ℕ)
    (hb : IsQueryBoundP A.choose fidIsReq n) (h1 : IsQueryBoundP A.choose fidIsHash q₁)
    (h2 : ∀ st P, IsTotalQueryBound (A.forge st P) q₂) :
    (avg fun Th : Dom Sd Tw Msg → Y ↦ SM_DT_TCR_Advantage (A.honest cap Th)) ≤
      (((2 * (q₂ : ℝ≥0∞) + 1) ^ 2 / (Fintype.card Y : ℝ≥0∞)) ^ (2⁻¹ : ℝ) +
        2 * q₁ * ((Fintype.card Sd : ℝ≥0∞)⁻¹) ^ (2⁻¹ : ℝ)) ^ 2 := by
  rw [← fid_tcrExp_eq cap A n hb]
  exact tcr_exact_le (fid_emb_isQueryBound n A.choose q₁ h1)
    (fid_ph2_isQueryBound A.forge q₂ h2)

end Sim
end PQ.QROM

#print axioms PQ.QROM.fid_chal_step
#print axioms PQ.QROM.fid_coll_step
#print axioms PQ.QROM.fid_sim
#print axioms PQ.QROM.fid_advantage
#print axioms PQ.QROM.fid_tcrExp_eq
#print axioms PQ.QROM.fid_emb_isQueryBound
#print axioms PQ.QROM.fid_tcr_classical_le
