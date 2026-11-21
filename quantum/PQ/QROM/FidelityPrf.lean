import PQ.QROM.FidelityGen
import PQ.QROM.ExactPrf
import VCVio.CryptoFoundations.PRF

/-!
# Fidelity of the exact PRF game to VCVio's PRF experiments

`prfExactReal` / `prfExactIdeal` (`PQ/QROM/ExactPrf.lean`), restricted to classical adversaries
with one uniform coin and classical queries to the random function `F : K × Dm → Y`, are VCVio's
`prfRealExperiment` / `prfIdealExperiment` for the scheme `eval k d = F (k, d)` with uniform
key, averaged over the uniformly random `F`.

* `fidSEmb`, `fidS_sim`: the embedding of `PQ/QROM/FidelityGen.lean` for the one-port signature
  `qromSpec X Y` (hash queries: VCVio's `Quantum.classicalQuery`).
* `fidPrfScheme F : PRFScheme K Dm Y`, `FidPrfAdv Ω K Dm Y`, `FidPrfAdv.honest A F`.
* `fid_prf_ideal_eager`: **eager vs lazy ideal oracle**: VCVio's ideal experiment (lazy cached
  random oracle `prfIdealQueryImpl`) on the honest adversary has the probability of the average,
  over the coin and a uniform `R : Dm → Y`, of the classical run answered by `R`.  (VCVio's
  `evalDist_simulateQ_randomOracle_run'_empty_eq_uniformTable`, transported through the coin
  and the hash instantiation.)
* `fid_prf_real_eq`, `fid_prf_ideal_eq`: the two fidelity equalities.
* `fid_prf_classical_le`: `prfExact_real_le_ideal_add` as a bound for VCVio's experiments.
-/

open OracleComp OracleSpec ENNReal Quantum Matrix PRFScheme
open scoped Kronecker ComplexOrder

set_option linter.unusedSectionVars false

namespace PQ.QROM

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
  {ρ : Type} {rspec : OracleSpec.{0, 0} ρ} {Req Resp St State : Type}

/-! ## The embedding for the one-port signature -/

/-- Interactive adversaries over the one-port signature, on the trivial register. -/
abbrev FidSIAdv (X Y : Type) [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (Req Resp State : Type) (n : ℕ) (u : QReg) :=
  IAdv LocalSig.instruments.{0} (qromSpec X Y) Req Resp (FidOut State) n u

/-- The leaves of a segment. -/
abbrev FidSLeaf (X Y : Type) [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (Req Resp State : Type) (n : ℕ) (u : QReg) :=
  FidOut State u ⊕ (Req × (Resp → FidSIAdv X Y Req Resp State n u))

/-- **The embedding of a classical algorithm** with hash queries and requests, one port. -/
noncomputable def fidSEmb (cd : FidCodec rspec Req Resp) :
    (n : ℕ) → OracleComp ((X →ₒ Y) + rspec) State → FidSIAdv X Y Req Resp State n (QReg.of Unit)
  | 0 => OracleComp.construct (C := fun _ ↦ FidSIAdv X Y Req Resp State 0 (QReg.of Unit))
      (fun a ↦ QuantumComp.pure ⟨rfl, a⟩)
      (fun t _ ih ↦ match t, ih with
        | .inl q, ih => fidBind (classicalQuery q) ih
        | .inr r, ih => ih (cd.dflt r))
  | n + 1 => OracleComp.construct
      (C := fun _ ↦ QuantumComp LocalSig.instruments.{0} (qromSpec X Y)
        (FidSLeaf X Y Req Resp State n) (QReg.of Unit))
      (fun a ↦ QuantumComp.pure (.inl ⟨rfl, a⟩))
      (fun t k ih ↦ match t, k, ih with
        | .inl q, _, ih => fidBind (W := FidSLeaf X Y Req Resp State n) (classicalQuery q) ih
        | .inr r, k, _ =>
          QuantumComp.pure (.inr (cd.enc r, fun resp ↦ fidSEmb cd n (k (cd.dec r resp)))))

theorem fidS_run_query_self (H : X → Y) (t : X) :
    ((additiveOracleRuntime H).run₂ .instruments (classicalQuery t)).branch (H t) fidσ = fidσ := by
  have h := run_classicalQuery_branch_of_basis H (additiveOracleRuntime_step_branch_single H) t ()
    (H t)
  rw [if_pos rfl] at h
  exact h

theorem fidS_run_query_ne (H : X → Y) (t : X) {y : Y} (hy : y ≠ H t) :
    ((additiveOracleRuntime H).run₂ .instruments (classicalQuery t)).branch y fidσ = 0 := by
  have h := run_classicalQuery_branch_of_basis H (additiveOracleRuntime_step_branch_single H) t ()
    y
  rw [if_neg (Ne.symm hy)] at h
  exact h

/-- **Simulation**, one port. -/
theorem fidS_sim (cd : FidCodec rspec Req Resp) (H : X → Y) (ch : Req → St → Resp × St)
    (n : ℕ) (oa : OracleComp ((X →ₒ Y) + rspec) State) (s : St)
    (hb : IsQueryBoundP oa fidIsReq n) {W₂ : QReg → Type}
    (K : ∀ u, FidOut State u → St →
      QuantumComp LocalSig.instruments.{0} (qromSpec X Y) W₂ u) (c : Σ u, W₂ u) :
    ((additiveOracleRuntime H).run .instruments
        (IAdv.flat ch K n s (fidSEmb cd n oa))).branch c fidσ =
      ((additiveOracleRuntime H).run .instruments (K (QReg.of Unit)
        ⟨rfl, (fidGRun cd H ch oa s).1⟩ (fidGRun cd H ch oa s).2)).branch c fidσ := by
  induction n generalizing oa s with
  | zero =>
    induction oa using OracleComp.inductionOn with
    | pure a => rfl
    | query_bind t k ih =>
      rw [isQueryBoundP_query_bind_iff] at hb
      rcases t with q | r
      · have e : IAdv.flat ch K 0 s
            (fidSEmb cd 0 (liftM (OracleSpec.query (spec := (X →ₒ Y) + rspec) (.inl q)) >>= k)) =
            fidBind (classicalQuery q) fun y : Y ↦ IAdv.flat ch K 0 s (fidSEmb cd 0 (k y)) :=
          fidBind_bind (classicalQuery q) (fun y : Y ↦ fidSEmb cd 0 (k y)) _
        rw [e]
        exact (fid_run_fidBind_det (additiveOracleRuntime H) .instruments _ _ c _ _ (H q)
          (fidS_run_query_self _ _) (fun y hy ↦ fidS_run_query_ne _ _ hy)).trans
            (ih (H q) (hb.2 (H q)))
      · exact absurd hb.1 (by simp [fidIsReq])
  | succ n ihn =>
    induction oa using OracleComp.inductionOn generalizing s with
    | pure a => rfl
    | query_bind t k ih =>
      rw [isQueryBoundP_query_bind_iff] at hb
      rcases t with q | r
      · have e : IAdv.flat ch K (n + 1) s
            (fidSEmb cd (n + 1)
              (liftM (OracleSpec.query (spec := (X →ₒ Y) + rspec) (.inl q)) >>= k)) =
            fidBind (classicalQuery q) fun y : Y ↦
              IAdv.flat ch K (n + 1) s (fidSEmb cd (n + 1) (k y)) :=
          fidBind_bind (classicalQuery q) (fun y : Y ↦ fidSEmb cd (n + 1) (k y)) _
        rw [e]
        exact (fid_run_fidBind_det (additiveOracleRuntime H) .instruments _ _ c _ _ (H q)
          (fidS_run_query_self _ _) (fun y hy ↦ fidS_run_query_ne _ _ hy)).trans
            (ih (H q) s (hb.2 (H q)))
      · exact ihn (k (cd.dec r (ch (cd.enc r) s).1)) (ch (cd.enc r) s).2 (hb.2 _)

theorem fidS_emb_isQueryBound (cd : FidCodec rspec Req Resp) (n : ℕ)
    (oa : OracleComp ((X →ₒ Y) + rspec) State) (q : ℕ) (hq : IsQueryBoundP oa fidIsHash q) :
    IAdv.IsQueryBound n (fidSEmb cd n oa) (fun _ ↦ q) := by
  intro St ch s
  induction n generalizing oa s q with
  | zero =>
    induction oa using OracleComp.inductionOn generalizing q with
    | pure a => exact QuantumComp.isQueryBound_pure _ _
    | query_bind t k ih =>
      rw [isQueryBoundP_query_bind_iff] at hq
      rcases t with t | r
      · have e : IAdv.flat ch (IAdv.stop (L := LocalSig.instruments.{0})
            (spec := qromSpec X Y)) 0 s
            (fidSEmb cd 0 (liftM (OracleSpec.query (spec := (X →ₒ Y) + rspec) (.inl t)) >>= k)) =
            fidBind (classicalQuery t) fun y : Y ↦ IAdv.flat ch (IAdv.stop
              (L := LocalSig.instruments.{0}) (spec := qromSpec X Y)) 0 s
                (fidSEmb cd 0 (k y)) :=
          fidBind_bind (classicalQuery t) (fun y : Y ↦ fidSEmb cd 0 (k y)) _
        rw [e]
        have hq0 : 0 < q := by simpa [fidIsHash] using hq.1
        refine (fidBind_isQueryBound (b₁ := fun _ ↦ 1) (b₂ := fun _ ↦ q - 1)
          (isQueryBound_classicalQuery t) fun y : Y ↦ ih y (q := q - 1)
            (by simpa [fidIsHash] using hq.2 y)).mono fun i ↦ ?_
        simp only [Pi.add_apply]
        omega
      · exact ih (cd.dflt r) (q := q) (by simpa [fidIsHash] using hq.2 (cd.dflt r))
  | succ n ihn =>
    induction oa using OracleComp.inductionOn generalizing q s with
    | pure a => exact QuantumComp.isQueryBound_pure _ _
    | query_bind t k ih =>
      rw [isQueryBoundP_query_bind_iff] at hq
      rcases t with t | r
      · have e : IAdv.flat ch (IAdv.stop (L := LocalSig.instruments.{0})
            (spec := qromSpec X Y)) (n + 1) s
            (fidSEmb cd (n + 1)
              (liftM (OracleSpec.query (spec := (X →ₒ Y) + rspec) (.inl t)) >>= k)) =
            fidBind (classicalQuery t) fun y : Y ↦ IAdv.flat ch (IAdv.stop
              (L := LocalSig.instruments.{0}) (spec := qromSpec X Y)) (n + 1) s
                (fidSEmb cd (n + 1) (k y)) :=
          fidBind_bind (classicalQuery t) (fun y : Y ↦ fidSEmb cd (n + 1) (k y)) _
        rw [e]
        have hq0 : 0 < q := by simpa [fidIsHash] using hq.1
        refine (fidBind_isQueryBound (b₁ := fun _ ↦ 1) (b₂ := fun _ ↦ q - 1)
          (isQueryBound_classicalQuery t) fun y : Y ↦ ih y (s := s) (q := q - 1)
            (by simpa [fidIsHash] using hq.2 y)).mono fun i ↦ ?_
        simp only [Pi.add_apply]
        omega
      · exact ihn (oa := k (cd.dec r (ch (cd.enc r) s).1)) (s := (ch (cd.enc r) s).2) (q := q)
          (by simpa [fidIsHash] using hq.2 _)

section Coin

variable {Ω : Type} [Fintype Ω] [Nonempty Ω]

/-- The one-port embedding with a uniform coin. -/
noncomputable def fidSCoinEmb (cd : FidCodec rspec Req Resp)
    (choose : Ω → OracleComp ((X →ₒ Y) + rspec) State) :
    (n : ℕ) → FidSIAdv X Y Req Resp State n (QReg.of Unit)
  | 0 => fidBind (W := FidOut State) (QComp.act (SubInstrument.uniform Ω (QReg.of Unit)))
      fun ω ↦ fidSEmb cd 0 (choose ω)
  | n + 1 => fidBind (W := FidSLeaf X Y Req Resp State n)
      (QComp.act (SubInstrument.uniform Ω (QReg.of Unit))) fun ω ↦ fidSEmb cd (n + 1) (choose ω)

theorem fidSCoin_flat {W₂ : QReg → Type} (cd : FidCodec rspec Req Resp)
    (choose : Ω → OracleComp ((X →ₒ Y) + rspec) State) (ch : Req → St → Resp × St)
    (K : ∀ u, FidOut State u → St →
      QuantumComp LocalSig.instruments.{0} (qromSpec X Y) W₂ u) (n : ℕ) (s : St) :
    IAdv.flat ch K n s (fidSCoinEmb cd choose n) =
      fidBind (QComp.act (SubInstrument.uniform Ω (QReg.of Unit))) fun ω ↦
        IAdv.flat ch K n s (fidSEmb cd n (choose ω)) := by
  cases n with
  | zero => exact fidBind_bind _ (fun ω ↦ fidSEmb cd 0 (choose ω)) _
  | succ n => exact fidBind_bind _ (fun ω ↦ fidSEmb cd (n + 1) (choose ω)) _

theorem fidSCoin_emb_isQueryBound (cd : FidCodec rspec Req Resp)
    (choose : Ω → OracleComp ((X →ₒ Y) + rspec) State) (n q : ℕ)
    (hq : ∀ ω, IsQueryBoundP (choose ω) fidIsHash q) :
    IAdv.IsQueryBound n (fidSCoinEmb cd choose n) (fun _ ↦ q) := by
  intro St ch s
  rw [fidSCoin_flat]
  exact (fidBind_isQueryBound (b₁ := 0) (QComp.isQueryBound_act _ _)
    fun ω ↦ fidS_emb_isQueryBound cd n (choose ω) q (hq ω) St ch s).mono (zero_add _).le

/-- **The one-port game value on embedded classical algorithms**: the probability that the
embedded algorithm with a uniform coin, run against the deterministic challenger `ch` with
quantum access to `H`, ends with an output and a challenger state in `E`, is the average over
the coin of the indicator for the classical run. -/
theorem fidS_qprob (cd : FidCodec rspec Req Resp) (H : X → Y) (ch : Req → St → Resp × St)
    (n : ℕ) (choose : Ω → OracleComp ((X →ₒ Y) + rspec) State) (s : St)
    (hb : ∀ ω, IsQueryBoundP (choose ω) fidIsReq n) (E : State → St → Prop) :
    qprob .instruments H
        (IAdv.flat ch (IAdv.stop (L := LocalSig.instruments.{0}) (spec := qromSpec X Y)) n s
          (fidSCoinEmb cd choose n)) (SubState.basis ()) (fun p ↦ E p.2.1.2 p.2.2) =
      avg fun ω ↦ ind (E (fidGRun cd H ch (choose ω) s).1 (fidGRun cd H ch (choose ω) s).2) := by
  unfold qprob
  rw [evalDistMap_eq_leafProb, fidSCoin_flat]
  have hσ : (SubState.basis (() : (QReg.of Unit))).matrix ⊗ₖ
      (additiveOracleRuntime H).init.matrix = fidσ := fid_joint_basis
  rw [hσ]
  refine (fidGCoin_leafProb (additiveOracleRuntime H) _ fidσ_posSemidef _).trans ?_
  refine avg_congr fun ω ↦ ?_
  unfold leafProb
  simp only [fidS_sim cd H ch n (choose ω) s (hb ω)]
  have hp := leafProb_pure (R := additiveOracleRuntime H) (I := LocalSig.Interp.instruments.{0})
    (W := fun u ↦ FidOut State u × St) (A := QReg.of Unit)
    (⟨rfl, (fidGRun cd H ch (choose ω) s).1⟩, (fidGRun cd H ch (choose ω) s).2) fidσ
    (fun p ↦ E p.2.1.2 p.2.2)
  unfold leafProb at hp
  exact hp.trans ((congrArg (· * _) fidσ_trace).trans (one_mul _))

end Coin

/-! ## PRF -/

section Prf

variable {K Dm Ω : Type} [Fintype K] [DecidableEq K] [Fintype Dm] [DecidableEq Dm]
  [SampleableType K] [SampleableType Y] [SampleableType (Dm → Y)]
  [Fintype Ω] [Nonempty Ω] [SampleableType Ω]

/-- The PRF scheme derived from `F`: uniform key, `eval k d = F (k, d)`. -/
noncomputable def fidPrfScheme (F : K × Dm → Y) : PRFScheme K Dm Y := ⟨$ᵗ K, fun k d ↦ F (k, d)⟩

/-- Requests of the exact PRF game for the queries of the function oracle. -/
def fidPrfCodec (Dm Y : Type) [AddCommGroup Y] : FidCodec (Dm →ₒ Y) Dm Y where
  enc d := d
  dec _ y := y
  dflt _ := (0 : Y)

/-- A classical PRF distinguisher with a uniform coin `ω : Ω` and classical queries to `F`. -/
abbrev FidPrfAdv (Ω K Dm Y : Type) := Ω → OracleComp ((K × Dm →ₒ Y) + (Dm →ₒ Y)) Bool

/-- Answer the queries to `F`; pass the function-oracle queries on. -/
def fidPrfInst (F : K × Dm → Y) :
    QueryImpl ((K × Dm →ₒ Y) + (Dm →ₒ Y)) (OracleComp (PRFOracleSpec Dm Y)) :=
  fun t ↦ match t with
    | .inl q => pure (F q)
    | .inr d => liftM (OracleSpec.query (spec := PRFOracleSpec Dm Y) (.inr d))

/-- VCVio's PRF adversary at the function `F`. -/
noncomputable def fidPrfHonest (A : FidPrfAdv Ω K Dm Y) (F : K × Dm → Y) : PRFAdversary Dm Y :=
  ((liftM ($ᵗ Ω : ProbComp Ω) : OracleComp (PRFOracleSpec Dm Y) Ω) >>= fun ω ↦
    simulateQ (fidPrfInst F) (A ω) : OracleComp (PRFOracleSpec Dm Y) Bool)

/-- The event "the output bit is `true`" on the leaves of the exact game. -/
def fidPrfE : (Σ u, FidOut Bool u × Unit) → Prop := fun p ↦ p.2.1.2 = true

/-- The classical run of a distinguisher with `F` and the answer function `f`. -/
def fidPrfRun (F : K × Dm → Y) (f : Dm → Y) (oa : OracleComp ((K × Dm →ₒ Y) + (Dm →ₒ Y)) Bool) :
    Bool :=
  (fidGRun (fidPrfCodec Dm Y) F (prfExactCh f) oa ()).1

/-! ### Real world -/

theorem fid_prf_real_run (F : K × Dm → Y) (k : K)
    (oa : OracleComp ((K × Dm →ₒ Y) + (Dm →ₒ Y)) Bool) :
    simulateQ (prfRealQueryImpl (fidPrfScheme F) k) (simulateQ (fidPrfInst F) oa) =
      pure (fidPrfRun F (fun d ↦ F (k, d)) oa) := by
  induction oa using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind t k' ih =>
    rw [simulateQ_bind (fidPrfInst F), simulateQ_spec_query, simulateQ_bind]
    rcases t with q | d
    · simp only [fidPrfInst]
      rw [simulateQ_pure, pure_bind]
      exact ih (F q)
    · simp only [fidPrfInst]
      refine Eq.trans (congrArg (· >>= _) (simulateQ_spec_query
        (prfRealQueryImpl (fidPrfScheme F) k) (.inr d))) ?_
      rw [prfRealQueryImpl_apply_inr, pure_bind]
      exact ih _

theorem fid_prf_real_lift {α : Type} (F : K × Dm → Y) (k : K) (oa : ProbComp α) :
    simulateQ (prfRealQueryImpl (fidPrfScheme F) k)
      (liftM oa : OracleComp (PRFOracleSpec Dm Y) α) = oa := by
  unfold prfRealQueryImpl
  rw [QueryImpl.passthrough_add, QueryImpl.simulateQ_add_liftM_left]
  simp

theorem fid_prf_real_experiment (A : FidPrfAdv Ω K Dm Y) (F : K × Dm → Y) :
    fidPr (prfRealExperiment (fidPrfScheme F) (fidPrfHonest A F)) =
      avg fun k : K ↦ avg fun ω : Ω ↦ ind (fidPrfRun F (fun d ↦ F (k, d)) (A ω) = true) := by
  unfold prfRealExperiment
  refine (fidPr_uniform_bind _).trans (avg_congr fun k ↦ ?_)
  unfold fidPrfHonest
  rw [simulateQ_bind, fid_prf_real_lift]
  refine (fidPr_uniform_bind _).trans (avg_congr fun ω ↦ ?_)
  rw [fid_prf_real_run, fidPr_pure]

/-! ### Ideal world: lazy cached oracle vs eager uniform function -/

/-- The distinguisher with its queries to `F` answered: an algorithm over the function oracle
alone. -/
def fidPrfStrip (F : K × Dm → Y) (oa : OracleComp ((K × Dm →ₒ Y) + (Dm →ₒ Y)) Bool) :
    OracleComp (Dm →ₒ Y) Bool :=
  simulateQ (fun t ↦ match t with
    | .inl q => (pure (F q) : OracleComp (Dm →ₒ Y) Y)
    | .inr d => liftM (OracleSpec.query (spec := Dm →ₒ Y) d)) oa

theorem fid_prf_ideal_compose (F : K × Dm → Y)
    (oa : OracleComp ((K × Dm →ₒ Y) + (Dm →ₒ Y)) Bool) :
    simulateQ (prfIdealQueryImpl (D := Dm) (R := Y)) (simulateQ (fidPrfInst F) oa) =
      simulateQ ((Dm →ₒ Y).randomOracle) (fidPrfStrip F oa) := by
  induction oa using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind t k' ih =>
    unfold fidPrfStrip
    rw [simulateQ_bind (fidPrfInst F), simulateQ_spec_query, simulateQ_bind,
      simulateQ_bind, simulateQ_spec_query, simulateQ_bind]
    rcases t with q | d
    · simp only [fidPrfInst]
      rw [simulateQ_pure, pure_bind, simulateQ_pure, pure_bind]
      exact ih (F q)
    · simp only [fidPrfInst]
      refine Eq.trans (congrArg (· >>= _) (simulateQ_spec_query
        (prfIdealQueryImpl (D := Dm) (R := Y)) (.inr d))) ?_
      rw [prfIdealQueryImpl_apply_inr, simulateQ_spec_query]
      exact bind_congr fun u ↦ ih u

theorem fid_prf_strip_eval (F : K × Dm → Y) (R : Dm → Y)
    (oa : OracleComp ((K × Dm →ₒ Y) + (Dm →ₒ Y)) Bool) :
    evalWithAnswerFn (QueryImpl.ofFn R) (fidPrfStrip F oa) = fidPrfRun F R oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind t k' ih =>
    unfold fidPrfStrip
    rw [simulateQ_bind, simulateQ_spec_query, evalWithAnswerFn_bind]
    rcases t with q | d
    · simp only
      rw [evalWithAnswerFn_pure]
      exact ih (F q)
    · simp only
      rw [evalWithAnswerFn_liftM_query]
      exact ih (R d)

/-- **Eager vs lazy ideal oracle.**  VCVio's ideal PRF experiment (lazy cached random oracle),
on the honest adversary, has the probability of the average over the coin and an eagerly
sampled uniform `R : Dm → Y` of the classical run answered by `R`. -/
theorem fid_prf_ideal_eager (A : FidPrfAdv Ω K Dm Y) (F : K × Dm → Y) :
    fidPr (prfIdealExperiment (fidPrfHonest A F)) =
      avg fun ω : Ω ↦ avg fun R : Dm → Y ↦ ind (fidPrfRun F R (A ω) = true) := by
  unfold prfIdealExperiment fidPrfHonest
  rw [simulateQ_bind, StateT.run'_eq, StateT.run_bind,
    show prfIdealQueryImpl (D := Dm) (R := Y) = (Dm →ₒ Y).romImpl from rfl,
    OracleSpec.simulateQ_romImpl_liftM_run]
  simp only [map_bind, bind_map_left]
  refine (fidPr_uniform_bind _).trans (avg_congr fun ω ↦ ?_)
  have h := OracleComp.evalDist_simulateQ_randomOracle_run'_empty_eq_uniformTable
    (fidPrfStrip F (A ω))
  have h' : fidPr (Prod.fst <$> (simulateQ ((Dm →ₒ Y).romImpl)
      (simulateQ (fidPrfInst F) (A ω))).run ∅) =
      fidPr (do let g ← $ᵗ (Dm → Y)
                pure (evalWithAnswerFn (QueryImpl.ofFn g) (fidPrfStrip F (A ω)))) := by
    unfold fidPr
    rw [← h, ← fid_prf_ideal_compose]
    rfl
  rw [h']
  refine (fidPr_uniform_bind _).trans (avg_congr fun R ↦ ?_)
  rw [fidPr_pure, fid_prf_strip_eval]

/-! ### The fidelity equalities -/

theorem fid_prf_qprob (A : FidPrfAdv Ω K Dm Y) (n : ℕ)
    (hb : ∀ ω, IsQueryBoundP (A ω) fidIsReq n) (F : K × Dm → Y) (f : Dm → Y) :
    qprob .instruments F (prfExactProg n (fidSCoinEmb (fidPrfCodec Dm Y) A n) f)
        (SubState.basis ()) fidPrfE =
      avg fun ω : Ω ↦ ind (fidPrfRun F f (A ω) = true) :=
  fidS_qprob (fidPrfCodec Dm Y) F (prfExactCh f) n A () hb fun b _ ↦ b = true

theorem fid_sum2_eq_avg {A' B' : Type} [Fintype A'] [Fintype B'] (g : A' → B' → ℝ≥0∞) :
    ∑ a, ∑ b, ((Fintype.card A' : ℝ≥0∞)⁻¹ * (Fintype.card B' : ℝ≥0∞)⁻¹) * g a b =
      avg fun a ↦ avg fun b ↦ g a b := by
  unfold avg
  simp only [Finset.mul_sum, mul_assoc]

/-- **Fidelity of the real exact PRF experiment.** -/
theorem fid_prf_real_eq (A : FidPrfAdv Ω K Dm Y) (n : ℕ)
    (hb : ∀ ω, IsQueryBoundP (A ω) fidIsReq n) :
    prfExactReal .instruments (A := QReg.of Unit) (SubState.basis ()) n
        (fidSCoinEmb (fidPrfCodec Dm Y) A n) fidPrfE =
      avg fun F : K × Dm → Y ↦
        fidPr (prfRealExperiment (fidPrfScheme F) (fidPrfHonest A F)) := by
  unfold prfExactReal
  rw [fid_sum2_eq_avg, avg_comm]
  exact avg_congr fun F ↦ (avg_congr fun k ↦ fid_prf_qprob A n hb F _).trans
    (fid_prf_real_experiment A F).symm

/-- **Fidelity of the ideal exact PRF experiment.** -/
theorem fid_prf_ideal_eq (A : FidPrfAdv Ω K Dm Y) (n : ℕ)
    (hb : ∀ ω, IsQueryBoundP (A ω) fidIsReq n) :
    prfExactIdeal .instruments (A := QReg.of Unit) (SubState.basis ()) n
        (fidSCoinEmb (fidPrfCodec Dm Y) A n) fidPrfE =
      avg fun F : K × Dm → Y ↦ fidPr (prfIdealExperiment (fidPrfHonest A F)) := by
  unfold prfExactIdeal
  rw [fid_sum2_eq_avg]
  exact avg_congr fun F ↦ ((avg_congr fun R ↦ fid_prf_qprob A n hb F R).trans
    (avg_comm _)).trans (fid_prf_ideal_eager A F).symm

/-- **The exact PRF bound for VCVio's experiments**, averaged over the random function:
for classical distinguishers with a uniform coin, at most `q` classical queries to `F` and at
most `n` function-oracle queries,
`avg_F Pr[real ⇒ true] ≤ avg_F Pr[ideal ⇒ true] + 4 q / √|K|`, and conversely. -/
theorem fid_prf_classical_le [Nonempty K] [Nonempty Dm] (A : FidPrfAdv Ω K Dm Y) (n q : ℕ)
    (hb : ∀ ω, IsQueryBoundP (A ω) fidIsReq n) (hq : ∀ ω, IsQueryBoundP (A ω) fidIsHash q) :
    (avg fun F : K × Dm → Y ↦ fidPr (prfRealExperiment (fidPrfScheme F) (fidPrfHonest A F))) ≤
        (avg fun F : K × Dm → Y ↦ fidPr (prfIdealExperiment (fidPrfHonest A F))) +
          4 * q * ((Fintype.card K : ℝ≥0∞)⁻¹) ^ (2⁻¹ : ℝ) ∧
      (avg fun F : K × Dm → Y ↦ fidPr (prfIdealExperiment (fidPrfHonest A F))) ≤
        (avg fun F : K × Dm → Y ↦ fidPr (prfRealExperiment (fidPrfScheme F) (fidPrfHonest A F))) +
          4 * q * ((Fintype.card K : ℝ≥0∞)⁻¹) ^ (2⁻¹ : ℝ) := by
  rw [← fid_prf_real_eq A n hb, ← fid_prf_ideal_eq A n hb]
  exact ⟨prfExact_real_le_ideal_add _ _ _ (fidSCoin_emb_isQueryBound _ A n q hq) _,
    prfExact_ideal_le_real_add _ _ _ (fidSCoin_emb_isQueryBound _ A n q hq) _⟩

end Prf

end PQ.QROM

#print axioms PQ.QROM.fidS_sim
#print axioms PQ.QROM.fid_prf_ideal_eager
#print axioms PQ.QROM.fid_prf_real_eq
#print axioms PQ.QROM.fid_prf_ideal_eq
#print axioms PQ.QROM.fid_prf_classical_le
