import PQ.QROM.Fidelity

/-!
# Fidelity infrastructure: classical adversaries against any deterministic challenger

Generic form of the embedding of `PQ/QROM/Fidelity.lean`, for any two-port hash domain `X`, any
classical request oracle `rspec` and any deterministic challenger of an exact game.

* `FidCodec rspec Req Resp`: how the queries of the classical oracle `rspec` are read as
  requests of an `IAdv` (`enc`), how responses are read back (`dec`), and a default answer
  (`dflt`, used only beyond the request bound).
* `fidGEmb cd n oa`: the embedding of `oa : OracleComp ((X →ₒ Y) + rspec) State` as an `IAdv`
  with at most `n` requests (hash queries: basis-state quantum queries on port `false`).
* `fidGRun cd Th ch oa s`: the classical run of `oa` with hash queries answered by `Th` and
  requests answered by the challenger `ch` from the state `s`: result and final state.
* `fidG_sim`: the embedded program, run against `ch` from the basis state, has the branches of
  its continuation at `fidGRun`.
* `fidGPh2`, `fidG_leafProb_ph2`: classical second phases.
* `fidG_realProb`: the two-phase game of `PQ/QROM/TwoPhaseGame.lean` on embedded classical
  adversaries is the indicator of the win of the classical run.
* `fidG_emb_isQueryBound`, `fidG_ph2_isQueryBound`: query budgets.
* `fidGCoinEmb`, `fidGCoin_realProb`: a uniform coin drawn at the start.
* `fid_uniform_bind`, `fid_uniform_ind`: VCVio experiments that start by sampling uniformly.
-/

open OracleComp OracleSpec ENNReal Quantum Matrix
open scoped Kronecker ComplexOrder

set_option linter.unusedSectionVars false

namespace PQ.QROM

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
  {ρ : Type} {rspec : OracleSpec.{0, 0} ρ} {Req Resp St State : Type}

/-- Reading the classical oracle `rspec` as requests of an interactive adversary. -/
structure FidCodec (rspec : OracleSpec.{0, 0} ρ) (Req Resp : Type) where
  /-- The request of a query. -/
  enc : ρ → Req
  /-- The answer of a query, from the response. -/
  dec : (r : ρ) → Resp → rspec.Range r
  /-- A default answer (used only beyond the request bound). -/
  dflt : (r : ρ) → rspec.Range r

/-- Interactive adversaries on the trivial register with classical output `State`. -/
abbrev FidGIAdv (X Y : Type) [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (Req Resp State : Type) (n : ℕ) (u : QReg) :=
  IAdv LocalSig.instruments.{0} (qrom2Spec X Y) Req Resp (FidOut State) n u

/-- The leaves of a segment. -/
abbrev FidGLeaf (X Y : Type) [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (Req Resp State : Type) (n : ℕ) (u : QReg) :=
  FidOut State u ⊕ (Req × (Resp → FidGIAdv X Y Req Resp State n u))

/-- **The embedding of a classical first phase**, with at most `n` requests. -/
noncomputable def fidGEmb (cd : FidCodec rspec Req Resp) :
    (n : ℕ) → OracleComp ((X →ₒ Y) + rspec) State → FidGIAdv X Y Req Resp State n (QReg.of Unit)
  | 0 => OracleComp.construct (C := fun _ ↦ FidGIAdv X Y Req Resp State 0 (QReg.of Unit))
      (fun a ↦ QuantumComp.pure ⟨rfl, a⟩)
      (fun t _ ih ↦ match t, ih with
        | .inl q, ih => fidBind (fidQuery false q) ih
        | .inr r, ih => ih (cd.dflt r))
  | n + 1 => OracleComp.construct
      (C := fun _ ↦ QuantumComp LocalSig.instruments.{0} (qrom2Spec X Y)
        (FidGLeaf X Y Req Resp State n) (QReg.of Unit))
      (fun a ↦ QuantumComp.pure (.inl ⟨rfl, a⟩))
      (fun t k ih ↦ match t, k, ih with
        | .inl q, _, ih => fidBind (W := FidGLeaf X Y Req Resp State n) (fidQuery false q) ih
        | .inr r, k, _ =>
          QuantumComp.pure (.inr (cd.enc r, fun resp ↦ fidGEmb cd n (k (cd.dec r resp)))))

/-- **The classical run**: hash queries answered by `Th`, requests by the challenger `ch`. -/
def fidGRun (cd : FidCodec rspec Req Resp) (Th : X → Y) (ch : Req → St → Resp × St) :
    OracleComp ((X →ₒ Y) + rspec) State → St → State × St :=
  OracleComp.construct (C := fun _ ↦ St → State × St) (fun a s ↦ (a, s))
    (fun t _ ih ↦ match t, ih with
      | .inl q, ih => ih (Th q)
      | .inr r, ih => fun s ↦ ih (cd.dec r (ch (cd.enc r) s).1) (ch (cd.enc r) s).2)

/-- **Simulation.** The embedded program run against the challenger `ch` from the basis state
has the branches of its continuation at the classical run. -/
theorem fidG_sim (cd : FidCodec rspec Req Resp) (G : Bool → X → Y) (ch : Req → St → Resp × St)
    (n : ℕ) (oa : OracleComp ((X →ₒ Y) + rspec) State) (s : St)
    (hb : IsQueryBoundP oa fidIsReq n) {W₂ : QReg → Type}
    (K : ∀ u, FidOut State u → St →
      QuantumComp LocalSig.instruments.{0} (qrom2Spec X Y) W₂ u) (c : Σ u, W₂ u) :
    ((twoRuntime G).run .instruments (IAdv.flat ch K n s (fidGEmb cd n oa))).branch c fidσ =
      ((twoRuntime G).run .instruments (K (QReg.of Unit)
        ⟨rfl, (fidGRun cd (G false) ch oa s).1⟩ (fidGRun cd (G false) ch oa s).2)).branch c
        fidσ := by
  induction n generalizing oa s with
  | zero =>
    induction oa using OracleComp.inductionOn with
    | pure a => rfl
    | query_bind t k ih =>
      rw [isQueryBoundP_query_bind_iff] at hb
      rcases t with q | r
      · have e : IAdv.flat ch K 0 s
            (fidGEmb cd 0 (liftM (OracleSpec.query (spec := (X →ₒ Y) + rspec) (.inl q)) >>= k)) =
            fidBind (fidQuery false q) fun y : Y ↦ IAdv.flat ch K 0 s (fidGEmb cd 0 (k y)) :=
          fidBind_bind (fidQuery false q) (fun y : Y ↦ fidGEmb cd 0 (k y)) _
        rw [e]
        exact (fid_run_fidBind_det (twoRuntime G) .instruments _ _ c _ _ (G false q)
          (fid_run_query_self _ _ _) (fun y hy ↦ fid_run_query_ne _ _ _ hy)).trans
            (ih (G false q) (hb.2 (G false q)))
      · exact absurd hb.1 (by simp [fidIsReq])
  | succ n ihn =>
    induction oa using OracleComp.inductionOn generalizing s with
    | pure a => rfl
    | query_bind t k ih =>
      rw [isQueryBoundP_query_bind_iff] at hb
      rcases t with q | r
      · have e : IAdv.flat ch K (n + 1) s
            (fidGEmb cd (n + 1)
              (liftM (OracleSpec.query (spec := (X →ₒ Y) + rspec) (.inl q)) >>= k)) =
            fidBind (fidQuery false q) fun y : Y ↦
              IAdv.flat ch K (n + 1) s (fidGEmb cd (n + 1) (k y)) :=
          fidBind_bind (fidQuery false q) (fun y : Y ↦ fidGEmb cd (n + 1) (k y)) _
        rw [e]
        exact (fid_run_fidBind_det (twoRuntime G) .instruments _ _ c _ _ (G false q)
          (fid_run_query_self _ _ _) (fun y hy ↦ fid_run_query_ne _ _ _ hy)).trans
            (ih (G false q) s (hb.2 (G false q)))
      · exact ihn (k (cd.dec r (ch (cd.enc r) s).1)) (ch (cd.enc r) s).2 (hb.2 _)

/-- The same, for probabilities of events. -/
theorem fidG_leafProb (cd : FidCodec rspec Req Resp) (G : Bool → X → Y)
    (ch : Req → St → Resp × St) (n : ℕ) (oa : OracleComp ((X →ₒ Y) + rspec) State) (s : St)
    (hb : IsQueryBoundP oa fidIsReq n) {W₂ : QReg → Type}
    (K : ∀ u, FidOut State u → St →
      QuantumComp LocalSig.instruments.{0} (qrom2Spec X Y) W₂ u) (E : (Σ u, W₂ u) → Prop) :
    leafProb (twoRuntime G) .instruments (IAdv.flat ch K n s (fidGEmb cd n oa)) fidσ E =
      leafProb (twoRuntime G) .instruments (K (QReg.of Unit)
        ⟨rfl, (fidGRun cd (G false) ch oa s).1⟩ (fidGRun cd (G false) ch oa s).2) fidσ E := by
  unfold leafProb
  simp only [fidG_sim cd G ch n oa s hb K]

/-! ## Second phases -/

/-- A classical hash-only program as a program on any register `u = Unit` (port `true`). -/
noncomputable def fidGProg {β : Type} (prog : OracleComp (X →ₒ Y) β) (u : QReg)
    (h : u = QReg.of Unit) :
    QuantumComp LocalSig.instruments.{0} (qrom2Spec X Y) (fun _ ↦ β) u :=
  h ▸ (prog.toQuantumAt fun q ↦ fidQuery true q).forgetReg

theorem fidG_forgetReg {α : Type}
    (x : QComp (qrom2Spec X Y) (QReg.of Unit) (QReg.of Unit) α) :
    x.forgetReg = fidBind (W := fun _ ↦ α) x fun r ↦ QuantumComp.pure r := by
  unfold QuantumComp₂.forgetReg fidBind
  congr 1
  funext u p
  obtain ⟨rfl, a⟩ := p
  rfl

theorem fidσ_trace : ENNReal.ofReal (fidσ : Matrix (Unit × Unit) (Unit × Unit) ℂ).trace.re = 1 := by
  rw [Matrix.trace_single_eq_same, Complex.one_re, ENNReal.ofReal_one]

theorem fidσ_posSemidef : (fidσ : Matrix (Unit × Unit) (Unit × Unit) ℂ).PosSemidef := by
  rw [← fid_joint_basis]; exact joint_posSemidef _

/-- A classical hash-only program, run from the basis state, ends in the leaf of its value. -/
theorem fidG_leafProb_prog {β : Type} (G : Bool → X → Y) (prog : OracleComp (X →ₒ Y) β)
    (E : (Σ _ : QReg, β) → Prop) :
    leafProb (twoRuntime G) .instruments (fidGProg prog (QReg.of Unit) rfl) fidσ E =
      ind (E ⟨QReg.of Unit, evalWithAnswerFn (QueryImpl.ofFn (G true)) prog⟩) := by
  have e : fidGProg prog (QReg.of Unit) rfl =
      fidBind (W := fun _ ↦ β) (prog.toQuantumAt fun q ↦ fidQuery true q)
        fun r ↦ QuantumComp.pure r := fidG_forgetReg _
  unfold leafProb
  rw [e]
  have hbr : ∀ c, ((twoRuntime G).run .instruments
      (fidBind (W := fun _ ↦ β) (prog.toQuantumAt fun q ↦ fidQuery true q)
        fun r ↦ QuantumComp.pure r)).branch c fidσ =
      ((twoRuntime G).run .instruments (QuantumComp.pure (X := fun _ ↦ β)
        (evalWithAnswerFn (QueryImpl.ofFn (G true)) prog))).branch c fidσ := fun c ↦ by
    refine fid_run_fidBind_det (twoRuntime G) .instruments _ _ c _ _ _ ?_ fun r hr ↦ ?_
    · rcases fid_run_toQuantumAt G true prog
        (evalWithAnswerFn (QueryImpl.ofFn (G true)) prog) with h | h
      · exact h.1
      · exact absurd rfl h.2
    · rcases fid_run_toQuantumAt G true prog r with h | h
      · exact absurd h.2 hr
      · exact h.1
  simp only [hbr]
  have hp := leafProb_pure (R := twoRuntime G) (I := LocalSig.Interp.instruments.{0})
    (W := fun _ ↦ β) (A := QReg.of Unit) (evalWithAnswerFn (QueryImpl.ofFn (G true)) prog) fidσ E
  unfold leafProb at hp
  refine hp.trans ?_
  rw [fidσ_trace, one_mul]

theorem fidG_isQueryBound_query (b : Bool) (t : X) {bd : Bool → ℕ} (h : 0 < bd b) :
    (fidQuery (Y := Y) b t).IsQueryBound bd := by
  rw [fidQuery, QComp.isQueryBound_act_bind_iff]
  intro _
  refine (QuantumComp₂.isQueryBound_bind (b₁ := bd) (b₂ := 0) ?_
    fun _ ↦ QComp.isQueryBound_act _ _).mono (add_zero _).le
  exact (QuantumComp₂.isQueryBound_query_iff _ _ _ _).mpr h

theorem fidG_prog_isQueryBound {β : Type} (prog : OracleComp (X →ₒ Y) β) (q : ℕ)
    (hq : IsTotalQueryBound prog q) (u : QReg) (h : u = QReg.of Unit) :
    (fidGProg prog u h).IsQueryBound (secondBudget q) := by
  subst h
  refine (QuantumComp₂.isQueryBound_forgetReg (OracleComp.isQueryBound_toQuantumAt
    (b := secondBudget 1) (fun t ↦ fidG_isQueryBound_query true t (by simp [secondBudget]))
    hq)).mono fun i ↦ ?_
  cases i <;> simp [secondBudget]

theorem fidG_emb_isQueryBound (cd : FidCodec rspec Req Resp) (n : ℕ)
    (oa : OracleComp ((X →ₒ Y) + rspec) State) (q : ℕ) (hq : IsQueryBoundP oa fidIsHash q) :
    IAdv.IsQueryBound n (fidGEmb cd n oa) (firstBudget q) := by
  intro St ch s
  induction n generalizing oa s q with
  | zero =>
    induction oa using OracleComp.inductionOn generalizing q with
    | pure a => exact QuantumComp.isQueryBound_pure _ _
    | query_bind t k ih =>
      rw [isQueryBoundP_query_bind_iff] at hq
      rcases t with t | r
      · have e : IAdv.flat ch (IAdv.stop (L := LocalSig.instruments.{0})
            (spec := qrom2Spec X Y)) 0 s
            (fidGEmb cd 0 (liftM (OracleSpec.query (spec := (X →ₒ Y) + rspec) (.inl t)) >>= k)) =
            fidBind (fidQuery false t) fun y : Y ↦ IAdv.flat ch (IAdv.stop
              (L := LocalSig.instruments.{0}) (spec := qrom2Spec X Y)) 0 s
                (fidGEmb cd 0 (k y)) :=
          fidBind_bind (fidQuery false t) (fun y : Y ↦ fidGEmb cd 0 (k y)) _
        rw [e]
        have hq0 : 0 < q := by simpa [fidIsHash] using hq.1
        refine (fidBind_isQueryBound (b₁ := firstBudget 1) (b₂ := firstBudget (q - 1))
          (fidG_isQueryBound_query false t (by simp [firstBudget])) fun y : Y ↦ ih y (q := q - 1)
            (by simpa [fidIsHash] using hq.2 y)).mono fun i ↦ ?_
        cases i
        · simp [firstBudget]; omega
        · simp [firstBudget]
      · exact ih (cd.dflt r) (q := q) (by simpa [fidIsHash] using hq.2 (cd.dflt r))
  | succ n ihn =>
    induction oa using OracleComp.inductionOn generalizing q s with
    | pure a => exact QuantumComp.isQueryBound_pure _ _
    | query_bind t k ih =>
      rw [isQueryBoundP_query_bind_iff] at hq
      rcases t with t | r
      · have e : IAdv.flat ch (IAdv.stop (L := LocalSig.instruments.{0})
            (spec := qrom2Spec X Y)) (n + 1) s
            (fidGEmb cd (n + 1)
              (liftM (OracleSpec.query (spec := (X →ₒ Y) + rspec) (.inl t)) >>= k)) =
            fidBind (fidQuery false t) fun y : Y ↦ IAdv.flat ch (IAdv.stop
              (L := LocalSig.instruments.{0}) (spec := qrom2Spec X Y)) (n + 1) s
                (fidGEmb cd (n + 1) (k y)) :=
          fidBind_bind (fidQuery false t) (fun y : Y ↦ fidGEmb cd (n + 1) (k y)) _
        rw [e]
        have hq0 : 0 < q := by simpa [fidIsHash] using hq.1
        refine (fidBind_isQueryBound (b₁ := firstBudget 1) (b₂ := firstBudget (q - 1))
          (fidG_isQueryBound_query false t (by simp [firstBudget])) fun y : Y ↦
            ih y (s := s) (q := q - 1) (by simpa [fidIsHash] using hq.2 y)).mono fun i ↦ ?_
        cases i
        · simp [firstBudget]; omega
        · simp [firstBudget]
      · exact ihn (oa := k (cd.dec r (ch (cd.enc r) s).1)) (s := (ch (cd.enc r) s).2) (q := q)
          (by simpa [fidIsHash] using hq.2 _)

/-! ## A uniform coin at the start -/

section Coin

variable {Ω : Type} [Fintype Ω] [Nonempty Ω]

/-- The embedding with a uniform coin: flip `ω`, then run the embedding of `choose ω`. -/
noncomputable def fidGCoinEmb (cd : FidCodec rspec Req Resp)
    (choose : Ω → OracleComp ((X →ₒ Y) + rspec) State) :
    (n : ℕ) → FidGIAdv X Y Req Resp State n (QReg.of Unit)
  | 0 => fidBind (W := FidOut State) (QComp.act (SubInstrument.uniform Ω (QReg.of Unit)))
      fun ω ↦ fidGEmb cd 0 (choose ω)
  | n + 1 => fidBind (W := FidGLeaf X Y Req Resp State n)
      (QComp.act (SubInstrument.uniform Ω (QReg.of Unit))) fun ω ↦ fidGEmb cd (n + 1) (choose ω)

theorem fidGCoin_flat {W₂ : QReg → Type} (cd : FidCodec rspec Req Resp)
    (choose : Ω → OracleComp ((X →ₒ Y) + rspec) State) (ch : Req → St → Resp × St)
    (K : ∀ u, FidOut State u → St →
      QuantumComp LocalSig.instruments.{0} (qrom2Spec X Y) W₂ u) (n : ℕ) (s : St) :
    IAdv.flat ch K n s (fidGCoinEmb cd choose n) =
      fidBind (QComp.act (SubInstrument.uniform Ω (QReg.of Unit))) fun ω ↦
        IAdv.flat ch K n s (fidGEmb cd n (choose ω)) := by
  cases n with
  | zero => exact fidBind_bind _ (fun ω ↦ fidGEmb cd 0 (choose ω)) _
  | succ n => exact fidBind_bind _ (fun ω ↦ fidGEmb cd (n + 1) (choose ω)) _

theorem fidGCoin_branch {qs : QuantumOracleSpec.{0, 0}} (R : QuantumRuntime qs) (ω : Ω) :
    (R.run₂ .instruments (QComp.act (spec := qs)
      (SubInstrument.uniform Ω (QReg.of Unit)))).branch ω =
      ((Fintype.card Ω : ℂ)⁻¹) • LinearMap.id := by
  rw [QuantumRuntime.run₂_act, SubInstrument.bind_pure, DSubInstrument.branch_frame_apply]
  refine LinearMap.ext fun ρ ↦ ?_
  ext x x'
  simp [SubInstrument.branch_uniform_apply]

/-- **The coin averages.** -/
theorem fidGCoin_leafProb {W : QReg → Type} {qs : QuantumOracleSpec.{0, 0}} (R : QuantumRuntime qs)
    (k : Ω → QuantumComp LocalSig.instruments.{0} qs W (QReg.of Unit))
    {σ : Matrix (QReg.of Unit × R.D) (QReg.of Unit × R.D) ℂ} (hσ : σ.PosSemidef)
    (E : (Σ u, W u) → Prop) :
    leafProb R .instruments
        (fidBind (QComp.act (SubInstrument.uniform Ω (QReg.of Unit))) k) σ E =
      avg fun ω ↦ leafProb R .instruments (k ω) σ E := by
  unfold leafProb avg
  have hb : ∀ c, ENNReal.ofReal ((R.run .instruments
      (fidBind (QComp.act (SubInstrument.uniform Ω (QReg.of Unit))) k)).branch c σ).trace.re =
      ∑ ω, (Fintype.card Ω : ℝ≥0∞)⁻¹ *
        ENNReal.ofReal ((R.run .instruments (k ω)).branch c σ).trace.re := fun c ↦ by
    have h := fid_run_fidBind R LocalSig.Interp.instruments.{0}
      (QComp.act (spec := qs) (SubInstrument.uniform Ω (QReg.of Unit))) k c σ
    have hω : ∀ ω : Ω, (R.run .instruments (k ω)).branch c
        ((R.run₂ .instruments (QComp.act (spec := qs)
          (SubInstrument.uniform Ω (QReg.of Unit)))).branch ω σ) =
        ((Fintype.card Ω : ℂ)⁻¹) • (R.run .instruments (k ω)).branch c σ := fun ω ↦
      (congrArg ((R.run .instruments (k ω)).branch c)
        (LinearMap.congr_fun (fidGCoin_branch R ω) σ)).trans (by
          rw [LinearMap.smul_apply, LinearMap.id_apply, map_smul])
    refine (congrArg (fun M ↦ ENNReal.ofReal (Matrix.trace M).re)
      (h.trans ((tsum_fintype _).trans (Finset.sum_congr rfl fun ω _ ↦ hω ω)))).trans ?_
    rw [Matrix.trace_sum, Complex.re_sum, ENNReal.ofReal_sum_of_nonneg]
    · refine Finset.sum_congr rfl fun ω _ ↦ ?_
      rw [Matrix.trace_smul, smul_eq_mul, ← Complex.ofReal_natCast, ← Complex.ofReal_inv,
        Complex.re_ofReal_mul, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_inv_of_pos
          (by exact_mod_cast Fintype.card_pos), ENNReal.ofReal_natCast]
    · intro ω _
      rw [Matrix.trace_smul, smul_eq_mul, ← Complex.ofReal_natCast, ← Complex.ofReal_inv,
        Complex.re_ofReal_mul]
      exact mul_nonneg (by positivity)
        (Complex.nonneg_iff.1
          ((R.run .instruments (k ω)).posSemidef_branch_apply c hσ).trace_nonneg).1
  simp only [hb, Finset.sum_mul]
  rw [Summable.tsum_finsetSum fun _ _ ↦ CompleteLattice.summable]
  refine Finset.sum_congr rfl fun ω _ ↦ ?_
  rw [← ENNReal.tsum_mul_left]
  exact tsum_congr fun c ↦ mul_assoc _ _ _

theorem fidGCoin_emb_isQueryBound (cd : FidCodec rspec Req Resp)
    (choose : Ω → OracleComp ((X →ₒ Y) + rspec) State) (n q : ℕ)
    (hq : ∀ ω, IsQueryBoundP (choose ω) fidIsHash q) :
    IAdv.IsQueryBound n (fidGCoinEmb cd choose n) (firstBudget q) := by
  intro St ch s
  rw [fidGCoin_flat]
  exact (fidBind_isQueryBound (b₁ := 0) (QComp.isQueryBound_act _ _)
    fun ω ↦ fidG_emb_isQueryBound cd n (choose ω) q (hq ω) St ch s).mono (zero_add _).le

end Coin

/-! ## Two-phase games -/

section TwoPhase

variable {Sd Tw Msg Res : Type} [Fintype Sd] [DecidableEq Sd] [Fintype Tw] [DecidableEq Tw]
  [Fintype Msg] [DecidableEq Msg]

/-- **The embedding of a classical second phase.** -/
noncomputable def fidGPh2 (forge : State → Sd → OracleComp (Dom Sd Tw Msg →ₒ Y) Res) (P : Sd)
    (u : QReg) (o : FidOut State u) :
    QuantumComp LocalSig.instruments.{0} (qrom2Spec (Dom Sd Tw Msg) Y) (fun _ ↦ Res) u :=
  o.casesOn fun h st ↦ fidGProg (forge st P) u h

theorem fidG_ph2_isQueryBound (forge : State → Sd → OracleComp (Dom Sd Tw Msg →ₒ Y) Res) (q : ℕ)
    (hq : ∀ st P, IsTotalQueryBound (forge st P) q) (P : Sd) (u : QReg) (o : FidOut State u) :
    (fidGPh2 forge P u o).IsQueryBound (secondBudget q) := by
  obtain ⟨h, st⟩ := o
  exact fidG_prog_isQueryBound _ q (hq st P) u h

/-- **The two-phase game on embedded classical adversaries** is the indicator of the win of the
classical run, for every seed and hash. -/
theorem fidG_realProb (cd : FidCodec rspec Req Resp)
    (ch : (Tw × Msg → Y) → Req → St → Resp × St) (s₀ : St)
    (win : (Tw × Msg → Y) → Res → St → Prop) (n : ℕ)
    (choose : OracleComp ((Dom Sd Tw Msg →ₒ Y) + rspec) State)
    (forge : State → Sd → OracleComp (Dom Sd Tw Msg →ₒ Y) Res)
    (hb : IsQueryBoundP choose fidIsReq n) (P : Sd) (Th : Dom Sd Tw Msg → Y) :
    realProb .instruments (A := QReg.of Unit) (SubState.basis ()) ch s₀ n (fidGEmb cd n choose)
        (fidGPh2 forge) win P Th =
      ind (win (rowOf Th P)
        (evalWithAnswerFn (QueryImpl.ofFn Th)
          (forge (fidGRun cd Th (ch (rowOf Th P)) choose s₀).1 P))
        (fidGRun cd Th (ch (rowOf Th P)) choose s₀).2) := by
  unfold realProb composite
  rw [fid_joint_basis, fidG_leafProb cd (fun _ ↦ Th) (ch (rowOf Th P)) n choose s₀ hb]
  exact (leafProb_phase2K (twoRuntime fun _ ↦ Th) .instruments (fidGPh2 forge) P (QReg.of Unit)
    ⟨rfl, _⟩ _ fidσ_posSemidef (win (rowOf Th P))).trans
      (fidG_leafProb_prog (fun _ ↦ Th) _ _)

variable {Ω : Type} [Fintype Ω] [Nonempty Ω]

/-- With a uniform coin, the two-phase game is the average over the coin. -/
theorem fidGCoin_realProb (cd : FidCodec rspec Req Resp)
    (ch : (Tw × Msg → Y) → Req → St → Resp × St) (s₀ : St)
    (win : (Tw × Msg → Y) → Res → St → Prop) (n : ℕ)
    (choose : Ω → OracleComp ((Dom Sd Tw Msg →ₒ Y) + rspec) State)
    (ph2 : Sd → ∀ u, FidOut State u →
      QuantumComp LocalSig.instruments.{0} (qrom2Spec (Dom Sd Tw Msg) Y) (fun _ ↦ Res) u)
    (P : Sd) (Th : Dom Sd Tw Msg → Y) :
    realProb .instruments (A := QReg.of Unit) (SubState.basis ()) ch s₀ n
        (fidGCoinEmb cd choose n) ph2 win P Th =
      avg fun ω ↦ realProb .instruments (A := QReg.of Unit) (SubState.basis ()) ch s₀ n
        (fidGEmb cd n (choose ω)) ph2 win P Th := by
  unfold realProb composite
  rw [fidGCoin_flat]
  exact fidGCoin_leafProb _ _ (joint_posSemidef _) _

theorem fidGCoin_twoPhaseExp (cd : FidCodec rspec Req Resp)
    (ch : (Tw × Msg → Y) → Req → St → Resp × St) (s₀ : St)
    (win : (Tw × Msg → Y) → Res → St → Prop) (n : ℕ)
    (choose : Ω → OracleComp ((Dom Sd Tw Msg →ₒ Y) + rspec) State)
    (ph2 : Sd → ∀ u, FidOut State u →
      QuantumComp LocalSig.instruments.{0} (qrom2Spec (Dom Sd Tw Msg) Y) (fun _ ↦ Res) u) :
    twoPhaseExp .instruments (A := QReg.of Unit) (SubState.basis ()) ch s₀ n
        (fidGCoinEmb cd choose n) ph2 win =
      avg fun ω ↦ twoPhaseExp .instruments (A := QReg.of Unit) (SubState.basis ()) ch s₀ n
        (fidGEmb cd n (choose ω)) ph2 win := by
  unfold twoPhaseExp
  rw [avg_congr fun P ↦ avg_congr fun Th ↦ fidGCoin_realProb cd ch s₀ win n choose ph2 P Th,
    avg_congr fun P ↦ avg_comm _, avg_comm]

end TwoPhase

/-! ## VCVio experiments that start with a uniform sample -/

section Prob

variable {T : Type} [Fintype T] [SampleableType T]

/-- The probability of `true` of a boolean experiment, as in VCVio's advantages. -/
noncomputable abbrev fidPr (mx : ProbComp Bool) : ℝ≥0∞ := 𝒟[mx] {true}

theorem fidPr_pure (b : Bool) : fidPr (pure b) = ind (b = true) := by
  unfold fidPr
  rw [← prEvent_eq_evalDist_singleton, prEvent_pure]
  by_cases h : b = true
  · rw [ind_of_true h]; simp [h]
  · rw [ind_of_false h]; simp [h]

theorem fidPr_uniform_bind (f : T → ProbComp Bool) :
    fidPr (($ᵗ T) >>= f) = avg fun t ↦ fidPr (f t) := by
  unfold fidPr avg
  simp only [← prEvent_eq_evalDist_singleton, prEvent_bind_eq_sum_fintype,
    SampleableType.prEvent_uniformSample_eq_singleton]

end Prob

end PQ.QROM

#print axioms PQ.QROM.fidG_sim
#print axioms PQ.QROM.fidG_realProb
#print axioms PQ.QROM.fidG_emb_isQueryBound
#print axioms PQ.QROM.fidGCoin_twoPhaseExp
#print axioms PQ.QROM.fidPr_uniform_bind
