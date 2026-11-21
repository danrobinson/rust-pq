import PQ.Interactive.EUFCMA

/-!
# Collapse of an arbitrary quantum adversary into a classical strategy with real probabilities

Without any rationality assumption, the classical-interface behaviour of a quantum machine is
that of a classical strategy that samples each measurement outcome from the Born distribution.
The Born probabilities are arbitrary reals, so the strategy lives over the sampling spec
`distSpec` ("sample from a given finite distribution"), which carries an `AnswerMeasure` and hence
VCVio's `𝒟[·]` / `Pr{…}[…]` semantics.

`qWeight_close_eq_strategy`: for every quantum machine, every classical stateful probabilistic
implementation of its oracles and every event, the Born weight equals the probability of the event
when the implementation is run on `Q.toStrategy ρ`.
-/

open OracleComp OracleSpec ENNReal Quantum MeasureTheory
open scoped ComplexOrder

namespace PQ.Interactive

variable {W : Type} [Fintype W] {α β γ : Type}

/-! ## The sampling spec -/

/-- Index of a sampling query: a probability vector on `Fin (n+1)`. -/
abbrev DistIdx : Type := Σ n : ℕ, {p : Fin (n + 1) → ℝ≥0∞ // ∑ i, p i = 1}

/-- The oracle family "sample from the given finite distribution". -/
@[reducible] def distSpec : OracleSpec DistIdx := fun d ↦ Fin (d.1 + 1)

instance (d : DistIdx) : Fintype (distSpec.Range d) := inferInstanceAs (Fintype (Fin (d.1 + 1)))

/-- The measure of a probability vector (on the discrete σ-algebra). -/
noncomputable def distMeasure (d : DistIdx) : @Measure (Fin (d.1 + 1)) ⊤ :=
  @Finset.sum _ _ _ Finset.univ fun i ↦ d.2.1 i • @Measure.dirac _ ⊤ i

lemma distMeasure_singleton (d : DistIdx) (i : Fin (d.1 + 1)) :
    distMeasure d {i} = d.2.1 i := by
  let _ : MeasurableSpace (Fin (d.1 + 1)) := ⊤
  classical
  simp [distMeasure, Set.indicator_apply, eq_comm]

noncomputable instance : OracleSpec.AnswerMeasure distSpec :=
  @PFunctor.AnswerMeasure.mk distSpec.toPFunctor (fun _ ↦ ⊤) distMeasure fun d ↦ by
    let _ : MeasurableSpace (Fin (d.1 + 1)) := ⊤
    refine ⟨?_⟩
    simp [distMeasure, d.2.2]

/-- The private sampling interface of a strategy: real-probability and uniform sampling. -/
abbrev privSpec : OracleSpec (DistIdx ⊕ ℕ) := distSpec + unifSpec

/-! ## Probability rules over the sampling interface -/

/-- Probability of an event after one query with finitely many answers. -/
lemma prob_query_bind {κ : Type} {cs : OracleSpec κ} [OracleSpec.AnswerMeasure cs]
    (t : cs.Domain) [Fintype (cs.Range t)] (k : cs.Range t → OracleComp cs β) (q : β → Prop) :
    prob (liftM (cs.query t) >>= k) q =
      ∑ u, OracleSpec.AnswerMeasure.toMeasure t {u} * prob (k u) q := by
  unfold prob
  let _ : MeasurableSpace (cs.Range t) := ⊤
  rw [prEvent_bind_eq_lintegral_of_discrete, lintegral_fintype]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [mul_comm, evalDist_liftM_query_apply (spec := cs) t (MeasurableSet.of_discrete)]

lemma prob_dist_query_bind (d : DistIdx) (k : Fin (d.1 + 1) → OracleComp privSpec β)
    (q : β → Prop) :
    prob (liftM (privSpec.query (Sum.inl d)) >>= k) q = ∑ i, d.2.1 i * prob (k i) q := by
  rw [prob_query_bind (cs := privSpec) (Sum.inl d)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  congr 1
  exact distMeasure_singleton d i

lemma prob_priv_unif_query_bind (n : ℕ) (k : Fin (n + 1) → OracleComp privSpec β)
    (q : β → Prop) :
    prob (liftM (privSpec.query (Sum.inr n)) >>= k) q =
      ((n : ℝ≥0∞) + 1)⁻¹ * ∑ i, prob (k i) q := by
  rw [prob_query_bind (cs := privSpec) (Sum.inr n), Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  congr 1
  change (OracleSpec.AnswerMeasure.toMeasure (spec := unifSpec) n) {i} = _
  simp

/-- Embed classical probabilistic code into the sampling interface. -/
def liftR (oa : ProbComp α) : OracleComp privSpec α :=
  simulateQ (fun n ↦ liftM (privSpec.query (Sum.inr n))) oa

lemma liftR_query_bind (n : ℕ) (k : Fin (n + 1) → ProbComp α) :
    liftR (liftM (unifSpec.query n) >>= k) =
      liftM (privSpec.query (Sum.inr n)) >>= fun i ↦ liftR (k i) := by
  simp [liftR]

/-- Classical probabilistic pre-processing, strategy version of `qWeight_liftU_bind`. -/
lemma qWeight_liftU_bind_liftR (p : β → Prop) [DecidablePred p] (oa : ProbComp γ)
    (f : γ → Closed W β) (g : γ → OracleComp privSpec β) (c : ℝ≥0∞) (ρ : Matrix W W ℂ)
    (h : ∀ x, qWeight p (f x) ρ = c * prob (g x) p) :
    qWeight p (liftU oa >>= f) ρ = c * prob (liftR oa >>= g) p := by
  induction oa using OracleComp.inductionOn with
  | pure a => simpa [liftR] using h a
  | query_bind n k ih =>
    rw [liftU_query_bind, liftR_query_bind, bind_assoc, bind_assoc, qWeight_unif_bind,
      prob_priv_unif_query_bind]
    simp only [ih, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [mul_left_comm]

/-! ## The classical strategy -/

variable {ι' : Type} {spec' : OracleSpec ι'} {σ : Type}

open Classical in
/-- A probability vector from weights: the weights themselves if they sum to one, otherwise the
point mass at `0`. -/
noncomputable def normW {n : ℕ} (w : Fin (n + 1) → ℝ≥0∞) :
    {p : Fin (n + 1) → ℝ≥0∞ // ∑ i, p i = 1} :=
  if h : ∑ i, w i = 1 then ⟨w, h⟩ else ⟨Pi.single 0 1, by simp⟩

lemma normW_of_sum {n : ℕ} {w : Fin (n + 1) → ℝ≥0∞} (h : ∑ i, w i = 1) : (normW w).1 = w := by
  simp [normW, h]

/-- The sampling query for the Born distribution of the instrument `j` on the state `ρ`. -/
noncomputable def bornIdx (j : InstrIdx W) (ρ : Matrix W W ℂ) : DistIdx :=
  ⟨j.1, normW (bornW j.2.1 ρ)⟩

/-- The classical strategy of an arbitrary quantum machine `Q` started in the state `ρ`: each
instrument node is replaced by one sampling query for its Born distribution; the uniform queries
of `Q` and its oracle queries are kept. -/
noncomputable def toStrategy (Q : QOC W (unifSpec + spec') α) :
    Matrix W W ℂ → OracleComp (privSpec + spec') α :=
  OracleComp.construct (C := fun _ ↦ Matrix W W ℂ → OracleComp (privSpec + spec') α)
    (fun a _ ↦ pure a)
    (fun t _ ih ρ ↦
      match t, ih with
      | .inl j, ih =>
          liftM ((privSpec + spec').query (Sum.inl (Sum.inl (bornIdx j ρ)))) >>=
            fun i ↦ ih i (j.2.1.branch i ρ)
      | .inr (.inl n), ih =>
          liftM ((privSpec + spec').query (Sum.inl (Sum.inr n))) >>= fun u ↦ ih u ρ
      | .inr (.inr t), ih =>
          liftM ((privSpec + spec').query (Sum.inr t)) >>= fun u ↦ ih u ρ) Q

@[simp] lemma toStrategy_pure (a : α) (ρ : Matrix W W ℂ) :
    toStrategy (pure a : QOC W (unifSpec + spec') α) ρ = pure a := rfl

lemma toStrategy_instr_bind (j : InstrIdx W) (k : Fin (j.1 + 1) → QOC W (unifSpec + spec') α)
    (ρ : Matrix W W ℂ) :
    toStrategy (liftM ((instrSpec W + (unifSpec + spec')).query (Sum.inl j)) >>= k) ρ =
      liftM ((privSpec + spec').query (Sum.inl (Sum.inl (bornIdx j ρ)))) >>=
        fun i ↦ toStrategy (k i) (j.2.1.branch i ρ) := rfl

lemma toStrategy_unif_bind (n : ℕ) (k : Fin (n + 1) → QOC W (unifSpec + spec') α)
    (ρ : Matrix W W ℂ) :
    toStrategy (liftM ((instrSpec W + (unifSpec + spec')).query (Sum.inr (Sum.inl n))) >>= k) ρ =
      liftM ((privSpec + spec').query (Sum.inl (Sum.inr n))) >>=
        fun u ↦ toStrategy (k u) ρ := rfl

lemma toStrategy_query_bind (t : spec'.Domain) (k : spec'.Range t → QOC W (unifSpec + spec') α)
    (ρ : Matrix W W ℂ) :
    toStrategy (liftM ((instrSpec W + (unifSpec + spec')).query (Sum.inr (Sum.inr t))) >>= k) ρ =
      liftM ((privSpec + spec').query (Sum.inr t)) >>= fun u ↦ toStrategy (k u) ρ := rfl

/-- Run a classical implementation against a strategy: the private sampling queries are passed
through, the oracle queries are answered by `impl`. -/
def strategyImpl (impl : QueryImpl (unifSpec + spec') (StateT σ ProbComp)) :
    QueryImpl (privSpec + spec') (StateT σ (OracleComp privSpec))
  | .inl c => fun s ↦ (fun u ↦ (u, s)) <$> (liftM (privSpec.query c) : OracleComp privSpec _)
  | .inr t => fun s ↦ liftR ((impl (Sum.inr t)).run s)

/-- **Collapse of an arbitrary quantum machine, continuation form (T5).** -/
theorem qWeight_close_bind_strategy (impl : QueryImpl (unifSpec + spec') (StateT σ ProbComp))
    (himpl : ForwardsUnif impl) (p : β → Prop) [DecidablePred p]
    (f : α × σ → Closed W β) (g : α × σ → OracleComp privSpec β)
    (hfg : ∀ x (ρ' : Matrix W W ℂ), ρ'.PosSemidef →
      qWeight p (f x) ρ' = ENNReal.ofReal ρ'.trace.re * prob (g x) p)
    (Q : QOC W (unifSpec + spec') α) (s : σ) (ρ : Matrix W W ℂ) (hρ : ρ.PosSemidef) :
    qWeight p (close impl Q s >>= f) ρ =
      ENNReal.ofReal ρ.trace.re *
        prob ((simulateQ (strategyImpl impl) (toStrategy Q ρ)).run s >>= g) p := by
  induction Q using OracleComp.inductionOn generalizing s ρ with
  | pure a => simpa using hfg (a, s) ρ hρ
  | query_bind t k ih =>
    rcases t with j | n | t
    · -- instrument node
      have hrun : (simulateQ (strategyImpl impl)
            (liftM ((privSpec + spec').query (Sum.inl (Sum.inl (bornIdx j ρ)))) >>=
              fun i ↦ toStrategy (k i) (j.2.1.branch i ρ))).run s =
          liftM (privSpec.query (Sum.inl (bornIdx j ρ))) >>= fun i ↦
            (simulateQ (strategyImpl impl) (toStrategy (k i) (j.2.1.branch i ρ))).run s := by
        rw [simulateQ_bind, StateT.run_bind, simulateQ_spec_query]
        change ((fun u ↦ (u, s)) <$> _) >>= _ = _
        simp
      rw [close_instr_bind, bind_assoc, qWeight_instr_bind, toStrategy_instr_bind, hrun,
        bind_assoc, prob_dist_query_bind]
      simp only [ih _ _ _ (posSemidef_branch j _ hρ)]
      have hnn : ∀ i, 0 ≤ (j.2.1.branch i ρ).trace.re := fun i ↦
        (posSemidef_branch j i hρ).trace_re_nonneg
      have hsum : ∑ i, (j.2.1.branch i ρ).trace.re = ρ.trace.re := by
        rw [← Complex.re_sum]
        exact congrArg Complex.re (j.2.2.sum_trace_eq (s := Finset.univ) (by simp) ρ)
      by_cases hc : ρ.trace.re = 0
      · have h0 : ∀ i, (j.2.1.branch i ρ).trace.re = 0 := fun i ↦
          (Finset.sum_eq_zero_iff_of_nonneg fun i _ ↦ hnn i).mp (hsum.trans hc) i
            (Finset.mem_univ i)
        simp [h0, hc]
      · have hcpos : 0 < ρ.trace.re := lt_of_le_of_ne hρ.trace_re_nonneg (Ne.symm hc)
        have hw : ∑ i, bornW j.2.1 ρ i = 1 := by
          unfold bornW
          rw [← ENNReal.ofReal_sum_of_nonneg fun i _ ↦ div_nonneg (hnn i) hcpos.le,
            ← Finset.sum_div, hsum, div_self hc, ENNReal.ofReal_one]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        change _ = _ * ((normW (bornW j.2.1 ρ)).1 i * _)
        rw [normW_of_sum hw, ← mul_assoc, bornW, ← ENNReal.ofReal_mul hcpos.le,
          mul_div_cancel₀ _ hc]
    · -- uniform sampling of the machine
      have hrun : (simulateQ (strategyImpl impl)
            (liftM ((privSpec + spec').query (Sum.inl (Sum.inr n))) >>=
              fun u ↦ toStrategy (k u) ρ)).run s =
          liftM (privSpec.query (Sum.inr n)) >>= fun u ↦
            (simulateQ (strategyImpl impl) (toStrategy (k u) ρ)).run s := by
        rw [simulateQ_bind, StateT.run_bind, simulateQ_spec_query]
        change ((fun u ↦ (u, s)) <$> _) >>= _ = _
        simp
      rw [close_query_bind, himpl n s, liftU_map, liftU_query, bind_map_left, bind_assoc,
        qWeight_unif_bind, toStrategy_unif_bind, hrun, bind_assoc, prob_priv_unif_query_bind,
        Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [ih _ _ _ hρ, mul_left_comm]
    · -- oracle query
      have hrun : (simulateQ (strategyImpl impl)
            (liftM ((privSpec + spec').query (Sum.inr t)) >>=
              fun u ↦ toStrategy (k u) ρ)).run s =
          liftR ((impl (Sum.inr t)).run s) >>= fun x ↦
            (simulateQ (strategyImpl impl) (toStrategy (k x.1) ρ)).run x.2 := by
        rw [simulateQ_bind, StateT.run_bind, simulateQ_spec_query]
        rfl
      rw [close_query_bind, bind_assoc, toStrategy_query_bind, hrun, bind_assoc]
      exact qWeight_liftU_bind_liftR p _ _ _ _ ρ fun x ↦ ih _ _ _ hρ

/-- **Collapse of an arbitrary quantum machine (T5).**  No rationality assumption: for every
quantum machine `Q`, every classical stateful probabilistic implementation `impl` of its oracles
and every event, the Born weight of the closed machine from a density matrix `ρ` equals the
probability of the event when `impl` is run on the classical strategy `Q.toStrategy ρ`. -/
theorem qWeight_close_eq_strategy (impl : QueryImpl (unifSpec + spec') (StateT σ ProbComp))
    (himpl : ForwardsUnif impl) (p : α × σ → Prop) [DecidablePred p]
    (Q : QOC W (unifSpec + spec') α) (s : σ) (ρ : Matrix W W ℂ) (hρ : ρ.PosSemidef)
    (h1 : ρ.trace = 1) :
    qWeight p (close impl Q s) ρ =
      Pr{let y ← (simulateQ (strategyImpl impl) (toStrategy Q ρ)).run s}[p y] := by
  have := qWeight_close_bind_strategy impl himpl p pure pure
    (fun x ρ' _ ↦ by simp) Q s ρ hρ
  simpa [h1, prob_def] using this

/-! ## EUF-CMA for arbitrary quantum forgers -/

section eufcma

variable {M PK SK S : Type}

@[simp] lemma liftR_pure (a : α) : liftR (pure a) = pure a := by simp [liftR]

@[simp] lemma liftR_map (oa : ProbComp α) (f : α → β) : liftR (f <$> oa) = f <$> liftR oa := by
  simp [liftR]

/-- The scheme `sigAlg` with its algorithms run over the strategy's sampling interface
`distSpec + unifSpec` (they only use uniform sampling). -/
def liftSig (sigAlg : SignatureAlg ProbComp M PK SK S) :
    SignatureAlg (OracleComp privSpec) M PK SK S where
  keygen := liftR sigAlg.keygen
  sign pk sk m := liftR (sigAlg.sign pk sk m)
  verify pk m s := liftR (sigAlg.verify pk m s)

/-- The strategy implementation of the stateful signing oracle is VCVio's
`runWithSigningOracle` for the lifted scheme. -/
lemma run_simulateQ_strategyImpl_signImpl (sigAlg : SignatureAlg ProbComp M PK SK S) (pk : PK)
    (sk : SK) (oa : OracleComp (privSpec + (M →ₒ S)) α) (l₀ : QueryLog (M →ₒ S)) :
    (simulateQ (strategyImpl (signImpl sigAlg pk sk)) oa).run l₀ =
      (fun x ↦ (x.1, l₀ ++ x.2)) <$> (liftSig sigAlg).runWithSigningOracle pk sk oa := by
  unfold SignatureAlg.runWithSigningOracle
  induction oa using OracleComp.inductionOn generalizing l₀ with
  | pure a => simp
  | query_bind t k ih =>
    rw [simulateQ_bind, simulateQ_bind, StateT.run_bind, WriterT.run_bind',
      simulateQ_spec_query, simulateQ_spec_query]
    rcases t with c | m
    · have h1 : (strategyImpl (signImpl sigAlg pk sk) (Sum.inl c)).run l₀ =
          (fun u ↦ (u, l₀)) <$> (liftM (privSpec.query c) : OracleComp privSpec _) := rfl
      have h2 : ((privSpec.passthrough + (liftSig sigAlg).signingOracle pk sk) (Sum.inl c)).run =
          (fun u ↦ (u, ([] : QueryLog (M →ₒ S)))) <$>
            (liftM (privSpec.query c) : OracleComp privSpec _) := by
        simp only [QueryImpl.passthrough_add, QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply,
          QueryImpl.id'_apply]
        rfl
      rw [h1, h2]
      simp [ih]
    · have h1 : (strategyImpl (signImpl sigAlg pk sk) (Sum.inr m)).run l₀ =
          (fun σ ↦ (σ, l₀ ++ [⟨m, σ⟩])) <$> liftR (sigAlg.sign pk sk m) := by
        change liftR ((fun σ ↦ (σ, l₀ ++ [⟨m, σ⟩])) <$> sigAlg.sign pk sk m) = _
        rw [liftR_map]
      have h2 : ((privSpec.passthrough + (liftSig sigAlg).signingOracle pk sk) (Sum.inr m)).run =
          (fun σ ↦ (σ, ([⟨m, σ⟩] : QueryLog (M →ₒ S)))) <$> liftR (sigAlg.sign pk sk m) := by
        simp only [QueryImpl.passthrough_add, QueryImpl.add_apply_inr,
          SignatureAlg.signingOracle, QueryImpl.withLogging_apply, liftSig]
        simp
      rw [h1, h2]
      simp [ih]

variable {sigAlg : SignatureAlg ProbComp M PK SK S}

/-- The classical strategy of an arbitrary quantum forger, as an EUF-CMA adversary against the
scheme over the sampling interface `distSpec + unifSpec`. -/
noncomputable def QForger.toStrategy (Q : QForger W sigAlg) :
    SignatureAlg.UnforgeableAdversary (liftSig sigAlg) :=
  ⟨fun pk ↦ PQ.Interactive.toStrategy (Q.main pk) Q.ρ₀⟩

theorem qWeight_qSigExperiment_strategy (fresh : QueryLog (M →ₒ S) → M → S → Bool)
    (Q : QForger W sigAlg) :
    qWeight (· = true) (qSigExperiment fresh Q) Q.ρ₀ =
      prob ((liftSig sigAlg).keygen >>= fun ks ↦
        (liftSig sigAlg).runWithSigningOracle ks.1 ks.2
            (PQ.Interactive.toStrategy (Q.main ks.1) Q.ρ₀) >>= fun r ↦
          (liftSig sigAlg).verify ks.1 r.1.1 r.1.2 >>= fun verified ↦
            pure (fresh r.2 r.1.1 r.1.2 && verified)) (· = true) := by
  have h1 : ENNReal.ofReal Q.ρ₀.trace.re = 1 := by simp [Q.trace_eq_one]
  rw [← one_mul (prob _ _)]
  refine qWeight_liftU_bind_liftR _ _ _ _ _ _ fun ks ↦ ?_
  have hrun : (liftSig sigAlg).runWithSigningOracle ks.1 ks.2
        (PQ.Interactive.toStrategy (Q.main ks.1) Q.ρ₀) =
      (simulateQ (strategyImpl (signImpl sigAlg ks.1 ks.2))
        (PQ.Interactive.toStrategy (Q.main ks.1) Q.ρ₀)).run [] := by
    rw [run_simulateQ_strategyImpl_signImpl]
    simp
  rw [hrun, ← h1]
  refine qWeight_close_bind_strategy _ (forwardsUnif_signImpl sigAlg ks.1 ks.2) _ _ _
    (fun r ρ' _ ↦ ?_) _ _ _ Q.posSemidef
  exact qWeight_liftU_bind_liftR _ _ _ _ _ _ fun v ↦ by simp

/-- **Quantum EUF-CMA of an arbitrary quantum forger (T5).**  With no assumption on the forger,
its quantum EUF-CMA advantage is the success probability of VCVio's EUF-CMA experiment for the
same scheme, run over the sampling interface `distSpec + unifSpec`, against the classical
strategy of the forger. -/
theorem qUnforgeableAdvantage_eq_strategy (Q : QForger W sigAlg) :
    qUnforgeableAdvantage Q = 𝒟[SignatureAlg.unforgeableExperiment Q.toStrategy] {true} := by
  rw [qUnforgeableAdvantage, qUnforgeableExperiment, qWeight_qSigExperiment_strategy,
    ← prEvent_eq_evalDist_singleton]
  rfl

/-- **Lifting principle for arbitrary quantum forgers.**  A bound on the EUF-CMA success
probability of all classical adversaries with private sampling interface `distSpec + unifSpec`
holds for every quantum forger. -/
theorem qUnforgeableAdvantage_le_of_forall_strategy (Q : QForger W sigAlg)
    (bound : SignatureAlg.UnforgeableAdversary (liftSig sigAlg) → ℝ≥0∞)
    (h : ∀ A, 𝒟[SignatureAlg.unforgeableExperiment A] {true} ≤ bound A) :
    qUnforgeableAdvantage Q ≤ bound Q.toStrategy :=
  (qUnforgeableAdvantage_eq_strategy Q).trans_le (h _)

end eufcma

end PQ.Interactive

open PQ.Interactive in
#print axioms qWeight_close_bind_strategy
open PQ.Interactive in
#print axioms qWeight_close_eq_strategy
open PQ.Interactive in
#print axioms qUnforgeableAdvantage_eq_strategy
