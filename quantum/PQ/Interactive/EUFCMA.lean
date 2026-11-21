import PQ.Interactive.Collapse
import VCVio.CryptoFoundations.SignatureAlg

/-!
# EUF-CMA against quantum forgers with classical signing queries

`QForger W sigAlg` is a quantum machine with workspace `W` that receives the public key, may sample
uniformly, queries the signing oracle classically, and outputs a forgery.  The quantum EUF-CMA
experiment `qUnforgeableExperiment` is VCVio's `SignatureAlg.unforgeableExperiment` with the
quantum machine in place of the classical forger: key generation, the machine run against the
logged signing oracle, verification, freshness; its success probability is the Born weight
`qWeight`.

`qUnforgeableAdvantage_eq`: if the Born probabilities of the forger are rational, its quantum
EUF-CMA advantage *equals* VCVio's classical `unforgeableAdvantage` of the classical strategy
`Q.toClassical`.  Hence every classical bound holding for all classical forgers holds for the
quantum forger (`qUnforgeableAdvantage_le_of_forall`).
-/

open OracleComp OracleSpec ENNReal Quantum MeasureTheory
open scoped ComplexOrder

namespace PQ.Interactive

variable {W : Type} [Fintype W] {M PK SK S : Type} {α : Type}

/-- The logged signing oracle of the EUF-CMA game as a stateful implementation: uniform sampling
is forwarded, signing queries are answered by `sigAlg.sign pk sk` and the returned
`(message, signature)` pair is appended to the log. -/
def signImpl (sigAlg : SignatureAlg ProbComp M PK SK S) (pk : PK) (sk : SK) :
    QueryImpl (unifSpec + (M →ₒ S)) (StateT (QueryLog (M →ₒ S)) ProbComp)
  | .inl n => fun log ↦ (fun u ↦ (u, log)) <$> (liftM (unifSpec.query n) : ProbComp _)
  | .inr m => fun log ↦ (fun σ ↦ (σ, log ++ [⟨m, σ⟩])) <$> sigAlg.sign pk sk m

lemma forwardsUnif_signImpl (sigAlg : SignatureAlg ProbComp M PK SK S) (pk : PK) (sk : SK) :
    ForwardsUnif (signImpl sigAlg pk sk) := fun _ _ ↦ rfl

/-- The stateful signing oracle is VCVio's `runWithSigningOracle` (which logs in a writer monad),
started from an arbitrary log prefix. -/
lemma run_simulateQ_signImpl (sigAlg : SignatureAlg ProbComp M PK SK S) (pk : PK) (sk : SK)
    (oa : OracleComp (unifSpec + (M →ₒ S)) α) (l₀ : QueryLog (M →ₒ S)) :
    (simulateQ (signImpl sigAlg pk sk) oa).run l₀ =
      (fun x ↦ (x.1, l₀ ++ x.2)) <$> sigAlg.runWithSigningOracle pk sk oa := by
  unfold SignatureAlg.runWithSigningOracle
  induction oa using OracleComp.inductionOn generalizing l₀ with
  | pure a => simp
  | query_bind t k ih =>
    rw [simulateQ_bind, simulateQ_bind, StateT.run_bind, WriterT.run_bind',
      simulateQ_spec_query, simulateQ_spec_query]
    rcases t with n | m
    · have h1 : (signImpl sigAlg pk sk (Sum.inl n)).run l₀ =
          (fun u ↦ (u, l₀)) <$> (liftM (unifSpec.query n) : ProbComp _) := rfl
      have h2 : ((unifSpec.passthrough + sigAlg.signingOracle pk sk) (Sum.inl n)).run =
          (fun u ↦ (u, ([] : QueryLog (M →ₒ S)))) <$> (liftM (unifSpec.query n) : ProbComp _) := by
        simp only [QueryImpl.passthrough_add, QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply,
          QueryImpl.id'_apply]
        rfl
      rw [h1, h2]
      simp [ih]
    · have h1 : (signImpl sigAlg pk sk (Sum.inr m)).run l₀ =
          (fun σ ↦ (σ, l₀ ++ [⟨m, σ⟩])) <$> sigAlg.sign pk sk m := rfl
      have h2 : ((unifSpec.passthrough + sigAlg.signingOracle pk sk) (Sum.inr m)).run =
          (fun σ ↦ (σ, ([⟨m, σ⟩] : QueryLog (M →ₒ S)))) <$> sigAlg.sign pk sk m := by
        simp only [QueryImpl.passthrough_add, QueryImpl.add_apply_inr,
          SignatureAlg.signingOracle, QueryImpl.withLogging_apply]
        simp
      rw [h1, h2]
      simp [ih]

/-- A quantum EUF-CMA forger with workspace basis `W` against `sigAlg`: on input the public key,
a quantum machine with classical access to uniform sampling and the signing oracle, outputting a
candidate forgery; together with its initial workspace state. -/
structure QForger (W : Type) [Fintype W] (sigAlg : SignatureAlg ProbComp M PK SK S) where
  /-- The quantum machine run on the public key. -/
  main : PK → QOC W (unifSpec + (M →ₒ S)) (M × S)
  /-- Initial state of the workspace (a density matrix). -/
  ρ₀ : Matrix W W ℂ
  posSemidef : ρ₀.PosSemidef
  trace_eq_one : ρ₀.trace = 1

variable {sigAlg : SignatureAlg ProbComp M PK SK S}

/-- The signature game against a quantum forger with freshness predicate `fresh`: key generation,
the quantum machine run against the logged signing oracle, verification, freshness.  It is a closed
quantum-classical machine. -/
def qSigExperiment (fresh : QueryLog (M →ₒ S) → M → S → Bool) (Q : QForger W sigAlg) :
    Closed W Bool :=
  liftU sigAlg.keygen >>= fun ks ↦
    close (signImpl sigAlg ks.1 ks.2) (Q.main ks.1) [] >>= fun r ↦
      liftU (sigAlg.verify ks.1 r.1.1 r.1.2) >>= fun verified ↦
        pure (fresh r.2 r.1.1 r.1.2 && verified)

open scoped Classical in
/-- The quantum EUF-CMA experiment: `SignatureAlg.unforgeableExperiment` with the quantum machine
in place of the classical forger. -/
noncomputable def qUnforgeableExperiment (Q : QForger W sigAlg) : Closed W Bool :=
  qSigExperiment (fun log msg _ ↦ !log.wasQueried msg) Q

/-- Quantum EUF-CMA advantage: the Born probability that the experiment outputs `true`. -/
noncomputable def qUnforgeableAdvantage (Q : QForger W sigAlg) : ℝ≥0∞ :=
  qWeight (· = true) (qUnforgeableExperiment Q) Q.ρ₀

open scoped Classical in
/-- The quantum SUF-CMA experiment (`SignatureAlg.strongUnforgeableExperiment`). -/
noncomputable def qStrongUnforgeableExperiment (Q : QForger W sigAlg) : Closed W Bool :=
  qSigExperiment (fun log msg σ ↦ !SignatureAlg.signingLogContains log msg σ) Q

/-- Quantum SUF-CMA advantage. -/
noncomputable def qStrongUnforgeableAdvantage (Q : QForger W sigAlg) : ℝ≥0∞ :=
  qWeight (· = true) (qStrongUnforgeableExperiment Q) Q.ρ₀

/-- The classical forger simulating the quantum forger: it tracks the workspace state and samples
every measurement outcome with its Born probability. -/
noncomputable def QForger.toClassical (Q : QForger W sigAlg) :
    SignatureAlg.UnforgeableAdversary sigAlg :=
  ⟨fun pk ↦ toProbComp (Q.main pk) Q.ρ₀⟩

/-- The same classical strategy as a SUF-CMA adversary. -/
noncomputable def QForger.toClassicalStrong (Q : QForger W sigAlg) :
    SignatureAlg.StrongUnforgeableAdversary sigAlg :=
  ⟨fun pk ↦ toProbComp (Q.main pk) Q.ρ₀⟩

/-- The signature game against a quantum forger with rational Born probabilities has the same
success probability as the classical game against its classical strategy. -/
theorem qWeight_qSigExperiment (fresh : QueryLog (M →ₒ S) → M → S → Bool) (Q : QForger W sigAlg)
    (hQ : ∀ pk, RationalBorn (Q.main pk) Q.ρ₀) :
    qWeight (· = true) (qSigExperiment fresh Q) Q.ρ₀ =
      prob (sigAlg.keygen >>= fun ks ↦
        sigAlg.runWithSigningOracle ks.1 ks.2 (toProbComp (Q.main ks.1) Q.ρ₀) >>= fun r ↦
          sigAlg.verify ks.1 r.1.1 r.1.2 >>= fun verified ↦
            pure (fresh r.2 r.1.1 r.1.2 && verified)) (· = true) := by
  have h1 : ENNReal.ofReal Q.ρ₀.trace.re = 1 := by simp [Q.trace_eq_one]
  rw [← one_mul (prob _ _)]
  refine qWeight_liftU_bind _ _ _ _ _ _ fun ks ↦ ?_
  have hrun : sigAlg.runWithSigningOracle ks.1 ks.2 (toProbComp (Q.main ks.1) Q.ρ₀) =
      (simulateQ (signImpl sigAlg ks.1 ks.2) (toProbComp (Q.main ks.1) Q.ρ₀)).run [] := by
    rw [run_simulateQ_signImpl]
    simp
  rw [hrun, ← h1]
  refine qWeight_close_bind _ (forwardsUnif_signImpl sigAlg ks.1 ks.2) _ _ _ (fun r ρ' _ ↦ ?_)
    _ _ _ Q.posSemidef (hQ ks.1)
  exact qWeight_liftU_bind _ _ _ _ _ _ fun v ↦ by simp

/-- **Quantum EUF-CMA = classical EUF-CMA of the classical strategy (T3).** -/
theorem qUnforgeableAdvantage_eq (Q : QForger W sigAlg)
    (hQ : ∀ pk, RationalBorn (Q.main pk) Q.ρ₀) :
    qUnforgeableAdvantage Q =
      SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp Q.toClassical := by
  rw [qUnforgeableAdvantage, qUnforgeableExperiment, qWeight_qSigExperiment _ Q hQ,
    SignatureAlg.unforgeableAdvantage, ProbCompRuntime.probComp_evalDist,
    ← prEvent_eq_evalDist_singleton]
  rfl

/-- **Lifting principle.**  Any bound proved for all classical forgers holds for the quantum
forger `Q`, with the bound evaluated at the classical strategy of `Q`. -/
theorem qUnforgeableAdvantage_le_of_forall (Q : QForger W sigAlg)
    (hQ : ∀ pk, RationalBorn (Q.main pk) Q.ρ₀)
    (bound : SignatureAlg.UnforgeableAdversary sigAlg → ℝ≥0∞)
    (h : ∀ A, SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤ bound A) :
    qUnforgeableAdvantage Q ≤ bound Q.toClassical :=
  (qUnforgeableAdvantage_eq Q hQ).trans_le (h _)

/-- Quantum SUF-CMA = classical SUF-CMA of the classical strategy. -/
theorem qStrongUnforgeableAdvantage_eq (Q : QForger W sigAlg)
    (hQ : ∀ pk, RationalBorn (Q.main pk) Q.ρ₀) :
    qStrongUnforgeableAdvantage Q =
      SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp Q.toClassicalStrong := by
  rw [qStrongUnforgeableAdvantage, qStrongUnforgeableExperiment, qWeight_qSigExperiment _ Q hQ,
    SignatureAlg.strongUnforgeableAdvantage, ProbCompRuntime.probComp_evalDist,
    ← prEvent_eq_evalDist_singleton]
  rfl

theorem qStrongUnforgeableAdvantage_le_of_forall
    (Q : QForger W sigAlg) (hQ : ∀ pk, RationalBorn (Q.main pk) Q.ρ₀)
    (bound : SignatureAlg.StrongUnforgeableAdversary sigAlg → ℝ≥0∞)
    (h : ∀ A, SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp A ≤ bound A) :
    qStrongUnforgeableAdvantage Q ≤ bound Q.toClassicalStrong :=
  (qStrongUnforgeableAdvantage_eq Q hQ).trans_le (h _)

end PQ.Interactive

open PQ.Interactive in
#print axioms qUnforgeableAdvantage_eq
open PQ.Interactive in
#print axioms qUnforgeableAdvantage_le_of_forall
open PQ.Interactive in
#print axioms qStrongUnforgeableAdvantage_eq
