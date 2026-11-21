import PQ.Interactive.ApproxGames

/-!
# Limits of the named Born probabilities, and classical wrappers around quantum forgers

* Limit statements for the individual real/ideal Born probabilities of the two-world games
  (`qPrfRealPr`, `qPrfIdealPr`, `qSM_DT_UD_RealSuccess`, `qSM_DT_UD_IdealSuccess`,
  `qDsprFV_Success`, `qDsprFV_SPProbability`): each is the limit of the corresponding classical
  probability of the classical approximants.  These are what statements in linear form need.
* `QForger.wrapForger`: a classical interface translation (a stateless handler for the forger's
  queries, an encoding of the public key, a translation of the forgery) around a quantum forger
  against one scheme is a quantum forger against another scheme; its classical approximants are
  the translation applied to the approximants (`toClassicalWith_wrapForger`).
-/

open OracleComp OracleSpec ENNReal Quantum MeasureTheory Topology
open Filter (Tendsto atTop)
open scoped ComplexOrder

namespace PQ.Interactive

variable {W : Type} [Fintype W] {α β γ : Type}
variable {samp : ℕ → Sampler W}

section prf

variable {K D R : Type}

theorem tendsto_qPrfRealPr (hs : BornApprox samp) (prf : PRFScheme K D R)
    (Q : QOC W (PRFScheme.PRFOracleSpec D R) Bool) (ρ : Matrix W W ℂ) (hρ : ρ.PosSemidef)
    (h1 : ρ.trace = 1) :
    Tendsto (fun n ↦ 𝒟[prf.prfRealExperiment (toProbCompWith (samp n) Q ρ)] {true}) atTop
      (𝓝 (qPrfRealPr prf Q ρ)) :=
  tendsto_prfRealExperiment hs prf Q ρ hρ h1

theorem tendsto_qPrfIdealPr [DecidableEq D] [SampleableType R] (hs : BornApprox samp)
    (Q : QOC W (PRFScheme.PRFOracleSpec D R) Bool) (ρ : Matrix W W ℂ) (hρ : ρ.PosSemidef)
    (h1 : ρ.trace = 1) :
    Tendsto (fun n ↦ 𝒟[PRFScheme.prfIdealExperiment (toProbCompWith (samp n) Q ρ)] {true}) atTop
      (𝓝 (qPrfIdealPr Q ρ)) :=
  tendsto_prfIdealExperiment hs Q ρ hρ h1

end prf

section twoWorld

open TweakableHash

variable {ι PkSeed Tweak M M' Y : Type}

theorem tendsto_qSM_DT_UD_RealSuccess [DecidableEq Tweak] (hs : BornApprox samp)
    {P : SM_DT_UD_Problem ι PkSeed Tweak M M' Y} (adv : QSM_DT_UD_Adversary W P) :
    Tendsto (fun n ↦ SM_DT_UD_RealSuccess (adv.toClassicalWith (samp n))) atTop
      (𝓝 (qSM_DT_UD_RealSuccess adv)) :=
  tendsto_SM_DT_UD_Experiment hs .real adv

theorem tendsto_qSM_DT_UD_IdealSuccess [DecidableEq Tweak] (hs : BornApprox samp)
    {P : SM_DT_UD_Problem ι PkSeed Tweak M M' Y} (adv : QSM_DT_UD_Adversary W P) :
    Tendsto (fun n ↦ SM_DT_UD_IdealSuccess (adv.toClassicalWith (samp n))) atTop
      (𝓝 (qSM_DT_UD_IdealSuccess adv)) :=
  tendsto_SM_DT_UD_Experiment hs .ideal adv

theorem tendsto_qDsprFV_Success [Fintype M] [DecidableEq Tweak] [DecidableEq M] [DecidableEq Y]
    (hs : BornApprox samp) {P : SM_DT_DSPR_SourceFinalValidity.Problem ι PkSeed Tweak M Y}
    (adv : QDsprFV_Adversary W P) :
    Tendsto (fun n ↦ SM_DT_DSPR_SourceFinalValidity.Success (adv.toClassicalWith (samp n)))
      atTop (𝓝 (qDsprFV_Success adv)) := by
  rw [qDsprFV_Success, qDsprFV_Experiment]
  refine (tendsto_twoPhase hs _ _ _ _ _ adv.posSemidef adv.trace_eq_one).congr fun n ↦ ?_
  rw [SM_DT_DSPR_SourceFinalValidity.Success, ← prob_eq_evalDist_true]
  congr 1
  unfold SM_DT_DSPR_SourceFinalValidity.experiment
  simp only [bind_assoc, pure_bind]
  refine bind_congr fun pk ↦ bind_congr fun r ↦ ?_
  obtain ⟨st, gs⟩ := r
  refine bind_congr fun jb ↦ ?_
  obtain ⟨j, b⟩ := jb
  dsimp only
  cases gs.challenges[j]? with
  | none => rfl
  | some tm => rfl

theorem tendsto_qDsprFV_SPProbability [Fintype M] [DecidableEq Tweak] [DecidableEq M]
    [DecidableEq Y] (hs : BornApprox samp)
    {P : SM_DT_DSPR_SourceFinalValidity.Problem ι PkSeed Tweak M Y}
    (adv : QDsprFV_Adversary W P) :
    Tendsto (fun n ↦ SM_DT_DSPR_SourceFinalValidity.SPProbability (adv.toClassicalWith (samp n)))
      atTop (𝓝 (qDsprFV_SPProbability adv)) := by
  rw [qDsprFV_SPProbability, qDsprFV_SpExperiment]
  refine (tendsto_twoPhase hs _ _ _ _ _ adv.posSemidef adv.trace_eq_one).congr fun n ↦ ?_
  rw [SM_DT_DSPR_SourceFinalValidity.SPProbability, ← prob_eq_evalDist_true]
  congr 1
  unfold SM_DT_DSPR_SourceFinalValidity.spExperiment
  simp only [bind_assoc, pure_bind]
  refine bind_congr fun pk ↦ bind_congr fun r ↦ ?_
  obtain ⟨st, gs⟩ := r
  refine bind_congr fun jb ↦ ?_
  obtain ⟨j, b⟩ := jb
  dsimp only
  cases gs.challenges[j]? with
  | none => rfl
  | some tm => rfl

end twoWorld

/-! ## Classical interface translations around a quantum forger -/

section wrapForger

variable {M PK SK S Mb PKb SKb Sb : Type}
variable {alg : SignatureAlg ProbComp M PK SK S} {balg : SignatureAlg ProbComp Mb PKb SKb Sb}

/-- The quantum forger against `alg` obtained from a quantum forger `Q` against `balg` by a
classical interface translation: `encPk` translates the public key, the stateless handler `h`
answers `Q`'s queries with queries of the `alg` game, `rd` translates the forgery.  Same
workspace, same initial state; `Q` is run once. -/
def QForger.wrapForger (h : QueryImpl (unifSpec + (Mb →ₒ Sb)) (OracleComp (unifSpec + (M →ₒ S))))
    (encPk : PK → PKb) (rd : Mb × Sb → M × S) (Q : QForger W balg) : QForger W alg where
  main pk := rd <$> wrap0 h (Q.main (encPk pk))
  ρ₀ := Q.ρ₀
  posSemidef := Q.posSemidef
  trace_eq_one := Q.trace_eq_one

/-- The classical translation of a classical forger (the shape of `Reduction.Guarded.reduce` and
`Reduction.Coded.reduce`). -/
def wrapClassicalForger
    (h : QueryImpl (unifSpec + (Mb →ₒ Sb)) (OracleComp (unifSpec + (M →ₒ S))))
    (encPk : PK → PKb) (rd : Mb × Sb → M × S) (A : SignatureAlg.UnforgeableAdversary balg) :
    SignatureAlg.UnforgeableAdversary alg where
  main pk := rd <$> simulateQ h (A.main (encPk pk))

/-- **The approximants of the translated quantum forger are the translated approximants**, for
every sampler. -/
theorem toClassicalWith_wrapForger (s : Sampler W)
    (h : QueryImpl (unifSpec + (Mb →ₒ Sb)) (OracleComp (unifSpec + (M →ₒ S))))
    (hh : ForwardsUnif0 h) (encPk : PK → PKb) (rd : Mb × Sb → M × S) (Q : QForger W balg) :
    (Q.wrapForger (alg := alg) h encPk rd).toClassicalWith s =
      wrapClassicalForger h encPk rd (Q.toClassicalWith s) := by
  have hmain : ∀ pk, ((Q.wrapForger (alg := alg) h encPk rd).toClassicalWith s).main pk =
      (wrapClassicalForger (alg := alg) h encPk rd (Q.toClassicalWith s)).main pk := by
    intro pk
    change toProbCompWith s (_ <$> wrap0 _ _) Q.ρ₀ = _
    rw [toProbCompWith_map, toProbCompWith_wrap0 _ _ hh]
    rfl
  change SignatureAlg.UnforgeableAdversary.mk _ = SignatureAlg.UnforgeableAdversary.mk _
  congr 1
  funext pk
  exact hmain pk

/-- The exact (rational) form. -/
theorem toClassical_wrapForger
    (h : QueryImpl (unifSpec + (Mb →ₒ Sb)) (OracleComp (unifSpec + (M →ₒ S))))
    (hh : ForwardsUnif0 h) (encPk : PK → PKb) (rd : Mb × Sb → M × S) (Q : QForger W balg) :
    (Q.wrapForger (alg := alg) h encPk rd).toClassical =
      wrapClassicalForger h encPk rd Q.toClassical := by
  have hmain : ∀ pk, ((Q.wrapForger (alg := alg) h encPk rd).toClassical).main pk =
      (wrapClassicalForger (alg := alg) h encPk rd Q.toClassical).main pk := by
    intro pk
    change toProbComp (_ <$> wrap0 _ _) Q.ρ₀ = _
    rw [toProbComp_map, toProbComp_wrap0 _ hh]
    rfl
  change SignatureAlg.UnforgeableAdversary.mk _ = SignatureAlg.UnforgeableAdversary.mk _
  congr 1
  funext pk
  exact hmain pk

theorem rationalBorn_wrapForger
    (h : QueryImpl (unifSpec + (Mb →ₒ Sb)) (OracleComp (unifSpec + (M →ₒ S))))
    (encPk : PK → PKb) (rd : Mb × Sb → M × S) (Q : QForger W balg)
    (hQ : ∀ pk, RationalBorn (Q.main pk) Q.ρ₀) (pk : PK) :
    RationalBorn ((Q.wrapForger (alg := alg) h encPk rd).main pk)
      (Q.wrapForger (alg := alg) h encPk rd).ρ₀ :=
  rationalBorn_map _ _ _ (rationalBorn_wrap0 _ _ _ (hQ _))

end wrapForger

end PQ.Interactive

open PQ.Interactive in
#print axioms tendsto_qDsprFV_Success
open PQ.Interactive in
#print axioms toClassicalWith_wrapForger
