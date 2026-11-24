import PQ.Interactive.QromBridgeEvalProg
import PQ.QROM.ExactPrfStruct

/-!
# The PRF game of the Part-1 model for port-uniform machines and a structured oracle

* `lazy_eq_avg`: for every Part-1 machine `Q` over the PRF interface, the Born weight of the
  ideal experiment (VCVio's LAZY random function `prfIdealQueryImpl` on the possibly infinite
  domain `D`) equals the average over EAGER tables `R' : Dm → R` of the experiment in which the
  function queries `d` are answered by `R' (key d)`, for any injective `key : D → Dm` into a
  finite type.
* `prf_PU_real_le_ideal_add`: **the PRF bound in the Part-1 model**.  `A : (X → Y) → machine` a
  port-uniform family with at most `q` oracle calls (`PU A q`), the oracle `Hf g : X → Y` built
  from the uniform keyed function `g : K × Dm → R` locally (`loc`), the real PRF
  `k, d ↦ g (k, key d)`.  Then

    `E_g qPrfRealPr (A (Hf g)) ≤ E_g qPrfIdealPr (A (Hf g)) + 8 q² / |K|`

  where `qPrfRealPr`/`qPrfIdealPr` are the Part-1 games of `PQ/Interactive/Games.lean`
  (VCVio's real and lazy-ideal PRF oracles around the machine).  Uniform-sampling nodes, the
  probabilistic key generation and the lazy ideal oracle are all handled here.
-/

open OracleComp OracleSpec ENNReal Quantum MeasureTheory Matrix PQ.QROM
open scoped Kronecker ComplexOrder

set_option linter.unusedSectionVars false

namespace PQ.Interactive

section lazy

variable {W : Type} [Fintype W] {α : Type} {D R : Type}

/-- The "PRF" whose function is the fixed function `f` (trivial key). -/
def ansScheme (f : D → R) : PRFScheme Unit D R := ⟨pure (), fun _ d ↦ f d⟩

/-- The closed machine: function queries of `Q` answered by `f`. -/
noncomputable def ansRun (f : D → R) (Q : QOC W (PRFScheme.PRFOracleSpec D R) α) : Closed W α :=
  Prod.fst <$> close (statelessImpl ((ansScheme f).prfRealQueryImpl ())) Q ()

/-- The closed machine: function queries of `Q` answered by the lazy random function, from the
cache `c`. -/
noncomputable def idealRun [DecidableEq D] [SampleableType R]
    (Q : QOC W (PRFScheme.PRFOracleSpec D R) α) (c : (D →ₒ R).QueryCache) : Closed W α :=
  Prod.fst <$> close (PRFScheme.prfIdealQueryImpl (D := D) (R := R)) Q c

lemma close_unif_bind {σ ι' : Type} {spec' : OracleSpec ι'}
    (impl : QueryImpl (unifSpec + spec') (StateT σ ProbComp)) (h : ForwardsUnif impl) (n : ℕ)
    (k : Fin (n + 1) → QOC W (unifSpec + spec') α) (s : σ) :
    close impl (liftM ((instrSpec W + (unifSpec + spec')).query (Sum.inr (Sum.inl n))) >>= k) s =
      liftM ((instrSpec W + unifSpec).query (Sum.inr n)) >>= fun u ↦ close impl (k u) s := by
  rw [close_query_bind, h n s, liftU_map, liftU_query, bind_map_left]
  rfl

variable (f : D → R)

lemma ansRun_pure (a : α) : ansRun (W := W) f (pure a) = pure a := by
  simp [ansRun]

lemma ansRun_instr (j : InstrIdx W) (k : Fin (j.1 + 1) → QOC W (PRFScheme.PRFOracleSpec D R) α) :
    ansRun f (liftM ((instrSpec W + PRFScheme.PRFOracleSpec D R).query (Sum.inl j)) >>= k) =
      liftM ((instrSpec W + unifSpec).query (Sum.inl j)) >>= fun i ↦ ansRun f (k i) := by
  unfold ansRun
  rw [close_instr_bind, map_bind]

lemma ansRun_unif (n : ℕ) (k : Fin (n + 1) → QOC W (PRFScheme.PRFOracleSpec D R) α) :
    ansRun f (liftM ((instrSpec W + PRFScheme.PRFOracleSpec D R).query
        (Sum.inr (Sum.inl n))) >>= k) =
      liftM ((instrSpec W + unifSpec).query (Sum.inr n)) >>= fun u ↦ ansRun f (k u) := by
  unfold ansRun
  rw [close_unif_bind _ (forwardsUnif_prfReal _ _), map_bind]

lemma ansRun_oracle (d : D) (k : R → QOC W (PRFScheme.PRFOracleSpec D R) α) :
    ansRun f (liftM ((instrSpec W + PRFScheme.PRFOracleSpec D R).query
        (Sum.inr (Sum.inr d))) >>= k) = ansRun f (k (f d)) := by
  unfold ansRun
  rw [close_query_bind]
  have h : (statelessImpl ((ansScheme f).prfRealQueryImpl ()) (Sum.inr d)).run () =
      pure (f d, ()) := by
    change (fun u ↦ (u, ())) <$> (ansScheme f).prfRealQueryImpl () (Sum.inr d) = _
    rw [PRFScheme.prfRealQueryImpl_apply_inr]
    simp [ansScheme]
  rw [h, liftU_pure, pure_bind]

variable [DecidableEq D] [SampleableType R]

lemma idealRun_pure (a : α) (c : (D →ₒ R).QueryCache) :
    idealRun (W := W) (pure a) c = pure a := by
  simp [idealRun]

lemma idealRun_instr (j : InstrIdx W) (k : Fin (j.1 + 1) → QOC W (PRFScheme.PRFOracleSpec D R) α)
    (c : (D →ₒ R).QueryCache) :
    idealRun (liftM ((instrSpec W + PRFScheme.PRFOracleSpec D R).query (Sum.inl j)) >>= k) c =
      liftM ((instrSpec W + unifSpec).query (Sum.inl j)) >>= fun i ↦ idealRun (k i) c := by
  unfold idealRun
  rw [close_instr_bind, map_bind]

lemma idealRun_unif (n : ℕ) (k : Fin (n + 1) → QOC W (PRFScheme.PRFOracleSpec D R) α)
    (c : (D →ₒ R).QueryCache) :
    idealRun (liftM ((instrSpec W + PRFScheme.PRFOracleSpec D R).query
        (Sum.inr (Sum.inl n))) >>= k) c =
      liftM ((instrSpec W + unifSpec).query (Sum.inr n)) >>= fun u ↦ idealRun (k u) c := by
  unfold idealRun
  rw [close_unif_bind _ forwardsUnif_prfIdeal, map_bind]

lemma idealRun_oracle_some (d : D) (k : R → QOC W (PRFScheme.PRFOracleSpec D R) α)
    (c : (D →ₒ R).QueryCache) (r : R) (h : c d = some r) :
    idealRun (liftM ((instrSpec W + PRFScheme.PRFOracleSpec D R).query
        (Sum.inr (Sum.inr d))) >>= k) c = idealRun (k r) c := by
  unfold idealRun
  rw [close_query_bind]
  have hr : (PRFScheme.prfIdealQueryImpl (D := D) (R := R) (Sum.inr d)).run c = pure (r, c) := by
    change ((D →ₒ R).randomOracle d).run c = _
    rw [randomOracle.run_eq, h]
  rw [hr, liftU_pure, pure_bind]

lemma idealRun_oracle_none (d : D) (k : R → QOC W (PRFScheme.PRFOracleSpec D R) α)
    (c : (D →ₒ R).QueryCache) (h : c d = none) :
    idealRun (liftM ((instrSpec W + PRFScheme.PRFOracleSpec D R).query
        (Sum.inr (Sum.inr d))) >>= k) c =
      liftU ($ᵗ R) >>= fun r ↦ idealRun (k r) (c.cacheQuery d r) := by
  unfold idealRun
  rw [close_query_bind]
  have hr : (PRFScheme.prfIdealQueryImpl (D := D) (R := R) (Sum.inr d)).run c =
      ($ᵗ R) >>= fun u ↦ pure (u, c.cacheQuery d u) := by
    change ((D →ₒ R).randomOracle d).run c = _
    rw [randomOracle.run_eq, h]
  rw [hr, liftU_bind, bind_assoc, map_bind]
  simp

/-! ### Tables consistent with a cache -/

variable {Dm : Type} [Fintype Dm] [DecidableEq Dm] [Fintype R] [DecidableEq R]
  (key : D → Dm)

open Classical in
/-- The tables `R' : Dm → R` that agree with the cache `c` through `key`. -/
noncomputable def consTables (c : (D →ₒ R).QueryCache) : Finset (Dm → R) :=
  Finset.univ.filter fun R' ↦ ∀ d r, c d = some r → R' (key d) = r

lemma mem_consTables (c : (D →ₒ R).QueryCache) (R' : Dm → R) :
    R' ∈ consTables key c ↔ ∀ d r, c d = some r → R' (key d) = r := by
  simp [consTables]

lemma consTables_empty : consTables (R := R) key ∅ = Finset.univ := by
  ext R'
  simp [mem_consTables]

open Classical in
lemma consTables_cacheQuery (c : (D →ₒ R).QueryCache) (d : D) (hd : c d = none) (r : R) :
    consTables key (c.cacheQuery d r) = (consTables key c).filter fun R' ↦ R' (key d) = r := by
  ext R'
  rw [Finset.mem_filter, mem_consTables, mem_consTables]
  constructor
  · intro h
    refine ⟨fun d' r' hc ↦ h d' r' ?_, h d r (QueryCache.cacheQuery_self c d r)⟩
    have hne : d' ≠ d := fun e ↦ by rw [e, hd] at hc; exact nomatch hc
    rw [QueryCache.cacheQuery_of_ne c r hne]
    exact hc
  · rintro ⟨h1, h2⟩ d' r' hc
    by_cases hne : d' = d
    · subst hne
      rw [QueryCache.cacheQuery_self] at hc
      rw [← Option.some.inj hc]
      exact h2
    · rw [QueryCache.cacheQuery_of_ne c r hne] at hc
      exact h1 d' r' hc

variable (hkey : Function.Injective key)
include hkey

lemma card_consTables_cacheQuery (c : (D →ₒ R).QueryCache) (d : D) (hd : c d = none) (r r' : R) :
    (consTables key (c.cacheQuery d r)).card = (consTables key (c.cacheQuery d r')).card := by
  classical
  have hmem : ∀ (a b : R) (R' : Dm → R), R' ∈ consTables key (c.cacheQuery d a) →
      Function.update R' (key d) b ∈ consTables key (c.cacheQuery d b) := by
    intro a b R' hR'
    rw [consTables_cacheQuery key c d hd, Finset.mem_filter, mem_consTables] at hR' ⊢
    refine ⟨fun d' r'' hc ↦ ?_, by simp⟩
    have hne : key d' ≠ key d := fun e ↦ by
      rw [hkey e, hd] at hc
      exact nomatch hc
    rw [Function.update_of_ne hne]
    exact hR'.1 d' r'' hc
  have hval : ∀ (a : R) (R' : Dm → R), R' ∈ consTables key (c.cacheQuery d a) →
      R' (key d) = a := by
    intro a R' hR'
    rw [consTables_cacheQuery key c d hd, Finset.mem_filter] at hR'
    exact hR'.2
  refine Finset.card_bij' (fun R' _ ↦ Function.update R' (key d) r')
    (fun R' _ ↦ Function.update R' (key d) r) (fun R' h ↦ hmem r r' R' h)
    (fun R' h ↦ hmem r' r R' h) (fun R' h ↦ ?_) (fun R' h ↦ ?_)
  · rw [Function.update_idem, ← hval r R' h, Function.update_eq_self]
  · rw [Function.update_idem, ← hval r' R' h, Function.update_eq_self]

lemma card_consTables (c : (D →ₒ R).QueryCache) (d : D) (hd : c d = none) (r : R) :
    ((consTables key c).card : ℝ≥0∞) =
      (Fintype.card R : ℝ≥0∞) * ((consTables key (c.cacheQuery d r)).card : ℝ≥0∞) := by
  classical
  have h := Finset.card_eq_sum_card_fiberwise (f := fun R' : Dm → R ↦ R' (key d))
    (s := consTables key c) (t := Finset.univ) fun _ _ ↦ Finset.mem_univ _
  have h2 : ∀ b ∈ (Finset.univ : Finset R),
      ((consTables key c).filter fun R' ↦ R' (key d) = b).card =
        (consTables key (c.cacheQuery d r)).card := fun b _ ↦ by
    rw [← consTables_cacheQuery key c d hd b]
    exact card_consTables_cacheQuery key hkey c d hd b r
  rw [Finset.sum_congr rfl h2, Finset.sum_const, Finset.card_univ, smul_eq_mul] at h
  rw [h]
  push_cast
  rfl

variable [Nonempty R]

/-- Lazy = eager, relative to a cache. -/
theorem lazy_eq_sum (p : α → Prop) [DecidablePred p]
    (Q : QOC W (PRFScheme.PRFOracleSpec D R) α) :
    ∀ (c : (D →ₒ R).QueryCache) (M : Matrix W W ℂ),
      ((consTables key c).card : ℝ≥0∞) * qWeight p (idealRun Q c) M =
        ∑ R' ∈ consTables key c, qWeight p (ansRun (fun d ↦ R' (key d)) Q) M := by
  classical
  induction Q using OracleComp.inductionOn with
  | pure a =>
    intro c M
    simp only [idealRun_pure, ansRun_pure, Finset.sum_const, nsmul_eq_mul]
  | query_bind t k ih =>
    intro c M
    rcases t with j | n | d
    · simp only [idealRun_instr, ansRun_instr, qWeight_instr_bind]
      rw [Finset.mul_sum, Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ ↦ ih i c _
    · simp only [idealRun_unif, ansRun_unif, qWeight_unif_bind]
      rw [← Finset.mul_sum, Finset.sum_comm, mul_left_comm]
      congr 1
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ ↦ ih i c _
    · simp only [ansRun_oracle]
      rcases hc : c d with _ | r
      · rw [idealRun_oracle_none _ _ _ hc, qWeight_liftU_uniform_bind]
        have hR : (Fintype.card R : ℝ≥0∞) ≠ 0 := by simp
        have hR' : (Fintype.card R : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
        calc ((consTables key c).card : ℝ≥0∞) *
              ((Fintype.card R : ℝ≥0∞)⁻¹ *
                ∑ r, qWeight p (idealRun (k r) (c.cacheQuery d r)) M)
            = ∑ r, ((consTables key (c.cacheQuery d r)).card : ℝ≥0∞) *
                qWeight p (idealRun (k r) (c.cacheQuery d r)) M := by
              rw [← mul_assoc, Finset.mul_sum]
              refine Finset.sum_congr rfl fun r _ ↦ ?_
              have e : (Fintype.card R : ℝ≥0∞) *
                  ((consTables key (c.cacheQuery d r)).card : ℝ≥0∞) * (Fintype.card R : ℝ≥0∞)⁻¹ =
                  ((consTables key (c.cacheQuery d r)).card : ℝ≥0∞) := by
                rw [mul_comm (Fintype.card R : ℝ≥0∞), mul_assoc,
                  ENNReal.mul_inv_cancel hR hR', mul_one]
              rw [card_consTables key hkey c d hc r, e]
          _ = ∑ r, ∑ R' ∈ (consTables key c).filter (fun R' ↦ R' (key d) = r),
                qWeight p (ansRun (fun d ↦ R' (key d)) (k (R' (key d)))) M := by
              refine Finset.sum_congr rfl fun r _ ↦ ?_
              rw [ih r, consTables_cacheQuery key c d hc r]
              refine Finset.sum_congr rfl fun R' hR ↦ ?_
              rw [(Finset.mem_filter.1 hR).2]
          _ = _ := Finset.sum_fiberwise _ _ _
      · rw [idealRun_oracle_some _ _ _ r hc, ih r c M]
        refine Finset.sum_congr rfl fun R' hR ↦ ?_
        rw [(mem_consTables key c R').1 hR d r hc]

/-- **Lazy = eager.**  The ideal PRF experiment around any Part-1 machine equals the average over
uniformly random tables of the experiment with the function queries answered through `key`. -/
theorem lazy_eq_avg (p : α → Prop) [DecidablePred p]
    (Q : QOC W (PRFScheme.PRFOracleSpec D R) α) (M : Matrix W W ℂ) :
    qWeight p (idealRun Q ∅) M =
      (Fintype.card (Dm → R) : ℝ≥0∞)⁻¹ *
        ∑ R' : Dm → R, qWeight p (ansRun (fun d ↦ R' (key d)) Q) M := by
  have h := lazy_eq_sum key hkey p Q ∅ M
  rw [consTables_empty, Finset.card_univ] at h
  rw [← h, ← mul_assoc, ENNReal.inv_mul_cancel (by simp) (ENNReal.natCast_ne_top _), one_mul]

end lazy

/-! ## The PRF bound for port-uniform machines -/

section prf

variable {X Y E : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
  [Fintype E] [DecidableEq E]
  {K Dm D R : Type} [Fintype K] [DecidableEq K] [SampleableType K] [Fintype Dm] [DecidableEq Dm]
  [Fintype R] [DecidableEq R] [SampleableType R] [DecidableEq D]

/-- The PRF `k, d ↦ g (k, key d)` with uniform key. -/
noncomputable def keyedScheme (key : D → Dm) (g : K × Dm → R) : PRFScheme K D R :=
  ⟨$ᵗ K, fun k d ↦ g (k, key d)⟩

/-- Count port queries after each classical PRF query is answered by a fixed function.
The same budget applies uniformly to every such function. -/
def PrfAnswerCost
    (A : (X → Y) → QOC (WS X Y E) (PRFScheme.PRFOracleSpec D R) Bool) (q : ℕ) : Prop :=
  ∀ f : D → R, PUE (spec := unifSpec) cnt0 (fun H ↦ ansRun f (A H)) q

theorem PUE.prfAnswerCost
    {A : (X → Y) → QOC (WS X Y E) (PRFScheme.PRFOracleSpec D R) Bool} {q : ℕ}
    (hA : PUE (fun _ => 0) A q) : PrfAnswerCost A q :=
  fun _ ↦ PUE.map Prod.fst (PUE.close _ (fun _ _ => EvalCost.const _) hA ())

/-- Structured PRF bound charging both quantum port calls and classical evaluations of that port. -/
theorem prf_answer_real_le_ideal_add [Nonempty K] [Nonempty Dm] [Nonempty R] [Nonempty X]
    (key : D → Dm) (hkey : Function.Injective key)
    (A : (X → Y) → QOC (WS X Y E) (PRFScheme.PRFOracleSpec D R) Bool) (q : ℕ) (hA : PrfAnswerCost A q)
    (Hf : (K × Dm → R) → X → Y) (loc : X → Option (K × Dm))
    (hloc : ∀ g g' x, (∀ p, loc x = some p → g p = g' p) → Hf g x = Hf g' x)
    (ρ : SubState ((X × Y) × E)) :
    (∑ g : K × Dm → R, (Fintype.card (K × Dm → R) : ℝ≥0∞)⁻¹ *
        qPrfRealPr (keyedScheme key g) (A (Hf g)) (ρ.matrix ⊗ₖ (SubState.basis ()).matrix)) ≤
      (∑ g : K × Dm → R, (Fintype.card (K × Dm → R) : ℝ≥0∞)⁻¹ *
        qPrfIdealPr (A (Hf g)) (ρ.matrix ⊗ₖ (SubState.basis ()).matrix)) +
        ENNReal.ofReal (8 * (q : ℝ) ^ 2 / Fintype.card K) := by
  set M := ρ.matrix ⊗ₖ (SubState.basis ()).matrix with hM
  choose x hx hxe using fun f ↦ (hA f).exists_prog_qprob
  have hreal : ∀ g : K × Dm → R, qPrfRealPr (keyedScheme key g) (A (Hf g)) M =
      (Fintype.card K : ℝ≥0∞)⁻¹ * ∑ k : K, PQ.QROM.qprob LocalSig.Interp.instruments (Hf g)
        (x fun d ↦ g (k, key d)) ρ (fun p ↦ p.2 = true) := by
    intro g
    unfold qPrfRealPr qPrfRealExperiment
    have e : (keyedScheme key g).keygen = ($ᵗ K) := rfl
    rw [e, qWeight_liftU_uniform_bind]
    congr 1
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    exact (hxe (fun d ↦ g (k, key d)) (· = true) (Hf g) ρ).symm
  have hideal : ∀ g : K × Dm → R, qPrfIdealPr (A (Hf g)) M =
      (Fintype.card (Dm → R) : ℝ≥0∞)⁻¹ * ∑ R' : Dm → R,
        PQ.QROM.qprob LocalSig.Interp.instruments (Hf g) (x fun d ↦ R' (key d)) ρ
          (fun p ↦ p.2 = true) := by
    intro g
    have h := lazy_eq_avg key hkey (· = true) (A (Hf g)) M
    refine Eq.trans h ?_
    congr 1
    refine Finset.sum_congr rfl fun R' _ ↦ ?_
    exact (hxe (fun d ↦ R' (key d)) (· = true) (Hf g) ρ).symm
  have hmain := prfStruct_real_le_ideal_add (K := K) (Dm := Dm) (R := R)
    LocalSig.Interp.instruments ρ q Hf loc hloc (fun R' ↦ x fun d ↦ R' (key d))
    (fun R' ↦ hx _) (fun p ↦ p.2 = true)
  simp only [hreal, hideal]
  refine le_trans (le_of_eq ?_) (hmain.trans (le_of_eq ?_))
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun g _ ↦ ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ ↦ by ring
  · congr 1
    refine Finset.sum_congr rfl fun g _ ↦ ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun R' _ ↦ by ring

/-- Structured PRF bound charging both quantum port calls and classical evaluations of that port. -/
theorem prf_PUE_real_le_ideal_add [Nonempty K] [Nonempty Dm] [Nonempty R] [Nonempty X]
    (key : D → Dm) (hkey : Function.Injective key)
    (A : (X → Y) → QOC (WS X Y E) (PRFScheme.PRFOracleSpec D R) Bool) (q : ℕ) (hA : PUE (fun _ => 0) A q)
    (Hf : (K × Dm → R) → X → Y) (loc : X → Option (K × Dm))
    (hloc : ∀ g g' x, (∀ p, loc x = some p → g p = g' p) → Hf g x = Hf g' x)
    (ρ : SubState ((X × Y) × E)) :
    (∑ g : K × Dm → R, (Fintype.card (K × Dm → R) : ℝ≥0∞)⁻¹ *
        qPrfRealPr (keyedScheme key g) (A (Hf g)) (ρ.matrix ⊗ₖ (SubState.basis ()).matrix)) ≤
      (∑ g : K × Dm → R, (Fintype.card (K × Dm → R) : ℝ≥0∞)⁻¹ *
        qPrfIdealPr (A (Hf g)) (ρ.matrix ⊗ₖ (SubState.basis ()).matrix)) +
        ENNReal.ofReal (8 * (q : ℝ) ^ 2 / Fintype.card K) := by

  exact prf_answer_real_le_ideal_add key hkey A q hA.prfAnswerCost Hf loc hloc ρ

/-- **The PRF bound in the Part-1 model, structured oracle, port-uniform machines.** -/
theorem prf_PU_real_le_ideal_add [Nonempty K] [Nonempty Dm] [Nonempty R] [Nonempty X]
    (key : D → Dm) (hkey : Function.Injective key)
    (A : (X → Y) → QOC (WS X Y E) (PRFScheme.PRFOracleSpec D R) Bool) (q : ℕ) (hA : PU A q)
    (Hf : (K × Dm → R) → X → Y) (loc : X → Option (K × Dm))
    (hloc : ∀ g g' x, (∀ p, loc x = some p → g p = g' p) → Hf g x = Hf g' x)
    (ρ : SubState ((X × Y) × E)) :
    (∑ g : K × Dm → R, (Fintype.card (K × Dm → R) : ℝ≥0∞)⁻¹ *
        qPrfRealPr (keyedScheme key g) (A (Hf g)) (ρ.matrix ⊗ₖ (SubState.basis ()).matrix)) ≤
      (∑ g : K × Dm → R, (Fintype.card (K × Dm → R) : ℝ≥0∞)⁻¹ *
        qPrfIdealPr (A (Hf g)) (ρ.matrix ⊗ₖ (SubState.basis ()).matrix)) +
        ENNReal.ofReal (8 * (q : ℝ) ^ 2 / Fintype.card K) := by
  exact prf_PUE_real_le_ideal_add key hkey A q hA.toPUE Hf loc hloc ρ

end prf

end PQ.Interactive

open PQ.Interactive in
#print axioms lazy_eq_avg
open PQ.Interactive in
#print axioms prf_PU_real_le_ideal_add
