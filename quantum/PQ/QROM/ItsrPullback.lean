import PQ.QROM.ExactItsr4

/-!
# Adaptive ITSR for an adversary over a port oracle that embeds the random function

`itsr4_adaptive_le` (`ExactItsr4.lean`) is stated for an interactive adversary whose oracle IS
the random function `H : K × Xm → D`.  Here the adversary queries a port function
`φ H : X → Y` built from `H` LOCALLY along an injective map `ι : K × Xm → X`
(`hφ`: `φ H` and `φ G` differ only at points `ι z` with `H z ≠ G z`) — e.g. one hash component
of a port function presenting several components, the others fixed.  Its requests are of an
arbitrary type `Req`, read as target inputs through `tg : Req → Xm`, and its output is read as
a candidate through `oc`.  The statement (`itsrP_adaptive_le`) is the bound of
`itsr4_adaptive_le` verbatim.

The proof is the one of `ExactItsr4.lean`, with the port functions `φ (nFn …)`,
`φ (nBFn …)`: every generic step (`nRuntime_sqrt_le`, `massN`, `pflat_branch_congr`,
`pflat_queryWeight_congr`, `Hidden.search_le'`) is stated for arbitrary port functions; only
the reading of a port point as a row (`rowOf`) and the masses at the embedded points change.
-/

open MeasureTheory ENNReal Quantum Matrix Finset
open scoped Kronecker ComplexOrder

universe u v w

set_option linter.unusedSectionVars false

namespace PQ.QROM
namespace Pull

/-! ## The reprogramming step, port functions on an arbitrary domain -/

section Generic

variable {K X Y Req Par : Type} [Fintype K] [DecidableEq K] [Nonempty K] [Fintype X]
  [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y] [Fintype Par]
  {L : LocalSig.{u, v}} {Out : QReg → Type w} {A : QReg}

/-- The run over transcript ports against the randomizer challenger. -/
noncomputable def pComp {s : ℕ} (x : IAdv L (qromSpec X Y) Req K Out s A) (Rs : Fin s → K) :
    QuantumComp L (qromNSpec (List Req) X Y) (fun u ↦ Out u × List Req) A :=
  IAdv.pflat (rndCh Rs) s [] x

theorem pComp_isTotalBound {s q : ℕ} {x : IAdv L (qromSpec X Y) Req K Out s A}
    (hx : IAdv.IsQueryBound s x (fun _ ↦ q)) (Rs : Fin s → K) : IsTotalBound (pComp x Rs) q :=
  IAdv.pflat_isTotalBound (rndCh Rs) [] hx

/-- Mass of the run against the port functions `fam Rs Φ |t|` on the pair `c`. -/
noncomputable def mpgMass (I : L.Interp) (ρ : SubState A) {s : ℕ}
    (x : IAdv L (qromSpec X Y) Req K Out s A)
    (fam : (Fin s → K) → Par → ℕ → X → Y) (Rs : Fin s → K) (Φ : Par)
    (c : Σ _ : List Req, X) : ℝ≥0∞ :=
  massN I (fun t : List Req ↦ fam Rs Φ t.length) (pComp x Rs) (joint ρ) c

variable {I : L.Interp} {ρ : SubState A} {s : ℕ} {x : IAdv L (qromSpec X Y) Req K Out s A}
  {q Wt : ℕ} {fam : (Fin s → K) → Par → ℕ → X → Y} {rowOf : X → Option K}

omit [Fintype Par] in
theorem mpgMass_update
    (hupd : ∀ (Rs : Fin s → K) (Φ : Par) (j : Fin s) (r : K) (m : ℕ), m ≤ j.1 →
      fam (Function.update Rs j r) Φ m = fam Rs Φ m)
    (Rs : Fin s → K) (Φ : Par) (j : Fin s) (r : K)
    (c : Σ _ : List Req, X) (hc : c.1.length ≤ j.1) :
    mpgMass I ρ x fam (Function.update Rs j r) Φ c = mpgMass I ρ x fam Rs Φ c := by
  classical
  unfold mpgMass massN QuantumRuntime.indexMass QuantumRuntime.indexMassAt pComp
  refine tsum_congr fun i ↦ ?_
  refine pflat_queryWeight_congr I (D := QReg.of Unit) (σ₁ := SubState.basis ())
    (σ₂ := SubState.basis ())
    (s₁ := fun t : List Req ↦ (oracleQuery (fam (Function.update Rs j r) Φ t.length)).frame Unit)
    (s₂ := fun t : List Req ↦ (oracleQuery (fam Rs Φ t.length)).frame Unit)
    (rndCh (Function.update Rs j r)) (rndCh Rs) (fun p t ↦ p <+: t)
    (fun req t t' ↦ rndCh_step _ req t t') (fun req t t' ↦ rndCh_step _ req t t') c.1
    (fun req t ↦ ?_) (fun p hp ↦ ?_) (fun p hp σ ↦ ?_) s [] x _ i
  · by_cases ht : t.length = j.1
    · right
      have hlen : ¬ (t ++ [req]) <+: c.1 := fun h ↦ by
        have := h.length_le
        simp at this
        omega
      exact ⟨hlen, hlen⟩
    · left
      unfold rndCh
      rw [rndAt_update Rs j r ht]
  · have hle : p.length ≤ j.1 := hp.length_le.trans hc
    simp only [hupd Rs Φ j r _ hle]
  · have hne : p ≠ c.1 := fun h ↦ hp (h ▸ List.prefix_refl _)
    have : ∀ k : X, (⟨p, k⟩ : Σ _ : List Req, X) ≠ c := fun k h ↦ hne (by rw [← h])
    simp [this]

omit [Fintype Par] in
theorem mpg_diffMass_le
    (hne : ∀ (Rs : Fin s → K) (Φ : Par) (m : ℕ) (z : X),
      fam Rs Φ s z ≠ fam Rs Φ m z → ∃ j : Fin s, m ≤ j.1 ∧ rowOf z = some (Rs j))
    (Rs : Fin s → K) (Φ : Par) :
    diffMass I (fun _ ↦ fam Rs Φ s) (fun t : List Req ↦ fam Rs Φ t.length) (pComp x Rs)
        (joint ρ) ≤
      ∑ j : Fin s, ∑' c : Σ _ : List Req, X,
        if c.1.length ≤ j.1 then (if rowOf c.2 = some (Rs j) then mpgMass I ρ x fam Rs Φ c else 0)
        else 0 := by
  unfold diffMass
  rw [← Summable.tsum_finsetSum fun _ _ ↦ CompleteLattice.summable]
  refine tsum_le_tsum fun c ↦ ?_
  split_ifs with h
  · obtain ⟨j, hj, hR⟩ := hne Rs Φ _ _ h
    refine le_trans ?_ (Finset.single_le_sum (fun _ _ ↦ zero_le) (Finset.mem_univ j))
    simp only [hj, hR, ↓reduceIte]
    rfl
  · exact zero_le

theorem avg_mpg_diffMass_le
    (hupd : ∀ (Rs : Fin s → K) (Φ : Par) (j : Fin s) (r : K) (m : ℕ), m ≤ j.1 →
      fam (Function.update Rs j r) Φ m = fam Rs Φ m)
    (hne : ∀ (Rs : Fin s → K) (Φ : Par) (m : ℕ) (z : X),
      fam Rs Φ s z ≠ fam Rs Φ m z → ∃ j : Fin s, m ≤ j.1 ∧ rowOf z = some (Rs j))
    (hW : ∀ Rs : Fin s → K,
      IsWeightedBound (pComp x Rs) (fun t : List Req ↦ s - t.length) Wt) :
    (avg fun Rs : Fin s → K ↦ avg fun Φ : Par ↦
      diffMass I (fun _ ↦ fam Rs Φ s) (fun t : List Req ↦ fam Rs Φ t.length) (pComp x Rs)
        (joint ρ)) ≤ (Fintype.card K : ℝ≥0∞)⁻¹ * Wt := by
  refine (avg_mono fun Rs ↦ avg_mono fun Φ ↦ mpg_diffMass_le hne Rs Φ).trans ?_
  rw [avg_comm]
  refine avg_le fun Φ ↦ ?_
  rw [avg_finset_sum]
  have hj : ∀ j : Fin s, (avg fun Rs : Fin s → K ↦ ∑' c : Σ _ : List Req, X,
      if c.1.length ≤ j.1 then (if rowOf c.2 = some (Rs j) then mpgMass I ρ x fam Rs Φ c else 0)
      else 0) ≤
      (Fintype.card K : ℝ≥0∞)⁻¹ * avg fun Rs : Fin s → K ↦ ∑' c : Σ _ : List Req, X,
        if c.1.length ≤ j.1 then mpgMass I ρ x fam Rs Φ c else 0 := by
    intro j
    rw [avg_tsum, avg_tsum, ← ENNReal.tsum_mul_left]
    refine tsum_le_tsum fun c ↦ ?_
    by_cases hlen : c.1.length ≤ j.1
    · simp only [hlen, ↓reduceIte]
      rcases hr : rowOf c.2 with _ | r
      · simp only [reduceCtorEq, ↓reduceIte]
        exact (avg_le (c := 0) fun _ ↦ le_rfl).trans zero_le
      · have e : (fun Rs : Fin s → K ↦ if some r = some (Rs j) then mpgMass I ρ x fam Rs Φ c
            else 0) = fun Rs ↦ if Rs j = r then mpgMass I ρ x fam Rs Φ c else 0 := by
          funext Rs
          simp only [Option.some.injEq, eq_comm]
        rw [e]
        exact (avg_coord_eq j r (fun Rs ↦ mpgMass I ρ x fam Rs Φ c)
          fun Rs r ↦ mpgMass_update hupd Rs Φ j r c hlen).le
    · simp only [hlen, ↓reduceIte]
      exact (avg_le (c := 0) fun _ ↦ le_rfl).trans zero_le
  refine (Finset.sum_le_sum fun j _ ↦ hj j).trans ?_
  rw [← Finset.mul_sum, ← avg_finset_sum]
  refine mul_le_mul' le_rfl (avg_le fun Rs ↦ ?_)
  rw [← Summable.tsum_finsetSum fun _ _ ↦ CompleteLattice.summable]
  simp only [sum_fin_ite_le]
  exact (tsum_weighted_massN_le I _ (joint_posSemidef ρ) _ (hW Rs)).trans
    ((mul_le_mul' le_rfl (ofReal_trace_joint_le_one ρ)).trans (mul_one _).le)

/-- **Reprogramming step, port functions on an arbitrary domain.** -/
theorem mpg_sqrt_le
    (hupd : ∀ (Rs : Fin s → K) (Φ : Par) (j : Fin s) (r : K) (m : ℕ), m ≤ j.1 →
      fam (Function.update Rs j r) Φ m = fam Rs Φ m)
    (hne : ∀ (Rs : Fin s → K) (Φ : Par) (m : ℕ) (z : X),
      fam Rs Φ s z ≠ fam Rs Φ m z → ∃ j : Fin s, m ≤ j.1 ∧ rowOf z = some (Rs j))
    (hx : IAdv.IsQueryBound s x (fun _ ↦ q))
    (hW : ∀ Rs : Fin s → K,
      IsWeightedBound (pComp x Rs) (fun t : List Req ↦ s - t.length) Wt)
    (win : (Fin s → K) → Par → (Σ u, Out u × List Req) → Prop) :
    (avg fun Rs : Fin s → K ↦ avg fun Φ : Par ↦
        leafProb (nRuntime fun _ ↦ fam Rs Φ s) I (pComp x Rs) (joint ρ) (win Rs Φ)) ^
          (2⁻¹ : ℝ) ≤
      (avg fun Rs : Fin s → K ↦ avg fun Φ : Par ↦
        leafProb (nRuntime fun t : List Req ↦ fam Rs Φ t.length) I (pComp x Rs) (joint ρ)
          (win Rs Φ)) ^ (2⁻¹ : ℝ) +
        (4 * (q : ℝ≥0∞) * ((Fintype.card K : ℝ≥0∞)⁻¹ * Wt)) ^ (2⁻¹ : ℝ) := by
  refine (sqrt_avg_le _ _ _ fun Rs ↦ sqrt_avg_le _ _ _ fun Φ ↦
    (nRuntime_sqrt_le I (fun _ ↦ fam Rs Φ s) (fun t : List Req ↦ fam Rs Φ t.length)
      (joint_posSemidef ρ) (pComp_isTotalBound hx Rs) (win Rs Φ)).1).trans
    (add_le_add le_rfl (sqrt_le_sqrt ?_))
  simp only [avg_mul_left]
  exact mul_le_mul' le_rfl (avg_mpg_diffMass_le hupd hne hW)

end Generic

/-! ## The game over the port oracle -/

section GameP

variable {K Xm D X Y Req : Type} [Fintype K] [DecidableEq K] [Nonempty K] [Fintype Xm]
  [DecidableEq Xm] [Fintype D] [DecidableEq D] [Nonempty D] [Fintype X] [DecidableEq X]
  [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
  {L : LocalSig.{u, v}} {Out : QReg → Type w} {A : QReg}
  (ι : K × Xm → X) (φ : (K × Xm → D) → X → Y) (tg : Req → Xm) (oc : ∀ u, Out u → K × Xm)

/-- A leaf of the run, read as a candidate and a transcript of target inputs. -/
def lv (p : Σ u, Out u × List Req) : Σ _ : QReg, (K × Xm) × List Xm :=
  ⟨p.1, (oc p.1 p.2.1, p.2.2.map tg)⟩

variable (I : L.Interp) (ρ : SubState A) (s : ℕ)
  (x : IAdv L (qromSpec X Y) Req K Out s A)
  (Cov : Finset D → D → Prop) [∀ S, DecidablePred (Cov S)]

/-- **The adaptive ITSR experiment over the port oracle `φ H`.** -/
noncomputable def itsrPExp : ℝ≥0∞ :=
  avg fun Rs : Fin s → K ↦ avg fun H : K × Xm → D ↦
    qprob I (φ H) (IAdv.flat (rndCh Rs) (IAdv.stop (L := L) (spec := qromSpec X Y)) s [] x) ρ
      (fun p ↦ itsrAWin Cov Rs H (lv tg oc p))

variable {ι φ tg oc I ρ s x Cov} {q Wt : ℕ}

/-- The row of a port point: the randomizer of its preimage under `ι`, if any. -/
noncomputable def rowOf (ι : K × Xm → X) (z : X) : Option K := by
  classical
  exact if h : ∃ w, ι w = z then some (Classical.choose h).1 else none

theorem rowOf_apply (hι : Function.Injective ι) (w : K × Xm) : rowOf ι (ι w) = some w.1 := by
  classical
  unfold rowOf
  split_ifs with h'
  · rw [hι (Classical.choose_spec h')]
  · exact absurd ⟨w, rfl⟩ h'

omit [∀ S, DecidablePred (Cov S)] in
theorem itsrPExp_eq_N
    (win : (Fin s → K) → (K × Xm → D) → (Σ u, Out u × List Req) → Prop) :
    (avg fun Rs : Fin s → K ↦ avg fun H : K × Xm → D ↦
      qprob I (φ H) (IAdv.flat (rndCh Rs) (IAdv.stop (L := L) (spec := qromSpec X Y)) s [] x) ρ
        (win Rs H)) =
      avg fun Rs : Fin s → K ↦ avg fun Ψ : (K × Xm) × Option (Fin s) → D ↦
        leafProb (nRuntime fun _ ↦ φ (nFn Rs Ψ s)) I (pComp x Rs) (joint ρ)
          (win Rs (nFn Rs Ψ s)) := by
  refine avg_congr fun Rs ↦ ?_
  simp only [qprob_flat_eq]
  have hinj : Function.Injective
      (fun z : K × Xm ↦ ((z, lastIdx Rs s z.1) : (K × Xm) × Option (Fin s))) :=
    fun a b h ↦ congrArg Prod.fst h
  exact (sum_comp_injective' _ hinj
    (fun H : K × Xm → D ↦ leafProb (nRuntime fun _ ↦ φ H) I (pComp x Rs) (joint ρ)
      (win Rs H))).symm

omit [∀ S, DecidablePred (Cov S)] in
/-- **Lazy sampling of the target digests, port oracle.** -/
theorem itsrP_eq_B (Rs : Fin s → K) :
    (avg fun Ψ : (K × Xm) × Option (Fin s) → D ↦
      leafProb (nRuntime fun t : List Req ↦ φ (nFn Rs Ψ t.length)) I (pComp x Rs) (joint ρ)
        (fun p ↦ itsrAWin Cov Rs (nFn Rs Ψ s) (lv tg oc p))) =
      avg fun Ψ : (K × Xm) × Option (Fin s) → D ↦ avg fun d : Fin s → D ↦
        leafProb (nRuntime fun t : List Req ↦ φ (nBFn Rs d Ψ (t.map tg))) I (pComp x Rs)
          (joint ρ)
          (fun p ↦ itsrAWin Cov Rs (nFn Rs (owN Rs (p.2.2.map tg) d Ψ) s) (lv tg oc p)) := by
  unfold leafProb
  simp only [avg_tsum]
  refine tsum_congr fun p ↦ ?_
  obtain ⟨u, o, t⟩ := p
  refine (avg_involutive _ (swapN_involutive Rs (t.map tg))
    (fun Ψ : (K × Xm) × Option (Fin s) → D ↦
      ENNReal.ofReal ((((nRuntime fun t : List Req ↦ φ (nFn Rs Ψ t.length)).run I
        (pComp x Rs)).branch ⟨u, (o, t)⟩) (joint ρ)).trace.re *
        ind (itsrAWin Cov Rs (nFn Rs Ψ s) (lv tg oc ⟨u, (o, t)⟩)))).symm.trans ?_
  refine avg_congr fun Ψ ↦ avg_congr fun d ↦ ?_
  have hbr : ((nRuntime fun t' : List Req ↦
      φ (nFn Rs (owN Rs (t.map tg) d Ψ) t'.length)).run I (pComp x Rs)).branch ⟨u, (o, t)⟩ =
      ((nRuntime fun t' : List Req ↦ φ (nBFn Rs d Ψ (t'.map tg))).run I
        (pComp x Rs)).branch ⟨u, (o, t)⟩ :=
    pflat_branch_congr I (D := QReg.of Unit) (σ₁ := SubState.basis ())
      (σ₂ := SubState.basis ())
      (s₁ := fun t' : List Req ↦
        (oracleQuery (φ (nFn Rs (owN Rs (t.map tg) d Ψ) t'.length))).frame Unit)
      (s₂ := fun t' : List Req ↦ (oracleQuery (φ (nBFn Rs d Ψ (t'.map tg)))).frame Unit)
      (rndCh Rs) (fun p t ↦ p <+: t) (fun _ ↦ List.prefix_refl _)
      (fun req t t' ↦ rndCh_step _ req t t') t
      (fun t' ht' ↦ by
        have h := nFn_owN_prefix Rs d Ψ (ht'.map tg)
        rw [List.length_map] at h
        rw [h]) s [] x u o
  show ENNReal.ofReal ((((nRuntime fun t' : List Req ↦
      φ (nFn Rs (owN Rs (t.map tg) d Ψ) t'.length)).run I
      (pComp x Rs)).branch ⟨u, (o, t)⟩) (joint ρ)).trace.re *
      ind (itsrAWin Cov Rs (nFn Rs (owN Rs (t.map tg) d Ψ) s) (lv tg oc ⟨u, (o, t)⟩)) = _
  rw [hbr]

/-- **Search in the lazily-sampled world, port oracle.** -/
theorem itsrP_NB_le (hι : Function.Injective ι)
    (hφ : ∀ (H G : K × Xm → D) (z : X), φ H z ≠ φ G z → ∃ w, ι w = z ∧ H w ≠ G w)
    (hmono : ∀ (S S' : Finset D) (u : D), S ⊆ S' → Cov S u → Cov S' u)
    (hx : IAdv.IsQueryBound s x (fun _ ↦ q)) (Rs : Fin s → K) (d : Fin s → D) :
    (avg fun Ψ : (K × Xm) × Option (Fin s) → D ↦
      leafProb (nRuntime fun t : List Req ↦ φ (nBFn Rs d Ψ (t.map tg))) I (pComp x Rs)
        (joint ρ)
        (fun p ↦ itsrAWin Cov Rs (nFn Rs (owN Rs (p.2.2.map tg) d Ψ) s) (lv tg oc p))) ≤
      (2 * (q : ℝ≥0∞) + 1) ^ 2 *
        (((covered Cov (univ.image d)).card : ℝ≥0∞) * (Fintype.card D : ℝ≥0∞)⁻¹) := by
  classical
  set C : Finset D := covered Cov (univ.image d) with hC
  set G : ((K × Xm) × Option (Fin s) → D) → List Req → X → Y :=
    fun v t ↦ φ (nBFn Rs d v (t.map tg)) with hG
  set F : ((K × Xm) × Option (Fin s) → D) → ℝ≥0∞ := fun Ψ ↦
    leafProb (nRuntime (G Ψ)) I (pComp x Rs) (joint ρ)
      (fun p ↦ itsrAWin Cov Rs (nFn Rs (owN Rs (p.2.2.map tg) d Ψ) s) (lv tg oc p)) with hF
  have hF1 : ∀ Ψ, F Ψ ≤ 1 := fun Ψ ↦
    (leafProb_le _ (joint_posSemidef ρ) _).trans (ofReal_trace_joint_le_one ρ)
  have he : Function.Injective
      (fun c : Σ _ : List Req, K × Xm ↦ (⟨c.1, ι c.2⟩ : Σ _ : List Req, X)) := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    simp only [Sigma.mk.inj_iff, heq_eq_eq] at h
    obtain ⟨rfl, h2⟩ := h
    rw [hι h2]
  by_cases hU : Cᶜ.Nonempty
  · set U : {U : Finset D // U.Nonempty} := ⟨Cᶜ, hU⟩ with hUdef
    set cXD : ℝ≥0∞ := (Fintype.card ((K × Xm) × Option (Fin s) → D) : ℝ≥0∞) with hcXD
    set cXR : ℝ≥0∞ := (Fintype.card ((K × Xm) × Option (Fin s) → Res D) : ℝ≥0∞) with hcXR
    have iXD : cXD * cXD⁻¹ = 1 := natCast_mul_inv_cancel Fintype.card_ne_zero
    have iXR : cXR * cXR⁻¹ = 1 := natCast_mul_inv_cancel Fintype.card_ne_zero
    set κ : ℝ≥0∞ := cXD⁻¹ * cXR⁻¹ with hκ
    have hw : ∑ _τ : (K × Xm) × Option (Fin s) → D × Res D, κ ≤ 1 := by
      have := sum_fst_comp (X := (K × Xm) × Option (Fin s)) (A := D) (B := Res D) (fun _ ↦ κ)
      simp only [this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      calc cXR * (cXD * κ) = (cXD * cXD⁻¹) * (cXR * cXR⁻¹) := by rw [hκ]; ring
        _ ≤ 1 := by rw [iXD, iXR, mul_one]
    have hH : Hidden (Ω := (K × Xm) × Option (Fin s) → D × Res D) (fun _ ↦ κ)
        (fun τ k ↦ resU U (τ k)) (fun τ ↦ univ.filter fun k ↦ (τ k).1 ∉ U.1) (pMark U) := by
      intro k φ'
      have h := hidden_itsr (X := (K × Xm) × Option (Fin s))
        (∅ : Finset ((K × Xm) × Option (Fin s)))
        (fun _ ↦ Classical.arbitrary D) U κ k φ'
      simpa using h
    let outB : (Σ u, Out u × List Req) → (K × Xm) × Option (Fin s) := fun p ↦
      ((lv tg oc p).2.1, lastIdx Rs s (lv tg oc p).2.1.1)
    let bs : List Req → K × Xm → Option (Fin s) := fun t z ↦ lastIdx Rs t.length z.1
    let pr : ((K × Xm) × Option (Fin s) → D) → (K × Xm) × Option (Fin s) → ℝ≥0∞ := fun v y ↦
      leafProb (nRuntime (G v)) I (pComp x Rs) (joint ρ) (fun p ↦ outB p = y)
    let mm : ((K × Xm) × Option (Fin s) → D) → (K × Xm) × Option (Fin s) → ℝ≥0∞ := fun v ↦
      selMassG bs (fun c : Σ _ : List Req, K × Xm ↦
        massN I (G v) (pComp x Rs) (joint ρ) ⟨c.1, ι c.2⟩)
    have hpr : ∀ v, ∑ k, pr v k ≤ 1 := fun v ↦
      (sum_leafProb_eq_le (R := nRuntime (G v)) (I := I) (pComp x Rs)
        (joint_posSemidef ρ) outB).trans (ofReal_trace_joint_le_one ρ)
    have hmm : ∀ v, ∑ k, mm v k ≤ q := fun v ↦ by
      have h := sum_selMassG bs (fun c : Σ _ : List Req, K × Xm ↦
        massN I (G v) (pComp x Rs) (joint ρ) ⟨c.1, ι c.2⟩) univ
      simp only [Finset.mem_univ, ite_true] at h
      rw [h]
      refine (tsum_comp_le_tsum_of_injective he
        (fun c ↦ massN I (G v) (pComp x Rs) (joint ρ) c)).trans ?_
      exact (tsum_massN_le I _ (joint_posSemidef ρ) (pComp_isTotalBound hx Rs)).trans
        ((mul_le_mul' le_rfl (ofReal_trace_joint_le_one ρ)).trans (mul_one _).le)
    have hs := hH.search_le' hw q (fun τ ↦ F fun k ↦ (τ k).1) pr mm hpr hmm (by
      intro τ
      set Φ : (K × Xm) × Option (Fin s) → D := fun k ↦ (τ k).1 with hΦ
      set Φh : (K × Xm) × Option (Fin s) → D := fun k ↦ resU U (τ k) with hΦh
      set Sτ : Finset ((K × Xm) × Option (Fin s)) :=
        univ.filter fun k ↦ (τ k).1 ∉ U.1 with hSτ
      have h1 : F Φ ≤ leafProb (nRuntime (G Φ)) I (pComp x Rs) (joint ρ)
          (fun p ↦ outB p ∈ Sτ) :=
        leafProb_mono _ _ fun p hp ↦ by
          have hc := itsrAWin_owN Cov hmono Rs d Φ (lv tg oc p) hp
          refine Finset.mem_filter.2 ⟨Finset.mem_univ _, fun hin ↦ ?_⟩
          exact (Finset.mem_compl.1 hin) hc
      have h2 := (nRuntime_sqrt_le I (G Φ) (G Φh)
        (joint_posSemidef ρ) (pComp_isTotalBound hx Rs) (fun p ↦ outB p ∈ Sτ)).1
      have h3 : leafProb (nRuntime (G Φh)) I (pComp x Rs) (joint ρ)
          (fun p ↦ outB p ∈ Sτ) ≤ ∑ k ∈ Sτ, pr Φh k :=
        leafProb_mem_le_sum _ _ outB Sτ
      have h4 : diffMass I (G Φ) (G Φh) (pComp x Rs) (joint ρ) ≤ ∑ k ∈ Sτ, mm Φh k := by
        rw [sum_selMassG]
        unfold diffMass
        set f : (Σ _ : List Req, X) → ℝ≥0∞ := fun c ↦
          if G Φ c.1 c.2 ≠ G Φh c.1 c.2 then massN I (G Φh) (pComp x Rs) (joint ρ) c else 0
          with hf
        have hsupp : Function.support f ⊆ Set.range
            (fun c : Σ _ : List Req, K × Xm ↦ (⟨c.1, ι c.2⟩ : Σ _ : List Req, X)) := by
          intro c hc
          have hne : G Φ c.1 c.2 ≠ G Φh c.1 c.2 := by
            by_contra h
            exact hc (by simp only [hf, h, ne_eq, not_true_eq_false, ↓reduceIte])
          obtain ⟨w, hw, _⟩ := hφ _ _ _ hne
          exact ⟨⟨c.1, w⟩, by simp only [hw]⟩
        change ∑' c, f c ≤ _
        rw [← he.tsum_eq hsupp]
        refine tsum_le_tsum fun c ↦ ?_
        show (if G Φ c.1 (ι c.2) ≠ G Φh c.1 (ι c.2) then
            massN I (G Φh) (pComp x Rs) (joint ρ) ⟨c.1, ι c.2⟩ else 0) ≤ _
        by_cases hne : G Φ c.1 (ι c.2) ≠ G Φh c.1 (ι c.2)
        · obtain ⟨w, hw, hw'⟩ := hφ _ _ _ hne
          obtain rfl := hι hw
          have hin : (c.2, bs c.1 c.2) ∈ Sτ := by
            refine Finset.mem_filter.2 ⟨Finset.mem_univ _, fun hin ↦ nBFn_ne hw' ?_⟩
            simp only [hΦ, hΦh, resU, List.length_map]
            rw [ite_eq_left hin]
          rw [ite_eq_left hne, ite_eq_left hin]
        · rw [ite_eq_right hne]
          exact zero_le
      exact (sqrt_le_sqrt h1).trans (h2.trans (add_le_add (sqrt_le_sqrt h3)
        (sqrt_le_sqrt (mul_le_mul' le_rfl h4)))))
    have hp : pMark U = (C.card : ℝ≥0∞) * (Fintype.card D : ℝ≥0∞)⁻¹ := by
      simp [pMark, hUdef]
    rw [hp] at hs
    refine le_trans (le_of_eq ?_) hs
    have e' := sum_fst_comp (X := (K × Xm) × Option (Fin s)) (A := D) (B := Res D)
      (fun Φ ↦ κ * F Φ)
    refine Eq.trans ?_ e'.symm
    unfold avg
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun Φ _ ↦ ?_
    calc cXD⁻¹ * F Φ = (cXR * cXR⁻¹) * (cXD⁻¹ * F Φ) := by rw [iXR, one_mul]
      _ = _ := by rw [hκ]; ring
  · have hCu : C = univ := by
      rw [Finset.not_nonempty_iff_eq_empty] at hU
      exact (Finset.compl_eq_empty_iff _).1 hU
    have h1 : (1 : ℝ≥0∞) ≤ (2 * (q : ℝ≥0∞) + 1) ^ 2 *
        ((C.card : ℝ≥0∞) * (Fintype.card D : ℝ≥0∞)⁻¹) := by
      rw [hCu, Finset.card_univ, natCast_mul_inv_cancel Fintype.card_ne_zero, mul_one]
      exact one_le_two_mul_add_one_sq q
    exact (avg_le hF1).trans h1

theorem itsrP_hyb_le (hι : Function.Injective ι)
    (hφ : ∀ (H G : K × Xm → D) (z : X), φ H z ≠ φ G z → ∃ w, ι w = z ∧ H w ≠ G w)
    (hmono : ∀ (S S' : Finset D) (u : D), S ⊆ S' → Cov S u → Cov S' u)
    (hx : IAdv.IsQueryBound s x (fun _ ↦ q)) :
    (avg fun Rs : Fin s → K ↦ avg fun Ψ : (K × Xm) × Option (Fin s) → D ↦
      leafProb (nRuntime fun t : List Req ↦ φ (nFn Rs Ψ t.length)) I (pComp x Rs) (joint ρ)
        (fun p ↦ itsrAWin Cov Rs (nFn Rs Ψ s) (lv tg oc p))) ≤
      (2 * (q : ℝ≥0∞) + 1) ^ 2 * coverProb (Fin s) Cov := by
  refine avg_le fun Rs ↦ ?_
  rw [itsrP_eq_B Rs, avg_comm]
  refine (avg_mono fun d ↦ itsrP_NB_le hι hφ hmono hx Rs d).trans ?_
  rw [avg_mul_left]
  rfl

theorem itsrP_adaptive_weighted_sqrt_le (hι : Function.Injective ι)
    (hφ : ∀ (H G : K × Xm → D) (z : X), φ H z ≠ φ G z → ∃ w, ι w = z ∧ H w ≠ G w)
    (hmono : ∀ (S S' : Finset D) (u : D), S ⊆ S' → Cov S u → Cov S' u)
    (hx : IAdv.IsQueryBound s x (fun _ ↦ q))
    (hW : ∀ Rs : Fin s → K,
      IsWeightedBound (pComp x Rs) (fun t : List Req ↦ s - t.length) Wt) :
    itsrPExp φ tg oc I ρ s x Cov ^ (2⁻¹ : ℝ) ≤
      ((2 * (q : ℝ≥0∞) + 1) ^ 2 * coverProb (Fin s) Cov) ^ (2⁻¹ : ℝ) +
        (4 * (q : ℝ≥0∞) * ((Fintype.card K : ℝ≥0∞)⁻¹ * Wt)) ^ (2⁻¹ : ℝ) := by
  unfold itsrPExp
  rw [itsrPExp_eq_N]
  refine (mpg_sqrt_le (fam := fun Rs (Ψ : (K × Xm) × Option (Fin s) → D) m ↦ φ (nFn Rs Ψ m))
    (rowOf := rowOf ι) (fun Rs Ψ j r m hm ↦ ?_) (fun Rs Ψ m z h ↦ ?_) hx hW
    (fun Rs Ψ p ↦ itsrAWin Cov Rs (nFn Rs Ψ s) (lv tg oc p))).trans
    (add_le_add (sqrt_le_sqrt (itsrP_hyb_le hι hφ hmono hx)) le_rfl)
  · have : nFn (Function.update Rs j r) Ψ m = nFn Rs Ψ m := by
      funext z
      show Ψ (z, lastIdx (Function.update Rs j r) m z.1) = Ψ (z, lastIdx Rs m z.1)
      rw [lastIdx_update Rs j z.1 r hm]
    simp only [this]
  · obtain ⟨w, rfl, hw⟩ := hφ _ _ _ h
    rw [rowOf_apply hι]
    obtain ⟨j, hj, hR⟩ := lastIdx_ne (Rs := Rs) (m := m) (r := w.1) fun heq ↦ hw (by
      show Ψ (w, lastIdx Rs s w.1) = Ψ (w, lastIdx Rs m w.1)
      rw [heq])
    exact ⟨j, hj, by rw [hR]⟩

/-- **Adaptive ITSR over a port oracle embedding the random function, general regime, no
collision term.**  `Pr[win] ≤ (√((2q+1)² · coverProb (Fin s) Cov) + 2 q √(s/|K|))²`. -/
theorem itsrP_adaptive_le (hι : Function.Injective ι)
    (hφ : ∀ (H G : K × Xm → D) (z : X), φ H z ≠ φ G z → ∃ w, ι w = z ∧ H w ≠ G w)
    (hmono : ∀ (S S' : Finset D) (u : D), S ⊆ S' → Cov S u → Cov S' u)
    (hx : IAdv.IsQueryBound s x (fun _ ↦ q)) :
    itsrPExp φ tg oc I ρ s x Cov ≤
      (((2 * (q : ℝ≥0∞) + 1) ^ 2 * coverProb (Fin s) Cov) ^ (2⁻¹ : ℝ) +
        2 * q * ((s : ℝ≥0∞) * (Fintype.card K : ℝ≥0∞)⁻¹) ^ (2⁻¹ : ℝ)) ^ 2 := by
  have hW : ∀ Rs : Fin s → K,
      IsWeightedBound (pComp x Rs) (fun t : List Req ↦ s - t.length) (s * q) := fun Rs ↦
    isWeightedBound_of_isTotalBound (fun _ ↦ Nat.sub_le _ _) (pComp_isTotalBound hx Rs)
  have h := itsrP_adaptive_weighted_sqrt_le (I := I) (ρ := ρ) (tg := tg) (oc := oc) hι hφ hmono hx hW
  have e : 4 * (q : ℝ≥0∞) * ((Fintype.card K : ℝ≥0∞)⁻¹ * ((s * q : ℕ) : ℝ≥0∞)) =
      4 * q * ((s : ℝ≥0∞) * (Fintype.card K : ℝ≥0∞)⁻¹ * q) := by
    push_cast
    ring
  rw [e, sqrt_four_mul] at h
  calc itsrPExp φ tg oc I ρ s x Cov = (itsrPExp φ tg oc I ρ s x Cov ^ (2⁻¹ : ℝ)) ^ 2 :=
        (sq_sqrt _).symm
    _ ≤ _ := pow_le_pow_left' h 2

end GameP

end Pull
end PQ.QROM

#print axioms PQ.QROM.Pull.mpg_sqrt_le
#print axioms PQ.QROM.Pull.itsrP_eq_B
#print axioms PQ.QROM.Pull.itsrP_NB_le
#print axioms PQ.QROM.Pull.itsrP_adaptive_le
