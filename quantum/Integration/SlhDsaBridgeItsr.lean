import Integration.SlhDsaBridgeMsg
import HashSig.SLHDSA.Security.DigestTransport

/-!
# The ITSR term of the composed QROM theorem (game side)

NOT part of the default target; compiled like the other `Integration/*.lean` files.

`itsr_term`: under ONE named hypothesis `hModel` (the machine side, see below and
`quantum/HANDOFF-qprf.md`, "Part C — hypothesis consumed"),

  `avΩ c (fun ω ↦ qItsrAdvantage (itsrProblem Link.vp (primsΩ ω)) (qbItsrL (B ω)) (B ω).ρ₀)
     ≤ epsItsr Link.vp.params q' qs`,   `B = internalΩ c optRand₀ pkSeedDist₀ encΩ F`,

i.e. the hypothesis `hitsr` of `composed_of_linear_eps` (the same machine `qbItsrL` serves the
SUF and the EUF headline).  Not through `ItsrValue`/`MixLE`.

`hModel` asks, for each world `ω₀`, for ONE Part-2 interactive adversary over the in-cap `H_msg`
table (`IAdv … (qromSpec (BN × ItsrXm c) BM) (ItsrXm c) BN …`, at most `qs` requests, at most
`q'` oracle calls) whose presampled-randomizer winning probability with the index-cover relation
`idxCov` dominates the Part-1 ITSR advantage at `ω₀.withHmsg (hmsgTable c Hf)`, for every table
`Hf`.  It is NOT proved here.

Proved here:
* `coverProb_le_of_fiber` (generic): a decoding with equal fibers that maps the cover relation
  into another one does not increase the cover probability (uniform pushforward of `ι`-tuples,
  `avg_comp_fiber`).
* `coverProb_idxCov_le`: the cover probability of `itsrProblem`'s index relation on uniform
  `Bytes m` digests is at most the FORS cover probability on `Fin (2^h) × (Fin k → Fin (2^a))`
  (VCVio's `SLHDSA.DigestTransport.coveringDigest`, `card_fiber_coveringDigest`: the uniform
  pushforward through `splitDigest`; `match_of_mem_idxOf`).
* `avΩ_resample_hmsg`: resampling the `H_msg` component of the world.
* `itsr_bound_le`: `itsr4_adaptive_le`'s right-hand side with `Cov := idxCov`, `|K| = 2^128` is at
  most `epsItsr Link.vp.params q' qs` (`coverProb_fors`).
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal PQ.Interactive PQ.QROM Quantum
open scoped Kronecker ComplexOrder
set_option linter.unusedSectionVars false

namespace Reduction.QItsr
open Finset
set_option linter.unusedSectionVars false

variable {ι D D' : Type} [Fintype ι] [DecidableEq ι] [Fintype D] [DecidableEq D] [Fintype D']
  [DecidableEq D']

theorem card_fun_fiber (π : D → D') (N : ℕ) (hfib : ∀ z, (univ.filter fun d ↦ π d = z).card = N)
    (b : ι → D') : (univ.filter fun a : ι → D ↦ π ∘ a = b).card = N ^ Fintype.card ι := by
  classical
  have e : {a : ι → D // π ∘ a = b} ≃ ((i : ι) → {u : D // π u = b i}) :=
    (Equiv.subtypeEquivRight (q := fun a : ι → D ↦ ∀ i, π (a i) = b i) fun a ↦ funext_iff).trans
      (Equiv.subtypePiEquivPi (p := fun i u ↦ π u = b i))
  rw [← Fintype.card_subtype, Fintype.card_congr e, Fintype.card_pi]
  simp only [Fintype.card_subtype, hfib, prod_const, card_univ]

theorem sum_comp_fiber (π : D → D') (N : ℕ) (hN : 0 < N)
    (hfib : ∀ z, (univ.filter fun d ↦ π d = z).card = N) (g : (ι → D') → ℝ≥0∞) :
    ∑ a : ι → D, g (π ∘ a) = ∑ b : ι → D', (N ^ Fintype.card ι : ℕ) * g b := by
  classical
  rw [Finset.sum_comp (s := univ) (g := fun a : ι → D ↦ π ∘ a)]
  have himg : (univ.image fun a : ι → D ↦ π ∘ a) = univ := by
    refine eq_univ_of_forall fun b ↦ ?_
    have h := card_fun_fiber π N hfib b
    have hpos : 0 < (univ.filter fun a : ι → D ↦ π ∘ a = b).card := by
      rw [h]; exact pow_pos hN _
    obtain ⟨a, ha⟩ := card_pos.1 hpos
    exact mem_image.2 ⟨a, mem_univ _, (mem_filter.1 ha).2⟩
  rw [himg]
  refine sum_congr rfl fun b _ ↦ ?_
  rw [card_fun_fiber π N hfib b, nsmul_eq_mul]

theorem avg_comp_fiber (π : D → D') (N : ℕ) (hN : 0 < N)
    (hfib : ∀ z, (univ.filter fun d ↦ π d = z).card = N) (g : (ι → D') → ℝ≥0∞) :
    ∑ a : ι → D, (Fintype.card (ι → D) : ℝ≥0∞)⁻¹ * g (π ∘ a) =
      ∑ b : ι → D', (Fintype.card (ι → D') : ℝ≥0∞)⁻¹ * g b := by
  have hc : (Fintype.card (ι → D) : ℝ≥0∞) =
      (N ^ Fintype.card ι : ℕ) * (Fintype.card (ι → D') : ℝ≥0∞) := by
    have h := sum_comp_fiber (ι := ι) π N hN hfib (fun _ ↦ 1)
    simp only [sum_const, card_univ, nsmul_eq_mul, mul_one] at h
    rw [h, mul_comm]
  rw [← mul_sum, ← mul_sum, sum_comp_fiber π N hN hfib, ← mul_sum, hc,
    ENNReal.mul_inv (Or.inr (natCast_ne_top _)) (Or.inl (natCast_ne_top _))]
  have hN' : ((N ^ Fintype.card ι : ℕ) : ℝ≥0∞) ≠ 0 := by exact_mod_cast (pow_pos hN _).ne'
  calc ((N ^ Fintype.card ι : ℕ) : ℝ≥0∞)⁻¹ * (Fintype.card (ι → D') : ℝ≥0∞)⁻¹ *
        (((N ^ Fintype.card ι : ℕ) : ℝ≥0∞) * ∑ b, g b)
      = (((N ^ Fintype.card ι : ℕ) : ℝ≥0∞)⁻¹ * ((N ^ Fintype.card ι : ℕ) : ℝ≥0∞)) *
          ((Fintype.card (ι → D') : ℝ≥0∞)⁻¹ * ∑ b, g b) := by ring
    _ = _ := by rw [ENNReal.inv_mul_cancel hN' (natCast_ne_top _), one_mul]

variable [Nonempty D']

theorem coverProb_le_of_fiber (π : D → D') (N : ℕ) (hN : 0 < N)
    (hfib : ∀ z, (univ.filter fun d ↦ π d = z).card = N)
    (Cov : Finset D → D → Prop) [∀ S, DecidablePred (Cov S)]
    (Cov' : Finset D' → D' → Prop) [∀ S, DecidablePred (Cov' S)]
    (hcov : ∀ S u, Cov S u → Cov' (S.image π) (π u)) :
    coverProb ι Cov ≤ coverProb ι Cov' := by
  classical
  have hD : (Fintype.card D : ℝ≥0∞) = N * Fintype.card D' := by
    have h := Fintype.card_congr (Equiv.sigmaFiberEquiv π).symm
    rw [Fintype.card_sigma] at h
    simp only [Fintype.card_subtype, hfib, sum_const, card_univ, smul_eq_mul] at h
    rw [h]; push_cast; ring
  have hpt : ∀ d : ι → D, ((covered Cov (univ.image d)).card : ℝ≥0∞) * (Fintype.card D : ℝ≥0∞)⁻¹ ≤
      ((covered Cov' (univ.image (π ∘ d))).card : ℝ≥0∞) * (Fintype.card D' : ℝ≥0∞)⁻¹ := by
    intro d
    have hsub : covered Cov (univ.image d) ⊆
        univ.filter fun u ↦ π u ∈ covered Cov' (univ.image (π ∘ d)) := by
      intro u hu
      simp only [covered, mem_filter, mem_univ, true_and] at hu ⊢
      have := hcov _ u hu
      rwa [image_image] at this
    have hcard : (univ.filter fun u ↦ π u ∈ covered Cov' (univ.image (π ∘ d))).card =
        N * (covered Cov' (univ.image (π ∘ d))).card := by
      rw [card_eq_sum_card_fiberwise (s := univ.filter fun u ↦ π u ∈ covered Cov' (univ.image (π ∘ d)))
        (f := π) (t := covered Cov' (univ.image (π ∘ d))) (fun u hu ↦ (mem_filter.1 hu).2)]
      have : ∀ z ∈ covered Cov' (univ.image (π ∘ d)),
          ((univ.filter fun u ↦ π u ∈ covered Cov' (univ.image (π ∘ d))).filter
            fun u ↦ π u = z).card = N := by
        intro z hz
        rw [← hfib z]
        congr 1
        ext u
        simp only [mem_filter, mem_univ, true_and, and_iff_right_iff_imp]
        rintro rfl; exact hz
      rw [sum_congr rfl this, sum_const, smul_eq_mul, mul_comm]
    calc ((covered Cov (univ.image d)).card : ℝ≥0∞) * (Fintype.card D : ℝ≥0∞)⁻¹
        ≤ (N * (covered Cov' (univ.image (π ∘ d))).card : ℕ) * (Fintype.card D : ℝ≥0∞)⁻¹ := by
          gcongr
          rw [← hcard]; exact_mod_cast card_le_card hsub
      _ = _ := by
          rw [hD]; push_cast
          rw [ENNReal.mul_inv (Or.inr (natCast_ne_top _)) (Or.inl (natCast_ne_top _)),
            mul_comm (N : ℝ≥0∞), mul_assoc, ← mul_assoc (N : ℝ≥0∞),
            ENNReal.mul_inv_cancel (by exact_mod_cast hN.ne') (natCast_ne_top _), one_mul]
  unfold coverProb
  calc _ ≤ ∑ d : ι → D, (Fintype.card (ι → D) : ℝ≥0∞)⁻¹ *
        (((covered Cov' (univ.image (π ∘ d))).card : ℝ≥0∞) * (Fintype.card D' : ℝ≥0∞)⁻¹) :=
        sum_le_sum fun d _ ↦ mul_le_mul' le_rfl (hpt d)
    _ = _ := avg_comp_fiber π N hN hfib
        (fun b ↦ ((covered Cov' (univ.image b)).card : ℝ≥0∞) * (Fintype.card D' : ℝ≥0∞)⁻¹)

open SLHDSA.DigestTransport

/-- `H_msg` digests. -/
abbrev BM : Type := Bytes Link.vp.params.m

/-- The ITSR inputs within the cap: `(PK.seed, PK.root, bounded message)`. -/
abbrev ItsrXm (c : Caps) : Type := BN × BN × BList Byte c.ml

/-- The `H_msg` component of a world as a function on `randomizer × input`. -/
def hmsgTable (c : Caps) (Hf : BN × ItsrXm c → BM) : BN → BN → BN → BList Byte c.ml → BM :=
  fun r pk root ms ↦ Hf (r, (pk, root, ms))

/-- Replace the `H_msg` component. -/
def _root_.Reduction.FinFns.withHmsg {p : Params} {c : Caps} (ω : FinFns p c)
    (g : Bytes p.n → Bytes p.n → Bytes p.n → BList Byte c.ml → Bytes p.m) : FinFns p c :=
  { ω with hmsg := g }

/-- The FORS index list of a digest (the index map of `itsrProblem`). -/
def idxOf (d : BM) : List (Adrs × ℕ) := forsIndices Link.vp (splitDigest Link.vp.params d)

/-- The ITSR cover relation of `itsrProblem`, on digests. -/
def idxCov (S : Finset BM) (u : BM) : Prop := ∀ i ∈ idxOf u, ∃ d ∈ S, i ∈ idxOf d

instance (S : Finset BM) : DecidablePred (idxCov S) := fun u ↦ by
  unfold idxCov; infer_instance

theorem match_of_mem_idxOf (y z : BM) (i : Fin Link.vp.params.k)
    (h : ((splitDigest Link.vp.params y).forsAdrs,
        i.val * 2 ^ Link.vp.params.a +
          forsIdx Link.vp.params (splitDigest Link.vp.params y).md.toList i.val) ∈ idxOf z) :
    (coveringDigest Link.vp z).1 = (coveringDigest Link.vp y).1 ∧
      (coveringDigest Link.vp z).2 i = (coveringDigest Link.vp y).2 i := by
  simp only [idxOf, forsIndices, List.mem_map, List.mem_range] at h
  obtain ⟨j, hj, he⟩ := h
  obtain ⟨hadr, hnum⟩ := Prod.mk.inj he
  have ht : (splitDigest Link.vp.params z).idxTree.val =
      (splitDigest Link.vp.params y).idxTree.val := by
    have := congrArg Adrs.tree hadr
    simpa using this
  have hl : (splitDigest Link.vp.params z).idxLeaf.val =
      (splitDigest Link.vp.params y).idxLeaf.val := by
    have := congrArg Adrs.getKeyPairAddress hadr
    simpa using this
  have hz := forsIdx_lt Link.vp.params (splitDigest Link.vp.params z).md.toList j
  have hy := forsIdx_lt Link.vp.params (splitDigest Link.vp.params y).md.toList i.val
  have key : ∀ j i fz fy A : ℕ, 0 < A → fz < A → fy < A → j * A + fz = i * A + fy →
      j = i ∧ fz = fy := by
    intro j i fz fy A hA hz hy h
    have h1 := congrArg (· / A) h
    simp only [Nat.mul_comm _ A, Nat.mul_add_div hA, Nat.div_eq_of_lt hz,
      Nat.div_eq_of_lt hy, Nat.add_zero] at h1
    subst h1
    exact ⟨rfl, by omega⟩
  obtain ⟨hji, hf⟩ := key _ _ _ _ _ (Nat.two_pow_pos _) hz hy hnum
  subst hji
  refine ⟨(coveringDigest_fst_eq_iff Link.vp z y).2 ⟨Fin.ext ht, Fin.ext hl⟩, Fin.ext ?_⟩
  rw [coveringDigest_snd_val, coveringDigest_snd_val, hf]

theorem idxCov_forsCov (S : Finset BM) (u : BM) (h : idxCov S u) :
    forsCov (S.image (coveringDigest Link.vp)) (coveringDigest Link.vp u) := by
  intro j
  obtain ⟨d, hd, hmem⟩ := h ((splitDigest Link.vp.params u).forsAdrs,
      j.val * 2 ^ Link.vp.params.a +
        forsIdx Link.vp.params (splitDigest Link.vp.params u).md.toList j.val) (by
    simp only [idxOf, forsIndices, List.mem_map, List.mem_range]
    exact ⟨j.val, j.isLt, rfl⟩)
  obtain ⟨h1, h2⟩ := match_of_mem_idxOf u d j hmem
  exact ⟨coveringDigest Link.vp d, Finset.mem_image_of_mem _ hd, h1, h2⟩

/-- **The ITSR cover probability on `H_msg` digests is at most the FORS cover probability**:
uniform digests decode to uniform covering digests (`card_fiber_coveringDigest`). -/
theorem coverProb_idxCov_le (s : ℕ) :
    coverProb (Fin s) idxCov ≤
      coverProb (Fin s) (forsCov (I := Fin (2 ^ Link.vp.params.h))
        (L := Fin (2 ^ Link.vp.params.a)) (k := Link.vp.params.k)) :=
  coverProb_le_of_fiber (coveringDigest Link.vp) _ (Nat.two_pow_pos _)
    (card_fiber_coveringDigest Link.vp) idxCov _ idxCov_forsCov

section term
variable {E : Type} [Fintype E] [DecidableEq E] (c : Caps)
  (optRand₀ : Bytes Link.vp.params.n → Bytes Link.vp.params.n → ProbComp (Bytes Link.vp.params.n))
  (pkSeedDist₀ : ProbComp (Bytes Link.vp.params.n))
  (F : PortForger (EncX c) EncY E)

/-- The finite space of in-cap `H_msg` tables. -/
noncomputable instance hmsgFunFintype : Fintype (BN × ItsrXm c → BM) :=
  haveI : Fintype (ItsrXm c) := inferInstance
  haveI : DecidableEq (BN × ItsrXm c) := inferInstance
  haveI : Fintype BM := inferInstance
  Pi.instFintype

/-- The `H_msg` table as a function on `randomizer × input`. -/
def hmsgTableEquiv : (BN × ItsrXm c → BM) ≃ (BN → BN → BN → BList Byte c.ml → BM) where
  toFun := hmsgTable c
  invFun h := fun z ↦ h z.1 z.2.1 z.2.2.1 z.2.2.2
  left_inv _ := rfl
  right_inv _ := rfl

/-- Resampling the `H_msg` component does not change a uniform average. -/
theorem avΩ_resample_hmsg (f : Ω128 c → ℝ≥0∞) :
    avΩ c f = avΩ c fun ω ↦ ∑ Hf : BN × ItsrXm c → BM,
      (Fintype.card (BN × ItsrXm c → BM) : ℝ≥0∞)⁻¹ * f (ω.withHmsg (hmsgTable c Hf)) := by
  classical
  unfold avΩ
  set u : ℝ≥0∞ := (Fintype.card (Ω128 c) : ℝ≥0∞)⁻¹ with hu
  have hw : ∀ ω : Ω128 c, unifW (Ω128 c) ω = u := fun _ ↦ rfl
  simp only [hw]
  set cG : ℝ≥0∞ := (Fintype.card (BN × ItsrXm c → BM) : ℝ≥0∞) with hcG
  have hne : cG ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hnt : cG ≠ ⊤ := ENNReal.natCast_ne_top _
  let Φ : Ω128 c × (BN × ItsrXm c → BM) → Ω128 c × (BN × ItsrXm c → BM) :=
    fun p ↦ (p.1.withHmsg (hmsgTable c p.2), (hmsgTableEquiv c).symm p.1.hmsg)
  have hΦ : Function.Involutive Φ := by
    rintro ⟨⟨a, b, h, d⟩, g⟩
    rfl
  have h := Equiv.sum_comp hΦ.toPerm fun p : Ω128 c × (BN × ItsrXm c → BM) ↦ f p.1
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type] at h
  have h' : ∑ ω : Ω128 c, ∑ g : BN × ItsrXm c → BM, f (ω.withHmsg (hmsgTable c g)) =
      cG * ∑ ω : Ω128 c, f ω := by
    refine h.trans ?_
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Finset.mul_sum, hcG]
  calc ∑ ω : Ω128 c, u * f ω = u * (cG⁻¹ * (cG * ∑ ω : Ω128 c, f ω)) := by
        rw [← mul_assoc cG⁻¹, ENNReal.inv_mul_cancel hne hnt, one_mul, Finset.mul_sum]
    _ = _ := by
        rw [← h', Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun ω _ ↦ ?_
        rw [Finset.mul_sum, Finset.mul_sum]

theorem idxCov_mono (S S' : Finset BM) (u : BM) (h : S ⊆ S') (hc : idxCov S u) : idxCov S' u :=
  fun i hi ↦ by
    obtain ⟨d, hd, hdi⟩ := hc i hi
    exact ⟨d, h hd, hdi⟩

/-- The Part-2 bound at the parameters of SLH-DSA-SHA2-128s is `epsItsr`. -/
theorem itsr_bound_le (q' qs : ℕ) :
    (((2 * (q' : ℝ≥0∞) + 1) ^ 2 * coverProb (Fin qs) idxCov) ^ (2⁻¹ : ℝ) +
        2 * q' * ((qs : ℝ≥0∞) * (Fintype.card BN : ℝ≥0∞)⁻¹) ^ (2⁻¹ : ℝ)) ^ 2 ≤
      epsItsr Link.vp.params q' qs := by
  have hcp := coverProb_idxCov_le qs
  rw [coverProb_fors] at hcp
  simp only [Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat] at hcp
  have hK : (Fintype.card BN : ℝ≥0∞) = N128 := by
    rw [card_bytes_n]; simp only [N128, Nat.cast_pow, Nat.cast_ofNat]
  rw [hK]
  unfold epsItsr
  gcongr

theorem itsr_term (q' qs : ℕ)
    (hModel : ∀ ω₀ : Ω128 c, ∃ (L : LocalSig.{1, 0}) (A : QReg) (I : L.Interp) (ρ : SubState A)
      (x : IAdv L (qromSpec (BN × ItsrXm c) BM) (ItsrXm c) BN (fun _ ↦ BN × ItsrXm c) qs A),
      IAdv.IsQueryBound qs x (fun _ ↦ q') ∧
      ∀ Hf : BN × ItsrXm c → BM,
        qItsrAdvantage (itsrProblem Link.vp (primsΩ (ω₀.withHmsg (hmsgTable c Hf))))
            (qbItsrL (internalΩ c optRand₀ pkSeedDist₀ encΩ F (ω₀.withHmsg (hmsgTable c Hf))))
            F.ρ₀ ≤
          avg fun Rs : Fin qs → BN ↦
            qprob I Hf (IAdv.flat (rndCh Rs) (IAdv.stop (L := L)
              (spec := qromSpec (BN × ItsrXm c) BM)) qs [] x) ρ (itsrAWin idxCov Rs Hf)) :
    avΩ c (fun ω ↦ qItsrAdvantage (itsrProblem Link.vp (primsΩ ω))
      (qbItsrL (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω))
      (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω).ρ₀) ≤ epsItsr Link.vp.params q' qs := by
  rw [avΩ_resample_hmsg c]
  refine (avΩ_mono c fun ω₀ ↦ ?_).trans (le_of_eq (avΩ_const c _))
  obtain ⟨L, A, I, ρ, x, hx, hle⟩ := hModel ω₀
  calc _ ≤ ∑ Hf : BN × ItsrXm c → BM, (Fintype.card (BN × ItsrXm c → BM) : ℝ≥0∞)⁻¹ *
          avg (fun Rs : Fin qs → BN ↦ qprob I Hf (IAdv.flat (rndCh Rs) (IAdv.stop (L := L)
            (spec := qromSpec (BN × ItsrXm c) BM)) qs [] x) ρ (itsrAWin idxCov Rs Hf)) :=
        Finset.sum_le_sum fun Hf _ ↦ mul_le_mul' le_rfl (hle Hf)
    _ = itsrAdaptiveExp I ρ qs x idxCov := by
        unfold itsrAdaptiveExp mpExp avg
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun Rs _ ↦ Finset.sum_congr rfl fun Hf _ ↦ ?_
        ring
    _ ≤ _ := itsr4_adaptive_le (I := I) (ρ := ρ) (Cov := idxCov) idxCov_mono hx
    _ ≤ _ := itsr_bound_le q' qs

end term
end Reduction.QItsr

#print axioms Reduction.QItsr.coverProb_le_of_fiber
#print axioms Reduction.QItsr.coverProb_idxCov_le
#print axioms Reduction.QItsr.avΩ_resample_hmsg
#print axioms Reduction.QItsr.itsr_bound_le
#print axioms Reduction.QItsr.itsr_term
