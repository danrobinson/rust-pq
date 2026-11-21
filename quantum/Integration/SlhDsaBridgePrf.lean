import Integration.SlhDsaComposedFinal
import PQ.Interactive.QromBridgePrfStruct

/-!
# The encoding of the four hash components as one port function, and the `PRF` term

NOT part of the default target; checked by `scripts/check-integration.sh`.

## The encoding (`EncX c`, `EncY`, `encΩ`)

The port function of world `ω : Ω128 c` is `encΩ ω : EncX c → EncY` with

* `EncX c` = the disjoint union of the four (uncurried, bounded) domains of `Thash`, `H_msg`,
  `PRF`, `PRF_msg`;
* `EncY = Bytes n × Bytes m`, with the group of bytewise addition mod 256 (`encYGroup`);
* `encΩ ω (tag x)` = the value of the tagged component at `x`, in the first coordinate for the
  `n`-byte components and in the second for `H_msg`, the other coordinate `0`.

One port call `U_{encΩ ω} |x, y⟩ = |x, y + encΩ ω x⟩` evaluates exactly one component.

## The `PRF` term (`prf_term_suf`, `prf_term_euf`)

For every port forger `F` over this encoding with at most `q` port calls on every path:

  `avΩ c (real PRF game of qbPrfWC sufCheck / qbPrfC around F) ≤ avΩ c (ideal) + 8 q² / 2^128`

i.e. the field `prf` of `TermBounds` with count `q` (the reduction's own hashing is NOT charged:
it does not evaluate `PRF`), UNDER ONE NAMED HYPOTHESIS `hInd`: the distinguisher machine does
not depend on the `PRF` component of the world,
`prfMachSuf (ω.withPrf g) H = prfMachSuf ω H` (resp. `prfMachEuf`).  `hInd` is NOT proved: it is
not `rfl`, because `PublicKeyCore core` / `SignatureCore core` are structures indexed by the whole
`core` (which contains `PRF`), so the two machines pass through different intermediate types.
Everything else is proved: the machine is port-uniform (`pu_qbPrfWC`, `pu_qbPrfC`, `pu_intF`),
the key map is injective (`prfKey_injective`), resampling (`avΩ_resample_prf`), and
`prf_PU_real_le_ideal_add`.  No hypothesis on the forger's initial state beyond `PortForger`
(`exists_subState`).
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal PQ.Interactive PQ.QROM Quantum
open scoped ComplexOrder Kronecker

set_option linter.unusedSectionVars false

namespace Reduction

/-! ## The group on byte vectors -/

/-- Byte vectors as functions. -/
def bytesEquiv (k : ℕ) : Bytes k ≃ (Fin k → UInt8) where
  toFun v i := v[i]
  invFun f := Vector.ofFn f
  left_inv v := by
    ext i hi
    simp
  right_inv f := by
    funext i
    simp

/-- Bytewise addition mod 256. -/
noncomputable instance bytesGroup (k : ℕ) : AddCommGroup (Bytes k) :=
  (bytesEquiv k).addCommGroup

/-! ## The encoding -/

/-- Domain of the port function: tagged inputs of `Thash`, `H_msg`, `PRF`, `PRF_msg`. -/
abbrev EncX (c : Caps) : Type :=
  (Bytes Link.vp.params.n × Bytes 22 × BList (Bytes Link.vp.params.n) c.tl) ⊕
  ((Bytes Link.vp.params.n × Bytes Link.vp.params.n × Bytes Link.vp.params.n ×
      BList Byte c.ml) ⊕
  ((Bytes Link.vp.params.n × Bytes Link.vp.params.n × Bytes 22) ⊕
  (Bytes Link.vp.params.n × Bytes Link.vp.params.n × BList Byte c.ml)))

noncomputable instance encXDecEq (c : Caps) : DecidableEq (EncX c) := Classical.decEq _

/-- Codomain of the port function. -/
abbrev EncY : Type := Bytes Link.vp.params.n × Bytes Link.vp.params.m

/-- **The port function of world `ω`.** -/
def encΩ {c : Caps} (ω : Ω128 c) : EncX c → EncY
  | .inl x => (ω.thash x.1 x.2.1 x.2.2, 0)
  | .inr (.inl x) => (0, ω.hmsg x.1 x.2.1 x.2.2.1 x.2.2.2)
  | .inr (.inr (.inl x)) => (ω.prf x.1 x.2.1 x.2.2, 0)
  | .inr (.inr (.inr x)) => (ω.prfMsg x.1 x.2.1 x.2.2, 0)

/-- Replace the `PRF` component. -/
def FinFns.withPrf {p : Params} {c : Caps} (ω : FinFns p c)
    (g : Bytes p.n → Bytes p.n → Bytes 22 → Bytes p.n) : FinFns p c :=
  { ω with prf := g }

/-- Each component is recovered by one evaluation of the port function. -/
theorem encΩ_thash {c : Caps} (ω : Ω128 c) (pk a xs) :
    (encΩ ω (.inl (pk, a, xs))).1 = ω.thash pk a xs := rfl
theorem encΩ_hmsg {c : Caps} (ω : Ω128 c) (r pk root ms) :
    (encΩ ω (.inr (.inl (r, pk, root, ms)))).2 = ω.hmsg r pk root ms := rfl
theorem encΩ_prf {c : Caps} (ω : Ω128 c) (pk sk a) :
    (encΩ ω (.inr (.inr (.inl (pk, sk, a))))).1 = ω.prf pk sk a := rfl
theorem encΩ_prfMsg {c : Caps} (ω : Ω128 c) (sk r ms) :
    (encΩ ω (.inr (.inr (.inr (sk, r, ms))))).1 = ω.prfMsg sk r ms := rfl

/-- The `PRF` point read by a port query, as (key, (PK.seed, compressed address)). -/
def prfLoc {c : Caps} : EncX c →
    Option (Bytes Link.vp.params.n × (Bytes Link.vp.params.n × Bytes 22))
  | .inr (.inr (.inl x)) => some (x.2.1, (x.1, x.2.2))
  | _ => none

/-- The `PRF` component as a keyed function `(SK.seed, (PK.seed, ADRSc)) ↦ value`. -/
def prfTable (g : Bytes Link.vp.params.n × (Bytes Link.vp.params.n × Bytes 22) →
    Bytes Link.vp.params.n) :
    Bytes Link.vp.params.n → Bytes Link.vp.params.n → Bytes 22 → Bytes Link.vp.params.n :=
  fun pk k a ↦ g (k, (pk, a))

theorem encΩ_withPrf_local {c : Caps} (ω : Ω128 c)
    (g g' : Bytes Link.vp.params.n × (Bytes Link.vp.params.n × Bytes 22) →
      Bytes Link.vp.params.n) (x : EncX c)
    (h : ∀ p, prfLoc x = some p → g p = g' p) :
    encΩ (ω.withPrf (prfTable g)) x = encΩ (ω.withPrf (prfTable g')) x := by
  rcases x with x | x | x | x
  · rfl
  · rfl
  · change (g (x.2.1, (x.1, x.2.2)), _) = (g' (x.2.1, (x.1, x.2.2)), _)
    rw [h _ rfl]
  · rfl

/-! ## Initial states -/

/-- Every density matrix on `A × Unit` is `ρ ⊗ |()⟩⟨()|`. -/
theorem exists_subState {A : Type} [Fintype A] [DecidableEq A]
    (M : Matrix (A × Unit) (A × Unit) ℂ) (hM : M.PosSemidef) (h1 : M.trace = 1) :
    ∃ ρ : SubState A, M = ρ.matrix ⊗ₖ (SubState.basis ()).matrix := by
  have htr : (M.submatrix (fun a ↦ (a, ())) (fun a ↦ (a, ()))).trace = M.trace := by
    simp [Matrix.trace, Fintype.sum_prod_type]
  refine ⟨⟨M.submatrix (fun a ↦ (a, ())) (fun a ↦ (a, ())), hM.submatrix _, ?_⟩, ?_⟩
  · rw [htr, h1]
    simp
  · ext ⟨a, ⟨⟩⟩ ⟨b, ⟨⟩⟩
    simp [Matrix.kroneckerMap_apply, SubState.basis]

/-! ## Port-uniformity of the reduction machines -/

section pu

variable {X Y E : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
  [Fintype E] [DecidableEq E]
  {vp : ValidatedParams} {prims : Primitives vp.params}
  [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey]
  [Inhabited prims.Y]
  {optRand : PublicKeyCore prims.core → ProbComp prims.Y} {pkSeedDist : ProbComp prims.PkSeed}

/-- The SUF-CMA `PRF` distinguisher around a port-uniform forger is port-uniform. -/
theorem pu_qbPrfWC (w : WinCheck vp prims)
    (Qf : (X → Y) → QForger (WS X Y E) (internalAlg vp prims optRand pkSeedDist)) (q : ℕ)
    (hQ : ∀ pk, PU (fun H ↦ (Qf H).main pk) q) : PU (fun H ↦ qbPrfWC w (Qf H)) q := by
  unfold qbPrfWC qbPrfW qRunForgerSig
  refine PU.wrap0 _ ?_
  refine PU.liftQ_bind _ fun pkSeed ↦ PU.liftQ_bind _ fun skPrf ↦ PU.liftQ_bind _ fun root ↦ ?_
  exact PU.bind (q₂ := 0) (PU.wrap _ (hQ ⟨pkSeed, root⟩) []) fun z ↦ PU.liftQ _ 0

/-- The EUF-CMA `PRF` distinguisher around a port-uniform forger is port-uniform. -/
theorem pu_qbPrfC
    (Qf : (X → Y) → QForger (WS X Y E) (internalAlg vp prims optRand pkSeedDist)) (q : ℕ)
    (hQ : ∀ pk, PU (fun H ↦ (Qf H).main pk) q) : PU (fun H ↦ qbPrfC (Qf H)) q := by
  unfold qbPrfC qbPrf qRunForger
  refine PU.wrap0 _ ?_
  refine PU.liftQ_bind _ fun pkSeed ↦ PU.liftQ_bind _ fun skPrf ↦ PU.liftQ_bind _ fun root ↦ ?_
  exact PU.bind (q₂ := 0) (PU.wrap _ (hQ ⟨pkSeed, root⟩) _) fun z ↦ PU.liftQ _ 0

end pu

/-! ## Sizes -/

theorem card_bytes' (k : ℕ) : Fintype.card (Bytes k) = 256 ^ k := by
  rw [Fintype.card_congr (bytesEquiv k), Fintype.card_fun, Fintype.card_fin,
    ← FinEnum.card_eq_fintypeCard, FinEnum.card_UInt8]
  norm_num

theorem card_bytes_n : Fintype.card (Bytes Link.vp.params.n) = 2 ^ 128 := by
  rw [card_bytes']
  have : Link.vp.params.n = 16 := rfl
  rw [this]
  norm_num

/-! ## The `PRF` term -/

section term

variable {E : Type} [Fintype E] [DecidableEq E] (c : Caps)
  (optRand₀ : Bytes Link.vp.params.n → Bytes Link.vp.params.n → ProbComp (Bytes Link.vp.params.n))
  (pkSeedDist₀ : ProbComp (Bytes Link.vp.params.n))
  (F : PortForger (EncX c) EncY E)

/-- `n`-byte strings of the parameter set. -/
abbrev BN : Type := Bytes Link.vp.params.n

/-- Inputs of the secret-key `PRF` game: `(PK.seed, secret-key address)`. -/
abbrev PrfD : Type := BN × SkAdrs Link.vp

/-- The internal forger of the reduction in world `ω`, with the port computing `H`. -/
noncomputable def intF (ω : Ω128 c) (H : EncX c → EncY) :
    QForger (WS (EncX c) EncY E)
      (internalAlg Link.vp (primsΩ ω) (optRandOf c optRand₀ ω) pkSeedDist₀) :=
  qPureBytesToInternal (F.at H (algΩ c optRand₀ pkSeedDist₀ ω))

theorem pu_intF (q : ℕ) (hq : ∀ pk, CountBound isPort (F.main pk) q) (ω : Ω128 c)
    (pk : PublicKeyCore (primsΩ ω).core) :
    PU (fun H ↦ (intF c optRand₀ pkSeedDist₀ F ω H).main pk) q := by
  unfold intF qPureBytesToInternal qToInternal qPureBytesToTyped QForger.wrapForger PortForger.at
  exact PU.map _ (PU.wrap0 _ (PU.map _ (PU.wrap0 _ (PU.compileQ _ q (hq _)))))

/-- The SUF-CMA `PRF` distinguisher in world `ω` with the port computing `H`. -/
noncomputable def prfMachSuf (ω : Ω128 c) (H : EncX c → EncY) :
    QOC (WS (EncX c) EncY E) (PRFScheme.PRFOracleSpec PrfD BN) Bool :=
  qbPrfWC sufCheck (intF c optRand₀ pkSeedDist₀ F ω H)

/-- The EUF-CMA `PRF` distinguisher in world `ω` with the port computing `H`. -/
noncomputable def prfMachEuf (ω : Ω128 c) (H : EncX c → EncY) :
    QOC (WS (EncX c) EncY E) (PRFScheme.PRFOracleSpec PrfD BN) Bool :=
  qbPrfC (intF c optRand₀ pkSeedDist₀ F ω H)

/-- The `PRF` input as a point of the finite keyed table: `(PK.seed, compressed address)`. -/
def prfKey (d : PrfD) : BN × Bytes 22 := (d.1, Concrete.sha2AdrsKey d.2.1)

theorem prfKey_injective : Function.Injective prfKey := by
  rintro ⟨pk, a, ha⟩ ⟨pk', a', ha'⟩ h
  have h1 : pk = pk' := congrArg Prod.fst h
  have h2 : Concrete.sha2AdrsKey a = Concrete.sha2AdrsKey a' := congrArg Prod.snd h
  have hinj := (structural_randPrims_128s (Classical.arbitrary (Ω128 ⟨0, 0⟩)).toRand).keyInj
  have h3 : a = a' := hinj ha.addressFacts ha'.addressFacts h2
  subst h1
  subst h3
  rfl

/-- The keyed table of a `PRF` component. -/
def prfTableEquiv : (BN × (BN × Bytes 22) → BN) ≃ (BN → BN → Bytes 22 → BN) where
  toFun := prfTable
  invFun h := fun x ↦ h x.2.1 x.1 x.2.2
  left_inv _ := rfl
  right_inv _ := rfl

/-- Resampling the `PRF` component does not change a uniform average. -/
theorem avΩ_resample_prf (f : Ω128 c → ℝ≥0∞) :
    avΩ c f = avΩ c fun ω ↦ ∑ g : BN × (BN × Bytes 22) → BN,
      (Fintype.card (BN × (BN × Bytes 22) → BN) : ℝ≥0∞)⁻¹ * f (ω.withPrf (prfTable g)) := by
  classical
  unfold avΩ
  set u : ℝ≥0∞ := (Fintype.card (Ω128 c) : ℝ≥0∞)⁻¹ with hu
  have hw : ∀ ω : Ω128 c, unifW (Ω128 c) ω = u := fun _ ↦ rfl
  simp only [hw]
  set cG : ℝ≥0∞ := (Fintype.card (BN × (BN × Bytes 22) → BN) : ℝ≥0∞) with hcG
  have hne : cG ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hnt : cG ≠ ⊤ := ENNReal.natCast_ne_top _
  -- the involution swapping the `PRF` component with the fresh table
  let Φ : Ω128 c × (BN × (BN × Bytes 22) → BN) → Ω128 c × (BN × (BN × Bytes 22) → BN) :=
    fun p ↦ (p.1.withPrf (prfTable p.2), prfTableEquiv.symm p.1.prf)
  have hΦ : Function.Involutive Φ := by
    rintro ⟨⟨a, b, h, d⟩, g⟩
    rfl
  have h := Equiv.sum_comp hΦ.toPerm fun p : Ω128 c × (BN × (BN × Bytes 22) → BN) ↦ f p.1
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type] at h
  have h' : ∑ ω : Ω128 c, ∑ g : BN × (BN × Bytes 22) → BN, f (ω.withPrf (prfTable g)) =
      cG * ∑ ω : Ω128 c, f ω := by
    refine h.trans ?_
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Finset.mul_sum, hcG]
  calc ∑ ω : Ω128 c, u * f ω = u * (cG⁻¹ * (cG * ∑ ω : Ω128 c, f ω)) := by
        rw [← mul_assoc cG⁻¹, ENNReal.inv_mul_cancel hne hnt, one_mul, Finset.mul_sum]
    _ = _ := by
        rw [← h', Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun ω _ ↦ ?_
        rw [Finset.mul_sum, Finset.mul_sum]

lemma avΩ_mono {f g : Ω128 c → ℝ≥0∞} (h : ∀ ω, f ω ≤ g ω) : avΩ c f ≤ avΩ c g := by
  unfold avΩ
  exact Finset.sum_le_sum fun ω _ ↦ mul_le_mul' le_rfl (h ω)

lemma avΩ_const (a : ℝ≥0∞) : avΩ c (fun _ ↦ a) = a := by
  unfold avΩ
  rw [← Finset.sum_mul, sum_unifW, one_mul]

/-- **The `PRF` term for a port-uniform machine family that does not depend on the `PRF`
component of the world.** -/
theorem prf_term_of_indep
    (mach : Ω128 c → (EncX c → EncY) →
      QOC (WS (EncX c) EncY E) (PRFScheme.PRFOracleSpec PrfD BN) Bool)
    (prfS : Ω128 c → PRFScheme BN PrfD BN)
    (hS : ∀ (ω : Ω128 c) g, prfS (ω.withPrf (prfTable g)) = keyedScheme prfKey g)
    (q : ℕ) (hPU : ∀ ω, PU (mach ω) q)
    (hInd : ∀ ω g H, mach (ω.withPrf g) H = mach ω H)
    (M : Matrix (WS (EncX c) EncY E) (WS (EncX c) EncY E) ℂ) (hM : M.PosSemidef)
    (h1 : M.trace = 1) :
    avΩ c (fun ω ↦ qPrfRealPr (prfS ω) (mach ω (encΩ ω)) M) ≤
      avΩ c (fun ω ↦ qPrfIdealPr (mach ω (encΩ ω)) M) + epsPrf q := by
  obtain ⟨ρ, rfl⟩ := exists_subState M hM h1
  rw [avΩ_resample_prf c fun ω ↦ qPrfRealPr (prfS ω) (mach ω (encΩ ω)) _,
    avΩ_resample_prf c fun ω ↦ qPrfIdealPr (mach ω (encΩ ω)) _]
  simp only [hS, hInd]
  have key : ∀ ω : Ω128 c, _ ≤ _ := fun ω ↦
    prf_PU_real_le_ideal_add prfKey prfKey_injective (mach ω) q (hPU ω)
      (fun g ↦ encΩ (ω.withPrf (prfTable g))) prfLoc (encΩ_withPrf_local ω) ρ
  refine (avΩ_mono c key).trans (le_of_eq ?_)
  rw [avΩ_add, avΩ_const, card_cast_real card_bytes_n]
  rfl

/-- **`PRF` term, SUF-CMA**, under the one named hypothesis `hInd` (the machine does not depend
on the `PRF` component of the world).  No charge for the reduction's own hashing. -/
theorem prf_term_suf (q : ℕ) (hq : ∀ pk, CountBound isPort (F.main pk) q)
    (hInd : ∀ (ω : Ω128 c) g H, prfMachSuf c optRand₀ pkSeedDist₀ F (ω.withPrf g) H =
      prfMachSuf c optRand₀ pkSeedDist₀ F ω H) :
    avΩ c (fun ω ↦ qPrfRealPr (skPrfC Link.vp (primsΩ ω))
        (qbPrfWC sufCheck (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω))
        (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω).ρ₀) ≤
      avΩ c (fun ω ↦ qPrfIdealPr (qbPrfWC sufCheck (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω))
        (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω).ρ₀) + epsPrf q :=
  prf_term_of_indep c (prfMachSuf c optRand₀ pkSeedDist₀ F)
    (fun ω ↦ skPrfC Link.vp (primsΩ ω)) (fun _ _ ↦ rfl) q
    (fun ω ↦ pu_qbPrfWC sufCheck _ q fun pk ↦ pu_intF c optRand₀ pkSeedDist₀ F q hq ω pk)
    hInd F.ρ₀ F.posSemidef F.trace_eq_one

/-- **`PRF` term, EUF-CMA**, under the named hypothesis `hInd`. -/
theorem prf_term_euf (q : ℕ) (hq : ∀ pk, CountBound isPort (F.main pk) q)
    (hInd : ∀ (ω : Ω128 c) g H, prfMachEuf c optRand₀ pkSeedDist₀ F (ω.withPrf g) H =
      prfMachEuf c optRand₀ pkSeedDist₀ F ω H) :
    avΩ c (fun ω ↦ qPrfRealPr (skPrfC Link.vp (primsΩ ω))
        (qbPrfC (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω))
        (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω).ρ₀) ≤
      avΩ c (fun ω ↦ qPrfIdealPr (qbPrfC (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω))
        (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω).ρ₀) + epsPrf q :=
  prf_term_of_indep c (prfMachEuf c optRand₀ pkSeedDist₀ F)
    (fun ω ↦ skPrfC Link.vp (primsΩ ω)) (fun _ _ ↦ rfl) q
    (fun ω ↦ pu_qbPrfC _ q fun pk ↦ pu_intF c optRand₀ pkSeedDist₀ F q hq ω pk)
    hInd F.ρ₀ F.posSemidef F.trace_eq_one

end term

end Reduction

#print axioms Reduction.encΩ_withPrf_local
#print axioms Reduction.exists_subState
#print axioms Reduction.pu_qbPrfWC
#print axioms Reduction.pu_qbPrfC
#print axioms Reduction.card_bytes_n
#print axioms Reduction.pu_intF
#print axioms Reduction.prfKey_injective
#print axioms Reduction.avΩ_resample_prf
#print axioms Reduction.prf_term_of_indep
#print axioms Reduction.prf_term_suf
#print axioms Reduction.prf_term_euf
