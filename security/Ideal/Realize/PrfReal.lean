import Ideal.Realize.PrfCount
import Ideal.Realize.MsgReal

/-!
# The `PRF` realisers (SUF and EUF)

For an ideal-model forger `S`, a table-independent `opt_rand` sampler `oR` and any seed
distribution, ONE ideal-model `PRF` distinguisher `AprfS S oR pkSeedDist` (resp. `AprfE`)
whose instantiation at every table `g` IS the Reduction's `PRF` distinguisher
`bPrfWC sufCheck (S.typedS (optRandU oR) pkSeedDist g)` (resp. `bPrfC (S.typedE …)`):

* `AprfS = chainP P`, `P` the port program `bPrfWCOpenP` over `Rd = R₀ dT dH` at the forger
  `typedC codec₀ default S.main`; `chainP` issues every `Thash`/`H_msg` query as its compression
  chain (`hashC`) and every `PRF_msg` query as its HMAC chain (`prfMsgC`); the PRF game oracle
  stays the game's (it replaces the scheme's `PRF`);
* `bPrfWC_eq_inst`, `bPrfC_eq_inst`: the equations (`Reduction.Open.bPrfWCOpen_close_suf`, the
  open transport `bPrfWCOpen_setPrf`, `close_castP'`, port fusion, `Thash`/`H_msg` independence,
  `close_portP`);
* counts: compression queries `≤ qPrf qf qs ℓ = qf + Hn·thashCost len + (qs+1)·hmsgCost ℓ +
  qs·prfMsgCost ℓ`, PRF-game queries `≤ qOPrf qs = 2^h'·len + qs·signReads`;
* `realizesPrfSuf`, `realizesPrfEuf`; closed forms `qPrf_128s`, `qOPrf_128s`, `qPrf_le`.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security

namespace Ideal.Realize.Prf

open Reduction Reduction.Open Ideal.Transport
open Ideal.Realize.Msg (codec₀ optRand₀ Rd mainC cEmb instImpl_cEmb instImpl_liftM typedC
  bytesToTypedS_inst bytesToTyped_inst PortBounds portBounds_typedC thB okLen_le hashN
  hashN_128s thashCost_thB isTh isHm longH cEmb_bound cEmb_zero liftM_zero)

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- The PRF-game domain of the realisers. -/
abbrev Dsk : Type := Bytes 16 × SkAd

/-- The hash interface (with `PRF_msg`) answered at the table `g`. -/
def hImpl (g : CF St Blk) : QueryImpl (HSpec Rd) Id
  | .inl q => implTH (thG g) (hmG g) q
  | .inr t => pmG g t.1 t.2.1 t.2.2

/-- The closing handler at the table `g`, over the reference interface. -/
def closeR (g : CF St Blk) : QueryImpl (PSpec Rd Dsk) (OracleComp (unifSpec + (Dsk →ₒ Bytes 16)))
  | .inl n => (liftM (liftM (unifSpec.query n) : ProbComp _) :
      OracleComp (unifSpec + (Dsk →ₒ Bytes 16)) _)
  | .inr (.inl d) => (PRFScheme.functionQuery d : OracleComp (PRFScheme.PRFOracleSpec Dsk (Bytes 16)) _)
  | .inr (.inr q) => pure (hImpl g q)

theorem close_castP' (g : CF St Blk) {α : Type} (X : OracleComp (PSpec Rd Dsk) α) :
    simulateQ (closeImpl (primsG (liftC g)) (Bytes 16 × SkAd))
        (castP' (R₀ (thG g) (hmG g)) (prfG g) (pmG g) Dsk X) =
      simulateQ (closeR g) X := by krfl

/-- The hash interface with `PRF_msg`, as compression programs. -/
def hashPC : QueryImpl (HSpec Rd) (OracleComp CSpec)
  | .inl q => hashC q
  | .inr t => prfMsgC t.1 t.2.1 t.2.2

theorem hashPC_inst (g : CF St Blk) (q : (HSpec Rd).Domain) :
    simulateQ (instImpl₀ g) (hashPC q) = pure (f := ProbComp) (α := (HSpec Rd).Range q) (hImpl g q) := by
  rcases q with q | t
  · exact hashC_inst g q
  · exact prfMsgC_inst g t.1 t.2.1 t.2.2

/-- Interpretation of the port program: port and game queries forwarded, hash and `PRF_msg`
queries issued as compression chains. -/
def chainP : QueryImpl (QSpec Rd Dsk) (OracleComp (unifSpec + (hS St Blk + (Dsk →ₒ Bytes 16))))
  | .inl n => (liftM ((unifSpec + (hS St Blk + (Dsk →ₒ Bytes 16))).query (.inl n)) :
      OracleComp (unifSpec + (hS St Blk + (Dsk →ₒ Bytes 16))) _)
  | .inr (.inl t) => (liftM ((unifSpec + (hS St Blk + (Dsk →ₒ Bytes 16))).query (.inr t)) :
      OracleComp (unifSpec + (hS St Blk + (Dsk →ₒ Bytes 16))) _)
  | .inr (.inr q) => simulateQ (cEmb (X := Dsk →ₒ Bytes 16)) (hashPC q)

theorem close_portP (T : Bytes 16 → Bytes 22 → List (Bytes 16) → Bytes 16)
    (H : Bytes 16 → Bytes 16 → Bytes 16 → List Byte → Bytes 30) (g : CF St Blk) {α : Type}
    (X : OracleComp (QSpec (R₀ T H) Dsk) α) :
    simulateQ (closeR g) (simulateQ (portP (prims := R₀ T H) (D := Dsk) g) X) =
      simulateQ (instImpl g) (simulateQ chainP X) := by
  refine Ideal.Realize.simulateQ_comm_of_step _ _ _ _ (fun t => ?_) X
  rcases t with n | (q | d) | q
  · simp only [portP, chainP]
    rw [simulateQ_spec_query, simulateQ_spec_query]
    rfl
  · simp only [portP, chainP, simulateQ_pure]
    rw [simulateQ_spec_query]
    rfl
  · simp only [portP, chainP]
    rw [simulateQ_spec_query]
    erw [simulateQ_spec_query]
    rfl
  · simp only [portP, chainP]
    rw [simulateQ_spec_query, instImpl_cEmb, hashPC_inst, liftM_pure]
    rfl

/-- The SUF port program. -/
noncomputable def PprfS (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    (pkSeedDist : ProbComp (Bytes 16)) : OracleComp (QSpec Rd Dsk) Bool :=
  bPrfWCOpenP (prims := Rd) (optRand₀ oR) pkSeedDist sufCheckOpen (mainC S)

/-- The EUF port program. -/
noncomputable def PprfE (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    (pkSeedDist : ProbComp (Bytes 16)) : OracleComp (QSpec Rd Dsk) Bool :=
  bPrfCOpenP (prims := Rd) (optRand₀ oR) pkSeedDist (mainC S)

/-- The ideal-model distinguisher of a port program. -/
noncomputable def chainA (P : OracleComp (QSpec Rd Dsk) Bool) :
    PrfAdvI St Blk (Bytes 16) SkAd (Bytes 16) :=
  simulateQ chainP P

/-- **The ideal-model `PRF` distinguisher (SUF).** -/
noncomputable def AprfS (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    (pkSeedDist : ProbComp (Bytes 16)) : PrfAdvI St Blk (Bytes 16) SkAd (Bytes 16) :=
  chainA (PprfS S oR pkSeedDist)

/-- **The ideal-model `PRF` distinguisher (EUF).** -/
noncomputable def AprfE (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    (pkSeedDist : ProbComp (Bytes 16)) : PrfAdvI St Blk (Bytes 16) SkAd (Bytes 16) :=
  chainA (PprfE S oR pkSeedDist)

/-- **SUF: the Reduction's `PRF` distinguisher at every table is `AprfS` there.** -/
theorem bPrfWC_eq_inst (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    (pkSeedDist : ProbComp (Bytes 16)) (g : CF St Blk) :
    bPrfWC sufCheck (S.typedS (optRandU oR) pkSeedDist g) = (AprfS S oR pkSeedDist).inst g := by
  have h1 := (bPrfWCOpen_close_suf (prims := primsG (liftC g))
    (S.typedS (optRandU oR) pkSeedDist g)).symm
  refine h1.trans ?_
  have h2 := bPrfWCOpen_setPrf (R₀ (thG g) (hmG g)) (prfG g) (pmG g) (optRand₀ oR) (optRandU oR g)
    (fun _ => rfl) codec₀ pkSeedDist (fun pk => simulateQ (instImpl g) (S.main pk))
  have h2'' := congrArg (fun x => simulateQ (closeImpl (primsG (liftC g)) Dsk)
    (castP' (R₀ (thG g) (hmG g)) (prfG g) (pmG g) Dsk x)) h2
  refine (?_ : _ = _).trans (h2''.trans ?_)
  · show _ = _
    krfl
  refine (close_castP' g _).trans ?_
  have h3 := bytesToTypedS_inst (prims := R₀ (thG g) (hmG g)) (optRand := optRand₀ oR)
    (pkSeedDist := pkSeedDist) codec₀ g S.main
  rw [h3]
  have h4 := bPrfWCOpenP_fusion (prims := R₀ (thG g) (hmG g)) (optRand₀ oR) pkSeedDist g
    sufCheckOpen (typedC codec₀ default S.main)
  rw [← h4]
  have h5 : bPrfWCOpenP (prims := R₀ (thG g) (hmG g)) (optRand₀ oR) pkSeedDist sufCheckOpen
      (typedC codec₀ default S.main) = PprfS S oR pkSeedDist :=
    bPrfWCOpenP_withTH (prims := Rd) (thG g) (hmG g) (mainC S)
  rw [h5]
  exact close_portP (thG g) (hmG g) g _

/-- **EUF: the Reduction's `PRF` distinguisher at every table is `AprfE` there.** -/
theorem bPrfC_eq_inst (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    (pkSeedDist : ProbComp (Bytes 16)) (g : CF St Blk) :
    bPrfC (S.typedE (optRandU oR) pkSeedDist g) = (AprfE S oR pkSeedDist).inst g := by
  have h1 := (bPrfCOpen_close (prims := primsG (liftC g))
    (S.typedE (optRandU oR) pkSeedDist g)).symm
  refine h1.trans ?_
  have h2 := bPrfCOpen_setPrf (R₀ (thG g) (hmG g)) (prfG g) (pmG g) (optRand₀ oR) (optRandU oR g)
    (fun _ => rfl) codec₀ pkSeedDist (fun pk => simulateQ (instImpl g) (S.main pk))
  have h2'' := congrArg (fun x => simulateQ (closeImpl (primsG (liftC g)) Dsk)
    (castP' (R₀ (thG g) (hmG g)) (prfG g) (pmG g) Dsk x)) h2
  refine (?_ : _ = _).trans (h2''.trans ?_)
  · show _ = _
    krfl
  refine (close_castP' g _).trans ?_
  have h3 := bytesToTyped_inst (prims := R₀ (thG g) (hmG g)) (optRand := optRand₀ oR)
    (pkSeedDist := pkSeedDist) codec₀ g S.main
  rw [h3]
  have h4 := bPrfCOpenP_fusion (prims := R₀ (thG g) (hmG g)) (optRand₀ oR) pkSeedDist g
    (typedC codec₀ default S.main)
  rw [← h4]
  have h5 : bPrfCOpenP (prims := R₀ (thG g) (hmG g)) (optRand₀ oR) pkSeedDist
      (typedC codec₀ default S.main) = PprfE S oR pkSeedDist :=
    bPrfCOpenP_withTH (prims := Rd) (thG g) (hmG g) (mainC S)
  rw [h5]
  exact close_portP (thG g) (hmG g) g _

/-! ## Counts -/

section Weighted

variable {ι ι' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'} {α : Type}

private theorem step_arith4 {P : Prop} [Decidable P] {n c : ℕ} (h : ¬ P ∨ 0 < n) :
    (if P then c else 0) + (if P then n - 1 else n) * c = n * c := by
  by_cases hp : P
  · have hn : 0 < n := h.resolve_left (not_not.mpr hp)
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    simp [hp, Nat.succ_mul, Nat.add_comm]
  · simp [hp]

/-- **Weighted budget transfer with four classes** (`Ideal.Realize.qb_simulateQ_classes` with one
more class). -/
theorem qb_simulateQ_classes4 {p₀ p₁ p₂ p₃ p₄ : ι → Prop} [DecidablePred p₀] [DecidablePred p₁]
    [DecidablePred p₂] [DecidablePred p₃] [DecidablePred p₄] {q : ι' → Prop} [DecidablePred q]
    {impl : QueryImpl spec (OracleComp spec')} (c₁ c₂ c₃ c₄ : ℕ)
    (hstep : ∀ t, ¬ p₀ t → IsQueryBoundP (impl t) q
      ((if p₁ t then c₁ else 0) + (if p₂ t then c₂ else 0) + (if p₃ t then c₃ else 0) +
        (if p₄ t then c₄ else 0)))
    {oa : OracleComp spec α} {n₁ n₂ n₃ n₄ : ℕ}
    (h0 : IsQueryBoundP oa p₀ 0) (h1 : IsQueryBoundP oa p₁ n₁) (h2 : IsQueryBoundP oa p₂ n₂)
    (h3 : IsQueryBoundP oa p₃ n₃) (h4 : IsQueryBoundP oa p₄ n₄) :
    IsQueryBoundP (simulateQ impl oa) q (n₁ * c₁ + n₂ * c₂ + n₃ * c₃ + n₄ * c₄) := by
  induction oa using OracleComp.inductionOn generalizing n₁ n₂ n₃ n₄ with
  | pure x => simp
  | query_bind t mx ih =>
    rw [isQueryBoundP_query_bind_iff] at h0 h1 h2 h3 h4
    have ht0 : ¬ p₀ t := h0.1.resolve_right (Nat.lt_irrefl 0)
    simp only [simulateQ_query_bind, OracleQuery.input_query, monadLift_self]
    have hb := isQueryBoundP_bind (hstep t ht0) fun u _ =>
      ih u (by simpa [ht0] using h0.2 u) (h1.2 u) (h2.2 u) (h3.2 u) (h4.2 u)
    refine hb.mono (le_of_eq ?_)
    have e1 := step_arith4 (c := c₁) h1.1
    have e2 := step_arith4 (c := c₂) h2.1
    have e3 := step_arith4 (c := c₃) h3.1
    have e4 := step_arith4 (c := c₄) h4.1
    omega

end Weighted

theorem prfMsgCost_mono {n m : ℕ} (h : n ≤ m) : prfMsgCost n ≤ prfMsgCost m := by
  unfold prfMsgCost
  exact Nat.add_le_add_right (Nat.div_le_div_right (by omega)) _

/-- **The compression-query count of the `PRF` realisers**: the forger's own queries, the
`Thash` chains, the `H_msg` chains and the `PRF_msg` (HMAC) chains. -/
def qPrf (qf qs ℓ : ℕ) : ℕ :=
  qf * 1 + hashN qs * thashCost thB + (qs + 1) * hmsgCost ℓ + qs * prfMsgCost ℓ

/-- **The PRF-oracle count of the `PRF` realisers** (`Reduction.Open.bPrfWCOpen_suf_game`). -/
def qOPrf (qs : ℕ) : ℕ := 2 ^ Link.vp.params.hp * Link.vp.params.len + qs * signReads Link.vp

section Counts

variable (P : OracleComp (QSpec Rd Dsk) Bool) {qf qs ℓ : ℕ}

theorem chain_comp (hport : IsQueryBoundP P qPort qf) (hth : IsQueryBoundP P qTh (hashN qs))
    (hhm : IsQueryBoundP P qHm (qs + 1)) (hpm : IsQueryBoundP P qPm qs)
    (hbad : IsQueryBoundP P (qBad thB ℓ) 0) :
    IsQueryBoundP (chainA P) (fun i => isCompQ i = true) (qPrf qf qs ℓ) := by
  unfold chainA
  refine qb_simulateQ_classes4 (p₀ := qBad thB ℓ) (p₁ := qPort) (p₂ := qTh) (p₃ := qHm)
    (p₄ := qPm) 1 (thashCost thB) (hmsgCost ℓ) (prfMsgCost ℓ) (fun t ht => ?_)
    hbad hport hth hhm hpm
  rcases t with n | (q | d) | (h | ⟨k, r, M⟩)
  · exact (isQueryBoundP_query_iff _ _ _).2 fun h => by simp [isCompQ] at h
  · exact (isQueryBoundP_query_iff _ _ _).2 fun _ => by simp [liftQ]
  · exact (isQueryBoundP_query_iff _ _ _).2 fun h => by simp [isCompQ] at h
  · rcases h with ⟨pk, a, xs⟩ | ⟨R, pk, root, M⟩
    · have hx : xs.length ≤ thB := by
        simp only [liftQ, longH, decide_eq_true_eq, not_lt] at ht
        exact ht
      refine (cEmb_bound (X := Dsk →ₒ Bytes 16) _ _ (thashC_bound pk a xs)
        (fun i => isCompQ i = true) (fun _ => rfl) (fun _ => by simp [isCompQ])).mono ?_
      simp only [liftQ, isTh, isHm, ite_true, ite_false]
      exact (Nat.add_zero _).le.trans ((Nat.add_zero _).le.trans (thashCost_mono hx))
    · have hM : M.length ≤ ℓ := by
        simp only [liftQ, longH, decide_eq_true_eq, not_lt] at ht
        exact ht
      refine (cEmb_bound (X := Dsk →ₒ Bytes 16) _ _ (hmsgC_bound R pk root M)
        (fun i => isCompQ i = true) (fun _ => rfl) (fun _ => by simp [isCompQ])).mono ?_
      simpa [liftQ, isTh, isHm] using hmsgCost_mono hM
  · have hM : M.length ≤ ℓ := by
      simp only [liftQ, not_lt] at ht
      exact ht
    refine (cEmb_bound (X := Dsk →ₒ Bytes 16) _ _ (prfMsgC_bound k r M)
      (fun i => isCompQ i = true) (fun _ => rfl) (fun _ => by simp [isCompQ])).mono ?_
    simpa [liftQ] using prfMsgCost_mono hM

theorem chain_prf (hgame : IsQueryBoundP P qGame (qOPrf qs)) :
    IsQueryBoundP (chainA P) (fun i => isPrfQ i = true) (qOPrf qs) := by
  unfold chainA
  refine IsQueryBoundP.simulateQ_of_step hgame (fun t ht => ?_) (fun t ht => ?_)
  · rcases t with n | (q | d) | (h | m)
    · simp [liftQ] at ht
    · simp [liftQ] at ht
    · exact (isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos
    · simp [liftQ] at ht
    · simp [liftQ] at ht
  · rcases t with n | (q | d) | (h | m)
    · exact (isQueryBoundP_query_iff _ _ _).2 fun h => by simp [isPrfQ] at h
    · exact (isQueryBoundP_query_iff _ _ _).2 fun h => by simp [isPrfQ] at h
    · simp [liftQ] at ht
    · exact cEmb_zero (Xs := Dsk →ₒ Bytes 16) _ (fun i => isPrfQ i = true)
        (fun n => by simp [isPrfQ]) (fun c => by simp [isPrfQ])
    · exact cEmb_zero (Xs := Dsk →ₒ Bytes 16) _ (fun i => isPrfQ i = true)
        (fun n => by simp [isPrfQ]) (fun c => by simp [isPrfQ])

end Counts

/-! ## The realisers -/

section Realizers

variable (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
  (pkSeedDist : ProbComp (Bytes 16)) {qf qs ℓ : ℕ}
  (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List Byte) i = true) qf)
  (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List Byte) i = true) qs)
  (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQ (S := List Byte) ℓ i = true) 0)
  (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ)

include hqf hqs hlong hout

/-- **The `PRF` realiser of the SUF-CMA composition.** -/
noncomputable def realizesPrfSuf :
    RealizesPrf (fun g => Reduction.bPrfWC Reduction.sufCheck
      (S.typedS (optRandU oR) pkSeedDist g)) (qPrf qf qs ℓ) (qOPrf qs) :=
  have hF := Ideal.Realize.Msg.mainC_bounds S hqf hqs hlong hout
  RealizesPrf.ofEq (AprfS S oR pkSeedDist) (bPrfWC_eq_inst S oR pkSeedDist)
    (chain_comp _ (bPrfWCOpenP_port _ _ hF)
      (IsQueryBoundP.of_imp qTh_imp (bPrfWCOpenP_hash _ _ hF)) (bPrfWCOpenP_hm _ _ hF)
      (bPrfWCOpenP_pm _ _ hF) (bPrfWCOpenP_bad _ _ hF thB okLen_le))
    (chain_prf _ (bPrfWCOpenP_game _ _ hF))

/-- **The `PRF` realiser of the EUF-CMA composition.** -/
noncomputable def realizesPrfEuf :
    RealizesPrf (fun g => Reduction.bPrfC (S.typedE (optRandU oR) pkSeedDist g))
      (qPrf qf qs ℓ) (qOPrf qs) :=
  have hF := Ideal.Realize.Msg.mainC_bounds S hqf hqs hlong hout
  RealizesPrf.ofEq (AprfE S oR pkSeedDist) (bPrfC_eq_inst S oR pkSeedDist)
    (chain_comp _ (bPrfCOpenP_port _ _ hF)
      (IsQueryBoundP.of_imp qTh_imp (bPrfCOpenP_hash _ _ hF)) (bPrfCOpenP_hm _ _ hF)
      (bPrfCOpenP_pm _ _ hF) (bPrfCOpenP_bad _ _ hF thB okLen_le))
    (chain_prf _ (bPrfCOpenP_game _ _ hF))

end Realizers

/-! ## Closed forms -/

theorem qOPrf_128s (qs : ℕ) : qOPrf qs = 17920 + qs * 182784 := by
  unfold qOPrf
  rw [Resources.keygenReads_128s, Resources.signReads_128s]

/-- `qPrf` at SHA2-128s. -/
theorem qPrf_128s (qf qs ℓ : ℕ) :
    qPrf qf qs ℓ = qf + (269824 + qs * 2007385 + 3929) * 11 + (qs + 1) * ((ℓ + 56) / 64 + 3) +
      qs * ((ℓ + 24) / 64 + 4) := by
  unfold qPrf
  rw [hashN_128s, thashCost_thB]
  unfold hmsgCost prfMsgCost
  ring

/-- **Simple upper bound** on the compression queries of the `PRF` realisers (the same as
`Ideal.Realize.Msg.qMsg_le`). -/
theorem qPrf_le (qf qs ℓ : ℕ) : qPrf qf qs ℓ ≤ qf + (qs + 1) * (2 ^ 25 + 2 * ℓ) := by
  rw [qPrf_128s]
  have h1 : (ℓ + 56) / 64 ≤ ℓ + 1 := by omega
  have h2 : (ℓ + 24) / 64 * 64 ≤ ℓ + 24 := Nat.div_mul_le_self _ _
  nlinarith [Nat.zero_le qs, Nat.zero_le ℓ]

/-- Simple upper bound on the PRF-oracle queries of the `PRF` realisers. -/
theorem qOPrf_le (qs : ℕ) : qOPrf qs ≤ 2 ^ 18 * (qs + 1) := by
  rw [qOPrf_128s]
  omega

/-- Tighter form of `qPrf_le`. -/
theorem qPrf_le' (qf qs ℓ : ℕ) :
    qPrf qf qs ℓ ≤ qf + (qs + 1) * (22081242 + 2 * ((ℓ + 56) / 64)) := by
  rw [qPrf_128s]
  have h1 : (ℓ + 24) / 64 ≤ (ℓ + 56) / 64 := Nat.div_le_div_right (by omega)
  have h2 := Nat.mul_le_mul_left qs h1
  generalize (ℓ + 56) / 64 = x at *
  generalize (ℓ + 24) / 64 = y at *
  ring_nf
  ring_nf at h2
  omega

/-- Tighter form of `Ideal.Realize.Msg.qMsg_le` (below the class-TCR cap
`qf + (qs+1)·(25135729 + (ℓ+56)/64)` of `status/R-tcr.md`). -/
theorem qMsg_le' (qf qs ℓ : ℕ) :
    Ideal.Realize.Msg.qMsg qf qs ℓ ≤ qf + (qs + 1) * (22081238 + (ℓ + 56) / 64) := by
  rw [Ideal.Realize.Msg.qMsg_128s]
  nlinarith [Nat.zero_le qs, Nat.zero_le ℓ]

/-- A common cap on the compression queries of the `PRF` and `PRF_msg` realisers. -/
def QcPM (qf qs ℓ : ℕ) : ℕ := qf + (qs + 1) * (2 ^ 25 + 2 * ℓ)

/-- A cap on the PRF-oracle queries of the `PRF` realisers. -/
def NPM (qs : ℕ) : ℕ := 2 ^ 18 * (qs + 1)

/-- **The `Realizers.Le`-shaped bounds of the four realisers of this file and of `MsgReal`**
(fields `q`, `qO`, `qm`, `qOm`, `mlen`): `q = qPrf qf qs ℓ ≤ QcPM`, `qO = qOPrf qs ≤ NPM`,
`qm = qMsg qf qs ℓ ≤ QcPM`, `qOm = qs ≤ qs`, `mlen = ℓ ≤ 64·⌈ℓ/64⌉`. -/
theorem le_parts (qf qs ℓ : ℕ) :
    qPrf qf qs ℓ ≤ QcPM qf qs ℓ ∧ qOPrf qs ≤ NPM qs ∧
      Ideal.Realize.Msg.qMsg qf qs ℓ ≤ QcPM qf qs ℓ ∧ qs ≤ qs ∧ ℓ ≤ 64 * ((ℓ + 63) / 64) :=
  ⟨qPrf_le qf qs ℓ, qOPrf_le qs, Ideal.Realize.Msg.qMsg_le qf qs ℓ, le_rfl, by omega⟩

end Ideal.Realize.Prf

#print axioms Ideal.Realize.Prf.close_castP'
#print axioms Ideal.Realize.Prf.close_portP
#print axioms Ideal.Realize.Prf.bPrfWC_eq_inst
#print axioms Ideal.Realize.Prf.bPrfC_eq_inst
#print axioms Ideal.Realize.Prf.chain_comp
#print axioms Ideal.Realize.Prf.chain_prf
#print axioms Ideal.Realize.Prf.realizesPrfSuf
#print axioms Ideal.Realize.Prf.realizesPrfEuf
#print axioms Ideal.Realize.Prf.qPrf_128s
#print axioms Ideal.Realize.Prf.qOPrf_128s
#print axioms Ideal.Realize.Prf.qPrf_le
#print axioms Ideal.Realize.Prf.qOPrf_le
#print axioms Ideal.Realize.Prf.le_parts
#print axioms Ideal.Realize.Prf.qPrf_le'
#print axioms Ideal.Realize.Prf.qMsg_le'
