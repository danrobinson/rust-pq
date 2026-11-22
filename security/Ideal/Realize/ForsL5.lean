import Ideal.Realize.ForsRealize
import Ideal.Realize.PrfReal

/-!
# Per-arity compression counts for the FORS-leaf realisers (`status/TIGHT.md` §4.1, L5)

`q2Fors` charges every hash query of the FORS port program `thashCost len = 11` compression
queries.  A `Thash` evaluation on at most two values (`F`, `H`; all but `≈ 3.6·10^3` of the
`≈ 2.0·10^6` per signature) costs `thashCost 2 = 2`; `T_len` costs `11`, `T_k` `5`.  Here every
hash query is charged `2` and every LONG `Thash` query (more than two values) `9` more:

* `forsSignOpen_long`, `openKeygen_long`, `forsFindOpenP_long`: the port program makes at most
  `512 + qs·forsSignLong + 0` long `Thash` queries (`forsSignLong Link.vp = 3585`);
* `chainImplP_boundL`, `phase2C_boundL`: at most
  `q2ForsL qf qs ℓ = qf + 2·forsHashes qs + 9·(512 + 3585·qs) + (2qs+1)·hmsgCost ℓ`
  compression queries in the second phase (`q2ForsL_eq`: `= qf + 544286 + 3932321·qs +
  (2qs+1)·((ℓ+56)/64+3)`, against `q2Fors = qf + 2968229 + 21450308·qs + …`);
* `realizesDsprL_S/E`, `realizesForsTcrL_S/E`: the realisers of `ForsRealize.lean` (same
  adversaries, same experiments) with the parameters `pForsL`.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security TweakableHash

namespace Ideal.Realize.Fors

open Reduction Reduction.Open Reduction.Lazy Reduction.Resources2 Ideal.Realize

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- A `Thash` query on more than two values (`T_len`, `T_k`). -/
def isLongIdx {ι P K Y : Type} : ℕ ⊕ (ι ⊕ (SecIdx ⊕ PublicHashQuery P K Y)) → Bool
  | .inr (.inr (.inr (.thash _ _ xs))) => decide (2 < xs.length)
  | _ => false

section Generic

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]

attribute [local instance] Lazy.openQ

theorem long_liftIdx (t : (OSpec prims (forsG prims)).Domain) :
    isLongIdx (liftIdx (prims := prims) t) = isLongIdx t := by
  rcases t with n | i | d | q
  · rfl
  · rfl
  · rfl
  · cases q <;> rfl

/-- Long `Thash` queries of one open FORS signature: one `T_k`, and per hypertree layer one
`T_len` per XMSS leaf and one for the root recovery. -/
def forsSignLong (vp : ValidatedParams) : ℕ :=
  0 + vp.params.k * Lazy.authB 0 0 vp.params.a + vp.params.k * 0 +
    (vp.params.k * (0 + vp.params.a * 0) + 1) +
    vp.params.d * (Lazy.xmssSignB vp 0 1 0 0 + Lazy.xmssPkB vp 0 1 0)

theorem forsSignLong_128s : forsSignLong Link.vp = 3585 := by decide

theorem forsSignOpen_long (pk : PublicKeyCore prims.core) (ys : List prims.Y) (m : List Byte)
    (R : prims.Y) :
    IsQueryBoundP (forsSignOpen pk ys m R) (fun t => isLongIdx t = true) (forsSignLong vp) := by
  have hf : ∀ (a : Adrs) (y : prims.core.Y), IsQueryBoundP (PublicHash.f prims.core pk.pkSeed a y :
      OracleComp (Lazy.OSpec prims (forsG prims)) prims.Y) (fun t => isLongIdx t = true) 0 :=
    fun _ _ => (isQueryBoundP_query_iff _ _ _).2 fun h => by simp [isLongIdx] at h
  have htl : ∀ (a : Adrs) (ys : List prims.core.Y),
      IsQueryBoundP (PublicHash.tl prims.core pk.pkSeed a ys :
      OracleComp (Lazy.OSpec prims (forsG prims)) prims.Y) (fun t => isLongIdx t = true) 1 :=
    fun _ _ => (isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos
  have hh : ∀ (a : Adrs) (l r : prims.core.Y),
      IsQueryBoundP (PublicHash.h prims.core pk.pkSeed a l r :
      OracleComp (Lazy.OSpec prims (forsG prims)) prims.Y) (fun t => isLongIdx t = true) 0 :=
    fun _ _ _ => (isQueryBoundP_query_iff _ _ _).2 fun h => by simp [isLongIdx] at h
  have hs : ∀ a : Adrs, IsQueryBoundP (Lazy.secQ prims (forsG prims) a)
      (fun t => isLongIdx t = true) 0 :=
    fun _ => (isQueryBoundP_query_iff _ _ _).2 fun h => by simp [isLongIdx] at h
  have hm : IsQueryBoundP (PublicHash.hmsg prims.core R pk.pkSeed pk.pkRoot m :
      OracleComp (Lazy.OSpec prims (forsG prims)) _) (fun t => isLongIdx t = true) 0 :=
    (isQueryBoundP_query_iff _ _ _).2 fun h => by simp [isLongIdx] at h
  have himg : ∀ (md : List Byte) (adrs : Adrs),
      IsQueryBoundP (forsSignWithSecret prims.core (forsImgHashO pk.pkSeed)
          (PublicHash.h prims.core pk.pkSeed)
          (fun a => (pure (leafImage (vp := vp) ys (skToLeaf a)) :
            OracleComp (Lazy.OSpec prims (forsG prims)) prims.Y)) md adrs)
        (fun t => isLongIdx t = true)
        (vp.params.k * Lazy.authB 0 0 vp.params.a) := by
    intro md adrs
    refine Lazy.qb_ofFnM _ _ _ fun i => ?_
    have h := Lazy.qb_authPath (fun t => isLongIdx t = true)
      (forsLeafWithSecret prims.core (forsImgHashO pk.pkSeed)
        (fun a => (pure (leafImage (vp := vp) ys (skToLeaf a)) :
          OracleComp (Lazy.OSpec prims (forsG prims)) prims.Y)) adrs)
      (forsNodeHashWith (PublicHash.h prims.core pk.pkSeed) adrs) 0 0
      (i.val * 2 ^ vp.params.a + forsIdx vp.params md i.val) vp.params.a
      (fun j => by
        unfold forsLeafWithSecret
        rw [pure_bind, forsImgHashO_leaf]
        exact isQueryBoundP_pure _ _ _)
      (fun h i l r => hh _ l r)
    exact (Lazy.qb_bind _ (n := 0) (isQueryBoundP_pure _ _ _) fun sk =>
      Lazy.qb_bind _ (m := 0) h fun path => isQueryBoundP_pure _ _ _).mono (by omega)
  unfold forsSignOpen
  refine (Lazy.qb_bind _ hm fun digest =>
    Lazy.qb_bind _ (himg _ _) fun img =>
      Lazy.qb_bind _ (Lazy.qb_ofFnM _ _ 0 fun i =>
          Lazy.qb_bind _ (m := 0) ((isQueryBoundP_query_iff _ _ _).2 fun h => by
            simp [isLongIdx] at h) fun x =>
            isQueryBoundP_pure _ _ _) fun forsSig =>
        Lazy.qb_bind _ (Lazy.qb_forsPk _ prims.core _ _ _ hf htl hh forsSig _ _) fun forsPk =>
          Lazy.qb_bind _ (m := 0)
            (Lazy.qb_signFromPos _ prims.core _ _ _ _ hf htl hh hs _ _ _ _ _)
            fun htSig => isQueryBoundP_pure _ _ _).mono ?_
  unfold forsSignLong
  omega

/-- Long `Thash` queries of open key generation: one `T_len` per leaf of the top tree. -/
theorem openKeygen_long {ι : Type} {gspec : OracleSpec ι} (pkSeed : prims.PkSeed) :
    IsQueryBoundP (Lazy.openKeygen prims gspec pkSeed) (fun t => isLongIdx t = true)
      (Lazy.merkleB (Lazy.wotsB vp 0 0 + 1) 0 vp.params.hp) :=
  Lazy.qb_xmssNode (fun t => isLongIdx t = true) prims.core 0 1 0 0
    (hash := PublicHash.f prims.core pkSeed) (compress := PublicHash.tl prims.core pkSeed)
    (nodeHash := PublicHash.h prims.core pkSeed) (secret := Lazy.secQ prims gspec)
    (fun _ _ => (isQueryBoundP_query_iff _ _ _).2 fun h => by simp [isLongIdx] at h)
    (fun _ _ => (isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos)
    (fun _ _ _ => (isQueryBoundP_query_iff _ _ _).2 fun h => by simp [isLongIdx] at h)
    (fun _ => (isQueryBoundP_query_iff _ _ _).2 fun h => by simp [isLongIdx] at h) _ _ _

theorem keygenLongF_128s : Lazy.merkleB (Lazy.wotsB Link.vp 0 0 + 1) 0 Link.vp.params.hp = 512 := by
  decide

variable (optRand : PublicKeyCore prims.core → ProbComp prims.Y) (mainP : PortForgerProg vp prims)
  (pkSeed : prims.PkSeed) (ys : List prims.Y)

/-- **Long `Thash` queries of the FORS port program.** -/
theorem forsFindOpenP_long (qs : ℕ)
    (hqs : ∀ pk, IsQueryBoundP (mainP pk)
      (fun i => isSignQ (S := GeneralScheme.SignatureCore vp prims.core) i = true) qs) :
    IsQueryBoundP (forsFindOpenP optRand mainP pkSeed ys) (fun t => isLongIdx t = true)
      (Lazy.merkleB (Lazy.wotsB vp 0 0 + 1) 0 vp.params.hp + qs * forsSignLong vp) := by
  have hu : ∀ n, ¬ isLongIdx (ι := ℕ ⊕ (St × Blk)) (P := prims.PkSeed) (K := prims.AdrsKey)
      (Y := prims.Y) (.inl n) = true := by intro n; simp [isLongIdx]
  have hl : ∀ {β : Type} (oa : OracleComp (OSpec prims (forsG prims)) β) (n : ℕ),
      IsQueryBoundP oa (fun t => isLongIdx t = true) n →
      IsQueryBoundP (simulateQ liftG oa) (fun t => isLongIdx t = true) n :=
    fun oa n h => liftG_bound _ oa n (IsQueryBoundP.of_imp (fun t ht => by
      rwa [long_liftIdx] at ht) h)
  unfold forsFindOpenP
  refine (isQueryBoundP_bind (hl _ _ (openKeygen_long pkSeed)) fun root _ =>
    isQueryBoundP_bind (n := qs * forsSignLong vp) (m := 0) ?_ fun z hz =>
      hl _ _ ((findAnswerO_le (fun t => isLongIdx t = true) ⟨pkSeed, root⟩ ys z.2 z.1.1 z.1.2 0 0
        (fun key y => by simp [isLongIdx])
        ((isQueryBoundP_query_iff _ _ _).2 fun h => by simp [isLongIdx] at h)
        (fun e _ => (isQueryBoundP_query_iff _ _ _).2 fun h => by simp [isLongIdx] at h)).mono
          (by simp))).mono (by omega)
  unfold portRunF
  refine IsQueryBoundP.simulateQ_run_of_step_le (hqs _) (fun t ht s => ?_) (fun t ht s => ?_) []
  · rcases t with n | q | msg
    · simp [isSignQ] at ht
    · simp [isSignQ] at ht
    · exact signStepF optRand _ ys _ hu msg _ (fun R => hl _ _ (forsSignOpen_long _ ys msg R)) s
  · rcases t with n | q | msg
    · exact unifStepF optRand _ ys _ hu n s
    · exact portStepF optRand _ ys _ q 0 ((isQueryBoundP_query_iff _ _ _).2 fun h => by
        simp [isLongIdx] at h) s
    · simp [isSignQ] at ht

end Generic

/-! ## Compression queries -/

theorem thashCost_le_L (n : ℕ) (h : n ≤ 35) : thashCost n ≤ 2 + (if 2 < n then 9 else 0) := by
  unfold thashCost
  split_ifs with hl <;> omega

/-- **Port queries of the chain interpretation, per-arity costs**: `2` per hash query, `9` more
per long `Thash` query, `hmsgCost ℓ` per `H_msg` query. -/
theorem chainImplP_boundL (tbl : SecIdx → P₀.Y) (B ℓ : ℕ) {β : Type}
    (P : OracleComp (OSpec P₀ (GP P₀)) β) {n₁ n₂ n₃ n₄ : ℕ}
    (h0 : IsQueryBoundP P (fun t => isBadIdx B ℓ t = true) 0)
    (h1 : IsQueryBoundP P (fun t => isPortIdx t = true) n₁)
    (h2 : IsQueryBoundP P (fun t => Lazy.kind t = .hash) n₂)
    (h3 : IsQueryBoundP P (fun t => isHmsgIdx t = true) n₃)
    (h4 : IsQueryBoundP P (fun t => isLongIdx t = true) n₄) (hB : B ≤ Link.vp.params.len) :
    IsQueryBoundP (simulateQ (chainImplP tbl) P) (fun t => isPortI t = true)
      (n₁ * 1 + n₂ * 2 + n₃ * hmsgCost ℓ + n₄ * 9) := by
  refine Prf.qb_simulateQ_classes4 1 2 (hmsgCost ℓ) 9 (fun t ht => ?_) h0 h1 h2 h3 h4
  rcases t with n | (i | q) | d | (⟨pk, a, xs⟩ | ⟨R, pk, root, M⟩)
  · exact ((isQueryBoundP_query_iff _ _ _).2 fun h => by simp [isPortI] at h).mono (Nat.zero_le _)
  · exact ((isQueryBoundP_query_iff _ _ _).2 fun h => by simp [isPortI] at h).mono (Nat.zero_le _)
  · refine ((isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos).mono ?_
    simp only [isPortIdx, ↓reduceIte]
    omega
  · exact (isQueryBoundP_pure _ _ _).mono (Nat.zero_le _)
  · have hxs : xs.length ≤ B := by simpa [isBadIdx] using ht
    have hx35 : xs.length ≤ 35 := hxs.trans (hB.trans (by decide))
    refine (liftCS_bound _ _ (thashC_bound pk a xs)).mono
      ((thashCost_le_L xs.length hx35).trans ?_)
    by_cases hl : 2 < xs.length
    · simp [isPortIdx, Lazy.kind, isHmsgIdx, isLongIdx, hl]
    · simp [isPortIdx, Lazy.kind, isHmsgIdx, isLongIdx, hl]
  · have hM : M.length ≤ ℓ := by simpa [isBadIdx] using ht
    refine (liftCS_bound _ _ (hmsgC_bound R pk root M)).mono ?_
    simp only [isPortIdx, Lazy.kind, isHmsgIdx, isLongIdx]
    have := hmsgCost_mono hM
    simp
    omega

/-- **Compression queries of the second phase, per-arity costs.** -/
def q2ForsL (qf qs ℓ : ℕ) : ℕ :=
  qf * 1 + forsHashes qs * 2 + (qs + (1 + qs)) * hmsgCost ℓ +
    (Lazy.merkleB (Lazy.wotsB Link.vp 0 0 + 1) 0 Link.vp.params.hp + qs * forsSignLong Link.vp) * 9

theorem phase2C_boundL {β : Type} (post : List (P₀.AdrsKey × P₀.Y) → (ℕ × P₀.Y) × List ℕ → β)
    (optRand : PublicKeyCore P₀.core → ProbComp P₀.Y) (mainP : PortForgerProg Link.vp P₀)
    (qf qs ℓ : ℕ)
    (hqf : ∀ pk, IsQueryBoundP (mainP pk)
      (fun i => isPortQ (S := GeneralScheme.SignatureCore Link.vp P₀.core) i = true) qf)
    (hqs : ∀ pk, IsQueryBoundP (mainP pk)
      (fun i => isSignQ (S := GeneralScheme.SignatureCore Link.vp P₀.core) i = true) qs)
    (hlong : ∀ pk, IsQueryBoundP (mainP pk)
      (fun i => isLongQ (S := GeneralScheme.SignatureCore Link.vp P₀.core) ℓ i = true) 0)
    (hout : ∀ pk, ∀ z ∈ support (mainP pk), z.1.length ≤ ℓ)
    (tbl : SecIdx → P₀.Y) (tg : List (P₀.AdrsKey × P₀.Y)) (ys : List P₀.Y) (pk : P₀.PkSeed) :
    IsQueryBoundP (phase2C post optRand mainP tbl tg ys pk) (fun i => i.isRight = true)
      (q2ForsL qf qs ℓ) := by
  unfold phase2C
  refine (isQueryBoundP_bind (m := 0) (outerC_bound tg _ _ (chainImplP_boundL tbl
    Link.vp.params.len ℓ _
    (forsFindOpenP_bad optRand mainP pk ys _ ℓ okLen_le hlong hout)
    (forsFindOpenP_port optRand mainP pk ys qf hqf)
    (forsFindOpenP_hashes optRand mainP pk ys qs hqs)
    (forsFindOpenP_hmsg optRand mainP pk ys qs hqs)
    (forsFindOpenP_long optRand mainP pk ys qs hqs) le_rfl) []) fun z _ =>
      isQueryBoundP_pure _ _ _).mono ?_
  unfold q2ForsL forsHashes
  omega

theorem q2ForsL_eq (qf qs ℓ : ℕ) :
    q2ForsL qf qs ℓ = qf + 544286 + 3932321 * qs + (2 * qs + 1) * ((ℓ + 56) / 64 + 3) := by
  unfold q2ForsL
  rw [forsHashes_eq, keygenLongF_128s, forsSignLong_128s]
  unfold hmsgCost
  ring_nf

theorem q2ForsL_le_q2Fors (qf qs ℓ : ℕ) : q2ForsL qf qs ℓ ≤ q2Fors qf qs ℓ := by
  rw [q2ForsL_eq, q2Fors_eq]
  nlinarith [Nat.zero_le qs]

/-- Query parameters of the FORS-leaf realisers with per-arity costs. -/
def pForsL (qf qs ℓ : ℕ) : P3 := ⟨0, openPreTargets Link.vp, q2ForsL qf qs ℓ⟩

theorem pForsL_le_of {qf qs ℓ Qc N : ℕ} (h : (pFors qf qs ℓ).Le Qc N) :
    (pForsL qf qs ℓ).Le Qc N :=
  ⟨h.1, h.2.1, (q2ForsL_le_q2Fors qf qs ℓ).trans h.2.2⟩

/-! ## The realisers -/

section Realizers

variable (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
  (pkSeedDist : ProbComp (Bytes 16)) {qf qs ℓ : ℕ}
  (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List Byte) i = true) qf)
  (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List Byte) i = true) qs)
  (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQ (S := List Byte) ℓ i = true) 0)
  (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ)

include hqf hqs hlong hout

theorem dsprAdvI_guessL : (dsprAdvI S oR pkSeedDist).GuessBound (q2ForsL qf qs ℓ) := by
  unfold DsprAdv.GuessBound dsprAdvI
  intro st pk
  exact phase2C_boundL _ _ _ qf qs ℓ (mainP_port S hqf) (mainP_sign S hqs)
    (mainP_long S hlong) (mainP_out S hout) _ _ _ pk

theorem tcrAdvI_forgeL : (tcrAdvI S oR pkSeedDist).ForgeBound (q2ForsL qf qs ℓ) := by
  unfold FvAdv.ForgeBound tcrAdvI
  intro st pk
  exact phase2C_boundL (β := ℕ × P₀.Y) (fun _ z => forsTcrPost z) (optRand₀ oR dT dH) (mainP S)
    qf qs ℓ (mainP_port S hqf) (mainP_sign S hqs)
    (mainP_long S hlong) (mainP_out S hout) st.1 st.2.1 st.2.2 pk

/-- **FORS-leaf SM-DSPR realiser, SUF forger, per-arity costs.** -/
noncomputable def realizesDsprL_S :
    RealizesDspr pkSeedDist
      (fun g => Reduction.toDspr (Reduction.Lazy.bOpenPreS (S.typedS (optRandU oR) pkSeedDist g)))
      (pForsL qf qs ℓ) :=
  { realizesDspr_S S oR pkSeedDist hqf hqs hlong hout with
    hq₂ := dsprAdvI_guessL S oR pkSeedDist hqf hqs hlong hout }

/-- **FORS-leaf SM-DSPR realiser, EUF forger, per-arity costs.** -/
noncomputable def realizesDsprL_E :
    RealizesDspr pkSeedDist
      (fun g => Reduction.toDspr (Reduction.Lazy.bOpenPreS (S.typedE (optRandU oR) pkSeedDist g)))
      (pForsL qf qs ℓ) :=
  { realizesDspr_E S oR pkSeedDist hqf hqs hlong hout with
    hq₂ := dsprAdvI_guessL S oR pkSeedDist hqf hqs hlong hout }

/-- **FORS-leaf SM-TCR realiser, SUF forger, per-arity costs.** -/
noncomputable def realizesForsTcrL_S :
    RealizesForsTcr pkSeedDist
      (fun g => Reduction.toTcr (Reduction.Lazy.bOpenPreS (S.typedS (optRandU oR) pkSeedDist g)))
      (pForsL qf qs ℓ) :=
  { realizesForsTcr_S S oR pkSeedDist hqf hqs hlong hout with
    hq₂ := tcrAdvI_forgeL S oR pkSeedDist hqf hqs hlong hout }

/-- **FORS-leaf SM-TCR realiser, EUF forger, per-arity costs.** -/
noncomputable def realizesForsTcrL_E :
    RealizesForsTcr pkSeedDist
      (fun g => Reduction.toTcr (Reduction.Lazy.bOpenPreS (S.typedE (optRandU oR) pkSeedDist g)))
      (pForsL qf qs ℓ) :=
  { realizesForsTcr_E S oR pkSeedDist hqf hqs hlong hout with
    hq₂ := tcrAdvI_forgeL S oR pkSeedDist hqf hqs hlong hout }

end Realizers

end Ideal.Realize.Fors

#print axioms Ideal.Realize.Fors.forsSignOpen_long
#print axioms Ideal.Realize.Fors.openKeygen_long
#print axioms Ideal.Realize.Fors.forsFindOpenP_long
#print axioms Ideal.Realize.Fors.chainImplP_boundL
#print axioms Ideal.Realize.Fors.phase2C_boundL
#print axioms Ideal.Realize.Fors.q2ForsL_eq
#print axioms Ideal.Realize.Fors.q2ForsL_le_q2Fors
#print axioms Ideal.Realize.Fors.realizesDsprL_S
#print axioms Ideal.Realize.Fors.realizesDsprL_E
#print axioms Ideal.Realize.Fors.realizesForsTcrL_S
#print axioms Ideal.Realize.Fors.realizesForsTcrL_E
