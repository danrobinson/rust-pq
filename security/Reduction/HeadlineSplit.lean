import Reduction.Headline
import Reduction.TcrSplitClosed

/-!
# The final theorems with the `Thash` SM-TCR term split by arity class

`Reduction/Headline.lean` has one cross-arity term `Adv^{SM-TCR}_{Thash}(bTcrS A)`, in a game on
the variable-arity `Thash` in which a collision between inputs of different lengths also wins.
Here that term is replaced, in all four final theorems (internal/external, SUF/EUF), by

`Adv^{SM-TCR}_{Thash|1}(bTcrArS 1 A) + Adv^{SM-TCR}_{Thash|2}(bTcrArS 2 A)
   + Adv^{SM-TCR}_{Thash|len}(bTcrArS len A) + Adv^{SM-TCR}_{Thash|k}(bTcrArS k A)`.

**Games.**  `thashArityProblem vp prims pkSeedDist n` (`Reduction/TcrSplitFinal.lean`) is
VCVio's `SM_DT_TCR_Problem` — the same experiment `SM_DT_TCR_Experiment` as every other SM-TCR
term — whose target function is `Thash` restricted to inputs of exactly `n` blocks (message type
`{xs : List Y // xs.length = n}`), whose collection oracle evaluates the whole `Thash` at
non-target tweaks, and whose cap is `tcrTargets vp`.  A win is a second input **of the same
length `n`** colliding with a registered target.  In FIPS 205 terms (`F`, `H`, `T_l` are `Thash`
at 1, 2, `l` blocks; in the SHA2-128s bundle all are
`Trunc_n(SHA-256(PK.seed ‖ toByte(0, 64 − n) ‖ ADRSc ‖ M))` with `M` the concatenation of `xs`):

* `n = 1` — a genuine SM-TCR game on `F` (inputs: one `n`-byte block);
* `n = 2` — a genuine SM-TCR game on `H`;
* `n = len` — a genuine SM-TCR game on `T_len`;
* `n = k` — a genuine SM-TCR game on `T_k`.

**Relation to the paper's terms** (Hülsing–Kudinov Thm 1 / EasyCrypt `EUFCMA_SPHINCS_PLUS` have
TCR(FORS tree) + TCR(FORS roots) + TCR(WOTS pk) + TCR(XMSS tree) at this place).  The split is by
arity, not by address type:

* class `2` contains the FORS-tree nodes **and** the XMSS-tree nodes: the paper's two `H` terms
  are one term here (same function, one target set of both kinds);
* class `len` is the paper's TCR(WOTS pk) term, class `k` its TCR(FORS roots) term;
* class `1` is an **extra** `F` term (targets: FORS leaves and WOTS+ chain steps of the key
  structure) that the paper does not have at this place — a collision found by re-running
  verification may be at an `F` call.  It is in addition to the two other `F`-TCR terms
  (`3·TCR(F)` at FORS leaves, `TCR(F)` on chains), which are in other games and are unchanged;
* if two of `1, 2, len, k` coincide for a parameter set, the coinciding terms are the same
  advantage counted twice (not at SHA2-128s: `arities_injective_128s`, `1, 2, 35, 14`).

**Adversaries.**  `bTcrArS n A := TcrSplit.restrict (·.length = n) _ (Lazy.bTcrS A)`: runs the
sparse adversary `bTcrS A` once (its `choose`, then its `forge`); of the hash calls of the key
structure it forwards those of arity `n` to the challenge oracle and the others to the collection
oracle (`TcrSplit.route`); the collision found by `bTcrS A` is forwarded iff both inputs have
arity `n`.  No choice principle, no eager table (`scratch/Final/FinalCheck.lean`).

**Resources** (`bTcrArS_choose_run`, `bTcrArS_targets`, `arityTargets_128s`): in its game,
`bTcrArS n A` registers exactly the arity-`n` hash calls of the key structure as targets —
`arityTargets vp n` of them, closed form — and sends the remaining `tcrTargets vp − arityTargets
vp n` calls to the collection oracle; it draws the same `(structSecIdx vp).length` samples as
`bTcrS A`.  The cap of each class game is still `tcrTargets vp` (not the per-class count); the
same bounds in games capped at `arityTargets vp n` are in `Reduction/TightCapsHeadline.lean`.
Own hashing (`Reduction/Resources2Tcr.lean`): after the seed is revealed each `bTcrArS n A`
recomputes the whole key structure, exactly `tcrTargets vp` hash evaluations (`≈ 2^79.81` at
SHA2-128s, `Resources2.tcr_structure_exact`), so all four are structure-size in local work too.

Why the split is made at the event level: `Adv(bTcrS A) ≤ Σ_n Adv_n(bTcrArS n A)` is not claimed
(when verification yields no collision `bTcrS A` outputs the fixed guess `(0, [])`, which could
win by a cross-arity collision).  What is proved is that the *collision event of `G2`*
(`evColl`, resp. `class = tcr`) — the only thing the cross-arity term was used for — is covered
by the four class games, because verification and the honest structure agree on arities
(`verifyAritySound`).
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal

namespace Reduction

open TweakableHash

set_option linter.unusedSectionVars false

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]
variable {optRand : PublicKeyCore prims.core → ProbComp prims.Y}
  {pkSeedDist : ProbComp prims.PkSeed}

/-! ## The restricted adversaries derived from the sparse adversary -/

/-- The arity-`n` SM-TCR adversary derived from the sparse adversary `bTcrS A`. -/
noncomputable def bTcrArS (n : ℕ) (A : Forger vp prims optRand pkSeedDist) :
    SM_DT_TCR_Adversary (thashArityProblem vp prims pkSeedDist n) :=
  TcrSplit.restrict (fun xs => xs.length = n) (arityDefault prims n) (Lazy.bTcrS A)

/-- The four per-arity SM-TCR terms at the sparse adversary: `F`, `H`, `T_len`, `T_k`. -/
noncomputable def tcrSplitSumS (A : Forger vp prims optRand pkSeedDist) : ℝ≥0∞ :=
  SM_DT_TCR_Advantage (bTcrArS 1 A) + SM_DT_TCR_Advantage (bTcrArS 2 A) +
    SM_DT_TCR_Advantage (bTcrArS vp.params.len A) + SM_DT_TCR_Advantage (bTcrArS vp.params.k A)

theorem sum_aritiesS_eq (A : Forger vp prims optRand pkSeedDist) :
    ∑ i, SM_DT_TCR_Advantage (bTcrArS (arities vp i) A) = tcrSplitSumS A := by
  rw [Fin.sum_univ_four]
  rfl

/-- **The restricted adversary wins exactly when `bTcrS A` wins by an arity-`n` collision.** -/
theorem bTcrArS_advantage_eq (n : ℕ) (A : Forger vp prims optRand pkSeedDist) :
    SM_DT_TCR_Advantage (bTcrArS n A) =
      𝒟[TcrSplit.winIn (thashList vp prims pkSeedDist) (fun xs => xs.length = n) <$>
        TcrSplit.raw (Lazy.bTcrS A)] {true} :=
  TcrSplit.restrict_advantage_eq _ _ _

/-- The common experiment of the split at `bTcrS A`, with the `choose` phase evaluated. -/
theorem raw_bTcrS (hS : Structural vp prims) (A : Forger vp prims optRand pkSeedDist) :
    TcrSplit.raw (Lazy.bTcrS A) = (do
      let pkSeed ← pkSeedDist
      let tbl ← Lazy.sparseTable vp prims
      let r ← g2Run A tbl (idealPk vp prims tbl pkSeed)
      pure (pkSeed, honestCalls tbl pkSeed,
        (findCollision pkSeed (honestCalls tbl pkSeed)
          (verifyCalls (idealPk vp prims tbl pkSeed) r.1.1 r.1.2)).getD (0, []))) := by
  unfold TcrSplit.raw
  refine bind_congr fun pkSeed => ?_
  have h := Lazy.bTcrS_choose_run hS A pkSeed
  refine (congrArg (· >>= _) h).trans ?_
  rw [map_eq_bind_pure_comp]
  refine (bind_assoc _ _ _).trans ?_
  refine bind_congr fun tbl => ?_
  refine (pure_bind _ _).trans ?_
  refine (bind_assoc (g2Run A tbl (idealPk vp prims tbl pkSeed)) _ _).trans ?_
  refine bind_congr fun r => ?_
  exact pure_bind _ _

/-- **Collision branch, split.**  The collision event of `G2` (sparse table) is covered by the
four class games at the restricted sparse adversaries. -/
theorem brS_coll_split (hS : Structural vp prims) (A : Forger vp prims optRand pkSeedDist) :
    prTrue (g2WithS A evColl) ≤ tcrSplitSumS A := by
  rw [← sum_aritiesS_eq]
  let E : TcrSplit.Raw prims.PkSeed prims.AdrsKey prims.Y → Bool := fun r =>
    decide (∃ i : Fin 4, TcrSplit.winIn (thashList vp prims pkSeedDist)
      (fun xs => xs.length = arities vp i) r = true)
  have hsum := TcrSplit.prEvent_le_sum_restrict
    (fun (i : Fin 4) (xs : List prims.Y) => xs.length = arities vp i)
    (fun i => arityDefault prims (arities vp i)) (Lazy.bTcrS A) E
    (fun r hr => by simpa [E] using hr)
  refine le_trans ?_ hsum
  rw [raw_bTcrS hS A]
  unfold prTrue g2WithS
  simp only [map_bind, map_pure]
  rw [← prEvent_eq_evalDist_singleton, ← prEvent_eq_evalDist_singleton]
  refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun pkSeed => ?_
  refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun tbl => ?_
  refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun r => ?_
  obtain ⟨⟨msg, sig⟩, log⟩ := r
  unfold evColl
  dsimp only
  by_cases hv : (findCollision pkSeed (honestCalls tbl pkSeed)
      (verifyCalls (idealPk vp prims tbl pkSeed) msg sig)).isSome = true
  · obtain ⟨⟨j, m⟩, hjm⟩ := Option.isSome_iff_exists.mp hv
    obtain ⟨c, hc, t, ht, rfl, hkey, hne, heq⟩ := findCollision_spec _ _ _ j m hjm
    obtain ⟨hlen, i, hi⟩ :=
      verifyAritySound hS tbl pkSeed msg sig c hc t (List.mem_of_getElem? ht) hkey
    have hE : E (pkSeed, honestCalls tbl pkSeed,
        (findCollision pkSeed (honestCalls tbl pkSeed)
          (verifyCalls (idealPk vp prims tbl pkSeed) msg sig)).getD (0, [])) = true := by
      rw [hjm]
      simp only [E, decide_eq_true_eq]
      refine ⟨i, ?_⟩
      simp only [TcrSplit.winIn, Option.getD_some, ht, decide_eq_true_eq]
      exact ⟨hi, hlen.trans hi, hne, heq⟩
    rw [hE]
    simp [hv]
  · rw [Bool.not_eq_true] at hv
    rw [hv]
    simp

/-- In `G2`, a forgery of class `tcr` yields a collision (sparse table). -/
theorem g2Class_tcr_le_coll (hS : Structural vp prims) (A : Forger vp prims optRand pkSeedDist) :
    prTrue (g2Class A .tcr) ≤ prTrue (g2WithS A evColl) := by
  rw [Lazy.prTrue_g2Class_eq_sparse hS A .tcr]
  unfold prTrue g2WithS
  rw [← prEvent_eq_evalDist_singleton, ← prEvent_eq_evalDist_singleton]
  refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun pkSeed => ?_
  refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun tbl => ?_
  unfold Lazy.g2ClassAt
  refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun r => ?_
  obtain ⟨⟨msg, sig⟩, log⟩ := r
  unfold evColl
  dsimp only
  by_cases hv : (g2Valid (idealPk vp prims tbl pkSeed) log msg sig &&
      decide (g2ClassOf tbl (idealPk vp prims tbl pkSeed) log msg sig = .tcr)) = true
  · rw [Bool.and_eq_true, decide_eq_true_eq] at hv
    have hsome := findCollision_isSome_of_tcr hS tbl pkSeed log msg sig hv.1 hv.2
    rw [hsome]
    simp [hv.1, hv.2]
  · rw [Bool.not_eq_true] at hv
    rw [hv]
    simp

/-- **Step 6, split, at the sparse adversary** (unconditional):
`Pr[G2 ∧ class = tcr] ≤ Σ_{n ∈ {1, 2, len, k}} Adv^{SM-TCR}_{Thash|n}(bTcrArS n A)`. -/
theorem stepTCR_split_sparse (hS : Structural vp prims)
    (A : Forger vp prims optRand pkSeedDist) :
    prTrue (g2Class A .tcr) ≤ tcrSplitSumS A :=
  (g2Class_tcr_le_coll hS A).trans (brS_coll_split hS A)

/-- **Union bound over the four chargeable events of `G2`, with the collision branch split.** -/
theorem g2WithS_le_split (hS : Structural vp prims) (A : Forger vp prims optRand pkSeedDist)
    (win : prims.PkSeed → SecretTable vp prims → G2Out vp prims → Bool)
    (hwin : ∀ pkSeed tbl z, win pkSeed tbl z = true →
      evItsr pkSeed tbl z = true ∨ evOpen pkSeed tbl z = true ∨
        evColl pkSeed tbl z = true ∨ evWots pkSeed tbl z = true) :
    prTrue (g2WithS A win) ≤
      KeyedHash.ITSRAdvantage (Lazy.bItsrL A) +
        SM_DT_OpenPRE_SourceFinalValidity.advantage (Lazy.bOpenPreS A) +
        tcrSplitSumS A +
        ((vp.params.w - 2 : ℕ) : ℝ≥0∞) * SM_DT_UD_Advantage (rUd pkSeedDist (Lazy.bWotsS A)) +
        SM_DT_PRE_Advantage (rPre pkSeedDist (Lazy.bWotsS A)) +
        SM_DT_TCR_Advantage (rTcr pkSeedDist (Lazy.bWotsS A)) := by
  have h1 := g2WithS_le_add A win evItsr
    (fun pkSeed tbl z => evOpen pkSeed tbl z || (evColl pkSeed tbl z || evWots pkSeed tbl z))
    (fun pkSeed tbl z h => by
      rcases hwin pkSeed tbl z h with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by rw [h]; rfl)
      · exact Or.inr (by rw [h]; simp)
      · exact Or.inr (by rw [h]; simp))
  have h2 := g2WithS_le_add A
    (fun pkSeed tbl z => evOpen pkSeed tbl z || (evColl pkSeed tbl z || evWots pkSeed tbl z))
    evOpen (fun pkSeed tbl z => evColl pkSeed tbl z || evWots pkSeed tbl z)
    (fun pkSeed tbl z h => by simpa [Bool.or_eq_true] using h)
  have h3 := g2WithS_le_add A
    (fun pkSeed tbl z => evColl pkSeed tbl z || evWots pkSeed tbl z) evColl evWots
    (fun pkSeed tbl z h => by simpa [Bool.or_eq_true] using h)
  have hud := stepWotsUD hS pkSeedDist (Lazy.bWotsS A)
  have hfin := stepWotsFinal hS pkSeedDist (Lazy.bWotsS A)
  unfold StepWotsUD at hud
  unfold StepWotsFinal at hfin
  have hw := (brS_wots hS A).trans (hud.trans (add_le_add_left hfin _))
  calc prTrue (g2WithS A win)
      ≤ prTrue (g2WithS A evItsr) + (prTrue (g2WithS A evOpen) +
          (prTrue (g2WithS A evColl) + prTrue (g2WithS A evWots))) :=
        h1.trans (add_le_add_right (h2.trans (add_le_add_right h3 _)) _)
    _ ≤ KeyedHash.ITSRAdvantage (Lazy.bItsrL A) +
          (SM_DT_OpenPRE_SourceFinalValidity.advantage (Lazy.bOpenPreS A) +
          (tcrSplitSumS A +
          (SM_DT_PRE_Advantage (rPre pkSeedDist (Lazy.bWotsS A)) +
              SM_DT_TCR_Advantage (rTcr pkSeedDist (Lazy.bWotsS A)) +
            ((vp.params.w - 2 : ℕ) : ℝ≥0∞) *
              SM_DT_UD_Advantage (rUd pkSeedDist (Lazy.bWotsS A))))) :=
        add_le_add (brS_itsr hS A) (add_le_add (brS_open hS A)
          (add_le_add (brS_coll_split hS A) hw))
    _ = _ := by ring

/-- **Strong forgeries in `G2`, collision branch split.** -/
theorem g2W_le_split (hS : Structural vp prims) (w : WinCheck vp prims)
    (hw : ∀ pk f log, w pk f log = true → sufCheck pk f log = true)
    (A : Forger vp prims optRand pkSeedDist) :
    prTrue (g2W w A) ≤
      KeyedHash.ITSRAdvantage (Lazy.bItsrL A) +
        SM_DT_OpenPRE_SourceFinalValidity.advantage (Lazy.bOpenPreS A) +
        tcrSplitSumS A +
        ((vp.params.w - 2 : ℕ) : ℝ≥0∞) * SM_DT_UD_Advantage (rUd pkSeedDist (Lazy.bWotsS A)) +
        SM_DT_PRE_Advantage (rPre pkSeedDist (Lazy.bWotsS A)) +
        SM_DT_TCR_Advantage (rTcr pkSeedDist (Lazy.bWotsS A)) := by
  rw [g2W_eq_g2With, prTrue_g2With_eq_sparse hS A _ (winOfCheck_restrict hS w)]
  exact g2WithS_le_split hS A _ fun pkSeed tbl z h =>
    (sufWin_cases pkSeed tbl z (sufWin_of_sufCheck pkSeed tbl z (hw _ _ _ h))).elim
      (freshWin_cases hS pkSeed tbl z) (sameWin_cases hS pkSeed tbl z)

/-! ## Resources of the restricted adversaries -/

section Count

/-- `1` if `m = n`, else `0`. -/
def arInd (n m : ℕ) : ℕ := if m = n then 1 else 0

/-- **Number of hash calls of arity `n` in the key structure** (closed form):
`2^h` FORS instances, each with `k·2^a` leaves (`F`), `k·(2^a − 1)` nodes (`H`) and one roots
compression (`T_k`); `#trees = Σ_{i<d} 2^(h'·i)` XMSS trees, each with `2^h'` WOTS+ instances
(`len·(w−1)` chain steps `F`, one public-key compression `T_len`) and `2^h' − 1` nodes (`H`).
A kind contributes iff its arity is `n` (`arInd`), so coinciding arities add up. -/
def arityTargets (vp : ValidatedParams) (n : ℕ) : ℕ :=
  2 ^ vp.params.h *
      (vp.params.k * (2 ^ vp.params.a * arInd n 1 + (2 ^ vp.params.a - 1) * arInd n 2) +
        arInd n vp.params.k) +
    (allXmssTrees vp).length *
      (2 ^ vp.params.hp *
          (vp.params.len * ((vp.params.w - 1) * arInd n 1) + arInd n vp.params.len) +
        (2 ^ vp.params.hp - 1) * arInd n 2)

theorem countP_all_const {α : Type} (p : α → Bool) (e : ℕ) :
    ∀ l : List α, (∀ x ∈ l, [x].countP p = e) → l.countP p = l.length * e
  | [], _ => by simp
  | x :: l, h => by
      have h1 := h x (by simp)
      have h2 := countP_all_const p e l (fun y hy => h y (by simp [hy]))
      rw [show x :: l = [x] ++ l from rfl, List.countP_append, h1, h2, List.length_append,
        List.length_singleton]
      ring

theorem countP_flatMap_const {α β : Type} (p : α → Bool) (g : β → List α) (c : ℕ) :
    ∀ l : List β, (∀ b ∈ l, (g b).countP p = c) → (l.flatMap g).countP p = l.length * c
  | [], _ => by simp
  | b :: l, h => by
      have h1 := h b (by simp)
      have h2 := countP_flatMap_const p g c l (fun y hy => h y (by simp [hy]))
      rw [List.flatMap_cons, List.countP_append, h1, h2, List.length_cons]
      ring

theorem mf_M_countP {α : Type} (p : α → Bool) (leaf : ℕ → List α) (node : ℕ → ℕ → α) (c e : ℕ)
    (hc : ∀ t, (leaf t).countP p = c) (he : ∀ z t, [node (z + 1) t].countP p = e) :
    ∀ z t, (mf_M leaf node z t).countP p = 2 ^ z * c + (2 ^ z - 1) * e
  | 0, t => by simp [mf_M, hc]
  | z + 1, t => by
      rw [mf_M, List.countP_append, List.countP_append, mf_M_countP p leaf node c e hc he z,
        mf_M_countP p leaf node c e hc he z, he]
      obtain ⟨m, hm⟩ : ∃ m, 2 ^ z = m + 1 := ⟨2 ^ z - 1, by have := Nat.one_le_two_pow (n := z); omega⟩
      have h2 : (m + 1) * 2 - 1 = 2 * m + 1 := by omega
      rw [pow_succ, hm, h2, Nat.add_sub_cancel]
      ring

/-- The arity-`n` predicate on addresses. -/
def arP (vp : ValidatedParams) (n : ℕ) (a : Adrs) : Bool := decide (arityOf vp a = n)

theorem arP_single (n : ℕ) (a : Adrs) : [a].countP (arP vp n) = arInd n (arityOf vp a) := by
  by_cases h : arityOf vp a = n <;> simp [arP, arInd, h]

theorem mf_wotsL_countP (n : ℕ) (adrs : Adrs) :
    (mf_wotsL vp adrs).countP (arP vp n) =
      vp.params.len * ((vp.params.w - 1) * arInd n 1) + arInd n vp.params.len := by
  rw [mf_wotsL, List.countP_append, arP_single, arityOf_wotsPk,
    countP_flatMap_const (arP vp n) _ ((vp.params.w - 1) * arInd n 1)]
  · simp
  · intro i _
    have := countP_all_const (arP vp n) (arInd n 1)
      ((List.range (vp.params.w - 1)).map fun j =>
        (wotsChainAdrs adrs i.val).setHashAddress j) (fun x hx => by
        obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
        rw [arP_single, arityOf_chain])
    simpa using this

theorem mf_xmssL_countP (n : ℕ) (adrs : Adrs) :
    (mf_xmssL vp adrs).countP (arP vp n) =
      2 ^ vp.params.hp *
          (vp.params.len * ((vp.params.w - 1) * arInd n 1) + arInd n vp.params.len) +
        (2 ^ vp.params.hp - 1) * arInd n 2 :=
  mf_M_countP _ _ _ _ _ (fun _ => mf_wotsL_countP n _)
    (fun z t => by rw [arP_single, arityOf_xmssNode]) _ _

theorem mf_forsL_countP (n : ℕ) (adrs : Adrs) :
    (mf_forsL vp adrs).countP (arP vp n) =
      vp.params.k * (2 ^ vp.params.a * arInd n 1 + (2 ^ vp.params.a - 1) * arInd n 2) +
        arInd n vp.params.k := by
  rw [mf_forsL, List.countP_append, arP_single, arityOf_forsPk,
    countP_flatMap_const (arP vp n) _
      (2 ^ vp.params.a * arInd n 1 + (2 ^ vp.params.a - 1) * arInd n 2)]
  · simp
  · intro i _
    exact mf_M_countP _ _ _ _ _ (fun t => by rw [arP_single, arityOf_forsLeaf])
      (fun z t => by rw [arP_single, arityOf_forsNode]) _ _

theorem mf_all_countP (n : ℕ) : (mf_all vp).countP (arP vp n) = arityTargets vp n := by
  rw [mf_all, List.countP_append,
    countP_flatMap_const _ _ _ _ (fun bp _ => mf_forsL_countP (vp := vp) n bp.forsAdrs),
    countP_flatMap_const _ _ _ _ (fun c _ => mf_xmssL_countP (vp := vp) n c.toAdrs),
    allBottomPositions_length]
  rfl

/-- **The honest structure makes exactly `arityTargets vp n` hash calls of arity `n`.** -/
theorem honestCalls_countP (tbl : SecretTable vp prims) (pk : prims.PkSeed) (n : ℕ) :
    (honestCalls tbl pk).countP (fun c => decide (c.2.length = n)) = arityTargets vp n := by
  have h := congrArg (List.countP (fun x : prims.AdrsKey × ℕ => decide (x.2 = n)))
    (honestCalls_map_arity tbl pk)
  rw [List.countP_map, List.countP_map] at h
  exact h.trans (mf_all_countP n)

theorem classTargets_length {Tweak Y : Type} (P : List Y → Prop) [DecidablePred P] :
    ∀ L : List (Tweak × List Y),
      (TcrSplit.classTargets P L).length = L.countP (fun q => decide (P q.2))
  | [] => rfl
  | q :: L => by
      have ih := classTargets_length P L
      unfold TcrSplit.classTargets at ih ⊢
      by_cases h : P q.2 <;> simp [h, ih]

theorem otherTweaks_length {Tweak Y : Type} (P : List Y → Prop) [DecidablePred P]
    (L : List (Tweak × List Y)) :
    (TcrSplit.classTargets P L).length + (TcrSplit.otherTweaks P L).length = L.length := by
  rw [classTargets_length, TcrSplit.otherTweaks, List.length_map, ← List.countP_eq_length_filter,
    List.length_eq_countP_add_countP (fun q => decide (P q.2)) (l := L)]
  congr 2

/-- The `choose` phase of a restricted adversary in its class game is one run of the `choose`
phase of the original adversary in its own game, followed by a relabelling of the state. -/
theorem restrict_choose_run {PkSeed Tweak Y : Type} [DecidableEq Tweak]
    {th : TweakableHash PkSeed Tweak (List Y) Y} {N : ℕ} (P : List Y → Prop) [DecidablePred P]
    (d : {xs : List Y // P xs}) (B : SM_DT_TCR_Adversary (SM_DT_TCR_Problem.standalone th N))
    (pk : PkSeed) :
    (simulateQ (SM_DT_TCR_oracles (TcrSplit.classProblem th P N) pk)
        (TcrSplit.restrict P d B).choose).run ([], []) =
      (simulateQ (SM_DT_TCR_oracles (SM_DT_TCR_Problem.standalone th N) pk) B.choose).run
        ([], []) >>= fun z => pure ((z.1, z.2.1), TcrSplit.gState P z.2.1) :=
  TcrSplit.choose_coupling P th N pk B.choose []

end Count

/-- **The `choose` phase of `bTcrArS n A` in its class game**: one run of the `choose` phase of
`bTcrS A` (one sparse table); the final state of the class game is `gState` of the honest calls:
targets = the arity-`n` calls, collection queries = the tweaks of the others.  Nothing is
refused. -/
theorem bTcrArS_choose_run (hS : Structural vp prims) (n : ℕ)
    (A : Forger vp prims optRand pkSeedDist) (pk : prims.PkSeed) :
    (simulateQ (SM_DT_TCR_oracles (thashArityProblem vp prims pkSeedDist n) pk)
        (bTcrArS n A).choose).run ([], []) =
      (fun tbl => ((tbl, honestCalls tbl pk),
        TcrSplit.gState (fun xs => xs.length = n) (honestCalls tbl pk))) <$>
          Lazy.sparseTable vp prims := by
  have h := restrict_choose_run (fun xs : List prims.Y => xs.length = n) (arityDefault prims n)
    (Lazy.bTcrS A) pk
  have h' := Lazy.bTcrS_choose_run hS A pk
  unfold bTcrArS thashArityProblem
  refine h.trans ?_
  refine (congrArg (· >>= _) h').trans ?_
  rw [map_eq_bind_pure_comp, map_eq_bind_pure_comp]
  refine (bind_assoc _ _ _).trans ?_
  refine bind_congr fun tbl => ?_
  exact pure_bind _ _

/-- **Targets of `bTcrArS n A`**: exactly `arityTargets vp n` targets, with distinct tweaks among
all `tcrTargets vp` oracle calls; the other calls are collection queries. -/
theorem bTcrArS_targets (hS : Structural vp prims) (n : ℕ) (tbl : SecretTable vp prims)
    (pk : prims.PkSeed) :
    (TcrSplit.gState (fun xs => xs.length = n) (honestCalls tbl pk)).1.length =
        arityTargets vp n ∧
      (TcrSplit.gState (fun xs => xs.length = n) (honestCalls tbl pk)).1.length +
        (TcrSplit.gState (fun xs => xs.length = n) (honestCalls tbl pk)).2.length =
          tcrTargets vp ∧
      ((honestCalls tbl pk).map (·.1)).Nodup := by
  refine ⟨?_, ?_, (honestCalls_nodup_length hS tbl pk).1⟩
  · exact (classTargets_length (fun xs : List prims.Y => xs.length = n) _).trans
      (honestCalls_countP tbl pk n)
  · exact (otherTweaks_length (fun xs : List prims.Y => xs.length = n) _).trans
      (honestCalls_nodup_length hS tbl pk).2

/-! ## The split bound and the final theorems -/

variable [Fintype prims.Y]

/-- The right-hand side of the split final theorems: `boundFinal` with the cross-arity
SM-TCR(`Thash`) term replaced by four SM-TCR terms on `F`, `H`, `T_len`, `T_k`
(twelve advantages). -/
noncomputable def boundFinalSplit (pkSeedDist : ProbComp prims.PkSeed)
    (B₁ : PRFScheme.PRFAdversary (prims.PkSeed × SkAdrs vp) prims.Y) (B₂ : MsgPrfAdv prims)
    (B₃ : KeyedHash.ITSRAdversary (itsrProblem vp prims))
    (D : SM_DT_DSPR_SourceFinalValidity.Adversary (forsDsprProblem vp prims pkSeedDist))
    (T : SM_DT_TCR_SourceFinalValidity.Adversary (forsTcrProblem vp prims pkSeedDist))
    (C₁ : SM_DT_TCR_Adversary (thashArityProblem vp prims pkSeedDist 1))
    (C₂ : SM_DT_TCR_Adversary (thashArityProblem vp prims pkSeedDist 2))
    (C₃ : SM_DT_TCR_Adversary (thashArityProblem vp prims pkSeedDist vp.params.len))
    (C₄ : SM_DT_TCR_Adversary (thashArityProblem vp prims pkSeedDist vp.params.k))
    (B₆ : SM_DT_UD_Adversary (wotsUdProblem vp prims pkSeedDist))
    (B₇ : SM_DT_PRE_Adversary (wotsPreProblem vp prims pkSeedDist))
    (B₈ : SM_DT_TCR_Adversary (wotsTcrProblem vp prims pkSeedDist)) : ℝ≥0∞ :=
  (skPrfC vp prims).prfAdvantage B₁ + (msgPrf vp prims).prfAdvantage B₂ +
    KeyedHash.ITSRAdvantage B₃ +
    (SM_DT_DSPR_SourceFinalValidity.advantage D +
      3 * SM_DT_TCR_SourceFinalValidity.advantage T) +
    (SM_DT_TCR_Advantage C₁ + SM_DT_TCR_Advantage C₂ + SM_DT_TCR_Advantage C₃ +
      SM_DT_TCR_Advantage C₄) +
    ((vp.params.w - 2 : ℕ) : ℝ≥0∞) * SM_DT_UD_Advantage B₆ +
    SM_DT_PRE_Advantage B₇ +
    SM_DT_TCR_Advantage B₈

/-- The split EUF-CMA bound as a function of the forger. -/
noncomputable def betaEufFinalSplit (A : Forger vp prims optRand pkSeedDist) : ℝ≥0∞ :=
  boundFinalSplit pkSeedDist (bPrfC A) (Lazy.bPrfMsgL A) (Lazy.bItsrL A)
    (toDspr (Lazy.bOpenPreS A)) (toTcr (Lazy.bOpenPreS A))
    (bTcrArS 1 A) (bTcrArS 2 A) (bTcrArS vp.params.len A) (bTcrArS vp.params.k A)
    (rUd pkSeedDist (Lazy.bWotsS A)) (rPre pkSeedDist (Lazy.bWotsS A))
    (rTcr pkSeedDist (Lazy.bWotsS A))

/-- The split SUF-CMA bound as a function of the forger (the same program as the strong
forger). -/
noncomputable def betaSufFinalSplit (A : Forger vp prims optRand pkSeedDist) : ℝ≥0∞ :=
  boundFinalSplit pkSeedDist (bPrfWC sufCheck A) (Lazy.bPrfMsgWL sufCheck A) (Lazy.bItsrL A)
    (toDspr (Lazy.bOpenPreS A)) (toTcr (Lazy.bOpenPreS A))
    (bTcrArS 1 A) (bTcrArS 2 A) (bTcrArS vp.params.len A) (bTcrArS vp.params.k A)
    (rUd pkSeedDist (Lazy.bWotsS A)) (rPre pkSeedDist (Lazy.bWotsS A))
    (rTcr pkSeedDist (Lazy.bWotsS A))

private theorem compose_le' {a b c o d t e u f g : ℝ≥0∞} (ho : o ≤ d + 3 * t) :
    a + b + (c + o + e + u + f + g) ≤ a + b + c + (d + 3 * t) + e + u + f + g := by
  calc a + b + (c + o + e + u + f + g) = a + b + c + o + e + u + f + g := by ring
    _ ≤ a + b + c + (d + 3 * t) + e + u + f + g := by gcongr

/-- **Standard-model SUF-CMA security of SLH-DSA (FIPS 205 internal algorithms), per-function
TCR terms.**  For every strong forger `S` against `internalAlg vp prims optRand pkSeedDist`, with
`A := S.toUnforgeableAdversary` (the same program):

`Adv^{SUF-CMA}(S) ≤ Adv^{PRF}_{PRF on SkAdrs}(bPrfWC sufCheck A)
   + Adv^{PRF}_{PRF_msg}(bPrfMsgWL sufCheck A) + Adv^{ITSR}_{H_msg}(bItsrL A)
   + Adv^{SM-DSPR}_{F}(toDspr (bOpenPreS A)) + 3·Adv^{SM-TCR}_{F}(toTcr (bOpenPreS A))
   + Adv^{SM-TCR}_{F}(bTcrArS 1 A) + Adv^{SM-TCR}_{H}(bTcrArS 2 A)
   + Adv^{SM-TCR}_{T_len}(bTcrArS len A) + Adv^{SM-TCR}_{T_k}(bTcrArS k A)
   + (w-2)·Adv^{SM-UD}_{F}(rUd (bWotsS A)) + Adv^{SM-PRE}_{F}(rPre (bWotsS A))
   + Adv^{SM-TCR}_{F}(rTcr (bWotsS A))`.

No cryptographic hypothesis; no term on the variable-arity `Thash`. -/
theorem slhdsa_suf_cma_final_split (hS : Structural vp prims)
    (S : SignatureAlg.StrongUnforgeableAdversary (internalAlg vp prims optRand pkSeedDist)) :
    SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S ≤
      boundFinalSplit pkSeedDist (bPrfWC sufCheck S.toUnforgeableAdversary)
        (Lazy.bPrfMsgWL sufCheck S.toUnforgeableAdversary)
        (Lazy.bItsrL S.toUnforgeableAdversary)
        (toDspr (Lazy.bOpenPreS S.toUnforgeableAdversary))
        (toTcr (Lazy.bOpenPreS S.toUnforgeableAdversary))
        (bTcrArS 1 S.toUnforgeableAdversary) (bTcrArS 2 S.toUnforgeableAdversary)
        (bTcrArS vp.params.len S.toUnforgeableAdversary)
        (bTcrArS vp.params.k S.toUnforgeableAdversary)
        (rUd pkSeedDist (Lazy.bWotsS S.toUnforgeableAdversary))
        (rPre pkSeedDist (Lazy.bWotsS S.toUnforgeableAdversary))
        (rTcr pkSeedDist (Lazy.bWotsS S.toUnforgeableAdversary)) := by
  have h1 := suf_le_prf_add_g2 hS S
  have h2 := g2W_le_split hS sufCheck (fun _ _ _ h => h) S.toUnforgeableAdversary
  have h3 := forsOpenPre_le (Lazy.bOpenPreS S.toUnforgeableAdversary)
  rw [← prfAdvantageC_bPrfWC hS.bounds, ← Lazy.prfAdvantage_bPrfMsgWL] at h1
  unfold tcrSplitSumS at h2
  unfold boundFinalSplit
  exact (h1.trans (add_le_add_right h2 _)).trans (compose_le' h3)

/-- `slhdsa_suf_cma_final_split` in the form `∀ S, Adv S ≤ β S`. -/
theorem slhdsa_suf_cma_final_split' (hS : Structural vp prims) :
    ∀ S : SignatureAlg.StrongUnforgeableAdversary (internalAlg vp prims optRand pkSeedDist),
      SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S ≤
        betaSufFinalSplit S.toUnforgeableAdversary :=
  fun S => slhdsa_suf_cma_final_split hS S

/-- **Standard-model EUF-CMA security of SLH-DSA (FIPS 205 internal algorithms), per-function
TCR terms.**  As `slhdsa_suf_cma_final_split` for a chosen-message forger `A`, with the PRF
distinguishers `bPrfC A`, `bPrfMsgL A`. -/
theorem slhdsa_euf_cma_final_split (hS : Structural vp prims)
    (A : Forger vp prims optRand pkSeedDist) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤
      boundFinalSplit pkSeedDist (bPrfC A) (Lazy.bPrfMsgL A) (Lazy.bItsrL A)
        (toDspr (Lazy.bOpenPreS A)) (toTcr (Lazy.bOpenPreS A))
        (bTcrArS 1 A) (bTcrArS 2 A) (bTcrArS vp.params.len A) (bTcrArS vp.params.k A)
        (rUd pkSeedDist (Lazy.bWotsS A)) (rPre pkSeedDist (Lazy.bWotsS A))
        (rTcr pkSeedDist (Lazy.bWotsS A)) := by
  have h := final_of_steps_tcr A (bPrf A) (Lazy.bPrfMsgL A) (Lazy.bItsrL A) (Lazy.bOpenPreS A)
    (Lazy.bWotsS A) (rUd pkSeedDist (Lazy.bWotsS A)) (rPre pkSeedDist (Lazy.bWotsS A))
    (rTcr pkSeedDist (Lazy.bWotsS A)) (tcrSplitSumS A)
    (stepPRF hS A) (Lazy.stepPRFmsg_lazy A) (stepSplit A) (Lazy.stepITSR_lazy A)
    (Lazy.stepOpenPRE_sparse hS A) (stepTCR_split_sparse hS A)
    (Lazy.stepWotsEmbed_sparse hS A) (stepWotsUD hS pkSeedDist (Lazy.bWotsS A))
    (stepWotsFinal hS pkSeedDist (Lazy.bWotsS A))
  have h3 := forsOpenPre_le (Lazy.bOpenPreS A)
  unfold tcrSplitSumS at h
  unfold boundFinalSplit
  rw [prfAdvantageC_eq hS.bounds]
  refine h.trans ?_
  gcongr

/-- `slhdsa_euf_cma_final_split` in the form `∀ A, Adv A ≤ β A`. -/
theorem slhdsa_euf_cma_final_split' (hS : Structural vp prims) :
    ∀ A : Forger vp prims optRand pkSeedDist,
      SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤ betaEufFinalSplit A :=
  fun A => slhdsa_euf_cma_final_split hS A

/-- **EUF-CMA of the external pure interface (FIPS 205 Alg. 21/22/24), per-function TCR
terms**: the split bound at the internal forger `toInternal A`. -/
theorem slhdsa_pure_euf_cma_final_split (hS : Structural vp prims)
    (A : ExtForger vp prims optRand pkSeedDist) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤
      boundFinalSplit pkSeedDist (bPrfC (toInternal A)) (Lazy.bPrfMsgL (toInternal A))
        (Lazy.bItsrL (toInternal A))
        (toDspr (Lazy.bOpenPreS (toInternal A))) (toTcr (Lazy.bOpenPreS (toInternal A)))
        (bTcrArS 1 (toInternal A)) (bTcrArS 2 (toInternal A))
        (bTcrArS vp.params.len (toInternal A)) (bTcrArS vp.params.k (toInternal A))
        (rUd pkSeedDist (Lazy.bWotsS (toInternal A))) (rPre pkSeedDist (Lazy.bWotsS (toInternal A)))
        (rTcr pkSeedDist (Lazy.bWotsS (toInternal A))) :=
  external_bound_of_internal_bound betaEufFinalSplit (slhdsa_euf_cma_final_split' hS) A

/-- **SUF-CMA of the external pure interface, per-function TCR terms**: the split SUF bound at
the internal forger `toInternal S.toUnforgeableAdversary`. -/
theorem slhdsa_pure_suf_cma_final_split (hS : Structural vp prims)
    (S : ExtStrongForger vp prims optRand pkSeedDist) :
    SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S ≤
      boundFinalSplit pkSeedDist (bPrfWC sufCheck (toInternal S.toUnforgeableAdversary))
        (Lazy.bPrfMsgWL sufCheck (toInternal S.toUnforgeableAdversary))
        (Lazy.bItsrL (toInternal S.toUnforgeableAdversary))
        (toDspr (Lazy.bOpenPreS (toInternal S.toUnforgeableAdversary)))
        (toTcr (Lazy.bOpenPreS (toInternal S.toUnforgeableAdversary)))
        (bTcrArS 1 (toInternal S.toUnforgeableAdversary))
        (bTcrArS 2 (toInternal S.toUnforgeableAdversary))
        (bTcrArS vp.params.len (toInternal S.toUnforgeableAdversary))
        (bTcrArS vp.params.k (toInternal S.toUnforgeableAdversary))
        (rUd pkSeedDist (Lazy.bWotsS (toInternal S.toUnforgeableAdversary)))
        (rPre pkSeedDist (Lazy.bWotsS (toInternal S.toUnforgeableAdversary)))
        (rTcr pkSeedDist (Lazy.bWotsS (toInternal S.toUnforgeableAdversary))) :=
  (external_strong_advantage_le S).trans (slhdsa_suf_cma_final_split hS (toInternalS S))

/-- **Resources of all adversaries of the split bounds**: `FinalResources` (unchanged
adversaries), and for each arity `n` the `choose` run and target counts of `bTcrArS n A`. -/
theorem final_split_resources (hS : Structural vp prims) (A : Forger vp prims optRand pkSeedDist)
    (qs : ℕ) (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs) :
    FinalResources A qs (counts vp qs) ∧
    (∀ n pk, (simulateQ (SM_DT_TCR_oracles (thashArityProblem vp prims pkSeedDist n) pk)
        (bTcrArS n A).choose).run ([], []) =
      (fun tbl => ((tbl, honestCalls tbl pk),
        TcrSplit.gState (fun xs => xs.length = n) (honestCalls tbl pk))) <$>
          Lazy.sparseTable vp prims) ∧
    ∀ n (tbl : SecretTable vp prims) (pk : prims.PkSeed),
      (TcrSplit.gState (fun xs => xs.length = n) (honestCalls tbl pk)).1.length =
          arityTargets vp n ∧
        (TcrSplit.gState (fun xs => xs.length = n) (honestCalls tbl pk)).1.length +
          (TcrSplit.gState (fun xs => xs.length = n) (honestCalls tbl pk)).2.length =
            tcrTargets vp ∧
        ((honestCalls tbl pk).map (·.1)).Nodup :=
  ⟨final_resources hS A qs hA, fun n pk => bTcrArS_choose_run hS n A pk,
    fun n tbl pk => bTcrArS_targets hS n tbl pk⟩

end Reduction

/-! ## SLH-DSA-SHA2-128s -/

namespace Reduction

open TweakableHash

/-- **Target counts of the four class adversaries at SLH-DSA-SHA2-128s** (`len = 35`, `k = 14`):
`F`: `533756792467910173399552 ≈ 2^78.82` (FORS leaves + WOTS+ chain steps);
`H`: `528785142244921151848447 ≈ 2^78.81` (FORS nodes + XMSS nodes);
`T_len`: `9241421688590303744 ≈ 2^63.003`; `T_k`: `9223372036854775808 = 2^63`;
they add up to `tcrTargets = 1062560399506556770327551`. -/
theorem arityTargets_128s :
    arityTargets Link.vp 1 = 533756792467910173399552 ∧
    arityTargets Link.vp 2 = 528785142244921151848447 ∧
    arityTargets Link.vp Link.vp.params.len = 9241421688590303744 ∧
    arityTargets Link.vp Link.vp.params.k = 9223372036854775808 ∧
    arityTargets Link.vp 1 + arityTargets Link.vp 2 + arityTargets Link.vp Link.vp.params.len +
      arityTargets Link.vp Link.vp.params.k = tcrTargets Link.vp := by
  have e : ∀ n, arityTargets Link.vp n =
      2 ^ 63 * (14 * (2 ^ 12 * arInd n 1 + (2 ^ 12 - 1) * arInd n 2) + arInd n 14) +
        18049651735527937 * (2 ^ 9 * (35 * (15 * arInd n 1) + arInd n 35) +
          (2 ^ 9 - 1) * arInd n 2) := by
    intro n
    unfold arityTargets
    rw [Resources.allXmssTrees_length_128s]
    rfl
  have h1 : arityTargets Link.vp 1 = 533756792467910173399552 := by rw [e]; decide
  have h2 : arityTargets Link.vp 2 = 528785142244921151848447 := by rw [e]; decide
  have h3 : arityTargets Link.vp Link.vp.params.len = 9241421688590303744 := by
    rw [e]; decide
  have h4 : arityTargets Link.vp Link.vp.params.k = 9223372036854775808 := by
    rw [e]; decide
  refine ⟨h1, h2, h3, h4, ?_⟩
  rw [h1, h2, h3, h4, Resources.tcrTargets_128s_val]

/-- **SUF-CMA security of SLH-DSA-SHA2-128s (internal algorithms), per-function TCR terms.**
No hypothesis besides the strong forger. -/
theorem slhdsa_sha2_128s_suf_cma_final_split
    (optRand : PublicKeyCore Link.prims.core → ProbComp Link.prims.Y)
    (pkSeedDist : ProbComp Link.prims.PkSeed)
    (S : SignatureAlg.StrongUnforgeableAdversary
      (internalAlg Link.vp Link.prims optRand pkSeedDist)) :
    SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S ≤
      betaSufFinalSplit S.toUnforgeableAdversary :=
  slhdsa_suf_cma_final_split structural_128s S

/-- **EUF-CMA security of SLH-DSA-SHA2-128s (internal algorithms), per-function TCR terms.** -/
theorem slhdsa_sha2_128s_euf_cma_final_split
    (optRand : PublicKeyCore Link.prims.core → ProbComp Link.prims.Y)
    (pkSeedDist : ProbComp Link.prims.PkSeed)
    (A : Forger Link.vp Link.prims optRand pkSeedDist) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤ betaEufFinalSplit A :=
  slhdsa_euf_cma_final_split structural_128s A

/-- **EUF-CMA security of the external pure interface of SLH-DSA-SHA2-128s, per-function TCR
terms.** -/
theorem slhdsa_sha2_128s_pure_euf_cma_final_split
    (optRand : PublicKeyCore Link.prims.core → ProbComp Link.prims.Y)
    (pkSeedDist : ProbComp Link.prims.PkSeed)
    (A : ExtForger Link.vp Link.prims optRand pkSeedDist) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤
      betaEufFinalSplit (toInternal A) :=
  slhdsa_pure_euf_cma_final_split structural_128s A

/-- **SUF-CMA security of the external pure interface of SLH-DSA-SHA2-128s, per-function TCR
terms.** -/
theorem slhdsa_sha2_128s_pure_suf_cma_final_split
    (optRand : PublicKeyCore Link.prims.core → ProbComp Link.prims.Y)
    (pkSeedDist : ProbComp Link.prims.PkSeed)
    (S : ExtStrongForger Link.vp Link.prims optRand pkSeedDist) :
    SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S ≤
      betaSufFinalSplit (toInternal S.toUnforgeableAdversary) :=
  slhdsa_pure_suf_cma_final_split structural_128s S

#print axioms brS_coll_split
#print axioms stepTCR_split_sparse
#print axioms bTcrArS_choose_run
#print axioms bTcrArS_targets
#print axioms arityTargets_128s
#print axioms slhdsa_suf_cma_final_split
#print axioms slhdsa_euf_cma_final_split
#print axioms slhdsa_pure_euf_cma_final_split
#print axioms slhdsa_pure_suf_cma_final_split
#print axioms final_split_resources
#print axioms slhdsa_sha2_128s_suf_cma_final_split
#print axioms slhdsa_sha2_128s_euf_cma_final_split
#print axioms slhdsa_sha2_128s_pure_euf_cma_final_split
#print axioms slhdsa_sha2_128s_pure_suf_cma_final_split

end Reduction
