import Reduction.Open.WotsCounts

/-!
# Fresh samples of the wrappers `rUd`, `rPre`, `rTcr` (`rTcrT`), phase 1

The wrappers draw their own values of `prims.Y` by `monadLift ($ᵗ prims.Y)` inside
`udStart` / `preStart` / `tcrStart`.  To count these draws they are made explicit: the
*sampling-explicit* programs `rUdPickS`, `rPreChooseS`, `rTcrChooseS` are the phase-1 programs
over the interface extended by a one-point oracle `sampSpec prims` (`Unit →ₒ prims.Y`), in which
every such draw is a query to that oracle and everything else is unchanged.

* `*_interp`: answering the sampling oracle by `$ᵗ prims.Y` (`dropS`) gives back the phase-1
  program of the adversary, literally.
* `*_wrapper_samples_le`: the sampling-explicit program makes at most `#inst · len` sampling
  queries (`IsQueryBoundP`, i.e. on every path, whatever the oracles answer), for EVERY WOTS-game
  adversary `W`, in particular `Lazy.bWotsS A`.

The samples of `W` itself (uniform queries of `W.choose`) are forwarded as uniform queries and
are not sampling-oracle queries; for `bWotsS A` they are counted by `Lazy.bWotsS_choose_eq`.
`rUd` additionally draws its hybrid index, one `$ᵗ (Fin (w - 3 + 1))` (first step of `pick`,
kept as a lifted `ProbComp` in `rUdPickS`).
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal
open TweakableHash

namespace Reduction
namespace Open

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]
variable {optRand : PublicKeyCore prims.core → ProbComp prims.Y}

section Generic

variable {ι : Type} {spec : OracleSpec ι}

/-- The one-point sampling oracle for the wrapper's own values. -/
abbrev sampSpec (prims : Primitives vp.params) : OracleSpec Unit := Unit →ₒ prims.Y

/-- The index of a sampling-oracle query. -/
def isSamp {B : Type} : ℕ ⊕ (Unit ⊕ B) → Prop
  | Sum.inr (Sum.inl _) => True
  | _ => False

instance {B : Type} : DecidablePred (isSamp (B := B)) := fun t =>
  match t with
  | Sum.inr (Sum.inl _) => isTrue trivial
  | Sum.inr (Sum.inr _) => isFalse id
  | Sum.inl _ => isFalse id

/-- One explicit sample. -/
def sampQ : OracleComp (unifSpec + (sampSpec prims + spec)) prims.Y :=
  liftM ((unifSpec + (sampSpec prims + spec)).query (Sum.inr (Sum.inl ())))

/-- Embedding of the original interface into the extended one. -/
def embS : QueryImpl (unifSpec + spec) (OracleComp (unifSpec + (sampSpec prims + spec)))
  | Sum.inl k => liftM ((unifSpec + (sampSpec prims + spec)).query (Sum.inl k))
  | Sum.inr t => liftM ((unifSpec + (sampSpec prims + spec)).query (Sum.inr (Sum.inr t)))

/-- Interpretation of the extended interface: a sampling query is `$ᵗ prims.Y`. -/
noncomputable def dropS :
    QueryImpl (unifSpec + (sampSpec prims + spec)) (OracleComp (unifSpec + spec))
  | Sum.inl k => liftM ((unifSpec + spec).query (Sum.inl k))
  | Sum.inr (Sum.inl _) =>
    (monadLift ($ᵗ prims.Y : ProbComp prims.Y) : OracleComp (unifSpec + spec) prims.Y)
  | Sum.inr (Sum.inr t) => liftM ((unifSpec + spec).query (Sum.inr t))

theorem dropS_sampQ :
    simulateQ (dropS (prims := prims) (spec := spec)) sampQ =
      (monadLift ($ᵗ prims.Y : ProbComp prims.Y) : OracleComp (unifSpec + spec) prims.Y) := by
  unfold sampQ
  rw [simulateQ_spec_query]
  rfl

theorem drop_emb {α : Type} (p : OracleComp (unifSpec + spec) α) :
    simulateQ (dropS (prims := prims)) (simulateQ (embS (prims := prims)) p) = p := by
  induction p using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, ih]
    rcases t with n | t
    · simp only [embS, simulateQ_spec_query, dropS]
    · simp only [embS, simulateQ_spec_query, dropS]

theorem emb_qb {α : Type} (p : OracleComp (unifSpec + spec) α) :
    IsQueryBoundP (simulateQ (embS (prims := prims)) p) isSamp 0 := by
  induction p using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map]
    rcases t with n | t
    · simp only [embS]
      rw [isQueryBoundP_query_bind_iff]
      exact ⟨Or.inl id, fun u => by simpa [isSamp] using ih u⟩
    · simp only [embS]
      rw [isQueryBoundP_query_bind_iff]
      exact ⟨Or.inl id, fun u => by simpa [isSamp] using ih u⟩

/-- Fusion of an outer interpretation with a stateful simulation. -/
theorem fuse {ι₀ ι₁ ι₁' : Type} {spec₀ : OracleSpec ι₀} {spec₁ : OracleSpec ι₁}
    {spec₁' : OracleSpec ι₁'} {H : Type}
    (S' : QueryImpl spec₀ (StateT H (OracleComp spec₁')))
    (S : QueryImpl spec₀ (StateT H (OracleComp spec₁)))
    (h : QueryImpl spec₁' (OracleComp spec₁))
    (hq : ∀ q g, simulateQ h ((S' q).run g) = (S q).run g)
    {α : Type} (oa : OracleComp spec₀ α) (g : H) :
    simulateQ h ((simulateQ S' oa).run g) = (simulateQ S oa).run g := by
  induction oa using OracleComp.inductionOn generalizing g with
  | pure x => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, StateT.run_bind, hq]
    exact bind_congr fun p => ih p.1 p.2

theorem signProg_interp
    (startS : Adrs → ℕ → OracleComp (unifSpec + (sampSpec prims + spec)) prims.Y)
    (start : Adrs → ℕ → OracleComp (unifSpec + spec) prims.Y)
    (chainHash : Adrs → prims.Y → OracleComp (unifSpec + spec) prims.Y)
    (hstart : ∀ ca b, simulateQ dropS (startS ca b) = start ca b) (a : Adrs) (m : prims.Y) :
    simulateQ dropS (signProg (vp := vp) startS
        (fun a x => simulateQ (embS (prims := prims)) (chainHash a x)) a m) =
      signProg start chainHash a m := by
  unfold signProg
  have h1 := Vector.ofFnM_natural (simulateQ' (dropS (prims := prims) (spec := spec)))
    (fun i : Fin vp.params.len =>
      startS (wotsChainAdrs a i.val) (chainStepsCore prims.core m i.val))
    (fun i : Fin vp.params.len =>
      start (wotsChainAdrs a i.val) (chainStepsCore prims.core m i.val)) (fun i => hstart _ _)
  rw [simulateQ_bind]
  refine (congrArg (· >>= _) h1).trans (bind_congr fun sig => ?_)
  rw [simulateQ_bind]
  have h2 := wotsPkFromSigTopsWith_natural (simulateQ' (dropS (prims := prims) (spec := spec)))
    prims.core (fun a x => simulateQ (embS (prims := prims)) (chainHash a x)) chainHash
    (fun a y => drop_emb _) sig m a
  refine (congrArg (· >>= _) h2).trans (bind_congr fun tops => ?_)
  rw [simulateQ_pure]

/-- **Interpretation of the sampling-explicit simulator.** -/
theorem simChooseS_interp (W : WotsGame.Adversary prims)
    (startS : Adrs → ℕ → OracleComp (unifSpec + (sampSpec prims + spec)) prims.Y)
    (start : Adrs → ℕ → OracleComp (unifSpec + spec) prims.Y)
    (chainHash : Adrs → prims.Y → OracleComp (unifSpec + spec) prims.Y)
    (coll : prims.AdrsKey → List prims.Y → OracleComp (unifSpec + spec) prims.Y)
    (hstart : ∀ ca b, simulateQ dropS (startS ca b) = start ca b) :
    simulateQ dropS (WotsGame.simChoose W (wotsInsts vp) startS
        (fun a x => simulateQ (embS (prims := prims)) (chainHash a x))
        (fun k xs => simulateQ (embS (prims := prims)) (coll k xs))) =
      WotsGame.simChoose W (wotsInsts vp) start chainHash coll := by
  refine fuse (WotsFinal.simImpl (wotsInsts vp) startS _ _)
    (WotsFinal.simImpl (wotsInsts vp) start chainHash coll) dropS (fun q g => ?_) W.choose []
  rcases q with n | q | q
  · rw [simImpl_run_unif, simImpl_run_unif, simulateQ_bind, simulateQ_spec_query]
    simp only [simulateQ_pure]
    rfl
  · rw [simImpl_run_sign, simImpl_run_sign]
    split_ifs with h
    · rw [simulateQ_pure]
    · rw [simulateQ_bind, signProg_interp startS start chainHash hstart]
      simp only [simulateQ_pure]
  · rw [simImpl_run_coll, simImpl_run_coll]
    split_ifs with h
    · rw [simulateQ_pure]
    · rw [simulateQ_bind, drop_emb]
      simp only [simulateQ_pure]

/-- **Sampling queries of the sampling-explicit simulator**: at most `len` per accepted signing
query, hence at most `#inst · len`, for every `W` and whatever the oracles answer. -/
theorem simChooseS_samples (W : WotsGame.Adversary prims)
    (startS : Adrs → ℕ → OracleComp (unifSpec + (sampSpec prims + spec)) prims.Y)
    (chS : Adrs → prims.Y → OracleComp (unifSpec + (sampSpec prims + spec)) prims.Y)
    (collS : prims.AdrsKey → List prims.Y → OracleComp (unifSpec + (sampSpec prims + spec)) prims.Y)
    (hstart : ∀ ca b, IsQueryBoundP (startS ca b) isSamp 1)
    (hch : ∀ a y, IsQueryBoundP (chS a y) isSamp 0)
    (hcoll : ∀ k xs, IsQueryBoundP (collS k xs) isSamp 0) :
    IsQueryBoundP (WotsGame.simChoose W (wotsInsts vp) startS chS collS) isSamp
      ((wotsInsts vp).length * vp.params.len) := by
  have hsign : ∀ a m, IsQueryBoundP (signProg (vp := vp) startS chS a m) isSamp
      (vp.params.len * 1) := fun a m =>
    signProg_qb isSamp startS chS (fun _ => 1) 0 1 hstart hch (fun b hb => by omega) a m
  have key : ∀ {α : Type} (oa : OracleComp (WSpec prims) α) (g : List (WotsGame.Entry prims)),
      Lazy.HistInv vp g →
      IsQueryBoundP ((simulateQ (WotsFinal.simImpl (wotsInsts vp) startS chS collS) oa).run g)
        isSamp (((wotsInsts vp).length - g.length) * vp.params.len) := by
    intro α oa
    induction oa using OracleComp.inductionOn with
    | pure x => intro g _; simp
    | query_bind t k ih =>
      intro g hg
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, StateT.run_bind]
      rcases t with n | q | q
      · rw [simImpl_run_unif, bind_assoc, isQueryBoundP_query_bind_iff]
        refine ⟨Or.inl id, fun u => ?_⟩
        rw [pure_bind]
        simpa [isSamp] using ih u g hg
      · rw [simImpl_run_sign]
        split_ifs with h
        · rw [pure_bind]
          exact ih _ g hg
        · rw [not_or, not_not] at h
          rw [bind_assoc]
          have hg' : ∀ r : WotsSig vp.params prims.core × Vector prims.Y vp.params.len,
              Lazy.HistInv vp (g ++ [(q.1, q.2, r.1, r.2)]) := fun r =>
            Lazy.histInv_append hg _ h.1 h.2
          have hlen : g.length + 1 ≤ (wotsInsts vp).length := by
            have h1 : (q.1 :: g.map (·.1)).Nodup := List.nodup_cons.mpr ⟨h.2, hg.1⟩
            have h2 : q.1 :: g.map (·.1) ⊆ wotsInsts vp := by
              intro x hx
              rcases List.mem_cons.1 hx with rfl | hx
              · exact h.1
              · exact hg.2 x hx
            simpa using (List.subperm_of_subset h1 h2).length_le
          refine (Lazy.qb_bind _
            (m := ((wotsInsts vp).length - (g.length + 1)) * vp.params.len)
            (hsign q.1 q.2) fun r => ?_).mono ?_
          · rw [pure_bind]
            have := ih (some (r.1, r.2)) _ (hg' r)
            simpa using this
          · have e : (wotsInsts vp).length - g.length =
                ((wotsInsts vp).length - (g.length + 1)) + 1 := by omega
            rw [e, Nat.add_mul]
            omega
      · rw [simImpl_run_coll]
        split_ifs with h
        · rw [pure_bind]
          exact ih _ g hg
        · rw [bind_assoc]
          refine (Lazy.qb_bind _ (m := ((wotsInsts vp).length - g.length) * vp.params.len)
            (hcoll q.1 q.2) fun y => ?_).mono (by omega)
          rw [pure_bind]
          exact ih _ g hg
  have := key W.choose [] Lazy.histInv_nil
  simp only [List.length_nil, Nat.sub_zero] at this
  exact this

end Generic

variable (pkSeedDist : ProbComp prims.PkSeed)

/-! ## SM-UD -/

/-- The SM-UD interface extended by the sampling oracle. -/
abbrev UdSpecS (pkSeedDist : ProbComp prims.PkSeed) :=
  unifSpec + (sampSpec prims + (SM_DT_UD_challengeSpec prims.AdrsKey prims.Y +
    collectionSpec (wotsUdProblem vp prims pkSeedDist).thColl))

/-- `udStart` with its sample explicit. -/
noncomputable def udStartS (k : ℕ) (ca : Adrs) (b : ℕ) :
    OracleComp (UdSpecS (vp := vp) (prims := prims) pkSeedDist) prims.Y :=
  if k + 1 < b then simulateQ embS (udStart pkSeedDist k ca b)
  else sampQ >>= fun s =>
    simulateQ embS (chainWith (udChainHash pkSeedDist) ca s (min k (b - 1)) (b - min k (b - 1)))

theorem udStartS_interp (k : ℕ) (ca : Adrs) (b : ℕ) :
    simulateQ dropS (udStartS (vp := vp) pkSeedDist k ca b) = udStart pkSeedDist k ca b := by
  unfold udStartS
  split_ifs with h
  · exact drop_emb _
  · rw [simulateQ_bind, dropS_sampQ]
    simp only [drop_emb]
    unfold udStart
    rw [if_neg h]

theorem udStartS_qb (k : ℕ) (ca : Adrs) (b : ℕ) :
    IsQueryBoundP (udStartS (vp := vp) pkSeedDist k ca b) isSamp 1 := by
  unfold udStartS
  split_ifs with h
  · exact (emb_qb _).mono (by omega)
  · exact Lazy.qb_bind _ (n := 1) (m := 0) (by simp [sampQ]) fun s => emb_qb _

/-- **Phase 1 of `rUd pkSeedDist W` with the wrapper's `prims.Y` samples explicit.** -/
noncomputable def rUdPickS (W : WotsGame.Adversary prims) :
    OracleComp (UdSpecS (vp := vp) (prims := prims) pkSeedDist)
      (W.State × List (WotsGame.Entry prims)) :=
  simulateQ embS ((monadLift ($ᵗ (Fin (vp.params.w - 3 + 1)) :
      ProbComp (Fin (vp.params.w - 3 + 1))) :
    OracleComp (UdSpec (vp := vp) (prims := prims) pkSeedDist) (Fin (vp.params.w - 3 + 1)))) >>=
    fun k => WotsGame.simChoose W (wotsInsts vp) (udStartS pkSeedDist k.val)
      (fun a x => simulateQ embS (udChainHash pkSeedDist a x))
      (fun key xs => simulateQ embS (udColl pkSeedDist key xs))

/-- Answering the sampling oracle by `$ᵗ prims.Y` gives `(rUd pkSeedDist W).pick`. -/
theorem rUd_pickS_interp (W : WotsGame.Adversary prims) :
    simulateQ dropS (rUdPickS (vp := vp) pkSeedDist W) = (rUd pkSeedDist W).pick := by
  unfold rUdPickS
  rw [simulateQ_bind, drop_emb]
  exact bind_congr fun k =>
    simChooseS_interp W _ _ _ _ (udStartS_interp pkSeedDist k.val)

/-- **Wrapper samples of `rUd pkSeedDist W`** (any `W`, in particular `Lazy.bWotsS A`): at most
`#inst · len` values of `prims.Y` (besides the one hybrid index). -/
theorem rUd_wrapper_samples_le (W : WotsGame.Adversary prims) :
    IsQueryBoundP (rUdPickS (vp := vp) pkSeedDist W) isSamp
      ((wotsInsts vp).length * vp.params.len) := by
  have h2 : ∀ k : Fin (vp.params.w - 3 + 1),
      IsQueryBoundP (WotsGame.simChoose W (wotsInsts vp) (udStartS pkSeedDist k.val)
        (fun a x => simulateQ embS (udChainHash pkSeedDist a x))
        (fun key xs => simulateQ embS (udColl pkSeedDist key xs))) isSamp
        ((wotsInsts vp).length * vp.params.len) := fun k =>
    simChooseS_samples W _ _ _ (udStartS_qb pkSeedDist k.val) (fun a y => emb_qb _)
      (fun key xs => emb_qb _)
  have h := Lazy.qb_bind isSamp (n := 0) (emb_qb (prims := prims) ((monadLift
      ($ᵗ (Fin (vp.params.w - 3 + 1)) : ProbComp (Fin (vp.params.w - 3 + 1))) :
    OracleComp (UdSpec (vp := vp) (prims := prims) pkSeedDist) (Fin (vp.params.w - 3 + 1))))) h2
  rw [Nat.zero_add] at h
  exact h

/-! ## SM-PRE -/

abbrev PreSpecS (pkSeedDist : ProbComp prims.PkSeed) :=
  unifSpec + (sampSpec prims + (SM_DT_PRE_challengeSpec prims.AdrsKey prims.Y +
    collectionSpec (wotsPreProblem vp prims pkSeedDist).thColl))

/-- `preStart` with its sample explicit. -/
noncomputable def preStartS (ca : Adrs) (b : ℕ) :
    OracleComp (PreSpecS (vp := vp) (prims := prims) pkSeedDist) prims.Y :=
  if b = 0 then sampQ
  else simulateQ embS (preChal pkSeedDist (prims.adrsToKey (ca.setHashAddress (b - 1))))

theorem preStartS_interp (ca : Adrs) (b : ℕ) :
    simulateQ dropS (preStartS (vp := vp) pkSeedDist ca b) = preStart pkSeedDist ca b := by
  unfold preStartS preStart
  split_ifs with h
  · exact dropS_sampQ
  · exact drop_emb _

theorem preStartS_qb (ca : Adrs) (b : ℕ) :
    IsQueryBoundP (preStartS (vp := vp) pkSeedDist ca b) isSamp 1 := by
  unfold preStartS
  split_ifs with h
  · simp [sampQ]
  · exact (emb_qb _).mono (by omega)

/-- **Phase 1 of `rPre pkSeedDist W` with the wrapper's samples explicit.** -/
noncomputable def rPreChooseS (W : WotsGame.Adversary prims) :
    OracleComp (PreSpecS (vp := vp) (prims := prims) pkSeedDist)
      (W.State × List (WotsGame.Entry prims)) :=
  WotsGame.simChoose W (wotsInsts vp) (preStartS pkSeedDist)
    (fun a x => simulateQ embS (preChainHash pkSeedDist a x))
    (fun key xs => simulateQ embS (preColl pkSeedDist key xs))

theorem rPre_chooseS_interp (W : WotsGame.Adversary prims) :
    simulateQ dropS (rPreChooseS (vp := vp) pkSeedDist W) = (rPre pkSeedDist W).choose :=
  simChooseS_interp W _ _ _ _ (preStartS_interp pkSeedDist)

/-- **Wrapper samples of `rPre pkSeedDist W`** (any `W`): at most `#inst · len`. -/
theorem rPre_wrapper_samples_le (W : WotsGame.Adversary prims) :
    IsQueryBoundP (rPreChooseS (vp := vp) pkSeedDist W) isSamp
      ((wotsInsts vp).length * vp.params.len) :=
  simChooseS_samples W _ _ _ (preStartS_qb pkSeedDist) (fun a y => emb_qb _)
    (fun key xs => emb_qb _)

/-! ## SM-TCR on chains -/

abbrev WTcrSpecS (pkSeedDist : ProbComp prims.PkSeed) :=
  unifSpec + (sampSpec prims + (SM_DT_TCR_challengeSpec prims.AdrsKey prims.Y prims.Y +
    collectionSpec (wotsTcrProblem vp prims pkSeedDist).thColl))

/-- `tcrStart` with its sample explicit. -/
noncomputable def tcrStartS (ca : Adrs) (b : ℕ) :
    OracleComp (WTcrSpecS (vp := vp) (prims := prims) pkSeedDist) prims.Y :=
  sampQ >>= fun s => simulateQ embS
    (if b = 0 then (pure s : OracleComp (WTcrSpec (vp := vp) (prims := prims) pkSeedDist) prims.Y)
      else wtcrColl pkSeedDist (prims.adrsToKey (ca.setHashAddress (b - 1))) [s])

theorem tcrStartS_interp (ca : Adrs) (b : ℕ) :
    simulateQ dropS (tcrStartS (vp := vp) pkSeedDist ca b) = tcrStart pkSeedDist ca b := by
  unfold tcrStartS tcrStart
  rw [simulateQ_bind, dropS_sampQ]
  simp only [drop_emb]

theorem tcrStartS_qb (ca : Adrs) (b : ℕ) :
    IsQueryBoundP (tcrStartS (vp := vp) pkSeedDist ca b) isSamp 1 := by
  unfold tcrStartS
  exact Lazy.qb_bind _ (n := 1) (m := 0) (by simp [sampQ]) fun s => emb_qb _

/-- **Phase 1 of `rTcr pkSeedDist W` (= phase 1 of `rTcrT pkSeedDist W`) with the wrapper's
samples explicit.** -/
noncomputable def rTcrChooseS (W : WotsGame.Adversary prims) :
    OracleComp (WTcrSpecS (vp := vp) (prims := prims) pkSeedDist)
      (W.State × List (WotsGame.Entry prims)) :=
  WotsGame.simChoose W (wotsInsts vp) (tcrStartS pkSeedDist)
    (fun a x => simulateQ embS (tcrChainHash pkSeedDist a x))
    (fun key xs => simulateQ embS (wtcrColl pkSeedDist key xs))

theorem rTcr_chooseS_interp (W : WotsGame.Adversary prims) :
    simulateQ dropS (rTcrChooseS (vp := vp) pkSeedDist W) = (rTcr pkSeedDist W).choose :=
  simChooseS_interp W _ _ _ _ (tcrStartS_interp pkSeedDist)

theorem rTcrT_chooseS_interp (W : WotsGame.Adversary prims) :
    simulateQ dropS (rTcrChooseS (vp := vp) pkSeedDist W) =
      (rTcrT (vp := vp) pkSeedDist W).choose :=
  rTcr_chooseS_interp pkSeedDist W

/-- **Wrapper samples of `rTcr pkSeedDist W` / `rTcrT pkSeedDist W`** (any `W`): at most
`#inst · len` (one per chain of an accepted signing query). -/
theorem rTcr_wrapper_samples_le (W : WotsGame.Adversary prims) :
    IsQueryBoundP (rTcrChooseS (vp := vp) pkSeedDist W) isSamp
      ((wotsInsts vp).length * vp.params.len) :=
  simChooseS_samples W _ _ _ (tcrStartS_qb pkSeedDist) (fun a y => emb_qb _)
    (fun key xs => emb_qb _)

/-- Stable name for the tight-cap adversary (same program, `rTcrT_chooseS_interp`). -/
theorem rTcrT_wrapper_samples_le (W : WotsGame.Adversary prims) :
    IsQueryBoundP (rTcrChooseS (vp := vp) pkSeedDist W) isSamp
      ((wotsInsts vp).length * vp.params.len) :=
  rTcr_wrapper_samples_le pkSeedDist W

/-- `#inst · len` at SLH-DSA-SHA2-128s (`≈ 2^68.13`). -/
theorem wrapper_samples_128s :
    (wotsInsts Link.vp).length * Link.vp.params.len = 323449759100660631040 := by
  rw [← Resources.wotsChainTargets_eq, Resources.wotsChainTargets_128s_val]

end Open
end Reduction

#print axioms Reduction.Open.rUd_pickS_interp
#print axioms Reduction.Open.rUd_wrapper_samples_le
#print axioms Reduction.Open.rPre_chooseS_interp
#print axioms Reduction.Open.rPre_wrapper_samples_le
#print axioms Reduction.Open.rTcr_chooseS_interp
#print axioms Reduction.Open.rTcrT_chooseS_interp
#print axioms Reduction.Open.rTcr_wrapper_samples_le
#print axioms Reduction.Open.rTcrT_wrapper_samples_le
#print axioms Reduction.Open.wrapper_samples_128s
