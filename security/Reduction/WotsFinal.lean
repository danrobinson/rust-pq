import Reduction.WotsSim

/-!
# Step 9: the last hybrid (`Hyb_{w-2} ≤ SM-PRE + SM-TCR` on `F`)

In `hyb (w - 2)` a chain with digit `b ≥ 1` reveals `F(adrs(b-1), u)` for a uniform, otherwise
unused `u`, and a chain with `b = 0` reveals its uniform start value.  A winning forgery signs
`m' ≠ m`, so (WOTS+ checksum, `chainStepsCore_two_encodings`) some chain has `b' < b`; VCVio's
`wotsPkFromSigTops_cases` then gives either an `F`-preimage of the revealed value at step `b - 1`
(`rPre` wins SM-PRE) or an `F`-collision at a step `t ≥ b` against the honest chain value
(`rTcr` wins SM-TCR).  EC: `R_SMDTPREC_Game4WOTSTWES`, `R_SMDTTCRC_Game34WOTSTWES`.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal TweakableHash

namespace Reduction

set_option linter.unusedSectionVars false

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]

/-! ## SM-PRE -/

/-- Oracle interface of an SM-PRE adversary for `wotsPreProblem`. -/
abbrev PreSpec (pkSeedDist : ProbComp prims.PkSeed) :=
  unifSpec + (TweakableHash.SM_DT_PRE_challengeSpec prims.AdrsKey prims.Y +
    TweakableHash.collectionSpec (wotsPreProblem vp prims pkSeedDist).thColl)

/-- Collection query of the SM-PRE game. -/
def preColl (pkSeedDist : ProbComp prims.PkSeed) (key : prims.AdrsKey) (xs : List prims.Y) :
    OracleComp (PreSpec (vp := vp) (prims := prims) pkSeedDist) prims.Y := do
  let r ← ((PreSpec (vp := vp) (prims := prims) pkSeedDist).query
      (Sum.inr (Sum.inr ⟨(), key, xs⟩)) :
    OracleComp (PreSpec (vp := vp) (prims := prims) pkSeedDist) (Option prims.Y))
  pure (r.getD default)

/-- Challenge query of the SM-PRE game. -/
def preChal (pkSeedDist : ProbComp prims.PkSeed) (key : prims.AdrsKey) :
    OracleComp (PreSpec (vp := vp) (prims := prims) pkSeedDist) prims.Y := do
  let r ← ((PreSpec (vp := vp) (prims := prims) pkSeedDist).query (Sum.inr (Sum.inl key)) :
    OracleComp (PreSpec (vp := vp) (prims := prims) pkSeedDist) (Option prims.Y))
  pure (r.getD default)

/-- Number of chains of a message with nonzero digit among the first `n` chains: the number of
SM-PRE targets `rPre` requests for them. -/
def preCount (msg : prims.Y) (n : ℕ) : ℕ :=
  ((List.range n).filter fun i => chainStepsCore prims.core msg i ≠ 0).length

/-- Index, in `rPre`'s challenge history, of the target of chain `i` of history entry `j`. -/
def preTargetIndex (hist : List (WotsGame.Entry prims)) (j : ℕ) (i : ℕ) : ℕ :=
  ((hist.take j).map fun e => preCount e.2.1 vp.params.len).sum +
    match hist[j]? with
    | none => 0
    | some e => preCount e.2.1 i

/-- The SM-PRE answer extracted from a WOTS forgery: the first chain with a smaller forged digit
whose forged value, advanced to step `b - 1`, is an `F`-preimage of the revealed value. -/
def preAnswer (pk : prims.PkSeed) (hist : List (WotsGame.Entry prims)) (j : ℕ) (m' : prims.Y)
    (sig' : WotsSig vp.params prims.core) : ℕ × prims.Y :=
  match hist[j]? with
  | none => (0, default)
  | some (a, m, sig, _) =>
    ((List.finRange vp.params.len).findSome? fun i =>
      let b := chainStepsCore prims.core m i.val
      let b' := chainStepsCore prims.core m' i.val
      let x := chain prims pk (wotsChainAdrs a i.val) sig'[i.val] b' (b - 1 - b')
      if b' < b ∧ prims.F pk ((wotsChainAdrs a i.val).setHashAddress (b - 1)) x = sig[i.val] then
        some (preTargetIndex hist j i.val, x)
      else none).getD (0, default)

/-- How `rPre` produces the revealed value of a chain with digit `b`: a fresh uniform value if
`b = 0`, an SM-PRE challenge at step `b - 1` otherwise. -/
noncomputable def preStart (pkSeedDist : ProbComp prims.PkSeed) (ca : Adrs) (b : ℕ) :
    OracleComp (PreSpec (vp := vp) (prims := prims) pkSeedDist) prims.Y :=
  if b = 0 then
    (monadLift ($ᵗ prims.Y : ProbComp prims.Y) :
      OracleComp (PreSpec (vp := vp) (prims := prims) pkSeedDist) prims.Y)
  else preChal pkSeedDist (prims.adrsToKey (ca.setHashAddress (b - 1)))

/-- How `rPre` continues a chain: through the collection oracle. -/
def preChainHash (pkSeedDist : ProbComp prims.PkSeed) (a : Adrs) (x : prims.Y) :
    OracleComp (PreSpec (vp := vp) (prims := prims) pkSeedDist) prims.Y :=
  preColl pkSeedDist (prims.adrsToKey a) [x]

/-- The SM-PRE adversary built from a WOTS-game adversary. -/
noncomputable def rPre (pkSeedDist : ProbComp prims.PkSeed) (W : WotsGame.Adversary prims) :
    TweakableHash.SM_DT_PRE_Adversary (wotsPreProblem vp prims pkSeedDist) where
  State := W.State × List (WotsGame.Entry prims)
  choose :=
    WotsGame.simChoose W (wotsInsts vp) (preStart pkSeedDist) (preChainHash pkSeedDist)
      (preColl pkSeedDist)
  invert := fun st pk => do
    let (j, m', sig') ← W.forge st.1 pk
    return preAnswer pk st.2 j m' sig'

/-! ## SM-TCR -/

/-- Oracle interface of an SM-TCR adversary for `wotsTcrProblem`. -/
abbrev WTcrSpec (pkSeedDist : ProbComp prims.PkSeed) :=
  unifSpec + (TweakableHash.SM_DT_TCR_challengeSpec prims.AdrsKey prims.Y prims.Y +
    TweakableHash.collectionSpec (wotsTcrProblem vp prims pkSeedDist).thColl)

/-- Collection query of the SM-TCR game. -/
def wtcrColl (pkSeedDist : ProbComp prims.PkSeed) (key : prims.AdrsKey) (xs : List prims.Y) :
    OracleComp (WTcrSpec (vp := vp) (prims := prims) pkSeedDist) prims.Y := do
  let r ← ((WTcrSpec (vp := vp) (prims := prims) pkSeedDist).query
      (Sum.inr (Sum.inr ⟨(), key, xs⟩)) :
    OracleComp (WTcrSpec (vp := vp) (prims := prims) pkSeedDist) (Option prims.Y))
  pure (r.getD default)

/-- Challenge query of the SM-TCR game. -/
def wtcrChal (pkSeedDist : ProbComp prims.PkSeed) (key : prims.AdrsKey) (x : prims.Y) :
    OracleComp (WTcrSpec (vp := vp) (prims := prims) pkSeedDist) prims.Y := do
  let r ← ((WTcrSpec (vp := vp) (prims := prims) pkSeedDist).query (Sum.inr (Sum.inl (key, x))) :
    OracleComp (WTcrSpec (vp := vp) (prims := prims) pkSeedDist) (Option prims.Y))
  pure (r.getD default)

/-- Number of chain steps `rTcr` submits as targets for the first `n` chains of a message. -/
def tcrCount (msg : prims.Y) (n : ℕ) : ℕ :=
  ((List.range n).map fun i => vp.params.w - 1 - chainStepsCore prims.core msg i).sum

/-- Index, in `rTcr`'s challenge history, of step `t` of chain `i` of history entry `j`. -/
def tcrTargetIndex (hist : List (WotsGame.Entry prims)) (j : ℕ) (i t : ℕ) : ℕ :=
  ((hist.take j).map fun e => tcrCount e.2.1 vp.params.len).sum +
    match hist[j]? with
    | none => 0
    | some e => tcrCount e.2.1 i + (t - chainStepsCore prims.core e.2.1 i)

/-- The SM-TCR answer extracted from a WOTS forgery: the first chain and step at or above the
honest digit where the forged and honest chain values differ but hash to the same value. -/
def tcrAnswer (pk : prims.PkSeed) (hist : List (WotsGame.Entry prims)) (j : ℕ) (m' : prims.Y)
    (sig' : WotsSig vp.params prims.core) : ℕ × prims.Y :=
  match hist[j]? with
  | none => (0, default)
  | some (a, m, sig, _) =>
    ((List.finRange vp.params.len).findSome? fun i =>
      let b := chainStepsCore prims.core m i.val
      let b' := chainStepsCore prims.core m' i.val
      (List.range (vp.params.w - 1)).findSome? fun t =>
        let fv := chain prims pk (wotsChainAdrs a i.val) sig'[i.val] b' (t - b')
        let hv := chain prims pk (wotsChainAdrs a i.val) sig[i.val] b (t - b)
        if b ≤ t ∧ b' ≤ t ∧ fv ≠ hv ∧
            prims.F pk ((wotsChainAdrs a i.val).setHashAddress t) fv =
              prims.F pk ((wotsChainAdrs a i.val).setHashAddress t) hv then
          some (tcrTargetIndex hist j i.val t, fv)
        else none).getD (0, default)

/-- How `rTcr` produces the revealed value of a chain with digit `b`: it samples the start value
itself and takes the one hidden step (if any) through the collection oracle. -/
noncomputable def tcrStart (pkSeedDist : ProbComp prims.PkSeed) (ca : Adrs) (b : ℕ) :
    OracleComp (WTcrSpec (vp := vp) (prims := prims) pkSeedDist) prims.Y := do
  let s ← (monadLift ($ᵗ prims.Y : ProbComp prims.Y) :
    OracleComp (WTcrSpec (vp := vp) (prims := prims) pkSeedDist) prims.Y)
  if b = 0 then pure s
  else wtcrColl pkSeedDist (prims.adrsToKey (ca.setHashAddress (b - 1))) [s]

/-- How `rTcr` continues a chain: every step is submitted as an SM-TCR target. -/
def tcrChainHash (pkSeedDist : ProbComp prims.PkSeed) (a : Adrs) (x : prims.Y) :
    OracleComp (WTcrSpec (vp := vp) (prims := prims) pkSeedDist) prims.Y :=
  wtcrChal pkSeedDist (prims.adrsToKey a) x

/-- The SM-TCR adversary built from a WOTS-game adversary: it knows every start value (sampling
it itself and taking the one hidden step through the collection oracle) and submits every chain
step from the revealed position upward as a target. -/
noncomputable def rTcr (pkSeedDist : ProbComp prims.PkSeed) (W : WotsGame.Adversary prims) :
    TweakableHash.SM_DT_TCR_Adversary (wotsTcrProblem vp prims pkSeedDist) where
  State := W.State × List (WotsGame.Entry prims)
  choose :=
    WotsGame.simChoose W (wotsInsts vp) (tcrStart pkSeedDist) (tcrChainHash pkSeedDist)
      (wtcrColl pkSeedDist)
  forge := fun st pk => do
    let (j, m', sig') ← W.forge st.1 pk
    return tcrAnswer pk st.2 j m' sig'

/-! ## Lemmas -/

/-- **Deterministic extraction for the WOTS game.**  A winning forgery against a history entry
yields a correct `preAnswer` or a correct `tcrAnswer` (from `wotsPkFromSigTops_cases`). -/
theorem win_cases (hS : Structural vp prims) (pk : prims.PkSeed)
    (hist : List (WotsGame.Entry prims)) (j : ℕ) (m' : prims.Y)
    (sig' : WotsSig vp.params prims.core) (e : WotsGame.Entry prims) (he : hist[j]? = some e)
    (hwin : WotsGame.win pk hist j m' sig' = true)
    (htops : e.2.2.2 = wotsPkFromSigTops prims e.2.2.1 e.2.1 pk e.1) :
    (∃ i : Fin vp.params.len, chainStepsCore prims.core m' i.val < chainStepsCore prims.core e.2.1 i.val ∧
        prims.F pk ((wotsChainAdrs e.1 i.val).setHashAddress (chainStepsCore prims.core e.2.1 i.val - 1))
          (preAnswer pk hist j m' sig').2 = e.2.2.1[i.val] ∧
        (preAnswer pk hist j m' sig').1 = preTargetIndex hist j i.val) ∨
    (∃ (i : Fin vp.params.len) (t : ℕ), chainStepsCore prims.core e.2.1 i.val ≤ t ∧ t < vp.params.w - 1 ∧
        (tcrAnswer pk hist j m' sig').1 = tcrTargetIndex hist j i.val t ∧
        (tcrAnswer pk hist j m' sig').2 ≠
          chain prims pk (wotsChainAdrs e.1 i.val) e.2.2.1[i.val]
            (chainStepsCore prims.core e.2.1 i.val) (t - chainStepsCore prims.core e.2.1 i.val) ∧
        prims.F pk ((wotsChainAdrs e.1 i.val).setHashAddress t) (tcrAnswer pk hist j m' sig').2 =
          prims.F pk ((wotsChainAdrs e.1 i.val).setHashAddress t)
            (chain prims pk (wotsChainAdrs e.1 i.val) e.2.2.1[i.val]
              (chainStepsCore prims.core e.2.1 i.val)
              (t - chainStepsCore prims.core e.2.1 i.val))) := by
  obtain ⟨a, m, sig, tops⟩ := e
  have hwin' : m' ≠ m ∧ wotsPkFromSigTops prims sig' m' pk a = tops := by
    simpa [WotsGame.win, he] using hwin
  obtain ⟨hne, htops'⟩ := hwin'
  have htops2 : tops = wotsPkFromSigTops prims sig m pk a := htops
  obtain ⟨i, hlt, hcase⟩ := wotsPkFromSigTops_cases vp.valid prims hS.byteLaws sig' sig m' m pk a
    hne (htops'.trans htops2)
  rcases hcase with hpre | ⟨t, hbt, htw, hneq, hcoll⟩
  · left
    simp only [preAnswer, he]
    cases hfs : (List.finRange vp.params.len).findSome? fun i : Fin vp.params.len =>
        if chainStepsCore prims.core m' i.val < chainStepsCore prims.core m i.val ∧
            prims.F pk ((wotsChainAdrs a i.val).setHashAddress
                (chainStepsCore prims.core m i.val - 1))
              (chain prims pk (wotsChainAdrs a i.val) sig'[i.val]
                (chainStepsCore prims.core m' i.val)
                (chainStepsCore prims.core m i.val - 1 - chainStepsCore prims.core m' i.val)) =
              sig[i.val] then
          some (preTargetIndex hist j i.val,
            chain prims pk (wotsChainAdrs a i.val) sig'[i.val]
              (chainStepsCore prims.core m' i.val)
              (chainStepsCore prims.core m i.val - 1 - chainStepsCore prims.core m' i.val))
        else none with
    | none =>
      exfalso
      have h := List.findSome?_eq_none_iff.mp hfs i (List.mem_finRange i)
      rw [if_pos ⟨hlt, hpre⟩] at h
      exact Option.some_ne_none _ h
    | some r =>
      obtain ⟨i', -, hi'⟩ := List.exists_of_findSome?_eq_some hfs
      split_ifs at hi' with hc
      cases hi'
      exact ⟨i', hc.1, hc.2, rfl⟩
  · right
    simp only [tcrAnswer, he]
    cases hfs : (List.finRange vp.params.len).findSome? fun i : Fin vp.params.len =>
        (List.range (vp.params.w - 1)).findSome? fun t =>
          if chainStepsCore prims.core m i.val ≤ t ∧ chainStepsCore prims.core m' i.val ≤ t ∧
              chain prims pk (wotsChainAdrs a i.val) sig'[i.val]
                  (chainStepsCore prims.core m' i.val) (t - chainStepsCore prims.core m' i.val) ≠
                chain prims pk (wotsChainAdrs a i.val) sig[i.val]
                  (chainStepsCore prims.core m i.val) (t - chainStepsCore prims.core m i.val) ∧
              prims.F pk ((wotsChainAdrs a i.val).setHashAddress t)
                  (chain prims pk (wotsChainAdrs a i.val) sig'[i.val]
                    (chainStepsCore prims.core m' i.val)
                    (t - chainStepsCore prims.core m' i.val)) =
                prims.F pk ((wotsChainAdrs a i.val).setHashAddress t)
                  (chain prims pk (wotsChainAdrs a i.val) sig[i.val]
                    (chainStepsCore prims.core m i.val)
                    (t - chainStepsCore prims.core m i.val)) then
            some (tcrTargetIndex hist j i.val t,
              chain prims pk (wotsChainAdrs a i.val) sig'[i.val]
                (chainStepsCore prims.core m' i.val) (t - chainStepsCore prims.core m' i.val))
          else none with
    | none =>
      exfalso
      have h := List.findSome?_eq_none_iff.mp
        (List.findSome?_eq_none_iff.mp hfs i (List.mem_finRange i)) t (List.mem_range.mpr htw)
      rw [if_pos ⟨hbt, le_trans hlt.le hbt, hneq, hcoll⟩] at h
      exact Option.some_ne_none _ h
    | some r =>
      obtain ⟨i', -, hi'⟩ := List.exists_of_findSome?_eq_some hfs
      obtain ⟨t', ht', hi''⟩ := List.exists_of_findSome?_eq_some hi'
      split_ifs at hi'' with hc
      cases hi''
      exact ⟨i', t', hc.1, List.mem_range.mp ht', rfl, hc.2.2.1, hc.2.2.2⟩

/-! Helper lemmas live in `Reduction.WotsFinal` to avoid name clashes with other packages. -/

namespace WotsFinal

/-! ## Generic tools: nested simulation with an invariant, and `Vector.ofFnM` runs -/

section Tools
variable {ι₀ ι₁ : Type} {spec₀ : OracleSpec ι₀} {spec₁ : OracleSpec ι₁} {H Sg : Type}

theorem nested_run (S : QueryImpl spec₀ (StateT H (OracleComp spec₁)))
    (O : QueryImpl spec₁ (StateT Sg ProbComp)) (G : QueryImpl spec₀ (StateT H ProbComp))
    (I : H → Sg → Prop)
    (hstep : ∀ (q : spec₀.Domain) (h : H) (σ : Sg), I h σ →
      ∃ (γ : Type) (mx : ProbComp γ) (F : γ → (spec₀.Range q × H) × Sg),
        (simulateQ O ((S q).run h)).run σ =ᵈ F <$> mx ∧
        (G q).run h =ᵈ (fun c => (F c).1) <$> mx ∧ ∀ c, I (F c).1.2 (F c).2)
    {α : Type} (oa : OracleComp spec₀ α) (h : H) (σ : Sg) (hI : I h σ) :
    ((fun z => z.1) <$> (simulateQ O ((simulateQ S oa).run h)).run σ) =ᵈ (simulateQ G oa).run h ∧
    ∀ z ∈ support ((simulateQ O ((simulateQ S oa).run h)).run σ), I z.1.2 z.2 := by
  induction oa using OracleComp.inductionOn generalizing h σ with
  | pure x => simp [hI]
  | query_bind t oa ih =>
    obtain ⟨γ, mx, F, hA, hG, hI'⟩ := hstep t h σ hI
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, StateT.run_bind, map_bind]
    constructor
    · refine (hA.bind_left _).trans ?_
      rw [bind_map_left]
      refine (EvalDistEq.bind_right mx (fun c => (ih _ _ _ (hI' c)).1)).trans ?_
      refine EvalDistEq.trans ?_ (hG.symm.bind_left _)
      rw [bind_map_left]
    · intro z hz
      rw [mem_support_bind_iff] at hz
      obtain ⟨w, hw, hz⟩ := hz
      rw [support_eq_of_evalDistEq hA, support_map] at hw
      obtain ⟨c, -, rfl⟩ := hw
      exact (ih _ _ _ (hI' c)).2 z hz
theorem vector_push_ofFn {α β : Type} {n : ℕ} (g : Fin (n + 1) → β → α) (us : Vector β n) (u : β) :
    (Vector.ofFn fun i : Fin n => g i.castSucc us[i]).push (g (Fin.last n) u) =
      Vector.ofFn fun i : Fin (n + 1) => g i (us.push u)[i] := by
  ext i hi
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
  · simp [Vector.getElem_push, h]
  · subst h
    simp [Vector.getElem_push]
    rfl

theorem vector_back_push {β : Type} {n : ℕ} (us : Vector β n) (u : β) : (us.push u).back = u := by
  simp [Vector.back]

theorem vector_zero_eq {α : Type} (w : Vector α 0) : w = #v[] := by ext i hi; omega

theorem ofFnM_run_sample {β α : Type} [SampleableType β] (O : QueryImpl spec₁ (StateT Sg ProbComp))
    (J : (k : ℕ) → Vector β k → Sg → Prop) :
    ∀ {n : ℕ} (f : Fin n → OracleComp spec₁ α) (g : Fin n → β → α) (step : Fin n → β → Sg → Sg)
    (_ : ∀ (i : Fin n) (us : Vector β i.val) (σ : Sg), J i.val us σ →
       ((simulateQ O (f i)).run σ =ᵈ (fun u => (g i u, step i u σ)) <$> ($ᵗ β : ProbComp β)) ∧
        ∀ u, J (i.val + 1) (us.push u) (step i u σ))
    (σ₀ : Sg) (_ : J 0 #v[] σ₀),
    ∃ fin : Vector β n → Sg,
      (simulateQ O (Vector.ofFnM f)).run σ₀ =ᵈ
        (fun us : Vector β n => (Vector.ofFn fun i => g i us[i], fin us)) <$>
          ($ᵗ (Vector β n) : ProbComp _) ∧ ∀ us, J n us (fin us) := by
  intro n
  induction n with
  | zero =>
    intro f g step hf σ₀ h0
    refine ⟨fun _ => σ₀, ?_, fun us => ?_⟩
    · have : ($ᵗ (Vector β 0) : ProbComp _) = pure #v[] := rfl
      rw [this]
      simp only [Vector.ofFnM_zero, simulateQ_pure, StateT.run_pure, map_pure]
      rw [vector_zero_eq (Vector.ofFn _)]
    · rw [vector_zero_eq us]; exact h0
  | succ n ih =>
    intro f g step hf σ₀ h0
    obtain ⟨fin', hX, hJ'⟩ := ih (fun i => f i.castSucc) (fun i => g i.castSucc)
      (fun i => step i.castSucc) (fun i us σ hJ => hf i.castSucc us σ hJ) σ₀ h0
    refine ⟨fun us => step (Fin.last n) us.back (fin' us.pop), ?_, fun us => ?_⟩
    · simp only [Vector.ofFnM_succ, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure]
      refine (hX.bind_left _).trans ?_
      rw [bind_map_left]
      refine (EvalDistEq.bind_right _
        (fun us => ((hf (Fin.last n) us (fin' us) (hJ' us)).1.bind_left _))).trans ?_
      have : ($ᵗ (Vector β (n + 1)) : ProbComp _) =
          Vector.push <$> ($ᵗ (Vector β n) : ProbComp _) <*> ($ᵗ β : ProbComp β) := rfl
      rw [this]
      simp only [bind_map_left, seq_eq_bind_map, map_bind, Functor.map_map, bind_pure_comp]
      simp only [vector_push_ofFn, Vector.pop_push, vector_back_push]
      exact EvalDistEq.rfl
    · have := (hf (Fin.last n) us.pop (fin' us.pop) (hJ' us.pop)).2 us.back
      rwa [Vector.push_pop_back] at this

theorem ofFnM_run_det {α : Type} (O : QueryImpl spec₁ (StateT Sg ProbComp))
    (J : ℕ → Sg → Prop) :
    ∀ {n : ℕ} (f : Fin n → OracleComp spec₁ α) (v : Fin n → α) (step : Fin n → Sg → Sg)
    (_ : ∀ (i : Fin n) (σ : Sg), J i.val σ →
       ((simulateQ O (f i)).run σ =ᵈ (pure (v i, step i σ) : ProbComp _)) ∧ J (i.val + 1) (step i σ))
    (σ₀ : Sg) (_ : J 0 σ₀),
    ∃ fin : Sg,
      (simulateQ O (Vector.ofFnM f)).run σ₀ =ᵈ (pure (Vector.ofFn v, fin) : ProbComp _) ∧
        J n fin := by
  intro n
  induction n with
  | zero =>
    intro f v step hf σ₀ h0
    refine ⟨σ₀, ?_, h0⟩
    simp only [Vector.ofFnM_zero, simulateQ_pure, StateT.run_pure]
    rw [vector_zero_eq (Vector.ofFn _)]
  | succ n ih =>
    intro f v step hf σ₀ h0
    obtain ⟨fin', hX, hJ'⟩ := ih (fun i => f i.castSucc) (fun i => v i.castSucc)
      (fun i => step i.castSucc) (fun i σ hJ => hf i.castSucc σ hJ) σ₀ h0
    refine ⟨step (Fin.last n) fin', ?_, (hf (Fin.last n) fin' hJ').2⟩
    simp only [Vector.ofFnM_succ, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure]
    refine (hX.bind_left _).trans ?_
    rw [pure_bind]
    refine ((hf (Fin.last n) fin' hJ').1.bind_left _).trans ?_
    rw [pure_bind]
    have := vector_push_ofFn (fun i (_ : Unit) => v i) (Vector.replicate n ()) ()
    rw [show (Vector.ofFn fun i : Fin n => v i.castSucc).push (v (Fin.last n)) = Vector.ofFn v from this]
end Tools

/-! ## The WOTS-game simulator run inside an SM game -/

section Sim
variable {ι : Type} {spec : OracleSpec ι} {Sg : Type}

/-- The outer oracle of a reduction: uniform sampling is forwarded. -/
abbrev outer (O₂ : QueryImpl spec (StateT Sg ProbComp)) :
    QueryImpl (unifSpec + spec) (StateT Sg ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT Sg ProbComp) + O₂

abbrev simImpl (insts : List Adrs)
    (startVal : Adrs → ℕ → OracleComp (unifSpec + spec) prims.Y)
    (chainHash : Adrs → prims.Y → OracleComp (unifSpec + spec) prims.Y)
    (coll : prims.AdrsKey → List prims.Y → OracleComp (unifSpec + spec) prims.Y) :=
  ((QueryImpl.ofLift unifSpec (OracleComp (unifSpec + spec))).liftTarget
        (StateT (List (WotsGame.Entry prims)) (OracleComp (unifSpec + spec))) +
      (WotsGame.simSignOracle insts startVal chainHash + WotsGame.simCollOracle insts coll))

theorem outer_lift (O₂ : QueryImpl spec (StateT Sg ProbComp)) {α : Type} (oa : ProbComp α) (σ : Sg) :
    (simulateQ (outer O₂) (monadLift oa : OracleComp (unifSpec + spec) α)).run σ =
      (fun a => (a, σ)) <$> oa := by
  have : (monadLift oa : OracleComp (unifSpec + spec) α) = oa.liftComp (unifSpec + spec) := rfl
  rw [this, outer, QueryImpl.simulateQ_add_liftComp_left, simulateQ_liftTarget]
  simp

theorem sim_step (O₂ : QueryImpl spec (StateT Sg ProbComp)) (k : ℕ) (insts : List Adrs)
    (pk : prims.PkSeed)
    (startVal : Adrs → ℕ → OracleComp (unifSpec + spec) prims.Y)
    (chainHash : Adrs → prims.Y → OracleComp (unifSpec + spec) prims.Y)
    (coll : prims.AdrsKey → List prims.Y → OracleComp (unifSpec + spec) prims.Y)
    (I : List (WotsGame.Entry prims) → Sg → Prop)
    (hcoll : ∀ hist σ key xs, I hist σ → WotsGame.reservedKey insts key = false →
      ∃ σ', (simulateQ (outer O₂) (coll key xs)).run σ =ᵈ
        (pure (prims.Thash pk key xs, σ') : ProbComp _) ∧ I hist σ')
    (hsign : ∀ hist σ a m, I hist σ → a ∈ insts → a ∉ hist.map (·.1) →
      ∃ fin1 : Vector prims.Y vp.params.len → Sg,
        (simulateQ (outer O₂) (Vector.ofFnM fun i : Fin vp.params.len =>
            startVal (wotsChainAdrs a i.val) (chainStepsCore prims.core m i.val))).run σ =ᵈ
          (fun ss => (WotsGame.hybSig k pk a m ss, fin1 ss)) <$>
            ($ᵗ (Vector prims.Y vp.params.len) : ProbComp _) ∧
        ∀ ss, ∃ fin2,
          (simulateQ (outer O₂) (wotsPkFromSigTopsWith prims.core chainHash
              (WotsGame.hybSig k pk a m ss) m a)).run (fin1 ss) =ᵈ
            (pure (wotsPkFromSigTops prims (WotsGame.hybSig k pk a m ss) m pk a, fin2) :
              ProbComp _) ∧
          I (hist ++ [(a, m, WotsGame.hybSig k pk a m ss,
            wotsPkFromSigTops prims (WotsGame.hybSig k pk a m ss) m pk a)]) fin2)
    (q : (unifSpec + (WotsGame.signSpec prims + WotsGame.collSpec prims)).Domain)
    (h : List (WotsGame.Entry prims)) (σ : Sg) (hI : I h σ) :
    ∃ (γ : Type) (mx : ProbComp γ)
      (F : γ → ((unifSpec + (WotsGame.signSpec prims + WotsGame.collSpec prims)).Range q ×
        List (WotsGame.Entry prims)) × Sg),
      (simulateQ (outer O₂) ((simImpl insts startVal chainHash coll q).run h)).run σ =ᵈ F <$> mx ∧
      (WotsGame.oracles k insts pk q).run h =ᵈ (fun c => (F c).1) <$> mx ∧
      ∀ c, I (F c).1.2 (F c).2 := by
  rcases q with n | q | q
  · refine ⟨_, (liftM (unifSpec.query n) : ProbComp _), fun u => ((u, h), σ), ?_, ?_, fun _ => hI⟩
    · have h1 : (simImpl (prims := prims) insts startVal chainHash coll (Sum.inl n)).run h =
          (monadLift ((fun u => (u, h)) <$> (liftM (unifSpec.query n) : ProbComp _)) :
            OracleComp (unifSpec + spec) _) := by
        simp [simImpl]
        rfl
      rw [h1, outer_lift]
      simp
    · simp [WotsGame.oracles]
  · by_cases hq : q.1 ∉ insts ∨ q.1 ∈ List.map (fun x => x.1) h
    · refine ⟨Unit, pure (), fun _ => ((none, h), σ), ?_, ?_, fun _ => hI⟩
      · simp only [simImpl, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl,
          WotsGame.simSignOracle, StateT.run_bind, StateT.run_get, pure_bind, if_pos hq,
          StateT.run_pure, simulateQ_pure, map_pure]
        exact EvalDistEq.rfl
      · simp only [WotsGame.oracles, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl,
          WotsGame.signOracle, StateT.run_bind, StateT.run_get, pure_bind, if_pos hq,
          StateT.run_pure, map_pure]
        exact EvalDistEq.rfl
    · have hq' := hq
      rw [not_or, not_not] at hq'
      obtain ⟨fin1, h1, h2⟩ := hsign h σ q.1 q.2 hI hq'.1 hq'.2
      choose fin2 h2 h3 using h2
      refine ⟨_, ($ᵗ (Vector prims.Y vp.params.len) : ProbComp _), fun ss =>
        ((some (WotsGame.hybSig k pk q.1 q.2 ss,
            wotsPkFromSigTops prims (WotsGame.hybSig k pk q.1 q.2 ss) q.2 pk q.1),
          h ++ [(q.1, q.2, WotsGame.hybSig k pk q.1 q.2 ss,
            wotsPkFromSigTops prims (WotsGame.hybSig k pk q.1 q.2 ss) q.2 pk q.1)]), fin2 ss),
        ?_, ?_, fun ss => h3 ss⟩
      · simp only [simImpl, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl,
          WotsGame.simSignOracle, bind_pure_comp, StateT.run_bind, StateT.run_get, pure_bind,
          if_neg hq, StateT.run_monadLift, monadLift_self, bind_assoc, StateT.run_map,
          StateT.run_set, map_pure, simulateQ_bind, simulateQ_pure, StateT.run_pure,
          simulateQ_map, bind_map_left, Functor.map_map]
        refine (h1.bind_left _).trans ?_
        rw [bind_map_left]
        refine (EvalDistEq.bind_right _ (fun ss => (h2 ss).map _)).trans ?_
        simp only [map_pure, bind_pure_comp]
        exact EvalDistEq.rfl
      · simp only [WotsGame.oracles, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl,
          WotsGame.signOracle, StateT.run_bind, StateT.run_get, pure_bind, if_neg hq,
          StateT.run_pure, map_pure, StateT.run_monadLift, monadLift_self, bind_assoc,
          StateT.run_set, bind_pure_comp, bind_map_left, StateT.run_map, Functor.map_map]
        exact EvalDistEq.rfl
  · by_cases hq : WotsGame.reservedKey insts q.1 = true
    · refine ⟨Unit, pure (), fun _ => ((none, h), σ), ?_, ?_, fun _ => hI⟩
      · simp [simImpl, WotsGame.simCollOracle, hq]
      · simp [WotsGame.oracles, WotsGame.collOracle, hq]
    · obtain ⟨σ', h1, h2⟩ := hcoll h σ q.1 q.2 hI (by simpa using hq)
      refine ⟨Unit, pure (), fun _ => ((some (prims.Thash pk q.1 q.2), h), σ'), ?_, ?_,
        fun _ => h2⟩
      · simp only [simImpl, QueryImpl.add_apply_inr, WotsGame.simCollOracle, if_neg hq,
          StateT.run_monadLift, monadLift_self, simulateQ_bind, simulateQ_map, simulateQ_pure,
          StateT.run_bind, StateT.run_map, StateT.run_pure, bind_pure_comp, map_pure,
          Functor.map_map]
        refine (h1.map _).trans ?_
        simp
      · simp [WotsGame.oracles, WotsGame.collOracle, hq]

end Sim

/-! ## Chain-step tweaks, counts and the shape of the last hybrid's signature -/

section Keys

/-- Tweak of step `t` of chain `i` of the instance with base address `a`. -/
def stepKey (prims : Primitives vp.params) (a : Adrs) (i t : ℕ) : prims.AdrsKey :=
  prims.adrsToKey ((wotsChainAdrs a i).setHashAddress t)

theorem stepKey_inj (hS : Structural vp prims) {a a' : Adrs} (ha : a ∈ wotsInsts vp)
    (ha' : a' ∈ wotsInsts vp) {i i' t t' : ℕ} (hi : i < vp.params.len)
    (hi' : i' < vp.params.len) (ht : t < vp.params.w - 1) (ht' : t' < vp.params.w - 1)
    (h : stepKey prims a i t = stepKey prims a' i' t') : a = a' ∧ i = i' ∧ t = t' := by
  simp only [wotsInsts, List.mem_map] at ha ha'
  obtain ⟨pos, -, rfl⟩ := ha
  obtain ⟨pos', -, rfl⟩ := ha'
  have h1 : wotsStepAdrs (pos, ⟨i, hi⟩) ⟨t, ht⟩ = wotsStepAdrs (pos', ⟨i', hi'⟩) ⟨t', ht'⟩ :=
    hS.keyInj (addressFacts_wotsStepAdrs hS.bounds _ _)
      (addressFacts_wotsStepAdrs hS.bounds _ _) h
  have h2 := wotsStepAdrs_injective vp (a₁ := ((pos, ⟨i, hi⟩), ⟨t, ht⟩))
    (a₂ := ((pos', ⟨i', hi'⟩), ⟨t', ht'⟩)) h1
  simp only [Prod.mk.injEq, Fin.mk.injEq] at h2
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h2
  exact ⟨rfl, rfl, rfl⟩

theorem reservedKey_stepKey {insts : List Adrs} {a : Adrs} (ha : a ∈ insts) {i t : ℕ}
    (hi : i < vp.params.len) (ht : t < vp.params.w - 1) :
    WotsGame.reservedKey insts (stepKey prims a i t) = true := by
  simp only [WotsGame.reservedKey, List.any_eq_true, List.mem_range, decide_eq_true_eq]
  exact ⟨a, ha, i, hi, t, ht, rfl⟩

theorem preCount_succ (m : prims.Y) (k : ℕ) :
    preCount m (k + 1) = preCount m k + if chainStepsCore prims.core m k ≠ 0 then 1 else 0 := by
  simp only [preCount, List.range_succ, List.filter_append, List.length_append]
  by_cases h : chainStepsCore prims.core m k = 0 <;> simp [h]

theorem preCount_le (m : prims.Y) (k : ℕ) : preCount m k ≤ k := by
  unfold preCount
  exact (List.length_filter_le _ _).trans (by simp)

theorem tcrCount_succ (m : prims.Y) (k : ℕ) :
    tcrCount (vp := vp) m (k + 1) =
      tcrCount (vp := vp) m k + (vp.params.w - 1 - chainStepsCore prims.core m k) := by
  simp [tcrCount, List.range_succ]

theorem tcrCount_le (m : prims.Y) (k : ℕ) :
    tcrCount (vp := vp) m k ≤ k * (vp.params.w - 1) := by
  induction k with
  | zero => simp [tcrCount]
  | succ k ih =>
    rw [tcrCount_succ, Nat.succ_mul]
    exact Nat.add_le_add ih (Nat.sub_le _ _)

/-- Value revealed by the last hybrid for a chain with start value `u`. -/
def sigVal (pk : prims.PkSeed) (a : Adrs) (m : prims.Y) (i : ℕ) (u : prims.Y) : prims.Y :=
  if chainStepsCore prims.core m i = 0 then u
  else prims.F pk ((wotsChainAdrs a i).setHashAddress (chainStepsCore prims.core m i - 1)) u

theorem hybSig_last (pk : prims.PkSeed) (a : Adrs) (m : prims.Y)
    (ss : Vector prims.Y vp.params.len) :
    WotsGame.hybSig (vp.params.w - 2) pk a m ss =
      Vector.ofFn fun i : Fin vp.params.len => sigVal pk a m i.val ss[i] := by
  unfold WotsGame.hybSig
  congr 1
  funext i
  have hb := chainStepsCore_le prims.core m i.val
  by_cases h0 : chainStepsCore prims.core m i.val = 0
  · simp [sigVal, h0]
  · have h1 : min (vp.params.w - 2) (chainStepsCore prims.core m i.val - 1) =
        chainStepsCore prims.core m i.val - 1 := by omega
    have h2 : chainStepsCore prims.core m i.val - (chainStepsCore prims.core m i.val - 1) = 1 := by
      omega
    simp only [sigVal, h0, if_false, h1, h2]
    rw [show (1 : ℕ) = 0 + 1 from rfl, chain_succ, chain_zero, Nat.add_zero]
    rfl

end Keys

/-! ## The SM-PRE reduction: invariant and per-query analysis -/

section Pre
variable (pkSeedDist : ProbComp prims.PkSeed)

/-- The two game oracles of SM-PRE (challenge and collection) at seed `pk`. -/
noncomputable abbrev preO₂ (pk : prims.PkSeed) :
    QueryImpl (SM_DT_PRE_challengeSpec prims.AdrsKey prims.Y +
      collectionSpec (wotsPreProblem vp prims pkSeedDist).thColl)
      (StateT (SM_DT_PRE_State prims.AdrsKey prims.Y) ProbComp) :=
  SM_DT_PRE_challengeOracle (wotsPreProblem vp prims pkSeedDist) pk +
    collectionOracle (Q := prims.AdrsKey × prims.Y) Prod.fst
      (wotsPreProblem vp prims pkSeedDist).thColl pk

theorem preColl_run (pk : prims.PkSeed) (key : prims.AdrsKey) (xs : List prims.Y)
    (qs : List (prims.AdrsKey × prims.Y)) (tws : List prims.AdrsKey)
    (h : ¬ TweakReserved Prod.fst qs key) :
    (simulateQ (outer (preO₂ pkSeedDist pk)) (preColl pkSeedDist key xs)).run (qs, tws) =
      pure (prims.Thash pk key xs, (qs, tws ++ [key])) := by
  simp [preColl, outer, preO₂, collectionOracle, h]
  rfl

theorem preChal_run (pk : prims.PkSeed) (key : prims.AdrsKey)
    (qs : List (prims.AdrsKey × prims.Y)) (tws : List prims.AdrsKey)
    (hlen : qs.length < wotsChainTargets vp) (hfresh : TweakFresh Prod.fst qs tws key) :
    (simulateQ (outer (preO₂ pkSeedDist pk)) (preChal pkSeedDist key)).run (qs, tws) =
      (fun u => (prims.Thash pk key [u], (qs ++ [(key, u)], tws))) <$>
        ($ᵗ prims.Y : ProbComp prims.Y) := by
  have h1 := SM_DT_PRE_challengeOracle_run_of_fresh
    (prob := wotsPreProblem vp prims pkSeedDist) (pk := pk) (t := key) (qsChal := qs)
    (twsColl := tws) hlen hfresh
  simp [preChal, outer, preO₂, h1]
  rfl

theorem pre_chain_run (pk : prims.PkSeed) (ad : Adrs) (x : prims.Y) (i s : ℕ)
    (qs : List (prims.AdrsKey × prims.Y)) (tws : List prims.AdrsKey)
    (hfresh : ∀ j < s, ¬ TweakReserved Prod.fst qs (prims.adrsToKey (ad.setHashAddress (i + j)))) :
    (simulateQ (outer (preO₂ pkSeedDist pk)) (chainWith (preChainHash pkSeedDist) ad x i s)).run
        (qs, tws) =ᵈ
      (pure (chain prims pk ad x i s,
        (qs, tws ++ (List.range s).map fun j => prims.adrsToKey (ad.setHashAddress (i + j)))) :
        ProbComp _) := by
  induction s with
  | zero => simp [chainWith_zero]
  | succ s ih =>
    rw [chainWith_succ, simulateQ_bind, StateT.run_bind]
    refine ((ih fun j hj => hfresh j (Nat.lt_succ_of_lt hj)).bind_left _).trans ?_
    rw [pure_bind]
    simp only [preChainHash]
    rw [preColl_run pkSeedDist pk _ _ qs _ (hfresh s (Nat.lt_succ_self s)), chain_succ,
      List.range_succ, List.map_append, ← List.append_assoc]
    exact EvalDistEq.rfl

/-- Invariant relating the mirrored signing history to the SM-PRE game state. -/
structure PreInv (pk : prims.PkSeed) (hist : List (WotsGame.Entry prims))
    (σ : SM_DT_PRE_State prims.AdrsKey prims.Y) : Prop where
  nodup : (hist.map (·.1)).Nodup
  mem : ∀ e ∈ hist, e.1 ∈ wotsInsts vp
  tops : ∀ e ∈ hist, e.2.2.2 = wotsPkFromSigTops prims e.2.2.1 e.2.1 pk e.1
  len : σ.1.length = (hist.map fun e => preCount e.2.1 vp.params.len).sum
  tgt : ∀ j e, hist[j]? = some e → ∀ i : Fin vp.params.len,
    chainStepsCore prims.core e.2.1 i.val ≠ 0 →
    ∃ u, σ.1[preTargetIndex hist j i.val]? =
        some (stepKey prims e.1 i.val (chainStepsCore prims.core e.2.1 i.val - 1), u) ∧
      prims.F pk ((wotsChainAdrs e.1 i.val).setHashAddress
        (chainStepsCore prims.core e.2.1 i.val - 1)) u = e.2.2.1[i.val]
  qs : ∀ q ∈ σ.1, ∃ e ∈ hist, ∃ i, i < vp.params.len ∧ chainStepsCore prims.core e.2.1 i ≠ 0 ∧
    q.1 = stepKey prims e.1 i (chainStepsCore prims.core e.2.1 i - 1)
  tws : ∀ k ∈ σ.2, WotsGame.reservedKey (wotsInsts vp) k = false ∨
    ∃ e ∈ hist, ∃ i t, i < vp.params.len ∧ chainStepsCore prims.core e.2.1 i ≤ t ∧
      t < vp.params.w - 1 ∧ k = stepKey prims e.1 i t

theorem hist_length_lt {hist : List (WotsGame.Entry prims)} (hnodup : (hist.map (·.1)).Nodup)
    (hmem : ∀ e ∈ hist, e.1 ∈ wotsInsts vp) {a : Adrs} (ha : a ∈ wotsInsts vp)
    (hnew : a ∉ hist.map (·.1)) : hist.length + 1 ≤ wotsInstanceCount vp.params := by
  have h1 : (a :: hist.map (·.1)).Nodup := List.nodup_cons.mpr ⟨hnew, hnodup⟩
  have h2 : a :: hist.map (·.1) ⊆ wotsInsts vp := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ha
    · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
      exact hmem e he
  have h3 := (List.subperm_of_subset h1 h2).length_le
  simpa [wotsInsts] using h3

theorem sum_preCount_le (hist : List (WotsGame.Entry prims)) :
    (hist.map fun e => preCount e.2.1 vp.params.len).sum ≤ hist.length * vp.params.len := by
  induction hist with
  | nil => simp
  | cons e hist ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
    have := preCount_le e.2.1 vp.params.len
    omega

theorem pre_hcoll (pk : prims.PkSeed) (hist : List (WotsGame.Entry prims))
    (σ : SM_DT_PRE_State prims.AdrsKey prims.Y) (key : prims.AdrsKey) (xs : List prims.Y)
    (hI : PreInv pk hist σ) (hres : WotsGame.reservedKey (wotsInsts vp) key = false) :
    ∃ σ', (simulateQ (outer (preO₂ pkSeedDist pk)) (preColl pkSeedDist key xs)).run σ =ᵈ
      (pure (prims.Thash pk key xs, σ') : ProbComp _) ∧ PreInv pk hist σ' := by
  obtain ⟨qs, tws⟩ := σ
  have hnot : ¬ TweakReserved Prod.fst qs key := by
    rintro ⟨q, hq, rfl⟩
    obtain ⟨e, he, i, hi, hb, hk⟩ := hI.qs q hq
    have hbw := chainStepsCore_le prims.core e.2.1 i
    rw [hk, reservedKey_stepKey (hI.mem e he) hi (by omega)] at hres
    exact Bool.noConfusion hres
  refine ⟨(qs, tws ++ [key]), ?_, ⟨hI.nodup, hI.mem, hI.tops, hI.len, hI.tgt, hI.qs, ?_⟩⟩
  · rw [preColl_run pkSeedDist pk key xs qs tws hnot]
  · intro k hk
    rcases List.mem_append.mp hk with hk | hk
    · exact hI.tws k hk
    · left
      rw [List.mem_singleton.mp hk]
      exact hres

theorem pre_hsign (hS : Structural vp prims) (pk : prims.PkSeed)
    (hist : List (WotsGame.Entry prims)) (σ : SM_DT_PRE_State prims.AdrsKey prims.Y)
    (a : Adrs) (m : prims.Y) (hI : PreInv pk hist σ) (ha : a ∈ wotsInsts vp)
    (hnew : a ∉ hist.map (·.1)) :
    ∃ fin1 : Vector prims.Y vp.params.len → SM_DT_PRE_State prims.AdrsKey prims.Y,
      (simulateQ (outer (preO₂ pkSeedDist pk)) (Vector.ofFnM fun i : Fin vp.params.len =>
          preStart pkSeedDist (wotsChainAdrs a i.val) (chainStepsCore prims.core m i.val))).run σ =ᵈ
        (fun ss => (WotsGame.hybSig (vp.params.w - 2) pk a m ss, fin1 ss)) <$>
          ($ᵗ (Vector prims.Y vp.params.len) : ProbComp _) ∧
      ∀ ss, ∃ fin2,
        (simulateQ (outer (preO₂ pkSeedDist pk)) (wotsPkFromSigTopsWith prims.core
            (preChainHash pkSeedDist) (WotsGame.hybSig (vp.params.w - 2) pk a m ss) m a)).run
            (fin1 ss) =ᵈ
          (pure (wotsPkFromSigTops prims (WotsGame.hybSig (vp.params.w - 2) pk a m ss) m pk a,
            fin2) : ProbComp _) ∧
        PreInv pk (hist ++ [(a, m, WotsGame.hybSig (vp.params.w - 2) pk a m ss,
          wotsPkFromSigTops prims (WotsGame.hybSig (vp.params.w - 2) pk a m ss) m pk a)]) fin2 := by
  obtain ⟨qs, tws⟩ := σ
  have hbw : ∀ i, chainStepsCore prims.core m i ≤ vp.params.w - 1 :=
    fun i => chainStepsCore_le prims.core m i
  have hcount := hist_length_lt hI.nodup hI.mem ha hnew
  have hqslen : qs.length ≤ hist.length * vp.params.len := hI.len ▸ sum_preCount_le hist
  -- distinctness of the new instance's tweaks from the old state
  have hold_qs : ∀ q ∈ qs, ∀ i t, i < vp.params.len → t < vp.params.w - 1 →
      q.1 ≠ stepKey prims a i t := by
    intro q hq i t hi ht hk
    obtain ⟨e, he, i', hi', hb', hk'⟩ := hI.qs q hq
    have hbw' := chainStepsCore_le prims.core e.2.1 i'
    have := (stepKey_inj hS (hI.mem e he) ha hi' hi (by omega) ht (hk'.symm.trans hk)).1
    exact hnew (this ▸ List.mem_map_of_mem (f := (·.1)) he)
  have hold_tws : ∀ i t, i < vp.params.len → t < vp.params.w - 1 →
      stepKey prims a i t ∉ tws := by
    intro i t hi ht hk
    rcases hI.tws _ hk with h | ⟨e, he, i', t', hi', -, ht', hk'⟩
    · rw [reservedKey_stepKey ha hi ht] at h
      exact Bool.noConfusion h
    · have := (stepKey_inj hS ha (hI.mem e he) hi hi' ht ht' hk').1
      exact hnew (this ▸ List.mem_map_of_mem (f := (·.1)) he)
  -- phase 1: the revealed values
  let J : (k : ℕ) → Vector prims.Y k → SM_DT_PRE_State prims.AdrsKey prims.Y → Prop :=
    fun k us σ' => σ'.2 = tws ∧ ∃ L : List (prims.AdrsKey × prims.Y), σ'.1 = qs ++ L ∧
      L.length = preCount m k ∧
      (∀ q ∈ L, ∃ i, i < k ∧ chainStepsCore prims.core m i ≠ 0 ∧
        q.1 = stepKey prims a i (chainStepsCore prims.core m i - 1)) ∧
      (∀ i (hi : i < k), chainStepsCore prims.core m i ≠ 0 →
        L[preCount m i]? = some (stepKey prims a i (chainStepsCore prims.core m i - 1), us[i]))
  obtain ⟨fin1, h1, hJ⟩ := ofFnM_run_sample (outer (preO₂ pkSeedDist pk)) J
    (fun i : Fin vp.params.len =>
      preStart pkSeedDist (wotsChainAdrs a i.val) (chainStepsCore prims.core m i.val))
    (fun i u => sigVal pk a m i.val u)
    (fun i u σ' => if chainStepsCore prims.core m i.val = 0 then σ'
      else (σ'.1 ++ [(stepKey prims a i.val (chainStepsCore prims.core m i.val - 1), u)], σ'.2))
    (by
      rintro i us ⟨qs', tws'⟩ ⟨h2, L, hL, hlen, hmemL, hget⟩
      simp only at h2 hL
      subst tws' qs'
      by_cases hb : chainStepsCore prims.core m i.val = 0
      · constructor
        · simp only [preStart, hb, if_true]
          rw [outer_lift]
          simp only [sigVal, hb, if_true]
          exact EvalDistEq.rfl
        · intro u
          simp only [hb, if_true]
          refine ⟨rfl, L, rfl, ?_, ?_, ?_⟩
          · rw [preCount_succ, hlen]; simp [hb]
          · intro q hq
            obtain ⟨i', hi', r⟩ := hmemL q hq
            exact ⟨i', by omega, r⟩
          · intro i' hi' hb'
            have hlt : i' < i.val := by
              rcases Nat.lt_succ_iff_lt_or_eq.mp hi' with h | h
              · exact h
              · subst h; exact absurd hb hb'
            rw [hget i' hlt hb']
            simp [hlt]
      · have hbi : chainStepsCore prims.core m i.val - 1 < vp.params.w - 1 := by
          have := hbw i.val; omega
        have hfresh : TweakFresh Prod.fst (qs ++ L) tws
            (stepKey prims a i.val (chainStepsCore prims.core m i.val - 1)) := by
          refine ⟨?_, hold_tws _ _ i.isLt hbi⟩
          rintro ⟨q, hq, hk⟩
          rcases List.mem_append.mp hq with hq | hq
          · exact hold_qs q hq _ _ i.isLt hbi hk
          · obtain ⟨i', hi', hb', hk'⟩ := hmemL q hq
            have hbi' : chainStepsCore prims.core m i' - 1 < vp.params.w - 1 := by
              have := hbw i'; omega
            have := (stepKey_inj hS ha ha (by omega) i.isLt hbi' hbi (hk'.symm.trans hk)).2.1
            omega
        have hlen' : (qs ++ L).length < wotsChainTargets vp := by
          have h3 := preCount_le m i.val
          have h4 := Nat.mul_le_mul_right vp.params.len hcount
          rw [Nat.succ_mul] at h4
          have h5 : wotsChainTargets vp = wotsInstanceCount vp.params * vp.params.len := rfl
          have h6 := i.isLt
          rw [List.length_append, hlen, h5]
          omega
        constructor
        · simp only [preStart, hb, ite_false]
          rw [show prims.adrsToKey ((wotsChainAdrs a i.val).setHashAddress
              (chainStepsCore prims.core m i.val - 1)) =
              stepKey prims a i.val (chainStepsCore prims.core m i.val - 1) from rfl,
            preChal_run pkSeedDist pk _ _ _ hlen' hfresh]
          simp only [sigVal, hb, ite_false]
          exact EvalDistEq.rfl
        · intro u
          simp only [hb, ite_false]
          refine ⟨rfl, L ++ [(stepKey prims a i.val (chainStepsCore prims.core m i.val - 1), u)],
            by simp, ?_, ?_, ?_⟩
          · rw [preCount_succ, List.length_append, hlen]; simp [hb]
          · intro q hq
            rcases List.mem_append.mp hq with hq | hq
            · obtain ⟨i', hi', r⟩ := hmemL q hq
              exact ⟨i', by omega, r⟩
            · rw [List.mem_singleton.mp hq]
              exact ⟨i.val, Nat.lt_succ_self _, hb, rfl⟩
          · intro i' hi' hb'
            rcases Nat.lt_succ_iff_lt_or_eq.mp hi' with hlt | heq
            · have h7 := hget i' hlt hb'
              have h8 : preCount m i' < L.length := (List.getElem?_eq_some_iff.mp h7).1
              rw [List.getElem?_append_left h8, h7]
              simp [hlt]
            · subst heq
              rw [← hlen, List.getElem?_append_right (le_refl _)]
              simp)
    (qs, tws) ⟨rfl, [], by simp, by simp [preCount], by simp, fun i hi => absurd hi (by omega)⟩
  refine ⟨fin1, ?_, ?_⟩
  · have e : (fun us : Vector prims.Y vp.params.len =>
          (Vector.ofFn fun i : Fin vp.params.len => sigVal pk a m i.val us[i], fin1 us)) =
        fun ss => (WotsGame.hybSig (vp.params.w - 2) pk a m ss, fin1 ss) :=
      funext fun ss => by rw [hybSig_last]
    rw [← e]
    exact h1
  · intro ss
    obtain ⟨h2, L, hL, hlen, hmemL, hget⟩ := hJ ss
    generalize hfin : fin1 ss = σ1 at h2 hL
    obtain ⟨qs1, tws1⟩ := σ1
    simp only at h2 hL
    subst tws1 qs1
    have hsig : ∀ i : Fin vp.params.len,
        (WotsGame.hybSig (vp.params.w - 2) pk a m ss)[i.val] = sigVal pk a m i.val ss[i] := by
      intro i
      rw [hybSig_last]
      simp
    generalize WotsGame.hybSig (vp.params.w - 2) pk a m ss = sig at hsig ⊢
    let J2 : ℕ → SM_DT_PRE_State prims.AdrsKey prims.Y → Prop :=
      fun k σ'' => σ''.1 = qs ++ L ∧ ∃ T : List prims.AdrsKey, σ''.2 = tws ++ T ∧
        ∀ key ∈ T, ∃ i t, i < k ∧ chainStepsCore prims.core m i ≤ t ∧ t < vp.params.w - 1 ∧
          key = stepKey prims a i t
    obtain ⟨fin2, h3, hJ2⟩ := ofFnM_run_det (outer (preO₂ pkSeedDist pk)) J2
      (fun i : Fin vp.params.len => chainWith (preChainHash pkSeedDist) (wotsChainAdrs a i.val)
        sig[i.val] (chainStepsCore prims.core m i.val)
        (vp.params.w - 1 - chainStepsCore prims.core m i.val))
      (fun i => chain prims pk (wotsChainAdrs a i.val) sig[i.val]
        (chainStepsCore prims.core m i.val) (vp.params.w - 1 - chainStepsCore prims.core m i.val))
      (fun i σ'' => (σ''.1, σ''.2 ++
        (List.range (vp.params.w - 1 - chainStepsCore prims.core m i.val)).map fun j =>
          prims.adrsToKey ((wotsChainAdrs a i.val).setHashAddress
            (chainStepsCore prims.core m i.val + j))))
      (by
        rintro i ⟨qs'', tws''⟩ ⟨hq, T, hT, hTm⟩
        simp only at hq hT
        subst qs'' tws''
        refine ⟨pre_chain_run pkSeedDist pk _ _ _ _ _ _ ?_, rfl, _, (List.append_assoc _ _ _), ?_⟩
        · rintro j hj ⟨q, hq, hk⟩
          have hjw : chainStepsCore prims.core m i.val + j < vp.params.w - 1 := by omega
          rcases List.mem_append.mp hq with hq | hq
          · exact hold_qs q hq _ _ i.isLt hjw hk
          · obtain ⟨i', hi', hb', hk'⟩ := hmemL q hq
            have hbi' : chainStepsCore prims.core m i' - 1 < vp.params.w - 1 := by
              have := hbw i'; omega
            have h9 := stepKey_inj hS ha ha hi' i.isLt hbi' hjw (hk'.symm.trans hk)
            obtain ⟨-, h10, h11⟩ := h9
            subst h10
            omega
        · intro key hkey
          rcases List.mem_append.mp hkey with hkey | hkey
          · obtain ⟨i', t, hi', r⟩ := hTm key hkey
            exact ⟨i', t, by omega, r⟩
          · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hkey
            have hj' := List.mem_range.mp hj
            exact ⟨i.val, _, Nat.lt_succ_self _, Nat.le_add_right _ _, by omega, rfl⟩)
      (qs ++ L, tws) ⟨rfl, [], by simp, by simp⟩
    obtain ⟨qs2, tws2⟩ := fin2
    obtain ⟨hq2, T, hT, hTm⟩ := hJ2
    simp only at hq2 hT
    subst qs2 tws2
    refine ⟨(qs ++ L, tws ++ T), ?_, ?_⟩
    · rw [wotsPkFromSigTops_eq_ofFn]
      exact h3
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [List.map_append, List.nodup_append]
        exact ⟨hI.nodup, by simp, by
          intro x hx y hy
          rw [List.map_singleton, List.mem_singleton] at hy
          subst hy
          exact fun h => hnew (h ▸ hx)⟩
      · intro e he
        rcases List.mem_append.mp he with he | he
        · exact hI.mem e he
        · rw [List.mem_singleton.mp he]; exact ha
      · intro e he
        rcases List.mem_append.mp he with he | he
        · exact hI.tops e he
        · rw [List.mem_singleton.mp he]
      · simp [hlen, hI.len]
      · intro j e hj i hb
        rcases Nat.lt_or_ge j hist.length with hjl | hjl
        · have hj' : hist[j]? = some e := by rwa [List.getElem?_append_left hjl] at hj
          have hidx : preTargetIndex (hist ++ [(a, m, sig,
              wotsPkFromSigTops prims sig m pk a)]) j i.val = preTargetIndex hist j i.val := by
            simp only [preTargetIndex]
            rw [List.getElem?_append_left hjl, List.take_append_of_le_length hjl.le]
          obtain ⟨u, hu, hF⟩ := hI.tgt j e hj' i hb
          refine ⟨u, ?_, hF⟩
          rw [hidx]
          have h8 := (List.getElem?_eq_some_iff.mp hu).1
          show (qs ++ L)[_]? = _
          rw [List.getElem?_append_left h8]
          exact hu
        · have hjeq : j = hist.length := by
            have := (List.getElem?_eq_some_iff.mp hj).1
            simp at this
            omega
          subst hjeq
          have he : e = (a, m, sig, wotsPkFromSigTops prims sig m pk a) := by
            simpa using hj.symm
          subst he
          have hidx : preTargetIndex (hist ++ [(a, m, sig,
              wotsPkFromSigTops prims sig m pk a)]) hist.length i.val =
              qs.length + preCount m i.val := by
            simp [preTargetIndex, hI.len]
          refine ⟨ss[i], ?_, ?_⟩
          · rw [hidx]
            show (qs ++ L)[_]? = _
            rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
            exact hget i.val i.isLt hb
          · show _ = sig[i.val]
            rw [hsig i]
            simp only [sigVal]
            simp only [hb, ite_false]
      · intro q hq
        rcases List.mem_append.mp hq with hq | hq
        · obtain ⟨e, he, r⟩ := hI.qs q hq
          exact ⟨e, List.mem_append_left _ he, r⟩
        · obtain ⟨i', hi', r⟩ := hmemL q hq
          exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), i', hi', r⟩
      · intro k hk
        rcases List.mem_append.mp hk with hk | hk
        · rcases hI.tws k hk with h | ⟨e, he, r⟩
          · exact Or.inl h
          · exact Or.inr ⟨e, List.mem_append_left _ he, r⟩
        · obtain ⟨i', t, hi', r⟩ := hTm k hk
          exact Or.inr ⟨_, List.mem_append_right _ (List.mem_singleton_self _), i', t, hi', r⟩

end Pre

/-! ## The SM-TCR reduction: invariant and per-query analysis -/

section Tcr
variable (pkSeedDist : ProbComp prims.PkSeed)

/-- The two game oracles of SM-TCR (challenge and collection) at seed `pk`. -/
abbrev tcrO₂ (pk : prims.PkSeed) :
    QueryImpl (SM_DT_TCR_challengeSpec prims.AdrsKey prims.Y prims.Y +
      collectionSpec (wotsTcrProblem vp prims pkSeedDist).thColl)
      (StateT (SM_DT_TCR_State prims.AdrsKey prims.Y) ProbComp) :=
  SM_DT_TCR_challengeOracle (wotsTcrProblem vp prims pkSeedDist) pk +
    collectionOracle (Q := prims.AdrsKey × prims.Y) Prod.fst
      (wotsTcrProblem vp prims pkSeedDist).thColl pk

theorem wtcrColl_run (pk : prims.PkSeed) (key : prims.AdrsKey) (xs : List prims.Y)
    (qs : List (prims.AdrsKey × prims.Y)) (tws : List prims.AdrsKey)
    (h : ¬ TweakReserved Prod.fst qs key) :
    (simulateQ (outer (tcrO₂ pkSeedDist pk)) (wtcrColl pkSeedDist key xs)).run (qs, tws) =
      pure (prims.Thash pk key xs, (qs, tws ++ [key])) := by
  simp [wtcrColl, outer, tcrO₂, collectionOracle, h]
  rfl

theorem wtcrChal_run (pk : prims.PkSeed) (key : prims.AdrsKey) (x : prims.Y)
    (qs : List (prims.AdrsKey × prims.Y)) (tws : List prims.AdrsKey)
    (hlen : qs.length < wotsStepTargets vp) (hfresh : TweakFresh Prod.fst qs tws key) :
    (simulateQ (outer (tcrO₂ pkSeedDist pk)) (wtcrChal pkSeedDist key x)).run (qs, tws) =
      pure (prims.Thash pk key [x], (qs ++ [(key, x)], tws)) := by
  have h1 := SM_DT_TCR_challengeOracle_run_of_fresh
    (prob := wotsTcrProblem vp prims pkSeedDist) (pk := pk) (t := key) (m := x) (qsChal := qs)
    (twsColl := tws) hlen hfresh
  simp [wtcrChal, outer, tcrO₂, h1]
  rfl

theorem tcr_chain_run (pk : prims.PkSeed) (ad : Adrs) (x : prims.Y) (i s : ℕ)
    (qs : List (prims.AdrsKey × prims.Y)) (tws : List prims.AdrsKey)
    (h : ∀ j < s, qs.length + j < wotsStepTargets vp ∧
      TweakFresh Prod.fst (qs ++ (List.range j).map fun j' =>
        (prims.adrsToKey (ad.setHashAddress (i + j')), chain prims pk ad x i j')) tws
        (prims.adrsToKey (ad.setHashAddress (i + j)))) :
    (simulateQ (outer (tcrO₂ pkSeedDist pk)) (chainWith (tcrChainHash pkSeedDist) ad x i s)).run
        (qs, tws) =ᵈ
      (pure (chain prims pk ad x i s,
        (qs ++ (List.range s).map fun j =>
          (prims.adrsToKey (ad.setHashAddress (i + j)), chain prims pk ad x i j), tws)) :
        ProbComp _) := by
  induction s with
  | zero => simp [chainWith_zero]
  | succ s ih =>
    rw [chainWith_succ, simulateQ_bind, StateT.run_bind]
    refine ((ih fun j hj => h j (Nat.lt_succ_of_lt hj)).bind_left _).trans ?_
    rw [pure_bind]
    simp only [tcrChainHash]
    rw [wtcrChal_run pkSeedDist pk _ _ _ _ (by simpa using (h s (Nat.lt_succ_self s)).1)
      (h s (Nat.lt_succ_self s)).2, chain_succ, List.range_succ, List.map_append,
      ← List.append_assoc]
    exact EvalDistEq.rfl

/-- Invariant relating the mirrored signing history to the SM-TCR game state. -/
structure TcrInv (pk : prims.PkSeed) (hist : List (WotsGame.Entry prims))
    (σ : SM_DT_TCR_State prims.AdrsKey prims.Y) : Prop where
  nodup : (hist.map (·.1)).Nodup
  mem : ∀ e ∈ hist, e.1 ∈ wotsInsts vp
  tops : ∀ e ∈ hist, e.2.2.2 = wotsPkFromSigTops prims e.2.2.1 e.2.1 pk e.1
  len : σ.1.length = (hist.map fun e => tcrCount (vp := vp) e.2.1 vp.params.len).sum
  tgt : ∀ j e, hist[j]? = some e → ∀ (i : Fin vp.params.len) (t : ℕ),
    chainStepsCore prims.core e.2.1 i.val ≤ t → t < vp.params.w - 1 →
    σ.1[tcrTargetIndex hist j i.val t]? =
      some (stepKey prims e.1 i.val t,
        chain prims pk (wotsChainAdrs e.1 i.val) e.2.2.1[i.val]
          (chainStepsCore prims.core e.2.1 i.val) (t - chainStepsCore prims.core e.2.1 i.val))
  qs : ∀ q ∈ σ.1, ∃ e ∈ hist, ∃ i t, i < vp.params.len ∧ chainStepsCore prims.core e.2.1 i ≤ t ∧
    t < vp.params.w - 1 ∧ q.1 = stepKey prims e.1 i t
  tws : ∀ k ∈ σ.2, WotsGame.reservedKey (wotsInsts vp) k = false ∨
    ∃ e ∈ hist, ∃ i, i < vp.params.len ∧ chainStepsCore prims.core e.2.1 i ≠ 0 ∧
      k = stepKey prims e.1 i (chainStepsCore prims.core e.2.1 i - 1)

theorem sum_tcrCount_le (hist : List (WotsGame.Entry prims)) :
    (hist.map fun e => tcrCount (vp := vp) e.2.1 vp.params.len).sum ≤
      hist.length * (vp.params.len * (vp.params.w - 1)) := by
  induction hist with
  | nil => simp
  | cons e hist ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
    have := tcrCount_le (vp := vp) e.2.1 vp.params.len
    omega

theorem tcr_hcoll (pk : prims.PkSeed) (hist : List (WotsGame.Entry prims))
    (σ : SM_DT_TCR_State prims.AdrsKey prims.Y) (key : prims.AdrsKey) (xs : List prims.Y)
    (hI : TcrInv pk hist σ) (hres : WotsGame.reservedKey (wotsInsts vp) key = false) :
    ∃ σ', (simulateQ (outer (tcrO₂ pkSeedDist pk)) (wtcrColl pkSeedDist key xs)).run σ =ᵈ
      (pure (prims.Thash pk key xs, σ') : ProbComp _) ∧ TcrInv pk hist σ' := by
  obtain ⟨qs, tws⟩ := σ
  have hnot : ¬ TweakReserved Prod.fst qs key := by
    rintro ⟨q, hq, rfl⟩
    obtain ⟨e, he, i, t, hi, hb, ht, hk⟩ := hI.qs q hq
    rw [hk, reservedKey_stepKey (hI.mem e he) hi ht] at hres
    exact Bool.noConfusion hres
  refine ⟨(qs, tws ++ [key]), ?_, ⟨hI.nodup, hI.mem, hI.tops, hI.len, hI.tgt, hI.qs, ?_⟩⟩
  · rw [wtcrColl_run pkSeedDist pk key xs qs tws hnot]
  · intro k hk
    rcases List.mem_append.mp hk with hk | hk
    · exact hI.tws k hk
    · left
      rw [List.mem_singleton.mp hk]
      exact hres

theorem tcr_hsign (hS : Structural vp prims) (pk : prims.PkSeed)
    (hist : List (WotsGame.Entry prims)) (σ : SM_DT_TCR_State prims.AdrsKey prims.Y)
    (a : Adrs) (m : prims.Y) (hI : TcrInv pk hist σ) (ha : a ∈ wotsInsts vp)
    (hnew : a ∉ hist.map (·.1)) :
    ∃ fin1 : Vector prims.Y vp.params.len → SM_DT_TCR_State prims.AdrsKey prims.Y,
      (simulateQ (outer (tcrO₂ pkSeedDist pk)) (Vector.ofFnM fun i : Fin vp.params.len =>
          tcrStart pkSeedDist (wotsChainAdrs a i.val) (chainStepsCore prims.core m i.val))).run σ =ᵈ
        (fun ss => (WotsGame.hybSig (vp.params.w - 2) pk a m ss, fin1 ss)) <$>
          ($ᵗ (Vector prims.Y vp.params.len) : ProbComp _) ∧
      ∀ ss, ∃ fin2,
        (simulateQ (outer (tcrO₂ pkSeedDist pk)) (wotsPkFromSigTopsWith prims.core
            (tcrChainHash pkSeedDist) (WotsGame.hybSig (vp.params.w - 2) pk a m ss) m a)).run
            (fin1 ss) =ᵈ
          (pure (wotsPkFromSigTops prims (WotsGame.hybSig (vp.params.w - 2) pk a m ss) m pk a,
            fin2) : ProbComp _) ∧
        TcrInv pk (hist ++ [(a, m, WotsGame.hybSig (vp.params.w - 2) pk a m ss,
          wotsPkFromSigTops prims (WotsGame.hybSig (vp.params.w - 2) pk a m ss) m pk a)]) fin2 := by
  obtain ⟨qs, tws⟩ := σ
  have hbw : ∀ i, chainStepsCore prims.core m i ≤ vp.params.w - 1 :=
    fun i => chainStepsCore_le prims.core m i
  have hcount := hist_length_lt hI.nodup hI.mem ha hnew
  have hqslen : qs.length ≤ hist.length * (vp.params.len * (vp.params.w - 1)) :=
    hI.len ▸ sum_tcrCount_le hist
  have hcap : (hist.length + 1) * (vp.params.len * (vp.params.w - 1)) ≤ wotsStepTargets vp := by
    have h5 : wotsStepTargets vp = wotsInstanceCount vp.params * vp.params.len * vp.params.w := rfl
    rw [h5, Nat.mul_assoc]
    exact Nat.mul_le_mul hcount (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
  rw [Nat.succ_mul] at hcap
  have hold_qs : ∀ q ∈ qs, ∀ i t, i < vp.params.len → t < vp.params.w - 1 →
      q.1 ≠ stepKey prims a i t := by
    intro q hq i t hi ht hk
    obtain ⟨e, he, i', t', hi', -, ht', hk'⟩ := hI.qs q hq
    have := (stepKey_inj hS (hI.mem e he) ha hi' hi ht' ht (hk'.symm.trans hk)).1
    exact hnew (this ▸ List.mem_map_of_mem (f := (·.1)) he)
  have hold_tws : ∀ i t, i < vp.params.len → t < vp.params.w - 1 →
      stepKey prims a i t ∉ tws := by
    intro i t hi ht hk
    rcases hI.tws _ hk with h | ⟨e, he, i', hi', hb', hk'⟩
    · rw [reservedKey_stepKey ha hi ht] at h
      exact Bool.noConfusion h
    · have hbw' := chainStepsCore_le prims.core e.2.1 i'
      have := (stepKey_inj hS ha (hI.mem e he) hi hi' ht (by omega) hk').1
      exact hnew (this ▸ List.mem_map_of_mem (f := (·.1)) he)
  -- phase 1: the revealed values
  let J : (k : ℕ) → Vector prims.Y k → SM_DT_TCR_State prims.AdrsKey prims.Y → Prop :=
    fun k _ σ' => σ'.1 = qs ∧ ∃ T : List prims.AdrsKey, σ'.2 = tws ++ T ∧
      ∀ key ∈ T, ∃ i, i < k ∧ chainStepsCore prims.core m i ≠ 0 ∧
        key = stepKey prims a i (chainStepsCore prims.core m i - 1)
  obtain ⟨fin1, h1, hJ⟩ := ofFnM_run_sample (outer (tcrO₂ pkSeedDist pk)) J
    (fun i : Fin vp.params.len =>
      tcrStart pkSeedDist (wotsChainAdrs a i.val) (chainStepsCore prims.core m i.val))
    (fun i u => sigVal pk a m i.val u)
    (fun i _ σ' => if chainStepsCore prims.core m i.val = 0 then σ'
      else (σ'.1, σ'.2 ++ [stepKey prims a i.val (chainStepsCore prims.core m i.val - 1)]))
    (by
      rintro i us ⟨qs', tws'⟩ ⟨h2, T, hT, hTm⟩
      simp only at h2 hT
      subst qs' tws'
      by_cases hb : chainStepsCore prims.core m i.val = 0
      · constructor
        · simp only [tcrStart, hb, if_true, simulateQ_bind, StateT.run_bind, simulateQ_pure,
            StateT.run_pure]
          rw [outer_lift, bind_map_left]
          simp only [sigVal, hb, if_true, bind_pure_comp]
          exact EvalDistEq.rfl
        · intro u
          simp only [hb, if_true]
          refine ⟨rfl, T, rfl, ?_⟩
          intro key hkey
          obtain ⟨i', hi', r⟩ := hTm key hkey
          exact ⟨i', by omega, r⟩
      · have hbi : chainStepsCore prims.core m i.val - 1 < vp.params.w - 1 := by
          have := hbw i.val; omega
        have hnot : ¬ TweakReserved Prod.fst qs (prims.adrsToKey
            ((wotsChainAdrs a i.val).setHashAddress (chainStepsCore prims.core m i.val - 1))) :=
          fun ⟨q, hq, hk⟩ => hold_qs q hq _ _ i.isLt hbi hk
        constructor
        · simp only [tcrStart, hb, ite_false, simulateQ_bind, StateT.run_bind]
          rw [outer_lift, bind_map_left]
          simp only [wtcrColl_run pkSeedDist pk _ _ _ _ hnot, sigVal, hb, ite_false,
            bind_pure_comp]
          exact EvalDistEq.rfl
        · intro u
          simp only [hb, ite_false]
          refine ⟨rfl, T ++ [stepKey prims a i.val (chainStepsCore prims.core m i.val - 1)],
            by simp, ?_⟩
          intro key hkey
          rcases List.mem_append.mp hkey with hkey | hkey
          · obtain ⟨i', hi', r⟩ := hTm key hkey
            exact ⟨i', by omega, r⟩
          · rw [List.mem_singleton.mp hkey]
            exact ⟨i.val, Nat.lt_succ_self _, hb, rfl⟩)
    (qs, tws) ⟨rfl, [], by simp, by simp⟩
  refine ⟨fin1, ?_, ?_⟩
  · have e : (fun us : Vector prims.Y vp.params.len =>
          (Vector.ofFn fun i : Fin vp.params.len => sigVal pk a m i.val us[i], fin1 us)) =
        fun ss => (WotsGame.hybSig (vp.params.w - 2) pk a m ss, fin1 ss) :=
      funext fun ss => by rw [hybSig_last]
    rw [← e]
    exact h1
  · intro ss
    obtain ⟨h2, T, hT, hTm⟩ := hJ ss
    generalize hfin : fin1 ss = σ1 at h2 hT
    obtain ⟨qs1, tws1⟩ := σ1
    simp only at h2 hT
    subst qs1 tws1
    generalize WotsGame.hybSig (vp.params.w - 2) pk a m ss = sig
    let J2 : ℕ → SM_DT_TCR_State prims.AdrsKey prims.Y → Prop :=
      fun k σ'' => σ''.2 = tws ++ T ∧ ∃ M : List (prims.AdrsKey × prims.Y), σ''.1 = qs ++ M ∧
        M.length = tcrCount (vp := vp) m k ∧
        (∀ q ∈ M, ∃ i t, i < k ∧ chainStepsCore prims.core m i ≤ t ∧ t < vp.params.w - 1 ∧
          q.1 = stepKey prims a i t) ∧
        (∀ i (_ : i < k) (hil : i < vp.params.len) (t : ℕ), chainStepsCore prims.core m i ≤ t →
          t < vp.params.w - 1 →
          M[tcrCount (vp := vp) m i + (t - chainStepsCore prims.core m i)]? =
            some (stepKey prims a i t, chain prims pk (wotsChainAdrs a i) sig[i]
              (chainStepsCore prims.core m i) (t - chainStepsCore prims.core m i)))
    obtain ⟨fin2, h3, hJ2⟩ := ofFnM_run_det (outer (tcrO₂ pkSeedDist pk)) J2
      (fun i : Fin vp.params.len => chainWith (tcrChainHash pkSeedDist) (wotsChainAdrs a i.val)
        sig[i.val] (chainStepsCore prims.core m i.val)
        (vp.params.w - 1 - chainStepsCore prims.core m i.val))
      (fun i => chain prims pk (wotsChainAdrs a i.val) sig[i.val]
        (chainStepsCore prims.core m i.val) (vp.params.w - 1 - chainStepsCore prims.core m i.val))
      (fun i σ'' => (σ''.1 ++
        (List.range (vp.params.w - 1 - chainStepsCore prims.core m i.val)).map fun j =>
          (prims.adrsToKey ((wotsChainAdrs a i.val).setHashAddress
            (chainStepsCore prims.core m i.val + j)),
           chain prims pk (wotsChainAdrs a i.val) sig[i.val]
            (chainStepsCore prims.core m i.val) j), σ''.2))
      (by
        rintro i ⟨qs'', tws''⟩ ⟨ht2, M, hM, hMlen, hMm, hMget⟩
        simp only at ht2 hM
        subst qs'' tws''
        refine ⟨tcr_chain_run pkSeedDist pk _ _ _ _ _ _ ?_, rfl, _, (List.append_assoc _ _ _),
          ?_, ?_, ?_⟩
        · intro j hj
          have hjw : chainStepsCore prims.core m i.val + j < vp.params.w - 1 := by omega
          refine ⟨?_, ?_, ?_⟩
          · have h3 := tcrCount_le (vp := vp) m i.val
            have h4 := Nat.mul_le_mul_right (vp.params.w - 1) (Nat.succ_le_of_lt i.isLt)
            rw [Nat.succ_mul] at h4
            rw [List.length_append, hMlen]
            omega
          · rintro ⟨q, hq, hk⟩
            rcases List.mem_append.mp hq with hq | hq
            · rcases List.mem_append.mp hq with hq | hq
              · exact hold_qs q hq _ _ i.isLt hjw hk
              · obtain ⟨i', t, hi', -, ht, hk'⟩ := hMm q hq
                have := (stepKey_inj hS ha ha (by omega) i.isLt ht hjw (hk'.symm.trans hk)).2.1
                omega
            · obtain ⟨j', hj', rfl⟩ := List.mem_map.mp hq
              have hj'' := List.mem_range.mp hj'
              have := (stepKey_inj hS ha ha i.isLt i.isLt (by omega) hjw hk).2.2
              omega
          · intro hk
            rcases List.mem_append.mp hk with hk | hk
            · exact hold_tws _ _ i.isLt hjw hk
            · obtain ⟨i', hi', hb', hk'⟩ := hTm _ hk
              have hbi' : chainStepsCore prims.core m i' - 1 < vp.params.w - 1 := by
                have := hbw i'; omega
              obtain ⟨-, h10, h11⟩ := stepKey_inj hS ha ha i.isLt hi' hjw hbi' hk'
              subst h10
              omega
        · rw [List.length_append, hMlen, tcrCount_succ]; simp
        · intro q hq
          rcases List.mem_append.mp hq with hq | hq
          · obtain ⟨i', t, hi', r⟩ := hMm q hq
            exact ⟨i', t, by omega, r⟩
          · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hq
            have hj' := List.mem_range.mp hj
            exact ⟨i.val, _, Nat.lt_succ_self _, Nat.le_add_right _ _, by omega, rfl⟩
        · intro i' hi' hil t hbt ht
          rcases Nat.lt_succ_iff_lt_or_eq.mp hi' with hlt | heq
          · have h7 := hMget i' hlt hil t hbt ht
            have h8 := (List.getElem?_eq_some_iff.mp h7).1
            rw [List.getElem?_append_left h8, h7]
          · subst heq
            rw [← hMlen, List.getElem?_append_right (Nat.le_add_right _ _),
              Nat.add_sub_cancel_left, List.getElem?_map,
              List.getElem?_range (by omega)]
            simp only [Option.map_some]
            rw [Nat.add_sub_cancel' hbt]
            rfl)
      (qs, tws ++ T) ⟨rfl, [], by simp, by simp [tcrCount], by simp,
        fun i hi => absurd hi (by omega)⟩
    obtain ⟨qs2, tws2⟩ := fin2
    obtain ⟨ht2, M, hM, hMlen, hMm, hMget⟩ := hJ2
    simp only at ht2 hM
    subst qs2 tws2
    refine ⟨(qs ++ M, tws ++ T), ?_, ?_⟩
    · rw [wotsPkFromSigTops_eq_ofFn]
      exact h3
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [List.map_append, List.nodup_append]
        exact ⟨hI.nodup, by simp, by
          intro x hx y hy
          rw [List.map_singleton, List.mem_singleton] at hy
          subst hy
          exact fun h => hnew (h ▸ hx)⟩
      · intro e he
        rcases List.mem_append.mp he with he | he
        · exact hI.mem e he
        · rw [List.mem_singleton.mp he]; exact ha
      · intro e he
        rcases List.mem_append.mp he with he | he
        · exact hI.tops e he
        · rw [List.mem_singleton.mp he]
      · simp [hMlen, hI.len]
      · intro j e hj i t hbt ht
        rcases Nat.lt_or_ge j hist.length with hjl | hjl
        · have hj' : hist[j]? = some e := by rwa [List.getElem?_append_left hjl] at hj
          have hidx : tcrTargetIndex (hist ++ [(a, m, sig,
              wotsPkFromSigTops prims sig m pk a)]) j i.val t = tcrTargetIndex hist j i.val t := by
            simp only [tcrTargetIndex]
            rw [List.getElem?_append_left hjl, List.take_append_of_le_length hjl.le]
          have hu := hI.tgt j e hj' i t hbt ht
          rw [hidx]
          have h8 := (List.getElem?_eq_some_iff.mp hu).1
          show (qs ++ M)[_]? = _
          rw [List.getElem?_append_left h8]
          exact hu
        · have hjeq : j = hist.length := by
            have := (List.getElem?_eq_some_iff.mp hj).1
            simp at this
            omega
          subst hjeq
          have he : e = (a, m, sig, wotsPkFromSigTops prims sig m pk a) := by
            simpa using hj.symm
          subst he
          have hidx : tcrTargetIndex (hist ++ [(a, m, sig,
              wotsPkFromSigTops prims sig m pk a)]) hist.length i.val t =
              qs.length + (tcrCount (vp := vp) m i.val + (t - chainStepsCore prims.core m i.val)) := by
            simp [tcrTargetIndex, hI.len]
          rw [hidx]
          show (qs ++ M)[_]? = _
          rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
          exact hMget i.val i.isLt i.isLt t hbt ht
      · intro q hq
        rcases List.mem_append.mp hq with hq | hq
        · obtain ⟨e, he, r⟩ := hI.qs q hq
          exact ⟨e, List.mem_append_left _ he, r⟩
        · obtain ⟨i', t, hi', r⟩ := hMm q hq
          exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), i', t, hi', r⟩
      · intro k hk
        rcases List.mem_append.mp hk with hk | hk
        · rcases hI.tws k hk with h | ⟨e, he, r⟩
          · exact Or.inl h
          · exact Or.inr ⟨e, List.mem_append_left _ he, r⟩
        · obtain ⟨i', hi', r⟩ := hTm k hk
          exact Or.inr ⟨_, List.mem_append_right _ (List.mem_singleton_self _), i', hi', r⟩

end Tcr

/-! ## Assembly -/

section Final
variable (pkSeedDist : ProbComp prims.PkSeed)

/-- The last hybrid, returning the seed, the signing history and the forgery. -/
noncomputable def gameTriple (W : WotsGame.Adversary prims) :
    ProbComp (prims.PkSeed × List (WotsGame.Entry prims) ×
      (ℕ × prims.Y × WotsSig vp.params prims.core)) := do
  let pk ← pkSeedDist
  let y ← (simulateQ (WotsGame.oracles (vp.params.w - 2) (wotsInsts vp) pk) W.choose).run []
  let f ← W.forge y.1 pk
  pure (pk, y.2, f)

theorem hyb_eq (W : WotsGame.Adversary prims) :
    WotsGame.hyb pkSeedDist (wotsInsts vp) (vp.params.w - 2) W =
      (fun y => WotsGame.win y.1 y.2.1 y.2.2.1 y.2.2.2.1 y.2.2.2.2) <$>
        gameTriple pkSeedDist W := by
  simp only [WotsGame.hyb, gameTriple, map_bind, map_pure]
  refine bind_congr fun pk => bind_congr fun y => bind_congr fun f => ?_
  simp only [WotsGame.win]
  cases y.2[f.1]? <;> rfl

/-- The forgery yields a correct SM-PRE answer (first disjunct of `win_cases`). -/
def PreGood (pk : prims.PkSeed) (hist : List (WotsGame.Entry prims)) (j : ℕ) (m' : prims.Y)
    (sig' : WotsSig vp.params prims.core) : Prop :=
  ∃ e, hist[j]? = some e ∧ ∃ i : Fin vp.params.len,
    chainStepsCore prims.core m' i.val < chainStepsCore prims.core e.2.1 i.val ∧
    prims.F pk ((wotsChainAdrs e.1 i.val).setHashAddress
        (chainStepsCore prims.core e.2.1 i.val - 1))
      (preAnswer pk hist j m' sig').2 = e.2.2.1[i.val] ∧
    (preAnswer pk hist j m' sig').1 = preTargetIndex hist j i.val

/-- The forgery yields a correct SM-TCR answer (second disjunct of `win_cases`). -/
def TcrGood (pk : prims.PkSeed) (hist : List (WotsGame.Entry prims)) (j : ℕ) (m' : prims.Y)
    (sig' : WotsSig vp.params prims.core) : Prop :=
  ∃ e, hist[j]? = some e ∧ ∃ (i : Fin vp.params.len) (t : ℕ),
    chainStepsCore prims.core e.2.1 i.val ≤ t ∧ t < vp.params.w - 1 ∧
    (tcrAnswer pk hist j m' sig').1 = tcrTargetIndex hist j i.val t ∧
    (tcrAnswer pk hist j m' sig').2 ≠
      chain prims pk (wotsChainAdrs e.1 i.val) e.2.2.1[i.val]
        (chainStepsCore prims.core e.2.1 i.val) (t - chainStepsCore prims.core e.2.1 i.val) ∧
    prims.F pk ((wotsChainAdrs e.1 i.val).setHashAddress t) (tcrAnswer pk hist j m' sig').2 =
      prims.F pk ((wotsChainAdrs e.1 i.val).setHashAddress t)
        (chain prims pk (wotsChainAdrs e.1 i.val) e.2.2.1[i.val]
          (chainStepsCore prims.core e.2.1 i.val)
          (t - chainStepsCore prims.core e.2.1 i.val))

theorem win_good (hS : Structural vp prims) (pk : prims.PkSeed)
    (hist : List (WotsGame.Entry prims)) (j : ℕ) (m' : prims.Y)
    (sig' : WotsSig vp.params prims.core)
    (htops : ∀ e ∈ hist, e.2.2.2 = wotsPkFromSigTops prims e.2.2.1 e.2.1 pk e.1)
    (hwin : WotsGame.win pk hist j m' sig' = true) :
    PreGood pk hist j m' sig' ∨ TcrGood pk hist j m' sig' := by
  cases he : hist[j]? with
  | none => simp [WotsGame.win, he] at hwin
  | some e =>
    rcases win_cases hS pk hist j m' sig' e he hwin (htops e (List.mem_of_getElem? he)) with
      h | h
    · exact Or.inl ⟨e, he, h⟩
    · exact Or.inr ⟨e, he, h⟩

theorem prTrue_eq (g : ProbComp Bool) : prTrue g = Pr{let b ← g}[b = true] := by
  rw [prEvent_eq_evalDist_of_discrete]
  unfold prTrue
  congr 1

theorem pre_bound (hS : Structural vp prims) (W : WotsGame.Adversary prims) :
    Pr{let y ← gameTriple pkSeedDist W}[PreGood y.1 y.2.1 y.2.2.1 y.2.2.2.1 y.2.2.2.2] ≤
        SM_DT_PRE_Advantage (rPre pkSeedDist W) ∧
      ∀ y ∈ support (gameTriple pkSeedDist W), ∀ e ∈ y.2.1,
        e.2.2.2 = wotsPkFromSigTops prims e.2.2.1 e.2.1 y.1 e.1 := by
  have hrun := fun pk : prims.PkSeed =>
    nested_run _ (outer (preO₂ pkSeedDist pk))
      (WotsGame.oracles (vp.params.w - 2) (wotsInsts vp) pk) (PreInv pk)
      (sim_step (preO₂ pkSeedDist pk) (vp.params.w - 2) (wotsInsts vp) pk
        (preStart pkSeedDist) (preChainHash pkSeedDist) (preColl pkSeedDist) (PreInv pk)
        (pre_hcoll pkSeedDist pk) (pre_hsign pkSeedDist hS pk)) W.choose [] ([], [])
      ⟨by simp, by simp, by simp, by simp, by intro j e h; simp at h, by simp, by simp⟩
  let Xp : ProbComp (prims.PkSeed ×
      ((W.State × List (WotsGame.Entry prims)) × SM_DT_PRE_State prims.AdrsKey prims.Y) ×
      (ℕ × prims.Y × WotsSig vp.params prims.core)) := do
    let pk ← pkSeedDist
    let z ← (simulateQ (outer (preO₂ pkSeedDist pk))
      (WotsGame.simChoose W (wotsInsts vp) (preStart pkSeedDist) (preChainHash pkSeedDist)
        (preColl pkSeedDist))).run ([], [])
    let f ← W.forge z.1.1 pk
    pure (pk, z, f)
  have hproj : ((fun x => (x.1, x.2.1.1.2, x.2.2)) <$> Xp) =ᵈ gameTriple pkSeedDist W := by
    simp only [Xp, gameTriple, map_bind, map_pure]
    refine EvalDistEq.bind_right _ fun pk => ?_
    refine EvalDistEq.trans ?_ ((hrun pk).1.bind_left _)
    rw [bind_map_left]
    exact EvalDistEq.rfl
  have hsupp : ∀ x ∈ support Xp, PreInv x.1 x.2.1.1.2 x.2.1.2 := by
    intro x hx
    simp only [Xp, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hx
    obtain ⟨pk, -, z, hz, f, -, rfl⟩ := hx
    exact (hrun pk).2 z hz
  let K : (prims.PkSeed ×
      ((W.State × List (WotsGame.Entry prims)) × SM_DT_PRE_State prims.AdrsKey prims.Y) ×
      (ℕ × prims.Y × WotsSig vp.params prims.core)) → ProbComp Bool := fun x =>
    match x.2.1.2.1[(preAnswer x.1 x.2.1.1.2 x.2.2.1 x.2.2.2.1 x.2.2.2.2).1]? with
    | none => return false
    | some (t, u) =>
      return decide (prims.Thash x.1 t [(preAnswer x.1 x.2.1.1.2 x.2.2.1 x.2.2.2.1 x.2.2.2.2).2] =
        prims.Thash x.1 t [u])
  have hexp : SM_DT_PRE_Experiment (rPre pkSeedDist W) = Xp >>= K := by
    simp only [SM_DT_PRE_Experiment, rPre, Xp, K, bind_assoc, pure_bind]
    refine bind_congr fun pk => bind_congr fun z => bind_congr fun f => ?_
    generalize z.2.1[(preAnswer pk z.1.2 f.1 f.2.1 f.2.2).1]? = o
    rcases o with _ | ⟨t, u⟩ <;> rfl
  constructor
  · rw [SM_DT_PRE_Advantage, ← prTrue, prTrue_eq, hexp, ← hproj.prEvent_eq, prEvent_map]
    refine prEvent_le_prEvent_bind_of_support Xp K _ _ fun x hx hgood => ?_
    obtain ⟨e, he, i, hlt, hF, hidx⟩ := hgood
    obtain ⟨u, hu, hFu⟩ := (hsupp x hx).tgt _ e he i (by omega)
    simp only [K]
    rw [hidx, hu]
    simp only []
    rw [prEvent_pure]
    rw [if_pos]
    rw [decide_eq_true_iff]
    exact hF.trans hFu.symm
  · intro y hy e he
    rw [← support_eq_of_evalDistEq hproj, support_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact (hsupp x hx).tops e he

theorem tcr_bound (hS : Structural vp prims) (W : WotsGame.Adversary prims) :
    Pr{let y ← gameTriple pkSeedDist W}[TcrGood y.1 y.2.1 y.2.2.1 y.2.2.2.1 y.2.2.2.2] ≤
      SM_DT_TCR_Advantage (rTcr pkSeedDist W) := by
  have hrun := fun pk : prims.PkSeed =>
    nested_run _ (outer (tcrO₂ pkSeedDist pk))
      (WotsGame.oracles (vp.params.w - 2) (wotsInsts vp) pk) (TcrInv pk)
      (sim_step (tcrO₂ pkSeedDist pk) (vp.params.w - 2) (wotsInsts vp) pk
        (tcrStart pkSeedDist) (tcrChainHash pkSeedDist) (wtcrColl pkSeedDist) (TcrInv pk)
        (tcr_hcoll pkSeedDist pk) (tcr_hsign pkSeedDist hS pk)) W.choose [] ([], [])
      ⟨by simp, by simp, by simp, by simp, by intro j e h; simp at h, by simp, by simp⟩
  let Xt : ProbComp (prims.PkSeed ×
      ((W.State × List (WotsGame.Entry prims)) × SM_DT_TCR_State prims.AdrsKey prims.Y) ×
      (ℕ × prims.Y × WotsSig vp.params prims.core)) := do
    let pk ← pkSeedDist
    let z ← (simulateQ (outer (tcrO₂ pkSeedDist pk))
      (WotsGame.simChoose W (wotsInsts vp) (tcrStart pkSeedDist) (tcrChainHash pkSeedDist)
        (wtcrColl pkSeedDist))).run ([], [])
    let f ← W.forge z.1.1 pk
    pure (pk, z, f)
  have hproj : ((fun x => (x.1, x.2.1.1.2, x.2.2)) <$> Xt) =ᵈ gameTriple pkSeedDist W := by
    simp only [Xt, gameTriple, map_bind, map_pure]
    refine EvalDistEq.bind_right _ fun pk => ?_
    refine EvalDistEq.trans ?_ ((hrun pk).1.bind_left _)
    rw [bind_map_left]
    exact EvalDistEq.rfl
  have hsupp : ∀ x ∈ support Xt, TcrInv x.1 x.2.1.1.2 x.2.1.2 := by
    intro x hx
    simp only [Xt, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hx
    obtain ⟨pk, -, z, hz, f, -, rfl⟩ := hx
    exact (hrun pk).2 z hz
  let K : (prims.PkSeed ×
      ((W.State × List (WotsGame.Entry prims)) × SM_DT_TCR_State prims.AdrsKey prims.Y) ×
      (ℕ × prims.Y × WotsSig vp.params prims.core)) → ProbComp Bool := fun x =>
    match x.2.1.2.1[(tcrAnswer x.1 x.2.1.1.2 x.2.2.1 x.2.2.2.1 x.2.2.2.2).1]? with
    | none => return false
    | some (t, u) =>
      return decide ((tcrAnswer x.1 x.2.1.1.2 x.2.2.1 x.2.2.2.1 x.2.2.2.2).2 ≠ u ∧
        prims.Thash x.1 t [(tcrAnswer x.1 x.2.1.1.2 x.2.2.1 x.2.2.2.1 x.2.2.2.2).2] =
          prims.Thash x.1 t [u])
  have hexp : SM_DT_TCR_Experiment (rTcr pkSeedDist W) = Xt >>= K := by
    simp only [SM_DT_TCR_Experiment, rTcr, Xt, K, bind_assoc, pure_bind]
    refine bind_congr fun pk => bind_congr fun z => bind_congr fun f => ?_
    generalize z.2.1[(tcrAnswer pk z.1.2 f.1 f.2.1 f.2.2).1]? = o
    rcases o with _ | ⟨t, u⟩ <;> rfl
  rw [SM_DT_TCR_Advantage, ← prTrue, prTrue_eq, hexp, ← hproj.prEvent_eq, prEvent_map]
  refine prEvent_le_prEvent_bind_of_support Xt K _ _ fun x hx hgood => ?_
  obtain ⟨e, he, i, t, hbt, ht, hidx, hne, hF⟩ := hgood
  have hu := (hsupp x hx).tgt _ e he i t hbt ht
  simp only [K]
  rw [hidx, hu]
  simp only []
  rw [prEvent_pure, if_pos]
  rw [decide_eq_true_iff]
  exact ⟨hne, hF⟩

end Final

end WotsFinal

open WotsFinal in
/-- **Step 9.** -/
theorem stepWotsFinal (hS : Structural vp prims) (pkSeedDist : ProbComp prims.PkSeed)
    (W : WotsGame.Adversary prims) :
    StepWotsFinal pkSeedDist W (rPre pkSeedDist W) (rTcr pkSeedDist W) := by
  unfold StepWotsFinal
  obtain ⟨hpre, htops⟩ := pre_bound pkSeedDist hS W
  have htcr := tcr_bound pkSeedDist hS W
  rw [prTrue_eq, hyb_eq, prEvent_map]
  calc Pr{let y ← gameTriple pkSeedDist W}[
          WotsGame.win y.1 y.2.1 y.2.2.1 y.2.2.2.1 y.2.2.2.2 = true]
      ≤ Pr{let y ← gameTriple pkSeedDist W}[PreGood y.1 y.2.1 y.2.2.1 y.2.2.2.1 y.2.2.2.2 ∨
          TcrGood y.1 y.2.1 y.2.2.1 y.2.2.2.1 y.2.2.2.2] :=
        prEvent_mono_of_support _ _ _ fun y hy h => win_good hS _ _ _ _ _ (htops y hy) h
    _ ≤ Pr{let y ← gameTriple pkSeedDist W}[PreGood y.1 y.2.1 y.2.2.1 y.2.2.2.1 y.2.2.2.2] +
          Pr{let y ← gameTriple pkSeedDist W}[TcrGood y.1 y.2.1 y.2.2.1 y.2.2.2.1 y.2.2.2.2] :=
        prEvent_or_le _ _ _
    _ ≤ _ := add_le_add hpre htcr

end Reduction

#print axioms Reduction.win_cases
#print axioms Reduction.stepWotsFinal
