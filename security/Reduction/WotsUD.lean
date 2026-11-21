import Reduction.WotsFinal

/-!
# Step 8: the undetectability hybrid (`Hyb₀ → Hyb_{w-2}`)

`rUd W` (EC: `R_SMDTUDC_Game23WOTSTWES`) draws a hybrid index `k < w - 2` and simulates the WOTS
game for `W`.  For a chain with digit `b`:

* if `k + 1 < b`, it asks the SM-UD challenge oracle at the tweak of step `k` of the chain and
  continues the answer from position `k + 1` to `b` through the collection oracle;
* otherwise it samples the start value itself (position `min k (b - 1)`).

In the real world (answers `F(tweak, u)`, `u` uniform) this is `hyb k`; in the ideal world
(uniform answers) it is `hyb (k + 1)`.  Averaging over `k` gives
`|Pr[Hyb₀] − Pr[Hyb_{w-2}]| = (w - 2) · Adv^{SM-UD}(rUd W)` (HK22 Thm. 2, EC lines 4910–4951).
Each chain contributes at most one UD target, so the target cap `wotsChainTargets` suffices
(`Resources.rUd_challenges_le`).  The number of collection queries is that of `W` plus at most
`#inst·len·(w−1)`; `rUd (bWots A)` inherits the infeasibility of `bWots A`.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal TweakableHash

namespace Reduction

set_option linter.unusedSectionVars false

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]

/-- Oracle interface of an SM-UD adversary for `wotsUdProblem`. -/
abbrev UdSpec (pkSeedDist : ProbComp prims.PkSeed) :=
  unifSpec + (TweakableHash.SM_DT_UD_challengeSpec prims.AdrsKey prims.Y +
    TweakableHash.collectionSpec (wotsUdProblem vp prims pkSeedDist).thColl)

/-- Collection query of the SM-UD game (a refused query is read as `default`). -/
def udColl (pkSeedDist : ProbComp prims.PkSeed) (key : prims.AdrsKey) (xs : List prims.Y) :
    OracleComp (UdSpec (vp := vp) (prims := prims) pkSeedDist) prims.Y := do
  let r ← ((UdSpec (vp := vp) (prims := prims) pkSeedDist).query
      (Sum.inr (Sum.inr ⟨(), key, xs⟩)) :
    OracleComp (UdSpec (vp := vp) (prims := prims) pkSeedDist) (Option prims.Y))
  pure (r.getD default)

/-- Challenge query of the SM-UD game (a refused query is read as `default`). -/
def udChal (pkSeedDist : ProbComp prims.PkSeed) (key : prims.AdrsKey) :
    OracleComp (UdSpec (vp := vp) (prims := prims) pkSeedDist) prims.Y := do
  let r ← ((UdSpec (vp := vp) (prims := prims) pkSeedDist).query (Sum.inr (Sum.inl key)) :
    OracleComp (UdSpec (vp := vp) (prims := prims) pkSeedDist) (Option prims.Y))
  pure (r.getD default)

/-- How `rUd` continues a chain: through the collection oracle. -/
def udChainHash (pkSeedDist : ProbComp prims.PkSeed) (a : Adrs) (x : prims.Y) :
    OracleComp (UdSpec (vp := vp) (prims := prims) pkSeedDist) prims.Y :=
  udColl pkSeedDist (prims.adrsToKey a) [x]

/-- How `rUd` at hybrid index `k` produces the revealed value of a chain with digit `b`. -/
noncomputable def udStart (pkSeedDist : ProbComp prims.PkSeed) (k : ℕ) (ca : Adrs) (b : ℕ) :
    OracleComp (UdSpec (vp := vp) (prims := prims) pkSeedDist) prims.Y :=
  if k + 1 < b then do
    let y ← udChal pkSeedDist (prims.adrsToKey (ca.setHashAddress k))
    chainWith (udChainHash pkSeedDist) ca y (k + 1) (b - (k + 1))
  else do
    let s ← (monadLift ($ᵗ prims.Y : ProbComp prims.Y) :
      OracleComp (UdSpec (vp := vp) (prims := prims) pkSeedDist) prims.Y)
    chainWith (udChainHash pkSeedDist) ca s (min k (b - 1)) (b - min k (b - 1))

/-- The SM-UD adversary built from a WOTS-game adversary. -/
noncomputable def rUd (pkSeedDist : ProbComp prims.PkSeed) (W : WotsGame.Adversary prims) :
    TweakableHash.SM_DT_UD_Adversary (wotsUdProblem vp prims pkSeedDist) where
  State := W.State × List (WotsGame.Entry prims)
  pick := do
    let k ← (monadLift ($ᵗ (Fin (vp.params.w - 3 + 1)) : ProbComp (Fin (vp.params.w - 3 + 1))) :
      OracleComp (UdSpec (vp := vp) (prims := prims) pkSeedDist) (Fin (vp.params.w - 3 + 1)))
    WotsGame.simChoose W (wotsInsts vp) (udStart pkSeedDist k.val) (udChainHash pkSeedDist)
      (udColl pkSeedDist)
  distinguish := fun st pk => do
    let (j, m', sig') ← W.forge st.1 pk
    return WotsGame.win pk st.2 j m' sig'

/-! Helper lemmas live in `Reduction.WotsUD`. -/

namespace WotsUD

open WotsFinal

/-! ## Pointwise shape of the simulated signature -/

/-- Hybrid played by `rUd` at index `k` in the given world. -/
def hidx : SM_DT_UD_World → ℕ → ℕ
  | .real, k => k
  | .ideal, k => k + 1

/-- Answer of the challenge oracle as a function of its uniform sample. -/
def udResp (world : SM_DT_UD_World) (pk : prims.PkSeed) (key : prims.AdrsKey) (u : prims.Y) :
    prims.Y :=
  match world with
  | .real => prims.Thash pk key [u]
  | .ideal => u

/-- Position from which `udStart` continues the chain through the collection oracle. -/
def udPos (k b : ℕ) : ℕ := if k + 1 < b then k + 1 else min k (b - 1)

theorem udPos_pos {k b : ℕ} (h : k + 1 < b) : udPos k b = k + 1 := if_pos h
theorem udPos_neg {k b : ℕ} (h : ¬ k + 1 < b) : udPos k b = min k (b - 1) := if_neg h

/-- The challenge tweak (if any) `udStart` requests for chain `i` with digit `b`. -/
def udNewQ (prims : Primitives vp.params) (k : ℕ) (a : Adrs) (i b : ℕ) : List prims.AdrsKey :=
  if k + 1 < b then [stepKey prims a i k] else []

/-- The collection tweaks `udStart` spends for chain `i` with digit `b`. -/
def udNewT (prims : Primitives vp.params) (k : ℕ) (a : Adrs) (i b : ℕ) : List prims.AdrsKey :=
  (List.range (b - udPos k b)).map fun j => stepKey prims a i (udPos k b + j)

/-- Value revealed by `udStart` for chain `i` (digit `b`) as a function of its uniform sample. -/
def udVal (world : SM_DT_UD_World) (k : ℕ) (pk : prims.PkSeed) (a : Adrs) (i b : ℕ)
    (u : prims.Y) : prims.Y :=
  chain prims pk (wotsChainAdrs a i)
    (if k + 1 < b then udResp world pk (stepKey prims a i k) u else u) (udPos k b) (b - udPos k b)

theorem chain_front (pk : prims.PkSeed) (ad : Adrs) (x : prims.Y) (k n : ℕ) :
    chain prims pk ad (prims.F pk (ad.setHashAddress k) x) (k + 1) n =
      chain prims pk ad x k (n + 1) := by
  induction n with
  | zero => rw [chain_zero, chain_succ, chain_zero, Nat.add_zero]
  | succ n ih =>
    rw [chain_succ, ih, chain_succ prims pk ad x k (n + 1),
      show k + 1 + n = k + (n + 1) by omega]

theorem udVal_eq (world : SM_DT_UD_World) (k : ℕ) (pk : prims.PkSeed) (a : Adrs) (i b : ℕ)
    (u : prims.Y) :
    udVal world k pk a i b u =
      chain prims pk (wotsChainAdrs a i) u (min (hidx world k) (b - 1))
        (b - min (hidx world k) (b - 1)) := by
  unfold udVal
  by_cases h : k + 1 < b
  · rw [if_pos h, udPos_pos h]
    cases world with
    | real =>
      have h1 : min (hidx .real k) (b - 1) = k := by simp only [hidx]; omega
      have h2 : b - k = (b - (k + 1)) + 1 := by omega
      rw [h1, h2]
      exact chain_front pk (wotsChainAdrs a i) u k (b - (k + 1))
    | ideal =>
      have h1 : min (hidx .ideal k) (b - 1) = k + 1 := by simp only [hidx]; omega
      rw [h1]
      rfl
  · rw [if_neg h, udPos_neg h]
    have h1 : min (hidx world k) (b - 1) = min k (b - 1) := by
      cases world with
      | real => rfl
      | ideal => simp only [hidx]; omega
    rw [h1]

theorem hybSig_ud (world : SM_DT_UD_World) (k : ℕ) (pk : prims.PkSeed) (a : Adrs) (m : prims.Y)
    (ss : Vector prims.Y vp.params.len) :
    WotsGame.hybSig (hidx world k) pk a m ss =
      Vector.ofFn fun i : Fin vp.params.len =>
        udVal world k pk a i.val (chainStepsCore prims.core m i.val) ss[i] := by
  unfold WotsGame.hybSig
  congr 1
  funext i
  rw [udVal_eq]
  rfl

/-! ## The SM-UD oracles and single-call evaluations -/

section Run
variable (pkSeedDist : ProbComp prims.PkSeed)

/-- The two game oracles of SM-UD (challenge and collection) at seed `pk`. -/
noncomputable abbrev udO₂ (world : SM_DT_UD_World) (pk : prims.PkSeed) :
    QueryImpl (SM_DT_UD_challengeSpec prims.AdrsKey prims.Y +
      collectionSpec (wotsUdProblem vp prims pkSeedDist).thColl)
      (StateT (SM_DT_UD_State prims.AdrsKey) ProbComp) :=
  SM_DT_UD_challengeOracle world (wotsUdProblem vp prims pkSeedDist) pk +
    collectionOracle (Q := prims.AdrsKey) id (wotsUdProblem vp prims pkSeedDist).thColl pk

theorem udColl_run (world : SM_DT_UD_World) (pk : prims.PkSeed) (key : prims.AdrsKey)
    (xs : List prims.Y) (qs tws : List prims.AdrsKey) (h : ¬ TweakReserved id qs key) :
    (simulateQ (outer (udO₂ pkSeedDist world pk)) (udColl pkSeedDist key xs)).run (qs, tws) =
      pure (prims.Thash pk key xs, (qs, tws ++ [key])) := by
  simp [udColl, outer, udO₂, collectionOracle, h]
  rfl

theorem udChal_run (world : SM_DT_UD_World) (pk : prims.PkSeed) (key : prims.AdrsKey)
    (qs tws : List prims.AdrsKey) (hlen : qs.length < wotsChainTargets vp)
    (hfresh : TweakFresh id qs tws key) :
    (simulateQ (outer (udO₂ pkSeedDist world pk)) (udChal pkSeedDist key)).run (qs, tws) =
      (fun u => (udResp world pk key u, (qs ++ [key], tws))) <$>
        ($ᵗ prims.Y : ProbComp prims.Y) := by
  cases world with
  | real =>
    have h1 := SM_DT_UD_challengeOracle_run_of_fresh_real
      (prob := wotsUdProblem vp prims pkSeedDist) (pk := pk) (t := key) (qsChal := qs)
      (twsColl := tws) hlen hfresh
    simp [udChal, outer, udO₂, h1]
    rfl
  | ideal =>
    have h1 := SM_DT_UD_challengeOracle_run_of_fresh_ideal
      (prob := wotsUdProblem vp prims pkSeedDist) (pk := pk) (t := key) (qsChal := qs)
      (twsColl := tws) hlen hfresh
    simp [udChal, outer, udO₂, h1]
    rfl

theorem ud_chain_run (world : SM_DT_UD_World) (pk : prims.PkSeed) (ad : Adrs) (x : prims.Y)
    (i s : ℕ) (qs tws : List prims.AdrsKey)
    (hfresh : ∀ j < s, ¬ TweakReserved id qs (prims.adrsToKey (ad.setHashAddress (i + j)))) :
    (simulateQ (outer (udO₂ pkSeedDist world pk))
        (chainWith (udChainHash pkSeedDist) ad x i s)).run (qs, tws) =ᵈ
      (pure (chain prims pk ad x i s,
        (qs, tws ++ (List.range s).map fun j => prims.adrsToKey (ad.setHashAddress (i + j)))) :
        ProbComp _) := by
  induction s with
  | zero => simp [chainWith_zero]
  | succ s ih =>
    rw [chainWith_succ, simulateQ_bind, StateT.run_bind]
    refine ((ih fun j hj => hfresh j (Nat.lt_succ_of_lt hj)).bind_left _).trans ?_
    rw [pure_bind]
    simp only [udChainHash]
    rw [udColl_run pkSeedDist world pk _ _ qs _ (hfresh s (Nat.lt_succ_self s)), chain_succ,
      List.range_succ, List.map_append, ← List.append_assoc]
    exact EvalDistEq.rfl

theorem udStart_run (world : SM_DT_UD_World) (pk : prims.PkSeed) (k : ℕ) (a : Adrs) (i b : ℕ)
    (qs tws : List prims.AdrsKey)
    (hchal : k + 1 < b → qs.length < wotsChainTargets vp ∧
      TweakFresh id qs tws (stepKey prims a i k))
    (hcoll : ∀ j < b - udPos k b,
      ¬ TweakReserved id (qs ++ udNewQ prims k a i b) (stepKey prims a i (udPos k b + j))) :
    (simulateQ (outer (udO₂ pkSeedDist world pk))
        (udStart pkSeedDist k (wotsChainAdrs a i) b)).run (qs, tws) =ᵈ
      (fun u => (udVal world k pk a i b u, (qs ++ udNewQ prims k a i b, tws ++ udNewT prims k a i b)))
        <$> ($ᵗ prims.Y : ProbComp prims.Y) := by
  by_cases h : k + 1 < b
  · have hp := udPos_pos h
    have hn : udNewQ prims k a i b = [stepKey prims a i k] := if_pos h
    rw [hn, hp] at hcoll
    simp only [udStart, if_pos h, simulateQ_bind, StateT.run_bind]
    have hc := udChal_run pkSeedDist world pk
      (prims.adrsToKey ((wotsChainAdrs a i).setHashAddress k)) qs tws (hchal h).1 (hchal h).2
    rw [hc, bind_map_left]
    refine (EvalDistEq.bind_right _ (fun u => ud_chain_run pkSeedDist world pk
      (wotsChainAdrs a i) _ (k + 1) (b - (k + 1)) _ tws hcoll)).trans ?_
    simp only [udVal, udNewT, if_pos h, hp, hn, bind_pure_comp]
    exact EvalDistEq.rfl
  · have hp := udPos_neg h
    have hn : udNewQ prims k a i b = [] := if_neg h
    rw [hn, hp, List.append_nil] at hcoll
    simp only [udStart, if_neg h, simulateQ_bind, StateT.run_bind]
    rw [outer_lift, bind_map_left]
    refine (EvalDistEq.bind_right _ (fun u => ud_chain_run pkSeedDist world pk
      (wotsChainAdrs a i) u (min k (b - 1)) (b - min k (b - 1)) qs tws hcoll)).trans ?_
    simp only [udVal, udNewT, if_neg h, hp, hn, List.append_nil, bind_pure_comp]
    exact EvalDistEq.rfl

/-! ## Invariant and per-query analysis -/

/-- Invariant relating the mirrored signing history to the SM-UD game state at hybrid index `k`:
challenge tweaks are step `k` of chains with digit `> k + 1`; reserved collection tweaks are
chain steps of signed instances other than a challenged step. -/
structure UdInv (k : ℕ) (hist : List (WotsGame.Entry prims))
    (σ : SM_DT_UD_State prims.AdrsKey) : Prop where
  nodup : (hist.map (·.1)).Nodup
  mem : ∀ e ∈ hist, e.1 ∈ wotsInsts vp
  len : σ.1.length ≤ hist.length * vp.params.len
  qs : ∀ q ∈ σ.1, ∃ e ∈ hist, ∃ i, i < vp.params.len ∧
    k + 1 < chainStepsCore prims.core e.2.1 i ∧ q = stepKey prims e.1 i k
  tws : ∀ key ∈ σ.2, WotsGame.reservedKey (wotsInsts vp) key = false ∨
    ∃ e ∈ hist, ∃ i t, i < vp.params.len ∧ t < vp.params.w - 1 ∧ key = stepKey prims e.1 i t ∧
      (k + 1 < chainStepsCore prims.core e.2.1 i → t ≠ k)

theorem ud_hcoll (world : SM_DT_UD_World) (k : ℕ) (pk : prims.PkSeed)
    (hist : List (WotsGame.Entry prims)) (σ : SM_DT_UD_State prims.AdrsKey)
    (key : prims.AdrsKey) (xs : List prims.Y)
    (hI : UdInv k hist σ) (hres : WotsGame.reservedKey (wotsInsts vp) key = false) :
    ∃ σ', (simulateQ (outer (udO₂ pkSeedDist world pk)) (udColl pkSeedDist key xs)).run σ =ᵈ
      (pure (prims.Thash pk key xs, σ') : ProbComp _) ∧ UdInv k hist σ' := by
  obtain ⟨qs, tws⟩ := σ
  have hnot : ¬ TweakReserved id qs key := by
    rintro ⟨q, hq, rfl⟩
    obtain ⟨e, he, i, hi, hb, hk⟩ := hI.qs q hq
    have hbw := chainStepsCore_le prims.core e.2.1 i
    have hk' : id q = stepKey prims e.1 i k := hk
    rw [hk', reservedKey_stepKey (hI.mem e he) hi (by omega)] at hres
    exact Bool.noConfusion hres
  refine ⟨(qs, tws ++ [key]), ?_, ⟨hI.nodup, hI.mem, hI.len, hI.qs, ?_⟩⟩
  · rw [udColl_run pkSeedDist world pk key xs qs tws hnot]
  · intro k' hk
    rcases List.mem_append.mp hk with hk | hk
    · exact hI.tws k' hk
    · left
      rw [List.mem_singleton.mp hk]
      exact hres

theorem ud_hsign (hS : Structural vp prims) (world : SM_DT_UD_World) (k : ℕ) (pk : prims.PkSeed)
    (hist : List (WotsGame.Entry prims)) (σ : SM_DT_UD_State prims.AdrsKey)
    (a : Adrs) (m : prims.Y) (hI : UdInv k hist σ) (ha : a ∈ wotsInsts vp)
    (hnew : a ∉ hist.map (·.1)) :
    ∃ fin1 : Vector prims.Y vp.params.len → SM_DT_UD_State prims.AdrsKey,
      (simulateQ (outer (udO₂ pkSeedDist world pk)) (Vector.ofFnM fun i : Fin vp.params.len =>
          udStart pkSeedDist k (wotsChainAdrs a i.val)
            (chainStepsCore prims.core m i.val))).run σ =ᵈ
        (fun ss => (WotsGame.hybSig (hidx world k) pk a m ss, fin1 ss)) <$>
          ($ᵗ (Vector prims.Y vp.params.len) : ProbComp _) ∧
      ∀ ss, ∃ fin2,
        (simulateQ (outer (udO₂ pkSeedDist world pk)) (wotsPkFromSigTopsWith prims.core
            (udChainHash pkSeedDist) (WotsGame.hybSig (hidx world k) pk a m ss) m a)).run
            (fin1 ss) =ᵈ
          (pure (wotsPkFromSigTops prims (WotsGame.hybSig (hidx world k) pk a m ss) m pk a,
            fin2) : ProbComp _) ∧
        UdInv k (hist ++ [(a, m, WotsGame.hybSig (hidx world k) pk a m ss,
          wotsPkFromSigTops prims (WotsGame.hybSig (hidx world k) pk a m ss) m pk a)]) fin2 := by
  obtain ⟨qs, tws⟩ := σ
  have hbw : ∀ i, chainStepsCore prims.core m i ≤ vp.params.w - 1 :=
    fun i => chainStepsCore_le prims.core m i
  have hcount := hist_length_lt hI.nodup hI.mem ha hnew
  have hqslen : qs.length ≤ hist.length * vp.params.len := hI.len
  have hcap : hist.length * vp.params.len + vp.params.len ≤ wotsChainTargets vp := by
    have h4 := Nat.mul_le_mul_right vp.params.len hcount
    rw [Nat.succ_mul] at h4
    exact h4
  -- the new instance's tweaks do not occur in the old state
  have hold_qs : ∀ q ∈ qs, ∀ i t, i < vp.params.len → t < vp.params.w - 1 →
      q ≠ stepKey prims a i t := by
    intro q hq i t hi ht hk
    obtain ⟨e, he, i', hi', hb', hk'⟩ := hI.qs q hq
    have hbw' := chainStepsCore_le prims.core e.2.1 i'
    have := (stepKey_inj hS (hI.mem e he) ha hi' hi (by omega) ht (hk'.symm.trans hk)).1
    exact hnew (this ▸ List.mem_map_of_mem (f := (·.1)) he)
  have hold_tws : ∀ i t, i < vp.params.len → t < vp.params.w - 1 →
      stepKey prims a i t ∉ tws := by
    intro i t hi ht hk
    rcases hI.tws _ hk with h | ⟨e, he, i', t', hi', ht', hk', -⟩
    · rw [reservedKey_stepKey ha hi ht] at h
      exact Bool.noConfusion h
    · have := (stepKey_inj hS ha (hI.mem e he) hi hi' ht ht' hk').1
      exact hnew (this ▸ List.mem_map_of_mem (f := (·.1)) he)
  -- phase 1: the revealed values
  let J : (n : ℕ) → Vector prims.Y n → SM_DT_UD_State prims.AdrsKey → Prop :=
    fun n _ σ' => ∃ L T : List prims.AdrsKey, σ'.1 = qs ++ L ∧ σ'.2 = tws ++ T ∧
      L.length ≤ n ∧
      (∀ q ∈ L, ∃ i, i < n ∧ i < vp.params.len ∧ k + 1 < chainStepsCore prims.core m i ∧
        q = stepKey prims a i k) ∧
      (∀ key ∈ T, ∃ i t, i < vp.params.len ∧ t < vp.params.w - 1 ∧
        key = stepKey prims a i t ∧ (k + 1 < chainStepsCore prims.core m i → t ≠ k))
  obtain ⟨fin1, h1, hJ⟩ := ofFnM_run_sample (outer (udO₂ pkSeedDist world pk)) J
    (fun i : Fin vp.params.len =>
      udStart pkSeedDist k (wotsChainAdrs a i.val) (chainStepsCore prims.core m i.val))
    (fun i u => udVal world k pk a i.val (chainStepsCore prims.core m i.val) u)
    (fun i _ σ' => (σ'.1 ++ udNewQ prims k a i.val (chainStepsCore prims.core m i.val),
      σ'.2 ++ udNewT prims k a i.val (chainStepsCore prims.core m i.val)))
    (by
      rintro i us ⟨qs', tws'⟩ ⟨L, T, hL, hT, hlen, hLm, hTm⟩
      simp only at hL hT
      subst qs' tws'
      have hbi := hbw i.val
      have hil := i.isLt
      generalize hb : chainStepsCore prims.core m i.val = b at hbi
      have hLne : ∀ q ∈ qs ++ L, ∀ t, t < vp.params.w - 1 → (k + 1 < b → t ≠ k) →
          q ≠ stepKey prims a i.val t := by
        intro q hq t ht himp hk
        rcases List.mem_append.mp hq with hq | hq
        · exact hold_qs q hq i.val t hil ht hk
        · obtain ⟨i', hi', hi'l, hb', hk'⟩ := hLm q hq
          have hbw' := hbw i'
          have := (stepKey_inj hS ha ha hi'l hil (by omega) ht (hk'.symm.trans hk)).2.1
          omega
      have hchal : k + 1 < b → (qs ++ L).length < wotsChainTargets vp ∧
          TweakFresh id (qs ++ L) (tws ++ T) (stepKey prims a i.val k) := by
        intro h
        refine ⟨?_, ?_, ?_⟩
        · rw [List.length_append]
          omega
        · rintro ⟨q, hq, hk⟩
          rcases List.mem_append.mp hq with hq | hq
          · exact hold_qs q hq i.val k hil (by omega) hk
          · obtain ⟨i', hi', hi'l, hb', hk'⟩ := hLm q hq
            have := (stepKey_inj hS ha ha hi'l hil (by omega) (by omega) (hk'.symm.trans hk)).2.1
            omega
        · intro hmem
          rcases List.mem_append.mp hmem with hmem | hmem
          · exact hold_tws i.val k hil (by omega) hmem
          · obtain ⟨i', t, hi', ht, hk', himp⟩ := hTm _ hmem
            obtain ⟨-, h1, h2⟩ := stepKey_inj hS ha ha hil hi' (by omega) ht hk'
            subst h1
            rw [hb] at himp
            exact himp h h2.symm
      have hcoll : ∀ j < b - udPos k b,
          ¬ TweakReserved id ((qs ++ L) ++ udNewQ prims k a i.val b)
            (stepKey prims a i.val (udPos k b + j)) := by
        rintro j hj ⟨q, hq, hk⟩
        have ht : udPos k b + j < vp.params.w - 1 := by omega
        rcases List.mem_append.mp hq with hq | hq
        · refine hLne q hq _ ht (fun h => ?_) hk
          rw [udPos_pos h]
          omega
        · by_cases h : k + 1 < b
          · rw [udNewQ, if_pos h, List.mem_singleton] at hq
            rw [hq] at hk
            have := (stepKey_inj hS ha ha hil hil (by omega) ht hk).2.2
            rw [udPos_pos h] at this
            omega
          · rw [udNewQ, if_neg h] at hq
            exact absurd hq (List.not_mem_nil)
      constructor
      · exact udStart_run pkSeedDist world pk k a i.val b (qs ++ L) (tws ++ T) hchal hcoll
      · intro u
        refine ⟨L ++ udNewQ prims k a i.val b, T ++ udNewT prims k a i.val b,
          (List.append_assoc _ _ _), (List.append_assoc _ _ _), ?_, ?_, ?_⟩
        · rw [List.length_append]
          have : (udNewQ prims k a i.val b).length ≤ 1 := by
            unfold udNewQ; split_ifs <;> simp
          omega
        · intro q hq
          rcases List.mem_append.mp hq with hq | hq
          · obtain ⟨i', hi', r⟩ := hLm q hq
            exact ⟨i', by omega, r⟩
          · by_cases h : k + 1 < b
            · rw [udNewQ, if_pos h, List.mem_singleton] at hq
              exact ⟨i.val, Nat.lt_succ_self _, hil, by rw [hb]; exact h, hq⟩
            · rw [udNewQ, if_neg h] at hq
              exact absurd hq (List.not_mem_nil)
        · intro key hkey
          rcases List.mem_append.mp hkey with hkey | hkey
          · exact hTm key hkey
          · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hkey
            have hj' := List.mem_range.mp hj
            refine ⟨i.val, _, hil, by omega, rfl, fun h => ?_⟩
            rw [hb] at h
            rw [udPos_pos h]
            omega)
    (qs, tws) ⟨[], [], by simp, by simp, by simp, by simp, by simp⟩
  refine ⟨fin1, ?_, ?_⟩
  · have e : (fun us : Vector prims.Y vp.params.len =>
          (Vector.ofFn fun i : Fin vp.params.len =>
            udVal world k pk a i.val (chainStepsCore prims.core m i.val) us[i], fin1 us)) =
        fun ss => (WotsGame.hybSig (hidx world k) pk a m ss, fin1 ss) :=
      funext fun ss => by rw [hybSig_ud]
    rw [← e]
    exact h1
  · intro ss
    obtain ⟨L, T, hL, hT, hlen, hLm, hTm⟩ := hJ ss
    generalize hfin : fin1 ss = σ1 at hL hT
    obtain ⟨qs1, tws1⟩ := σ1
    simp only at hL hT
    subst qs1 tws1
    generalize WotsGame.hybSig (hidx world k) pk a m ss = sig
    let J2 : ℕ → SM_DT_UD_State prims.AdrsKey → Prop :=
      fun _ σ'' => σ''.1 = qs ++ L ∧ ∃ T' : List prims.AdrsKey, σ''.2 = tws ++ T' ∧
        ∀ key ∈ T', ∃ i t, i < vp.params.len ∧ t < vp.params.w - 1 ∧
          key = stepKey prims a i t ∧ (k + 1 < chainStepsCore prims.core m i → t ≠ k)
    obtain ⟨fin2, h3, hJ2⟩ := ofFnM_run_det (outer (udO₂ pkSeedDist world pk)) J2
      (fun i : Fin vp.params.len => chainWith (udChainHash pkSeedDist) (wotsChainAdrs a i.val)
        sig[i.val] (chainStepsCore prims.core m i.val)
        (vp.params.w - 1 - chainStepsCore prims.core m i.val))
      (fun i => chain prims pk (wotsChainAdrs a i.val) sig[i.val]
        (chainStepsCore prims.core m i.val) (vp.params.w - 1 - chainStepsCore prims.core m i.val))
      (fun i σ'' => (σ''.1, σ''.2 ++
        (List.range (vp.params.w - 1 - chainStepsCore prims.core m i.val)).map fun j =>
          prims.adrsToKey ((wotsChainAdrs a i.val).setHashAddress
            (chainStepsCore prims.core m i.val + j))))
      (by
        rintro i ⟨qs'', tws''⟩ ⟨hq, T', hT', hTm'⟩
        simp only at hq hT'
        subst qs'' tws''
        refine ⟨ud_chain_run pkSeedDist world pk _ _ _ _ _ _ ?_, rfl, _,
          (List.append_assoc _ _ _), ?_⟩
        · rintro j hj ⟨q, hq, hk⟩
          have hjw : chainStepsCore prims.core m i.val + j < vp.params.w - 1 := by omega
          rcases List.mem_append.mp hq with hq | hq
          · exact hold_qs q hq _ _ i.isLt hjw hk
          · obtain ⟨i', hi', hi'l, hb', hk'⟩ := hLm q hq
            have hbw' := hbw i'
            obtain ⟨-, h10, h11⟩ := stepKey_inj hS ha ha hi'l i.isLt (by omega) hjw
              (hk'.symm.trans hk)
            subst h10
            omega
        · intro key hkey
          rcases List.mem_append.mp hkey with hkey | hkey
          · exact hTm' key hkey
          · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hkey
            have hj' := List.mem_range.mp hj
            exact ⟨i.val, _, i.isLt, by omega, rfl, fun h => by omega⟩)
      (qs ++ L, tws ++ T) ⟨rfl, T, rfl, hTm⟩
    obtain ⟨qs2, tws2⟩ := fin2
    obtain ⟨hq2, T', hT', hTm'⟩ := hJ2
    simp only at hq2 hT'
    subst qs2 tws2
    refine ⟨(qs ++ L, tws ++ T'), ?_, ?_⟩
    · rw [wotsPkFromSigTops_eq_ofFn]
      exact h3
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩
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
      · show (qs ++ L).length ≤ _
        rw [List.length_append, List.length_append, List.length_singleton, Nat.succ_mul]
        omega
      · intro q hq
        rcases List.mem_append.mp hq with hq | hq
        · obtain ⟨e, he, r⟩ := hI.qs q hq
          exact ⟨e, List.mem_append_left _ he, r⟩
        · obtain ⟨i', -, hi', r⟩ := hLm q hq
          exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), i', hi', r⟩
      · intro key hkey
        rcases List.mem_append.mp hkey with hkey | hkey
        · rcases hI.tws key hkey with h | ⟨e, he, r⟩
          · exact Or.inl h
          · exact Or.inr ⟨e, List.mem_append_left _ he, r⟩
        · obtain ⟨i', t, r⟩ := hTm' key hkey
          exact Or.inr ⟨_, List.mem_append_right _ (List.mem_singleton_self _), i', t, r⟩

end Run

/-! ## Assembly -/

section Final
variable (pkSeedDist : ProbComp prims.PkSeed)

/-- The SM-UD experiment of `rUd` with the hybrid index fixed to `k`. -/
noncomputable def udFixed (world : SM_DT_UD_World) (k : ℕ) (W : WotsGame.Adversary prims) :
    ProbComp Bool := do
  let pk ← pkSeedDist
  let z ← (simulateQ (outer (udO₂ pkSeedDist world pk))
    (WotsGame.simChoose W (wotsInsts vp) (udStart pkSeedDist k) (udChainHash pkSeedDist)
      (udColl pkSeedDist))).run ([], [])
  let f ← W.forge z.1.1 pk
  pure (WotsGame.win pk z.1.2 f.1 f.2.1 f.2.2)

/-- At a fixed index `k`, `rUd` plays hybrid `k` (real world) resp. `k + 1` (ideal world). -/
theorem udFixed_eq (hS : Structural vp prims) (world : SM_DT_UD_World) (k : ℕ)
    (W : WotsGame.Adversary prims) :
    udFixed pkSeedDist world k W =ᵈ WotsGame.hyb pkSeedDist (wotsInsts vp) (hidx world k) W := by
  have hrun := fun pk : prims.PkSeed =>
    nested_run _ (outer (udO₂ pkSeedDist world pk))
      (WotsGame.oracles (hidx world k) (wotsInsts vp) pk) (UdInv k)
      (sim_step (udO₂ pkSeedDist world pk) (hidx world k) (wotsInsts vp) pk
        (udStart pkSeedDist k) (udChainHash pkSeedDist) (udColl pkSeedDist) (UdInv k)
        (ud_hcoll pkSeedDist world k pk) (ud_hsign pkSeedDist hS world k pk)) W.choose [] ([], [])
      ⟨by simp, by simp, by simp, by simp, by simp⟩
  have hh : WotsGame.hyb pkSeedDist (wotsInsts vp) (hidx world k) W = (do
      let pk ← pkSeedDist
      let y ← (simulateQ (WotsGame.oracles (hidx world k) (wotsInsts vp) pk) W.choose).run []
      let f ← W.forge y.1 pk
      pure (WotsGame.win pk y.2 f.1 f.2.1 f.2.2)) := by
    simp only [WotsGame.hyb]
    refine bind_congr fun pk => bind_congr fun y => bind_congr fun f => ?_
    simp only [WotsGame.win]
    cases y.2[f.1]? <;> rfl
  rw [hh]
  unfold udFixed
  refine EvalDistEq.bind_right _ fun pk => ?_
  refine EvalDistEq.trans ?_ ((hrun pk).1.bind_left _)
  rw [bind_map_left]
  exact EvalDistEq.rfl

/-- The SM-UD experiment of `rUd` is the uniform mixture of the fixed-index experiments. -/
theorem experiment_eq (world : SM_DT_UD_World) (W : WotsGame.Adversary prims) :
    SM_DT_UD_Experiment world (rUd pkSeedDist W) =ᵈ
      (($ᵗ (Fin (vp.params.w - 3 + 1)) : ProbComp _) >>= fun kf =>
        udFixed pkSeedDist world kf.val W) := by
  have h1 : ∀ pk : prims.PkSeed,
      (simulateQ (SM_DT_UD_oracles world (wotsUdProblem vp prims pkSeedDist) pk)
        (rUd pkSeedDist W).pick).run ([], []) =
      (($ᵗ (Fin (vp.params.w - 3 + 1)) : ProbComp _) >>= fun kf =>
        (simulateQ (outer (udO₂ pkSeedDist world pk))
          (WotsGame.simChoose W (wotsInsts vp) (udStart pkSeedDist kf.val)
            (udChainHash pkSeedDist) (udColl pkSeedDist))).run ([], [])) := by
    intro pk
    show (simulateQ (outer (udO₂ pkSeedDist world pk))
      ((monadLift ($ᵗ (Fin (vp.params.w - 3 + 1)) : ProbComp (Fin (vp.params.w - 3 + 1))) :
        OracleComp (UdSpec (vp := vp) (prims := prims) pkSeedDist) _) >>= fun kf =>
          WotsGame.simChoose W (wotsInsts vp) (udStart pkSeedDist kf.val)
            (udChainHash pkSeedDist) (udColl pkSeedDist))).run ([], []) = _
    rw [simulateQ_bind, StateT.run_bind, outer_lift, bind_map_left]
  have h2 : SM_DT_UD_Experiment world (rUd pkSeedDist W) =
      (pkSeedDist >>= fun pk => ($ᵗ (Fin (vp.params.w - 3 + 1)) : ProbComp _) >>= fun kf =>
        (simulateQ (outer (udO₂ pkSeedDist world pk))
          (WotsGame.simChoose W (wotsInsts vp) (udStart pkSeedDist kf.val)
            (udChainHash pkSeedDist) (udColl pkSeedDist))).run ([], []) >>= fun z =>
        W.forge z.1.1 pk >>= fun f => pure (WotsGame.win pk z.1.2 f.1 f.2.1 f.2.2)) := by
    unfold SM_DT_UD_Experiment
    show (pkSeedDist >>= fun pk => _) = _
    refine bind_congr fun pk => ?_
    rw [h1 pk]
    exact bind_assoc _ _ _
  rw [h2]
  exact EvalDistEq.bind_bind_swap _ _ _

/-- Both worlds at once: `(w - 2) · Pr[SM-UD experiment] = Σ_k Pr[hyb (hidx world k)]`. -/
theorem ud_sum (hS : Structural vp prims) (world : SM_DT_UD_World)
    (W : WotsGame.Adversary prims) (hw : 3 ≤ vp.params.w) :
    ((vp.params.w - 2 : ℕ) : ℝ≥0∞) * 𝒟[SM_DT_UD_Experiment world (rUd pkSeedDist W)] {true} =
      ∑ k ∈ Finset.range (vp.params.w - 2),
        prTrue (WotsGame.hyb pkSeedDist (wotsInsts vp) (hidx world k) W) := by
  have e1 : 𝒟[SM_DT_UD_Experiment world (rUd pkSeedDist W)] {true} =
      prTrue (SM_DT_UD_Experiment world (rUd pkSeedDist W)) := rfl
  rw [e1, prTrue_eq, (experiment_eq pkSeedDist world W).prEvent_eq, prEvent_bind_eq_sum_fintype]
  simp only [SampleableType.prEvent_uniformSample_eq_singleton, Fintype.card_fin]
  rw [← Finset.mul_sum,
    Fin.sum_univ_eq_sum_range
      (fun k => Pr{let b ← udFixed pkSeedDist world k W}[b = true]) (vp.params.w - 3 + 1),
    show vp.params.w - 3 + 1 = vp.params.w - 2 by omega, ← mul_assoc,
    ENNReal.mul_inv_cancel (Nat.cast_ne_zero.mpr (by omega)) (ENNReal.natCast_ne_top _), one_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [prTrue_eq]
  exact (udFixed_eq pkSeedDist hS world k W).prEvent_eq _

end Final

end WotsUD

open WotsUD in
/-- Real world at hybrid index `k` is `hyb k`; ideal world is `hyb (k + 1)` (statement for the
averaged adversary). -/
theorem udReal_rUd (hS : Structural vp prims) (pkSeedDist : ProbComp prims.PkSeed)
    (W : WotsGame.Adversary prims) (hw : 3 ≤ vp.params.w) :
    ((vp.params.w - 2 : ℕ) : ℝ≥0∞) * 𝒟[TweakableHash.SM_DT_UD_Experiment .real
        (rUd pkSeedDist W)] {true} =
      ∑ k ∈ Finset.range (vp.params.w - 2),
        prTrue (WotsGame.hyb pkSeedDist (wotsInsts vp) k W) :=
  ud_sum pkSeedDist hS .real W hw

open WotsUD in
theorem udIdeal_rUd (hS : Structural vp prims) (pkSeedDist : ProbComp prims.PkSeed)
    (W : WotsGame.Adversary prims) (hw : 3 ≤ vp.params.w) :
    ((vp.params.w - 2 : ℕ) : ℝ≥0∞) * 𝒟[TweakableHash.SM_DT_UD_Experiment .ideal
        (rUd pkSeedDist W)] {true} =
      ∑ k ∈ Finset.range (vp.params.w - 2),
        prTrue (WotsGame.hyb pkSeedDist (wotsInsts vp) (k + 1) W) :=
  ud_sum pkSeedDist hS .ideal W hw

/-- **Step 8.** -/
theorem stepWotsUD (hS : Structural vp prims) (pkSeedDist : ProbComp prims.PkSeed)
    (W : WotsGame.Adversary prims) : StepWotsUD pkSeedDist W (rUd pkSeedDist W) := by
  unfold StepWotsUD
  by_cases hw : 3 ≤ vp.params.w
  · have hR := udReal_rUd hS pkSeedDist W hw
    have hI := udIdeal_rUd hS pkSeedDist W hw
    have hadv : 𝒟[SM_DT_UD_Experiment .real (rUd pkSeedDist W)] {true} ≤
        𝒟[SM_DT_UD_Experiment .ideal (rUd pkSeedDist W)] {true} +
          SM_DT_UD_Advantage (rUd pkSeedDist W) :=
      MeasureTheory.Measure.apply_true_le_add_boolDist _ _
    generalize 𝒟[SM_DT_UD_Experiment .real (rUd pkSeedDist W)] {true} = R at hR hadv
    have hfin : ((vp.params.w - 2 : ℕ) : ℝ≥0∞) *
        𝒟[SM_DT_UD_Experiment .ideal (rUd pkSeedDist W)] {true} ≠ ⊤ :=
      ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (MeasureTheory.measure_ne_top _ _)
    generalize 𝒟[SM_DT_UD_Experiment .ideal (rUd pkSeedDist W)] {true} = I at hI hadv hfin
    generalize SM_DT_UD_Advantage (rUd pkSeedDist W) = adv at hadv
    generalize hp : (fun k => prTrue (WotsGame.hyb pkSeedDist (wotsInsts vp) k W)) = p
    have hp' : ∀ k, prTrue (WotsGame.hyb pkSeedDist (wotsInsts vp) k W) = p k :=
      fun k => congrFun hp k
    simp only [hp'] at hR hI ⊢
    generalize vp.params.w - 2 = n at hR hI hfin ⊢
    have tel : p 0 + ∑ k ∈ Finset.range n, p (k + 1) = ∑ k ∈ Finset.range n, p k + p n := by
      rw [← Finset.sum_range_succ, Finset.sum_range_succ', add_comm]
    rw [← hI, ← hR] at tel
    have h1 : (n : ℝ≥0∞) * I + p 0 ≤ (n : ℝ≥0∞) * I + (p n + (n : ℝ≥0∞) * adv) := by
      calc (n : ℝ≥0∞) * I + p 0 = (n : ℝ≥0∞) * R + p n := by rw [add_comm, tel]
        _ ≤ (n : ℝ≥0∞) * (I + adv) + p n := by gcongr
        _ = (n : ℝ≥0∞) * I + (p n + (n : ℝ≥0∞) * adv) := by rw [mul_add, add_assoc, add_comm (p n)]
    exact (ENNReal.add_le_add_iff_left hfin).mp h1
  · have h0 : vp.params.w - 2 = 0 := by omega
    rw [h0]
    exact le_self_add

end Reduction

#print axioms Reduction.udReal_rUd
#print axioms Reduction.udIdeal_rUd
#print axioms Reduction.stepWotsUD
