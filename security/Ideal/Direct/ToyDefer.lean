import Ideal.Direct.ToySwap

/-!
# The toy game: the deferred game and the coupling

The **deferred game** `G2P` runs the adversary against two lazy tables: the table `g0`
(`hS`) and the honest-value table `s` (`sS`).  A compression query at the honest cell of a
*revealed* position of a chain is answered from `s`; every other compression query (in
particular one at an honest cell of a hidden position) goes to `g0`.  A reveal reads `s`.  So
hidden honest values are never sampled while they are hidden; the secret is drawn only at the
very end.  The handler logs every `g0` cell it reads (`hl`) and every compression query of the
adversary (`fl`).  After the adversary, the deferred game evaluates the chain from the forged
value through the same routing (`walkX`), completes `s` (`compS`), draws the secret, and outputs
the event `Efin`:

* a query of the adversary at a chain block whose input equals the honest value there
  (`isGF`: a guess of a hidden value, since at revealed positions the query is routed to `s`),
* a query of the adversary at the secret-keyed block of the secret (`isGK`),
* a logged `g0` cell at a chain block whose output equals the next honest value (`isHit`),
* the forged value equal to the honest value at its (hidden) position.

`realWin_le_G2` (the coupling): the real game is won with at most the probability of `Efin` in
the deferred game.  Proof: re-randomisation (`realWin_eq_Psi`); identical until bad between the
real handler at the table `Psi g0 s k` and the deferred handler at the tables `g0`, `s`
(`prEvent_le_untilBad`; they differ only at an honest cell of a hidden position, which is `isGF`
or `isGK` of the logged query); the winning chain from the forged value is caught by the
first-match walk (`walk_hit`); lazy = eager for the two tables of the deferred game.
-/

open OracleComp OracleSpec ENNReal MeasureTheory

set_option linter.unusedSectionVars false

namespace Ideal.Direct.Toy

/-- State of the deferred game's handler: lowest revealed positions, the `g0` cells read
(with their values), the adversary's compression queries. -/
structure GS (m : ℕ) (St Blk : Type) where
  r : Fin m → ℕ
  hl : List ((St × Blk) × St)
  fl : List (St × Blk)

namespace Params

variable {St Blk K Y : Type} (T : Params St Blk K Y)

/-- The honest-value table. -/
abbrev sS : OracleSpec T.HIdx := T.HIdx →ₒ St

/-- The tables of the deferred game. -/
abbrev spec2 := hS St Blk + T.sS

/-- Initial state. -/
def gs0 : GS T.m St Blk := ⟨T.r0, [], []⟩

/-- Log a compression query `q` answered `vb.1`; `vb.2` says whether it read `g0`. -/
def logH (gs : GS T.m St Blk) (q : St × Blk) (vb : St × Bool) : GS T.m St Blk :=
  if vb.2 then { gs with hl := (q, vb.1) :: gs.hl, fl := q :: gs.fl } else gs

/-- Query `g0`. -/
abbrev qG (q : St × Blk) : OracleComp (unifSpec + T.spec2) St :=
  liftM ((unifSpec + T.spec2).query (.inr (.inl q)))

/-- Query `s`. -/
abbrev qS (i : T.HIdx) : OracleComp (unifSpec + T.spec2) St :=
  liftM ((unifSpec + T.spec2).query (.inr (.inr i)))

variable [DecidableEq St]

/-- A chain-block query at a revealed position, with its chain, position and input. -/
def revPos (r : Fin T.m → ℕ) (q : St × Blk) : Option (Fin T.m × ℕ × Y) :=
  if q.1 = T.cv then
    match T.parse q.2 with
    | .chn a j x => if j < T.w ∧ r a ≤ j then some (a, j, x) else none
    | _ => none
  else none

variable [DecidableEq Y]

/-- The routing of one compression query: at a revealed position, compare the input with the
honest value; if equal, answer the next honest value, else read `g0`; elsewhere read `g0`.
The flag says whether `g0` was read. -/
def core (r : Fin T.m → ℕ) (q : St × Blk) : OracleComp (unifSpec + T.spec2) (St × Bool) :=
  match T.revPos r q with
  | some (a, j, x) => do
      let u ← T.qS (a, T.ix j)
      if T.out u = x then (fun u' => (u', false)) <$> T.qS (a, T.ix (j + 1))
      else (fun v => (v, true)) <$> T.qG q
  | none => (fun v => (v, true)) <$> T.qG q

/-- The deferred game's handler. -/
def H2 : QueryImpl T.advSpec (StateT (GS T.m St Blk) (OracleComp (unifSpec + T.spec2))) := fun
  | .inl n => StateT.mk fun gs =>
      (fun u => (u, gs)) <$> (liftM ((unifSpec + T.spec2).query (.inl n)) :
        OracleComp (unifSpec + T.spec2) (Fin (n + 1)))
  | .inr (.inl q) => StateT.mk fun gs => (fun vb => (vb.1, T.logH gs q vb)) <$> T.core gs.r q
  | .inr (.inr ab) => StateT.mk fun gs =>
      (fun u => (T.out u, { gs with r := T.rUpd gs.r ab.1 ab.2 })) <$> T.qS (ab.1, T.ix (T.cl ab.2))

/-- The chain from `x` at position `j`, `n` steps, through the deferred routing; returns the
end value and the `g0` cells read. -/
def walkX (r : Fin T.m → ℕ) (a : Fin T.m) :
    ℕ → ℕ → Y → OracleComp (unifSpec + T.spec2) (Y × List ((St × Blk) × St))
  | _, 0, x => pure (x, [])
  | j, n + 1, x => do
      let vb ← T.core r (T.cv, T.F a j x)
      let z ← walkX r a (j + 1) n (T.out vb.1)
      pure (z.1, if vb.2 then ((T.cv, T.F a j x), vb.1) :: z.2 else z.2)

variable [Fintype St] [Fintype Blk]

/-- Complete the honest-value table. -/
noncomputable def compS : OracleComp (unifSpec + T.spec2) (T.HIdx → St) :=
  (Finset.univ : Finset T.HIdx).toList.foldlM
    (fun f i => (fun u => Function.update f i u) <$> T.qS i) (fun _ => T.cv)

/-- A query at a chain block whose input is the honest value there. -/
def isGF (sv : T.HIdx → St) (q : St × Blk) : Prop :=
  q.1 = T.cv ∧ ∃ a j x, T.parse q.2 = .chn a j x ∧ j < T.w ∧ x = T.out (sv (a, T.ix j))

/-- A query at the secret-keyed block of the secret. -/
def isGK (k : K) (q : St × Blk) : Prop :=
  q.1 = T.cv ∧ ∃ a, T.parse q.2 = .key a k

/-- A `g0` cell at a chain block whose output is the next honest value. -/
def isHit (sv : T.HIdx → St) (e : (St × Blk) × St) : Prop :=
  e.1.1 = T.cv ∧ ∃ a j x, T.parse e.1.2 = .chn a j x ∧ j < T.w ∧
    T.out e.2 = T.out (sv (a, T.ix (j + 1)))

/-- The final event of the deferred game. -/
def Efin (o : Fin T.m × ℕ × Y) (gs : GS T.m St Blk) (wl : List ((St × Blk) × St)) (k : K)
    (sv : T.HIdx → St) : Prop :=
  (∃ q ∈ gs.fl, T.isGF sv q) ∨ (∃ q ∈ gs.fl, T.isGK k q) ∨ (∃ e ∈ gs.hl ++ wl, T.isHit sv e) ∨
    (o.2.1 < gs.r o.1 ∧ o.2.2 = T.out (sv (o.1, T.ix o.2.1)))

variable [SampleableType K]

open Classical in
/-- **The deferred game.** -/
noncomputable def G2P (A : OracleComp T.advSpec (Fin T.m × ℕ × Y)) :
    OracleComp (unifSpec + T.spec2) Bool := do
  let z ← (simulateQ T.H2 A).run T.gs0
  let wv ← T.walkX z.2.r z.1.1 z.1.2.1 (T.w - z.1.2.1) z.1.2.2
  let sv ← T.compS
  let k ← (liftM ($ᵗ K : ProbComp K) : OracleComp (unifSpec + T.spec2) K)
  pure (decide (T.Efin z.1 z.2 wv.2 k sv))

/-! ## The deferred game at fixed tables -/

/-- The two tables as one answer function. -/
def tbl2 (g0 : CF St Blk) (s : T.HIdx → St) : (t : (St × Blk) ⊕ T.HIdx) → T.spec2.Range t
  | .inl q => g0 q
  | .inr i => s i

/-- The routing at fixed tables. -/
def coreV (g0 : CF St Blk) (s : T.HIdx → St) (r : Fin T.m → ℕ) (q : St × Blk) : St × Bool :=
  match T.revPos r q with
  | some (a, j, x) => if T.out (s (a, T.ix j)) = x then (s (a, T.ix (j + 1)), false) else (g0 q, true)
  | none => (g0 q, true)

/-- The deferred walk at fixed tables. -/
def walkO2 (g0 : CF St Blk) (s : T.HIdx → St) (r : Fin T.m → ℕ) (a : Fin T.m) :
    ℕ → ℕ → Y → Y × List ((St × Blk) × St)
  | _, 0, x => (x, [])
  | j, n + 1, x =>
      let vb := T.coreV g0 s r (T.cv, T.F a j x)
      let z := walkO2 g0 s r a (j + 1) n (T.out vb.1)
      (z.1, if vb.2 then ((T.cv, T.F a j x), vb.1) :: z.2 else z.2)

/-- The deferred handler at fixed tables. -/
def O2H (g0 : CF St Blk) (s : T.HIdx → St) :
    QueryImpl T.advSpec (StateT (GS T.m St Blk) ProbComp) := fun
  | .inl n => StateT.mk fun gs => (fun u => (u, gs)) <$> (unifSpec.query n : ProbComp (Fin (n + 1)))
  | .inr (.inl q) => StateT.mk fun gs =>
      pure ((T.coreV g0 s gs.r q).1, T.logH gs q (T.coreV g0 s gs.r q))
  | .inr (.inr ab) => StateT.mk fun gs =>
      pure (T.out (s (ab.1, T.ix (T.cl ab.2))), { gs with r := T.rUpd gs.r ab.1 ab.2 })

theorem ans_core (g0 : CF St Blk) (s : T.HIdx → St) (r : Fin T.m → ℕ) (q : St × Blk) :
    simulateQ (HP.ansImpl (T.tbl2 g0 s)) (T.core r q) = pure (T.coreV g0 s r q) := by
  unfold core coreV
  rcases T.revPos r q with _ | ⟨a, j, x⟩
  · simp only [simulateQ_map, ans_query (spec := T.spec2), map_pure]; rfl
  · simp only [simulateQ_bind, ans_query (spec := T.spec2), pure_bind]
    by_cases h : T.out (s (a, T.ix j)) = x
    · simp only [tbl2, h, if_true, simulateQ_map, ans_query (spec := T.spec2), map_pure]
    · simp only [tbl2, h, if_false, simulateQ_map, ans_query (spec := T.spec2), map_pure]

theorem ans_walkX (g0 : CF St Blk) (s : T.HIdx → St) (r : Fin T.m → ℕ) (a : Fin T.m) (n : ℕ) :
    ∀ j x, simulateQ (HP.ansImpl (T.tbl2 g0 s)) (T.walkX r a j n x) =
      pure (T.walkO2 g0 s r a j n x) := by
  induction n with
  | zero => intro j x; simp [walkX, walkO2]
  | succ n ih =>
    intro j x
    simp only [walkX, walkO2, simulateQ_bind, ans_core, pure_bind, ih, simulateQ_pure]

theorem foldl_update_apply (s f : T.HIdx → St) (l : List T.HIdx) (i : T.HIdx) :
    (l.foldl (fun f i => Function.update f i (s i)) f) i = if i ∈ l then s i else f i := by
  induction l generalizing f with
  | nil => simp
  | cons j l ih =>
    rw [List.foldl_cons, ih]
    by_cases hi : i ∈ l
    · simp [hi]
    · by_cases hij : i = j
      · subst hij; simp [hi]
      · simp [hi, hij]

theorem ans_compS (g0 : CF St Blk) (s : T.HIdx → St) :
    simulateQ (HP.ansImpl (T.tbl2 g0 s)) T.compS = pure s := by
  have hgen : ∀ (l : List T.HIdx) (f : T.HIdx → St),
      simulateQ (HP.ansImpl (T.tbl2 g0 s))
        (l.foldlM (fun f i => (fun u => Function.update f i u) <$> T.qS i) f) =
        pure (l.foldl (fun f i => Function.update f i (s i)) f) := by
    intro l
    induction l with
    | nil => intro f; simp
    | cons j l ih =>
      intro f
      simp only [List.foldlM_cons, List.foldl_cons, simulateQ_bind, simulateQ_map,
        ans_query (spec := T.spec2), map_pure, pure_bind, ih]
      rfl
  unfold compS
  rw [hgen]
  congr 1
  funext i
  rw [foldl_update_apply]
  simp

theorem ans_H2_run (g0 : CF St Blk) (s : T.HIdx → St) {α : Type} (oa : OracleComp T.advSpec α)
    (gs : GS T.m St Blk) :
    simulateQ (HP.ansImpl (T.tbl2 g0 s)) ((simulateQ T.H2 oa).run gs) =
      (simulateQ (T.O2H g0 s) oa).run gs := by
  refine simulateQ_StateT_compose _ _ _ (fun t gs => ?_) oa gs
  rcases t with n | q | ab
  · simp [H2, O2H, unifFwdAnswerImpl]
  · simp only [H2, O2H, StateT.run_mk, simulateQ_map, ans_core, map_pure]
  · simp only [H2, O2H, StateT.run_mk, simulateQ_map, ans_query (spec := T.spec2), map_pure]
    rfl

open Classical in
theorem ans_G2P (g0 : CF St Blk) (s : T.HIdx → St) (A : OracleComp T.advSpec (Fin T.m × ℕ × Y)) :
    simulateQ (HP.ansImpl (T.tbl2 g0 s)) (T.G2P A) =
      (simulateQ (T.O2H g0 s) A).run T.gs0 >>= fun z => ($ᵗ K : ProbComp K) >>= fun k =>
        pure (decide (T.Efin z.1 z.2
          (T.walkO2 g0 s z.2.r z.1.1 z.1.2.1 (T.w - z.1.2.1) z.1.2.2).2 k s)) := by
  unfold G2P
  simp only [simulateQ_bind, ans_H2_run, ans_walkX, ans_compS, pure_bind,
    HP.simulateQ_ansImpl_liftM, simulateQ_pure]

variable [DecidableEq Blk] [SampleableType St]

/-- The pair of tables as one dependent table. -/
def tbl2Equiv : CF St Blk × (T.HIdx → St) ≃ ((t : (St × Blk) ⊕ T.HIdx) → T.spec2.Range t) where
  toFun p := T.tbl2 p.1 p.2
  invFun F := (fun q => F (.inl q), fun i => F (.inr i))
  left_inv p := rfl
  right_inv F := by funext t; rcases t with q | i <;> rfl

open Classical in
/-- **Lazy = eager for the deferred game.** -/
theorem G2_eq_eager (A : OracleComp T.advSpec (Fin T.m × ℕ × Y)) :
    HP.prT ((simulateQ T.spec2.romImpl (T.G2P A)).run' ∅) =
      HP.prT (($ᵗ (CF St Blk) : ProbComp (CF St Blk)) >>= fun g0 =>
        ($ᵗ (T.HIdx → St) : ProbComp (T.HIdx → St)) >>= fun s =>
          (simulateQ (T.O2H g0 s) A).run T.gs0 >>= fun z => ($ᵗ K : ProbComp K) >>= fun k =>
            pure (decide (T.Efin z.1 z.2
              (T.walkO2 g0 s z.2.r z.1.1 z.1.2.1 (T.w - z.1.2.1) z.1.2.2).2 k s))) := by
  refine HP.prT_congr ?_
  let : SampleableType ((t : (St × Blk) ⊕ T.HIdx) → T.spec2.Range t) :=
    SampleableType.ofEquiv T.tbl2Equiv
  rw [OracleComp.evalDist_simulateQ_romImpl_run'_eq_completeTable]
  have hdraw : ∀ k : ((t : (St × Blk) ⊕ T.HIdx) → T.spec2.Range t) → ProbComp Bool,
      ($ᵗ ((t : (St × Blk) ⊕ T.HIdx) → T.spec2.Range t) >>= k) =
        $ᵗ (CF St Blk) >>= fun g => $ᵗ (T.HIdx → St) >>= fun s => k (T.tbl2 g s) := by
    intro k
    change (T.tbl2Equiv <$> ((·, ·) <$> ($ᵗ (CF St Blk)) <*> ($ᵗ (T.HIdx → St)))) >>= k = _
    simp only [seq_eq_bind_map, map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp]
    rfl
  rw [hdraw]
  refine congrArg _ (bind_congr fun g => bind_congr fun s => ?_)
  rw [OracleComp.completeTable_empty]
  exact T.ans_G2P g s A

/-! ## Identical until a hidden honest cell is queried -/

variable [DecidableEq K]

/-- The adversary has queried an honest cell of a hidden position. -/
def badE (s : T.HIdx → St) (k : K) (gs : GS T.m St Blk) : Prop :=
  ∃ q ∈ gs.fl, T.isGF s q ∨ T.isGK k q

theorem logH_r (gs : GS T.m St Blk) (q : St × Blk) (vb : St × Bool) : (T.logH gs q vb).r = gs.r := by
  unfold logH; split_ifs <;> rfl

theorem fl_subset_logH (gs : GS T.m St Blk) (q : St × Blk) (vb : St × Bool) :
    ∀ q' ∈ gs.fl, q' ∈ (T.logH gs q vb).fl := by
  intro q' hq'
  unfold logH; split_ifs
  · exact List.mem_cons_of_mem _ hq'
  · exact hq'

/-- At fixed tables the deferred routing agrees with `Psi`, except at an honest cell of a hidden
position, where the query is logged and is `isGF` or `isGK`. -/
theorem coreV_eq_Psi (g0 : CF St Blk) (s : T.HIdx → St) (k : K) (r : Fin T.m → ℕ)
    (q : St × Blk) :
    (T.coreV g0 s r q).1 = T.Psi g0 s k q ∨
      ((T.coreV g0 s r q).2 = true ∧ (T.isGF s q ∨ T.isGK k q)) := by
  obtain ⟨c, b⟩ := q
  by_cases hc : c = T.cv
  · subst hc
    rcases hp : T.parse b with ⟨a, k'⟩ | ⟨a, j, x⟩ | _
    · have hrev : T.revPos r (T.cv, b) = none := by simp [revPos, hp]
      by_cases hk : k' = k
      · subst hk
        exact .inr ⟨by simp [coreV, hrev], .inr ⟨rfl, a, hp⟩⟩
      · exact .inl (by simp [coreV, hrev, Psi, hp, hk])
    · by_cases hrv : j < T.w ∧ r a ≤ j
      · have hrev : T.revPos r (T.cv, b) = some (a, j, x) := by simp [revPos, hp, hrv]
        left
        by_cases hx : T.out (s (a, T.ix j)) = x
        · simp [coreV, hrev, hx, Psi, hp, hrv.1]
        · simp [coreV, hrev, hx, Psi, hp, Ne.symm hx]
      · have hrev : T.revPos r (T.cv, b) = none := by simp [revPos, hp, hrv]
        by_cases hjx : j < T.w ∧ x = T.out (s (a, T.ix j))
        · exact .inr ⟨by simp [coreV, hrev], .inl ⟨rfl, a, j, x, hp, hjx.1, hjx.2⟩⟩
        · exact .inl (by simp [coreV, hrev, Psi, hp, hjx])
    · have hrev : T.revPos r (T.cv, b) = none := by simp [revPos, hp]
      exact .inl (by simp [coreV, hrev, Psi, hp])
  · have hrev : T.revPos r (c, b) = none := by simp [revPos, hc]
    exact .inl (by simp [coreV, hrev, Psi, hc])

theorem untilBad_agree (g0 : CF St Blk) (s : T.HIdx → St) (k : K) (t : T.advSpec.Domain)
    (gs : GS T.m St Blk) :
    (∀ z ∈ support ((T.O2H g0 s t).run gs), T.badE s k z.2) ∨
      (fun z => (z.1, z.2.r)) <$> (T.O2H g0 s t).run gs =
        (T.realE (T.Psi g0 s k) k t).run gs.r := by
  rcases t with n | q | ab
  · right; simp [O2H, realE]
  · rcases T.coreV_eq_Psi g0 s k gs.r q with h | ⟨hflag, hbad⟩
    · right
      simp only [O2H, realE, StateT.run_mk, map_pure, h, logH_r]
    · left
      intro z hz
      simp only [O2H, StateT.run_mk, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      refine ⟨q, ?_, hbad⟩
      simp [logH, hflag]
  · right
    simp only [O2H, realE, StateT.run_mk, map_pure]
    rw [T.sH_Psi g0 s k ab.1 (T.cl ab.2) (by simp [cl])]

theorem badE_mono (g0 : CF St Blk) (s : T.HIdx → St) (k : K) (t : T.advSpec.Domain)
    (gs : GS T.m St Blk) (hb : T.badE s k gs) :
    ∀ z ∈ support ((T.O2H g0 s t).run gs), T.badE s k z.2 := by
  obtain ⟨q', hq', hb⟩ := hb
  intro z hz
  rcases t with n | q | ab
  · simp only [O2H, StateT.run_mk, support_map] at hz
    obtain ⟨u, -, rfl⟩ := hz
    exact ⟨q', hq', hb⟩
  · simp only [O2H, StateT.run_mk, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨q', T.fl_subset_logH _ _ _ q' hq', hb⟩
  · simp only [O2H, StateT.run_mk, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨q', hq', hb⟩

/-! ## The first-match walk -/

/-- **First-match walk.**  If the chain from `x` at position `j` reaches the honest value at
`j + n` at the table `Psi g0 s k`, then `x` is the honest value at `j`, or the deferred walk read
a `g0` cell whose output is the next honest value. -/
theorem walk_hit (g0 : CF St Blk) (s : T.HIdx → St) (k : K) (r : Fin T.m → ℕ) (a : Fin T.m)
    (n : ℕ) : ∀ j x, j + n ≤ T.w →
      T.walkV (T.Psi g0 s k) a j n x = T.out (s (a, T.ix (j + n))) →
      x = T.out (s (a, T.ix j)) ∨ ∃ e ∈ (T.walkO2 g0 s r a j n x).2, T.isHit s e := by
  induction n with
  | zero => intro j x _ h; exact .inl (by simpa [walkV] using h)
  | succ n ih =>
    intro j x hjn h
    by_cases hx : x = T.out (s (a, T.ix j))
    · exact .inl hx
    · right
      have hj : j < T.w := by omega
      have hPsi : T.Psi g0 s k (T.cv, T.F a j x) = g0 (T.cv, T.F a j x) := by
        simp [Psi, T.parse_F, hx]
      have hcore : T.coreV g0 s r (T.cv, T.F a j x) = (g0 (T.cv, T.F a j x), true) := by
        unfold coreV
        by_cases hrv : j < T.w ∧ r a ≤ j
        · have hrev : T.revPos r (T.cv, T.F a j x) = some (a, j, x) := by
            simp [revPos, T.parse_F, hrv]
          simp [hrev, Ne.symm hx]
        · have hrev : T.revPos r (T.cv, T.F a j x) = none := by simp [revPos, T.parse_F, hrv]
          simp [hrev]
      rw [walkV, hPsi] at h
      rw [walkO2, hcore]
      simp only [if_true, List.mem_cons]
      rcases ih (j + 1) _ (by omega) (by rw [h, show j + 1 + n = j + (n + 1) by omega])
        with h1 | ⟨e, he, hhit⟩
      · exact ⟨_, .inl rfl, rfl, a, j, x, T.parse_F a j x, hj, h1⟩
      · exact ⟨e, .inr he, hhit⟩

/-! ## The coupling -/

open Classical in
/-- **Coupling.**  The real game is won with at most the probability of the deferred game's
final event. -/
theorem realWin_le_G2 (A : OracleComp T.advSpec (Fin T.m × ℕ × Y)) :
    T.realWin A ≤ HP.prT ((simulateQ T.spec2.romImpl (T.G2P A)).run' ∅) := by
  rw [realWin_eq_Psi, G2_eq_eager, HP.prT_swap]
  refine HP.prT_bind_mono _ _ _ fun g0 _ => ?_
  rw [HP.prT_swap]
  refine HP.prT_bind_mono _ _ _ fun s _ => ?_
  rw [HP.prT_swap]
  refine HP.prT_bind_mono _ _ _ fun k _ => ?_
  unfold realEG
  rw [HP.prT_bind_pure]
  have h1 := prEvent_le_untilBad (T.realE (T.Psi g0 s k) k) (T.O2H g0 s) GS.r (T.badE s k)
    (fun t gs hb => T.badE_mono g0 s k t gs hb) (fun t gs _ => T.untilBad_agree g0 s k t gs)
    (fun z => T.winE (T.Psi g0 s k) k z) A T.gs0
  refine (le_of_eq ?_).trans (h1.trans ?_)
  · simp only [decide_eq_true_eq]; rfl
  · rw [HP.prT_bind_pure]
    simp only [decide_eq_true_eq]
    refine prEvent_mono _ _ _ fun z hz => ?_
    rcases hz with ⟨hlt, hwalk⟩ | ⟨q, hq, hb | hb⟩
    · rw [T.sH_Psi g0 s k _ _ le_rfl] at hwalk
      by_cases hjw : z.1.2.1 ≤ T.w
      · rcases T.walk_hit g0 s k z.2.r z.1.1 (T.w - z.1.2.1) z.1.2.1 z.1.2.2 (by omega)
            (by rw [hwalk, show z.1.2.1 + (T.w - z.1.2.1) = T.w by omega]) with h | ⟨e, he, hhit⟩
        · exact .inr (.inr (.inr ⟨hlt, h⟩))
        · exact .inr (.inr (.inl ⟨e, List.mem_append_right _ he, hhit⟩))
      · have h0 : T.w - z.1.2.1 = 0 := by omega
        rw [h0, walkV] at hwalk
        have hix : T.ix z.1.2.1 = T.ix T.w := by ext; simp [ix]; omega
        exact .inr (.inr (.inr ⟨hlt, by rw [hix]; exact hwalk⟩))
    · exact .inl ⟨q, hq, hb⟩
    · exact .inr (.inl ⟨q, hq, hb⟩)

end Params

end Ideal.Direct.Toy

#print axioms Ideal.Direct.Toy.Params.G2_eq_eager
#print axioms Ideal.Direct.Toy.Params.walk_hit
#print axioms Ideal.Direct.Toy.Params.realWin_le_G2
