import Ideal.Direct.ToyDefs

/-!
# The toy game: the real game over an eager table, and the re-randomisation of honest cells

* `realE g k`, `realEG g k A`: the real game at a fixed table `g` and secret `k`;
  `realWin_eq_eager`: the lazy game equals the average of `realEG` over a uniform table.
* `Psi g0 s k`: the table `g0` with every honest cell replaced by the corresponding entry of an
  independent table `s` of honest values (cell `(cv, P a k)` gets `s (a, 0)`, cell
  `(cv, F a j (out (s (a, j))))` gets `s (a, j + 1)`).  Its honest chain values are exactly
  `out ∘ s` (`sH_Psi`).
* `reRand k`: `(g0, s) ↦ (Psi g0 s k, g0 at the honest cells)` is a bijection
  (`reRand_bijective`), so `Psi g0 s k` is a uniform table when `g0` and `s` are
  (`realWin_eq_Psi`).  This is the deferral tool: in the `Psi` form the honest values are
  i.i.d. uniform and independent of `g0`, whatever the order in which they are revealed.
-/

open OracleComp OracleSpec ENNReal MeasureTheory

set_option linter.unusedSectionVars false

namespace Ideal.Direct.Toy

namespace Params

variable {St Blk K Y : Type} (T : Params St Blk K Y)

/-! ## Eager evaluation -/

/-- The honest chain's full chaining values at a fixed table. -/
def sH (g : CF St Blk) (k : K) (a : Fin T.m) : ℕ → St
  | 0 => g (T.cv, T.P a k)
  | j + 1 => g (T.cv, T.F a j (T.out (sH g k a j)))

/-- The chain from `x` at position `j`, `n` steps, at a fixed table. -/
def walkV (g : CF St Blk) (a : Fin T.m) : ℕ → ℕ → Y → Y
  | _, 0, x => x
  | j, n + 1, x => walkV g a (j + 1) n (T.out (g (T.cv, T.F a j x)))

/-- The real game's handler at a fixed table. -/
def realE (g : CF St Blk) (k : K) : QueryImpl T.advSpec (StateT (Fin T.m → ℕ) ProbComp) := fun
  | .inl n => StateT.mk fun r => (fun u => (u, r)) <$> (unifSpec.query n : ProbComp (Fin (n + 1)))
  | .inr (.inl q) => StateT.mk fun r => pure (g q, r)
  | .inr (.inr ab) => StateT.mk fun r =>
      pure (T.out (T.sH g k ab.1 (T.cl ab.2)), T.rUpd r ab.1 ab.2)

variable [DecidableEq Y]

/-- The winning condition at a fixed table. -/
abbrev winE (g : CF St Blk) (k : K) (z : (Fin T.m × ℕ × Y) × (Fin T.m → ℕ)) : Prop :=
  z.1.2.1 < z.2 z.1.1 ∧ T.walkV g z.1.1 z.1.2.1 (T.w - z.1.2.1) z.1.2.2 = T.out (T.sH g k z.1.1 T.w)

/-- The real game at a fixed table and secret. -/
def realEG (g : CF St Blk) (k : K) (A : OracleComp T.advSpec (Fin T.m × ℕ × Y)) :
    ProbComp Bool := do
  let z ← (simulateQ (T.realE g k) A).run T.r0
  pure (decide (T.winE g k z))

omit [DecidableEq Y] in
theorem ans_query {ι : Type} {spec : OracleSpec ι} (a : (t : ι) → spec.Range t) (t : ι) :
    simulateQ (HP.ansImpl a) (liftM ((unifSpec + spec).query (.inr t)) :
      OracleComp (unifSpec + spec) (spec.Range t)) = pure (a t) := by
  simpa using HP.simulateQ_ansImpl_inr_bind a t pure

theorem ans_chainQ (g : CF St Blk) (k : K) (a : Fin T.m) (j : ℕ) :
    simulateQ (HP.ansImpl (spec := hS St Blk) g) (T.chainQ k a j) = pure (T.sH g k a j) := by
  induction j with
  | zero => exact ans_query (spec := hS St Blk) g _
  | succ j ih =>
    simp only [chainQ, sH, simulateQ_bind, ih, pure_bind]
    exact ans_query (spec := hS St Blk) g _

theorem ans_walkQ (g : CF St Blk) (a : Fin T.m) (n : ℕ) :
    ∀ j x, simulateQ (HP.ansImpl (spec := hS St Blk) g) (T.walkQ a j n x) =
      pure (T.walkV g a j n x) := by
  induction n with
  | zero => intro j x; simp [walkQ, walkV]
  | succ n ih =>
    intro j x
    simp only [walkQ, walkV, simulateQ_bind]
    rw [ans_query (spec := hS St Blk) g, pure_bind, ih]

theorem ans_realImpl_run (g : CF St Blk) (k : K) {α : Type} (oa : OracleComp T.advSpec α)
    (r : Fin T.m → ℕ) :
    simulateQ (HP.ansImpl (spec := hS St Blk) g) ((simulateQ (T.realImpl k) oa).run r) =
      (simulateQ (T.realE g k) oa).run r := by
  refine simulateQ_StateT_compose _ _ _ (fun t s => ?_) oa r
  rcases t with n | q | ab
  · simp [realImpl, realE, unifFwdAnswerImpl]
  · simp only [realImpl, realE, StateT.run_mk, simulateQ_map, ans_query (spec := hS St Blk) g,
      map_pure]
  · simp only [realImpl, realE, StateT.run_mk, simulateQ_map, ans_chainQ, map_pure]

variable [SampleableType K]

theorem ans_realProg (g : CF St Blk) (A : OracleComp T.advSpec (Fin T.m × ℕ × Y)) :
    simulateQ (HP.ansImpl (spec := hS St Blk) g) (T.realProg A) =
      ($ᵗ K : ProbComp K) >>= fun k => T.realEG g k A := by
  unfold realProg realEG
  simp only [simulateQ_bind, HP.simulateQ_ansImpl_liftM]
  refine bind_congr fun k => ?_
  rw [ans_realImpl_run]
  refine bind_congr fun z => ?_
  simp only [ans_walkQ, ans_chainQ, pure_bind, simulateQ_pure]

variable [DecidableEq St] [DecidableEq Blk] [SampleableType St] [Fintype St] [Fintype Blk]

/-- **The lazy game is the eager game.** -/
theorem realWin_eq_eager (A : OracleComp T.advSpec (Fin T.m × ℕ × Y)) :
    T.realWin A = HP.prT (($ᵗ (CF St Blk) : ProbComp (CF St Blk)) >>= fun g =>
      ($ᵗ K : ProbComp K) >>= fun k => T.realEG g k A) := by
  unfold realWin
  refine HP.prT_congr ?_
  let : SampleableType ((t : St × Blk) → (hS St Blk).Range t) :=
    inferInstanceAs (SampleableType (CF St Blk))
  rw [OracleComp.evalDist_simulateQ_romImpl_run'_eq_completeTable]
  refine congrArg _ (bind_congr fun g => ?_)
  rw [OracleComp.completeTable_empty]
  exact ans_realProg T g A

/-! ## Re-randomising the honest cells -/

variable [DecidableEq K]

/-- The table `g0` with its honest cells replaced by the honest-value table `s`. -/
def Psi (g0 : CF St Blk) (s : T.HIdx → St) (k : K) : CF St Blk := fun q =>
  if q.1 = T.cv then
    match T.parse q.2 with
    | .key a k' => if k' = k then s (a, T.ix 0) else g0 q
    | .chn a j x => if j < T.w ∧ x = T.out (s (a, T.ix j)) then s (a, T.ix (j + 1)) else g0 q
    | .other => g0 q
  else g0 q

theorem ix_val {j : ℕ} (hj : j ≤ T.w) : (T.ix j).val = j := by
  simp [ix, Nat.min_eq_left hj]

theorem sH_Psi (g0 : CF St Blk) (s : T.HIdx → St) (k : K) (a : Fin T.m) :
    ∀ j ≤ T.w, T.sH (T.Psi g0 s k) k a j = s (a, T.ix j) := by
  intro j
  induction j with
  | zero => intro _; simp [sH, Psi, T.parse_P]
  | succ j ih =>
    intro hj
    have hj' : j < T.w := by omega
    rw [sH, ih (by omega)]
    simp [Psi, T.parse_F, hj']

/-- The honest cell of index `i`. -/
def pos (s : T.HIdx → St) (k : K) (i : T.HIdx) : St × Blk :=
  if i.2.val = 0 then (T.cv, T.P i.1 k)
  else (T.cv, T.F i.1 (i.2.val - 1) (T.out (s (i.1, T.ix (i.2.val - 1)))))

theorem ix_eq_of_val {i : Fin (T.w + 1)} {j : ℕ} (h : i.val = j) : T.ix j = i := by
  ext; rw [ix_val T (by omega)]; exact h.symm

theorem Psi_pos (g0 : CF St Blk) (s : T.HIdx → St) (k : K) (i : T.HIdx) :
    T.Psi g0 s k (T.pos s k i) = s i := by
  obtain ⟨a, j⟩ := i
  by_cases hj : j.val = 0
  · simp only [pos, hj, if_true, Psi, T.parse_P]
    simp [T.ix_eq_of_val hj]
  · have hw : j.val - 1 < T.w := by omega
    simp only [pos, hj, if_false, Psi, T.parse_F, if_true, hw, true_and]
    rw [T.ix_eq_of_val (show j.val = j.val - 1 + 1 by omega)]

theorem Psi_of_ne (g0 : CF St Blk) (s : T.HIdx → St) (k : K) (q : St × Blk)
    (hq : ∀ i, T.pos s k i ≠ q) : T.Psi g0 s k q = g0 q := by
  obtain ⟨c, b⟩ := q
  unfold Psi
  by_cases hc : c = T.cv
  · subst hc
    simp only [if_true]
    split
    · rename_i a k' hb
      by_cases hk : k' = k
      · subst hk
        exact absurd (by rw [(T.parse_key _ _ _).1 hb]; simp [pos]) (hq (a, ⟨0, by omega⟩))
      · simp [hk]
    · rename_i a j x hb
      by_cases hjx : j < T.w ∧ x = T.out (s (a, T.ix j))
      · refine absurd ?_ (hq (a, ⟨j + 1, by omega⟩))
        obtain ⟨hj, hx⟩ := hjx
        subst hx
        rw [(T.parse_chn _ _ _ _).1 hb]
        simp [pos]
      · simp [hjx]
    · rfl
  · simp [hc]

/-- The re-randomisation map. -/
def reRand (k : K) (p : CF St Blk × (T.HIdx → St)) : CF St Blk × (T.HIdx → St) :=
  (T.Psi p.1 p.2 k, fun i => p.1 (T.pos p.2 k i))

theorem reRand_injective (k : K) : Function.Injective (T.reRand k) := by
  rintro ⟨g0, s⟩ ⟨g0', s'⟩ h
  simp only [reRand, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have hs : s = s' := by
    funext i
    obtain ⟨a, j⟩ := i
    have hj : j.val ≤ T.w := by omega
    have e1 := T.sH_Psi g0 s k a j.val hj
    have e2 := T.sH_Psi g0' s' k a j.val hj
    rw [T.ix_eq_of_val rfl] at e1 e2
    rw [← e1, ← e2, h1]
  subst hs
  refine Prod.ext ?_ rfl
  funext q
  by_cases hq : ∃ i, T.pos s k i = q
  · obtain ⟨i, rfl⟩ := hq
    exact congrFun h2 i
  · push Not at hq
    show g0 q = g0' q
    rw [← T.Psi_of_ne g0 s k q hq, ← T.Psi_of_ne g0' s k q hq, h1]

theorem reRand_bijective (k : K) : Function.Bijective (T.reRand k) :=
  Finite.injective_iff_bijective.mp (T.reRand_injective k)

/-- **Re-randomisation.**  The real game equals the game in which the table is `Psi g0 s k`
for independent uniform `g0` and `s`. -/
theorem realWin_eq_Psi (A : OracleComp T.advSpec (Fin T.m × ℕ × Y)) :
    T.realWin A = HP.prT (($ᵗ K : ProbComp K) >>= fun k =>
      ($ᵗ (CF St Blk) : ProbComp (CF St Blk)) >>= fun g0 =>
        ($ᵗ (T.HIdx → St) : ProbComp (T.HIdx → St)) >>= fun s =>
          T.realEG (T.Psi g0 s k) k A) := by
  rw [realWin_eq_eager, HP.prT_swap]
  refine HP.prT_bind_congr _ _ _ fun k _ => HP.prT_congr ?_
  have key := HP.evalDist_uniform_pair_bijective (V := CF St Blk) (T := T.HIdx → St) (α := Bool)
    ($ᵗ (CF St Blk)) ($ᵗ (T.HIdx → St))
    SampleableType.evalDist_uniformSample SampleableType.evalDist_uniformSample (T.reRand k)
    (T.reRand_bijective k) (fun p : CF St Blk × (T.HIdx → St) => T.realEG p.1 k A)
  simp only [reRand] at key
  rw [key]
  exact evalDist_bind_congr_of_support (β := Bool) _ _ _ fun g0 _ =>
    (OracleComp.evalDist_bind_const _ _).symm

end Params

end Ideal.Direct.Toy

#print axioms Ideal.Direct.Toy.Params.realWin_eq_eager
#print axioms Ideal.Direct.Toy.Params.realWin_eq_Psi
