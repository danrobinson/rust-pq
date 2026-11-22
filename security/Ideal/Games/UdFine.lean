import Ideal.Games.Ud
import Ideal.Core.ChainFine

/-!
# SM-UD in the ideal-compression model with finer accounting of the second phase

`ud_bound`'s term `q₂/|M'|` charges every compression query of the distinguisher's second phase.
Here the second phase may be given with chain queries (`pcS`, expanded by `expandImpl`), and only
its raw compression queries are charged, as soon as none of its chain queries starts with the
seed block (`freeC`): such a chain reads only public cells of the ideal game unless a public
value is `IV` or `cv` (`Core/ChainFine.lean`).  The price is an additive
`(2 q₂ + 2 (q₁ + qc)·max 1 L + 1)/|St|` (`PubBad` in phase one, in phase two, `cv = IV`) and, for a
set `bad` of public seeds of probability `≤ β` where the raw count is not claimed, `β·q₂/|M'|`.

* `prEvent_preSim_pubHit_le`: after the modified phase one `preSim`, a fixed value `w` is the
  value of a public cell with probability at most `(q₁ + qc)·max 1 L/|St|`;
* `prT_ud_phase2_le_fine`: the phase-two comparison of `prT_ud_phase2_le` with `qM/|M'|` for
  `q₂/|M'|`, from a cache that is not `PubBad`, `cv ≠ IV`;
* `ud_ideal_le_fine`, `ud_bound_fine`: the resulting bounds.

The hypotheses are on the ideal-model adversary only (its chain queries, its raw count); they say
nothing about what the queries ask.  A chain query whose first block IS the seed block is simply
not allowed by `freeC`; such a query can always be issued as raw queries instead (and is then
charged).
-/

open OracleComp OracleSpec ENNReal

namespace Ideal

open TweakableHash

variable {St Blk PkSeed Tweak M M' Y ι : Type} {F : THFam St Blk PkSeed Tweak M Y ι}

/-! ## Averaging an error that depends on the drawn value -/

section Avg

variable {α : Type}

theorem prT_bind_le_add_mul_all (mx : ProbComp α) (f g k : α → ProbComp Bool) (a b : ℝ≥0∞)
    (h : ∀ x, HP.prT (f x) ≤ HP.prT (g x) + a + b * HP.prT (k x)) :
    HP.prT (mx >>= f) ≤ HP.prT (mx >>= g) + a + b * HP.prT (mx >>= k) := by
  unfold HP.prT at h ⊢
  let : MeasurableSpace α := ⊤
  rw [prEvent_bind_eq_lintegral_of_discrete, prEvent_bind_eq_lintegral_of_discrete,
    prEvent_bind_eq_lintegral_of_discrete]
  calc ∫⁻ x, Pr{let y ← f x}[y = true] ∂𝒟[mx]
      ≤ ∫⁻ x, (Pr{let y ← g x}[y = true] + a + b * Pr{let y ← k x}[y = true]) ∂𝒟[mx] :=
        MeasureTheory.lintegral_mono h
    _ = ∫⁻ x, Pr{let y ← g x}[y = true] ∂𝒟[mx] + a * 𝒟[mx] Set.univ +
          b * ∫⁻ x, Pr{let y ← k x}[y = true] ∂𝒟[mx] := by
        rw [MeasureTheory.lintegral_add_right _ (measurable_from_top),
          MeasureTheory.lintegral_add_right _ measurable_const, MeasureTheory.lintegral_const,
          MeasureTheory.lintegral_const_mul _ measurable_from_top]
    _ ≤ _ := by
        gcongr
        exact mul_le_of_le_one_right' (evalDist_apply_univ_le_one mx)

/-- An additive error `a + b·prT (k x)` of the continuations survives a common draw, with
`prT (mx >>= k)` for `prT (k x)`. -/
theorem prT_bind_le_add_mul (mx : ProbComp α) (f g k : α → ProbComp Bool) (a b : ℝ≥0∞)
    (h : ∀ x ∈ support mx, HP.prT (f x) ≤ HP.prT (g x) + a + b * HP.prT (k x)) :
    HP.prT (mx >>= f) ≤ HP.prT (mx >>= g) + a + b * HP.prT (mx >>= k) := by
  rw [bind_eq_attach_bind mx f, bind_eq_attach_bind mx g, bind_eq_attach_bind mx k]
  exact prT_bind_le_add_mul_all _ _ _ _ a b fun x => h x.1 x.2

theorem prT_pure_decide (p : Prop) [Decidable p] :
    HP.prT (pure (decide p)) = if p then 1 else 0 := by
  rw [HP.prT_pure]
  by_cases h : p <;> simp [h]

end Avg

/-! ## Step bound with an admissibility condition -/

section StepOk

variable {ι₀ : Type} {spec : OracleSpec ι₀} {σ α : Type}

/-- `prEvent_bad_le_of_step` with the per-step bound required only at queries satisfying `ok`,
for a computation all of whose queries satisfy `ok`. -/
theorem prEvent_bad_le_of_step_ok (so : QueryImpl spec (StateT σ ProbComp)) (bad : σ → Prop)
    (p ok : ι₀ → Prop) [DecidablePred p] (ε : ℝ≥0∞)
    (hp : ∀ t s, ¬ bad s → p t → ok t → Pr{let z ← (so t).run s}[bad z.2] ≤ ε)
    (hnp : ∀ t s, ¬ bad s → ¬ p t → ∀ z ∈ support ((so t).run s), ¬ bad z.2)
    (oa : OracleComp spec α) (n : ℕ) (hn : IsQueryBoundP oa p n) (hok : AllQueriesSatisfy oa ok)
    (s : σ) (hs : ¬ bad s) :
    Pr{let z ← (simulateQ so oa).run s}[bad z.2] ≤ n * ε := by
  classical
  induction oa using OracleComp.inductionOn generalizing n s with
  | pure x =>
    simp only [simulateQ_pure, StateT.run_pure]
    rw [prEvent_pure]
    simp only [hs, ↓reduceIte]
    exact zero_le
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hn
    rw [allQueriesSatisfy_query_bind_iff] at hok
    rw [run_simulateQ_query_bind]
    by_cases hpt : p t
    · simp only [hpt, ↓reduceIte] at hn
      have hn0 : 0 < n := by simpa using hn.1
      refine (prEvent_bind_le_prEvent_add ((so t).run s)
        (fun us => (simulateQ so (k us.1)).run us.2) (fun us => bad us.2) (fun z => bad z.2)
        (ε := (n - 1 : ℕ) * ε) fun us hus => ih us.1 (n - 1) (hn.2 us.1) (hok.2 us.1) us.2
          hus).trans ?_
      refine (add_le_add_left (hp t s hs hpt hok.1) _).trans (le_of_eq ?_)
      obtain ⟨k', rfl⟩ : ∃ k', n = k' + 1 := ⟨n - 1, by omega⟩
      simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
      ring
    · simp only [hpt, ↓reduceIte] at hn
      exact prEvent_bind_le_of_forall_le_of_support _ _ _ fun us hus =>
        ih us.1 n (hn.2 us.1) (hok.2 us.1) us.2 (hnp t s hs hpt us hus)

end StepOk

section Lemmas

variable [DecidableEq St] [DecidableEq Blk] [SampleableType St] [Fintype St]

/-! ## Phase one: public values -/

/-- A fresh public step makes a fixed value `w` a public value with probability `≤ 1/|St|`. -/
theorem prEvent_randomOracle_pub_pubHit_le (w : St) (q : St × Blk) (s : Cache St Blk)
    (hs : ¬ PubHit w s) :
    Pr{let z ← ((hS St Blk + tS St Blk).randomOracle (.inl q)).run s}[PubHit w z.2] ≤
      (Fintype.card St : ℝ≥0∞)⁻¹ := by
  classical
  rcases randomOracle_run_pub_cases q s with ⟨v, -, h⟩ | ⟨hnone, h⟩
  · rw [h, prEvent_pure]; simp [hs]
  · rw [h, prEvent_map]
    refine (prEvent_mono _ _ (fun u => u = w) fun u hu => ?_).trans
      (SampleableType.prEvent_uniformSample_eq_singleton w).le
    obtain ⟨q', hq'⟩ := hu
    by_cases e : q' = q
    · subst e
      rw [QueryCache.cacheQuery_self] at hq'
      exact Option.some.inj hq'
    · rw [QueryCache.cacheQuery_of_ne (t := .inl q) s u (by simpa using e)] at hq'
      exact absurd ⟨q', hq'⟩ hs

/-- A lazy-oracle run of public queries makes a fixed value `w` the value of a public cell with
probability at most (its number of queries)`/|St|`. -/
theorem prEvent_romImpl_pubHit_le (w : St) {α : Type}
    (oa : OracleComp (unifSpec + (hS St Blk + tS St Blk)) α) (n : ℕ)
    (hn : IsQueryBoundP oa (fun i => i.isRight = true) n) (c : Cache St Blk)
    (hc : ¬ PubHit w c) :
    Pr{let z ← (simulateQ (hS St Blk + tS St Blk).romImpl oa).run c}[PubHit w z.2] ≤
      n * (Fintype.card St : ℝ≥0∞)⁻¹ := by
  classical
  refine prEvent_bad_le_of_step _ (PubHit w) _ _ ?_ ?_ oa n hn c hc
  · rintro (n | t) s hs ht
    · simp at ht
    · rw [romImpl_run_inr]
      rcases t with q | B
      · exact prEvent_randomOracle_pub_pubHit_le w q s hs
      · rcases randomOracle_run_row_cases B s with ⟨v, -, h⟩ | ⟨hnone, h⟩
        · rw [h, prEvent_pure]; simp [hs]
        · rw [h, prEvent_map, prEvent_eq_zero_of_forall_not _ _ fun u hu => hs ?_]
          · exact zero_le
          · obtain ⟨q', hq'⟩ := hu
            exact ⟨q', by rwa [QueryCache.cacheQuery_of_ne (t := .inr B) s u (by simp)] at hq'⟩
  · rintro (n | t) s hs ht z hz
    · rw [romImpl_run_inl, support_map] at hz
      obtain ⟨u, -, rfl⟩ := hz
      exact hs
    · simp at ht

theorem foldlM_pub_bound (bs : List Blk) (v : St) :
    IsQueryBoundP (List.foldlM (m := OracleComp (unifSpec + (hS St Blk + tS St Blk)))
      (fun c b => (unifSpec + (hS St Blk + tS St Blk)).query (.inr (.inl (c, b)))) v bs)
      (fun i => i.isRight = true) bs.length := by
  induction bs generalizing v with
  | nil => exact isQueryBoundP_pure _ _ _
  | cons b bs ih =>
    simp only [List.foldlM_cons]
    exact (isQueryBoundP_bind ((isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos)
      fun c' _ => ih c').mono (by simp; omega)

/-- **Phase one: a fixed public value.**  After the modified phase one `preSim`, run from the
empty state, a fixed value `w` is the value of a public cell with probability at most
`(q₁ + qc)·max 1 L/|St|`. -/
theorem prEvent_preSim_pubHit_le [DecidableEq Tweak] (w : St) (A : UdAdv F) (q₁ qc L : ℕ)
    (hq₁ : A.PickBound q₁) (hc : A.CollBound qc) (hL : A.CollLen L) :
    Pr{let z ← (simulateQ (preSim F) A.pick).run (([], []), ∅)}[PubHit w z.2.2] ≤
      ((q₁ + qc) * max 1 L : ℕ) * (Fintype.card St : ℝ≥0∞)⁻¹ := by
  classical
  have hn : IsQueryBoundP A.pick (fun t => F.pIsH t = true ∨ F.pIsColl t = true) (q₁ + qc) :=
    hq₁.or hc
  have key := prEvent_bad_le_of_step_ok (preSim F) (fun s : PreSimState Tweak St Blk => PubHit w s.2)
    (fun t => F.pIsH t = true ∨ F.pIsColl t = true)
    (fun i => match i with
      | .inr (.inr (.inr q)) => (F.cch q.1 q.2.1 q.2.2).2.length ≤ L
      | _ => True)
    ((max 1 L : ℕ) * (Fintype.card St : ℝ≥0∞)⁻¹) ?_ ?_ A.pick (q₁ + qc) hn hL
    ((([] : List (Tweak × St)), ([] : List Tweak)), (∅ : Cache St Blk)) (by
      rintro ⟨q, hq⟩; simp at hq)
  · refine key.trans (le_of_eq ?_)
    push_cast
    ring
  · rintro (n | q | t | q) s hs hpt hok
    · simp [THFam.pIsH, THFam.pIsColl] at hpt
    · simp only [preSim, StateT.run_mk, prEvent_map]
      rw [chainRO_run_pub]
      refine (prEvent_randomOracle_pub_pubHit_le w q s.2 hs).trans ?_
      calc (Fintype.card St : ℝ≥0∞)⁻¹ = (1 : ℕ) * (Fintype.card St : ℝ≥0∞)⁻¹ := by simp
        _ ≤ _ := by gcongr; exact le_max_left 1 L
    · simp [THFam.pIsH, THFam.pIsColl] at hpt
    · simp only [preSim, StateT.run_mk]
      split_ifs with hr
      · rw [prEvent_pure]; simp [hs]
      · rw [prEvent_map, chainRO_run_chain]
        refine (prEvent_bind_le_of_forall_le_of_support _ _ _ fun z₁ hz₁ => ?_)
        have hrow : ¬ PubHit w z₁.2 := by
          rintro ⟨q', hq'⟩
          rcases randomOracle_run_row_cases (F.cch q.1 q.2.1 q.2.2).1 s.2 with
            ⟨v, -, h⟩ | ⟨-, h⟩
          · rw [h, support_pure, Set.mem_singleton_iff] at hz₁
            rw [hz₁] at hq'
            exact hs ⟨q', hq'⟩
          · rw [h, support_map] at hz₁
            obtain ⟨u, -, rfl⟩ := hz₁
            exact hs ⟨q', by rwa [QueryCache.cacheQuery_of_ne (t := .inr _) s.2 u (by simp)]
              at hq'⟩
        refine (prEvent_romImpl_pubHit_le w _ _ (foldlM_pub_bound _ z₁.1) z₁.2 hrow).trans ?_
        gcongr
        exact_mod_cast hok.trans (le_max_right 1 L)
  · rintro (n | q | t | q) s hs hpt z hz
    · simp only [preSim, StateT.run_mk, support_map] at hz
      obtain ⟨u, -, rfl⟩ := hz
      exact hs
    · simp [THFam.pIsH, THFam.pIsColl] at hpt
    · simp only [preSim, StateT.run_mk] at hz
      split_ifs at hz
      · simp only [support_pure, Set.mem_singleton_iff] at hz
        rw [hz]; exact hs
      · rw [support_map] at hz
        obtain ⟨u, -, rfl⟩ := hz
        exact hs
    · simp [THFam.pIsH, THFam.pIsColl] at hpt

/-! ## Phase two -/

/-- **Phase two, fine form.**  As `prT_ud_phase2_le`, for a second phase that is the expansion of
a program `dC` with at most `qM` raw compression queries and only free chain queries, from a
cache that is not `PubBad`, `cv ≠ IV`: the error is `qM/|M'| + 2 q₂/|St|`. -/
theorem prT_ud_phase2_le_fine [DecidableEq Tweak] [SampleableType M'] [Fintype M']
    (emb : M' → M) (hemb : Function.Injective emb)
    (btw : Blk → Tweak) (hbtwT : ∀ t m, btw (F.tch t m).1 = t)
    (hinj : ∀ t m m', (F.tch t m).1 = (F.tch t m').1 → m = m')
    (A : UdAdv F) (q₂ : ℕ) (hq₂ : A.DistBound q₂) (st : A.State) (seed : PkSeed)
    (dC : OracleComp (pcS St Blk) Bool)
    (hdC : A.distinguish st seed = simulateQ (expandImpl F.IV) dC) (qM : ℕ)
    (hqM : IsQueryBoundP dC (fun t => isRawC t = true) qM)
    (hfree : AllQueriesSatisfy dC (freeC (F.sb seed)))
    (s : PreSimState Tweak St Blk) (hI : PreInv btw s) (cv : St) (hcv : cv ≠ F.IV)
    (hpb : ¬ PubBad F.IV cv s.2) :
    HP.prT (udPhiR F emb s >>= fun p =>
        (simulateQ (routeRO F.IV (F.sb seed) cv) (udP₂ A seed (st, p.1))).run' p.2) ≤
      HP.prT ((simulateQ (routeRO F.IV (F.sb seed) cv) (udP₂ A seed (st, udPj s.1))).run' s.2) +
        qM * (Fintype.card M' : ℝ≥0∞)⁻¹ + q₂ * (2 * (Fintype.card St : ℝ≥0∞)⁻¹) := by
  classical
  obtain ⟨⟨qs, tw⟩, c⟩ := s
  have hcellinj : ∀ (k : Tweak) (x x' : M'), preCell F emb k x = preCell F emb k x' → x = x' :=
    fun k x x' h => hemb (hinj k _ _ h)
  have step1 : HP.prT (udPhiR F emb ((qs, tw), c) >>= fun p =>
        (simulateQ (routeRO F.IV (F.sb seed) cv) (udP₂ A seed (st, p.1))).run' p.2) ≤
      HP.prT (hideDraw qs >>= fun xs =>
        (simulateQ (routeRO F.IV (F.sb seed) cv) (A.distinguish st seed)).run c >>= fun z =>
          if HiddenRead (hidMap (preCell F emb) xs) z.2 then pure true else pure z.1) := by
    simp only [udPhiR, prePhi, Functor.map_map, bind_map_left, udP₂]
    refine HP.prT_bind_mono _ _ _ fun xs hxs => ?_
    have hnr := not_hiddenRead_of_inv (F := F) emb btw hbtwT hI hxs
    have e : (simulateQ (routeRO F.IV (F.sb seed) cv) (A.distinguish st seed)).run'
          (patch c (hidMap (preCell F emb) xs)) =
        (simulateQ (hS St Blk + tS St Blk).romImpl
          (simulateQ (route F.IV (F.sb seed) cv) (A.distinguish st seed))).run
            (patch c (hidMap (preCell F emb) xs)) >>= fun z => pure z.1 := by
      rw [StateT.run'_eq, simulateQ_romImpl_route, map_eq_bind_pure_comp]
      rfl
    rw [e]
    refine (prT_run_romImpl_patch_le _ _ (fun z => pure z.1) c hnr).trans (le_of_eq ?_)
    rw [simulateQ_romImpl_route]
  refine step1.trans ?_
  rw [HP.prT_swap]
  have e2 : (simulateQ (routeRO F.IV (F.sb seed) cv)
        (udP₂ A seed (st, udPj ((qs, tw), c).1))).run' c =
      (simulateQ (routeRO F.IV (F.sb seed) cv) (A.distinguish st seed)).run c >>= fun z =>
        pure z.1 := by
    rw [StateT.run'_eq, map_eq_bind_pure_comp]
    rfl
  rw [e2]
  refine (prT_bind_le_add_mul _ _ (fun z => pure z.1) (fun z => pure (decide (PubBad F.IV cv z.2)))
    (qM * (Fintype.card M' : ℝ≥0∞)⁻¹) 1 fun z hz => ?_).trans ?_
  · refine (HP.prT_bind_le_prEvent_add (hideDraw qs) _
      (fun xs => HiddenRead (hidMap (preCell F emb) xs) z.2) (ε := HP.prT (pure z.1))
      fun xs _ hne => ?_).trans ?_
    · simp only [hne, ite_false]
      exact le_rfl
    · rw [add_comm, add_assoc]
      refine add_le_add le_rfl ?_
      rw [hdC] at hz
      have hpot := routeRO_potential_fine F.IV (F.sb seed) cv hcv
        (fun c' : Cache St Blk =>
          Pr{let xs ← hideDraw (M' := M') qs}[HiddenRead (hidMap (preCell F emb) xs) c'])
        (Fintype.card M' : ℝ≥0∞)⁻¹
        (fun c' q u => prEvent_mono _ _ _ fun xs h => hiddenRead_cacheQuery_pub h)
        (fun c' B u => (prEvent_mono _ _ _ fun xs h => hiddenRead_cacheQuery_row h).trans
          ((prEvent_or_le _ _ _).trans (add_le_add le_rfl
            (prEvent_hideDraw_cell_le (preCell F emb) btw (fun k x => hbtwT k (emb x)) hcellinj
              qs hI.1 B))))
        dC qM hqM hfree c z hz
      have h0 : Pr{let xs ← hideDraw (M' := M') qs}[HiddenRead (hidMap (preCell F emb) xs) c] = 0 :=
        prEvent_eq_zero_of_forall_mem_support _ _ fun xs hxs =>
          not_hiddenRead_of_inv (F := F) emb btw hbtwT hI hxs
      rw [prT_pure_decide, one_mul]
      by_cases hb : PubBad F.IV cv z.2
      · simp only [hb, ↓reduceIte]
        exact le_add_left (prEvent_le_one _)
      · simp only [hb, ↓reduceIte, add_zero]
        rcases hpot with h | h
        · rw [h0, zero_add] at h
          exact h
        · exact absurd h hb
  · rw [one_mul]
    refine add_le_add le_rfl ?_
    rw [HP.prT_bind_pure]
    simp only [decide_eq_true_eq]
    exact prEvent_routeRO_pubBad_le F.IV (F.sb seed) cv (A.distinguish st seed) q₂ (hq₂ st seed)
      c hpb


/-! ## Phase one, averaged -/

theorem prT_bind_bind_decide {α β : Type} (mx : ProbComp α) (my : ProbComp β) (P : α → β → Prop)
    [∀ a b, Decidable (P a b)] :
    HP.prT (mx >>= fun a => my >>= fun b => pure (decide (P a b))) =
      Pr{let w ← (mx >>= fun a => my >>= fun b => pure (a, b))}[P w.1 w.2] := by
  have h := HP.prT_bind_pure (mx >>= fun a => my >>= fun b => pure (a, b))
    (fun w => decide (P w.1 w.2))
  simp only [bind_assoc, pure_bind, decide_eq_true_eq] at h
  exact h

open Classical in
/-- The averaged bad event of the fine phase two: `cv = IV`, or a public value after phase one
is `IV` or `cv`. -/
theorem prT_preSim_cvBad_le [DecidableEq Tweak] (A : UdAdv F) (q₁ qc L : ℕ)
    (hq₁ : A.PickBound q₁) (hc : A.CollBound qc) (hL : A.CollLen L) :
    HP.prT ((simulateQ (preSim F) A.pick).run (([], []), ∅) >>= fun z =>
        ($ᵗ St : ProbComp St) >>= fun cv => pure (decide (cv = F.IV ∨ PubBad F.IV cv z.2.2))) ≤
      (1 + 2 * ((q₁ + qc) * max 1 L) : ℕ) * (Fintype.card St : ℝ≥0∞)⁻¹ := by
  classical
  set K : ℝ≥0∞ := ((q₁ + qc) * max 1 L : ℕ) * (Fintype.card St : ℝ≥0∞)⁻¹ with hK
  set mz := (simulateQ (preSim F) A.pick).run (([], []), ∅)
  have hK1 : ∀ w, Pr{let z ← mz}[PubHit w z.2.2] ≤ K := fun w =>
    prEvent_preSim_pubHit_le w A q₁ qc L hq₁ hc hL
  rw [prT_bind_bind_decide]
  set mw := mz >>= fun z => ($ᵗ St : ProbComp St) >>= fun cv => pure (z, cv)
  have e1 : Pr{let w ← mw}[w.2 = F.IV] = (Fintype.card St : ℝ≥0∞)⁻¹ := by
    rw [← prT_bind_bind_decide (P := fun (_ : A.State × PreSimState Tweak St Blk) cv => cv = F.IV),
      HP.prT_bind_const, HP.prT_bind_pure]
    simp only [decide_eq_true_eq]
    exact SampleableType.prEvent_uniformSample_eq_singleton F.IV
  have e2 : Pr{let w ← mw}[PubHit F.IV w.1.2.2] ≤ K := by
    rw [← prT_bind_bind_decide (P := fun (z : A.State × PreSimState Tweak St Blk) (_ : St) =>
      PubHit F.IV z.2.2)]
    rw [HP.prT_bind_congr mz _ (fun z : A.State × PreSimState Tweak St Blk =>
      pure (decide (PubHit F.IV z.2.2))) (fun z _ => HP.prT_bind_const _ _), HP.prT_bind_pure]
    simp only [decide_eq_true_eq]
    exact hK1 F.IV
  have e3 : Pr{let w ← mw}[PubHit w.2 w.1.2.2] ≤ K := by
    rw [← prT_bind_bind_decide (P := fun (z : A.State × PreSimState Tweak St Blk) (cv : St) =>
      PubHit cv z.2.2), HP.prT_swap]
    refine HP.prT_bind_le_of_forall_le _ _ fun cv _ => ?_
    rw [HP.prT_bind_pure]
    simp only [decide_eq_true_eq]
    exact hK1 cv
  calc Pr{let w ← mw}[w.2 = F.IV ∨ PubBad F.IV w.2 w.1.2.2]
      ≤ Pr{let w ← mw}[w.2 = F.IV] +
          (Pr{let w ← mw}[PubHit F.IV w.1.2.2] + Pr{let w ← mw}[PubHit w.2 w.1.2.2]) :=
        (prEvent_or_le _ _ _).trans (add_le_add le_rfl (prEvent_or_le _ _ _))
    _ ≤ (Fintype.card St : ℝ≥0∞)⁻¹ + (K + K) := by rw [e1]; gcongr
    _ = _ := by rw [hK]; push_cast; ring

/-! ## The two ideal games, fine form -/

theorem arith_seed_bad (X c P a : ℝ≥0∞) : X + c + 1 * P ≤ X + (a + 1 * P) + c * 1 := by
  rw [mul_one]
  calc X + c + 1 * P = X + 1 * P + c := by ring
    _ ≤ X + (a + 1 * P) + c := by gcongr; exact le_add_self

theorem arith_seed_avg (X a P c p β : ℝ≥0∞) (h : p ≤ β) :
    X + (a + 1 * P) + c * p ≤ X + (a + c * β) + 1 * P :=
  calc X + (a + 1 * P) + c * p ≤ X + (a + 1 * P) + c * β := by gcongr
    _ = _ := by ring

open Classical in
/-- **The two ideal SM-UD games, fine accounting.**  As `ud_ideal_le`, for a distinguisher that is
the expansion of programs `dC st pk` with chain queries: outside a set `bad` of public seeds of
probability at most `β`, `dC st pk` makes at most `qM` raw compression queries and only free
chain queries.  The error `q₂/|M'|` becomes `qM/|M'| + β·q₂/|M'| + 2 q₂/|St|` plus
`(1 + 2 (q₁ + qc)·max 1 L)/|St|`. -/
theorem ud_ideal_le_fine [DecidableEq Tweak] [SampleableType M'] [Fintype M']
    [SampleableType Y] [Finite Y]
    (emb : M' → M) (hemb : Function.Injective emb)
    (hsingle : ∀ t m, (F.tch t m).2 = [])
    (btw : Blk → Tweak) (hbtwT : ∀ t m, btw (F.tch t m).1 = t)
    (hbtwC : ∀ i t m, btw (F.cch i t m).1 = t)
    (hinj : ∀ t m m', (F.tch t m).1 = (F.tch t m').1 → m = m')
    (hout : ∀ p : Y → Prop, Pr{let u ← $ᵗ St}[p (F.out u)] = Pr{let y ← $ᵗ Y}[p y])
    (A : UdAdv F) (q₁ qc L q₂ : ℕ) (hq₁ : A.PickBound q₁) (hc : A.CollBound qc)
    (hL : A.CollLen L) (hq₂ : A.DistBound q₂)
    (dC : A.State → PkSeed → OracleComp (pcS St Blk) Bool)
    (hdC : ∀ st pk, A.distinguish st pk = simulateQ (expandImpl F.IV) (dC st pk))
    (bad : PkSeed → Prop) (β : ℝ≥0∞) (hβ : Pr{let s ← F.seedGen}[bad s] ≤ β) (qM : ℕ)
    (hqM : ∀ st pk, ¬ bad pk → IsQueryBoundP (dC st pk) (fun t => isRawC t = true) qM)
    (hfree : ∀ st pk, ¬ bad pk → AllQueriesSatisfy (dC st pk) (freeC (F.sb pk))) :
    𝒟[idealGame F.IV F.sb F.seedGen (udProg₁ .real emb A) (udP₂ A)] {true} ≤
      𝒟[idealGame F.IV F.sb F.seedGen (udProg₁ .ideal emb A) (udP₂ A)] {true} +
        (qM * (Fintype.card M' : ℝ≥0∞)⁻¹ + q₂ * (2 * (Fintype.card St : ℝ≥0∞)⁻¹) +
          q₂ * (Fintype.card M' : ℝ≥0∞)⁻¹ * β) +
        (1 + 2 * ((q₁ + qc) * max 1 L) : ℕ) * (Fintype.card St : ℝ≥0∞)⁻¹ := by
  set εM : ℝ≥0∞ := (Fintype.card M' : ℝ≥0∞)⁻¹
  set εS : ℝ≥0∞ := q₂ * (2 * (Fintype.card St : ℝ≥0∞)⁻¹)
  rw [← HP.prT_eq, ← HP.prT_eq, idealGame_eq_phases, idealGame_eq_phases,
    prT_congr_evalDistEq ((ud_phase1_real emb hsingle btw hbtwT hbtwC A).bind_left _),
    prT_congr_evalDistEq ((ud_phase1_ideal emb hout A).bind_left _)]
  simp only [udPhiI, bind_assoc, pure_bind]
  refine (prT_bind_le_add_mul _ _ (fun z => F.seedGen >>= fun seed =>
      ($ᵗ St : ProbComp St) >>= fun cv =>
        (simulateQ (routeRO F.IV (F.sb seed) cv) (udP₂ A seed (z.1, udPj z.2.1))).run' z.2.2)
    (fun z => ($ᵗ St : ProbComp St) >>= fun cv =>
      pure (decide (cv = F.IV ∨ PubBad F.IV cv z.2.2)))
    (qM * εM + εS + q₂ * εM * β) 1 fun z hz => ?_).trans ?_
  · have hI : PreInv btw z.2 :=
      simulateQ_run_preservesInv (preSim F) (PreInv btw) (preInv_step btw hbtwC) A.pick
        (([], []), ∅) ⟨by simp, fun B hB => by simp at hB, by simp⟩ z hz
    rw [HP.prT_swap]
    refine (prT_bind_le_add_mul _ _ (fun seed => ($ᵗ St : ProbComp St) >>= fun cv =>
        (simulateQ (routeRO F.IV (F.sb seed) cv) (udP₂ A seed (z.1, udPj z.2.1))).run' z.2.2)
      (fun seed => pure (decide (bad seed)))
      (qM * εM + εS + 1 * HP.prT (($ᵗ St : ProbComp St) >>= fun cv =>
        pure (decide (cv = F.IV ∨ PubBad F.IV cv z.2.2)))) (q₂ * εM) fun seed _ => ?_).trans ?_
    · rw [HP.prT_swap]
      refine (prT_bind_le_add_mul _ _ (fun cv =>
          (simulateQ (routeRO F.IV (F.sb seed) cv) (udP₂ A seed (z.1, udPj z.2.1))).run' z.2.2)
        (fun cv => pure (decide (cv = F.IV ∨ PubBad F.IV cv z.2.2)))
        (if bad seed then q₂ * εM else qM * εM + εS) 1 fun cv _ => ?_).trans ?_
      · by_cases hb : cv = F.IV ∨ PubBad F.IV cv z.2.2
        · rw [prT_pure_decide, if_pos hb, one_mul]
          exact (HP.prT_le_one _).trans le_add_self
        · rw [prT_pure_decide, if_neg hb, mul_zero, add_zero]
          simp only [not_or] at hb
          by_cases hs : bad seed
          · rw [if_pos hs]
            exact prT_ud_phase2_le emb hemb btw hbtwT hinj A q₂ hq₂ z.1 z.2 hI seed cv
          · rw [if_neg hs]
            refine (prT_ud_phase2_le_fine emb hemb btw hbtwT hinj A q₂ hq₂ z.1 seed (dC z.1 seed)
              (hdC z.1 seed) qM (hqM z.1 seed hs) (hfree z.1 seed hs) z.2 hI cv hb.1
              hb.2).trans (le_of_eq ?_)
            rw [add_assoc]
      · rw [prT_pure_decide]
        split_ifs with hs
        · exact arith_seed_bad _ _ _ _
        · exact le_of_eq (by ring)
    · exact arith_seed_avg _ _ _ _ _ _ (by rw [HP.prT_bind_pure]; simpa using hβ)
  · rw [one_mul]
    exact add_le_add le_rfl (prT_preSim_cvBad_le A q₁ qc L hq₁ hc hL)

/-- **SM-UD, fine accounting** (`ud_bound` with `ud_ideal_le_fine` for `ud_ideal_le`). -/
theorem ud_bound_fine [Finite Blk] [SampleableType (CF St Blk)]
    [DecidableEq Tweak] [SampleableType M'] [Fintype M'] [SampleableType Y] [Finite Y]
    (emb : M' → M) (hemb : Function.Injective emb)
    (hsb : Function.Injective F.sb)
    (γ : ℝ≥0∞) (hγ : ∀ s, Pr{let s' ← F.seedGen}[s' = s] ≤ γ)
    (hsingle : ∀ t m, (F.tch t m).2 = [])
    (btw : Blk → Tweak) (hbtwT : ∀ t m, btw (F.tch t m).1 = t)
    (hbtwC : ∀ i t m, btw (F.cch i t m).1 = t)
    (hinj : ∀ t m m', (F.tch t m).1 = (F.tch t m').1 → m = m')
    (hout : ∀ p : Y → Prop, Pr{let u ← $ᵗ St}[p (F.out u)] = Pr{let y ← $ᵗ Y}[p y])
    (A : UdAdv F) (q₁ qch qc L q₂ : ℕ)
    (hq₁ : A.PickBound q₁) (hch : A.ChalBound qch) (hc : A.CollBound qc)
    (hL : A.CollLen L) (hq₂ : A.DistBound q₂)
    (dC : A.State → PkSeed → OracleComp (pcS St Blk) Bool)
    (hdC : ∀ st pk, A.distinguish st pk = simulateQ (expandImpl F.IV) (dC st pk))
    (bad : PkSeed → Prop) (β : ℝ≥0∞) (hβ : Pr{let s ← F.seedGen}[bad s] ≤ β) (qM : ℕ)
    (hqM : ∀ st pk, ¬ bad pk → IsQueryBoundP (dC st pk) (fun t => isRawC t = true) qM)
    (hfree : ∀ st pk, ¬ bad pk → AllQueriesSatisfy (dC st pk) (freeC (F.sb pk))) :
    udRealI F emb hemb A ≤
      udIdealI F emb hemb A + (qM + q₂ * β) * (Fintype.card M' : ℝ≥0∞)⁻¹ + 2 * q₁ * γ +
        (2 * (2 * q₁ + (qch + qc) * (1 + 2 * L) + 1) + (1 + 2 * ((q₁ + qc) * max 1 L)) +
          2 * q₂ : ℕ) * (Fintype.card St : ℝ≥0∞)⁻¹ := by
  rw [udRealI_eq_realGame, udIdealI_eq_realGame]
  have hT : ∀ t m, (F.tch t m).2.length ≤ L := fun t m => by rw [hsingle]; exact Nat.zero_le _
  have h1 := hiddenPrefix F.IV F.sb hsb F.seedGen γ hγ (udProg₁ .real emb A) (udP₂ A) q₁
    (qch + qc) L (udProg₁_pubBound .real emb A hq₁) (udProg₁_chainBound .real emb A hch hc)
    (udProg₁_chainLen .real emb A hT hL)
  have h2 := ud_ideal_le_fine emb hemb hsingle btw hbtwT hbtwC hinj hout A q₁ qc L q₂ hq₁ hc hL
    hq₂ dC hdC bad β hβ qM hqM hfree
  have h3 := hiddenPrefix_ge F.IV F.sb hsb F.seedGen γ hγ (udProg₁ .ideal emb A) (udP₂ A) q₁
    (qch + qc) L (udProg₁_pubBound .ideal emb A hq₁) (udProg₁_chainBound .ideal emb A hch hc)
    (udProg₁_chainLen .ideal emb A hT hL)
  refine h1.trans ((add_le_add (add_le_add (h2.trans (add_le_add (add_le_add h3 le_rfl)
    le_rfl)) le_rfl) le_rfl).trans (le_of_eq ?_))
  push_cast
  ring

end Lemmas

end Ideal

#print axioms Ideal.prEvent_preSim_pubHit_le
#print axioms Ideal.prT_ud_phase2_le_fine
#print axioms Ideal.ud_ideal_le_fine
#print axioms Ideal.ud_bound_fine
