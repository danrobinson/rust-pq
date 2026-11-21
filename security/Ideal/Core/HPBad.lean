import Ideal.Core.HPFlag

/-!
# The bound on the bad event of the hidden-prefix hop

`prT_badGame_le`: the seed and `cv`, drawn after phase one of the eager ideal game, make a traced
query touch a hidden cell (or `cv = IV`) with probability at most
`q₁ * γ + (2 * q₁ + C * (1 + 2 * L) + 1) / |St|`.
-/

open OracleComp OracleSpec ENNReal

namespace Ideal.HP

variable {St Blk PkSeed σ : Type}

/-! ## Union bound over a list -/

theorem prEvent_list_exists_le {ρ ι : Type} (mx : ProbComp ρ) (W : ρ → ι → Prop)
    (w : ι → ℝ≥0∞) (l : List ι) (h : ∀ t ∈ l, Pr{let r ← mx}[W r t] ≤ w t) :
    Pr{let r ← mx}[∃ t ∈ l, W r t] ≤ (l.map w).sum := by
  induction l with
  | nil =>
    rw [prEvent_eq_zero_of_forall_not mx _ (by simp)]
    exact zero_le
  | cons a l ih =>
    refine (prEvent_mono mx _ (fun r => W r a ∨ ∃ t ∈ l, W r t) (by simp)).trans ?_
    refine (prEvent_or_le mx _ _).trans ?_
    rw [List.map_cons, List.sum_cons]
    exact add_le_add (h a (by simp)) (ih fun t ht => h t (by simp [ht]))

/-! ## The seed and `cv` -/

/-- The seed and `cv`, drawn after phase one. -/
noncomputable def rho [SampleableType St] (seedGen : ProbComp PkSeed) : ProbComp (PkSeed × St) :=
  seedGen >>= fun seed => (fun cv => (seed, cv)) <$> ($ᵗ St)

theorem prEvent_rho_fst [SampleableType St] (seedGen : ProbComp PkSeed) (p : PkSeed → Prop)
    {ε : ℝ≥0∞} (h : Pr{let s ← seedGen}[p s] ≤ ε) :
    Pr{let r ← rho (St := St) seedGen}[p r.1] ≤ ε := by
  unfold rho
  refine (prEvent_bind_le_prEvent_of_forall_eq_zero seedGen _ p (fun r : PkSeed × St => p r.1)
    fun a ha => ?_).trans h
  rw [prEvent_map]
  exact prEvent_eq_zero_of_forall_not _ _ fun _ => ha

theorem prEvent_rho_snd [SampleableType St] (seedGen : ProbComp PkSeed) (p : St → Prop)
    {ε : ℝ≥0∞} (h : Pr{let cv ← $ᵗ St}[p cv] ≤ ε) :
    Pr{let r ← rho (St := St) seedGen}[p r.2] ≤ ε := by
  unfold rho
  refine prEvent_bind_le_of_forall_le seedGen _ (fun r : PkSeed × St => p r.2) fun a => ?_
  rw [prEvent_map]
  exact h

theorem prEvent_seed_cell [DecidableEq St] (IV : St) (sb : PkSeed → Blk)
    (hsb : Function.Injective sb) (seedGen : ProbComp PkSeed) (γ : ℝ≥0∞)
    (hγ : ∀ s, Pr{let s' ← seedGen}[s' = s] ≤ γ) (q : St × Blk) :
    Pr{let s ← seedGen}[q = (IV, sb s)] ≤ γ := by
  by_cases h : ∃ s₀, q = (IV, sb s₀)
  · obtain ⟨s₀, rfl⟩ := h
    refine (prEvent_mono seedGen _ (fun s => s = s₀) fun s hs => ?_).trans (hγ s₀)
    exact (hsb (Prod.mk.inj hs).2).symm
  · rw [prEvent_eq_zero_of_forall_not seedGen _ fun s hs => h ⟨s, hs⟩]
    exact zero_le

/-! ## Chaining values equal to `cv` -/

/-- Some chaining value of the continuation from `c` through `bs` that is used as a cell row
equals `cv`. -/
def cvHit [DecidableEq St] (cv : St) (g : CF St Blk) : St → List Blk → Bool
  | _, [] => false
  | c, b :: bs => decide (c = cv) || cvHit cv g (g (c, b)) bs

theorem cellBad_imp [DecidableEq St] [DecidableEq Blk] (IV : St) (sbs : Blk) (cv : St)
    (g : CF St Blk) (c : St) (bs : List Blk) (h : cellBad IV sbs cv g c bs = true) :
    (decide (c = IV) || restIV IV g c bs) = true ∨ cvHit cv g c bs = true := by
  induction bs generalizing c with
  | nil => simp [cellBad] at h
  | cons b bs ih =>
    simp only [cellBad, Bool.or_eq_true, decide_eq_true_eq, Prod.mk.injEq] at h
    simp only [restIV, cvHit, Bool.or_eq_true, decide_eq_true_eq]
    rcases h with (⟨h, -⟩ | h) | h
    · exact Or.inl (Or.inl h)
    · exact Or.inr (Or.inl h)
    · rcases ih _ h with h' | h'
      · simp only [Bool.or_eq_true, decide_eq_true_eq] at h'
        exact Or.inl (Or.inr h')
      · exact Or.inr (Or.inr h')

theorem prEvent_cvHit [Fintype St] [DecidableEq St] [SampleableType St] (g : CF St Blk) (c : St)
    (bs : List Blk) :
    Pr{let cv ← $ᵗ St}[cvHit cv g c bs = true] ≤
      (bs.length : ℝ≥0∞) * (Fintype.card St : ℝ≥0∞)⁻¹ := by
  induction bs generalizing c with
  | nil =>
    rw [prEvent_eq_zero_of_forall_not _ _ (by simp [cvHit])]
    exact zero_le
  | cons b bs ih =>
    refine (prEvent_mono _ _ (fun cv => c = cv ∨ cvHit cv g (g (c, b)) bs = true)
      (by simp [cvHit])).trans ?_
    refine (prEvent_or_le _ _ _).trans ?_
    rw [SampleableType.prEvent_uniformSample_eq_singleton' c, List.length_cons, Nat.cast_add,
      Nat.cast_one, add_mul, one_mul, add_comm]
    exact add_le_add (ih _) le_rfl

/-! ## The bound for a fixed trace -/

section Fixed

variable [Fintype St] [DecidableEq St] [DecidableEq Blk] [SampleableType St]

/-- The seed-and-`cv` event charged to a traced query. -/
def Wev (IV : St) (sb : PkSeed → Blk) (g : CF St Blk) (T : Blk → St) (r : PkSeed × St) :
    (St × Blk) ⊕ (Blk × List Blk) → Prop
  | .inl q => q = (IV, sb r.1) ∨ q.1 = r.2
  | .inr q => cvHit r.2 g (T q.1) q.2 = true

/-- The weight charged to a traced query. -/
noncomputable def wt (St : Type) [Fintype St] {Blk : Type} (γ : ℝ≥0∞) :
    (St × Blk) ⊕ (Blk × List Blk) → ℝ≥0∞
  | .inl _ => γ + (Fintype.card St : ℝ≥0∞)⁻¹
  | .inr q => (q.2.length : ℝ≥0∞) * (Fintype.card St : ℝ≥0∞)⁻¹

omit [DecidableEq Blk] in
theorem prEvent_Wev_le (IV : St) (sb : PkSeed → Blk) (hsb : Function.Injective sb)
    (seedGen : ProbComp PkSeed) (γ : ℝ≥0∞) (hγ : ∀ s, Pr{let s' ← seedGen}[s' = s] ≤ γ)
    (g : CF St Blk) (T : Blk → St) (t : (St × Blk) ⊕ (Blk × List Blk)) :
    Pr{let r ← rho (St := St) seedGen}[Wev IV sb g T r t] ≤ wt St γ t := by
  rcases t with q | q
  · simp only [Wev, wt]
    refine (prEvent_or_le _ _ _).trans (add_le_add ?_ ?_)
    · exact prEvent_rho_fst seedGen (fun s => q = (IV, sb s))
        (prEvent_seed_cell IV sb hsb seedGen γ hγ q)
    · exact prEvent_rho_snd seedGen (fun cv => q.1 = cv)
        (SampleableType.prEvent_uniformSample_eq_singleton' q.1).le
  · simp only [Wev, wt]
    exact prEvent_rho_snd seedGen (fun cv => cvHit cv g (T q.1) q.2 = true)
      (prEvent_cvHit g (T q.1) q.2)

omit [DecidableEq St] [DecidableEq Blk] [SampleableType St] in
theorem sum_wt_le (γ : ℝ≥0∞) (L : ℕ) (l : List ((St × Blk) ⊕ (Blk × List Blk)))
    (hl : ∀ t ∈ l, chainLenLe L (.inr t)) :
    (l.map (wt St γ)).sum ≤
      (l.countP (fun t => decide (isPub (.inr t) = true)) : ℝ≥0∞) *
          (γ + (Fintype.card St : ℝ≥0∞)⁻¹) +
        (l.countP (fun t => decide (isChain (.inr t) = true)) : ℝ≥0∞) *
          ((L : ℝ≥0∞) * (Fintype.card St : ℝ≥0∞)⁻¹) := by
  induction l with
  | nil => simp
  | cons t l ih =>
    have ih' := ih fun t' ht' => hl t' (by simp [ht'])
    rw [List.map_cons, List.sum_cons, List.countP_cons, List.countP_cons]
    set a := List.countP (fun t => decide (isPub (Sum.inr t) = true)) l
    set b := List.countP (fun t => decide (isChain (Sum.inr t) = true)) l
    rcases t with q | q
    · simp only [wt, isPub, isChain, decide_true, ite_true, Bool.false_eq_true, decide_false,
        ite_false, Nat.cast_add, Nat.cast_one, add_zero, add_mul, one_mul]
      calc _ ≤ γ + (Fintype.card St : ℝ≥0∞)⁻¹ + _ := add_le_add le_rfl ih'
        _ = _ := by ring
    · have hq : q.2.length ≤ L := hl (.inr q) (by simp)
      have hq' : (q.2.length : ℝ≥0∞) * (Fintype.card St : ℝ≥0∞)⁻¹ ≤
          (L : ℝ≥0∞) * (Fintype.card St : ℝ≥0∞)⁻¹ := by gcongr
      simp only [wt, isPub, isChain, decide_true, ite_true, Bool.false_eq_true, decide_false,
        ite_false, Nat.cast_add, Nat.cast_one, add_zero, add_mul, one_mul]
      calc _ ≤ (L : ℝ≥0∞) * (Fintype.card St : ℝ≥0∞)⁻¹ + _ := add_le_add hq' ih'
        _ = _ := by ring

omit [Fintype St] [SampleableType St] in
theorem badQ_imp (IV : St) (sb : PkSeed → Blk) (g : CF St Blk) (T : Blk → St) (r : PkSeed × St)
    (l : List ((St × Blk) ⊕ (Blk × List Blk))) (hno : l.any (hasIV IV g T) = false)
    (h : (decide (r.2 = IV) || l.any (badQ IV (sb r.1) r.2 g T)) = true) :
    r.2 = IV ∨ ∃ t ∈ l, Wev IV sb g T r t := by
  simp only [Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true] at h
  rcases h with h | ⟨t, ht, hb⟩
  · exact Or.inl h
  · refine Or.inr ⟨t, ht, ?_⟩
    have hno' : hasIV IV g T t = false := by
      rw [List.any_eq_false] at hno
      simpa using hno t ht
    rcases t with q | q
    · simp only [badQ, Bool.or_eq_true, decide_eq_true_eq] at hb
      exact hb
    · simp only [badQ] at hb
      rcases cellBad_imp IV (sb r.1) r.2 g _ _ hb with h' | h'
      · simp only [hasIV] at hno'
        rw [hno'] at h'
        exact absurd h' (by simp)
      · exact h'

/-- For a fixed trace without an `IV` answer, the bad event over the seed and `cv`. -/
theorem prEvent_bad_fixed_le (IV : St) (sb : PkSeed → Blk) (hsb : Function.Injective sb)
    (seedGen : ProbComp PkSeed) (γ : ℝ≥0∞) (hγ : ∀ s, Pr{let s' ← seedGen}[s' = s] ≤ γ)
    (g : CF St Blk) (T : Blk → St) (q₁ C L : ℕ) (l : List ((St × Blk) ⊕ (Blk × List Blk)))
    (hq : l.countP (fun t => decide (isPub (.inr t) = true)) ≤ q₁)
    (hC : l.countP (fun t => decide (isChain (.inr t) = true)) ≤ C)
    (hL : ∀ t ∈ l, chainLenLe L (.inr t)) (hno : l.any (hasIV IV g T) = false) :
    Pr{let r ← rho (St := St) seedGen}[
        (decide (r.2 = IV) || l.any (badQ IV (sb r.1) r.2 g T)) = true] ≤
      (Fintype.card St : ℝ≥0∞)⁻¹ + ((q₁ : ℝ≥0∞) * (γ + (Fintype.card St : ℝ≥0∞)⁻¹) +
        (C : ℝ≥0∞) * ((L : ℝ≥0∞) * (Fintype.card St : ℝ≥0∞)⁻¹)) := by
  refine (prEvent_mono _ _ (fun r => r.2 = IV ∨ ∃ t ∈ l, Wev IV sb g T r t)
    fun r hr => badQ_imp IV sb g T r l hno hr).trans ?_
  refine (prEvent_or_le _ _ _).trans (add_le_add ?_ ?_)
  · exact prEvent_rho_snd seedGen (fun cv => cv = IV)
      (SampleableType.prEvent_uniformSample_eq_singleton IV).le
  · refine (prEvent_list_exists_le _ _ (wt St γ) l fun t _ =>
      prEvent_Wev_le IV sb hsb seedGen γ hγ g T t).trans ?_
    refine (sum_wt_le γ L l hL).trans (add_le_add ?_ ?_)
    · gcongr
    · gcongr

end Fixed

/-! ## The bad game -/

theorem prT_badGame_le [Fintype St] [DecidableEq St] [DecidableEq Blk] [SampleableType St]
    [Fintype Blk] [SampleableType (CF St Blk)]
    (IV : St) (sb : PkSeed → Blk) (hsb : Function.Injective sb) (seedGen : ProbComp PkSeed)
    (γ : ℝ≥0∞) (hγ : ∀ s, Pr{let s' ← seedGen}[s' = s] ≤ γ)
    (prog₁ : OracleComp (unifSpec + (hS St Blk + chainS St Blk)) σ) (q₁ C L : ℕ)
    (hq : IsQueryBoundP prog₁ (fun i => isPub i = true) q₁)
    (hC : IsQueryBoundP prog₁ (fun i => isChain i = true) C)
    (hL : AllQueriesSatisfy prog₁ (chainLenLe L)) :
    prT (badGame IV sb seedGen prog₁) ≤
      q₁ * γ + (2 * q₁ + C * (1 + 2 * L) + 1 : ℕ) * (Fintype.card St : ℝ≥0∞)⁻¹ := by
  set packed : ProbComp (CF St Blk × (Blk → St) × σ × List ((St × Blk) ⊕ (Blk × List Blk))) :=
    $ᵗ (CF St Blk) >>= fun g => $ᵗ (Blk → St) >>= fun T =>
      (simulateQ (trImpl (pairAns g (chainI g T))) prog₁).run [] >>= fun z => pure (g, T, z)
    with hpacked
  have hbad : badGame IV sb seedGen prog₁ = packed >>= fun y => rho seedGen >>= fun r =>
      pure (decide (r.2 = IV) || y.2.2.2.any (badQ IV (sb r.1) r.2 y.1 y.2.1)) := by
    simp only [badGame, hpacked, rho, bind_assoc, pure_bind, bind_map_left]
  have hflag : Pr{let y ← packed}[y.2.2.2.any (hasIV IV y.1 y.2.1) = true] ≤
      ((q₁ + C * (1 + L) : ℕ) : ℝ≥0∞) * (Fintype.card St : ℝ≥0∞)⁻¹ := by
    refine le_of_eq_of_le ?_ (prEvent_trace_hasIV_le IV prog₁ q₁ C L hq hC hL)
    rw [← prT_bind_pure]
    simp only [hpacked, bind_assoc, pure_bind]
  rw [hbad]
  refine (prT_bind_le_prEvent_add packed _
    (fun y => y.2.2.2.any (hasIV IV y.1 y.2.1) = true)
    (ε := (Fintype.card St : ℝ≥0∞)⁻¹ + ((q₁ : ℝ≥0∞) * (γ + (Fintype.card St : ℝ≥0∞)⁻¹) +
        (C : ℝ≥0∞) * ((L : ℝ≥0∞) * (Fintype.card St : ℝ≥0∞)⁻¹))) ?_).trans ?_
  · rintro ⟨g, T, z⟩ hy hno
    simp only [hpacked, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hy
    obtain ⟨g', -, T', -, z', hz, heq⟩ := hy
    obtain ⟨rfl, rfl, rfl⟩ := Prod.mk.inj heq |>.imp id fun h => Prod.mk.inj h
    rw [prT_bind_pure]
    have h1 := trace_countP_le (pairAns g (chainI g T)) (fun i => isPub i = true) prog₁ q₁ hq
      [] z hz
    have h2 := trace_countP_le (pairAns g (chainI g T)) (fun i => isChain i = true) prog₁ C hC
      [] z hz
    have h3 := trace_forall (pairAns g (chainI g T)) (chainLenLe L) prog₁ hL [] (by simp) z hz
    exact prEvent_bad_fixed_le IV sb hsb seedGen γ hγ g T q₁ C L z.2 (by simpa using h1)
      (by simpa using h2) h3 (by simpa using hno)
  · refine (add_le_add hflag le_rfl).trans (le_of_eq ?_)
    push_cast
    ring

end Ideal.HP

#print axioms Ideal.HP.prT_badGame_le
