import Ideal.Core.HPBad

/-!
# Generic lemmas for the PRF game in the ideal-compression model

All lemmas are about programs run against *answer functions* (`HP.ansImpl`, `HP.trImpl`) that
are computed from eagerly sampled uniform tables.

* `mix cs t g`: the table `g` with the cells in the list `cs` frozen to the values of `t`;
  `prT_freeze`: freezing one more cell of a uniform table to a fresh uniform value.
* `prT_coll_le` (birthday bound): a program making at most `n` oracle queries, each of which
  reads one cell of a uniform table `g`, touches two distinct cells with equal `g`-values with
  probability at most `n² / |V|`.
* `prT_rename_le` (lazy random function under a renaming of its inputs): answering `d` by
  `out (T (φ d))` for a uniform table `T` is the same as answering `d` by `R d` for a uniform
  table `R`, unless two distinct queried inputs collide under `φ`.
-/

open OracleComp OracleSpec ENNReal

namespace Ideal.Prf

open Ideal.HP

variable {C V α : Type}

/-! ## Small `prT` facts -/

theorem prT_bind_pure_mono {ρ : Type} (mx : ProbComp ρ) (p p' : ρ → Bool)
    (h : ∀ x, p x = true → p' x = true) :
    prT (mx >>= fun x => pure (p x)) ≤ prT (mx >>= fun x => pure (p' x)) := by
  rw [prT_bind_pure, prT_bind_pure]
  exact prEvent_mono mx _ _ h

theorem prT_bind_pure_false {ρ : Type} (mx : ProbComp ρ) : prT (mx >>= fun _ => pure false) = 0 := by
  rw [prT_bind_const, prT_pure]
  rfl

/-! ## Frozen cells -/

section Mix

variable [DecidableEq C]

/-- The table `g` with the cells of `cs` frozen to the values of `t`. -/
def mix (cs : List C) (t g : C → V) : C → V := fun c => if c ∈ cs then t c else g c

theorem mix_nil (t g : C → V) : mix [] t g = g := by
  funext c
  simp [mix]

theorem mix_of_mem {cs : List C} {c : C} (h : c ∈ cs) (t g : C → V) : mix cs t g c = t c := by
  simp [mix, h]

theorem mix_of_not_mem {cs : List C} {c : C} (h : c ∉ cs) (t g : C → V) : mix cs t g c = g c := by
  simp [mix, h]

theorem mix_append_of_mem {cs : List C} {c : C} (h : c ∈ cs) (t g : C → V) :
    mix (cs ++ [c]) t g = mix cs t g := by
  funext c'
  by_cases hc : c' = c
  · subst hc; simp [mix, h]
  · simp [mix, hc]

theorem mix_append_self (cs : List C) (c : C) (t g : C → V) (v : V) :
    mix (cs ++ [c]) (Function.update t c v) g c = v := by
  simp [mix]

theorem mix_update {cs : List C} {c : C} (h : c ∉ cs) (t g : C → V) (v : V) :
    mix cs t (Function.update g c v) = mix (cs ++ [c]) (Function.update t c v) g := by
  funext c'
  by_cases hc : c' = c
  · subst hc; simp [mix, h]
  · by_cases hm : c' ∈ cs <;> simp [mix, hc, hm]

/-- Freeze one more cell of a uniform table to a fresh uniform value. -/
theorem prT_freeze [Finite C] [SampleableType V] [SampleableType (C → V)] {cs : List C} {c : C}
    (h : c ∉ cs) (t : C → V) (F : (C → V) → ProbComp Bool) :
    prT ($ᵗ (C → V) >>= fun g => F (mix cs t g)) =
      prT ($ᵗ V >>= fun v => $ᵗ (C → V) >>= fun g =>
        F (mix (cs ++ [c]) (Function.update t c v) g)) := by
  let : MeasurableSpace V := ⊤
  refine prT_congr ?_
  have hb := evalDist_bind_bind_update ($ᵗ V) ($ᵗ (C → V))
    SampleableType.evalDist_uniformSample SampleableType.evalDist_uniformSample c
    (fun g => F (mix cs t g))
  rw [← hb]
  simp only [mix_update h]

end Mix

/-! ## Birthday bound for adaptive readers of a uniform table -/

section Coll

theorem prEvent_mem_values_le [Fintype V] [SampleableType V] (t : C → V) (cs : List C) :
    Pr{let v ← $ᵗ V}[∃ c' ∈ cs, v = t c'] ≤
      (cs.length : ℝ≥0∞) * (Fintype.card V : ℝ≥0∞)⁻¹ := by
  refine (prEvent_list_exists_le ($ᵗ V) (fun v c' => v = t c')
    (fun _ => (Fintype.card V : ℝ≥0∞)⁻¹) cs fun c' _ =>
      (SampleableType.prEvent_uniformSample_eq_singleton (t c')).le).trans (le_of_eq ?_)
  simp

variable [DecidableEq C] [DecidableEq V] {ι : Type} {spec : OracleSpec ι}

/-- Two distinct cells of the list have equal `g`-values. -/
def collB (g : C → V) (cs : List C) : Bool :=
  decide (∃ c ∈ cs, ∃ c' ∈ cs, c ≠ c' ∧ g c = g c')

/-- **Birthday bound.**  Every oracle query `t` reads the cell `cell t` of a uniform table (its
answer depends on the table through that cell only).  A program making at most `n` oracle
queries touches two distinct cells with equal table values with probability at most
`n * (|l| + n) / |V|`, where `l` is the trace so far, whose cells are frozen to
collision-free values. -/
theorem prT_coll_le_aux [Fintype V] [SampleableType V] [Finite C] [SampleableType (C → V)]
    (cell : ι → C) (ans : (C → V) → (t : ι) → spec.Range t)
    (hans : ∀ g g' t, g (cell t) = g' (cell t) → ans g t = ans g' t)
    (oa : OracleComp (unifSpec + spec) α) (n : ℕ)
    (hn : IsQueryBoundP oa (fun i => i.isRight = true) n) (l : List ι) (t : C → V)
    (hno : ∀ c ∈ l.map cell, ∀ c' ∈ l.map cell, c ≠ c' → t c ≠ t c') :
    prT ($ᵗ (C → V) >>= fun g =>
        (simulateQ (trImpl (ans (mix (l.map cell) t g))) oa).run l >>= fun z =>
          pure (collB (mix (l.map cell) t g) (z.2.map cell))) ≤
      ((n * (l.length + n) : ℕ) : ℝ≥0∞) * (Fintype.card V : ℝ≥0∞)⁻¹ := by
  induction oa using OracleComp.inductionOn generalizing n l t with
  | pure x =>
    have h0 : ∀ g : C → V, collB (mix (l.map cell) t g) (l.map cell) = false := by
      intro g
      simp only [collB, decide_eq_false_iff_not]
      rintro ⟨c, hc, c', hc', hne, heq⟩
      rw [mix_of_mem hc, mix_of_mem hc'] at heq
      exact hno c hc c' hc' hne heq
    simp only [simulateQ_pure, StateT.run_pure, pure_bind, h0]
    rw [prT_bind_pure_false]
    exact zero_le
  | query_bind t₀ k ih =>
    rw [isQueryBoundP_query_bind_iff] at hn
    rcases t₀ with m | t₀
    · simp only [run_stImpl_inl_bind, bind_assoc]
      rw [prT_swap]
      refine prT_bind_le_of_forall_le _ _ fun x _ => ?_
      exact ih x n (hn.2 x) l t hno
    · have hpos : 0 < n := hn.1.resolve_left (by simp)
      have hk := fun x => hn.2 x
      simp only [Sum.isRight_inr, ite_true] at hk
      by_cases hc : cell t₀ ∈ l.map cell
      · -- the cell is already frozen
        have hans' : ∀ g : C → V, ans (mix (l.map cell) t g) t₀ = ans t t₀ := fun g =>
          hans _ _ _ (mix_of_mem hc t g)
        simp only [run_stImpl_inr_bind, hans']
        have hno' : ∀ c ∈ (l ++ [t₀]).map cell, ∀ c' ∈ (l ++ [t₀]).map cell,
            c ≠ c' → t c ≠ t c' := by
          intro c hc1 c' hc2
          have e : ∀ c, c ∈ (l ++ [t₀]).map cell → c ∈ l.map cell := by
            intro c h
            simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append,
              List.mem_singleton] at h
            rcases h with h | h
            · exact h
            · rw [h]; exact hc
          exact hno c (e c hc1) c' (e c' hc2)
        have := ih (ans t t₀) (n - 1) (hk _) (l ++ [t₀]) t hno'
        simp only [List.map_append, List.map_cons, List.map_nil, mix_append_of_mem hc] at this
        refine this.trans ?_
        refine mul_le_mul_left (Nat.cast_le.mpr ?_) _
        simp only [List.length_append, List.length_cons, List.length_nil]
        rcases n with _ | m
        · omega
        · simp only [Nat.add_sub_cancel]; nlinarith
      · -- a fresh cell: freeze it to a uniform value
        rw [prT_freeze hc t (fun M =>
          (simulateQ (trImpl (ans M)) (liftM ((unifSpec + spec).query (.inr t₀)) >>= k)).run l >>=
            fun z => pure (collB M (z.2.map cell)))]
        refine (prT_bind_le_prEvent_add ($ᵗ V) _ (fun v => ∃ c' ∈ l.map cell, v = t c')
          (ε := (((n - 1) * (l.length + 1 + (n - 1)) : ℕ) : ℝ≥0∞) *
            (Fintype.card V : ℝ≥0∞)⁻¹) fun v _ hv => ?_).trans ?_
        · have hans' : ∀ g : C → V,
              ans (mix (l.map cell ++ [cell t₀]) (Function.update t (cell t₀) v) g) t₀ =
                ans (Function.update t (cell t₀) v) t₀ := fun g =>
            hans _ _ _ (mix_of_mem (by simp) _ g)
          simp only [run_stImpl_inr_bind, hans']
          have hno' : ∀ c ∈ (l ++ [t₀]).map cell, ∀ c' ∈ (l ++ [t₀]).map cell,
              c ≠ c' → Function.update t (cell t₀) v c ≠ Function.update t (cell t₀) v c' := by
            intro c hc1 c' hc2 hne
            simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append,
              List.mem_singleton] at hc1 hc2
            rcases hc1 with h1 | h1 <;> rcases hc2 with h2 | h2
            · have e1 : c ≠ cell t₀ := fun e => hc (e ▸ h1)
              have e2 : c' ≠ cell t₀ := fun e => hc (e ▸ h2)
              rw [Function.update_of_ne e1, Function.update_of_ne e2]
              exact hno c h1 c' h2 hne
            · have e1 : c ≠ cell t₀ := fun e => hc (e ▸ h1)
              rw [h2, Function.update_of_ne e1, Function.update_self]
              exact fun e => hv ⟨c, h1, e.symm⟩
            · have e2 : c' ≠ cell t₀ := fun e => hc (e ▸ h2)
              rw [h1, Function.update_of_ne e2, Function.update_self]
              exact fun e => hv ⟨c', h2, e⟩
            · exact absurd (h1.trans h2.symm) hne
          have := ih (ans (Function.update t (cell t₀) v) t₀) (n - 1) (hk _) (l ++ [t₀])
            (Function.update t (cell t₀) v) hno'
          simpa only [List.map_append, List.map_cons, List.map_nil, List.length_append,
            List.length_cons, List.length_nil, zero_add] using this
        · refine (add_le_add (prEvent_mem_values_le t (l.map cell)) le_rfl).trans ?_
          rw [← add_mul, List.length_map, ← Nat.cast_add]
          refine mul_le_mul_left (Nat.cast_le.mpr ?_) _
          rcases n with _ | m
          · omega
          · simp only [Nat.add_sub_cancel]; nlinarith

/-- **Birthday bound**, from the empty trace. -/
theorem prT_coll_le [Fintype V] [SampleableType V] [Finite C] [SampleableType (C → V)]
    (cell : ι → C) (ans : (C → V) → (t : ι) → spec.Range t)
    (hans : ∀ g g' t, g (cell t) = g' (cell t) → ans g t = ans g' t)
    (oa : OracleComp (unifSpec + spec) α) (n : ℕ)
    (hn : IsQueryBoundP oa (fun i => i.isRight = true) n) :
    prT ($ᵗ (C → V) >>= fun g => (simulateQ (trImpl (ans g)) oa).run [] >>= fun z =>
        pure (collB g (z.2.map cell))) ≤
      ((n ^ 2 : ℕ) : ℝ≥0∞) * (Fintype.card V : ℝ≥0∞)⁻¹ := by
  have h := prT_coll_le_aux cell ans hans oa n hn [] (fun _ => Classical.arbitrary V) (by simp)
  simp only [List.map_nil, mix_nil, List.length_nil, zero_add] at h
  rwa [← sq] at h

end Coll

/-! ## A random function under a renaming of its inputs -/

section Rename

variable {ι₀ : Type} {spec₀ : OracleSpec ι₀} {D E Y : Type}

/-- Answers: the side oracle by `a₀`, the function oracle at `d` by `out (T (φ d))`. -/
def ansL (a₀ : (t : ι₀) → spec₀.Range t) (φ : D → E) (out : V → Y) (T : E → V) :
    (t : ι₀ ⊕ D) → (spec₀ + (D →ₒ Y)).Range t
  | .inl t => a₀ t
  | .inr d => out (T (φ d))

/-- Answers: the side oracle by `a₀`, the function oracle by the table `R`. -/
def ansR (a₀ : (t : ι₀) → spec₀.Range t) (R : D → Y) :
    (t : ι₀ ⊕ D) → (spec₀ + (D →ₒ Y)).Range t
  | .inl t => a₀ t
  | .inr d => R d

/-- The function-oracle queries of a trace. -/
def dq (l : List (ι₀ ⊕ D)) : List D := l.filterMap Sum.getRight?

@[simp] theorem dq_nil : dq ([] : List (ι₀ ⊕ D)) = [] := rfl

@[simp] theorem dq_append_inl (l : List (ι₀ ⊕ D)) (t : ι₀) : dq (l ++ [.inl t]) = dq l := by
  simp [dq]

@[simp] theorem dq_append_inr (l : List (ι₀ ⊕ D)) (d : D) : dq (l ++ [.inr d]) = dq l ++ [d] := by
  simp [dq]

/-- Two distinct inputs of the list collide under `φ`. -/
def collφ [DecidableEq D] [DecidableEq E] (φ : D → E) (s : List D) : Bool :=
  decide (∃ d ∈ s, ∃ d' ∈ s, d ≠ d' ∧ φ d = φ d')

/-- `out` of a uniform value is uniform: change of variables under `prT`. -/
theorem prT_bind_out [SampleableType V] [SampleableType Y] (out : V → Y)
    (hout : ∀ p : Y → Prop, Pr{let u ← $ᵗ V}[p (out u)] = Pr{let y ← $ᵗ Y}[p y])
    (G : Y → ProbComp Bool) :
    prT ($ᵗ V >>= fun v => G (out v)) = prT ($ᵗ Y >>= G) := by
  let : MeasurableSpace Y := ⊤
  have h1 : (out <$> ($ᵗ V : ProbComp V)) =ᵈ ($ᵗ Y : ProbComp Y) := by
    apply OracleComp.evalDistEq_of_forall_prEvent_eq_output
    intro y
    rw [prEvent_map]
    exact hout (· = y)
  have h2 : 𝒟[out <$> ($ᵗ V : ProbComp V)] = 𝒟[($ᵗ Y : ProbComp Y)] :=
    evalDistEq_iff_evalDist_eq.mp h1
  refine prT_congr ?_
  have h3 : ($ᵗ V >>= fun v => G (out v)) = (out <$> ($ᵗ V : ProbComp V)) >>= G := by
    rw [bind_map_left]
  rw [h3, evalDist_bind_of_discrete _ G, evalDist_bind_of_discrete _ G, h2]

variable [DecidableEq D] [DecidableEq E]

/-- **Renaming lemma** (generalised over the trace so far, whose function-oracle inputs are
frozen consistently in both tables and do not collide under `φ`). -/
theorem prT_rename_le_aux [Finite D] [Finite E] [SampleableType V] [SampleableType Y]
    [SampleableType (E → V)] [SampleableType (D → Y)]
    (a₀ : (t : ι₀) → spec₀.Range t) (φ : D → E) (out : V → Y)
    (hout : ∀ p : Y → Prop, Pr{let u ← $ᵗ V}[p (out u)] = Pr{let y ← $ᵗ Y}[p y])
    (oa : OracleComp (unifSpec + (spec₀ + (D →ₒ Y))) Bool) (l : List (ι₀ ⊕ D))
    (tL : E → V) (tR : D → Y) (hcons : ∀ d ∈ dq l, out (tL (φ d)) = tR d)
    (hno : ∀ d ∈ dq l, ∀ d' ∈ dq l, φ d = φ d' → d = d') :
    prT ($ᵗ (E → V) >>= fun T =>
        simulateQ (ansImpl (ansL a₀ φ out (mix ((dq l).map φ) tL T))) oa) ≤
      prT ($ᵗ (D → Y) >>= fun R => simulateQ (ansImpl (ansR a₀ (mix (dq l) tR R))) oa) +
        prT ($ᵗ (D → Y) >>= fun R =>
          (simulateQ (trImpl (ansR a₀ (mix (dq l) tR R))) oa).run l >>= fun z =>
            pure (collφ φ (dq z.2))) := by
  induction oa using OracleComp.inductionOn generalizing l tL tR with
  | pure x =>
    simp only [simulateQ_pure]
    rw [prT_bind_const, prT_bind_const]
    exact le_self_add
  | query_bind t₀ k ih =>
    rcases t₀ with m | t₀ | d
    · simp only [simulateQ_ansImpl_inl_bind, run_stImpl_inl_bind, bind_assoc]
      rw [prT_swap, prT_swap ($ᵗ (D → Y)), prT_swap ($ᵗ (D → Y))]
      exact prT_bind_le_add _ _ _ _ fun x => ih x l tL tR hcons hno
    · simp only [simulateQ_ansImpl_inr_bind, run_stImpl_inr_bind]
      have := ih (a₀ t₀) (l ++ [.inl t₀]) tL tR (by simpa using hcons) (by simpa using hno)
      simp only [dq_append_inl] at this
      exact this
    · by_cases hd : d ∈ dq l
      · -- a repeated input: both sides answer with the frozen value
        have hL : ∀ T : E → V,
            ansL a₀ φ out (mix ((dq l).map φ) tL T) (.inr d) = tR d := fun T => by
          show out (mix ((dq l).map φ) tL T (φ d)) = tR d
          rw [mix_of_mem (List.mem_map_of_mem hd), hcons d hd]
        have hR : ∀ R : D → Y, ansR a₀ (mix (dq l) tR R) (.inr d) = tR d := fun R =>
          mix_of_mem hd tR R
        simp only [simulateQ_ansImpl_inr_bind, run_stImpl_inr_bind, hL, hR]
        have hmem : ∀ d', d' ∈ dq (l ++ [.inr d]) → d' ∈ dq l := by
          intro d' h
          rw [dq_append_inr, List.mem_append, List.mem_singleton] at h
          rcases h with h | h
          · exact h
          · rw [h]; exact hd
        have := ih (tR d) (l ++ [.inr d]) tL tR (fun d' h => hcons d' (hmem d' h))
          (fun d₁ h₁ d₂ h₂ => hno d₁ (hmem d₁ h₁) d₂ (hmem d₂ h₂))
        simpa only [dq_append_inr, List.map_append, List.map_cons, List.map_nil,
          mix_append_of_mem hd, mix_append_of_mem (List.mem_map_of_mem (f := φ) hd)] using this
      · by_cases hφ : φ d ∈ (dq l).map φ
        · -- a new input colliding with an old one: the bad event is certain
          obtain ⟨d', hd', hφ'⟩ := List.mem_map.mp hφ
          have h1 : prT ($ᵗ (D → Y) >>= fun R =>
              (simulateQ (trImpl (ansR a₀ (mix (dq l) tR R)))
                (liftM ((unifSpec + (spec₀ + (D →ₒ Y))).query (.inr (.inr d))) >>= k)).run l >>=
                fun z => pure (collφ φ (dq z.2))) = 1 := by
            refine prT_eq_one_of_support _ fun b hb => ?_
            rw [mem_support_bind_iff] at hb
            obtain ⟨R, -, hb⟩ := hb
            rw [run_stImpl_inr_bind, mem_support_bind_iff] at hb
            obtain ⟨z, hz, hb⟩ := hb
            simp only [support_pure, Set.mem_singleton_iff] at hb
            have := run_stImpl_inv (ansR a₀ (mix (dq l) tR R)) (fun t l => l ++ [t])
              (fun l' => collφ φ (dq l') = true)
              (fun t s hs => by
                simp only [collφ, decide_eq_true_eq] at hs ⊢
                obtain ⟨d₁, h₁, d₂, h₂, hne, heq⟩ := hs
                have hsub : ∀ x, x ∈ dq s → x ∈ dq (s ++ [t]) := fun x hx => by
                  rcases t with t | t
                  · simpa using hx
                  · simp [hx]
                exact ⟨d₁, hsub _ h₁, d₂, hsub _ h₂, hne, heq⟩)
              (k _) (l ++ [.inr d])
              (by
                simp only [collφ, decide_eq_true_eq, dq_append_inr]
                exact ⟨d', by simp [hd'], d, by simp, fun e => hd (e ▸ hd'), hφ'⟩) z hz
            rw [hb, this]
          rw [h1]
          exact (prT_le_one _).trans le_add_self
        · -- a fresh input: freeze the two cells to coupled uniform values
          rw [prT_freeze hφ tL (fun M => simulateQ (ansImpl (ansL a₀ φ out M))
              (liftM ((unifSpec + (spec₀ + (D →ₒ Y))).query (.inr (.inr d))) >>= k)),
            prT_freeze hd tR (fun M => simulateQ (ansImpl (ansR a₀ M))
              (liftM ((unifSpec + (spec₀ + (D →ₒ Y))).query (.inr (.inr d))) >>= k)),
            prT_freeze hd tR (fun M => (simulateQ (trImpl (ansR a₀ M))
              (liftM ((unifSpec + (spec₀ + (D →ₒ Y))).query (.inr (.inr d))) >>= k)).run l >>=
                fun z => pure (collφ φ (dq z.2)))]
          have hL : ∀ (v : V) (T : E → V), ansL a₀ φ out
              (mix ((dq l).map φ ++ [φ d]) (Function.update tL (φ d) v) T) (.inr d) = out v :=
            fun v T => congrArg out (mix_append_self _ _ _ _ _)
          have hR : ∀ (y : Y) (R : D → Y),
              ansR a₀ (mix (dq l ++ [d]) (Function.update tR d y) R) (.inr d) = y :=
            fun y R => mix_append_self _ _ _ _ _
          simp only [simulateQ_ansImpl_inr_bind, run_stImpl_inr_bind, hL, hR]
          have e2 := prT_bind_out out hout (fun y => $ᵗ (D → Y) >>= fun R =>
              (simulateQ (trImpl (ansR a₀ (mix (dq l ++ [d]) (Function.update tR d y) R)))
                (k y)).run (l ++ [(Sum.inr d : ι₀ ⊕ D)]) >>= fun z => pure (collφ φ (dq z.2)))
          have e1 := prT_bind_out out hout (fun y => $ᵗ (D → Y) >>= fun R =>
              simulateQ (ansImpl (ansR a₀ (mix (dq l ++ [d]) (Function.update tR d y) R))) (k y))
          refine le_trans ?_ (le_of_eq (congrArg₂ (· + ·) e1 e2))
          refine prT_bind_le_add _ _ _ _ fun v => ?_
          have hcons' : ∀ d' ∈ dq (l ++ [.inr d]),
              out (Function.update tL (φ d) v (φ d')) = Function.update tR d (out v) d' := by
            intro d' h
            rw [dq_append_inr, List.mem_append, List.mem_singleton] at h
            rcases h with h | h
            · have e1 : φ d' ≠ φ d := fun e => hφ (e ▸ List.mem_map_of_mem h)
              have e2 : d' ≠ d := fun e => hd (e ▸ h)
              rw [Function.update_of_ne e1, Function.update_of_ne e2]
              exact hcons d' h
            · rw [h, Function.update_self, Function.update_self]
          have hno' : ∀ d₁ ∈ dq (l ++ [.inr d]), ∀ d₂ ∈ dq (l ++ [.inr d]),
              φ d₁ = φ d₂ → d₁ = d₂ := by
            intro d₁ h₁ d₂ h₂ heq
            rw [dq_append_inr, List.mem_append, List.mem_singleton] at h₁ h₂
            rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
            · exact hno d₁ h₁ d₂ h₂ heq
            · exact absurd (List.mem_map_of_mem (f := φ) h₁) (by rw [heq, h₂]; exact hφ)
            · exact absurd (List.mem_map_of_mem (f := φ) h₂) (by rw [← heq, h₁]; exact hφ)
            · rw [h₁, h₂]
          have := ih (out v) (l ++ [.inr d]) (Function.update tL (φ d) v)
            (Function.update tR d (out v)) hcons' hno'
          simpa only [dq_append_inr, List.map_append, List.map_cons, List.map_nil] using this

/-- **Renaming lemma.**  Answering the function oracle at `d` by `out (T (φ d))` for a uniform
table `T` wins at most as often as answering it from a uniform table `R`, plus the probability
that two distinct queried inputs collide under `φ` in the latter run. -/
theorem prT_rename_le [Finite D] [Finite E] [SampleableType V] [SampleableType Y]
    [SampleableType (E → V)] [SampleableType (D → Y)]
    (a₀ : (t : ι₀) → spec₀.Range t) (φ : D → E) (out : V → Y)
    (hout : ∀ p : Y → Prop, Pr{let u ← $ᵗ V}[p (out u)] = Pr{let y ← $ᵗ Y}[p y])
    (oa : OracleComp (unifSpec + (spec₀ + (D →ₒ Y))) Bool) :
    prT ($ᵗ (E → V) >>= fun T => simulateQ (ansImpl (ansL a₀ φ out T)) oa) ≤
      prT ($ᵗ (D → Y) >>= fun R => simulateQ (ansImpl (ansR a₀ R)) oa) +
        prT ($ᵗ (D → Y) >>= fun R => (simulateQ (trImpl (ansR a₀ R)) oa).run [] >>= fun z =>
          pure (collφ φ (dq z.2))) := by
  have h := prT_rename_le_aux a₀ φ out hout oa [] (fun _ => Classical.arbitrary V)
    (fun _ => Classical.arbitrary Y) (by simp) (by simp)
  simpa only [dq_nil, List.map_nil, mix_nil] using h

end Rename

end Ideal.Prf

#print axioms Ideal.Prf.prT_coll_le
#print axioms Ideal.Prf.prT_rename_le
