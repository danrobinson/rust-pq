import Ideal.Games.MsgPrfLemmas

/-!
# A lazy random function under a renaming of its inputs

`prT_lazy_rename_le`: answering the function oracle at `d` by `out (T (φ d))` for a uniform table
`T : E → V` (`E` finite) wins at most as often as answering it by a lazy random function on `D`
(`D` arbitrary, possibly infinite), plus the probability that two distinct queried inputs collide
under `φ` in the *former* run.
-/

open OracleComp OracleSpec ENNReal

namespace Ideal.MsgPrf

open Ideal.HP Ideal.Prf

variable {St Blk D E V Y : Type}

section Inst

variable {ι : Type} {spec : OracleSpec ι} {α : Type}

theorem simulateQ_instImpl_inl_bind (g : CF St Blk) (m : ℕ)
    (k : (unifSpec + (hS St Blk + spec)).Range (.inl m) →
      OracleComp (unifSpec + (hS St Blk + spec)) α) :
    simulateQ (instImpl g) (liftM ((unifSpec + (hS St Blk + spec)).query (.inl m)) >>= k) =
      liftM ((unifSpec + spec).query (.inl m)) >>= fun u => simulateQ (instImpl g) (k u) := by
  rw [simulateQ_bind, simulateQ_spec_query]
  rfl

theorem simulateQ_instImpl_comp_bind (g : CF St Blk) (q : St × Blk)
    (k : (unifSpec + (hS St Blk + spec)).Range (.inr (.inl q)) →
      OracleComp (unifSpec + (hS St Blk + spec)) α) :
    simulateQ (instImpl g) (liftM ((unifSpec + (hS St Blk + spec)).query (.inr (.inl q))) >>= k) =
      simulateQ (instImpl g) (k (g q)) := by
  rw [simulateQ_bind, simulateQ_spec_query]
  exact pure_bind _ _

theorem simulateQ_instImpl_orc_bind (g : CF St Blk) (t : ι)
    (k : (unifSpec + (hS St Blk + spec)).Range (.inr (.inr t)) →
      OracleComp (unifSpec + (hS St Blk + spec)) α) :
    simulateQ (instImpl g) (liftM ((unifSpec + (hS St Blk + spec)).query (.inr (.inr t))) >>= k) =
      liftM ((unifSpec + spec).query (.inr t)) >>= fun u => simulateQ (instImpl g) (k u) := by
  rw [simulateQ_bind, simulateQ_spec_query]
  rfl

end Inst

variable [DecidableEq D] [DecidableEq E]

/-- **Lazy renaming lemma** (generalised over the trace so far: the function-oracle inputs of the
trace are exactly the cached inputs, their cached values are the images of the frozen cells, and
they do not collide under `φ`). -/
theorem prT_lazy_rename_le_aux [Finite E] [SampleableType V] [SampleableType Y]
    [SampleableType (E → V)] (g : CF St Blk) (φ : D → E) (out : V → Y)
    (hout : ∀ p : Y → Prop, Pr{let u ← $ᵗ V}[p (out u)] = Pr{let y ← $ᵗ Y}[p y])
    (oa : OracleComp (unifSpec + (hS St Blk + (D →ₒ Y))) Bool) (l : List ((St × Blk) ⊕ D))
    (tL : E → V) (cD : (D →ₒ Y).QueryCache)
    (hdom : ∀ d, d ∈ dq l ↔ cD d ≠ none)
    (hcons : ∀ d ∈ dq l, cD d = some (out (tL (φ d))))
    (hno : ∀ d ∈ dq l, ∀ d' ∈ dq l, φ d = φ d' → d = d') :
    prT ($ᵗ (E → V) >>= fun T => simulateQ (ansImpl
        (ansL (spec₀ := hS St Blk) (fun q => g q) φ out (mix ((dq l).map φ) tL T))) oa) ≤
      prT ((simulateQ (D →ₒ Y).romImpl (simulateQ (instImpl g) oa)).run' cD) +
        prT ($ᵗ (E → V) >>= fun T => (simulateQ (trImpl
          (ansL (spec₀ := hS St Blk) (fun q => g q) φ out (mix ((dq l).map φ) tL T))) oa).run l >>=
            fun z => pure (collφ φ (dq z.2))) := by
  induction oa using OracleComp.inductionOn generalizing l tL cD with
  | pure x =>
    simp only [simulateQ_pure]
    rw [prT_bind_const]
    refine le_trans (le_of_eq ?_) le_self_add
    simp
  | query_bind t₀ k ih =>
    rcases t₀ with m | q | d
    · simp only [simulateQ_ansImpl_inl_bind, run_stImpl_inl_bind, bind_assoc]
      rw [simulateQ_instImpl_inl_bind, run'_romImpl_inl_bind, prT_swap, prT_swap ($ᵗ (E → V))]
      exact prT_bind_le_add _ _ _ _ fun x => ih x l tL cD hdom hcons hno
    · simp only [simulateQ_ansImpl_inr_bind, run_stImpl_inr_bind]
      rw [simulateQ_instImpl_comp_bind]
      have := ih (g q) (l ++ [.inl q]) tL cD (by simpa using hdom) (by simpa using hcons)
        (by simpa using hno)
      simp only [dq_append_inl] at this
      exact this
    · rw [simulateQ_instImpl_orc_bind, run'_romImpl_inr_bind]
      by_cases hd : d ∈ dq l
      · -- a repeated input: both sides answer with the cached value
        have hc : cD d = some (out (tL (φ d))) := hcons d hd
        rw [QueryImpl.withCaching_run_some _ hc, pure_bind]
        have hL : ∀ T : E → V, ansL (spec₀ := hS St Blk) (fun q => g q) φ out
            (mix ((dq l).map φ) tL T) (.inr d) = out (tL (φ d)) := fun T => by
          show out (mix ((dq l).map φ) tL T (φ d)) = _
          rw [mix_of_mem (List.mem_map_of_mem hd)]
        simp only [simulateQ_ansImpl_inr_bind, run_stImpl_inr_bind, hL]
        have hmem : ∀ d', d' ∈ dq (l ++ [.inr d]) ↔ d' ∈ dq l := by
          intro d'
          rw [dq_append_inr, List.mem_append, List.mem_singleton]
          constructor
          · rintro (h | h)
            · exact h
            · rw [h]; exact hd
          · exact Or.inl
        have := ih (out (tL (φ d))) (l ++ [.inr d]) tL cD
          (fun d' => (hmem d').trans (hdom d'))
          (fun d' h => hcons d' ((hmem d').mp h))
          (fun d₁ h₁ d₂ h₂ => hno d₁ ((hmem d₁).mp h₁) d₂ ((hmem d₂).mp h₂))
        simpa only [dq_append_inr, List.map_append, List.map_cons, List.map_nil,
          mix_append_of_mem (List.mem_map_of_mem (f := φ) hd)] using this
      · have hc : cD d = none := by
          by_contra h
          exact hd ((hdom d).mpr h)
        by_cases hφ : φ d ∈ (dq l).map φ
        · -- a new input colliding with an old one: the bad event is certain
          obtain ⟨d', hd', hφ'⟩ := List.mem_map.mp hφ
          have h1 : prT ($ᵗ (E → V) >>= fun T => (simulateQ (trImpl
              (ansL (spec₀ := hS St Blk) (fun q => g q) φ out (mix ((dq l).map φ) tL T)))
                (liftM ((unifSpec + (hS St Blk + (D →ₒ Y))).query (.inr (.inr d))) >>= k)).run l >>=
                fun z => pure (collφ φ (dq z.2))) = 1 := by
            refine prT_eq_one_of_support _ fun b hb => ?_
            rw [mem_support_bind_iff] at hb
            obtain ⟨T, -, hb⟩ := hb
            rw [run_stImpl_inr_bind, mem_support_bind_iff] at hb
            obtain ⟨z, hz, hb⟩ := hb
            simp only [support_pure, Set.mem_singleton_iff] at hb
            have := run_stImpl_inv
              (ansL (spec₀ := hS St Blk) (fun q => g q) φ out (mix ((dq l).map φ) tL T))
              (fun t l => l ++ [t]) (fun l' => collφ φ (dq l') = true)
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
        · -- a fresh input: couple the frozen cell with the lazily sampled answer
          rw [QueryImpl.withCaching_run_none _ hc, bind_map_left, uniformSampleImpl_apply]
          rw [prT_freeze hφ tL (fun M => simulateQ (ansImpl
                (ansL (spec₀ := hS St Blk) (fun q => g q) φ out M))
              (liftM ((unifSpec + (hS St Blk + (D →ₒ Y))).query (.inr (.inr d))) >>= k)),
            prT_freeze hφ tL (fun M => (simulateQ (trImpl
                (ansL (spec₀ := hS St Blk) (fun q => g q) φ out M))
              (liftM ((unifSpec + (hS St Blk + (D →ₒ Y))).query (.inr (.inr d))) >>= k)).run l >>=
                fun z => pure (collφ φ (dq z.2)))]
          have hL : ∀ (v : V) (T : E → V), ansL (spec₀ := hS St Blk) (fun q => g q) φ out
              (mix ((dq l).map φ ++ [φ d]) (Function.update tL (φ d) v) T) (.inr d) = out v :=
            fun v T => congrArg out (mix_append_self _ _ _ _ _)
          simp only [simulateQ_ansImpl_inr_bind, run_stImpl_inr_bind, hL]
          have e1 := prT_bind_out out hout (fun y =>
            (simulateQ (D →ₒ Y).romImpl (simulateQ (instImpl g) (k y))).run' (cD.cacheQuery d y))
          refine le_trans ?_ (le_of_eq (congrArg₂ (· + ·) e1 rfl))
          refine prT_bind_le_add _ _ _ _ fun v => ?_
          have hdom' : ∀ d', d' ∈ dq (l ++ [.inr d]) ↔ (cD.cacheQuery d (out v)) d' ≠ none := by
            intro d'
            rw [dq_append_inr, List.mem_append, List.mem_singleton]
            by_cases e : d' = d
            · subst e
              simp [QueryCache.cacheQuery_self]
            · rw [QueryCache.cacheQuery_of_ne _ _ e, ← hdom d']
              simp [e]
          have hcons' : ∀ d' ∈ dq (l ++ [.inr d]), (cD.cacheQuery d (out v)) d' =
              some (out (Function.update tL (φ d) v (φ d'))) := by
            intro d' h
            rw [dq_append_inr, List.mem_append, List.mem_singleton] at h
            rcases h with h | h
            · have e1 : φ d' ≠ φ d := fun e => hφ (e ▸ List.mem_map_of_mem h)
              have e2 : d' ≠ d := fun e => hd (e ▸ h)
              rw [Function.update_of_ne e1, QueryCache.cacheQuery_of_ne _ _ e2]
              exact hcons d' h
            · rw [h, Function.update_self, QueryCache.cacheQuery_self]
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
            (cD.cacheQuery d (out v)) hdom' hcons' hno'
          simpa only [dq_append_inr, List.map_append, List.map_cons, List.map_nil] using this

/-- **Lazy renaming lemma.**  Answering the function oracle at `d` by `out (T (φ d))` for a
uniform table `T` wins at most as often as answering it by a lazy random function, plus the
probability that two distinct queried inputs collide under `φ` in the former run. -/
theorem prT_lazy_rename_le [Finite E] [SampleableType V] [SampleableType Y]
    [SampleableType (E → V)] (g : CF St Blk) (φ : D → E) (out : V → Y)
    (hout : ∀ p : Y → Prop, Pr{let u ← $ᵗ V}[p (out u)] = Pr{let y ← $ᵗ Y}[p y])
    (oa : OracleComp (unifSpec + (hS St Blk + (D →ₒ Y))) Bool) :
    prT ($ᵗ (E → V) >>= fun T => simulateQ (ansImpl
        (ansL (spec₀ := hS St Blk) (fun q => g q) φ out T)) oa) ≤
      prT ((simulateQ (D →ₒ Y).romImpl (simulateQ (instImpl g) oa)).run' ∅) +
        prT ($ᵗ (E → V) >>= fun T => (simulateQ (trImpl
          (ansL (spec₀ := hS St Blk) (fun q => g q) φ out T)) oa).run [] >>=
            fun z => pure (collφ φ (dq z.2))) := by
  have h := prT_lazy_rename_le_aux g φ out hout oa [] (fun _ => Classical.arbitrary V) ∅
    (by simp) (by simp) (by simp)
  simpa only [dq_nil, List.map_nil, mix_nil] using h

end Ideal.MsgPrf

#print axioms Ideal.MsgPrf.prT_lazy_rename_le
