import Reduction.Open.WotsCountsSM

/-!
# From counter growth in every run to a syntactic query bound

The collection / challenge counts of the WOTS first phases (`Reduction/Open/WotsCounts*.lean`)
are stated semantically: in every run of the simulator inside a game `O₂` (any oracle on any
state with a counter growing by at most one per counted query), the counter grows by at most
`N` (`simChoose_bWotsWith_count`).  A syntactic `IsQueryBoundP` bound follows by running the
program against a **universal counting oracle** `univO samp c`: every answer is possible
(`samp t` has full support) and the state counts the queries.

* `univO`, `univ_step_shift`, `univ_run_shift` (the runs from `σ` are those from `0` shifted);
* `qb_of_univ`: if every run from `0` ends with counter `≤ N`, the program makes at most `N`
  counted queries;
* `optU` — a full-support sampler of `Option Y`.
-/

open OracleComp OracleSpec

namespace Ideal.Realize.Wots

open Reduction WotsFinal

section Univ

variable {ι : Type} {spec : OracleSpec ι}

/-- The universal counting oracle: answers from `samp t`, counter raised by `c t`. -/
noncomputable def univO (samp : (t : ι) → ProbComp (spec.Range t)) (c : ι → ℕ) :
    QueryImpl spec (StateT ℕ ProbComp) :=
  fun t => StateT.mk fun σ => (fun r => (r, σ + c t)) <$> samp t

variable (samp : (t : ι) → ProbComp (spec.Range t)) (c : ι → ℕ)

theorem univ_outer_inl (n : ℕ) (σ : ℕ) :
    (outer (univO samp c) (.inl n)).run σ =
      (fun u => (u, σ)) <$> (liftM (unifSpec.query n) : ProbComp _) := by
  simp [outer]

theorem univ_outer_inr (t : ι) (σ : ℕ) :
    (outer (univO samp c) (.inr t)).run σ = (fun r => (r, σ + c t)) <$> samp t := by
  simp [outer, univO]

theorem univ_step_shift (t : ℕ ⊕ ι) (σ : ℕ) :
    (outer (univO samp c) t).run σ =
      (fun p => (p.1, p.2 + σ)) <$> (outer (univO samp c) t).run 0 := by
  rcases t with n | t
  · rw [univ_outer_inl, univ_outer_inl, Functor.map_map]
    simp
  · rw [univ_outer_inr, univ_outer_inr, Functor.map_map]
    congr 1
    funext r
    simp [Nat.add_comm]

theorem univ_run_shift {α : Type} (oa : OracleComp (unifSpec + spec) α) (σ : ℕ) :
    (simulateQ (outer (univO samp c)) oa).run σ =
      (fun p => (p.1, p.2 + σ)) <$> (simulateQ (outer (univO samp c)) oa).run 0 := by
  induction oa using OracleComp.inductionOn generalizing σ with
  | pure x => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rw [univ_step_shift samp c t σ, bind_map_left, map_bind]
    refine bind_congr fun p => ?_
    rw [ih p.1 (p.2 + σ), ih p.1 p.2, Functor.map_map]
    congr 1
    funext q
    simp [Nat.add_assoc]

/-- The count of one query: `0` for sampling, `c t` otherwise. -/
def cnt (c : ι → ℕ) : ℕ ⊕ ι → ℕ
  | .inl _ => 0
  | .inr t => c t

theorem univ_mem (hs : ∀ t, support (samp t) = Set.univ) (t : ℕ ⊕ ι)
    (u : (unifSpec + spec).Range t) :
    (u, cnt c t) ∈ support ((outer (univO samp c) t).run 0) := by
  rcases t with n | t
  · rw [univ_outer_inl, support_map]
    exact ⟨u, mem_support_query _ _, rfl⟩
  · rw [univ_outer_inr, support_map]
    exact ⟨u, by rw [hs]; trivial, by simp [cnt]⟩

/-- **Semantic → syntactic.**  If every run of `oa` against the universal counting oracle,
started at `0`, ends with counter `≤ N`, then `oa` makes at most `N` queries satisfying `pc`
(`c` counts exactly the `pc`-queries of `spec`; sampling queries are not counted). -/
theorem qb_of_univ (hs : ∀ t, support (samp t) = Set.univ) (pc : ℕ ⊕ ι → Prop)
    [DecidablePred pc] (hc : ∀ t, c t = if pc (.inr t) then 1 else 0)
    (hu : ∀ n, ¬ pc (.inl n)) {α : Type} (oa : OracleComp (unifSpec + spec) α) (N : ℕ)
    (h : ∀ z ∈ support ((simulateQ (outer (univO samp c)) oa).run 0), z.2 ≤ N) :
    IsQueryBoundP oa pc N := by
  induction oa using OracleComp.inductionOn generalizing N with
  | pure x => exact isQueryBoundP_pure _ _ _
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff]
    have hct : cnt c t = if pc t then 1 else 0 := by
      rcases t with n | t
      · simp [cnt, hu n]
      · exact hc t
    -- every continuation run, shifted by the step's count, is a run of the whole program
    have hk : ∀ u, ∀ z ∈ support ((simulateQ (outer (univO samp c)) (k u)).run 0),
        z.2 + (if pc t then 1 else 0) ≤ N := by
      intro u z hz
      have hmem := univ_mem samp c hs t u
      rw [hct] at hmem
      apply h (z.1, z.2 + (if pc t then 1 else 0))
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      refine (mem_support_bind_iff _ _ _).2 ⟨_, hmem, ?_⟩
      rw [univ_run_shift samp c (k u), support_map]
      exact ⟨z, hz, rfl⟩
    refine ⟨?_, fun u => ih u _ fun z hz => ?_⟩
    · by_cases hp : pc t
      · refine Or.inr ?_
        obtain ⟨u, -⟩ := (support_nonempty ((outer (univO samp c) t).run 0))
        obtain ⟨z, hz⟩ := support_nonempty ((simulateQ (outer (univO samp c)) (k u.1)).run 0)
        have := hk u.1 z hz
        simp only [hp, ite_true] at this
        omega
      · exact Or.inl hp
    · have := hk u z hz
      by_cases hp : pc t <;> simp only [hp, ite_true, ite_false] at this ⊢ <;> omega

end Univ

/-- A full-support sampler of `Option Y`. -/
noncomputable def optU (Y : Type) [SampleableType Y] : ProbComp (Option Y) := do
  let b ← ($ᵗ Bool : ProbComp Bool)
  if b then some <$> ($ᵗ Y : ProbComp Y) else pure none

theorem support_optU (Y : Type) [SampleableType Y] : support (optU Y) = Set.univ := by
  ext o
  simp only [Set.mem_univ, iff_true]
  unfold optU
  rw [mem_support_bind_iff]
  rcases o with _ | y
  · exact ⟨false, mem_support_uniformSample _, by simp⟩
  · exact ⟨true, mem_support_uniformSample _, by simp⟩

end Ideal.Realize.Wots

#print axioms Ideal.Realize.Wots.qb_of_univ
#print axioms Ideal.Realize.Wots.support_optU
