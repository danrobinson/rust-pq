import Ideal.Games.ItsrTape
import VCVio.CryptoFoundations.HardnessAssumptions.KeyedHash.Covering

/-!
# Two-colour coverage for an adaptive reader of a uniform table (milestone M0b, `status/DIRECT.md`)

A program reads cells of a uniformly random table `g : C → V`.  Each query carries a *colour*
fixed by the query itself, hence chosen before the value of the cell is seen: colour 0
(*candidate*, `lg₀`) or colour 1 (*coverer*, `lg₁`), or none.  A cell takes the colour of its
FIRST read (`logM2`): the colouring is predictable.  The `out`-images of the cells are digests
`Digest h a k` (a leaf and `k` digits, VCVio's ITSR model).

* `prT_tape2_le`: the values of the candidate cells and of the coverer cells, each in order of
  first read, are dominated by two INDEPENDENT tapes of `n₀` and `n₁` uniform values, for every
  event monotone in both lists.  This is `Ideal.Itsr.prT_tape_le_marked` with two marks.
* `prT_tape2_cov_le`: on two independent tapes, some candidate digest has each of its `k` digits
  matched, at its own leaf, by some coverer digest, with probability at most
  `n₀ · targetCoverBound h a k n₁` (VCVio's split per-target bound,
  `= n₀ · Σ_r S(k, r) (n₁)_r 2^{-h r} 2^{-a k}`).
* **`twoColour_le`**: for the adaptive reader with at most `n₀` candidate and `n₁` coverer
  queries, the probability that some candidate cell is covered by the coverer cells is at most
  `n₀ · targetCoverBound h a k n₁`.  This is the plan's M0b bound at `ρ = 0` (no pre-read
  coverers).  The pre-read extension is NOT proved here (see `status/DIRECT.md`, the section of
  2026-11-22).
-/

open OracleComp OracleSpec ENNReal KeyedHash.Covering

set_option linter.unusedSectionVars false

namespace Ideal.Direct

open Ideal.HP Ideal.Prf AnswerTape Ideal.Itsr

variable {C V Y α : Type}

/-! ## Monotone events of two tapes -/

section Tape

variable [SampleableType Y]

/-- An event of a prefix-extended tape that is monotone under sublists. -/
def Mono1 (F : List Y → ProbComp Bool) : Prop :=
  ∀ l l', l.Sublist l' → prT (F l) ≤ prT (F l')

theorem prT_tapeF_succ_ge (F : List Y → ProbComp Bool) (hF : Mono1 F) (pre : List Y) (m : ℕ) :
    prT (tapeList Y m >>= fun r => F (pre ++ r)) ≤
      prT (tapeList Y (m + 1) >>= fun r => F (pre ++ r)) := by
  rw [tapeList_succ]
  simp only [bind_assoc, pure_bind]
  rw [← prT_bind_const ($ᵗ Y) (tapeList Y m >>= fun r => F (pre ++ r))]
  refine prT_bind_mono _ _ _ fun u _ => prT_bind_mono _ _ _ fun r _ => hF _ _ ?_
  exact List.Sublist.append (List.Sublist.refl _) (List.sublist_cons_self _ _)

theorem prT_tapeF_mono (F : List Y → ProbComp Bool) (hF : Mono1 F) (pre : List Y) {m n : ℕ}
    (h : m ≤ n) :
    prT (tapeList Y m >>= fun r => F (pre ++ r)) ≤ prT (tapeList Y n >>= fun r => F (pre ++ r)) := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (prT_tapeF_succ_ge F hF pre _)

/-- Two independent tapes and an event of the two prefix-extended lists. -/
noncomputable def tape2 (W : List Y → List Y → Bool) (p₀ p₁ : List Y) (n₀ n₁ : ℕ) : ProbComp Bool :=
  tapeList Y n₀ >>= fun r₀ => tapeList Y n₁ >>= fun r₁ => pure (W (p₀ ++ r₀) (p₁ ++ r₁))

/-- Monotone in both lists. -/
def Mono2 (W : List Y → List Y → Bool) : Prop :=
  ∀ l₀ l₀' l₁ l₁', l₀.Sublist l₀' → l₁.Sublist l₁' → W l₀ l₁ = true → W l₀' l₁' = true

theorem prT_pure_mono {b b' : Bool} (h : b = true → b' = true) :
    prT (pure b : ProbComp Bool) ≤ prT (pure b') := by
  rw [prT_pure, prT_pure]
  cases b
  · simp
  · simp [h rfl]

theorem tape2_mono (W : List Y → List Y → Bool) (hW : Mono2 W) (p₀ p₁ : List Y) {m₀ n₀ m₁ n₁ : ℕ}
    (h₀ : m₀ ≤ n₀) (h₁ : m₁ ≤ n₁) : prT (tape2 W p₀ p₁ m₀ m₁) ≤ prT (tape2 W p₀ p₁ n₀ n₁) := by
  unfold tape2
  refine (prT_bind_mono _ _ (fun r₀ => tapeList Y n₁ >>= fun r₁ => pure (W (p₀ ++ r₀) (p₁ ++ r₁)))
    fun r₀ _ => ?_).trans ?_
  · exact prT_tapeF_mono (fun l => pure (W (p₀ ++ r₀) l)) (fun l l' hl =>
      prT_pure_mono fun hw => hW _ _ _ _ (List.Sublist.refl _) hl hw) p₁ h₁
  · exact prT_tapeF_mono (fun l => tapeList Y n₁ >>= fun r₁ => pure (W l (p₁ ++ r₁)))
      (fun l l' hl => prT_bind_mono _ _ _ fun r₁ _ =>
        prT_pure_mono fun hw => hW _ _ _ _ hl (List.Sublist.refl _) hw) p₀ h₀

end Tape

/-! ## Two-colour logging -/

section Log

variable [DecidableEq C] {ι : Type} {spec : OracleSpec ι}

/-- Two-colour logging: all distinct cells read; the cells first read by a colour-0 query; the
cells first read by a colour-1 query. -/
def logM2 (cell : ι → C) (lg₀ lg₁ : ι → Bool) (t : ι) (st : List C × List C × List C) :
    List C × List C × List C :=
  (logU cell t st.1,
    if lg₀ t = true ∧ cell t ∉ st.1 then st.2.1 ++ [cell t] else st.2.1,
    if lg₁ t = true ∧ cell t ∉ st.1 then st.2.2 ++ [cell t] else st.2.2)

/-- **Two-colour tape domination** (generalised over the cells read so far, frozen to `t`). -/
theorem prT_tape2_le_aux [Finite C] [SampleableType V] [SampleableType Y] [SampleableType (C → V)]
    (cell : ι → C) (lg₀ lg₁ : ι → Bool) (hdis : ∀ t, ¬ (lg₀ t = true ∧ lg₁ t = true))
    (ans : (C → V) → (t : ι) → spec.Range t)
    (hans : ∀ g g' t, g (cell t) = g' (cell t) → ans g t = ans g' t)
    (out : V → Y)
    (hout : ∀ p : Y → Prop, Pr{let u ← $ᵗ V}[p (out u)] = Pr{let y ← $ᵗ Y}[p y])
    (W : List Y → List Y → Bool) (hW : Mono2 W)
    (oa : OracleComp (unifSpec + spec) α) (n₀ n₁ : ℕ)
    (hn₀ : IsQueryBoundP oa (fun i => lgB lg₀ i = true) n₀)
    (hn₁ : IsQueryBoundP oa (fun i => lgB lg₁ i = true) n₁)
    (a s₀ s₁ : List C) (hs₀ : ∀ c ∈ s₀, c ∈ a) (hs₁ : ∀ c ∈ s₁, c ∈ a) (t : C → V) :
    prT ($ᵗ (C → V) >>= fun g =>
        (simulateQ (stImpl (ans (mix a t g)) (logM2 cell lg₀ lg₁)) oa).run (a, s₀, s₁) >>= fun z =>
          pure (W (z.2.2.1.map fun c => out (mix a t g c)) (z.2.2.2.map fun c => out (mix a t g c)))) ≤
      prT (tape2 W (s₀.map fun c => out (t c)) (s₁.map fun c => out (t c)) n₀ n₁) := by
  induction oa using OracleComp.inductionOn generalizing n₀ n₁ a s₀ s₁ t with
  | pure x =>
    have h0 : ∀ (s : List C) (hs : ∀ c ∈ s, c ∈ a) (g : C → V),
        (s.map fun c => out (mix a t g c)) = s.map fun c => out (t c) :=
      fun s hs g => List.map_congr_left fun c hc => by rw [mix_of_mem (hs c hc)]
    simp only [simulateQ_pure, StateT.run_pure, pure_bind, h0 s₀ hs₀, h0 s₁ hs₁]
    rw [prT_bind_const]
    refine (tape2_mono W hW _ _ (Nat.zero_le n₀) (Nat.zero_le n₁)).trans' ?_
    simp [tape2]
  | query_bind t₀ k ih =>
    rw [isQueryBoundP_query_bind_iff] at hn₀ hn₁
    rcases t₀ with m | t₀
    · simp only [run_stImpl_inl_bind, bind_assoc]
      rw [prT_swap]
      refine prT_bind_le_of_forall_le _ _ fun x _ => ?_
      exact ih x n₀ n₁ (hn₀.2 x) (hn₁.2 x) a s₀ s₁ hs₀ hs₁ t
    · have hk₀ : ∀ x, IsQueryBoundP (k x) (fun i => lgB lg₀ i = true)
          (if lg₀ t₀ = true then n₀ - 1 else n₀) := fun x => hn₀.2 x
      have hk₁ : ∀ x, IsQueryBoundP (k x) (fun i => lgB lg₁ i = true)
          (if lg₁ t₀ = true then n₁ - 1 else n₁) := fun x => hn₁.2 x
      by_cases hc : cell t₀ ∈ a
      · have hans' : ∀ g : C → V, ans (mix a t g) t₀ = ans t t₀ := fun g =>
          hans _ _ _ (mix_of_mem hc t g)
        have hu : logM2 cell lg₀ lg₁ t₀ (a, s₀, s₁) = (a, s₀, s₁) := by
          simp [logM2, logU_of_mem hc, hc]
        simp only [run_stImpl_inr_bind, hans', hu]
        refine (ih (ans t t₀) _ _ (hk₀ _) (hk₁ _) a s₀ s₁ hs₀ hs₁ t).trans
          (tape2_mono W hW _ _ ?_ ?_)
        · split <;> omega
        · split <;> omega
      · rw [prT_freeze hc t (fun M =>
          (simulateQ (stImpl (ans M) (logM2 cell lg₀ lg₁))
            (liftM ((unifSpec + spec).query (.inr t₀)) >>= k)).run (a, s₀, s₁) >>=
            fun z => pure (W (z.2.2.1.map fun c => out (M c)) (z.2.2.2.map fun c => out (M c))))]
        have hans' : ∀ (v : V) (g : C → V),
            ans (mix (a ++ [cell t₀]) (Function.update t (cell t₀) v) g) t₀ =
              ans (Function.update t (cell t₀) v) t₀ := fun v g =>
          hans _ _ _ (mix_of_mem (by simp) _ g)
        have hmap : ∀ (s : List C) (hs : ∀ c ∈ s, c ∈ a) (v : V),
            s.map (fun c => out (Function.update t (cell t₀) v c)) = s.map (fun c => out (t c)) :=
          fun s hs v => List.map_congr_left fun c hcm => by
            rw [Function.update_of_ne (fun e : c = cell t₀ => hc (e ▸ hs c hcm))]
        have hsa : ∀ (s : List C), (∀ c ∈ s, c ∈ a) → ∀ c ∈ s, c ∈ a ++ [cell t₀] :=
          fun s hs c hcm => List.mem_append_left _ (hs c hcm)
        have hsa' : ∀ (s : List C), (∀ c ∈ s, c ∈ a) → ∀ c ∈ s ++ [cell t₀], c ∈ a ++ [cell t₀] :=
          fun s hs c hcm => by
            rcases List.mem_append.mp hcm with h | h
            · exact List.mem_append_left _ (hs c h)
            · exact List.mem_append_right _ h
        have hlast : ∀ (s : List C) (hs : ∀ c ∈ s, c ∈ a) (v : V),
            (s ++ [cell t₀]).map (fun c => out (Function.update t (cell t₀) v c)) =
              s.map (fun c => out (t c)) ++ [out v] := fun s hs v => by
          rw [List.map_append, hmap s hs v]; simp
        by_cases hl₀ : lg₀ t₀ = true
        · have hl₁ : ¬ lg₁ t₀ = true := fun h => hdis t₀ ⟨hl₀, h⟩
          have hu : logM2 cell lg₀ lg₁ t₀ (a, s₀, s₁) = (a ++ [cell t₀], s₀ ++ [cell t₀], s₁) := by
            simp [logM2, logU_of_not_mem hc, hc, hl₀, hl₁]
          have hpos : 0 < n₀ := hn₀.1.resolve_left (by simp [lgB, hl₀])
          simp only [hl₀, hl₁, ite_true, ite_false, Bool.false_eq_true] at hk₀ hk₁
          simp only [run_stImpl_inr_bind, hans', hu]
          refine (prT_bind_mono _ _ _ fun v _ => (ih _ (n₀ - 1) n₁ (hk₀ _) (hk₁ _) _ _ _
            (hsa' s₀ hs₀) (hsa s₁ hs₁) (Function.update t (cell t₀) v))).trans (le_of_eq ?_)
          simp only [hlast s₀ hs₀, hmap s₁ hs₁, tape2, List.append_assoc, List.singleton_append]
          rw [prT_bind_out out hout (fun y => tapeList Y (n₀ - 1) >>= fun r₀ => tapeList Y n₁ >>=
            fun r₁ => pure (W (s₀.map (fun c => out (t c)) ++ y :: r₀)
              (s₁.map (fun c => out (t c)) ++ r₁)))]
          obtain ⟨m, rfl⟩ : ∃ m, n₀ = m + 1 := ⟨n₀ - 1, by omega⟩
          rw [tapeList_succ]
          simp only [bind_assoc, pure_bind, Nat.add_sub_cancel]
        · by_cases hl₁ : lg₁ t₀ = true
          · have hu : logM2 cell lg₀ lg₁ t₀ (a, s₀, s₁) =
                (a ++ [cell t₀], s₀, s₁ ++ [cell t₀]) := by
              simp [logM2, logU_of_not_mem hc, hc, hl₀, hl₁]
            have hpos : 0 < n₁ := hn₁.1.resolve_left (by simp [lgB, hl₁])
            simp only [hl₀, hl₁, ite_true, ite_false, Bool.false_eq_true] at hk₀ hk₁
            simp only [run_stImpl_inr_bind, hans', hu]
            refine (prT_bind_mono _ _ _ fun v _ => (ih _ n₀ (n₁ - 1) (hk₀ _) (hk₁ _) _ _ _
              (hsa s₀ hs₀) (hsa' s₁ hs₁) (Function.update t (cell t₀) v))).trans (le_of_eq ?_)
            simp only [hlast s₁ hs₁, hmap s₀ hs₀, tape2, List.append_assoc, List.singleton_append]
            rw [prT_swap]
            refine prT_bind_congr _ _ _ fun r₀ _ => ?_
            rw [prT_bind_out out hout (fun y => tapeList Y (n₁ - 1) >>= fun r₁ =>
              pure (W (s₀.map (fun c => out (t c)) ++ r₀) (s₁.map (fun c => out (t c)) ++ y :: r₁)))]
            obtain ⟨m, rfl⟩ : ∃ m, n₁ = m + 1 := ⟨n₁ - 1, by omega⟩
            rw [tapeList_succ]
            simp only [bind_assoc, pure_bind, Nat.add_sub_cancel]
          · have hu : logM2 cell lg₀ lg₁ t₀ (a, s₀, s₁) = (a ++ [cell t₀], s₀, s₁) := by
              simp [logM2, logU_of_not_mem hc, hc, hl₀, hl₁]
            simp only [hl₀, hl₁, ite_false, Bool.false_eq_true] at hk₀ hk₁
            simp only [run_stImpl_inr_bind, hans', hu]
            refine prT_bind_le_of_forall_le _ _ fun v _ => ?_
            refine (ih _ n₀ n₁ (hk₀ _) (hk₁ _) _ _ _ (hsa s₀ hs₀) (hsa s₁ hs₁)
              (Function.update t (cell t₀) v)).trans (le_of_eq ?_)
            rw [hmap s₀ hs₀, hmap s₁ hs₁]

/-- **Two-colour tape domination.** -/
theorem prT_tape2_le [Finite C] [SampleableType V] [SampleableType Y] [SampleableType (C → V)]
    (cell : ι → C) (lg₀ lg₁ : ι → Bool) (hdis : ∀ t, ¬ (lg₀ t = true ∧ lg₁ t = true))
    (ans : (C → V) → (t : ι) → spec.Range t)
    (hans : ∀ g g' t, g (cell t) = g' (cell t) → ans g t = ans g' t)
    (out : V → Y)
    (hout : ∀ p : Y → Prop, Pr{let u ← $ᵗ V}[p (out u)] = Pr{let y ← $ᵗ Y}[p y])
    (W : List Y → List Y → Bool) (hW : Mono2 W)
    (oa : OracleComp (unifSpec + spec) α) (n₀ n₁ : ℕ)
    (hn₀ : IsQueryBoundP oa (fun i => lgB lg₀ i = true) n₀)
    (hn₁ : IsQueryBoundP oa (fun i => lgB lg₁ i = true) n₁) :
    prT ($ᵗ (C → V) >>= fun g =>
        (simulateQ (stImpl (ans g) (logM2 cell lg₀ lg₁)) oa).run ([], [], []) >>= fun z =>
          pure (W (z.2.2.1.map fun c => out (g c)) (z.2.2.2.map fun c => out (g c)))) ≤
      prT (tape2 W [] [] n₀ n₁) := by
  have h := prT_tape2_le_aux cell lg₀ lg₁ hdis ans hans out hout W hW oa n₀ n₁ hn₀ hn₁ [] [] []
    (by simp) (by simp) (fun _ => Classical.arbitrary V)
  simpa only [mix_nil, List.map_nil] using h

end Log

/-! ## Coverage on two independent tapes -/

section Cover

open Classical

variable (h a k : ℕ)

open Classical in
/-- Each of the `k` digits of `y` is matched, at `y`'s leaf, by some digest of `L`. -/
def covL (y : Digest h a k) (L : List (Digest h a k)) : Prop :=
  ∀ i, ∃ z ∈ L, z.1 = y.1 ∧ z.2 i = y.2 i

open Classical in
/-- Some candidate digest is covered by the coverer digests. -/
noncomputable def covW (l₀ l₁ : List (Digest h a k)) : Bool := decide (∃ y ∈ l₀, covL h a k y l₁)

theorem covW_mono : Mono2 (covW h a k) := by
  intro l₀ l₀' l₁ l₁' h₀ h₁ hw
  simp only [covW, decide_eq_true_eq] at hw ⊢
  obtain ⟨y, hy, hcov⟩ := hw
  exact ⟨y, h₀.subset hy, fun i => by
    obtain ⟨z, hz, h⟩ := hcov i
    exact ⟨z, h₁.subset hz, h⟩⟩

/-- A uniform digest is covered by a tape of `n` independent uniform digests with probability at
most `targetCoverBound h a k n` (VCVio's split bound with one target position). -/
theorem prEvent_cov_tape_le (n : ℕ) :
    Pr{let p ← (do
        let y ← ($ᵗ (Digest h a k) : ProbComp (Digest h a k))
        let r ← tapeList (Digest h a k) n
        pure (y, r))}[covL h a k p.1 p.2] ≤ targetCoverBound h a k n := by
  have hsplit := evalDist_answerTape_tapeCoveredSplit_le_mul_targetCoverBound h a k (n + 1) 1 n
    (fun _ => 0) Fin.succ (fun _ j => (Fin.succ_ne_zero j).symm)
  rw [Nat.cast_one, one_mul] at hsplit
  have heq : (do
        let y ← ($ᵗ (Digest h a k) : ProbComp (Digest h a k))
        let r ← tapeList (Digest h a k) n
        pure (y, r)) =
      (fun v : Fin (n + 1) → Digest h a k => (v 0, List.ofFn fun j : Fin n => v j.succ)) <$>
        answerTape (Digest h a k) (n + 1) := by
    rw [answerTape_succ, tapeList_eq_map_answerTape]
    simp only [map_bind, map_pure, bind_map_left, Fin.cons_zero, Fin.cons_succ]
  rw [heq, prEvent_map]
  refine le_trans ?_ hsplit
  rw [prEvent_eq_evalDist_of_discrete]
  refine MeasureTheory.measure_mono (μ := 𝒟[answerTape (Digest h a k) (n + 1)]) fun v hv => ?_
  simp only [Function.comp_apply, Set.mem_setOf_eq] at hv ⊢
  have hf : ∀ i : Fin k, ∃ j : Fin n, (v j.succ).1 = (v 0).1 ∧ (v j.succ).2 i = (v 0).2 i := by
    intro i
    obtain ⟨z, hz, h1, h2⟩ := hv i
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hz
    exact ⟨j, h1, h2⟩
  choose f hf using hf
  exact ⟨0, f, hf⟩

/-- On two independent tapes of `n₀` candidates and `n₁` coverers, some candidate is covered with
probability at most `n₀ · targetCoverBound h a k n₁`. -/
theorem prT_tape2_cov_le (n₀ n₁ : ℕ) :
    prT (tape2 (covW h a k) [] [] n₀ n₁) ≤ n₀ * targetCoverBound h a k n₁ := by
  induction n₀ with
  | zero => simp [tape2, covW, HP.prT]
  | succ n ih =>
    unfold tape2 at ih ⊢
    rw [tapeList_succ]
    simp only [List.nil_append, bind_assoc, pure_bind] at ih ⊢
    have hsplit : ∀ (u : Digest h a k) (r₀ r₁ : List (Digest h a k)),
        covW h a k (u :: r₀) r₁ = (decide (covL h a k u r₁) || covW h a k r₀ r₁) := by
      intro u r₀ r₁
      simp only [covW, List.mem_cons, exists_eq_or_imp]
      by_cases h1 : covL h a k u r₁ <;> simp [h1]
    simp only [hsplit]
    calc _ ≤ prT (($ᵗ (Digest h a k)) >>= fun u => tapeList (Digest h a k) n >>= fun r₀ =>
            tapeList (Digest h a k) n₁ >>= fun r₁ => pure (decide (covL h a k u r₁))) +
          prT (($ᵗ (Digest h a k)) >>= fun u => tapeList (Digest h a k) n >>= fun r₀ =>
            tapeList (Digest h a k) n₁ >>= fun r₁ => pure (covW h a k r₀ r₁)) := by
          refine prT_bind_le_add _ _ _ _ fun u => ?_
          refine prT_bind_le_add _ _ _ _ fun r₀ => ?_
          refine prT_bind_le_add _ _ _ _ fun r₁ => ?_
          rw [prT_pure, prT_pure, prT_pure]
          cases decide (covL h a k u r₁) <;> cases covW h a k r₀ r₁ <;> simp
      _ ≤ targetCoverBound h a k n₁ + n * targetCoverBound h a k n₁ := by
          refine add_le_add ?_ ?_
          · rw [prT_bind_congr _ _ (fun u => tapeList (Digest h a k) n₁ >>= fun r₁ =>
              pure (decide (covL h a k u r₁))) fun u _ => prT_bind_const _ _]
            refine le_trans (le_of_eq ?_) (prEvent_cov_tape_le h a k n₁)
            rw [show (($ᵗ (Digest h a k) : ProbComp (Digest h a k)) >>= fun u =>
                tapeList (Digest h a k) n₁ >>= fun r₁ => pure (decide (covL h a k u r₁))) =
                (do let p ← (do
                      let y ← ($ᵗ (Digest h a k) : ProbComp (Digest h a k))
                      let r ← tapeList (Digest h a k) n₁
                      pure (y, r))
                    pure (decide (covL h a k p.1 p.2))) by simp only [bind_assoc, pure_bind]]
            rw [HP.prT_bind_pure]
            simp only [decide_eq_true_eq]
          · rw [prT_bind_const]; exact ih
      _ = ((n + 1 : ℕ) : ℝ≥0∞) * targetCoverBound h a k n₁ := by push_cast; ring

end Cover

/-! ## The headline -/

/-- **Two-colour coverage (milestone M0b at `ρ = 0`).**  An adaptive reader of a uniform table
`g : C → V` whose queries carry a predictable colour — candidate (`lg₀`) or coverer (`lg₁`), a
cell keeping the colour of its first read — making at most `n₀` candidate and `n₁` coverer
queries (any number of uncoloured queries and coins): the probability that the digest of some
candidate cell has each of its `k` digits matched, at its own leaf, by the digest of some coverer
cell is at most `n₀ · targetCoverBound h a k n₁`
(`= n₀ · Σ_{r ≤ k} C(n₁, r) · #surj(k, r) · 2^{-h r} · 2^{-a k}
   = n₀ · Σ_r S(k, r) (n₁)_r 2^{-h r} 2^{-a k}`).
Only coverer cells count as coverers: the bound has no term in the number of candidates or of
uncoloured reads beyond the factor `n₀`. -/
theorem twoColour_le (h a k : ℕ) [DecidableEq C] {ι : Type} {spec : OracleSpec ι} [Finite C]
    [SampleableType V] [SampleableType (C → V)]
    (cell : ι → C) (lg₀ lg₁ : ι → Bool) (hdis : ∀ t, ¬ (lg₀ t = true ∧ lg₁ t = true))
    (ans : (C → V) → (t : ι) → spec.Range t)
    (hans : ∀ g g' t, g (cell t) = g' (cell t) → ans g t = ans g' t)
    (out : V → Digest h a k)
    (hout : ∀ p : Digest h a k → Prop, Pr{let u ← $ᵗ V}[p (out u)] = Pr{let y ← $ᵗ (Digest h a k)}[p y])
    (oa : OracleComp (unifSpec + spec) α) (n₀ n₁ : ℕ)
    (hn₀ : IsQueryBoundP oa (fun i => lgB lg₀ i = true) n₀)
    (hn₁ : IsQueryBoundP oa (fun i => lgB lg₁ i = true) n₁) :
    prT ($ᵗ (C → V) >>= fun g =>
        (simulateQ (stImpl (ans g) (logM2 cell lg₀ lg₁)) oa).run ([], [], []) >>= fun z =>
          pure (covW h a k (z.2.2.1.map fun c => out (g c)) (z.2.2.2.map fun c => out (g c)))) ≤
      n₀ * targetCoverBound h a k n₁ :=
  (prT_tape2_le cell lg₀ lg₁ hdis ans hans out hout (covW h a k) (covW_mono h a k) oa n₀ n₁ hn₀
    hn₁).trans (prT_tape2_cov_le h a k n₀ n₁)

end Ideal.Direct

#print axioms Ideal.Direct.prT_tape2_le
#print axioms Ideal.Direct.prEvent_cov_tape_le
#print axioms Ideal.Direct.prT_tape2_cov_le
#print axioms Ideal.Direct.twoColour_le
