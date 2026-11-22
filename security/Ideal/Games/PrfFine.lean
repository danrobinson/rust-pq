import Ideal.Games.Prf

/-!
# PRF security of the two-block keyed function with finer accounting (shape marking)

`Ideal.prfAdvantageI_le_marked`: the bound of `Ideal.prfAdvantageI_le` with the key-guessing
term `q / |K|` replaced by `qM / |K|`, where `qM` bounds only the compression queries whose block
is of key-block shape, `∃ a k, B = blk a k` (`markQ`).  The birthday term `(q + qO)² / |St|`
still counts every compression query.

Why: the bad event of the override hop (`Prf.badK`) is a compression query at a block
`blk a k` for the secret key `k`; a query whose block is of the form `blk a k'` for NO `(a, k')`
is never bad, whatever the key (`prEvent_badK_le_marked`).  Nothing else of the proof changes.
-/

open OracleComp OracleSpec ENNReal PRFScheme

namespace Ideal.Prf

open Ideal.HP

variable {St Blk K PkSeed Ad Y : Type}

/-- A compression query whose block is of key-block shape. -/
def markQ (blk : Ad → K → Blk) : ℕ ⊕ ((St × Blk) ⊕ (PkSeed × Ad)) → Prop
  | .inr (.inl q) => ∃ a k, q.2 = blk a k
  | _ => False

noncomputable instance (blk : Ad → K → Blk) : DecidablePred (markQ (St := St) (PkSeed := PkSeed) blk) :=
  fun _ => Classical.propDecidable _

theorem markQ_imp (blk : Ad → K → Blk) (t : ℕ ⊕ ((St × Blk) ⊕ (PkSeed × Ad)))
    (h : markQ blk t) : isCompQ t = true := by
  rcases t with n | q | d
  · exact h.elim
  · rfl
  · exact h.elim

section Ovr

variable [Fintype Ad] [DecidableEq Blk]

/-- **Marked form of `prEvent_badK_le`**: only key-block-shaped compression queries can be bad. -/
theorem prEvent_badK_le_marked [Fintype K] [SampleableType K] (blk : Ad → K → Blk)
    (hblk : ∀ a a' k k', blk a k = blk a' k' → a = a' ∧ k = k')
    (l : List ((St × Blk) ⊕ (PkSeed × Ad))) :
    Pr{let k ← $ᵗ K}[l.any (badK blk k) = true] ≤
      (l.countP (fun t => decide (markQ blk (.inr t))) : ℝ≥0∞) *
        (Fintype.card K : ℝ≥0∞)⁻¹ := by
  induction l with
  | nil =>
    rw [prEvent_eq_zero_of_forall_not _ _ (by simp)]
    exact zero_le
  | cons t l ih =>
    refine (prEvent_mono _ _ (fun k => badK blk k t = true ∨ l.any (badK blk k) = true)
      (by simp)).trans ?_
    refine (prEvent_or_le _ _ _).trans ?_
    rcases t with q | d
    · by_cases h : ∃ a₀ k₀, q.2 = blk a₀ k₀
      · obtain ⟨a₀, k₀, h₀⟩ := h
        have h1 : Pr{let k ← $ᵗ K}[badK (PkSeed := PkSeed) blk k (.inl q) = true] ≤
            (Fintype.card K : ℝ≥0∞)⁻¹ := by
          refine (prEvent_mono _ _ (fun k => k = k₀) fun k hk => ?_).trans
            (SampleableType.prEvent_uniformSample_eq_singleton k₀).le
          simp only [badK, decide_eq_true_eq] at hk
          obtain ⟨a, ha⟩ := hk
          exact (hblk _ _ _ _ (ha.symm.trans h₀)).2
        have hm : markQ (St := St) (PkSeed := PkSeed) blk (.inr (.inl q)) := ⟨a₀, k₀, h₀⟩
        refine (add_le_add h1 ih).trans (le_of_eq ?_)
        rw [List.countP_cons_of_pos (by simpa using hm)]
        push_cast
        ring
      · have h1 : Pr{let k ← $ᵗ K}[badK (PkSeed := PkSeed) blk k (.inl q) = true] = 0 := by
          refine prEvent_eq_zero_of_forall_not _ _ fun k hk => h ?_
          simp only [badK, decide_eq_true_eq] at hk
          obtain ⟨a, ha⟩ := hk
          exact ⟨a, k, ha⟩
        have hm : ¬ markQ (St := St) (PkSeed := PkSeed) blk (.inr (.inl q)) := h
        rw [h1, zero_add]
        refine ih.trans (le_of_eq ?_)
        rw [List.countP_cons_of_neg (by simpa using hm)]
    · have h1 : Pr{let k ← $ᵗ K}[badK blk k (.inr d : (St × Blk) ⊕ (PkSeed × Ad)) = true] = 0 :=
        prEvent_eq_zero_of_forall_not _ _ (by simp [badK])
      rw [h1, zero_add]
      refine ih.trans (le_of_eq ?_)
      rw [List.countP_cons_of_neg (fun h => by simp only [decide_eq_true_eq] at h; exact h)]

end Ovr

section Bound

variable [Fintype St] [DecidableEq St] [SampleableType St] [Fintype Blk] [DecidableEq Blk]
  [SampleableType (CF St Blk)] [Fintype K] [SampleableType K] [Fintype PkSeed]
  [DecidableEq PkSeed] [Fintype Ad] [DecidableEq Ad] [SampleableType Y]

omit [DecidableEq St] [Fintype Blk] [Fintype PkSeed] [DecidableEq PkSeed] [DecidableEq Ad]
  [SampleableType Y] in
/-- The bad event of the override hop has probability at most `qM / |K|`. -/
theorem prT_badK_le_marked (IV : St) (sb : PkSeed → Blk) (blk : Ad → K → Blk) (out : St → Y)
    (hblk : ∀ a a' k k', blk a k = blk a' k' → a = a' ∧ k = k')
    (A : PrfAdvI St Blk PkSeed Ad Y) (qM : ℕ)
    (hqM : IsQueryBoundP A (markQ blk) qM) :
    prT ($ᵗ K >>= fun k => $ᵗ (CF St Blk) >>= fun g => $ᵗ (St × Ad → St) >>= fun T =>
      (simulateQ (trImpl (hybAns IV sb out g T)) A).run [] >>= fun z =>
        pure (z.2.any (badK blk k))) ≤ (qM : ℝ≥0∞) * (Fintype.card K : ℝ≥0∞)⁻¹ := by
  have hsw := prT_swap ($ᵗ K) ($ᵗ (CF St Blk) >>= fun g => $ᵗ (St × Ad → St) >>= fun T =>
      (simulateQ (trImpl (hybAns IV sb out g T)) A).run [])
    (fun k z => pure (z.2.any (badK blk k)))
  simp only [bind_assoc] at hsw
  rw [hsw]
  refine prT_bind_le_of_forall_le _ _ fun g _ => prT_bind_le_of_forall_le _ _ fun T _ =>
    prT_bind_le_of_forall_le _ _ fun z hz => ?_
  rw [prT_bind_pure]
  refine (prEvent_badK_le_marked blk hblk z.2).trans ?_
  have h1 := trace_countP_le (hybAns IV sb out g T) (markQ blk) A qM hqM [] z hz
  gcongr
  simpa using h1

/-- **One-sided bound, marked form.** -/
theorem prT_real_le_marked (IV : St) (sb : PkSeed → Blk) (blk : Ad → K → Blk) (out : St → Y)
    (hblk : ∀ a a' k k', blk a k = blk a' k' → a = a' ∧ k = k')
    (hne : ∀ pk a k, sb pk ≠ blk a k) (hsb : Function.Injective sb)
    (hout : ∀ p : Y → Prop, Pr{let u ← $ᵗ St}[p (out u)] = Pr{let y ← $ᵗ Y}[p y])
    (A : PrfAdvI St Blk PkSeed Ad Y) (qM q qO : ℕ)
    (hqM : IsQueryBoundP A (markQ blk) qM)
    (hq : IsQueryBoundP A (fun i => isCompQ i = true) q)
    (hO : IsQueryBoundP A (fun i => isPrfQ i = true) qO) :
    prT (prfRealGameI IV sb blk out A) ≤
      prT (prfIdealGameI A) + ((qM : ℝ≥0∞) * (Fintype.card K : ℝ≥0∞)⁻¹ +
        (((q + qO) ^ 2 : ℕ) : ℝ≥0∞) * (Fintype.card St : ℝ≥0∞)⁻¹) := by
  set H : ProbComp Bool := $ᵗ (CF St Blk) >>= fun g => $ᵗ (St × Ad → St) >>= fun T =>
    simulateQ (ansImpl (hybAns IV sb out g T)) A with hH
  have hreal : prT (prfRealGameI IV sb blk out A) ≤
      prT H + (qM : ℝ≥0∞) * (Fintype.card K : ℝ≥0∞)⁻¹ := by
    rw [prfRealGameI_eq, prT_swap]
    have hk : ∀ k : K, prT ($ᵗ (CF St Blk) >>= fun g =>
          simulateQ (ansImpl (realAns IV sb blk out g k)) A) ≤
        prT H + prT ($ᵗ (CF St Blk) >>= fun g => $ᵗ (St × Ad → St) >>= fun T =>
          (simulateQ (trImpl (hybAns IV sb out g T)) A).run [] >>= fun z =>
            pure (z.2.any (badK blk k))) := by
      intro k
      rw [prT_ovr blk hblk k (fun g => simulateQ (ansImpl (realAns IV sb blk out g k)) A)]
      refine prT_bind_le_add _ _ _ _ fun g => prT_bind_le_add _ _ _ _ fun T => ?_
      have := prT_simulateQ_le_add_trace (realAns IV sb blk out (ovr blk k g T) k)
        (hybAns IV sb out g T) (badK blk k)
        (fun t ht => realAns_ovr IV sb blk out hblk hne k g T t ht) A pure []
      simpa only [bind_pure] using this
    refine (prT_bind_le_add ($ᵗ K) _ (fun _ => H) _ hk).trans ?_
    rw [prT_bind_const]
    exact add_le_add le_rfl (prT_badK_le_marked IV sb blk out hblk A qM hqM)
  have hN : IsQueryBoundP A (fun i => i.isRight = true) (q + qO) := by
    refine IsQueryBoundP.of_imp (fun t ht => ?_) (hq.or hO)
    rcases t with n | q | d
    · simp at ht
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hhyb : prT H ≤ prT (prfIdealGameI A) +
      (((q + qO) ^ 2 : ℕ) : ℝ≥0∞) * (Fintype.card St : ℝ≥0∞)⁻¹ := by
    have hg : ∀ g : CF St Blk,
        prT ($ᵗ (St × Ad → St) >>= fun T => simulateQ (ansImpl (hybAns IV sb out g T)) A) ≤
          prT ($ᵗ (PkSeed × Ad → Y) >>= fun R => simulateQ (ansImpl (idealAns g R)) A) +
          prT ($ᵗ (PkSeed × Ad → Y) >>= fun R =>
            (simulateQ (trImpl (idealAns g R)) A).run [] >>= fun z =>
              pure (collφ (phi IV sb g) (dq z.2))) := fun g =>
      prT_rename_le (spec₀ := hS St Blk) (fun q => g q) (phi IV sb g) out hout A
    rw [prT_congr (evalDist_prfIdealGameI A), hH]
    refine (prT_bind_le_add ($ᵗ (CF St Blk)) _ _ _ hg).trans ?_
    refine add_le_add le_rfl ?_
    rw [prT_swap]
    exact prT_bind_le_of_forall_le _ _ fun R _ => prT_collφ_le IV sb hsb A (q + qO) hN R
  calc prT (prfRealGameI IV sb blk out A)
      ≤ prT H + (qM : ℝ≥0∞) * (Fintype.card K : ℝ≥0∞)⁻¹ := hreal
    _ ≤ prT (prfIdealGameI A) + (((q + qO) ^ 2 : ℕ) : ℝ≥0∞) * (Fintype.card St : ℝ≥0∞)⁻¹ +
          (qM : ℝ≥0∞) * (Fintype.card K : ℝ≥0∞)⁻¹ := add_le_add hhyb le_rfl
    _ = _ := by rw [add_assoc, add_comm ((((q + qO) ^ 2 : ℕ) : ℝ≥0∞) * _)]

end Bound

theorem markQ_negAdv (blk : Ad → K → Blk) (A : PrfAdvI St Blk PkSeed Ad Y) (qM : ℕ)
    (h : IsQueryBoundP A (markQ blk) qM) : IsQueryBoundP (negAdv A) (markQ blk) qM :=
  (isQueryBoundP_map_iff _ _ _).mpr h

end Ideal.Prf

namespace Ideal

open Ideal.HP Ideal.Prf

variable {St Blk K PkSeed Ad Y : Type}

/-- **PRF security in the ideal-compression model, marked form.**  As `prfAdvantageI_le`, with
the key-guessing term counting only the `qM` compression queries whose block is of the form
`blk a k` for some `a`, `k` (`Prf.markQ`). -/
theorem prfAdvantageI_le_marked [Fintype St] [DecidableEq St] [SampleableType St] [Fintype Blk]
    [DecidableEq Blk] [SampleableType (CF St Blk)] [Fintype K] [SampleableType K]
    [Fintype PkSeed] [DecidableEq PkSeed] [Fintype Ad] [DecidableEq Ad] [SampleableType Y]
    (IV : St) (sb : PkSeed → Blk) (blk : Ad → K → Blk) (out : St → Y)
    (hblk : ∀ a a' k k', blk a k = blk a' k' → a = a' ∧ k = k')
    (hne : ∀ pk a k, sb pk ≠ blk a k) (hsb : Function.Injective sb)
    (hout : ∀ p : Y → Prop, Pr{let u ← $ᵗ St}[p (out u)] = Pr{let y ← $ᵗ Y}[p y])
    (A : PrfAdvI St Blk PkSeed Ad Y) (qM q qO : ℕ)
    (hqM : IsQueryBoundP A (markQ blk) qM)
    (hq : IsQueryBoundP A (fun i => isCompQ i = true) q)
    (hO : IsQueryBoundP A (fun i => isPrfQ i = true) qO) :
    prfAdvantageI IV sb blk out A ≤
      (qM : ℝ≥0∞) * (Fintype.card K : ℝ≥0∞)⁻¹ +
        (((q + qO) ^ 2 : ℕ) : ℝ≥0∞) * (Fintype.card St : ℝ≥0∞)⁻¹ := by
  unfold prfAdvantageI prfRealIdeal prfIdealIdeal
  refine MeasureTheory.Measure.boolDist_le_of_apply_le _ _ fun b => ?_
  cases b
  · have h := prT_real_le_marked IV sb blk out hblk hne hsb hout (negAdv A) qM q qO
      (markQ_negAdv blk A qM hqM)
      ((isQueryBoundP_map_iff _ _ _).mpr hq) ((isQueryBoundP_map_iff _ _ _).mpr hO)
    rwa [prfRealGameI_not, prfIdealGameI_not, prT_not_map, prT_not_map] at h
  · have h := prT_real_le_marked IV sb blk out hblk hne hsb hout A qM q qO hqM hq hO
    rwa [prT_eq, prT_eq] at h

end Ideal

#print axioms Ideal.Prf.prEvent_badK_le_marked
#print axioms Ideal.prfAdvantageI_le_marked
