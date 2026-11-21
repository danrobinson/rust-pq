import Ideal.Games.PrfDefs
import Ideal.Games.PrfLemmas

/-!
# PRF security of the two-block keyed function in the ideal-compression model

`Ideal.prfAdvantageI_le`: for `f_g(k, (pk, a)) = out (g (g (IV, sb pk), blk a k))` with `g` a
uniformly random compression table that the distinguisher can query,

`prfAdvantageI ≤ q / |K| + (q + qO)² / |St|`

for a distinguisher making at most `q` compression queries and `qO` function queries.

Proof.  All games are run against answer functions computed from eagerly sampled tables.
* `prT_ovr`: for a fixed key `k`, overriding every cell `(c, blk a k)` of a uniform `g` by
  `T (c, a)` for an independent uniform `T : St × Ad → St` gives a uniform table.
* With the overridden table the function oracle at `(pk, a)` returns
  `out (T (g (IV, sb pk), a))`, and a compression query `(c, B)` is answered by `g` unless
  `B = blk a k` for some `a` (`realAns_ovr`): identical until bad.  The game answered by `g` and
  `out (T (g (IV, sb pk), a))` does not depend on `k`, so drawing `k` after the run bounds the bad
  event by `q / |K|` (`prEvent_badK_le`).
* `Prf.prT_rename_le`: `(pk, a) ↦ out (T (g (IV, sb pk), a))` is a uniform random function
  unless two queried inputs collide under `(pk, a) ↦ (g (IV, sb pk), a)`; such a collision is a
  collision of `g` on two distinct touched cells, bounded by the birthday bound
  `Prf.prT_coll_le`.
* `evalDist_prfIdealGameI`: the lazy random function of the ideal experiment is a uniform table.
* The same bound for the negated distinguisher gives the other direction of the distance.
-/

open OracleComp OracleSpec ENNReal PRFScheme

namespace Ideal.Prf

open Ideal.HP

variable {St Blk K PkSeed Ad Y : Type}

/-! ## The experiments as answer-function runs -/

/-- Answers of the real experiment at table `g` and key `k`. -/
def realAns (IV : St) (sb : PkSeed → Blk) (blk : Ad → K → Blk) (out : St → Y) (g : CF St Blk)
    (k : K) : (t : (St × Blk) ⊕ (PkSeed × Ad)) → (hS St Blk + ((PkSeed × Ad) →ₒ Y)).Range t
  | .inl q => g q
  | .inr d => prfF IV sb blk out g k d

/-- Answers of the ideal experiment at table `g` and function table `R`. -/
abbrev idealAns (g : CF St Blk) (R : PkSeed × Ad → Y) :
    (t : (St × Blk) ⊕ (PkSeed × Ad)) → (hS St Blk + ((PkSeed × Ad) →ₒ Y)).Range t :=
  ansR (spec₀ := hS St Blk) (fun q => g q) R

/-- The cell of the inner table read by the function oracle at `(pk, a)`. -/
def phi (IV : St) (sb : PkSeed → Blk) (g : CF St Blk) (d : PkSeed × Ad) : St × Ad :=
  (g (IV, sb d.1), d.2)

/-- Answers of the hybrid: compression queries by `g`, the function oracle at `(pk, a)` by
`out (T (g (IV, sb pk), a))`. -/
abbrev hybAns (IV : St) (sb : PkSeed → Blk) (out : St → Y) (g : CF St Blk) (T : St × Ad → St) :
    (t : (St × Blk) ⊕ (PkSeed × Ad)) → (hS St Blk + ((PkSeed × Ad) →ₒ Y)).Range t :=
  ansL (spec₀ := hS St Blk) (fun q => g q) (phi IV sb g) out T

theorem simulateQ_real [SampleableType K] (IV : St) (sb : PkSeed → Blk) (blk : Ad → K → Blk)
    (out : St → Y) (g : CF St Blk) (k : K) {α : Type}
    (oa : OracleComp (unifSpec + (hS St Blk + ((PkSeed × Ad) →ₒ Y))) α) :
    simulateQ ((prfSchemeI IV sb blk out g).prfRealQueryImpl k) (simulateQ (instImpl g) oa) =
      simulateQ (ansImpl (realAns IV sb blk out g k)) oa := by
  refine QueryImpl.simulateQ_simulateQ_eq_of_apply (fun t => ?_) oa
  rcases t with n | q | d
  · exact simulateQ_spec_query _ _
  · rfl
  · exact simulateQ_spec_query _ _

theorem simulateQ_ideal (g : CF St Blk) (R : PkSeed × Ad → Y) {α : Type}
    (oa : OracleComp (unifSpec + (hS St Blk + ((PkSeed × Ad) →ₒ Y))) α) :
    simulateQ (unifFwdAnswerImpl (QueryImpl.ofFn R)) (simulateQ (instImpl g) oa) =
      simulateQ (ansImpl (idealAns g R)) oa := by
  refine QueryImpl.simulateQ_simulateQ_eq_of_apply (fun t => ?_) oa
  rcases t with n | q | d
  · exact simulateQ_spec_query _ _
  · rfl
  · exact simulateQ_spec_query _ _

theorem prfRealGameI_eq [SampleableType K] [SampleableType (CF St Blk)] [SampleableType Y]
    [DecidableEq PkSeed] [DecidableEq Ad] (IV : St) (sb : PkSeed → Blk) (blk : Ad → K → Blk)
    (out : St → Y) (A : PrfAdvI St Blk PkSeed Ad Y) :
    prfRealGameI IV sb blk out A = $ᵗ (CF St Blk) >>= fun g => $ᵗ K >>= fun k =>
      simulateQ (ansImpl (realAns IV sb blk out g k)) A := by
  unfold prfRealGameI
  refine bind_congr fun g => ?_
  show ($ᵗ K >>= fun k => simulateQ ((prfSchemeI IV sb blk out g).prfRealQueryImpl k)
    (simulateQ (instImpl g) A)) = _
  simp only [simulateQ_real]

/-- The ideal experiment with an eagerly sampled function table. -/
theorem evalDist_prfIdealGameI [SampleableType (CF St Blk)] [SampleableType Y]
    [DecidableEq PkSeed] [DecidableEq Ad] [Fintype PkSeed] [Fintype Ad]
    (A : PrfAdvI St Blk PkSeed Ad Y) :
    𝒟[prfIdealGameI A] = 𝒟[$ᵗ (CF St Blk) >>= fun g => $ᵗ (PkSeed × Ad → Y) >>= fun R =>
      simulateQ (ansImpl (idealAns g R)) A] := by
  unfold prfIdealGameI
  refine evalDist_bind_congr_of_support _ _ _ fun g _ => ?_
  unfold prfIdealExperiment prfIdealQueryImpl
  rw [OracleComp.evalDist_simulateQ_romImpl_run'_eq_completeTable]
  refine congrArg _ (bind_congr fun R => ?_)
  rw [OracleComp.completeTable_empty]
  exact simulateQ_ideal g R A

/-! ## The override -/

section Ovr

variable [Fintype Ad] [DecidableEq Blk]

/-- The table `g` with every cell `(c, blk a k)` overridden by `T (c, a)`. -/
noncomputable def ovr (blk : Ad → K → Blk) (k : K) (g : CF St Blk) (T : St × Ad → St) :
    CF St Blk :=
  fun q => if h : ∃ a, q.2 = blk a k then T (q.1, h.choose) else g q

theorem ovr_blk (blk : Ad → K → Blk)
    (hblk : ∀ a a' k k', blk a k = blk a' k' → a = a' ∧ k = k') (k : K) (g : CF St Blk)
    (T : St × Ad → St) (c : St) (a : Ad) : ovr blk k g T (c, blk a k) = T (c, a) := by
  have h : ∃ a', (c, blk a k).2 = blk a' k := ⟨a, rfl⟩
  have e : h.choose = a := (hblk _ _ _ _ h.choose_spec).1.symm
  unfold ovr
  rw [dite_eq_left_of_eq_true (eq_true h), e]

theorem ovr_of_not (blk : Ad → K → Blk) (k : K) (g : CF St Blk) (T : St × Ad → St)
    (q : St × Blk) (h : ¬ ∃ a, q.2 = blk a k) : ovr blk k g T q = g q := by
  unfold ovr
  rw [dite_eq_right_of_eq_false (eq_false h)]

/-- **The overridden table is uniform.** -/
theorem prT_ovr [DecidableEq St] [Fintype St] [Fintype Blk] [SampleableType St]
    [SampleableType (CF St Blk)] (blk : Ad → K → Blk)
    (hblk : ∀ a a' k k', blk a k = blk a' k' → a = a' ∧ k = k') (k : K)
    (F : CF St Blk → ProbComp Bool) :
    prT ($ᵗ (CF St Blk) >>= F) =
      prT ($ᵗ (CF St Blk) >>= fun g => $ᵗ (St × Ad → St) >>= fun T => F (ovr blk k g T)) := by
  refine prT_congr ?_
  have h1 : 𝒟[$ᵗ (CF St Blk) >>= F] =
      𝒟[$ᵗ (CF St Blk) >>= fun g => $ᵗ (St × Ad → St) >>= fun _ => F g] :=
    evalDist_bind_congr_of_support _ _ _ fun g _ => (OracleComp.evalDist_bind_const _ _).symm
  rw [h1]
  set σ : CF St Blk × (St × Ad → St) → CF St Blk × (St × Ad → St) :=
    fun p => (ovr blk k p.1 p.2, fun x => p.1 (x.1, blk x.2 k)) with hσ
  have hσinv : Function.Involutive σ := by
    rintro ⟨g, T⟩
    refine Prod.ext ?_ ?_
    · funext q
      by_cases hq : ∃ a, q.2 = blk a k
      · obtain ⟨a, ha⟩ := hq
        obtain ⟨c, B⟩ := q
        simp only at ha
        subst ha
        simp only [hσ]
        rw [ovr_blk blk hblk]
      · simp only [hσ]
        rw [ovr_of_not _ _ _ _ _ hq, ovr_of_not _ _ _ _ _ hq]
    · funext x
      simp only [hσ]
      rw [ovr_blk blk hblk]
  have key := evalDist_uniform_pair_bijective ($ᵗ (CF St Blk)) ($ᵗ (St × Ad → St))
    SampleableType.evalDist_uniformSample SampleableType.evalDist_uniformSample σ
    hσinv.bijective (fun p => F p.1)
  rw [← key]

/-- A compression query at a block of the form `blk a k`. -/
def badK (blk : Ad → K → Blk) (k : K) : (St × Blk) ⊕ (PkSeed × Ad) → Bool
  | .inl q => decide (∃ a, q.2 = blk a k)
  | .inr _ => false

/-- Outside the bad queries, the real answers at the overridden table are the hybrid answers. -/
theorem realAns_ovr (IV : St) (sb : PkSeed → Blk) (blk : Ad → K → Blk) (out : St → Y)
    (hblk : ∀ a a' k k', blk a k = blk a' k' → a = a' ∧ k = k')
    (hne : ∀ pk a k, sb pk ≠ blk a k) (k : K) (g : CF St Blk) (T : St × Ad → St)
    (t : (St × Blk) ⊕ (PkSeed × Ad)) (ht : badK (PkSeed := PkSeed) blk k t = false) :
    realAns IV sb blk out (ovr blk k g T) k t = hybAns IV sb out g T t := by
  rcases t with q | d
  · simp only [badK, decide_eq_false_iff_not] at ht
    exact ovr_of_not blk k g T q ht
  · show out (ovr blk k g T (ovr blk k g T (IV, sb d.1), blk d.2 k)) =
      out (T (g (IV, sb d.1), d.2))
    rw [ovr_blk blk hblk, ovr_of_not blk k g T (IV, sb d.1) fun ⟨a, ha⟩ => hne _ _ _ ha]

/-- The key, drawn after the run, makes a traced compression query bad with probability at most
`1 / |K|` per compression query. -/
theorem prEvent_badK_le [Fintype K] [SampleableType K] (blk : Ad → K → Blk)
    (hblk : ∀ a a' k k', blk a k = blk a' k' → a = a' ∧ k = k')
    (l : List ((St × Blk) ⊕ (PkSeed × Ad))) :
    Pr{let k ← $ᵗ K}[l.any (badK blk k) = true] ≤
      (l.countP (fun t => decide (isCompQ (.inr t) = true)) : ℝ≥0∞) *
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
    · have h1 : Pr{let k ← $ᵗ K}[badK (PkSeed := PkSeed) blk k (.inl q) = true] ≤
          (Fintype.card K : ℝ≥0∞)⁻¹ := by
        by_cases h : ∃ k₀ a₀, q.2 = blk a₀ k₀
        · obtain ⟨k₀, a₀, h₀⟩ := h
          refine (prEvent_mono _ _ (fun k => k = k₀) fun k hk => ?_).trans
            (SampleableType.prEvent_uniformSample_eq_singleton k₀).le
          simp only [badK, decide_eq_true_eq] at hk
          obtain ⟨a, ha⟩ := hk
          exact (hblk _ _ _ _ (ha.symm.trans h₀)).2
        · rw [prEvent_eq_zero_of_forall_not _ _ fun k hk => h ?_]
          · exact zero_le
          · simp only [badK, decide_eq_true_eq] at hk
            obtain ⟨a, ha⟩ := hk
            exact ⟨k, a, ha⟩
      refine (add_le_add h1 ih).trans (le_of_eq ?_)
      simp only [isCompQ, decide_true, List.countP_cons_of_pos, Nat.cast_add, Nat.cast_one]
      ring
    · have h1 : Pr{let k ← $ᵗ K}[badK blk k (.inr d : (St × Blk) ⊕ (PkSeed × Ad)) = true] = 0 :=
        prEvent_eq_zero_of_forall_not _ _ (by simp [badK])
      rw [h1, zero_add]
      refine ih.trans (le_of_eq ?_)
      simp [isCompQ]

end Ovr

/-! ## Collisions of the renaming are collisions of the compression table -/

/-- The cell of the compression table touched by a query. -/
def cellOf (IV : St) (sb : PkSeed → Blk) : (St × Blk) ⊕ (PkSeed × Ad) → St × Blk
  | .inl q => q
  | .inr d => (IV, sb d.1)

theorem mem_dq {ι₀ D : Type} (l : List (ι₀ ⊕ D)) (d : D) : d ∈ dq l ↔ .inr d ∈ l := by
  induction l with
  | nil => simp
  | cons t l ih =>
    rcases t with t | t <;> simp [dq, List.filterMap_cons] at ih ⊢

theorem collB_of_collφ [DecidableEq St] [DecidableEq Blk] [DecidableEq PkSeed] [DecidableEq Ad]
    (IV : St) (sb : PkSeed → Blk) (hsb : Function.Injective sb) (g : CF St Blk)
    (l : List ((St × Blk) ⊕ (PkSeed × Ad))) (h : collφ (phi IV sb g) (dq l) = true) :
    collB g (l.map (cellOf IV sb)) = true := by
  simp only [collφ, decide_eq_true_eq] at h
  obtain ⟨d, hd, d', hd', hne, heq⟩ := h
  simp only [collB, decide_eq_true_eq]
  have heq' : (g (IV, sb d.1), d.2) = (g (IV, sb d'.1), d'.2) := heq
  have h1 : g (IV, sb d.1) = g (IV, sb d'.1) := (Prod.mk.inj heq').1
  have h2 : d.2 = d'.2 := (Prod.mk.inj heq').2
  refine ⟨(IV, sb d.1), List.mem_map.mpr ⟨.inr d, (mem_dq l d).mp hd, rfl⟩,
    (IV, sb d'.1), List.mem_map.mpr ⟨.inr d', (mem_dq l d').mp hd', rfl⟩, fun e => ?_, h1⟩
  exact hne (Prod.ext (hsb (Prod.mk.inj e).2) h2)

/-! ## The one-sided bound -/

section Bound

variable [Fintype St] [DecidableEq St] [SampleableType St] [Fintype Blk] [DecidableEq Blk]
  [SampleableType (CF St Blk)] [Fintype K] [SampleableType K] [Fintype PkSeed]
  [DecidableEq PkSeed] [Fintype Ad] [DecidableEq Ad] [SampleableType Y]

omit [DecidableEq St] [Fintype Blk] [Fintype PkSeed] [DecidableEq PkSeed] [DecidableEq Ad]
  [SampleableType Y] in
/-- The bad event of the override hop has probability at most `q / |K|`. -/
theorem prT_badK_le (IV : St) (sb : PkSeed → Blk) (blk : Ad → K → Blk) (out : St → Y)
    (hblk : ∀ a a' k k', blk a k = blk a' k' → a = a' ∧ k = k')
    (A : PrfAdvI St Blk PkSeed Ad Y) (q : ℕ)
    (hq : IsQueryBoundP A (fun i => isCompQ i = true) q) :
    prT ($ᵗ K >>= fun k => $ᵗ (CF St Blk) >>= fun g => $ᵗ (St × Ad → St) >>= fun T =>
      (simulateQ (trImpl (hybAns IV sb out g T)) A).run [] >>= fun z =>
        pure (z.2.any (badK blk k))) ≤ (q : ℝ≥0∞) * (Fintype.card K : ℝ≥0∞)⁻¹ := by
  have hsw := prT_swap ($ᵗ K) ($ᵗ (CF St Blk) >>= fun g => $ᵗ (St × Ad → St) >>= fun T =>
      (simulateQ (trImpl (hybAns IV sb out g T)) A).run [])
    (fun k z => pure (z.2.any (badK blk k)))
  simp only [bind_assoc] at hsw
  rw [hsw]
  refine prT_bind_le_of_forall_le _ _ fun g _ => prT_bind_le_of_forall_le _ _ fun T _ =>
    prT_bind_le_of_forall_le _ _ fun z hz => ?_
  rw [prT_bind_pure]
  refine (prEvent_badK_le blk hblk z.2).trans ?_
  have h1 := trace_countP_le (hybAns IV sb out g T) (fun i => isCompQ i = true) A q hq [] z hz
  gcongr
  simpa using h1

omit [Fintype PkSeed] [Fintype Ad] [SampleableType Y] in
/-- For a fixed function table, two queried inputs collide under `phi` with probability at most
`n² / |St|` over the compression table. -/
theorem prT_collφ_le (IV : St) (sb : PkSeed → Blk) (hsb : Function.Injective sb)
    (A : PrfAdvI St Blk PkSeed Ad Y) (n : ℕ) (hn : IsQueryBoundP A (fun i => i.isRight = true) n)
    (R : PkSeed × Ad → Y) :
    prT ($ᵗ (CF St Blk) >>= fun g => (simulateQ (trImpl (idealAns g R)) A).run [] >>= fun z =>
      pure (collφ (phi IV sb g) (dq z.2))) ≤
        ((n ^ 2 : ℕ) : ℝ≥0∞) * (Fintype.card St : ℝ≥0∞)⁻¹ := by
  have hc := prT_coll_le (C := St × Blk) (V := St)
    (spec := hS St Blk + ((PkSeed × Ad) →ₒ Y)) (cellOf IV sb)
    (fun g => idealAns g R) (fun g g' t h => by
      rcases t with q | d
      · exact h
      · rfl) A n hn
  refine le_trans ?_ hc
  refine prT_bind_mono _ _ _ fun g _ => ?_
  exact prT_bind_pure_mono _ _ _ fun z hz => collB_of_collφ IV sb hsb g z.2 hz

/-- **One-sided bound**: the real experiment returns `true` at most as often as the ideal one,
plus `q / |K| + (q + qO)² / |St|`. -/
theorem prT_real_le (IV : St) (sb : PkSeed → Blk) (blk : Ad → K → Blk) (out : St → Y)
    (hblk : ∀ a a' k k', blk a k = blk a' k' → a = a' ∧ k = k')
    (hne : ∀ pk a k, sb pk ≠ blk a k) (hsb : Function.Injective sb)
    (hout : ∀ p : Y → Prop, Pr{let u ← $ᵗ St}[p (out u)] = Pr{let y ← $ᵗ Y}[p y])
    (A : PrfAdvI St Blk PkSeed Ad Y) (q qO : ℕ)
    (hq : IsQueryBoundP A (fun i => isCompQ i = true) q)
    (hO : IsQueryBoundP A (fun i => isPrfQ i = true) qO) :
    prT (prfRealGameI IV sb blk out A) ≤
      prT (prfIdealGameI A) + ((q : ℝ≥0∞) * (Fintype.card K : ℝ≥0∞)⁻¹ +
        (((q + qO) ^ 2 : ℕ) : ℝ≥0∞) * (Fintype.card St : ℝ≥0∞)⁻¹) := by
  -- the hybrid, and its two bad events
  set H : ProbComp Bool := $ᵗ (CF St Blk) >>= fun g => $ᵗ (St × Ad → St) >>= fun T =>
    simulateQ (ansImpl (hybAns IV sb out g T)) A with hH
  -- real ≤ hybrid + bad key
  have hreal : prT (prfRealGameI IV sb blk out A) ≤
      prT H + (q : ℝ≥0∞) * (Fintype.card K : ℝ≥0∞)⁻¹ := by
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
    exact add_le_add le_rfl (prT_badK_le IV sb blk out hblk A q hq)
  -- hybrid ≤ ideal + collision
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
      ≤ prT H + (q : ℝ≥0∞) * (Fintype.card K : ℝ≥0∞)⁻¹ := hreal
    _ ≤ prT (prfIdealGameI A) + (((q + qO) ^ 2 : ℕ) : ℝ≥0∞) * (Fintype.card St : ℝ≥0∞)⁻¹ +
          (q : ℝ≥0∞) * (Fintype.card K : ℝ≥0∞)⁻¹ := add_le_add hhyb le_rfl
    _ = _ := by rw [add_assoc, add_comm ((((q + qO) ^ 2 : ℕ) : ℝ≥0∞) * _)]

end Bound

/-! ## Negating the distinguisher -/

/-- The distinguisher with its output bit negated. -/
def negAdv (A : PrfAdvI St Blk PkSeed Ad Y) : PrfAdvI St Blk PkSeed Ad Y :=
  show OracleComp (unifSpec + (hS St Blk + ((PkSeed × Ad) →ₒ Y))) Bool from
    not <$> (show OracleComp (unifSpec + (hS St Blk + ((PkSeed × Ad) →ₒ Y))) Bool from A)

theorem prT_not_map (X : ProbComp Bool) : prT (not <$> X) = 𝒟[X] {false} := by
  unfold prT
  rw [Functor.map_map, prEvent_eq_evalDist_of_discrete]
  congr 1
  ext b
  cases b <;> simp

theorem prfRealGameI_not [SampleableType K] [SampleableType (CF St Blk)] [SampleableType Y]
    [DecidableEq PkSeed] [DecidableEq Ad] (IV : St) (sb : PkSeed → Blk) (blk : Ad → K → Blk)
    (out : St → Y) (A : PrfAdvI St Blk PkSeed Ad Y) :
    prfRealGameI IV sb blk out (negAdv A) = not <$> prfRealGameI IV sb blk out A := by
  simp only [prfRealGameI, negAdv, PrfAdvI.inst, prfRealExperiment, simulateQ_map, map_bind]

theorem prfIdealGameI_not [SampleableType (CF St Blk)] [SampleableType Y]
    [DecidableEq PkSeed] [DecidableEq Ad] (A : PrfAdvI St Blk PkSeed Ad Y) :
    prfIdealGameI (negAdv A) = not <$> prfIdealGameI A := by
  simp only [prfIdealGameI, negAdv, PrfAdvI.inst, prfIdealExperiment, simulateQ_map, map_bind,
    StateT.run'_eq, StateT.run_map, Functor.map_map]

end Ideal.Prf

namespace Ideal

open Ideal.HP Ideal.Prf

variable {St Blk K PkSeed Ad Y : Type}

/-- **PRF security in the ideal-compression model.**  Let
`f_g(k, (pk, a)) = out (g (g (IV, sb pk), blk a k))` where `(a, k) ↦ blk a k` is injective, no
seed block is a key block, `sb` is injective and `out` of a uniform chaining value is uniform.
A distinguisher making at most `q` compression queries and `qO` function queries has advantage
at most `q / |K| + (q + qO)² / |St|`. -/
theorem prfAdvantageI_le [Fintype St] [DecidableEq St] [SampleableType St] [Fintype Blk]
    [DecidableEq Blk] [SampleableType (CF St Blk)] [Fintype K] [SampleableType K]
    [Fintype PkSeed] [DecidableEq PkSeed] [Fintype Ad] [DecidableEq Ad] [SampleableType Y]
    (IV : St) (sb : PkSeed → Blk) (blk : Ad → K → Blk) (out : St → Y)
    (hblk : ∀ a a' k k', blk a k = blk a' k' → a = a' ∧ k = k')
    (hne : ∀ pk a k, sb pk ≠ blk a k) (hsb : Function.Injective sb)
    (hout : ∀ p : Y → Prop, Pr{let u ← $ᵗ St}[p (out u)] = Pr{let y ← $ᵗ Y}[p y])
    (A : PrfAdvI St Blk PkSeed Ad Y) (q qO : ℕ)
    (hq : IsQueryBoundP A (fun i => isCompQ i = true) q)
    (hO : IsQueryBoundP A (fun i => isPrfQ i = true) qO) :
    prfAdvantageI IV sb blk out A ≤
      (q : ℝ≥0∞) * (Fintype.card K : ℝ≥0∞)⁻¹ +
        (((q + qO) ^ 2 : ℕ) : ℝ≥0∞) * (Fintype.card St : ℝ≥0∞)⁻¹ := by
  unfold prfAdvantageI prfRealIdeal prfIdealIdeal
  refine MeasureTheory.Measure.boolDist_le_of_apply_le _ _ fun b => ?_
  cases b
  · have h := prT_real_le IV sb blk out hblk hne hsb hout (negAdv A) q qO
      ((isQueryBoundP_map_iff _ _ _).mpr hq) ((isQueryBoundP_map_iff _ _ _).mpr hO)
    rwa [prfRealGameI_not, prfIdealGameI_not, prT_not_map, prT_not_map] at h
  · have h := prT_real_le IV sb blk out hblk hne hsb hout A q qO hq hO
    rwa [prT_eq, prT_eq] at h

end Ideal

#print axioms Ideal.prfAdvantageI_le
