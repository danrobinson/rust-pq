import Ideal.Games.PrfLemmas
import VCVio.OracleComp.QueryTracking.RandomOracle.Tape

/-!
# Adaptive readers of a uniform table and tapes of independent uniform values

A program whose oracle queries each read one cell of a uniformly random table `g : C → V` is run
while logging the *distinct* cells it reads, in order of first read (`logU`).  The values of the
logged cells are independent uniform values: for every event `W` on value lists that is monotone
under list insertion (`l <+ l' → W l → W l'`),

`Pr[W (log.map (out ∘ g))] ≤ Pr[W (tape)]`,  `tape` = `n` independent uniform values

(`prT_tape_le`), where `n` bounds the number of oracle queries and `out : V → Y` maps uniform
values to uniform values.

`prT_tape_bad_le`: a tape of `n` uniform values has a repeated entry or contains a fixed value
`v₀` with probability at most `n² / |V|`.
-/

open OracleComp OracleSpec ENNReal

namespace Ideal.Itsr

open Ideal.HP Ideal.Prf AnswerTape

variable {C V Y α : Type}

/-! ## Monotone tape events -/

section Tape

variable [SampleableType Y]

theorem prT_tape_succ_ge (W : List Y → Bool) (hW : ∀ l l' : List Y, l.Sublist l' → W l = true → W l' = true)
    (pre : List Y) (m : ℕ) :
    prT (tapeList Y m >>= fun r => pure (W (pre ++ r))) ≤
      prT (tapeList Y (m + 1) >>= fun r => pure (W (pre ++ r))) := by
  rw [tapeList_succ]
  simp only [bind_assoc, pure_bind]
  rw [← prT_bind_const ($ᵗ Y) (tapeList Y m >>= fun r => pure (W (pre ++ r)))]
  refine prT_bind_mono _ _ _ fun u _ => ?_
  refine prT_bind_pure_mono _ _ _ fun r h => hW _ _ ?_ h
  exact List.Sublist.append (List.Sublist.refl _) (List.sublist_cons_self _ _)

theorem prT_tape_mono (W : List Y → Bool) (hW : ∀ l l' : List Y, l.Sublist l' → W l = true → W l' = true)
    (pre : List Y) {m n : ℕ} (h : m ≤ n) :
    prT (tapeList Y m >>= fun r => pure (W (pre ++ r))) ≤
      prT (tapeList Y n >>= fun r => pure (W (pre ++ r))) := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (prT_tape_succ_ge W hW pre _)

end Tape

/-! ## The log of distinct cells -/

section Log

variable [DecidableEq C] {ι : Type} {spec : OracleSpec ι}

/-- Log the cell of a query if it is new. -/
def logU (cell : ι → C) (t : ι) (s : List C) : List C :=
  if cell t ∈ s then s else s ++ [cell t]

theorem logU_of_mem {cell : ι → C} {t : ι} {s : List C} (h : cell t ∈ s) : logU cell t s = s := by
  simp [logU, h]

theorem logU_of_not_mem {cell : ι → C} {t : ι} {s : List C} (h : cell t ∉ s) :
    logU cell t s = s ++ [cell t] := by
  simp [logU, h]

theorem subset_logU (cell : ι → C) (t : ι) (s : List C) : ∀ c ∈ s, c ∈ logU cell t s := by
  intro c hc
  unfold logU
  split
  · exact hc
  · exact List.mem_append_left _ hc

theorem mem_logU (cell : ι → C) (t : ι) (s : List C) : cell t ∈ logU cell t s := by
  unfold logU
  split
  · assumption
  · simp

/-- **Tape domination** (generalised over the log so far, whose cells are frozen to `t`). -/
theorem prT_tape_le_aux [Finite C] [SampleableType V] [SampleableType Y] [SampleableType (C → V)]
    (cell : ι → C) (ans : (C → V) → (t : ι) → spec.Range t)
    (hans : ∀ g g' t, g (cell t) = g' (cell t) → ans g t = ans g' t)
    (out : V → Y)
    (hout : ∀ p : Y → Prop, Pr{let u ← $ᵗ V}[p (out u)] = Pr{let y ← $ᵗ Y}[p y])
    (W : List Y → Bool) (hW : ∀ l l' : List Y, l.Sublist l' → W l = true → W l' = true)
    (oa : OracleComp (unifSpec + spec) α) (n : ℕ)
    (hn : IsQueryBoundP oa (fun i => i.isRight = true) n) (s : List C) (t : C → V) :
    prT ($ᵗ (C → V) >>= fun g =>
        (simulateQ (stImpl (ans (mix s t g)) (logU cell)) oa).run s >>= fun z =>
          pure (W (z.2.map fun c => out (mix s t g c)))) ≤
      prT (tapeList Y n >>= fun r => pure (W (s.map (fun c => out (t c)) ++ r))) := by
  induction oa using OracleComp.inductionOn generalizing n s t with
  | pure x =>
    have h0 : ∀ g : C → V, (s.map fun c => out (mix s t g c)) = s.map fun c => out (t c) :=
      fun g => List.map_congr_left fun c hc => by rw [mix_of_mem hc]
    simp only [simulateQ_pure, StateT.run_pure, pure_bind, h0]
    rw [prT_bind_const]
    refine (prT_tape_mono W hW _ (Nat.zero_le n)).trans' ?_
    simp
  | query_bind t₀ k ih =>
    rw [isQueryBoundP_query_bind_iff] at hn
    rcases t₀ with m | t₀
    · simp only [run_stImpl_inl_bind, bind_assoc]
      rw [prT_swap]
      refine prT_bind_le_of_forall_le _ _ fun x _ => ?_
      exact ih x n (hn.2 x) s t
    · have hpos : 0 < n := hn.1.resolve_left (by simp)
      have hk := fun x => hn.2 x
      simp only [Sum.isRight_inr, ite_true] at hk
      by_cases hc : cell t₀ ∈ s
      · have hans' : ∀ g : C → V, ans (mix s t g) t₀ = ans t t₀ := fun g =>
          hans _ _ _ (mix_of_mem hc t g)
        simp only [run_stImpl_inr_bind, hans', logU_of_mem hc]
        exact (ih (ans t t₀) (n - 1) (hk _) s t).trans (prT_tape_mono W hW _ (Nat.sub_le n 1))
      · rw [prT_freeze hc t (fun M =>
          (simulateQ (stImpl (ans M) (logU cell))
            (liftM ((unifSpec + spec).query (.inr t₀)) >>= k)).run s >>=
            fun z => pure (W (z.2.map fun c => out (M c))))]
        have hans' : ∀ (v : V) (g : C → V),
            ans (mix (s ++ [cell t₀]) (Function.update t (cell t₀) v) g) t₀ =
              ans (Function.update t (cell t₀) v) t₀ := fun v g =>
          hans _ _ _ (mix_of_mem (by simp) _ g)
        simp only [run_stImpl_inr_bind, hans', logU_of_not_mem hc]
        have hstep : ∀ v : V,
            prT ($ᵗ (C → V) >>= fun g =>
              (simulateQ (stImpl (ans (mix (s ++ [cell t₀]) (Function.update t (cell t₀) v) g))
                (logU cell)) (k (ans (Function.update t (cell t₀) v) t₀))).run (s ++ [cell t₀]) >>=
                fun z => pure (W (z.2.map fun c =>
                  out (mix (s ++ [cell t₀]) (Function.update t (cell t₀) v) g c)))) ≤
            prT (tapeList Y (n - 1) >>= fun r =>
              pure (W (s.map (fun c => out (t c)) ++ out v :: r))) := by
          intro v
          refine (ih _ (n - 1) (hk _) (s ++ [cell t₀]) (Function.update t (cell t₀) v)).trans
            (le_of_eq ?_)
          have e : (s ++ [cell t₀]).map (fun c => out (Function.update t (cell t₀) v c)) =
              s.map (fun c => out (t c)) ++ [out v] := by
            rw [List.map_append]
            congr 1
            · exact List.map_congr_left fun c hcs => by
                rw [Function.update_of_ne (fun e : c = cell t₀ => hc (e ▸ hcs))]
            · simp
          simp only [e, List.append_assoc, List.singleton_append]
        refine (prT_bind_mono _ _ _ fun v _ => hstep v).trans (le_of_eq ?_)
        rw [prT_bind_out out hout (fun y => tapeList Y (n - 1) >>= fun r =>
          pure (W (s.map (fun c => out (t c)) ++ y :: r)))]
        obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
        rw [tapeList_succ]
        simp only [bind_assoc, pure_bind, Nat.add_sub_cancel]

/-- **Tape domination.**  Every oracle query `t` reads the cell `cell t` of a uniform table.  For
a program making at most `n` oracle queries and an insertion-monotone event `W`, the `out`-values
of the distinct cells read (in order of first read) satisfy `W` at most as often as a tape of `n`
independent uniform values. -/
theorem prT_tape_le [Finite C] [SampleableType V] [SampleableType Y] [SampleableType (C → V)]
    (cell : ι → C) (ans : (C → V) → (t : ι) → spec.Range t)
    (hans : ∀ g g' t, g (cell t) = g' (cell t) → ans g t = ans g' t)
    (out : V → Y)
    (hout : ∀ p : Y → Prop, Pr{let u ← $ᵗ V}[p (out u)] = Pr{let y ← $ᵗ Y}[p y])
    (W : List Y → Bool) (hW : ∀ l l' : List Y, l.Sublist l' → W l = true → W l' = true)
    (oa : OracleComp (unifSpec + spec) α) (n : ℕ)
    (hn : IsQueryBoundP oa (fun i => i.isRight = true) n) :
    prT ($ᵗ (C → V) >>= fun g =>
        (simulateQ (stImpl (ans g) (logU cell)) oa).run [] >>= fun z =>
          pure (W (z.2.map fun c => out (g c)))) ≤
      prT (tapeList Y n >>= fun r => pure (W r)) := by
  have h := prT_tape_le_aux cell ans hans out hout W hW oa n hn [] (fun _ => Classical.arbitrary V)
  simpa only [mix_nil, List.map_nil, List.nil_append] using h

end Log

/-! ## Repetitions and a fixed value on a tape -/

section Bad

variable [DecidableEq V]

/-- The value list has a repeated entry or contains `v₀`. -/
def badV (v₀ : V) (l : List V) : Bool := decide (¬ l.Nodup ∨ v₀ ∈ l)

theorem badV_mono (v₀ : V) (l l' : List V) (h : l.Sublist l') (hb : badV v₀ l = true) :
    badV v₀ l' = true := by
  simp only [badV, decide_eq_true_eq] at hb ⊢
  rcases hb with hb | hb
  · exact Or.inl fun hn => hb (hn.sublist h)
  · exact Or.inr (h.subset hb)

theorem prT_tape_bad_le [Fintype V] [SampleableType V] (v₀ : V) (n : ℕ) :
    prT (tapeList V n >>= fun r => pure (badV v₀ r)) ≤
      ((n ^ 2 : ℕ) : ℝ≥0∞) * (Fintype.card V : ℝ≥0∞)⁻¹ := by
  induction n with
  | zero => simp [badV, prT_pure]
  | succ m ih =>
    rw [tapeList_succ]
    simp only [bind_assoc, pure_bind]
    rw [prT_swap]
    refine (prT_bind_le_prEvent_add (tapeList V m) _ (fun r => badV v₀ r = true)
      (ε := ((m + 1 : ℕ) : ℝ≥0∞) * (Fintype.card V : ℝ≥0∞)⁻¹) fun r hr hb => ?_).trans ?_
    · have hlen : r.length = m := by
        rw [tapeList_eq_map_answerTape, support_map] at hr
        obtain ⟨v, -, rfl⟩ := hr
        simp
      rw [prT_bind_pure]
      refine (prEvent_mono _ _ (fun u => ∃ c' ∈ v₀ :: r, u = id c') fun u hu => ?_).trans
        ((prEvent_mem_values_le id (v₀ :: r)).trans (le_of_eq (by simp [hlen])))
      simp only [badV, decide_eq_true_eq, not_or, not_not] at hb hu
      simp only [List.nodup_cons, List.mem_cons, id] at hu ⊢
      rcases hu with hu | hu | hu
      · by_cases hur : u ∈ r
        · exact ⟨u, Or.inr hur, rfl⟩
        · exact absurd hb.1 (fun h => hu ⟨hur, h⟩)
      · exact ⟨v₀, Or.inl rfl, hu.symm⟩
      · exact absurd hu hb.2
    · rw [← prT_bind_pure]
      refine (add_le_add ih le_rfl).trans ?_
      rw [← add_mul, ← Nat.cast_add]
      refine mul_le_mul_left (Nat.cast_le.mpr ?_) _
      nlinarith

end Bad

end Ideal.Itsr

#print axioms Ideal.Itsr.prT_tape_le
#print axioms Ideal.Itsr.prT_tape_bad_le
