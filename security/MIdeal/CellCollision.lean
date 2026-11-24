import Ideal.Games.ItsrTape

namespace MIdeal.CellCollision
open Ideal Ideal.HP Ideal.Itsr Ideal.Prf OracleComp OracleSpec ENNReal

variable {C V Y : Type} [DecidableEq C] [Finite C] [Fintype Y] [DecidableEq Y]
variable [SampleableType V] [SampleableType Y] [SampleableType (C → V)]

abbrev Reader (C V : Type) := OracleComp (unifSpec + (C →ₒ V))

/-- A reader chooses two cells, then the verifier reads both outputs. -/
def check (out : V → Y) (A : Reader C V (C × C)) : Reader C V Bool := do
  let (c,d) ← A
  let u ← (unifSpec + (C →ₒ V)).query (.inr c)
  let v ← (unifSpec + (C →ₒ V)).query (.inr d)
  return decide (c ≠ d ∧ out u = out v)

theorem check_bound (out : V → Y) (A : Reader C V (C × C)) (q : ℕ)
    (hq : IsQueryBoundP A (fun i => i.isRight = true) q) :
    IsQueryBoundP (check out A) (fun i => i.isRight = true) (q + 2) := by
  apply isQueryBoundP_bind hq
  rintro ⟨c,d⟩ _
  simp [isQueryBoundP_query_bind_iff]

private theorem bad_of_pair (out : V → Y) (init : Y) (g : C → V) (c d : C) (l : List C)
    (hne : c ≠ d) (he : out (g c) = out (g d)) :
    badV init ((logU id d (logU id c l)).map fun t => out (g t)) = true := by
  apply decide_eq_true
  left
  intro nodup
  exact hne (List.inj_on_of_nodup_map nodup (subset_logU id d _ _ (mem_logU id c l)) (mem_logU id d _) he)

/-- Birthday bound for two distinct cells selected with adaptive public table access.
The projection of a fresh table output must be uniform on the digest space. -/
theorem bound (out : V → Y) (init : Y)
    (uniform : ∀ P : Y → Prop, Pr{let u ← $ᵗ V}[P (out u)] = Pr{let y ← $ᵗ Y}[P y])
    (A : Reader C V (C × C)) (q : ℕ) (hq : IsQueryBoundP A (fun i => i.isRight = true) q) :
    prT ($ᵗ (C → V) >>= fun g => simulateQ (ansImpl (spec := C →ₒ V) g) A >>= fun p =>
      pure (decide (p.1 ≠ p.2 ∧ out (g p.1) = out (g p.2)))) ≤
      (((q+2)^2 : ℕ) : ℝ≥0∞) * (Fintype.card Y : ℝ≥0∞)⁻¹ := by
  apply le_trans _ ((prT_tape_le (spec := C →ₒ V) id (fun g t => g t) (fun _ _ _ h => h)
    out uniform (badV init) (badV_mono init) (check out A) (q+2) (check_bound out A q hq)).trans (prT_tape_bad_le init _))
  apply prT_bind_mono
  intro g _
  rw [← fst_map_run_stImpl (spec := C →ₒ V) g (logU id) A []]
  simp only [check, simulateQ_bind, StateT.run_bind, bind_assoc, bind_map_left]
  apply prT_bind_mono
  rintro ⟨⟨c,d⟩,l⟩ _
  simp only [simulateQ_spec_query, stImpl, StateT.run_mk, pure_bind, simulateQ_pure, StateT.run_pure]
  by_cases h : c ≠ d ∧ out (g c) = out (g d)
  · rw [bad_of_pair out init g c d l h.1 h.2]
    simp [h, prT_pure]
  · simp [h, prT_pure]
end MIdeal.CellCollision
