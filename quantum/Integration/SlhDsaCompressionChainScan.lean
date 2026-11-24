import Integration.SlhDsaCompressionCost

namespace Reduction.Compression.ChainScan
open MLink Ideal SLHDSA OracleComp OracleSpec PQ.Interactive
variable {S0 B0 T : Type} [DecidableEq S0] [DecidableEq B0] [DecidableEq T] (p : S0 → T)

def scan (g : CF S0 B0) (c d : S0) :
    List B0 → List B0 → Option ((S0 × B0) × (S0 × B0))
  | b :: bs, e :: es =>
    let u := (c,b)
    let v := (d,e)
    if u ≠ v ∧ p (g u) = p (g v) then some (u,v)
    else scan g (g u) (g v) bs es
  | _, _ => none

theorem scan_sound (g : CF S0 B0) (c d : S0) (bs es : List B0)
    (u v : (S0 × B0)) (h : scan p g c d bs es = some (u,v)) :
    u ≠ v ∧ p (g u) = p (g v) := by
  induction bs generalizing c d es with
  | nil => simp [scan] at h
  | cons b bs ih =>
    cases es with
    | nil => simp [scan] at h
    | cons e es =>
      simp only [scan] at h
      split at h
      · rename_i hit
        cases h
        exact hit
      · exact ih _ _ _ h

theorem scan_none (g : CF S0 B0) (c d : S0) (bs es : List B0)
    (len : bs.length = es.length) (ne : bs ≠ []) (h : scan p g c d bs es = none)
    (eq : p (mdFold g c bs) = p (mdFold g d es)) : c = d ∧ bs = es := by
  induction bs generalizing c d es with
  | nil => contradiction
  | cons b bs ih =>
    cases es with
    | nil => simp at len
    | cons e es =>
      simp only [scan] at h
      split at h
      · contradiction
      · rename_i miss
        simp only [List.length_cons, Nat.succ.injEq] at len
        change p (mdFold g (g (c,b)) bs) = p (mdFold g (g (d,e)) es) at eq
        have next : p (g (c,b)) = p (g (d,e)) ∧ bs = es := by
          by_cases empty : bs = []
          · subst bs
            have he : es = [] := List.length_eq_zero_iff.mp len.symm
            subst es
            exact ⟨eq,rfl⟩
          · obtain ⟨hg,he⟩ := ih _ _ _ len empty h eq
            exact ⟨congrArg (p) hg,he⟩
        have cell : (c,b) = (d,e) := by
          by_contra diff
          exact miss ⟨diff,next.1⟩
        exact ⟨congrArg Prod.fst cell,congrArg₂ List.cons (congrArg Prod.snd cell) next.2⟩

theorem scan_cost (tab : (Input → Output) → CF S0 B0)
    (read_cost : ∀ u, EvalCost (fun H => (pure (tab H u) : ProbComp S0)) 1)
    (c d : S0) (bs es : List B0) :
    EvalCost (fun H => (pure (scan p (tab H) c d bs es) : ProbComp (Option ((S0 × B0) × (S0 × B0)))))
      (2 * bs.length) := by
  induction bs generalizing c d es with
  | nil => exact EvalCost.const (pure none)
  | cons b bs ih =>
    cases es with
    | nil => exact (EvalCost.const (pure none)).mono (Nat.zero_le _)
    | cons e es =>
      let step := fun (c' d' : S0) (H : Input → Output) =>
        (pure (if (c,b) ≠ (d,e) ∧ p c' = p d' then some ((c,b),(d,e))
          else scan p (tab H) c' d' bs es) : ProbComp (Option ((S0 × B0) × (S0 × B0))))
      have inner (c' d' : S0) : EvalCost (step c' d') (2 * bs.length) := by
        unfold step
        split
        · exact (EvalCost.const _).mono (Nat.zero_le _)
        · exact ih c' d' es
      have cost := EvalCost.bind (read_cost (c,b)) (fun c' =>
        EvalCost.bind (read_cost (d,e)) (inner c'))
      rw [show 2 * (b :: bs).length = 1 + (1 + 2 * bs.length) by simp; omega]
      simpa only [step, pure_bind, scan] using cost

end Reduction.Compression.ChainScan
