import Integration.SlhDsaShakePermutationSparseShadow
import Integration.SlhDsaShakePermutationSparseFake

/-! Label each classical first-phase permutation query by its current tweak.
Up to a root-capacity return and an auxiliary-image hit, the local shadow
program and the linked whole permutation have the same transcript. -/
namespace Reduction.ShakePermutation.SparsePort.Phase
open Classical OracleComp OracleSpec Quantum SetOracle ENNReal
noncomputable section
set_option linter.unusedSectionVars false
set_option maxRecDepth 8192
variable {T J Y Z α β : Type} [DecidableEq T]

abbrev Tagged (T : Type) := unifSpec + ((T × Words) →ₒ Words)

def run (f : T → Words → Words) (ev : α → ℝ≥0∞) (p : OracleComp (Tagged T) α) :=
  OracleComp.construct (C := fun _ => ℝ≥0∞) ev (fun i _ k => match i with
    | .inl _ => uniformMean k
    | .inr (d,x) => k (f d x)) p

def erase : QueryImpl (Tagged T) (OracleComp Trace.Fwd)
  | .inl n => liftM (Trace.Fwd.query (.inl n))
  | .inr (_,w) => liftM (Trace.Fwd.query (.inr w))

def valid (a : J ↪ Words) (tag : J → T) (p : OracleComp (Tagged T) α) : Prop :=
  OracleComp.construct (C := fun _ => Prop) (fun _ => True) (fun i _ k => match i with
    | .inl _ => ∀ r, k r
    | .inr (d,w) => (∀ j, a j = w → tag j = d) ∧ ∀ y, ¬Trace.zeroCap y → k y) p

theorem valid_bind (a : J ↪ Words) (tag : J → T) (p : OracleComp (Tagged T) α)
    (k : α → OracleComp (Tagged T) β) (h : valid a tag p) (hk : ∀ r, valid a tag (k r)) :
    valid a tag (p >>= k) := by
  induction p using OracleComp.inductionOn with
  | pure r => simpa only [pure_bind] using hk r
  | query_bind i f ih =>
    rw [bind_assoc]
    rcases i with n|⟨d,w⟩
    · exact fun r => ih r (h r)
    · exact ⟨h.1,fun y hy => ih y (h.2 y hy)⟩

theorem run_le (f : T → Words → Words) (ev : α → ℝ≥0∞) (h : ∀ z, ev z ≤ 1)
    (p : OracleComp (Tagged T) α) : run f ev p ≤ 1 := by
  induction p using OracleComp.inductionOn with
  | pure r => exact h r
  | query_bind i k ih =>
    rcases i with n|⟨d,x⟩
    · exact ShakeXof.mean_le_const ih
    · exact ih _

def risk (π : Permutation) (bad : Words → Prop) [DecidablePred bad] (p : OracleComp (Tagged T) α) :=
  Classic.eager π (fun b => if b then 1 else 0) (Trace.monitor bad (simulateQ erase p))

private theorem risk_uniform (π : Permutation) (bad : Words → Prop) [DecidablePred bad] (n : ℕ)
    (k : Fin (n+1) → OracleComp (Tagged T) α) :
    risk π bad ((liftM ((Tagged T).query (.inl n)) : OracleComp (Tagged T) _) >>= k) = uniformMean (fun r => risk π bad (k r)) := by
  simp only [risk,simulateQ_bind,simulateQ_spec_query,erase]
  rfl

private theorem risk_step (π : Permutation) (bad : Words → Prop) [DecidablePred bad] (d : T)
    (x : Words) (k : Words → OracleComp (Tagged T) α) :
    risk π bad ((liftM ((Tagged T).query (.inr (d,x))) : OracleComp (Tagged T) Words) >>= k) =
      if bad (π x) then 1 else risk π bad (k (π x)) := by
  simp only [risk,simulateQ_bind,simulateQ_spec_query,erase]
  change Classic.eager π _ (if bad (π x) then pure true else _) = _
  split <;> rfl

variable (e : Words ≃ Y × Z) (a : J ↪ Words) (π : Permutation) (s : J → Z)
  (tag : J → T) (F : J → Y) [Fintype J]

theorem coupled (ok : Function.Injective (Program.pair a π (target e s F)))
    (p : OracleComp (Tagged T) α) (cert : valid a tag p)
    (ev : α → ℝ≥0∞) (bounded : ∀ r, ev r ≤ 1) :
    let z := Program.resample a (π,target e s F)
    run (fun _ => z.1) ev p ≤ run (shadow e a π s tag F) ev p + risk z.1 Trace.zeroCap p +
      risk z.1 (Trace.fake z.2) p := by
  let z := Program.resample a (π,target e s F)
  dsimp only
  induction p using OracleComp.inductionOn with
  | pure x => exact le_self_add.trans le_self_add
  | query_bind i k ih =>
    rcases i with n|⟨d,x⟩
    · rw [risk_uniform,risk_uniform]
      change uniformMean (fun r => run (fun _ : T => z.1) ev (k r)) ≤
        uniformMean (fun r => run (shadow e a π s tag F) ev (k r)) +
        uniformMean (fun r => risk z.1 Trace.zeroCap (k r)) + uniformMean (fun r => risk z.1 (Trace.fake z.2) (k r))
      have h := Finset.sum_le_sum (s:=Finset.univ) (fun r _ => mul_le_mul' (le_refl (unifW _ r)) (ih r (cert r)))
      simpa only [uniformMean,mul_add,Finset.sum_add_distrib] using h
    · rw [risk_step,risk_step]
      let y := z.1 x
      by_cases root : Trace.zeroCap y
      · rw [ite_eq_left root]
        apply (run_le (fun _ : T => z.1) ev bounded _).trans
        exact le_add_self.trans le_self_add
      by_cases hit : Trace.fake z.2 y
      · rw [ite_eq_left hit]
        apply (run_le (fun _ : T => z.1) ev bounded _).trans
        exact le_add_self
      have hclear (j : J) : y ≠ z.2 j := fun he => hit ⟨j,he.symm⟩
      have same := shadow_agrees e a π s tag F ok d x cert.1 hclear
      rw [ite_eq_right (show ¬ Trace.zeroCap (z.1 x) from root),ite_eq_right (show ¬ Trace.fake z.2 (z.1 x) from hit)]
      change run _ ev (k y) ≤ run _ ev (k (shadow e a π s tag F d x)) + _ + _
      rw [same]; exact ih y (cert.2 y root)

end
end Reduction.ShakePermutation.SparsePort.Phase
#print axioms Reduction.ShakePermutation.SparsePort.Phase.coupled
