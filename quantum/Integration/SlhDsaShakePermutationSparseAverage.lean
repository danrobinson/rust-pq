import Integration.SlhDsaShakePermutationSparsePhase

/-! Statistical transfer with a classical local-tweak phase followed by
an arbitrary joint quantum experiment on the shared two-way port. -/
namespace Reduction.ShakePermutation.SparsePort.Phase
open Classical SetOracle Classic OracleComp PQ.Interactive ENNReal
noncomputable section
set_option maxRecDepth 16000
set_option maxHeartbeats 1500000
set_option linter.unusedSectionVars false
variable {J Y Z T α : Type} [Fintype J] [DecidableEq J] [Fintype Y] [DecidableEq Y] [Nonempty Y]
 [Fintype Z] [DecidableEq Z] [Nonempty Z] [DecidableEq T]
variable (e : Words ≃ Y × Z) (a : J ↪ Words) (base : J) (tag : J → T)
variable (P : OracleComp (Tagged T) α) (W : (Port → Words) → (J → Y) → α → ℝ≥0∞)

private theorem avg_add {X : Type} [Fintype X] (f g : X → ℝ≥0∞) :
    uniformMean (fun x => f x + g x) = uniformMean f + uniformMean g := by
  simp only [uniformMean,mul_add,Finset.sum_add_distrib]

private theorem avg_mono {X : Type} [Fintype X] {f g : X → ℝ≥0∞} (h : ∀ x, f x ≤ g x) :
    uniformMean f ≤ uniformMean g :=
  Finset.sum_le_sum fun x _ => mul_le_mul' (le_refl _) (h x)

private theorem switch (V : Permutation → (J → Words) → ℝ≥0∞) :
    uniformMean (fun π => uniformMean (V π)) = uniformMean (fun π => uniformMean (fun t =>
      V (Program.resample a (π,t)).1 (Program.resample a (π,t)).2)) := by
  let v := Function.Involutive.toPerm _ (Program.resample_involutive a)
  have h := Equiv.sum_comp v (fun z => unifW Permutation z.1 * (unifW (J → Words) z.2 * V z.1 z.2))
  have he (z) : v z = Program.resample a z := rfl
  simp only [he] at h
  simpa only [uniformMean,Finset.mul_sum,Fintype.sum_prod_type,unifW] using h.symm

def actual (π : Permutation) := run (fun _ : T => π) (W (oracle π) (exactTable e a π)) P

def ideal (π : Permutation) (w : Parts J Y Z) :=
  run (shadow e a π w.2 tag w.1) (W (simulatedPort e a π w.2 base w.1) w.1) P

def error (π : Permutation) (t : J → Words) :=
  risk π Trace.zeroCap P + risk π (Trace.fake t) P

private def bad (π : Permutation) (t : J → Words) :=
  Trace.indicator (¬Function.Injective (Program.pair a π t)) +
    Trace.indicator (¬small (splitWorld e t).2)

private theorem bad_mean (π : Permutation) (jcap : Fintype.card J ≤ 2^768) (zcap : 2^1344 ≤ Fintype.card Z) :
    uniformMean (bad e a π) ≤ ((2:ℝ≥0∞)^63)⁻¹ + ((2:ℝ≥0∞)^384)⁻¹ := by
  unfold bad
  rw [avg_add]
  apply add_le_add
  · apply rate
    have wordcard : Fintype.card Words = 2^1600 := by
      change Fintype.card (Fin 25 → UInt64) = _
      rw [Fintype.card_fun,Fintype.card_fin,← FinEnum.card_eq_fintypeCard,FinEnum.card_UInt64,← pow_mul]
    have eq : (fun t => ¬Function.Injective (Program.pair a π t)) =
        fun t => ¬Function.Injective (labels (π ∘ a) t) := by
      funext t
      apply congrArg (fun u : Bool × J → Words => ¬Function.Injective u)
      funext ⟨b,j⟩; cases b <;> rfl
    have hh := fail_nat (π ∘ a) (π.injective.comp a.injective) jcap wordcard
    rw [← eq] at hh
    simpa only [Nat.card_eq_fintype_card] using hh
  · rw [split_mean e (fun w => Trace.indicator (¬small w.2)),pair_mean]
    apply ShakeXof.mean_le_const
    intro _
    exact rate _ _ (bucket_risk jcap zcap)

private theorem each (π : Permutation) (t : J → Words) (cert : valid a tag P)
    (bounded : ∀ H f x, W H f x ≤ 1) :
    let z := Program.resample a (π,t)
    actual e a P W z.1 ≤ ideal e a base tag P W π (splitWorld e t) + error P z.1 z.2 + bad e a π t := by
  dsimp only
  by_cases ok : Function.Injective (Program.pair a π t)
  · by_cases sm : small (splitWorld e t).2
    · have eq : target e (splitWorld e t).2 (splitWorld e t).1 = t := funext fun j => e.symm_apply_apply (t j)
      have good : Function.Injective (Program.pair a π (target e (splitWorld e t).2 (splitWorld e t).1)) := by rwa [eq]
      have law := local_law e a base π t ok sm
      have h := coupled e a π (splitWorld e t).2 tag (splitWorld e t).1 good P cert
        (W (oracle (Program.resample a (π,t)).1) (exactTable e a (Program.resample a (π,t)).1)) (bounded _ _)
      rw [eq] at h
      unfold actual ideal error bad
      simp only [Trace.indicator,not_not.mpr ok,not_not.mpr sm,ite_false,add_zero,zero_add]
      rw [law.1,law.2] at h ⊢
      simpa only [add_assoc] using h
    · have low : actual e a P W (Program.resample a (π,t)).1 ≤ 1 := run_le (fun _ : T => (Program.resample a (π,t)).1) _ (bounded (oracle (Program.resample a (π,t)).1) (exactTable e a (Program.resample a (π,t)).1)) P
      unfold bad
      simp only [Trace.indicator,ite_eq_left sm]
      exact low.trans (le_add_self.trans le_add_self)
  · have low : actual e a P W (Program.resample a (π,t)).1 ≤ 1 := run_le (fun _ : T => (Program.resample a (π,t)).1) _ (bounded (oracle (Program.resample a (π,t)).1) (exactTable e a (Program.resample a (π,t)).1)) P
    unfold bad
    simp only [Trace.indicator,ite_eq_left ok]
    exact low.trans (le_self_add.trans le_add_self)

theorem phase_transfer (jcap : Fintype.card J ≤ 2^768) (zcap : 2^1344 ≤ Fintype.card Z)
    (cert : valid a tag P) (bounded : ∀ H f x, W H f x ≤ 1) (Q : ℕ)
    (count : CountBound (fun i => i.isRight = true) (simulateQ erase P) Q) :
    uniformMean (actual e a P W) ≤
      uniformMean (fun π => uniformMean (fun f : J → Y => uniformMean (fun s : J → Z => ideal e a base tag P W π (f,s)))) +
      (Q * forestPenalty Rate Words Q + Q*((Fintype.card J:ℝ≥0∞)/Fintype.card Words)) +
      (((2:ℝ≥0∞)^63)⁻¹ + ((2:ℝ≥0∞)^384)⁻¹) := by
  let actual' (π : Permutation) (_ : J → Words) := actual e a P W π
  have sw := switch a actual'
  simp only [actual',const_mean] at sw
  apply sw.le.trans
  have aux := avg_mono (fun π => avg_mono (fun t => each e a base tag P W π t cert bounded))
  apply aux.trans
  simp only [avg_add]
  rw [← switch a (error P)]
  apply add_le_add _ (ShakeXof.mean_le_const (fun π => bad_mean e a π jcap zcap))
  apply add_le_add
  · apply le_of_eq; apply congrArg uniformMean; funext π
    rw [split_mean,pair_mean]
  · change uniformMean (fun π => uniformMean (fun t => risk π Trace.zeroCap P + risk π (Trace.fake t) P)) ≤ _
    simp only [avg_add,const_mean]
    exact add_le_add (Trace.root_risk _ Q count) (ShakeXof.mean_le_const (fun π => Trace.fake_risk π _ Q count))

end
end Reduction.ShakePermutation.SparsePort.Phase
#print axioms Reduction.ShakePermutation.SparsePort.Phase.phase_transfer
