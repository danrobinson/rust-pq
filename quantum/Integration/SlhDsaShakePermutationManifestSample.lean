import Integration.SlhDsaShakePermutationManifestOrdinary
import Integration.SlhDsaShakePermutationManifestGame
import Integration.SlhDsaShakePermutationClassicalForest

/-! Uniform conditional sampler for the whole ordinary permutation on a
fixed tree of ordinary sponge inputs. -/
namespace Reduction.ShakePermutation.Manifest.Ordinary
open Classical SetOracle ENNReal Fix
set_option maxRecDepth 8192
noncomputable section
variable {I : Type} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
private theorem card_eq (t : Tree I) (w : Assignment I) :
    Fintype.card (I ↪ Words) * Fintype.card (Extension t w) = Fintype.card Permutation := by
  rw [← Nat.card_eq_fintype_card,← Nat.card_eq_fintype_card,← Nat.card_eq_fintype_card]
  exact nat_embedding_fiber (inputs t w.2 w.1) (outputs w.2 w.1)

theorem bad_count (t : Tree I) (ncap : Nat.card I ≤ 2^512) :
    2^512 * Nat.card {π : Permutation // ¬ Good t π} ≤ (Nat.card I)^2 * Nat.card Permutation := by
  classical
  apply count_to_risk (Good t) ncap
  simp only [Nat.card_eq_fintype_card]
  rw [← Fintype.card_congr (enumeration t),Fintype.card_sigma,Finset.mul_sum]
  simp only [card_eq,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.cast_id]
  rw [Fintype.card_prod]
  change _ ≤ Fintype.card ((I → Rate) × Caps I) * _
  rw [Fintype.card_prod,Nat.mul_comm (Fintype.card (Caps I))]

private theorem sigma_mean {A : Type} [Fintype A] (B : A → Type) [∀ a, Fintype (B a)]
    (test : (a : A) → B a → ℝ≥0∞) (same : ∀ a b, Fintype.card (B a) = Fintype.card (B b)) :
    uniformMean (fun z : Σ a, B a => test z.1 z.2) = uniformMean (fun a => uniformMean (test a)) := by
  classical
  cases isEmpty_or_nonempty A with
  | inl none => simp [uniformMean]
  | inr some =>
    obtain ⟨a⟩ := some
    simp only [uniformMean,unifW,Fintype.sum_sigma,Fintype.card_sigma,same _ a,
      Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.cast_id,Nat.cast_mul,
      ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl (ENNReal.natCast_ne_top _)),
      Finset.mul_sum,mul_assoc]

private theorem prod_mean {A B : Type} [Fintype A] [Fintype B] (v : A × B → ℝ≥0∞) :
    uniformMean v = uniformMean (fun a => uniformMean (fun b => v (a,b))) := by
  simp only [uniformMean,Fintype.sum_prod_type,unifW,Fintype.card_prod,Nat.cast_mul,
    ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl (ENNReal.natCast_ne_top _)),
    Finset.mul_sum,mul_assoc]

/-- Each supplied output f is a full uniform rate. The simulator chooses
independent distinct nonzero capacities and a uniformly random permutation
extending the resulting prescribed edges. The test can query both directions
of that permutation coherently without restriction. -/
theorem conditional (t : Tree I) (W : Permutation → (I → Rate) → ℝ≥0∞) :
    uniformMean (fun π : {π : Permutation // Good t π} => W π.val (fun i => rateOf (ordinary π.val (t.paths i)))) =
      uniformMean (fun f : I → Rate => uniformMean (fun c : Caps I =>
        uniformMean (fun e : Extension t (f,c) => W e.val f))) := by
  classical
  let V (π : {π : Permutation // Good t π}) := W π.val (fun i => rateOf (ordinary π.val (t.paths i)))
  let test (a : Assignment I) (e : Extension t a) := W e.val a.1
  have eval (z : Σ w, Extension t w) : V (enumeration t z) = test z.1 z.2 := by
    apply congrArg (W _)
    funext i
    change rateOf (ordinary z.2.val (t.paths i)) = z.1.1 i
    rw [states]; apply rate_join
  have eq := Classic.mean_equiv (enumeration t) V
  simp only [eval] at eq
  rw [← eq,sigma_mean (Extension t) test]
  · exact prod_mean _
  · intro a b
    have h : 0 < Fintype.card (I ↪ Words) := Fintype.card_pos_iff.mpr ⟨inputs t a.2 a.1⟩
    apply Nat.eq_of_mul_eq_mul_left h
    rw [card_eq,card_eq]

/-- One-sided advantage for a fixed, ordinary XOR-sponge prefix tree against
any joint quantum test of both permutation directions and all node outputs. -/
theorem game (t : Tree I) (ncap : Nat.card I ≤ 2^512)
    (W : Permutation → (I → Rate) → ℝ≥0∞) (bounded : ∀ π f, W π f ≤ 1) :
    uniformMean (fun π : Permutation => W π (fun i => rateOf (ordinary π (t.paths i)))) ≤
      uniformMean (fun f : I → Rate => uniformMean (fun c : Caps I =>
        uniformMean (fun e : Extension t (f,c) => W e.val f))) + (Nat.card I : ℝ≥0∞)^2/2^512 := by
  classical
  have cap := bad_count t ncap
  simp only [Nat.card_eq_fintype_card] at cap
  have bound := Classic.mean_select (Good t)
    (fun π : Permutation => W π (fun i => rateOf (ordinary π (t.paths i)))) (fun _ => bounded _ _)
  rw [conditional] at bound
  rw [Nat.card_eq_fintype_card]
  exact bound.trans (add_le_add le_rfl (Manifest.fraction _ _ _ Fintype.card_pos cap))

/-- Specialize the fixed-tree comparison to the byte-level padded SHAKE
XOF for the selected parameter set. Every queried string must have a
designated leaf before the permutation is sampled. -/
theorem byte_game (S : MLink.Sha2Set) {A : Type} (bytes : A → List SLHDSA.Byte)
    (t : Tree I) (leaf : A → I) (fits : ∀ a, t.paths (leaf a) = messageBlocks (MLink.sp (bytes a)))
    (ncap : Nat.card I ≤ 2^512)
    (W : Permutation → (A → SLHDSA.Bytes S.vp.params.m) → ℝ≥0∞) (bounded : ∀ π g, W π g ≤ 1) :
    uniformMean (fun π : Permutation => W π (fun a => answer S (lanes π) (bytes a))) ≤
      uniformMean (fun f : I → Rate => uniformMean (fun c : Caps I => uniformMean
        (fun e : Extension t (f,c) => W e.val (fun a => ShakeXof.head (output_sizes S).2 (Completion.bytes (f (leaf a))))))) +
          (Nat.card I : ℝ≥0∞)^2/2^512 := by
  let F := fun (r : I → Rate) a => ShakeXof.head (output_sizes S).2 (Completion.bytes (r (leaf a)))
  have h := game t ncap (fun π r => W π (F r)) (fun _ _ => bounded _ _)
  simpa only [F,fits,answer_blocks] using h

end
end Reduction.ShakePermutation.Manifest.Ordinary
#print axioms Reduction.ShakePermutation.Manifest.Ordinary.conditional
#print axioms Reduction.ShakePermutation.Manifest.Ordinary.bad_count

#print axioms Reduction.ShakePermutation.Manifest.Ordinary.byte_game
