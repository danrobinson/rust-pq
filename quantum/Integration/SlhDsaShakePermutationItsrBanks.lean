import Integration.SlhDsaShakePermutationItsrHead
import Integration.SlhDsaShakePermutationClassicalForestBound

/-! One full-word recording cell suffices for either mask direction or
the rate shear. The unused word coordinates are uniform independent coins. -/
namespace Reduction.ShakePermutation.ItsrLabel
open Classical Tails MLink SLHDSA Quantum OracleSpec ENNReal SetOracle
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 1200000
set_option allowUnsafeReducibility true in
attribute [local irreducible] Graph.support SetOracle.uniformMean
abbrev Addr := (Bool × Rate) ⊕ Capacity
abbrev Bank := Database Addr Words

def slice {I X V W : Type} (idx : I → X) (read : W → V) (D : Database X W) (i : I) :=
  (D (idx i)).map read

def mask (b : Bool) (r : Rate) : Addr := .inl (b,r)
def tailHead (z : Capacity) : Addr := .inr z

def held (D : Bank) := slice tailHead rateOf D
def masks (D : Bank) (b : Bool) := slice (mask b) capOf D

def label (S : Sha2Set) (π : Permutation) (L : ℕ) (D : Bank) : Bool :=
  decide (Good S π L (masks D false) (masks D true) (held D))

theorem mask_inj (b : Bool) : Function.Injective (mask b) :=
  fun _ _ eq => congrArg Prod.snd (Sum.inl.inj eq)

theorem slice_size {I V X W : Type} [Fintype X] [Fintype I] [Fintype V] [DecidableEq I] [DecidableEq V]
    (idx : I → X) (inj : Function.Injective idx) (rd : W → V) (D : Database X W) :
    (Graph.support (slice idx rd D)).card ≤ D.size := by
  change (Graph.support (slice idx rd D)).card ≤ (Finset.univ.filter (fun j => (D j).isSome)).card
  apply Finset.card_le_card_of_injOn idx
  · intro i hi
    change i ∈ Graph.support (slice idx rd D) at hi
    have use := (Graph.mem_support (slice idx rd D) i).mp hi
    cases e : D (idx i) with
    | none => simp [slice,e] at use
    | some v =>
      change idx i ∈ Finset.univ.filter (fun j => (D j).isSome)
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _,by rw [e]; rfl⟩
  · exact fun _ _ _ _ eq => inj eq

theorem slice_other {I V : Type} (idx : I → Addr) (rd : Words → V) (D : Bank) (x : Addr) (v : Words)
    (away : ∀ i, idx i ≠ x) : slice idx rd (Function.update D x (some v)) = slice idx rd D := by
  funext i
  simp only [slice,Function.update_of_ne (away i)]

theorem slice_same {I V : Type} [DecidableEq I] (idx : I → Addr) (inj : Function.Injective idx)
    (rd : Words → V) (D : Bank) (i : I) (v : Words) :
    slice idx rd (Function.update D (idx i) (some v)) = Function.update (slice idx rd D) i (some (rd v)) := by
  funext j
  by_cases e : j = i
  · subst j; simp [slice]
  · simp only [slice,Function.update_of_ne e,Function.update_of_ne (inj.ne e)]

theorem slice_extends {I V : Type} (idx : I → Addr) (rd : Words → V) (D : Bank) (x : Addr) (v : Words)
    (empty : D x = none) : Graph.Extends (slice idx rd D) (slice idx rd (Function.update D x (some v))) := by
  intro i a ha
  have ne : idx i ≠ x := by rintro e; simp [slice,e,empty] at ha
  simpa only [slice,Function.update_of_ne ne] using ha

theorem stable_bad (S π L) (D : Bank) (x : Addr) (hx : D x = none) (v : Words) (b : label S π L D = false) :
    label S π L (Function.update D x (some v)) = false := by
  simp only [label,decide_eq_false_iff_not] at b ⊢
  intro g
  exact b (good_of_extension (slice_extends _ _ _ _ v hx) (slice_extends _ _ _ _ v hx)
    (slice_extends _ _ _ _ v hx) g)

theorem cap_mean (f : Capacity → ℝ≥0∞) : uniformMean (fun v : Words => f (capOf v)) = uniformMean f := by
  exact (Classic.mean_equiv Classic.wordSplit (fun z => f z.2)).trans
    ((Classic.avg_prod (fun z : Rate × Capacity => f z.2)).trans (Classic.avg_const (U := Rate) (uniformMean f)))

theorem rate_mean (f : Rate → ℝ≥0∞) : uniformMean (fun v : Words => f (rateOf v)) = uniformMean f := by
  exact (Classic.mean_equiv Classic.wordSplit (fun z => f z.1)).trans
    ((Classic.avg_prod (fun z : Rate × Capacity => f z.1)).trans (by simp only [Classic.avg_const]))

end
end Reduction.ShakePermutation.ItsrLabel
