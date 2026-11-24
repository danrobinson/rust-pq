import Integration.SlhDsaShakePermutationProgram
import Integration.SlhDsaShakeXofTcr
import PQ.QROM.ExactPrfTight

namespace Reduction.ShakePermutation.Program
open Classical Quantum PQ.Interactive PQ.QROM ENNReal
open scoped Kronecker ComplexOrder
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option allowUnsafeReducibility true in
attribute [local irreducible] changed oracle owner
variable {I J E : Type} [Fintype I] [Nonempty I] [DecidableEq I] [Fintype E] [DecidableEq E]

theorem bounded_overlap_game {X Y : Type} [Nonempty X] [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
    (base : X → Y) (g : I → X → Y) (keys : X → Finset I) (d : ℕ) (bound : ∀ p, (keys p).card ≤ d) (keep : ∀ i p, i ∉ keys p → g i p = base p)
    (M : (X → Y) → Closed (WS X Y E) Bool) (q : ℕ)
    (hq : PUE (spec:=unifSpec) cnt0 M q) (ρ : SubState ((X × Y) × E)) :
    let w := fun H => qWeight (· = true) (M H) (ρ.matrix ⊗ₖ (SubState.basis ()).matrix)
    SetOracle.uniformMean (fun i => w (g i)) ≤ w base + ENNReal.ofReal (8*(q:ℝ)^2*((d:ℝ)/Fintype.card I)) := by
  classical
  dsimp only
  obtain ⟨x,hx,eval⟩ := hq.exists_prog_qprob
  let event := fun p : (Σ _ : QReg, Bool) => p.2 = true
  let acc := fun H : X → Y => qprob LocalSig.Interp.instruments H x ρ event
  have eq (H : X → Y) : acc H = _ := eval (· = true) H ρ
  simp_rw [← eq]
  have le1 (H : X → Y) : acc H ≤ 1 :=
    (HybridModel.ofProgram LocalSig.Interp.instruments x ρ q hx event).prob_le_one _ id
  refine le_add_ofReal_of_abs_toReal (ShakeXof.mean_le_const fun _ => le1 _) (le1 _) ?_
  let marks (i : I) := Finset.univ.filter fun p => i ∈ keys p
  let u := (Fintype.card I : ℝ)⁻¹
  have hidden (p : X) : ∑ i ∈ Finset.univ.filter (fun i => p ∈ marks i), u ≤ (d:ℝ)/Fintype.card I := by
    have hf : Finset.univ.filter (fun i => p ∈ marks i) = keys p := by ext i; simp [marks]
    rw [hf,Finset.sum_const,nsmul_eq_mul,div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (bound p)) (by positivity)
  have supp (i : I) (p : X) (ne : g i p ≠ base p) : p ∈ marks i := by
    simp only [marks,Finset.mem_filter,Finset.mem_univ,true_and]
    by_contra h
    exact ne (keep i p h)
  have main := Purify.qprob_tight_avg LocalSig.Interp.instruments x ρ q hx event
    (fun _ : I => u) (fun _ => inv_nonneg.mpr (Nat.cast_nonneg _))
    g base marks supp ((d:ℝ)/Fintype.card I) (by positivity) hidden
  have total : ∑ _i : I, u = 1 := by simp [u,Fintype.card_ne_zero]
  rw [total,one_mul] at main
  rw [SetOracle.uniformMean,ENNReal.toReal_sum (fun i _ => mul_ne_top (by simp [unifW]) (ne_top_of_le_ne_top one_ne_top (le1 _)))]
  simpa only [acc,ENNReal.toReal_mul,unifW,ENNReal.toReal_inv,ENNReal.toReal_natCast,u,div_eq_mul_inv] using main

theorem fiber_game {X Y : Type} [Nonempty X] [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
    (base : X → Y) (g : I → X → Y) (tag : X → Option I) (keep : ∀ i p, tag p ≠ some i → g i p = base p)
    (M : (X → Y) → Closed (WS X Y E) Bool) (q : ℕ)
    (hq : PUE (spec:=unifSpec) cnt0 M q) (ρ : SubState ((X × Y) × E)) :
    let w := fun H => qWeight (· = true) (M H) (ρ.matrix ⊗ₖ (SubState.basis ()).matrix)
    SetOracle.uniformMean (fun i => w (g i)) ≤ w base + ENNReal.ofReal (8*(q:ℝ)^2/Fintype.card I) := by
  classical
  let keys (p : X) := (tag p).toFinset
  have bound (p) : (keys p).card ≤ 1 := by cases h : tag p <;> simp [keys,h]
  have same (i) (p) (h : i ∉ keys p) : g i p = base p := by
    apply keep i p
    intro eq
    exact h (by simp [keys,eq])
  simpa only [Nat.cast_one,one_div,div_eq_mul_inv,one_mul] using
    bounded_overlap_game base g keys 1 bound same M q hq ρ

/-- The classical challenge answers may be fixed before applying this
comparison. Only the hidden column varies inside the uniform mean. -/
theorem column_game (π : Permutation) (f : (I × Bool × J) ↪ Words)
    (M : (Port → Words) → Closed (WS Port Words E) Bool) (q : ℕ)
    (hq : PUE (spec:=unifSpec) cnt0 M q) (ρ : SubState ((Port × Words) × E)) :
    let w := fun p => qWeight (· = true) (M (oracle p)) (ρ.matrix ⊗ₖ (SubState.basis ()).matrix)
    SetOracle.uniformMean (fun i => w (changed π f i)) ≤ w π + ENNReal.ofReal (8*(q:ℝ)^2/Fintype.card I) :=
  fiber_game (oracle π) (fun i => oracle (changed π f i))
    (fun p => owner f (if p.1 then p.2 else π p.2)) (agree π f) M q hq ρ

end Reduction.ShakePermutation.Program
#print axioms Reduction.ShakePermutation.Program.column_game
