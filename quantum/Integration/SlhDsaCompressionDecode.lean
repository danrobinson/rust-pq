import Integration.SlhDsaCompressionDatabaseAdaptive

namespace Reduction.Compression.Recording.Database
set_option linter.unusedSectionVars false
open Finset

variable {X Y V : Type} [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y] [DecidableEq Y]
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Scalar entries of the involution swapping the empty basis vector with
the uniform superposition over the full output alphabet. -/
noncomputable def entry : Option Y → Option Y → ℝ
  | none, none => 0
  | none, some _ | some _, none => coeff Y
  | some y, some z => (if y = z then 1 else 0) - coeff Y ^ 2

theorem swap_entries (ψ : Option Y → V) (u : Option Y) :
    swap ψ u = ∑ v : Option Y, entry u v • ψ v := by
  classical
  cases u with
  | none => simp only [Fintype.sum_option, swap, mean, entry, zero_smul, zero_add, Finset.smul_sum]
  | some y =>
    simp only [Fintype.sum_option, swap, mean, entry, sub_smul, ite_smul, one_smul, zero_smul,
      Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true, ← Finset.smul_sum, smul_sub, smul_smul]
    rw [sq]
    abel

noncomputable def coeffDB (d e : DB X Y) : ℝ := ∏ j, entry (d j) (e j)

/-- Simultaneously change every database cell to the ordinary table basis. -/
noncomputable def decode (ψ : Wave X Y V) : Wave X Y V :=
  fun x d => ∑ e, coeffDB d e • ψ x e

private theorem split_sum {W : Type} [AddCommMonoid W] (x : X) (f : DB X Y → W) :
    ∑ d, f d = ∑ r : Rest x Y, ∑ u : Option Y, f (assemble x r u) := by
  classical
  let e := Equiv.funSplitAt x (Option Y)
  calc ∑ d, f d = ∑ z : Option Y × Rest x Y, f (e.symm z) := (Equiv.sum_comp e.symm f).symm
       _ = _ := by rw [Fintype.sum_prod_type, Finset.sum_comm]; rfl

private theorem factor (d : DB X Y) (x : X) (r : Rest x Y) (u : Option Y) :
    coeffDB d (assemble x r u) = (∏ j : {j : X // j ≠ x}, entry (d j.val) (r j)) * entry (d x) u := by
  unfold coeffDB
  rw [Fintype.prod_eq_mul_prod_compl x]
  simp only [assemble_at]
  apply mul_comm _ _ |>.trans
  congr 1
  rw [Finset.prod_subtype ({x}ᶜ : Finset X) (p := fun z => z ≠ x) (fun z => by simp)]
  apply Finset.prod_congr rfl
  intro j _
  rw [assemble_other _ _ _ j.property]

private theorem decode_fibre (ψ : Wave X Y V) (x : X) (d : DB X Y) :
    decode ψ x d = ∑ r : Rest x Y, (∏ j : {j : X // j ≠ x}, entry (d j.val) (r j)) •
      swap (fun u => ψ x (assemble x r u)) (d x) := by
  unfold decode
  rw [split_sum x]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [swap_entries, Finset.smul_sum]
  exact Finset.sum_congr rfl fun u _ => by rw [factor, smul_smul]

/-- On each decoded table sector a recording query is exactly the controlled
operation for the entry at the selected address. -/
theorem decode_call (O : X → Option Y → V ≃ₗᵢ[ℝ] V) (ψ : Wave X Y V) (x : X) (d : DB X Y) :
    decode (call O ψ) x d = O x (d x) (decode ψ x d) := by
  rw [decode_fibre,decode_fibre ψ,map_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [map_smul]
  congr 1
  simp only [call_at,query,swap_involutive]

theorem decode_empty (η : X → V) (x : X) (d : DB X Y) :
    decode (emptyStart η) x d = coeffDB d (fun _ => none) • η x := by
  classical
  simp [decode, emptyStart, smul_ite]

theorem decode_total (η : X → V) (x : X) (H : X → Y) :
    decode (emptyStart η) x (fun j => some (H j)) = coeff Y ^ Fintype.card X • η x := by
  rw [decode_empty]
  simp [coeffDB,entry]

theorem decode_partial (η : X → V) (x : X) (d : DB X Y) (hd : ∃ j, d j = none) :
    decode (emptyStart η) x d = 0 := by
  obtain ⟨j,hj⟩ := hd
  rw [decode_empty]
  have h : coeffDB d (fun _ => none) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj,entry])
  rw [h,zero_smul]

/-- The squared amplitude weight of each total table is exactly its uniform
sampling probability. -/
theorem total_weight : (coeff Y ^ Fintype.card X)^2 = (Fintype.card (X → Y) : ℝ)⁻¹ := by
  rw [← pow_mul, Nat.mul_comm, pow_mul, coeff, inv_pow, Real.sq_sqrt (Nat.cast_nonneg _),
    inv_pow, Fintype.card_fun, Nat.cast_pow]

open Adaptive
variable {I J : Type} [Fintype I] [Fintype J]
theorem decode_instrument (K : I → Instrument X V J) (ψ : I → Wave X Y V) (ij : I × J)
    (x : X) (d : DB X Y) :
    decode (branch K ψ ij) x d = branch K (fun i => decode (ψ i)) ij x d := by
  unfold branch decode
  let a := fun e : DB X Y => WithLp.toLp 2 (fun j => ψ ij.1 j e)
  have vect : (WithLp.toLp 2 (fun j => ∑ e, coeffDB d e • ψ ij.1 j e) : Work X V) =
      ∑ e, coeffDB d e • a e := by
    ext j
    simp [a, WithLp.ofLp_sum]
  rw [vect,map_sum]
  simp [a, WithLp.ofLp_sum]

abbrev Worlds (X Y V : Type) [Fintype X] := (X → Y) → Work X V

noncomputable def ordinaryStep (K : I → Instrument X V J) (O : I × J → X → Option Y → V ≃ₗᵢ[ℝ] V)
    (Φ : I → Worlds X Y V) (ij : I × J) (H : X → Y) : Work X V :=
  WithLp.toLp 2 (fun x => O ij x (some (H x)) ((K ij.1).kraus ij.2 (Φ ij.1 H) x))

/-- Identical classical histories and controls in a recording execution and the
ordinary execution run separately on each fixed function. -/
inductive Paired (η : X → V) : (t : ℕ) → {I : Type} → [Fintype I] →
    (I → Wave X Y V) → (I → Worlds X Y V) → Prop
  | start : Paired η 0 (fun _ : Unit => emptyStart η) (fun _ _ => WithLp.toLp 2 η)
  | next {t : ℕ} {I J : Type} [Fintype I] [Fintype J] {ψ : I → Wave X Y V} {Φ : I → Worlds X Y V}
      (prior : Paired η t ψ Φ) (K : I → Instrument X V J) (O : I × J → X → Option Y → V ≃ₗᵢ[ℝ] V) :
      Paired η (t+1) (step K O ψ) (ordinaryStep K O Φ)

theorem Paired.recorded {η : X → V} {q : ℕ} {ψ : I → Wave X Y V} {Φ : I → Worlds X Y V}
    (run : Paired η q ψ Φ) : Execution η q ψ := by
  induction run with
  | start => exact .start
  | next _ K O ih => exact .next ih K O

theorem Paired.total {η : X → V} {q : ℕ} {ψ : I → Wave X Y V} {Φ : I → Worlds X Y V}
    (run : Paired η q ψ Φ) (i : I) (H : X → Y) (x : X) :
    decode (ψ i) x (fun j => some (H j)) = coeff Y ^ Fintype.card X • (Φ i H x) := by
  induction run generalizing x with
  | start => exact decode_total _ _ _
  | @next t I J fi fj ψ Φ prior K O ih =>
    rw [step,decode_call,decode_instrument]
    unfold branch ordinaryStep
    have he : (WithLp.toLp 2 (fun j => decode (ψ i.1) j (fun z => some (H z))) : Work X V) =
        coeff Y ^ Fintype.card X • Φ i.1 H := by
      ext j
      exact ih i.1 j
    rw [he,map_smul]
    exact (O i x (some (H x))).map_smul _ _

theorem Paired.partial_zero {η : X → V} {q : ℕ} {ψ : I → Wave X Y V} {Φ : I → Worlds X Y V}
    (run : Paired η q ψ Φ) (i : I) (d : DB X Y) (hd : ∃ j, d j = none) (x : X) :
    decode (ψ i) x d = 0 := by
  induction run generalizing x with
  | start => exact decode_partial _ _ _ hd
  | @next t I J fi fj ψ Φ prior K O ih =>
    rw [step,decode_call,decode_instrument]
    unfold branch
    have z : (WithLp.toLp 2 (fun j => decode (ψ i.1) j d) : Work X V) = 0 := by
      ext j
      exact ih i.1 j
    simp [z]

/-- Exact average over the classical random function, for any leaf predicate
that can depend on both the final history and the function. -/
theorem Paired.event_mass {η : X → V} {q : ℕ} {ψ : I → Wave X Y V} {Φ : I → Worlds X Y V}
    (run : Paired η q ψ Φ) (ev : I → (X → Y) → Prop) [∀ i, DecidablePred (ev i)] :
    (∑ i, ∑ H : X → Y, if ev i H then ∑ x, ‖decode (ψ i) x (fun j => some (H j))‖^2 else 0) =
      (Fintype.card (X → Y) : ℝ)⁻¹ *
        ∑ i, ∑ H : X → Y, if ev i H then ‖Φ i H‖^2 else 0 := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun H _ => ?_
  by_cases h : ev i H
  · simp only [h,ite_true,run.total, norm_smul,mul_pow, Real.norm_eq_abs,
      sq_abs,total_weight,PiLp.norm_sq_eq_of_L2,Finset.mul_sum]
  · simp [h]

end Reduction.Compression.Recording.Database
#print axioms Reduction.Compression.Recording.Database.decode_call
#print axioms Reduction.Compression.Recording.Database.total_weight
#print axioms Reduction.Compression.Recording.Database.decode_instrument
#print axioms Reduction.Compression.Recording.Database.Paired.event_mass
