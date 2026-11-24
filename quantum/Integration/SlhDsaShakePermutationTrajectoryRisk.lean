import Integration.SlhDsaShakePermutationMsgFormat

/-! Conditional chance of revisiting the starting state during a keyed
sponge suffix. Prior permutation edges can be retained between trials. -/
namespace Reduction.ShakePermutation.MsgTrajectory.Risk
open Classical SetOracle ENNReal OracleComp OracleComp.PermutationConditioning Classic
noncomputable section
variable {A U : Type} [Fintype A] [DecidableEq A] [Fintype U]

def penalty (A : Type) [Fintype A] (Q : ℕ) : ℝ≥0∞ :=
  (Q+2 : ℕ) / ((Fintype.card A-Q : ℕ) : ℝ≥0∞)

theorem rare (read : U ↪ A) (ban : Finset A) (f : U → ℝ≥0∞) (b h : ℝ≥0∞)
    (ok : ∀ u, read u ∉ ban → f u ≤ h) (worst : ∀ u, f u ≤ b) :
    uniformMean f ≤ h + (ban.card : ℝ≥0∞)/Fintype.card U*b := by
  classical
  let bad := Finset.univ.filter fun u => read u ∈ ban
  have per (u) : f u ≤ h + if u ∈ bad then b else 0 := by
    by_cases v : read u ∈ ban
    · simpa only [bad,Finset.mem_filter,Finset.mem_univ,true_and,ite_eq_left v] using (worst u).trans (le_add_self : b ≤ h+b)
    · simpa [bad,v] using ok u v
  have cnt : bad.card ≤ ban.card := Finset.card_le_card_of_injOn read
    (fun u hu => (Finset.mem_filter.mp hu).2) read.injective.injOn
  have hb : uniformMean (fun u => if u ∈ bad then b else 0) =
      (bad.card : ℝ≥0∞)/Fintype.card U*b := by
    simp [uniformMean,unifW,mul_ite,Finset.sum_ite_mem,div_eq_mul_inv,nsmul_eq_mul,mul_assoc]
  have lhs := Finset.sum_le_sum (s:=Finset.univ) fun u _ => mul_le_mul' (le_rfl : unifW U u ≤ _) (per u)
  apply lhs.trans
  simp only [mul_add,Finset.sum_add_distrib]
  apply add_le_add
  · change uniformMean (fun _ : U => h) ≤ h
    by_cases ex : Nonempty U
    · let _ := ex; simp only [uniformMean,← Finset.sum_mul,sum_unifW,one_mul,le_rfl]
    · let _ := not_nonempty_iff.mp ex; simp [uniformMean]
  · change uniformMean _ ≤ _
    rw [hb]
    gcongr

private def inputs (t : EdgeTrace A) := (t.map Prod.fst).toFinset

private theorem fresh_input (t : EdgeTrace A) (v : A) (hv : v ∉ inputs t) :
    ∀ z ∈ t, v ≠ z.1 := by
  rintro z hz rfl
  exact hv (List.mem_toFinset.mpr (List.mem_map.mpr ⟨z,hz,rfl⟩))

/-- Test a nonempty sequence of permutation calls, with reversible fixed
absorptions between successive calls, for a return to an initial word. -/
def returns (π : Equiv.Perm A) (root x : A) : List (Equiv.Perm A) → Bool
  | [] => decide (π x = root)
  | b::bs => decide (π x = root) || returns π root (b (π x)) bs

theorem ratio {T Q : ℕ} (len : T ≤ Q+2) (space : Fintype.card A-Q ≤ Fintype.card U) :
    (T : ℝ≥0∞)/Fintype.card U ≤ penalty A Q := by
  unfold penalty
  apply ENNReal.div_le_div <;> exact_mod_cast ‹_›

private def tailHit (π : Equiv.Perm A) (s y : A) : List (Equiv.Perm A) → Bool
  | [] => decide (y = s)
  | b::bs => decide (y = s) || returns π s (b y) bs

private theorem returns_step (π : Equiv.Perm A) (s x : A) (bs : List (Equiv.Perm A)) :
    returns π s x bs = tailHit π s (π x) bs := by cases bs <;> rfl

private theorem inputs_card (t : EdgeTrace A) : (inputs t).card ≤ t.length := by
  simpa only [inputs,List.length_map] using List.toFinset_card_le (t.map Prod.fst)

def boundedAt (W : Equiv.Perm A → ℝ≥0∞) (Q : ℕ) (b : ℝ≥0∞) :=
  ∀ t : EdgeTrace A, t.length ≤ Q → Nonempty (Extensions t) → uniformMean (fun π : Extensions t => W π.val) ≤ b

/-- Conditional bound for a path starting at a fresh input. The factor W
may encode subsequent trials under the same permutation. -/
theorem fresh_path (W : Equiv.Perm A → ℝ≥0∞) (Q : ℕ) (b : ℝ≥0∞) (hW : boundedAt W Q b)
    (root : A) (bs : List (Equiv.Perm A)) (t : EdgeTrace A) (x : UnusedInputs t)
    (ok : Nonempty (Extensions t)) (room : t.length+bs.length+1 ≤ Q) :
    uniformMean (fun π : Extensions t => if returns π.val root x.val bs then W π.val else 0) ≤
      ((bs.length+1 : ℕ) : ℝ≥0∞) * (penalty A Q*b) := by
  classical
  induction bs generalizing t with
  | nil =>
    simp_rw [returns_step]
    rw [fresh_forward t x ok (fun y π => if tailHit π root y [] then W π else 0)]
    let f := fun y : UnusedOutputs t => uniformMean (fun π : Extensions ((x.val,y.val)::t) =>
      if tailHit π.val root y.val [] then W π.val else 0)
    have bound (y : UnusedOutputs t) : f y ≤ b := by
      exact (Finset.sum_le_sum (fun π _ => mul_le_mul' le_rfl (show (if tailHit π.val root y.val [] then W π.val else 0) ≤ W π.val by split <;> simp))).trans
        (hW _ (by simpa using room) (extensions_cons_nonempty t x y ok))
    have r := rare (Function.Embedding.subtype _) {root} f b 0
      (fun y hy => by simpa [f,tailHit,show y.val ≠ root by simpa using hy,uniformMean]) bound
    have R := ratio (A:=A) (U:=UnusedOutputs t) (T:=1) (Q:=Q) (by omega) (by have := unused_card t; omega)
    exact (by simpa only [zero_add,Finset.card_singleton] using r :
      uniformMean f ≤ (1:ℕ)/ (Fintype.card (UnusedOutputs t) : ℝ≥0∞)*b).trans
      (by simpa using mul_le_mul' R (le_refl b))
  | cons g bs ih =>
    let ban := insert root ((insert x.val (inputs t)).image g.symm)
    simp_rw [returns_step _ root x.val (g::bs)]
    rw [fresh_forward t x ok (fun y π => if tailHit π root y (g::bs) then W π else 0)]
    let f := fun y : UnusedOutputs t => uniformMean (fun π : Extensions ((x.val,y.val)::t) =>
      if tailHit π.val root y.val (g::bs) then W π.val else 0)
    have room' (y : UnusedOutputs t) : ((x.val,y.val)::t).length+bs.length+1 ≤ Q := by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using room
    have bound (y : UnusedOutputs t) : f y ≤ b := by
      exact (Finset.sum_le_sum (fun π _ => mul_le_mul' le_rfl (show (if tailHit π.val root y.val (g::bs) then W π.val else 0) ≤ W π.val by split <;> simp))).trans
        (hW _ (by have := room' y; omega) (extensions_cons_nonempty t x y ok))
    have safe (y : UnusedOutputs t) (out : y.val ∉ ban) : f y ≤ (bs.length+1 : ℕ)*(penalty A Q*b) := by
      have ne : y.val ≠ root := fun e => out (Finset.mem_insert.mpr (Or.inl e))
      have clean : g y.val ∉ inputs ((x.val,y.val)::t) := by
        intro h
        apply out
        apply Finset.mem_insert.mpr ∘ Or.inr
        exact Finset.mem_image.mpr ⟨g y.val,by simpa [inputs] using h,g.symm_apply_apply _⟩
      simpa only [f,tailHit,decide_eq_false ne,Bool.false_or] using
        ih _ ⟨g y.val,fresh_input _ _ clean⟩ (extensions_cons_nonempty t x y ok) (room' y)
    have r := rare (Function.Embedding.subtype _) ban f b _ safe bound
    have size : ban.card ≤ Q+2 := by
      have a := Finset.card_insert_le root ((insert x.val (inputs t)).image g.symm)
      have c := Finset.card_image_le (f:=g.symm) (s:=insert x.val (inputs t))
      have d := Finset.card_insert_le x.val (inputs t)
      have e := inputs_card t
      dsimp only [ban]; omega
    have R := ratio (A:=A) (U:=UnusedOutputs t) size (by have := unused_card t; omega)
    apply r.trans ((add_le_add le_rfl (mul_le_mul' R (le_refl b))).trans ?_)
    simp only [List.length_cons,Nat.cast_add,Nat.cast_one,add_mul,one_mul,le_rfl]

private theorem swap_avg {B C : Type} [Fintype B] [Fintype C] (f : B → C → ℝ≥0∞) :
    uniformMean (fun x => uniformMean (f x)) = uniformMean (fun y => uniformMean (fun x => f x y)) := by
  simp only [uniformMean,Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => mul_left_comm ..

def mass (π : Equiv.Perm A) (g : Equiv.Perm A) (bs : List (Equiv.Perm A)) :=
  uniformMean (fun s : A => if returns π s (g s) bs then (1:ℝ≥0∞) else 0)

/-- Multiply the conditional expectation of a later test by the cost of
one return event. This preserves the multiplicative gain over many trials. -/
theorem one_trial (W : Equiv.Perm A → ℝ≥0∞) (Q : ℕ) (b : ℝ≥0∞) (hW : boundedAt W Q b)
    (g : Equiv.Perm A) (bs : List (Equiv.Perm A)) (t : EdgeTrace A)
    (ok : Nonempty (Extensions t)) (room : t.length+bs.length+1 ≤ Q) :
    uniformMean (fun π : Extensions t => mass π.val g bs * W π.val) ≤
      ((bs.length+2 : ℕ) : ℝ≥0∞) * penalty A Q*b := by
  classical
  let f (s : A) := uniformMean (fun π : Extensions t => if returns π.val s (g s) bs then W π.val else 0)
  have distrib (π : Equiv.Perm A) : mass π g bs*W π = uniformMean (fun s : A => if returns π s (g s) bs then W π else 0) := by
    simp only [mass,uniformMean,Finset.sum_mul]
    apply Finset.sum_congr rfl; intro s _
    cases v : returns π s (g s) bs <;> simp
  simp_rw [distrib]
  rw [swap_avg]
  change uniformMean f ≤ _
  have safe (s : A) (miss : g s ∉ inputs t) : f s ≤ ((bs.length+1:ℕ):ℝ≥0∞)*(penalty A Q*b) :=
    fresh_path W Q b hW s bs t ⟨g s,fresh_input _ _ miss⟩ ok room
  have worst (s : A) : f s ≤ b :=
    (Finset.sum_le_sum (fun π _ => mul_le_mul' le_rfl (show (if returns π.val s (g s) bs then W π.val else 0) ≤ W π.val by split <;> simp))).trans
      (hW _ (by omega) ok)
  have r := rare g.toEmbedding (inputs t) f b _ safe worst
  have R := ratio (A:=A) (U:=A) ((inputs_card t).trans (show t.length ≤ Q+2 by omega)) (Nat.sub_le _ _)
  apply r.trans ((add_le_add le_rfl (mul_le_mul' R (le_refl b))).trans ?_)
  rw [show bs.length+2=(bs.length+1)+1 by omega]
  simp only [Nat.cast_add,Nat.cast_one,add_mul,one_mul,mul_assoc,le_rfl]

theorem penalty_mono {q Q : ℕ} (room : q ≤ Q) : penalty A q ≤ penalty A Q := by
  apply ENNReal.div_le_div <;> exact_mod_cast (by omega : _)

theorem moments (g : Equiv.Perm A) (bs : List (Equiv.Perm A)) (Q n : ℕ)
    (room : n*(bs.length+1) ≤ Q) :
    boundedAt (fun π => (mass π g bs)^n) (Q-n*(bs.length+1))
      ((((bs.length+2 : ℕ) : ℝ≥0∞)*penalty A Q)^n) := by
  classical
  induction n with
  | zero =>
    intro t _ ex
    let _ := ex
    simp only [pow_zero,uniformMean,mul_one,sum_unifW,le_rfl]
  | succ n ih =>
    rw [Nat.succ_mul] at room ⊢
    have h := ih (by omega)
    intro t bound ok
    have hit := one_trial _ _ _ h g bs t ok (by omega)
    simp_rw [pow_succ'] 
    apply hit.trans
    exact mul_le_mul' (mul_le_mul' le_rfl (penalty_mono (Nat.sub_le _ _))) le_rfl

end
end Reduction.ShakePermutation.MsgTrajectory.Risk
#print axioms Reduction.ShakePermutation.MsgTrajectory.Risk.fresh_path
#print axioms Reduction.ShakePermutation.MsgTrajectory.Risk.moments
