import Integration.SlhDsaCompressionDecode

namespace Reduction.Compression.Recording.Database
set_option linter.unusedSectionVars false
open Finset
variable {X Y V : Type} [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y] [DecidableEq Y]
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V]

private theorem entry_symm (u v : Option Y) : entry u v = entry v u := by
  cases u <;> cases v <;> simp [entry,eq_comm]

private theorem entry_orth (e f : Option Y) :
    ∑ u : Option Y, entry u e * entry u f = if e = f then 1 else 0 := by
  let v := fun t : Option Y => if t = f then (1:ℝ) else 0
  have hv (u) : swap v u = entry u f := by
    simp [swap_entries,v,smul_eq_mul]
  have h := congrFun (swap_involutive v) e
  rw [swap_entries] at h
  simp only [hv,smul_eq_mul] at h
  simpa only [entry_symm e, v] using h

private theorem db_orth (e f : DB X Y) :
    ∑ d : DB X Y, coeffDB d e * coeffDB d f = if e = f then 1 else 0 := by
  classical
  simp only [coeffDB,← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (i : X) (u : Option Y) => entry u (e i) * entry u (f i))]
  simp only [entry_orth,Fintype.prod_boole, funext_iff]

noncomputable def tensor (v : DB X Y → V) (d : DB X Y) : V := ∑ e, coeffDB d e • v e

/-- Parseval on an arbitrary subset of database cells, represented by an
arbitrary finite address type (including the empty type). -/
theorem tensor_energy (v : DB X Y → V) :
    ∑ d, ‖tensor v d‖^2 = ∑ e, ‖v e‖^2 := by
  classical
  simp only [tensor,← real_inner_self_eq_norm_sq,sum_inner,inner_sum,real_inner_smul_left,real_inner_smul_right]
  calc _ = ∑ e : DB X Y, ∑ f : DB X Y, (∑ d : DB X Y, coeffDB d e * coeffDB d f) * inner ℝ (v e) (v f) := by
         simp only [Finset.sum_mul,mul_assoc]
         rw [Finset.sum_comm]
         apply Finset.sum_congr rfl
         intro e _
         rw [Finset.sum_comm]
         apply Finset.sum_congr rfl
         intro y _
         exact Finset.sum_congr rfl fun _ _ => by rw [real_inner_comm (v y) (v e)]
       _ = _ := by simp [db_orth,ite_mul]

def PairHit {T : Type} (p : Y → T) (a b : X) (d : DB X Y) : Prop :=
  ∃ u v, d a = some u ∧ d b = some v ∧ p u = p v

noncomputable def readCell (a : X) (v : DB X Y → V) (d : DB X Y) :=
  swap (fun u => v (assemble a (fun j => d j.val) u)) (d a)

private theorem split_sum {W : Type} [AddCommMonoid W] (a : X) (f : DB X Y → W) :
    ∑ d, f d = ∑ r : Rest a Y, ∑ u : Option Y, f (assemble a r u) := by
  classical
  let e := Equiv.funSplitAt a (Option Y)
  calc ∑ d, f d = ∑ z : Option Y × Rest a Y, f (e.symm z) := (Equiv.sum_comp e.symm f).symm
       _ = _ := by rw [Fintype.sum_prod_type, Finset.sum_comm]; rfl

theorem tensor_slice (v : DB X Y → V) (a : X) (r : Rest a Y) (u : Option Y) :
    tensor v (assemble a r u) = tensor (fun s => swap (fun w => v (assemble a s w)) u) r := by
  change decode (fun _ => v) a (assemble a r u) = _
  unfold decode tensor
  rw [split_sum a]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [swap_entries,Finset.smul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [smul_smul]
  congr 1
  unfold coeffDB
  rw [Fintype.prod_eq_mul_prod_compl a]
  simp only [assemble_at]
  rw [mul_comm (entry u w),Finset.prod_subtype ({a}ᶜ : Finset X) (p := fun z => z ≠ a) (fun z => by simp)]
  congr 1
  exact Finset.prod_congr rfl fun j _ => by rw [assemble_other _ _ _ j.property,assemble_other _ _ _ j.property]

theorem readCell_slice (a : X) (v : DB X Y → V) (r : Rest a Y) (u : Option Y) :
    readCell a v (assemble a r u) = swap (fun w => v (assemble a r w)) u := by
  unfold readCell
  rw [assemble_at]
  rw [show (fun j : {j : X // j ≠ a} => assemble a r u j.val) = r from
    funext fun j => assemble_other _ _ _ j.property]

private theorem readCell_other (v : DB X Y → V) (a b : X) (hb : b ≠ a) (r : Rest a Y) (u : Option Y) :
    readCell b v (assemble a r u) = readCell (⟨b,hb⟩ : {j : X // j ≠ a}) (fun s => v (assemble a s u)) r := by
  unfold readCell
  rw [assemble_other _ _ _ hb]
  congr 1
  funext w
  congr 1
  funext j
  by_cases ja : j = a
  · subst j
    rw [assemble_other _ _ _ hb.symm,assemble_at,assemble_at]
  by_cases jb : j = b
  · subst j
    rw [assemble_at,assemble_other _ _ _ hb,assemble_at]
  have hj : (⟨j,ja⟩ : {j : X // j ≠ a}) ≠ ⟨b,hb⟩ := fun h => jb (congrArg Subtype.val h)
  rw [assemble_other _ _ _ jb,assemble_other _ _ _ ja,assemble_other _ _ _ ja,assemble_other _ _ _ hj]

private theorem two_sum (a b : X) (h : b ≠ a) (f : DB X Y → ℝ) :
    ∑ d, f d = ∑ u : Option Y, ∑ w : Option Y, ∑ k : Rest (⟨b,h⟩ : {j : X // j ≠ a}) Y,
      f (assemble a (assemble (⟨b,h⟩ : {j : X // j ≠ a}) k w) u) := by
  rw [split_sum a,Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [split_sum (⟨b,h⟩ : {j : X // j ≠ a}),Finset.sum_comm]

open Classical in
/-- Rest-of-table decoding preserves an event determined entirely by these
two cells. Only two basis changes are needed for the measured comparison. -/
theorem pair_marginal {T : Type} (p : Y → T) (a b : X) (hab : a ≠ b) (v : DB X Y → V) :
    (∑ d : DB X Y, if PairHit p a b d then ‖tensor v d‖^2 else 0) =
      ∑ d : DB X Y, if PairHit p a b d then ‖readCell b (readCell a v) d‖^2 else 0 := by
  classical
  let z : {j : X // j ≠ a} := ⟨b,hab.symm⟩
  rw [two_sum a b hab.symm,two_sum a b hab.symm (fun d => if PairHit p a b d then ‖readCell b (readCell a v) d‖^2 else 0)]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun w _ => ?_
  have cond (k : Rest z Y) : PairHit p a b (assemble a (assemble z k w) u) ↔
      ∃ i j, u = some i ∧ w = some j ∧ p i = p j := by
    simp only [PairHit, assemble_at, assemble_other _ _ _ hab.symm]
    rw [show assemble z k w ⟨b,hab.symm⟩ = w from assemble_at z k w]
  dsimp only [z] at cond
  simp only [cond]
  by_cases hit : ∃ i j, u = some i ∧ w = some j ∧ p i = p j
  · simp only [hit,ite_true]
    simp only [tensor_slice, readCell_other _ a b hab.symm, readCell_slice]
    exact tensor_energy _
  · simp only [hit,ite_false,Finset.sum_const_zero]


noncomputable def sumWeight {A : Type} [Fintype A] (P : A → Prop) (v : A → V) : ℝ := by
  classical
  exact ∑ d, if P d then ‖v d‖^2 else 0

private theorem sw_nonneg {A : Type} [Fintype A] (P : A → Prop) (v : A → V) : 0 ≤ sumWeight P v := by
  classical
  exact Finset.sum_nonneg fun d _ => by split <;> first | exact sq_nonneg _ | exact le_rfl

private theorem sw_triangle {A : Type} [Fintype A] (P : A → Prop) (f g : A → V) :
    Real.sqrt (sumWeight P (fun d => f d + g d)) ≤ Real.sqrt (sumWeight P f) + Real.sqrt (sumWeight P g) := by
  classical
  let w := fun d => if P d then (1:ℝ) else 0
  have weight (v : A → V) : ∑ d, w d * ‖v d‖^2 = sumWeight P v := by simp [w,sumWeight,ite_mul]
  have h := PQ.QROM.Purify.sum_mul_add_sq_le w (fun d => ‖f d‖) (fun d => ‖g d‖)
    (fun d => by unfold w; split <;> norm_num) (Real.sqrt_nonneg (sumWeight P f)) (Real.sqrt_nonneg (sumWeight P g))
    (by rw [weight, Real.sq_sqrt (sw_nonneg P f)]) (by rw [weight, Real.sq_sqrt (sw_nonneg P g)])
  apply (Real.sqrt_le_left (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mpr
  rw [← weight]
  apply le_trans _ h
  exact Finset.sum_le_sum fun d _ => mul_le_mul_of_nonneg_left
    ((sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr (norm_add_le _ _))
    (by unfold w; split <;> norm_num)

theorem readCell_energy (a : X) (v : DB X Y → V) : ∑ d, ‖readCell a v d‖^2 = ∑ d, ‖v d‖^2 := by
  rw [split_sum a,split_sum a (fun d => ‖v d‖^2)]
  refine Finset.sum_congr rfl fun r _ => ?_
  simpa only [readCell_slice,Fintype.sum_option,energy] using swap_energy (fun w => v (assemble a r w))

private theorem diff_energy (f : Option Y → V) :
    ‖f none - mean f‖^2 ≤ 4 * energy f := by
  have h (g : Option Y → V) : ‖g none‖^2 ≤ energy g := le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have h₁ := h f
  have h₂ := h (swap f)
  rw [swap_energy] at h₂
  change ‖mean f‖^2 ≤ _ at h₂
  have h₃ := (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr (norm_sub_le (f none) (mean f))
  nlinarith [sq_nonneg (‖f none‖ - ‖mean f‖)]

variable {T : Type} [DecidableEq T]

private theorem one_fibre (p : Y → T) (N : ℝ) (hN : 0 < N)
    (uniform : ∀ B : Finset T, ((Finset.univ.filter fun y => p y ∈ B).card : ℝ) /
      Fintype.card Y ≤ (B.card : ℝ)/N)
    (a b : X) (hab : a ≠ b) (r : Rest a Y) (v : DB X Y → V) :
    sumWeight (fun w => PairHit p a b (assemble a r w))
      (fun w => readCell a v (assemble a r w) - v (assemble a r w)) ≤
        (4/N) * ∑ w : Option Y, ‖v (assemble a r w)‖^2 := by
  classical
  let f := fun w => v (assemble a r w)
  let z : {j : X // j ≠ a} := ⟨b,hab.symm⟩
  let B := ((r z).map p).toFinset
  have hit (w : Option Y) : PairHit p a b (assemble a r w) ↔ ∃ y, w = some y ∧ p y ∈ B := by
    unfold PairHit
    rw [assemble_at,assemble_other _ _ _ hab.symm]
    change (∃ u v, w = some u ∧ r z = some v ∧ p u = p v) ↔ _
    cases h : r z <;> simp [B,h,eq_comm]
  have value (y : Y) : readCell a v (assemble a r (some y)) - v (assemble a r (some y)) =
      coeff Y • (f none - mean f) := by rw [readCell_slice]; change f _ + _ - f _ = _; abel
  have hsum : sumWeight (fun w => PairHit p a b (assemble a r w))
      (fun w => readCell a v (assemble a r w) - v (assemble a r w)) =
      ((Finset.univ.filter fun y => p y ∈ B).card : ℝ) * ‖coeff Y • (f none - mean f)‖^2 := by
    unfold sumWeight
    rw [Fintype.sum_option]
    simp only [hit,reduceCtorEq,false_and,exists_false,ite_false,zero_add, Option.some.injEq,exists_eq_left',value]
    simp only [← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul]
  rw [hsum,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs,coeff,inv_pow,Real.sq_sqrt (Nat.cast_nonneg _)]
  have dens := uniform B
  have nc : B.card ≤ 1 := by cases h : r z <;> simp [B,h]
  have frac := dens.trans (div_le_div_of_nonneg_right (by exact_mod_cast nc : (B.card : ℝ) ≤ 1) hN.le)
  have h := mul_le_mul frac (diff_energy f) (sq_nonneg _) (by positivity)
  rw [div_eq_mul_inv] at h
  simp only [Fintype.sum_option]
  change _ ≤ _ * energy f
  convert h using 1 <;> ring

private theorem cell_amp (p : Y → T) (N : ℝ) (hN : 0 < N)
    (uniform : ∀ B : Finset T, ((Finset.univ.filter fun y => p y ∈ B).card : ℝ) /
      Fintype.card Y ≤ (B.card : ℝ)/N) (a b : X) (hab : a ≠ b) (v : DB X Y → V) :
    Real.sqrt (sumWeight (PairHit p a b) (readCell a v)) ≤
      Real.sqrt (sumWeight (PairHit p a b) v) + Real.sqrt (4/N) * Real.sqrt (∑ d, ‖v d‖^2) := by
  let err := fun d => readCell a v d - v d
  have h : sumWeight (PairHit p a b) err ≤ (4/N) * ∑ d, ‖v d‖^2 := by
    classical
    unfold sumWeight
    rw [split_sum a,split_sum a (fun d => ‖v d‖^2), Finset.mul_sum]
    exact Finset.sum_le_sum fun r _ => one_fibre p N hN uniform a b hab r v
  have sum_eq : readCell a v = fun d => v d + err d := by funext d; simp [err]
  rw [sum_eq]
  apply (sw_triangle ..).trans
  apply add_le_add le_rfl
  simpa only [Real.sqrt_mul (by positivity : 0 ≤ 4/N)] using Real.sqrt_le_sqrt h


private theorem pair_symm (p : Y → T) (a b : X) (d : DB X Y) :
    PairHit p a b d ↔ PairHit p b a d := by
  constructor <;> rintro ⟨u,v,hu,hv,e⟩ <;> exact ⟨v,u,hv,hu,e.symm⟩

private theorem sampled_le (p : Y → T) (a b : X) (v : DB X Y → V) :
    sumWeight (fun H : X → Y => p (H a) = p (H b)) (fun H => tensor v (fun j => some (H j))) ≤
      sumWeight (PairHit p a b) (tensor v) := by
  classical
  let incl : (X → Y) ↪ DB X Y := ⟨fun H j => some (H j), fun f g h =>
    funext fun x => Option.some.inj (congrFun h x)⟩
  let val := fun d : DB X Y => if PairHit p a b d then ‖tensor v d‖^2 else 0
  have h : ∑ d ∈ Finset.univ.map incl, val d ≤ ∑ d, val d :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun d _ _ => by
      unfold val
      split <;> first | exact sq_nonneg _ | exact le_rfl
  rw [Finset.sum_map] at h
  have cell (H : X → Y) : val (incl H) = if p (H a) = p (H b) then ‖tensor v (fun j => some (H j))‖^2 else 0 := by
    have he : PairHit p a b (incl H) ↔ p (H a) = p (H b) := by
      change (∃ u w, some (H a) = some u ∧ some (H b) = some w ∧ p u = p w) ↔ _
      simp
    simp only [val,he]
    rfl
  simpa only [cell,sumWeight,val] using h

/-- Any final fixed pair of distinct measured addresses, in any branch workspace.
Its ordinary equality-event amplitude is controlled by recorded collision
amplitude plus a two-cell readout error independent of the number of queries. -/
theorem readout_pair (p : Y → T) (N : ℝ) (hN : 0 < N)
    (uniform : ∀ B : Finset T, ((Finset.univ.filter fun y => p y ∈ B).card : ℝ) /
      Fintype.card Y ≤ (B.card : ℝ)/N)
    (a b : X) (hab : a ≠ b) (v : DB X Y → V) :
    Real.sqrt (sumWeight (fun H : X → Y => p (H a) = p (H b)) (fun H => tensor v (fun j => some (H j)))) ≤
      Real.sqrt (sumWeight (Collision p) v) + 2 * Real.sqrt (4/N) * Real.sqrt (∑ d, ‖v d‖^2) := by
  classical
  have marginal : sumWeight (PairHit p a b) (tensor v) = sumWeight (PairHit p a b) (readCell b (readCell a v)) :=
    pair_marginal p a b hab v
  have flip : PairHit p a b = PairHit p b a := funext fun d => propext (pair_symm p a b d)
  have left := cell_amp p N hN uniform a b hab v
  have right := cell_amp p N hN uniform b a hab.symm (readCell a v)
  rw [← flip, readCell_energy] at right
  have orig : sumWeight (PairHit p a b) v ≤ sumWeight (Collision p) v := by
    refine Finset.sum_le_sum fun d _ => ?_
    by_cases h : PairHit p a b d
    · obtain ⟨u,w,hu,hw,eq⟩ := h
      have hit : Collision p d := ⟨a,b,u,w,hab,hu,hw,eq⟩
      simp [hit, PairHit, hu, hw, eq]
    · simp [h]
      split <;> first | exact sq_nonneg _ | exact le_rfl
  have hv := Real.sqrt_le_sqrt (sampled_le p a b v)
  rw [marginal] at hv
  linarith [Real.sqrt_le_sqrt orig]


def reports (p : Y → T) (pair : Option (X × X)) (H : X → Y) : Prop :=
  ∃ a b, pair = some (a,b) ∧ a ≠ b ∧ p (H a) = p (H b)

theorem leaf_amp (p : Y → T) (N : ℝ) (hN : 0 < N)
    (uniform : ∀ B : Finset T, ((Finset.univ.filter fun y => p y ∈ B).card : ℝ) /
      Fintype.card Y ≤ (B.card : ℝ)/N) (pair : Option (X × X)) (v : DB X Y → V) :
    Real.sqrt (sumWeight (reports p pair) (fun H => tensor v (fun j => some (H j)))) ≤
      Real.sqrt (sumWeight (Collision p) v) + 2 * Real.sqrt (4/N) * Real.sqrt (∑ d, ‖v d‖^2) := by
  classical
  have h0 : 0 ≤ Real.sqrt (sumWeight (Collision p) v) + 2 * Real.sqrt (4/N) * Real.sqrt (∑ d, ‖v d‖^2) := by positivity
  cases pair with
  | none => simpa [sumWeight,reports] using h0
  | some pair =>
    obtain ⟨a,b⟩ := pair
    by_cases hab : a = b
    · subst b
      simpa [sumWeight,reports] using h0
    · have he : reports p (some (a,b)) = fun H => p (H a) = p (H b) := by
        funext H
        apply propext
        simp [reports,hab]
      rw [he]
      exact readout_pair p N hN uniform a b hab v

theorem numeric (q : ℕ) (N : ℝ) (hN : 0 < N) :
    (Real.sqrt (16*(q:ℝ)^3/N) + 2 * Real.sqrt (4/N))^2 ≤ 16*((q:ℝ)+1)^3/N := by
  have nno := Real.sqrt_pos.mpr hN
  have qno : 0 ≤ (q : ℝ) := Nat.cast_nonneg _
  let Q : ℝ := (q : ℝ) + 1
  have qle : Real.sqrt (q : ℝ) ≤ Real.sqrt Q := Real.sqrt_le_sqrt (by dsimp [Q]; linarith)
  have one : 1 ≤ Real.sqrt Q := Real.le_sqrt_of_sq_le (by dsimp [Q]; nlinarith)
  have b : (q : ℝ) * Real.sqrt q + 1 ≤ Q * Real.sqrt Q := by
    dsimp [Q] at *
    nlinarith [mul_le_mul_of_nonneg_left qle qno]
  have ha : Real.sqrt (16*(q:ℝ)^3/N) = 4 * (q:ℝ) * Real.sqrt q / Real.sqrt N := by
    rw [Real.sqrt_div (by positivity), show 16*(q:ℝ)^3 = (4*(q:ℝ))^2 * q by ring, Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (by positivity)]
  have hb : Real.sqrt (4/N) = 2 / Real.sqrt N := by
    rw [Real.sqrt_div (by norm_num : (0:ℝ) ≤ 4),show (4:ℝ)=2^2 by norm_num,Real.sqrt_sq (by norm_num)]
  rw [ha,hb]
  have upper : 4*(q:ℝ)*Real.sqrt q/Real.sqrt N + 2*(2/Real.sqrt N) ≤ 4*(Q*Real.sqrt Q)/Real.sqrt N := by
    calc _ = 4*((q:ℝ)*Real.sqrt q+1)/Real.sqrt N := by ring
         _ ≤ _ := by gcongr
  apply ((sq_le_sq₀ (by positivity) (by dsimp [Q]; positivity)).mpr upper).trans_eq
  rw [div_pow,mul_pow,mul_pow,Real.sq_sqrt hN.le,Real.sq_sqrt (by dsimp [Q]; positivity)]
  dsimp [Q]
  ring

/-- Final readout for a family of leaves with potentially different workspace
dimensions, when the collision mass and total mass of its recording execution
have already been bounded. -/
theorem readout_bound {I : Type} [Fintype I] {W : I → Type}
    [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace ℝ (W i)]
    (p : Y → T) (N : ℝ) (hN : 0 < N)
    (uniform : ∀ B : Finset T, ((Finset.univ.filter fun y => p y ∈ B).card : ℝ) /
      Fintype.card Y ≤ (B.card : ℝ)/N)
    (q : ℕ) (v : (i : I) → DB X Y → W i) (pair : I → Option (X × X))
    (cb : (∑ i, sumWeight (Collision p) (v i)) ≤ 16*(q:ℝ)^3/N)
    (norm : (∑ i, ∑ d, ‖v i d‖^2) ≤ 1) :
    (∑ i, sumWeight (reports p (pair i)) (fun H => tensor (v i) (fun j => some (H j)))) ≤
      16*((q:ℝ)+1)^3/N := by
  let a := 2 * Real.sqrt (4/N)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  let s := fun i => ∑ d, ‖v i d‖^2
  have nn (i) : 0 ≤ s i := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hpos : 0 ≤ 16*(q:ℝ)^3/N := by positivity
  have hx : ∑ i, (1:ℝ) * (Real.sqrt (sumWeight (Collision p) (v i)))^2 ≤
      (Real.sqrt (16*(q:ℝ)^3/N))^2 := by
    simpa only [one_mul,Real.sq_sqrt (sw_nonneg ..), Real.sq_sqrt hpos] using cb
  have hy : ∑ i, (1:ℝ)*(a*Real.sqrt (s i))^2 ≤ a^2 := by
    simp only [one_mul,mul_pow,Real.sq_sqrt (nn _),← Finset.mul_sum]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left norm (sq_nonneg a)
  have h := PQ.QROM.Purify.sum_mul_add_sq_le (fun _ : I => (1:ℝ))
    (fun i => Real.sqrt (sumWeight (Collision p) (v i))) (fun i => a * Real.sqrt (s i)) (fun _ => by norm_num)
    (Real.sqrt_nonneg _) ha hx hy
  apply le_trans _ (h.trans (numeric q N hN))
  apply Finset.sum_le_sum
  intro i _
  have hleaf := leaf_amp p N hN uniform (pair i) (v i)
  have sq := (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mpr hleaf
  simpa only [one_mul,Real.sq_sqrt (sw_nonneg ..)] using sq


open Classical in
/-- Concrete finite adaptive circuit theorem for the ordinary uniformly sampled
table. The event concerns the two addresses returned by the measured transcript. -/
theorem Paired.forged_pair_bound {I : Type} [Fintype I] (p : Y → T) (N : ℝ) (hN : 0 < N)
    (uniform : ∀ B : Finset T, ((Finset.univ.filter fun y => p y ∈ B).card : ℝ) /
      Fintype.card Y ≤ (B.card : ℝ)/N)
    (q : ℕ) (η : X → V) (hη : ∑ x, ‖η x‖^2 = 1)
    (ψ : I → Wave X Y V) (Φ : I → Worlds X Y V) (run : Paired η q ψ Φ)
    (pair : I → Option (X × X)) :
    (Fintype.card (X → Y) : ℝ)⁻¹ * (∑ i, ∑ H : X → Y, if reports p (pair i) H then ‖Φ i H‖^2 else 0) ≤
      16*((q:ℝ)+1)^3/N := by
  classical
  have cb := Adaptive.collision_bound p N hN uniform η hη q ψ run.recorded
  have total : ∑ i, mass (ψ i) = 1 := by
    clear cb pair
    induction run with
    | start => simp [empty_mass,hη]
    | next prior K O ih => simpa only [Adaptive.step,call_mass,Adaptive.branch_mass] using ih
  let v := fun z : I × X => ψ z.1 z.2
  have bound := readout_bound (W := fun _ : I × X => V) p N hN uniform q v (fun z => pair z.1)
    (by simpa only [Fintype.sum_prod_type,v,sumWeight,badMass] using cb)
    (by simpa only [Fintype.sum_prod_type,v,mass] using total.le)
  rw [← run.event_mass]
  apply le_trans _ bound
  apply le_of_eq
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold sumWeight
  rw [Finset.sum_comm (f := fun x H => if reports p (pair i) H then ‖tensor (v (i,x)) (fun j => some (H j))‖^2 else 0)]
  refine Finset.sum_congr rfl fun H _ => ?_
  by_cases hit : reports p (pair i) H <;> simp [hit,v,tensor,decode]

end Reduction.Compression.Recording.Database
#print axioms Reduction.Compression.Recording.Database.pair_marginal
#print axioms Reduction.Compression.Recording.Database.readout_pair
#print axioms Reduction.Compression.Recording.Database.readout_bound
#print axioms Reduction.Compression.Recording.Database.Paired.forged_pair_bound
