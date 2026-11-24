import Integration.SlhDsaCompressionRecording

/-! A finite recording database for coherent queries with an address register
and an arbitrary response/workspace Hilbert space. Prefix collisions are measured
in the recording basis. -/

namespace Reduction.Compression.Recording
namespace Database
set_option linter.unusedSectionVars false

variable {X Y T V : Type} [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y]
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V]
abbrev DB (X Y : Type) := X → Option Y
abbrev Rest (x : X) (Y : Type) := {j : X // j ≠ x} → Option Y
abbrev Wave (X Y V : Type) := X → DB X Y → V

def assemble (x : X) (r : Rest x Y) (u : Option Y) : DB X Y :=
  (Equiv.funSplitAt x (Option Y)).symm (u,r)

@[simp] theorem assemble_at (x : X) (r : Rest x Y) (u : Option Y) :
    assemble x r u x = u := by simp [assemble, Equiv.funSplitAt, Equiv.piSplitAt]
@[simp] theorem assemble_other (x : X) (r : Rest x Y) (u : Option Y) {z : X} (hz : z ≠ x) :
    assemble x r u z = r ⟨z,hz⟩ := by simp [assemble, Equiv.funSplitAt, Equiv.piSplitAt, hz]

theorem assemble_restrict (x : X) (d : DB X Y) :
    assemble x (fun z => d z.val) (d x) = d := (Equiv.funSplitAt x (Option Y)).symm_apply_apply d

noncomputable def call (O : X → Option Y → V ≃ₗᵢ[ℝ] V) (ψ : Wave X Y V) : Wave X Y V :=
  fun x d => query (O x) (fun u => ψ x (assemble x (fun z => d z.val) u)) (d x)

theorem call_at (O : X → Option Y → V ≃ₗᵢ[ℝ] V) (ψ : Wave X Y V)
    (x : X) (r : Rest x Y) (u : Option Y) :
    call O ψ x (assemble x r u) = query (O x) (fun t => ψ x (assemble x r t)) u := by
  unfold call
  simp only [assemble_at]
  rw [show (fun z : {z : X // z ≠ x} => assemble x r u z.val) = r from funext fun z => assemble_other _ _ _ z.property]

def occupied {I : Type} [Fintype I] (d : DB I Y) : Finset I :=
  Finset.univ.filter fun x => (d x).isSome

theorem occupied_rest_le (x : X) (r : Rest x Y) (u : Option Y) :
    (occupied r).card ≤ (occupied (assemble x r u)).card := by
  apply Finset.card_le_card_of_injOn Subtype.val
  · intro j hj
    change j ∈ occupied r at hj
    change j.val ∈ occupied (assemble x r u)
    simp only [occupied, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    simpa only [assemble_other _ _ _ j.property] using hj
  · exact fun _ _ _ _ h => Subtype.ext h

theorem occupied_assemble_le (x : X) (r : Rest x Y) (u : Option Y) :
    (occupied (assemble x r u)).card ≤ (occupied r).card + 1 := by
  let f : {z : X // z ≠ x} ↪ X := ⟨Subtype.val,Subtype.val_injective⟩
  have hs : occupied (assemble x r u) ⊆ insert x ((occupied r).map f) := by
    intro z hz
    by_cases h : z = x
    · simp [h]
    · apply Finset.mem_insert_of_mem
      apply Finset.mem_map.mpr
      refine ⟨⟨z,h⟩,?_,rfl⟩
      simpa only [occupied, Finset.mem_filter, Finset.mem_univ, true_and, assemble_other _ _ _ h] using hz
  exact (Finset.card_le_card hs).trans ((Finset.card_insert_le ..).trans_eq (by simp))

def Sparse (t : ℕ) (ψ : Wave X Y V) : Prop :=
  ∀ x d, t < (occupied d).card → ψ x d = 0

theorem query_zero (O : Option Y → V ≃ₗᵢ[ℝ] V) :
    query O (fun _ => 0) = fun _ => 0 := by
  funext u
  cases u <;> simp [query, swap, mean]

theorem call_sparse (O : X → Option Y → V ≃ₗᵢ[ℝ] V) (ψ : Wave X Y V)
    (t : ℕ) (hψ : Sparse t ψ) : Sparse (t+1) (call O ψ) := by
  intro x d hd
  let r : Rest x Y := fun z => d z.val
  have de : assemble x r (d x) = d := assemble_restrict x d
  have hcard := occupied_assemble_le x r (d x)
  rw [de] at hcard
  have zero : (fun u => ψ x (assemble x r u)) = fun _ => 0 := by
    funext u
    apply hψ
    have h := occupied_rest_le x r u
    omega
  calc call O ψ x d = call O ψ x (assemble x r (d x)) := congrArg _ de.symm
       _ = _ := by rw [call_at,zero,query_zero]

def Collision {I : Type} (p : Y → T) (d : DB I Y) :=
  ∃ i j a b, i ≠ j ∧ d i = some a ∧ d j = some b ∧ p a = p b

def prefixes {I : Type} [Fintype I] [DecidableEq T] (p : Y → T) (d : DB I Y) : Finset T :=
  (occupied d).biUnion fun i => ((d i).map p).toFinset

theorem mem_prefixes {I : Type} [Fintype I] [DecidableEq T] (p : Y → T) (d : DB I Y) (v : T) :
    v ∈ prefixes p d ↔ ∃ i a, d i = some a ∧ p a = v := by
  simp only [prefixes, Finset.mem_biUnion, occupied, Finset.mem_filter, Finset.mem_univ, true_and,
    Option.mem_toFinset, Option.mem_def]
  constructor
  · rintro ⟨i,_,h⟩
    cases e : d i with
    | none => simp [e] at h
    | some a => exact ⟨i,a,e,by simpa [e] using h⟩
  · rintro ⟨i,a,h,rfl⟩
    exact ⟨i,by simp [h],by simp [h]⟩

theorem prefixes_card {I : Type} [Fintype I] [DecidableEq T] (p : Y → T) (d : DB I Y) :
    (prefixes p d).card ≤ (occupied d).card := by
  apply (Finset.card_biUnion_le ..).trans
  calc _ ≤ ∑ _ ∈ occupied d, 1 := Finset.sum_le_sum fun i _ => by cases h : d i <;> simp
       _ = _ := by simp

theorem collision_assemble [DecidableEq T] (p : Y → T) (x : X) (r : Rest x Y) (u : Option Y) :
    Collision p (assemble x r u) ↔ Collision p r ∨ ∃ a, u = some a ∧ p a ∈ prefixes p r := by
  constructor
  · rintro ⟨i,j,a,b,hij,hi,hj,hab⟩
    by_cases h : i = x
    · subst i
      exact Or.inr ⟨a,(assemble_at ..).symm.trans hi,(mem_prefixes ..).mpr
        ⟨⟨j,hij.symm⟩,b,(assemble_other _ _ _ hij.symm).symm.trans hj,hab.symm⟩⟩
    by_cases h' : j = x
    · subst j
      exact Or.inr ⟨b,(assemble_at ..).symm.trans hj,(mem_prefixes ..).mpr
        ⟨⟨i,h⟩,a,(assemble_other _ _ _ h).symm.trans hi,hab⟩⟩
    exact Or.inl ⟨⟨i,h⟩,⟨j,h'⟩,a,b,fun e => hij (congrArg Subtype.val e),
      (assemble_other _ _ _ h).symm.trans hi,(assemble_other _ _ _ h').symm.trans hj,hab⟩
  · rintro (⟨i,j,a,b,hij,hi,hj,hab⟩|⟨a,hu,h⟩)
    · exact ⟨i.val,j.val,a,b,fun e => hij (Subtype.ext e),(assemble_other _ _ _ i.property).trans hi,
        (assemble_other _ _ _ j.property).trans hj,hab⟩
    · obtain ⟨j,b,hj,hb⟩ := (mem_prefixes ..).mp h
      exact ⟨x,j.val,a,b,j.property.symm,(assemble_at ..).trans hu,(assemble_other _ _ _ j.property).trans hj,hb.symm⟩

section Norms
noncomputable local instance collDec {I : Type} (p : Y → T) (d : DB I Y) : Decidable (Collision p d) := Classical.propDecidable _

variable [DecidableEq T]
noncomputable def mass (ψ : Wave X Y V) : ℝ :=
  ∑ x, ∑ d, ‖ψ x d‖^2

noncomputable def badMass (p : Y → T) (ψ : Wave X Y V) : ℝ := by
  classical
  exact ∑ x, ∑ d, if Collision p d then ‖ψ x d‖^2 else 0

lemma sum_fibres (x : X) (f : DB X Y → ℝ) :
    ∑ d, f d = ∑ r : Rest x Y, ∑ u : Option Y, f (assemble x r u) := by
  classical
  let e := Equiv.funSplitAt x (Option Y)
  calc ∑ d, f d = ∑ z : Option Y × Rest x Y, f (e.symm z) := (Equiv.sum_comp e.symm f).symm
       _ = _ := by rw [Fintype.sum_prod_type, Finset.sum_comm]; rfl

theorem call_mass (O : X → Option Y → V ≃ₗᵢ[ℝ] V) (ψ : Wave X Y V) :
    mass (call O ψ) = mass ψ := by
  unfold mass
  apply Finset.sum_congr rfl
  intro x _
  rw [sum_fibres x, sum_fibres x (fun d => ‖ψ x d‖^2)]
  refine Finset.sum_congr rfl fun r _ => ?_
  simpa only [call_at, Fintype.sum_option, energy] using query_energy (O x) (fun u => ψ x (assemble x r u))

private theorem fibre_le (p : Y → T) (N : ℝ) (hN : 0 < N)
    (uniform : ∀ B : Finset T,
      (((Finset.univ.filter fun y => p y ∈ B).card : ℝ) / Fintype.card Y) ≤ (B.card : ℝ) / N)
    (O : X → Option Y → V ≃ₗᵢ[ℝ] V) (ψ : Wave X Y V) (t : ℕ)
    (hs : Sparse t ψ) (clean : ∀ x d, Collision p d → ψ x d = 0) (x : X) (r : Rest x Y) :
    (∑ u : Option Y, if Collision p (assemble x r u) then ‖call O ψ x (assemble x r u)‖^2 else 0) ≤
      16 * ((t : ℝ) / N) * (∑ u : Option Y, ‖ψ x (assemble x r u)‖^2) := by
  classical
  let φ := fun u => ψ x (assemble x r u)
  let B := prefixes p r
  let M := Finset.univ.filter fun y => p y ∈ B
  have ht : 0 ≤ 16 * ((t : ℝ) / N) := by positivity
  have hz (all : ∀ u : Option Y, φ u = 0) : ∀ u, call O ψ x (assemble x r u) = 0 := by
    intro u
    rw [call_at]
    change query (O x) φ u = 0
    rw [show φ = fun _ => 0 from funext all, query_zero]
  by_cases live : (occupied r).card ≤ t ∧ ¬Collision p r
  · have fresh : ∀ y ∈ M, φ (some y) = 0 := fun y hy =>
      clean x _ ((collision_assemble ..).mpr (Or.inr ⟨y,rfl,(Finset.mem_filter.mp hy).2⟩))
    have h := query_marked_energy (O x) φ M fresh
    have m : (M.card : ℝ) / Fintype.card Y ≤ (t : ℝ) / N :=
      (uniform B).trans (div_le_div_of_nonneg_right (by exact_mod_cast (prefixes_card p r).trans live.1) hN.le)
    have he : 0 ≤ energy φ := add_nonneg (sq_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    have h' := h.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left m (by norm_num : (0:ℝ) ≤ 16)) he)
    simp only [Fintype.sum_option]
    simp only [collision_assemble, live.2, false_or, reduceCtorEq, false_and,
      exists_false, ite_false, zero_add, Option.some.injEq, exists_eq_left', call_at]
    rw [← Finset.sum_filter]
    simpa only [M,B,φ,energy] using h'
  · have forced : ∀ u, φ u = 0 := by
      intro u
      by_cases k : (occupied r).card ≤ t
      · exact clean x _ ((collision_assemble ..).mpr (Or.inl (by tauto)))
      · exact hs x _ (lt_of_lt_of_le (Nat.lt_of_not_ge k) (occupied_rest_le x r u))
    simp only [hz forced, norm_zero, zero_pow (by decide : 2 ≠ 0), ite_self, Finset.sum_const_zero]
    exact mul_nonneg ht (Finset.sum_nonneg fun _ _ => sq_nonneg _)

/-- Sum over precisely the fibres of the database state, including fibres which
already contain a collision away from the queried cell. -/
theorem call_clean_badMass (p : Y → T) (N : ℝ) (hN : 0 < N)
    (uniform : ∀ B : Finset T,
      (((Finset.univ.filter fun y => p y ∈ B).card : ℝ) / Fintype.card Y) ≤ (B.card : ℝ) / N)
    (O : X → Option Y → V ≃ₗᵢ[ℝ] V) (ψ : Wave X Y V) (t : ℕ)
    (hs : Sparse t ψ) (clean : ∀ x d, Collision p d → ψ x d = 0) :
    badMass p (call O ψ) ≤ 16 * ((t : ℝ) / N) * mass ψ := by
  classical
  unfold badMass mass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x _
  rw [sum_fibres x, sum_fibres x (fun d => ‖ψ x d‖^2),Finset.mul_sum]
  exact Finset.sum_le_sum fun r _ => fibre_le p N hN uniform O ψ t hs clean x r


private theorem mass_nonneg (ψ : Wave X Y V) : 0 ≤ mass ψ :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

private theorem bad_nonneg (p : Y → T) (ψ : Wave X Y V) : 0 ≤ badMass p ψ := by
  classical
  exact Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun d _ => by
    split <;> first | exact sq_nonneg _ | exact le_rfl

private theorem bad_le (p : Y → T) (ψ : Wave X Y V) : badMass p ψ ≤ mass ψ := by
  classical
  exact Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun d _ => by
    split <;> first | exact le_rfl | exact sq_nonneg _

private theorem query_add (O : Option Y → V ≃ₗᵢ[ℝ] V) (f g : Option Y → V) :
    query O (fun u => f u + g u) = fun u => query O f u + query O g u := by
  have swap_add (φ ξ : Option Y → V) : swap (fun u => φ u + ξ u) = fun u => swap φ u + swap ξ u := by
    funext u
    cases u <;> simp [swap, mean, Finset.sum_add_distrib, smul_add, smul_sub]; abel
  unfold query
  rw [swap_add]
  simp only [map_add]
  rw [swap_add]

theorem call_add (O : X → Option Y → V ≃ₗᵢ[ℝ] V) (f g : Wave X Y V) (x : X) (d : DB X Y) :
    call O (fun i z => f i z + g i z) x d = call O f x d + call O g x d := by
  unfold call
  rw [query_add]

private theorem bad_triangle (p : Y → T) (f g : Wave X Y V) :
    Real.sqrt (badMass p (fun x d => f x d + g x d)) ≤
      Real.sqrt (badMass p f) + Real.sqrt (badMass p g) := by
  classical
  let w := fun z : X × DB X Y => if Collision p z.2 then (1:ℝ) else 0
  have weight (φ : Wave X Y V) : ∑ z : X × DB X Y, w z * ‖φ z.1 z.2‖^2 = badMass p φ := by
    simp only [Fintype.sum_prod_type, badMass, w, ite_mul, one_mul, zero_mul]
  have h := PQ.QROM.Purify.sum_mul_add_sq_le w
    (fun z => ‖f z.1 z.2‖) (fun z => ‖g z.1 z.2‖) (fun z => by unfold w; split <;> norm_num)
    (Real.sqrt_nonneg (badMass p f)) (Real.sqrt_nonneg (badMass p g))
    (by rw [weight, Real.sq_sqrt (bad_nonneg ..)])
    (by rw [weight, Real.sq_sqrt (bad_nonneg ..)])
  apply (Real.sqrt_le_left (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mpr
  rw [← weight]
  apply le_trans _ h
  refine Finset.sum_le_sum fun z _ => ?_
  apply mul_le_mul_of_nonneg_left _ (by unfold w; split <;> norm_num)
  exact (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr (norm_add_le _ _)

/-- Amplitude of a collision after an arbitrary recording query. The input may
already contain collision amplitude; sparsity alone bounds the increment. -/
theorem call_bad_amplitude (p : Y → T) (N : ℝ) (hN : 0 < N)
    (uniform : ∀ B : Finset T,
      (((Finset.univ.filter fun y => p y ∈ B).card : ℝ) / Fintype.card Y) ≤ (B.card : ℝ) / N)
    (O : X → Option Y → V ≃ₗᵢ[ℝ] V) (ψ : Wave X Y V) (t : ℕ) (hs : Sparse t ψ) :
    Real.sqrt (badMass p (call O ψ)) ≤ Real.sqrt (badMass p ψ) +
      4 * Real.sqrt ((t : ℝ) / N) * Real.sqrt (mass ψ) := by
  classical
  let f : Wave X Y V := fun x d => if Collision p d then ψ x d else 0
  let g : Wave X Y V := fun x d => if Collision p d then 0 else ψ x d
  have splitψ : ψ = fun x d => f x d + g x d := by
    funext x d
    by_cases hd : Collision p d <;> simp [f,g,hd]
  have splitCall : call O ψ = fun x d => call O f x d + call O g x d := by
    conv_lhs => rw [splitψ]
    exact funext fun x => funext fun d => call_add O f g x d
  have prior : mass f = badMass p ψ := by
    simp only [mass,badMass,f,apply_ite (fun x : V => ‖x‖),norm_zero,ite_pow,zero_pow (by decide : 2 ≠ 0)]
  have cleanMass : mass g ≤ mass ψ := by
    refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun d _ => ?_
    by_cases hd : Collision p d <;> simp [g, hd]
  have sg : Sparse t g := fun x d hd => by simp [g,hs x d hd]
  have cg : ∀ x d, Collision p d → g x d = 0 := fun x d hd => by simp [g,hd]
  have hclean := call_clean_badMass p N hN uniform O g t sg cg
  have loss := Real.sqrt_le_sqrt (hclean.trans
    (mul_le_mul_of_nonneg_left cleanMass (by positivity : 0 ≤ 16 * ((t : ℝ)/N))))
  rw [Real.sqrt_mul (by positivity),Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 16),
    show Real.sqrt 16 = 4 by rw [show (16:ℝ) = 4^2 by norm_num, Real.sqrt_sq (by norm_num)]] at loss
  rw [splitCall]
  refine (bad_triangle p _ _).trans (add_le_add ?_ loss)
  apply Real.sqrt_le_sqrt
  exact (bad_le p _).trans_eq ((call_mass O f).trans prior)


/-- All input-address and workspace amplitudes at a fixed database. -/
abbrev Work (X V : Type) [Fintype X] := PiLp 2 (fun _ : X => V)

noncomputable def act (U : Work X V →ₗᵢ[ℝ] Work X V) (ψ : Wave X Y V) : Wave X Y V :=
  fun x d => U (WithLp.toLp 2 (fun j => ψ j d)) x

private theorem act_slice (U : Work X V →ₗᵢ[ℝ] Work X V) (ψ : Wave X Y V) (d : DB X Y) :
    ∑ x, ‖act U ψ x d‖^2 = ∑ x, ‖ψ x d‖^2 := by
  have h := congrArg (fun a : ℝ => a^2) (U.norm_map (WithLp.toLp 2 (fun j => ψ j d)))
  simpa only [PiLp.norm_sq_eq_of_L2, act] using h

theorem act_mass (U : Work X V →ₗᵢ[ℝ] Work X V) (ψ : Wave X Y V) :
    mass (act U ψ) = mass ψ := by
  unfold mass
  rw [Finset.sum_comm, Finset.sum_comm (f := fun x d => ‖ψ x d‖^2)]
  exact Finset.sum_congr rfl fun d _ => act_slice U ψ d

theorem act_badMass (p : Y → T) (U : Work X V →ₗᵢ[ℝ] Work X V) (ψ : Wave X Y V) :
    badMass p (act U ψ) = badMass p ψ := by
  classical
  unfold badMass
  rw [Finset.sum_comm, Finset.sum_comm (f := fun x d => if Collision p d then ‖ψ x d‖^2 else 0)]
  refine Finset.sum_congr rfl fun d _ => ?_
  by_cases hd : Collision p d <;> simp [hd, act_slice]

theorem act_sparse (U : Work X V →ₗᵢ[ℝ] Work X V) (ψ : Wave X Y V) (t : ℕ) (hs : Sparse t ψ) :
    Sparse t (act U ψ) := by
  intro x d h
  have z : (WithLp.toLp 2 (fun j => ψ j d) : Work X V) = 0 := by
    ext j
    exact hs j d h
  simp [act,z]

noncomputable def emptyStart (η : X → V) : Wave X Y V := by
  classical
  exact fun x d => if d = fun _ => none then η x else 0

theorem empty_sparse (η : X → V) : Sparse 0 (emptyStart (Y := Y) η) := by
  classical
  intro x d h
  have ne : d ≠ fun _ => none := by
    intro e
    subst d
    simp [occupied] at h
  simp [emptyStart, ne]

theorem empty_mass (η : X → V) : mass (emptyStart (Y := Y) η) = ∑ x, ‖η x‖^2 := by
  classical
  simp [mass, emptyStart, apply_ite (fun z : V => ‖z‖), ite_pow]

theorem empty_badMass (p : Y → T) (η : X → V) : badMass p (emptyStart η) = 0 := by
  classical
  unfold badMass
  refine Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun d _ => ?_
  by_cases hd : d = fun _ => none
  · subst d
    simp [Collision]
  · simp [emptyStart,hd]

/-- Recording circuit with an arbitrary workspace isometry between consecutive
controlled queries. The workspace operation can mix the entire address register. -/
noncomputable def run (η : X → V) (U : ℕ → Work X V →ₗᵢ[ℝ] Work X V)
    (O : ℕ → X → Option Y → V ≃ₗᵢ[ℝ] V) : ℕ → Wave X Y V
  | 0 => emptyStart η
  | t+1 => call (O t) (act (U t) (run η U O t))

theorem run_sparse (η : X → V) (U : ℕ → Work X V →ₗᵢ[ℝ] Work X V)
    (O : ℕ → X → Option Y → V ≃ₗᵢ[ℝ] V) (t : ℕ) :
    Sparse t (run η U O t) := by
  induction t with
  | zero => exact empty_sparse η
  | succ t ih => exact call_sparse _ _ t (act_sparse _ _ _ ih)

theorem run_mass (η : X → V) (U : ℕ → Work X V →ₗᵢ[ℝ] Work X V)
    (O : ℕ → X → Option Y → V ≃ₗᵢ[ℝ] V) (t : ℕ) :
    mass (run η U O t) = ∑ x, ‖η x‖^2 := by
  induction t with
  | zero => exact empty_mass η
  | succ t ih => rw [run,call_mass,act_mass,ih]

/-- Prefix collision mass after q recording queries from an empty database. -/
theorem run_collision_bound (p : Y → T) (N : ℝ) (hN : 0 < N)
    (uniform : ∀ B : Finset T,
      (((Finset.univ.filter fun y => p y ∈ B).card : ℝ) / Fintype.card Y) ≤ (B.card : ℝ) / N)
    (η : X → V) (norm : ∑ x, ‖η x‖^2 = 1) (U : ℕ → Work X V →ₗᵢ[ℝ] Work X V)
    (O : ℕ → X → Option Y → V ≃ₗᵢ[ℝ] V) (q : ℕ) :
    badMass p (run η U O q) ≤ 16 * (q : ℝ)^3 / N := by
  have amp (t : ℕ) (ht : t ≤ q) : Real.sqrt (badMass p (run η U O t)) ≤
      (t : ℝ) * (4 * Real.sqrt ((q : ℝ) / N)) := by
    induction t with
    | zero => simp [run,empty_badMass]
    | succ t ih =>
      have h := call_bad_amplitude p N hN uniform (O t) (act (U t) (run η U O t)) t
        (act_sparse _ _ t (run_sparse η U O t))
      rw [act_badMass,act_mass,run_mass,norm,Real.sqrt_one,mul_one] at h
      have ltq : t ≤ q := by omega
      have mono := Real.sqrt_le_sqrt (div_le_div_of_nonneg_right (by exact_mod_cast ltq : (t:ℝ) ≤ q) hN.le)
      apply h.trans
      push_cast
      nlinarith [ih ltq,mono]
  have h := (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mpr (amp q le_rfl)
  rw [Real.sq_sqrt (bad_nonneg ..)] at h
  apply h.trans_eq
  rw [mul_pow,mul_pow,Real.sq_sqrt (by positivity)]
  ring


open MLink Ideal MIdeal.Sha512 in
theorem sha512_recording_bound (S : Sha2Set) (η : X → V) (norm : ∑ x, ‖η x‖^2 = 1)
    (U : ℕ → Work X V →ₗᵢ[ℝ] Work X V)
    (O : ℕ → X → Option Chain512 → V ≃ₗᵢ[ℝ] V) (q : ℕ) :
    badMass (trunc S) (run η U O q) ≤ 16 * (q : ℝ)^3 / 2^(8*S.vp.params.n) :=
  run_collision_bound (trunc S) _ (by positivity) (fun B => (prefixCells_fraction S B).le) η norm U O q

end Norms

end Database
end Reduction.Compression.Recording
#print axioms Reduction.Compression.Recording.Database.run_sparse
#print axioms Reduction.Compression.Recording.Database.call_bad_amplitude
#print axioms Reduction.Compression.Recording.Database.run_collision_bound
#print axioms Reduction.Compression.Recording.Database.sha512_recording_bound
