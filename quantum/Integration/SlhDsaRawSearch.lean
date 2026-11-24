import Integration.SlhDsaCompressionCompileResponseNative

/-! Collision search with a raw finite oracle domain and arbitrary cell readout. -/
namespace Reduction.Compression.Recording.RawSearch
open PQ.QROM Quantum Database MLink Ideal Classical Finset
open Compile (Fiber shift slice_oracle Vec fibers decoded combine_branches sumPV aggregate_program clocked sumPV_ret price price_nn initial_numeric)
set_option linter.unusedSectionVars false
variable {X Y Z : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Nonempty Y]
  [Fintype Z] [DecidableEq Z] [AddCommGroup Z]
local notation "RState" => (fun A : QReg => DB X Y → Vec A)
private noncomputable def realIso {V W : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [NormedSpace ℝ V] [NormedSpace ℝ W]
    [IsScalarTower ℝ ℂ V] [IsScalarTower ℝ ℂ W] (e : V ≃ₗᵢ[ℂ] W) : V ≃ₗᵢ[ℝ] W :=
  { toLinearEquiv := e.toLinearEquiv.restrictScalars ℝ, norm_map' := e.norm_map }

noncomputable def expose {A U : QReg} (l : A ≃ (X × Z) × U) :
    Vec A ≃ₗᵢ[ℝ] Work X (Fiber (U × Unit) Z) :=
  (realIso (Purify.splitIso l)).trans (fibers X Z (U × Unit))

noncomputable def restore (U : QReg) :
    Work X (Fiber (U × Unit) Z) ≃ₗᵢ[ℝ] Vec (QReg.of ((X × Z) × U)) :=
  (fibers X Z (U × Unit)).symm.trans (realIso (Purify.joinIso X Z U))

variable {T : Type} [DecidableEq T] (p : Y → T) (N : ℝ) (hN : 0 < N)
variable (uniform : ∀ B : Finset T, ((Finset.univ.filter fun y => p y ∈ B).card : ℝ) /
  Fintype.card Y ≤ (B.card:ℝ)/N)
variable {L : LocalSig.{1,0}} (I : L.Interp) {A : QReg} (o : L.Op A)
noncomputable def kraus (b : L.Outcome o) (c : (L.next o b × Unit) × (A × Unit)) (v : RState A) : RState (L.next o b) :=
  fun d => Purify.primKraus I o b c (v d)

def sparse (t : ℕ) {A : QReg} (v : RState A) := ∀ d, t < (occupied d).card → v d = 0

theorem kraus_sparse (b : L.Outcome o) (c : (L.next o b × Unit) × (A × Unit)) (v : RState A)
    (t : ℕ) (h : sparse t v) : sparse t (kraus I o b c v) := by
  intro d hd
  simp only [kraus,h d hd,map_zero]

set_option linter.constructorNameAsVariable false in
theorem tensor_kraus (b : L.Outcome o) (c : (L.next o b × Unit) × (A × Unit)) (v : RState A) (d : (DB X Y)) :
    tensor (kraus I o b c v) d = Purify.primKraus I o b c (tensor v d) := by
  unfold tensor kraus
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro e he
  exact (((Purify.primKraus I o b c).restrictScalars ℝ).map_smul (coeffDB d e) (v e)).symm

/-- A finite selection of an instrument's outcomes can only lose weight.
The selection and all Kraus operators are independent of the sampled table. -/
theorem kraus_weight (v : RState A) (s : Finset (L.Outcome o)) (P : (DB X Y) → Prop) :
    (∑ b ∈ s, ∑ c, sumWeight P (kraus I o b c v)) ≤ sumWeight P v := by
  classical
  unfold sumWeight
  simp only [kraus]
  have h (b : L.Outcome o) :
      (∑ c : (L.next o b × Unit) × (A × Unit), ∑ d, if P d then ‖Purify.primKraus I o b c (v d)‖^2 else 0) =
        ∑ d, if P d then ∑ c, ‖Purify.primKraus I o b c (v d)‖^2 else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro d _
    by_cases hd : P d <;> simp [hd]
  simp_rw [h]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro d _
  by_cases hd : P d
  · simpa [hd] using Purify.prim_kraus_sum_le I o s (v d)
  · simp [hd]

noncomputable def total {A : QReg} (v : RState A) := ∑ d, ‖v d‖^2
noncomputable def bad {A : QReg} (v : RState A) := sumWeight (Collision p) v
noncomputable def potential (K : ℝ) {A : QReg} (v : RState A) :=
  (Real.sqrt (bad p v) + K * Real.sqrt (total v))^2

omit [DecidableEq T] in
private theorem bad_nn (v : RState A) : 0 ≤ bad p v := by
  classical
  unfold bad sumWeight
  apply Finset.sum_nonneg
  intro d _
  split <;> positivity

theorem total_nn (v : RState A) : 0 ≤ total v := Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem total_bound (o : L.Op A) (v : RState A) (s : Finset (L.Outcome o)) :
    (∑ b ∈ s, ∑ c, total (kraus I o b c v)) ≤ total v := by
  simpa only [total,sumWeight,ite_true] using kraus_weight I o v s (fun _ => True)

theorem kraus_potential (o : L.Op A) (s : Finset (L.Outcome o)) (v : RState A) (K : ℝ) (hK : 0 ≤ K) :
    (∑ b ∈ s, ∑ c, potential p K (kraus I o b c v)) ≤ potential p K v :=
  combine_branches s (fun b c => bad p (kraus I o b c v)) (fun b c => total (kraus I o b c v))
    K _ _ (fun _ _ => bad_nn p _) (fun _ _ => total_nn _) hK (kraus_weight I o v s (Collision p))
    (total_bound I o v s)

noncomputable def decodedWorld {A : QReg} (v : RState A) (h : (X → Y)) :=
  tensor v (fun j => some (h j))

omit [DecidableEq T] in
include hN in
theorem leaf_price {A : QReg} (Q n : ℕ) (v : RState A) :
    (Real.sqrt (bad p v) + (2*Real.sqrt (4/N))*Real.sqrt (total v))^2 ≤ potential p (price N Q n) v := by
    unfold potential price
    apply (sq_le_sq₀ (by positivity) (by positivity)).mpr
    apply add_le_add le_rfl
    apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
    exact le_add_of_nonneg_left (by positivity)

def project (a : (X → Y → Z)) (h : (X → Y)) (x : X) := a x (h x)
noncomputable def control (U : Type) [Fintype U] (a : (X → Y → Z)) (x : X) :
    Option Y → Fiber U Z ≃ₗᵢ[ℝ] Fiber U Z
  | none => LinearIsometryEquiv.refl ℝ _
  | some y => shift U (a x y)

set_option maxRecDepth 40000 in
theorem query_vector {A U : QReg} (l : A ≃ (X × Z) × U) (a : (X → Y → Z))
    (h : (X → Y)) (v : Vec A) :
    Purify.qvec l (project a h) v = restore U (WithLp.toLp 2 fun x =>
      control (U × Unit) a x (some (h x)) ((expose l v) x)) := by
  let u := (Tight.stdOracle X Z (U × Unit)).O (project a h) (Purify.splitIso l v)
  have eq : fibers X Z (U × Unit) u = WithLp.toLp 2 (fun x =>
      control (U × Unit) a x (some (h x)) ((expose l v) x)) := by
    ext1 x
    exact slice_oracle _ _ _ _
  rw [← eq]
  change _ = Purify.joinIso _ _ _ ((fibers X Z (U × Unit)).symm ((fibers X Z (U × Unit)) u))
  rw [LinearIsometryEquiv.symm_apply_apply]
  rfl

noncomputable def called (a : (X → Y → Z)) {A U : QReg} (l : A ≃ (X × Z) × U) (v : RState A) :
    RState (QReg.of ((X × Z) × U)) :=
  reindexCall (expose l) (restore U).symm (control (U × Unit) a) v

theorem called_sparse (a : (X → Y → Z)) {A U : QReg} (l : A ≃ (X × Z) × U)
    (v : RState A) (t : ℕ) (hs : sparse t v) : sparse (t+1) (called a l v) :=
  reindexCall_sparse (expose l) (restore U).symm (control (U × Unit) a) v t hs

theorem tensor_called (a : (X → Y → Z)) {A U : QReg} (l : A ≃ (X × Z) × U)
    (v : RState A) (h : (X → Y)) : tensor (called a l v) (fun j => some (h j)) =
      Purify.qvec l (project a h) (tensor v (fun j => some (h j))) :=
  (decoded (expose l) (restore U) (control (U × Unit) a) v h).trans
    (query_vector l a h (tensor v (fun j => some (h j)))).symm

theorem called_potential (a : (X → Y → Z)) {A U : QReg} (l : A ≃ (X × Z) × U) (v : RState A)
    (t Q : ℕ) (ht : t ≤ Q) (hs : sparse t v) (hN : 0 < N)
    (uniform : ∀ B : Finset T, ((Finset.univ.filter fun y => p y ∈ B).card : ℝ) / Fintype.card Y ≤
      (B.card:ℝ)/N) (K : ℝ) (hK : 0 ≤ K) :
    potential p K (called a l v) ≤ potential p (K + 4*Real.sqrt ((Q:ℝ)/N)) v := by
  have hm := reindexCall_mass (expose l) (restore U).symm (control (U × Unit) a) v
  have hb := reindexCall_bad_amplitude p N hN uniform (expose l) (restore U).symm (control (U × Unit) a) v t hs
  change total (called a l v) = total v at hm
  change Real.sqrt (bad p (called a l v)) ≤ Real.sqrt (bad p v) +
    4*Real.sqrt ((t:ℝ)/N)*Real.sqrt (total v) at hb
  have ht' := Real.sqrt_le_sqrt (div_le_div_of_nonneg_right (Nat.cast_le.mpr ht : (t:ℝ) ≤ Q) hN.le)
  unfold potential
  rw [hm]
  apply (sq_le_sq₀ (by positivity) (by positivity)).mpr
  have hs' := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht' (by norm_num : (0:ℝ) ≤ 4)) (Real.sqrt_nonneg (total v))
  calc _ ≤ (Real.sqrt (bad p v) + 4*Real.sqrt ((t:ℝ)/N)*Real.sqrt (total v)) + K*Real.sqrt (total v) := add_le_add hb le_rfl
       _ ≤ _ := by rw [add_mul]; linarith only [hs']


section Initial
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
private noncomputable def emptyOnly {X Y V : Type} [Zero V] (u : V) (d : DB X Y) : V := by
  classical
  exact if d = fun _ => none then u else 0

private theorem emptyOnly_mass (u : V) : ∑ d : DB X Y, ‖emptyOnly u d‖ ^ 2 = ‖u‖^2 := by
  classical
  simp [emptyOnly,apply_ite (fun v : V => ‖v‖),ite_pow]

private theorem emptyOnly_bad (p : Y → T) (u : V) :
    sumWeight (Collision (I := X) p) (emptyOnly u) = 0 := by
  classical
  unfold sumWeight
  apply Finset.sum_eq_zero
  intro d _
  by_cases h : d = fun _ => none
  · subst d
    exact ite_eq_right (by rintro ⟨i,j,a,b,hd,hi,_⟩; cases hi)
  · simp [emptyOnly,h]

private theorem emptyOnly_weight (P : DB X Y → Prop) (hP : ¬P (fun _ => none)) (u : V) :
    sumWeight P (emptyOnly u) = 0 := by
  classical
  unfold sumWeight
  refine Finset.sum_eq_zero fun d _ => ?_
  by_cases h : d = fun _ => none
  · subst d
    exact ite_eq_right hP
  · simp [emptyOnly,h]

private theorem emptyOnly_sparse (u : V) (d : DB X Y) (hd : 0 < (occupied d).card) : emptyOnly u d = 0 := by
  classical
  refine ite_eq_right fun h => ?_
  subst d
  simp [occupied] at hd

private theorem emptyOnly_tensor (h : X → Y) (u : V) :
    tensor (emptyOnly u) (fun i => some (h i)) = coeff Y ^ Fintype.card X • u := by
  classical
  simp [tensor, emptyOnly, smul_ite, coeffDB, entry]
/-- Before the first query, all recording cells are empty. -/
noncomputable def initialState (u : Vec A) : RState A := emptyOnly u

theorem initial_mass (u : Vec A) : ∑ d, ‖initialState (X:=X) (Y:=Y) u d‖ ^ 2 = ‖u‖^2 := emptyOnly_mass u

theorem initial_bad {T : Type} (p : Y → T) (u : Vec A) :
    sumWeight (Collision (I:=X) p) (initialState u) = 0 := emptyOnly_bad p u

theorem initial_weight (P : (DB X Y) → Prop) (hP : ¬P (fun _ => none)) (u : Vec A) :
    sumWeight P (initialState u) = 0 := emptyOnly_weight P hP u

theorem initial_sparse (u : Vec A) : sparse (X:=X) (Y:=Y) 0 (initialState u) := emptyOnly_sparse u

theorem initial_tensor (h : (X → Y)) (u : Vec A) :
    tensor (initialState u) (fun i => some (h i)) = coeff Y ^ Fintype.card X • u :=
  emptyOnly_tensor h u

theorem pv_smul_real {W : QReg → Type} (I : L.Interp) (H : X → Z) (x : QuantumComp L (qromSpec X Z) W A)
    (ev : (Σ i, W i) → Prop) (r : ℝ) (u : Vec A) :
    Purify.pv I H x ev (r • u) = r^2 * Purify.pv I H x ev u := by
  have e : ketBra (r • u) (r • u) = ((r : ℂ)^2) • ketBra u u := by
    ext i j
    simp only [ketBra_apply,WithLp.ofLp_smul,Pi.smul_apply,Complex.real_smul,star_mul',
      Complex.star_def,Complex.conj_ofReal,Matrix.smul_apply,smul_eq_mul]
    ring
  unfold Purify.pv Purify.gv
  rw [e,map_smul]
  simp [smul_eq_mul, ← Complex.ofReal_pow]


end Initial
variable {α : Type}
variable (a : (X → Y → Z)) (pick : α → Option (X × X))
local notation "Prog" => QuantumComp L (qromSpec X Z) (fun _ => α)
noncomputable def score {A : QReg} (x : Prog A) (v : RState A) :=
  sumPV I (project a) (fun h t => reports p (pick t.2) h) x (decodedWorld v)

omit [DecidableEq T] in
private theorem score_kraus {A : QReg} (o : L.Op A) (b : L.Outcome o) (c : (L.next o b × Unit) × (A × Unit))
    (x : Prog (L.next o b)) (v : RState A) :
    sumPV I (project a) (fun h t => reports p (pick t.2) h) x (fun h => Purify.primKraus I o b c (decodedWorld v h)) = score p I a pick x (kraus I o b c v) := by
  apply congrArg (sumPV I (project a) (fun h t => reports p (pick t.2) h) x)
  exact funext fun h => (tensor_kraus I o b c v (fun y => some (h y))).symm

private theorem at_local {A : QReg} (o : L.Op A) (k : (b : L.Outcome o) → Prog (L.next o b))
    (v : RState A) (K : ℝ) (hK : 0 ≤ K)
    (hc : ∀ b c, score p I a pick (k b) (kraus I o b c v) ≤ potential p K (kraus I o b c v)) :
    score p I a pick (QuantumComp.primBind o k) v ≤ potential p K v := by
  exact aggregate_program I o k (project a) (fun H t => reports p (pick t.2) H)
    (decodedWorld v) (fun b c => potential p K (kraus I o b c v))
    (potential p K v) (fun b c => (score_kraus p I a pick o b c (k b) v).le.trans (hc b c))
    (fun s => kraus_potential p I o s v K hK)

omit [DecidableEq T] in
private theorem at_query {A U : QReg} (l : A ≃ (X × Z) × U)
    (k : (qromSpec X Z).Result () → Prog _) (v : RState A) :
    score p I a pick (QuantumComp.queryBind () U l k) v =
      score p I a pick (k ()) (called a l v) := by
  simp only [score,sumPV,decodedWorld,Purify.pv_queryBind]
  apply Finset.sum_congr rfl
  intro h _
  exact congrArg (Purify.pv I (project a h) (k ()) (fun t => reports p (pick t.2) h)) (tensor_called a l v h).symm

omit [DecidableEq T] in
private theorem score_ret {A : QReg} (y : α) (v : RState A) :
    score p I a pick (QuantumComp.pure y) v = sumWeight (reports p (pick y)) (fun H => tensor v (fun j => some (H j))) :=
  sumPV_ret I (project a) (fun h t => reports p (pick t.2) h) (W := fun _ => α) y (decodedWorld v)

include hN uniform in
private theorem ret_bound {A : QReg} (y : α) (Q n : ℕ) (v : RState A) :
    score p I a pick (QuantumComp.pure y) v ≤ potential p (price N Q n) v := by
    have h := leaf_amp p N hN uniform (pick y) v
    have h' : sumWeight (reports p (pick y)) (fun H => tensor v (fun j => some (H j))) ≤
        (Real.sqrt (bad p v) + (2*Real.sqrt (4/N))*Real.sqrt (total v))^2 := by
      exact (Real.sqrt_le_iff.mp h).2
    rw [score_ret]
    exact h'.trans (leaf_price p N hN Q n v)

include hN uniform in
private theorem query_bound {A U : QReg} (l : A ≃ (X × Z) × U) (k : (qromSpec X Z).Result () → Prog _)
    (Q n t : ℕ)
    (ih : t+1+n ≤ Q → ∀ w : RState _, sparse (t+1) w → score p I a pick (k ()) w ≤ potential p (price N Q n) w)
    (ht : t+(n+1) ≤ Q) (v : RState A) (hs : sparse t v) :
    score p I a pick (QuantumComp.queryBind () U l k) v ≤ potential p (price N Q (n+1)) v := by
    rw [at_query]
    have h := ih (by omega) _ (called_sparse a l v t hs)
    have hop := called_potential p N a l v t Q (by omega) hs hN uniform _ (price_nn N Q n)
    apply h.trans
    have pp : price N Q (n+1) = price N Q n + 4*Real.sqrt ((Q:ℝ)/N) := by
      unfold price
      push_cast
      ring
    rw [pp]
    exact hop


include hN uniform in
theorem native_bound {A : QReg} (x : Prog A) (Q n t : ℕ) (hQ : QueryBounded x n) (ht : t+n ≤ Q)
    (v : RState A) (hs : sparse t v) : score p I a pick x v ≤ potential p (price N Q n) v := by
  refine clocked (P := fun {A} x n t => t+n ≤ Q → ∀ v : RState A, sparse t v →
    score p I a pick x v ≤ potential p (price N Q n) v) ?_ ?_ ?_ x n t hQ ht v hs <;> clear hs v ht
  · intro A y n t _ v _
    exact ret_bound p N hN uniform I a pick y Q n v
  · intro A o k n t ih ht v hs
    apply at_local p I a pick o k v _ (price_nn N Q n)
    intro b c
    exact ih b ht _ (kraus_sparse I o b c v t hs)
  · intro A U l k n t ih ht v hs
    exact query_bound p N hN uniform I a pick l k Q n t ih ht v hs

theorem initial_response {A : QReg} (h : (X → Y)) (x : Prog A) (ev : (Σ _ : QReg, α) → Prop) (u : Vec A) :
    Purify.pv I (project a h) x ev (tensor (initialState u) (fun i => some (h i))) =
      (Fintype.card (X → Y) : ℝ)⁻¹ * Purify.pv I (project a h) x ev u := by
  rw [initial_tensor,pv_smul_real,total_weight]

include hN uniform in
theorem pure_mean {A : QReg} (x : Prog A) (q : ℕ) (hx : QueryBounded x q) (u : Vec A) :
    (∑ h : (X → Y), (Fintype.card (X → Y) : ℝ)⁻¹ * Purify.pv I (project a h) x
      (fun t => reports p (pick t.2) h) u) ≤ 16*((q:ℝ)+1)^3/N * ‖u‖^2 := by
  have hh := native_bound p N hN uniform I a pick x q q 0 hx (by omega) (initialState u) (initial_sparse u)
  unfold score sumPV decodedWorld potential price bad total at hh
  simp only [initial_response,initial_bad,initial_mass] at hh
  exact hh.trans (initial_numeric q N hN _ (sq_nonneg _))

end Reduction.Compression.Recording.RawSearch
#print axioms Reduction.Compression.Recording.RawSearch.pure_mean
