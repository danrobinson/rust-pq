import Integration.SlhDsaCompressionCompileKraus
import Integration.SlhDsaCompressionReindex
import PQ.QROM.PurifyTight

namespace Reduction.Compression.Recording.Compile
open PQ.QROM Quantum Database MLink Ideal Classical Finset
variable {T : Type} [DecidableEq T] (p : Chain512 → T) (N : ℝ)
variable {L : LocalSig.{1,0}} (I : L.Interp) {A : QReg}

noncomputable def total {A : QReg} (v : State A) := ∑ d, ‖v d‖^2
noncomputable def bad {A : QReg} (v : State A) := sumWeight (Collision p) v
noncomputable def potential (K : ℝ) {A : QReg} (v : State A) :=
  (Real.sqrt (bad p v) + K * Real.sqrt (total v))^2

omit [DecidableEq T] in
private theorem bad_nn (v : State A) : 0 ≤ bad p v := by
  classical
  unfold bad sumWeight
  apply Finset.sum_nonneg
  intro d _
  split <;> positivity

private theorem total_nn (v : State A) : 0 ≤ total v := Finset.sum_nonneg fun _ _ => sq_nonneg _

private theorem combine {J : Type} [Fintype J] (x y : J → ℝ) (K b m : ℝ)
    (hx : ∀ j, 0 ≤ x j) (hy : ∀ j, 0 ≤ y j) (hK : 0 ≤ K)
    (hb : ∑ j, x j ≤ b) (hm : ∑ j, y j ≤ m) :
    ∑ j, (Real.sqrt (x j) + K * Real.sqrt (y j))^2 ≤
      (Real.sqrt b + K * Real.sqrt m)^2 := by
  have bpos := (Finset.sum_nonneg fun j _ => hx j).trans hb
  have mpos := (Finset.sum_nonneg fun j _ => hy j).trans hm
  have h := Purify.sum_mul_add_sq_le (fun _ : J => (1:ℝ)) (fun j => Real.sqrt (x j))
    (fun j => K*Real.sqrt (y j)) (fun _ => zero_le_one) (Real.sqrt_nonneg b)
    (mul_nonneg hK (Real.sqrt_nonneg m))
  simp only [one_mul,Real.sq_sqrt (hx _),Real.sq_sqrt bpos, mul_pow,Real.sq_sqrt (hy _),
    Real.sq_sqrt mpos,← Finset.mul_sum] at h
  exact h hb (mul_le_mul_of_nonneg_left hm (sq_nonneg K))

private theorem combine_branches {B : Type} {C : B → Type} [∀ b, Fintype (C b)]
    (s : Finset B) (x y : (b : B) → C b → ℝ) (K m n : ℝ)
    (hx : ∀ b c, 0 ≤ x b c) (hy : ∀ b c, 0 ≤ y b c) (hK : 0 ≤ K)
    (hm : ∑ b ∈ s, ∑ c, x b c ≤ m) (hn : ∑ b ∈ s, ∑ c, y b c ≤ n) :
    ∑ b ∈ s, ∑ c, (Real.sqrt (x b c) + K * Real.sqrt (y b c))^2 ≤
      (Real.sqrt m + K * Real.sqrt n)^2 := by
  classical
  let J := Σ b : s, C b.val
  have eq (f : (b : B) → C b → ℝ) :
      (∑ j : J, f j.1.val j.2) = ∑ b ∈ s, ∑ c, f b c := by
    rw [Fintype.sum_sigma]
    exact Finset.sum_attach s (fun b => ∑ c, f b c)
  have h := combine (fun j : J => x j.1.val j.2) (fun j : J => y j.1.val j.2) K m n
    (fun j => hx _ _) (fun j => hy _ _) hK ((eq x).le.trans hm) ((eq y).le.trans hn)
  exact (eq (fun b c => (Real.sqrt (x b c) + K * Real.sqrt (y b c))^2)).ge.trans h

private theorem total_bound (o : L.Op A) (v : State A) (s : Finset (L.Outcome o)) :
    (∑ b ∈ s, ∑ c, total (kraus I o b c v)) ≤ total v := by
  simpa only [total,sumWeight,ite_true] using kraus_weight I o v s (fun _ => True)

theorem kraus_potential (o : L.Op A) (s : Finset (L.Outcome o)) (v : State A) (K : ℝ) (hK : 0 ≤ K) :
    (∑ b ∈ s, ∑ c, potential p K (kraus I o b c v)) ≤ potential p K v :=
  combine_branches s (fun b c => bad p (kraus I o b c v)) (fun b c => total (kraus I o b c v))
    K _ _ (fun _ _ => bad_nn p _) (fun _ _ => total_nn _) hK (kraus_weight I o v s (Collision p))
    (total_bound I o v s)

noncomputable def called (a : CF St Blk) {A U : QReg} (l : A ≃ (Input × Output) × U) (v : State A) :
    State (QReg.of ((Input × Output) × U)) :=
  reindexCall (expose l) (restore U).symm (control (U × Unit) a) v

theorem called_sparse (a : CF St Blk) {A U : QReg} (l : A ≃ (Input × Output) × U)
    (v : State A) (t : ℕ) (hs : sparse t v) : sparse (t+1) (called a l v) :=
  reindexCall_sparse (expose l) (restore U).symm (control (U × Unit) a) v t hs

section
variable {X Y V W U : Type} [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y] [DecidableEq Y]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]

private theorem decoded (L : V ≃ₗᵢ[ℝ] Work X U) (R : Work X U ≃ₗᵢ[ℝ] W)
    (O : X → Option Y → U ≃ₗᵢ[ℝ] U) (v : DB X Y → V) (h : X → Y) :
    tensor (reindexCall L R.symm O v) (fun j => some (h j)) =
      R (WithLp.toLp 2 fun j => O j (some (h j)) (L (tensor v (fun j => some (h j))) j)) :=
  tensor_reindexCall L R.symm O v (fun j => some (h j))

end

theorem tensor_called (a : CF St Blk) {A U : QReg} (l : A ≃ (Input × Output) × U)
    (v : State A) (h : Full) : tensor (called a l v) (fun j => some (h j)) =
      Purify.qvec l (project a h) (tensor v (fun j => some (h j))) :=
  (decoded (expose l) (restore U) (control (U × Unit) a) v h).trans
    (query_vector l a h (tensor v (fun j => some (h j)))).symm

theorem called_potential (a : CF St Blk) {A U : QReg} (l : A ≃ (Input × Output) × U) (v : State A)
    (t Q : ℕ) (ht : t ≤ Q) (hs : sparse t v) (hN : 0 < N)
    (uniform : ∀ B : Finset T, ((Finset.univ.filter fun y => p y ∈ B).card : ℝ) / Fintype.card Chain512 ≤
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

end Reduction.Compression.Recording.Compile
#print axioms Reduction.Compression.Recording.Compile.called_potential
#print axioms Reduction.Compression.Recording.Compile.kraus_potential
