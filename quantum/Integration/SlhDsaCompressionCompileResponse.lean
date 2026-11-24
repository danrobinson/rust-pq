import Integration.SlhDsaCompressionCompileCore

namespace Reduction.Compression.Recording.Compile.Response
open PQ.QROM Quantum Database MLink Ideal Classical
variable {T : Type} [DecidableEq T] (p : Chain512 → T) (N : ℝ)
abbrev Mapping := Input → Chain512 → Output
def project (a : Mapping) (h : Full) (x : Input) := a x (h x)
noncomputable def control (U : Type) [Fintype U] (a : Mapping) (x : Input) :
    Option Chain512 → Fiber U Output ≃ₗᵢ[ℝ] Fiber U Output
  | none => LinearIsometryEquiv.refl ℝ _
  | some y => shift U (a x y)

set_option maxRecDepth 40000 in
theorem query_vector {A U : QReg} (l : A ≃ (Input × Output) × U) (a : Mapping)
    (h : Full) (v : Vec A) :
    Purify.qvec l (project a h) v = restore U (WithLp.toLp 2 fun x =>
      control (U × Unit) a x (some (h x)) ((expose l v) x)) := by
  let u := (Tight.stdOracle Input Output (U × Unit)).O (project a h) (Purify.splitIso l v)
  have eq : fibers Input Output (U × Unit) u = WithLp.toLp 2 (fun x =>
      control (U × Unit) a x (some (h x)) ((expose l v) x)) := by
    ext1 x
    exact slice_oracle _ _ _ _
  rw [← eq]
  change _ = Purify.joinIso _ _ _ ((fibers Input Output (U × Unit)).symm ((fibers Input Output (U × Unit)) u))
  rw [LinearIsometryEquiv.symm_apply_apply]
  rfl

noncomputable def called (a : Mapping) {A U : QReg} (l : A ≃ (Input × Output) × U) (v : State A) :
    State (QReg.of ((Input × Output) × U)) :=
  reindexCall (expose l) (restore U).symm (control (U × Unit) a) v

theorem called_sparse (a : Mapping) {A U : QReg} (l : A ≃ (Input × Output) × U)
    (v : State A) (t : ℕ) (hs : sparse t v) : sparse (t+1) (called a l v) :=
  reindexCall_sparse (expose l) (restore U).symm (control (U × Unit) a) v t hs

theorem tensor_called (a : Mapping) {A U : QReg} (l : A ≃ (Input × Output) × U)
    (v : State A) (h : Full) : tensor (called a l v) (fun j => some (h j)) =
      Purify.qvec l (project a h) (tensor v (fun j => some (h j))) :=
  (decoded (expose l) (restore U) (control (U × Unit) a) v h).trans
    (query_vector l a h (tensor v (fun j => some (h j)))).symm

theorem called_potential (a : Mapping) {A U : QReg} (l : A ≃ (Input × Output) × U) (v : State A)
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

end Reduction.Compression.Recording.Compile.Response
