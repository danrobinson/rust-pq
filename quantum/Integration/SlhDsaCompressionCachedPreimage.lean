import Integration.SlhDsaCompressionCachedCollision
import Integration.SlhDsaCompressionPreimage

namespace Reduction.Compression.Recording.Compile
open MLink Ideal OracleComp OracleSpec PQ.Interactive PQ.QROM Quantum ENNReal Classical
open scoped Kronecker ComplexOrder
variable {E α : Type} [Fintype E] [DecidableEq E]
local notation "Work" => WS Input Output E

private def embed : Right ↪ Input := ⟨Sum.inr,fun _ _ e => Sum.inr.inj e⟩

private theorem fixed (a : CF St Blk) (s : List Right) (t : Right → Chain512)
    (M : (Input → Output) → Closed Work α) (out : α → Right) (y : Chain512)
    (q : ℕ) (hq : PUE (spec := unifSpec) cnt0 M q)
    (ρ : Matrix Work Work ℂ) (hp : ρ.PosSemidef) (ht : ρ.trace = 1) :
    (∑ b : Right → Chain512, unifW _ b * qWeight (fun z => b (out z) = y)
      (M (oracle (a,Ideal.Prf.mix s t b))) ρ) ≤ (2*(q:ℝ≥0∞)+1)^2 / 2^512 := by
  classical
  obtain ⟨σ,hσ⟩ := exists_subState (A := (Input × Output) × E) ρ hp ht
  obtain ⟨A,hA⟩ := hq.exists_model σ
  let world := fun b : Right → Chain512 => oracle (a,Ideal.Prf.mix s t b)
  have localPort (b d : Right → Chain512) (x : Input) (hne : world b x ≠ world d x) :
      ∃ u, embed u = x ∧ b u ≠ d u := by
    cases x with
    | inl x => exact (hne rfl).elim
    | inr x =>
      refine ⟨x,rfl,fun he => hne ?_⟩
      by_cases hx : x ∈ s <;> simp [world,oracle,Ideal.Prf.mix,hx,he]
  let _ : AddCommGroup Chain512 := (arrayVectorEquivFin UInt64 8).addCommGroup
  have h := preimage_constant (A.pullback embed world localPort) out y
  simpa only [HybridModel.pullback_prob,hA,hσ,world,MIdeal.Sha512.card_chain512,Nat.cast_pow,Nat.cast_ofNat] using h

private theorem weight_set {Y : Type} [DecidableEq Y] (K : Finset Y) (f : α → Y)
    (X : Closed Work α) (ρ : Matrix Work Work ℂ) :
    qWeight (fun z => f z ∈ K) X ρ = ∑ y ∈ K, qWeight (fun z => f z = y) X ρ := by
  classical
  induction K using Finset.induction_on with
  | empty => simp [qWeight_false_fors]
  | @insert y K hy ih =>
    rw [Finset.sum_insert hy,← ih,← qWeight_or (p := fun z => f z = y) (q := fun z => f z ∈ K)
      (fun z e h => hy (e ▸ h))]
    exact qWeight_congr_ev (fun z => Finset.mem_insert) X ρ

/-- Finding any one of the fixed marked outputs of the fresh background table
when the quantum oracle overlays a revealed classical transcript. -/
theorem cached_preimage (a : CF St Blk) (s : List Right) (t : Right → Chain512)
    (M : (Input → Output) → Closed Work α) (out : α → Right) (K : Finset Chain512)
    (q : ℕ) (hq : PUE (spec := unifSpec) cnt0 M q)
    (ρ : Matrix Work Work ℂ) (hp : ρ.PosSemidef) (ht : ρ.trace = 1) :
    (∑ b : Right → Chain512, unifW _ b * qWeight (fun z => b (out z) ∈ K)
      (M (oracle (a,Ideal.Prf.mix s t b))) ρ) ≤ K.card * ((2*(q:ℝ≥0∞)+1)^2 / 2^512) := by
  simp_rw [weight_set K,Finset.mul_sum]
  rw [Finset.sum_comm]
  exact (Finset.sum_le_sum fun y _ => fixed a s t M out y q hq ρ hp ht).trans_eq (by simp)

open MIdeal.Sha512 in
theorem cached_prefix (S : Sha2Set) (a : CF St Blk) (s : List Right) (t : Right → Chain512)
    (M : (Input → Output) → Closed Work α) (out : α → Right) (B : Finset S.Node)
    (q : ℕ) (hq : PUE (spec := unifSpec) cnt0 M q)
    (ρ : Matrix Work Work ℂ) (hp : ρ.PosSemidef) (ht : ρ.trace = 1) :
    (∑ b : Right → Chain512, unifW _ b * qWeight (fun z => trunc S (b (out z)) ∈ B)
      (M (oracle (a,Ideal.Prf.mix s t b))) ρ) ≤
        (2*(q:ℝ≥0∞)+1)^2 * (B.card / 2^(8*S.vp.params.n)) := by
  let K := prefixCells S B
  have hf := trunc_uniform S (fun y => y ∈ B)
  simp only [SampleableType.prEvent_uniformSample] at hf
  have fraction : (K.card : ℝ≥0∞) / 2^512 = B.card / 2^(8*S.vp.params.n) := by
    have pow8 : (2:ℝ≥0∞)^8 = 256 := by norm_num
    simpa only [K,prefixCells,card_chain512,card_bytes,Nat.cast_pow,Nat.cast_ofNat,
      Finset.filter_mem_eq_inter, Finset.univ_inter,pow_mul,pow8] using hf
  have h := cached_preimage a s t M out K q hq ρ hp ht
  calc _ = ∑ b : Right → Chain512, unifW _ b * qWeight (fun z => b (out z) ∈ K)
             (M (oracle (a,Ideal.Prf.mix s t b))) ρ := by
               apply Finset.sum_congr rfl
               intro b _
               exact congrArg (unifW _ b * ·) (qWeight_congr_ev (fun z => (mem_prefixCells S B _).symm) _ _)
       _ ≤ _ := h
       _ = _ := by rw [← fraction]; exact mul_left_comm _ _ _

end Reduction.Compression.Recording.Compile
#print axioms Reduction.Compression.Recording.Compile.cached_preimage
#print axioms Reduction.Compression.Recording.Compile.cached_prefix
