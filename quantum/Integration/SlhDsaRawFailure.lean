import Integration.SlhDsaCompressionDatabaseGrowth
import Integration.SlhDsaRawSearch
import Integration.SlhDsaCompressionClassPort

/-! Recorded database growth and arbitrary finite readout predicates for raw quantum oracles. -/
namespace Reduction.Compression.Recording.RawFailure
open PQ.QROM Quantum Database MLink Ideal Classical Finset
open RawSearch (kraus kraus_weight total total_bound total_nn tensor_kraus decodedWorld sparse expose restore kraus_sparse initialState initial_sparse initial_weight initial_mass)
open Compile (Vec sumPV sumPV_ret combine_branches aggregate_program clocked mixed_mean_over)
variable {X Y Z : Type} [Fintype X] [Nonempty X] [DecidableEq X] [Fintype Y] [Nonempty Y] [DecidableEq Y]
  [Fintype Z] [DecidableEq Z] [AddCommGroup Z]
local notation "RState" => (fun A : QReg => DB X Y → Vec A)
set_option linter.unusedSectionVars false
variable {α : Type} {L : LocalSig.{1,0}} (I : L.Interp) (a : X → Y → Z)
variable (P : DB X Y → Prop) (E : α → (X → Y) → Prop)
local notation "Prog" => QuantumComp L (qromSpec X Z) (fun _ => α)

noncomputable def potential (K : ℝ) {A : QReg} (v : RState A) :=
  (Real.sqrt (sumWeight P v) + K * Real.sqrt (total v))^2
noncomputable def score {A : QReg} (x : Prog A) (v : RState A) :=
  sumPV I (RawSearch.project a) (fun h t => E t.2 h) x (decodedWorld v)

private theorem branch {A : QReg} (o : L.Op A) (s : Finset (L.Outcome o)) (v : RState A) (K : ℝ) (hK : 0 ≤ K) :
    (∑ b ∈ s, ∑ c, potential P K (kraus I o b c v)) ≤ potential P K v :=
  combine_branches s (fun b c => sumWeight P (kraus I o b c v)) (fun b c => total (kraus I o b c v))
    K _ _ (fun _ _ => sw_nonneg _ _) (fun _ _ => total_nn _) hK (kraus_weight I o v s P) (total_bound I o v s)

private theorem score_kraus {A : QReg} (o : L.Op A) (b : L.Outcome o) (c : (L.next o b × Unit) × (A × Unit))
    (x : Prog (L.next o b)) (v : RState A) :
    sumPV I (RawSearch.project a) (fun h t => E t.2 h) x (fun h => Purify.primKraus I o b c (decodedWorld v h)) = score I a E x (kraus I o b c v) := by
  apply congrArg (sumPV I (RawSearch.project a) (fun h t => E t.2 h) x)
  exact funext fun h => (tensor_kraus I o b c v (fun j => some (h j))).symm

set_option maxRecDepth 8192 in
private theorem local_score {A : QReg} (o : L.Op A) (k : (b : L.Outcome o) → Prog (L.next o b))
    (v : RState A) (K : ℝ) (hK : 0 ≤ K)
    (hc : ∀ b c, score I a E (k b) (kraus I o b c v) ≤ potential P K (kraus I o b c v)) :
    score I a E (QuantumComp.primBind o k) v ≤ potential P K v := by
  exact aggregate_program I o k (RawSearch.project a) (fun h t => E t.2 h)
    (decodedWorld v) (fun b c => potential P K (kraus I o b c v))
    (potential P K v) (fun b c => (score_kraus I a E o b c (k b) v).le.trans (hc b c))
    (fun s => branch I P o s v K hK)

private theorem query_eq {A U : QReg} (l : A ≃ (X × Z) × U)
    (k : (qromSpec X Z).Result () → Prog _) (v : RState A) :
    score I a E (QuantumComp.queryBind () U l k) v = score I a E (k ()) (RawSearch.called a l v) := by
  simp only [score,sumPV,decodedWorld,Purify.pv_queryBind]
  exact Finset.sum_congr rfl fun h _ =>
    congrArg (Purify.pv I (RawSearch.project a h) (k ()) (fun t => E t.2 h)) (RawSearch.tensor_called a l v h).symm

private theorem query_potential {A U : QReg} (l : A ≃ (X × Z) × U) (v : RState A)
    (t : ℕ) (δ K : ℝ) (hδ : 0 ≤ δ) (hK : 0 ≤ K) (g : Growth P t δ) (hs : sparse t v) :
    potential P K (RawSearch.called a l v) ≤ potential P (K+4*Real.sqrt δ) v := by
  have h := growth_reindex P t δ hδ g (expose l) (restore U).symm (RawSearch.control (U × Unit) a) v hs
  have mass := reindexCall_mass (expose l) (restore U).symm (RawSearch.control (U × Unit) a) v
  change total (RawSearch.called a l v) = total v at mass
  change Real.sqrt (sumWeight P (RawSearch.called a l v)) ≤ Real.sqrt (sumWeight P v) + _ * Real.sqrt (total v) at h
  unfold potential
  rw [mass,add_mul]
  exact (sq_le_sq₀ (by positivity) (by positivity)).mpr (by linarith only [h])

private theorem ret_eq {A : QReg} (y : α) (v : RState A) :
    score I a E (QuantumComp.pure y) v = sumWeight (E y) (fun H => tensor v (fun j => some (H j))) :=
  sumPV_ret I (RawSearch.project a) (fun h t => E t.2 h) (W := fun _ => α) y (decodedWorld v)

/-- Bounded native circuits, including arbitrary measured instruments, can
accumulate at most one growth charge per coherent query. The terminal estimate
can verify any event against a bounded classical readout certificate. -/
theorem native_bound {A : QReg} (x : Prog A) (Q n t : ℕ) (hx : QueryBounded x n) (ht : t+n ≤ Q)
    (v : RState A) (sp : sparse t v) (δ K : ℝ) (hδ : 0 ≤ δ) (hK : 0 ≤ K)
    (growth : ∀ t ≤ Q, Growth P t δ)
    (leaf : ∀ (A : QReg) (y : α) (w : RState A), sumWeight (E y) (fun h => tensor w (fun i => some (h i))) ≤ potential P K w) :
    score I a E x v ≤ potential P (K+n*(4*Real.sqrt δ)) v := by
  refine clocked (P := fun {A} x n t => t+n ≤ Q → ∀ v : RState A, sparse t v →
    score I a E x v ≤ potential P (K+n*(4*Real.sqrt δ)) v) ?_ ?_ ?_ x n t hx ht v sp <;> clear ht sp v
  · intro A y n t _ v _
    rw [ret_eq]
    apply (leaf A y v).trans
    unfold potential
    refine (sq_le_sq₀ (by positivity) (by positivity)).mpr ?_
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity : 0 ≤ (n:ℝ)*(4*Real.sqrt δ))) (Real.sqrt_nonneg _))
  · intro A o k n t ih ht v hs
    exact local_score I a P E o k v _ (by positivity) (fun b c => ih b ht _ (kraus_sparse I o b c v t hs))
  · intro A U l k n t ih ht v hs
    rw [query_eq]
    apply (ih (by omega) _ (RawSearch.called_sparse a l v t hs)).trans
    have eq : K+(n+1:ℕ)*(4*Real.sqrt δ) = (K+n*(4*Real.sqrt δ))+4*Real.sqrt δ := by push_cast; ring
    rw [eq]
    exact query_potential a P l v t δ _ hδ (by positivity) (growth t (by omega)) hs

/-- A clean empty database yields the homogeneous pure-state bound required
for arbitrary (mixed) initial density matrices. -/
theorem pure_mean {A : QReg} (x : Prog A) (q : ℕ) (hx : QueryBounded x q) (u : Vec A)
    (δ K : ℝ) (hδ : 0 ≤ δ) (hK : 0 ≤ K) (empty : ¬P (fun _ => none))
    (growth : ∀ t ≤ q, Growth P t δ)
    (leaf : ∀ (A : QReg) (y : α) (w : RState A), sumWeight (E y) (fun h => tensor w (fun i => some (h i))) ≤ potential P K w) :
    (∑ h : (X → Y), (Fintype.card (X → Y) : ℝ)⁻¹ * Purify.pv I (RawSearch.project a h) x
      (fun t => E t.2 h) u) ≤ (K+q*(4*Real.sqrt δ))^2 * ‖u‖^2 := by
  have hh := native_bound I a P E x q q 0 hx (by omega) (initialState u) (initial_sparse u) δ K hδ hK growth leaf
  unfold score sumPV decodedWorld potential total at hh
  simpa only [RawSearch.initial_response,initial_weight P empty,Real.sqrt_zero,zero_add,initial_mass,mul_pow,
    Real.sq_sqrt (sq_nonneg ‖u‖)] using hh

open OracleComp OracleSpec PQ.Interactive ENNReal
open scoped ComplexOrder
theorem machine_mean {W : Type} [Fintype W] [DecidableEq W]
    (M : (X → Z) → Closed (WS X Z W) α) (q : ℕ) (hq : PUE (spec := unifSpec) cnt0 M q)
    (ρ₀ : Matrix (WS X Z W) (WS X Z W) ℂ) (hp : ρ₀.PosSemidef) (ht : ρ₀.trace = 1)
    (δ K : ℝ) (hδ : 0 ≤ δ) (hK : 0 ≤ K) (empty : ¬P (fun _ => none))
    (growth : ∀ t ≤ q, Growth P t δ)
    (leaf : ∀ (A : QReg) (y : α) (w : RState A), sumWeight (E y) (fun h => tensor w (fun i => some (h i))) ≤ potential P K w) :
    (∑ h : (X → Y), unifW _ h * qWeight (fun y => E y h) (M (RawSearch.project a h)) ρ₀) ≤
      ENNReal.ofReal ((K+q*(4*Real.sqrt δ))^2) := by
  obtain ⟨x,hx,he⟩ := hq.exists_prog_qprob
  obtain ⟨ρ,hρ⟩ := exists_subState (A := (X × Z) × W) ρ₀ hp ht
  apply le_trans _ (mixed_mean_over LocalSig.Interp.instruments x ρ q hx (RawSearch.project a)
    (fun h t => E t.2 h) _ (sq_nonneg _) (fun u =>
      pure_mean LocalSig.Interp.instruments a P E x q hx u δ K hδ hK empty growth leaf))
  apply Finset.sum_le_sum
  intro h _
  apply mul_le_mul' le_rfl
  rw [he (fun y => E y h) _ ρ,← hρ]

end Reduction.Compression.Recording.RawFailure
#print axioms Reduction.Compression.Recording.RawFailure.native_bound
#print axioms Reduction.Compression.Recording.RawFailure.machine_mean
