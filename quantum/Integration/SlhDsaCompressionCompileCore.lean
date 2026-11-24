import Integration.SlhDsaCompressionCompilePotential
import Integration.SlhDsaCompressionCompileInitial

/-! A bounded VCVio program is evaluated against its decoded recording state.
Local instruments may have infinitely many outcomes. The finite-cut Kraus
estimate controls their total via a summable branch series. -/

namespace Reduction.Compression.Recording.Compile
open PQ.QROM Quantum Database MLink Ideal Classical Finset
variable {α T : Type} [DecidableEq T] (p : Chain512 → T) (N : ℝ) (hN : 0 < N)
variable (uniform : ∀ B : Finset T, ((Finset.univ.filter fun y => p y ∈ B).card : ℝ) /
  Fintype.card Chain512 ≤ (B.card:ℝ)/N)
variable {L : LocalSig.{1,0}} (I : L.Interp) (a : CF St Blk) (pick : α → Option (Input × Input))
local notation "Prog" => QuantumComp L (qromSpec Input Output) (fun _ => α)
noncomputable def sumPV {B X Y : Type} [Fintype B] [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y] [AddCommGroup Y] {A : QReg} {W : QReg → Type}
    (world : B → X → Y) (ev : B → (Σ g, W g) → Prop) (x : QuantumComp L (qromSpec X Y) W A) (u : B → Vec A) :=
  ∑ h, Purify.pv I (world h) x (ev h) (u h)

noncomputable def decodedWorld {A : QReg} (v : State A) (h : Full) :=
  tensor v (fun j => some (h j))

noncomputable def price (Q n : ℕ) := 4*(n:ℝ)*Real.sqrt ((Q:ℝ)/N) + 2*Real.sqrt (4/N)
theorem price_nn (Q n : ℕ) : 0 ≤ price N Q n := by unfold price; positivity

private theorem aggregate {Ω B : Type} [Fintype Ω] {C : B → Type} [∀ b, Fintype (C b)]
    (inWeight : Ω → ℝ) (br : (b : B) → C b → Ω → ℝ) (cap : (b : B) → C b → ℝ) (K : ℝ)
    (hn : ∀ b c h, 0 ≤ br b c h)
    (hs : ∀ h, HasSum (fun b => ∑ c, br b c h) (inWeight h))
    (hh : ∀ b c, ∑ h, br b c h ≤ cap b c)
    (hm : ∀ s : Finset B, ∑ b ∈ s, ∑ c, cap b c ≤ K) : ∑ h, inWeight h ≤ K := by
  classical
  have ht := hasSum_sum (s := (Finset.univ : Finset Ω)) fun h _ => hs h
  rw [← ht.tsum_eq]
  apply Real.tsum_le_of_sum_le
  · intro b
    exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => hn ..
  · intro s
    apply le_trans _ (hm s)
    apply Finset.sum_le_sum
    intro b _
    rw [Finset.sum_comm]
    exact Finset.sum_le_sum fun c _ => hh b c

theorem aggregate_program {B X Y : Type} [Fintype B] [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y] [AddCommGroup Y] {A : QReg} {W : QReg → Type}
    (o : L.Op A) (k : (b : L.Outcome o) → QuantumComp L (qromSpec X Y) W (L.next o b))
    (world : B → X → Y) (ev : B → (Σ g, W g) → Prop) (w : B → Vec A)
    (cap : (b : L.Outcome o) → ((L.next o b × Unit) × (A × Unit)) → ℝ) (K : ℝ)
    (hc : ∀ b c, sumPV I world ev (k b) (fun H => Purify.primKraus I o b c (w H)) ≤ cap b c)
    (hm : ∀ s : Finset (L.Outcome o), ∑ b ∈ s, ∑ c, cap b c ≤ K) :
    sumPV I world ev (QuantumComp.primBind o k) w ≤ K := by
  apply aggregate _ (fun b c H => Purify.pv I (world H) (k b) (ev H) (Purify.primKraus I o b c (w H))) cap
  · exact fun _ _ _ => Purify.pv_nonneg ..
  · intro H
    obtain ⟨s,e⟩ := Purify.pv_primBind I (world H) o k (ev H) (w H)
    exact e ▸ s.hasSum
  · exact hc
  · exact hm

theorem clocked {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    {W : QReg → Type} (P : ∀ {A : QReg}, QuantumComp L (qromSpec X Y) W A → ℕ → ℕ → Prop)
    (ret : ∀ (A) (y : W A) n t, P (QuantumComp.pure y) n t)
    (localOp : ∀ (A) (o : L.Op A) (k : (b : L.Outcome o) → QuantumComp L (qromSpec X Y) W (L.next o b))
       n t, (∀ b, P (k b) n t) → P (QuantumComp.primBind o k) n t)
    (queryOp : ∀ (A U : QReg) (l : A ≃ (X × Y) × U)
       (k : (qromSpec X Y).Result () → QuantumComp L (qromSpec X Y) W _)
       n t, P (k ()) n (t+1) → P (QuantumComp.queryBind () U l k) (n+1) t)
    {A : QReg} (x : QuantumComp L (qromSpec X Y) W A) (n t : ℕ) (hx : QueryBounded x n) : P x n t := by
  revert n t hx
  refine QuantumComp.inductionOn (motive := fun A x => ∀ n t : ℕ, QueryBounded x n → P x n t) ?_ ?_ ?_ x
  · exact fun A y n t _ => ret A y n t
  · exact fun A o k ih n t hq => localOp A o k n t fun b => ih b n t ((QuantumComp.isQueryBound_primBind_iff ..).1 hq b)
  · intro A i U l k ih n t hq
    cases i
    obtain ⟨hn,hk⟩ := (QuantumComp.isQueryBound_queryBind_iff (L := L) (spec := qromSpec X Y)
      PUnit.unit U l k (fun _ => n)).1 hq
    have hn' : 0<n := hn
    obtain ⟨n,rfl⟩ : ∃ n', n=n'+1 := ⟨n-1,by omega⟩
    have hk' : QueryBounded (k ()) n := (hk ()).mono fun j => by rw [Subsingleton.elim j ()]; simp
    exact queryOp A U l k n t (ih () n (t+1) hk')

theorem sumPV_ret {B X Y : Type} [Fintype B] [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    [AddCommGroup Y] {A : QReg} {W : QReg → Type} (world : B → X → Y) (ev : B → (Σ g, W g) → Prop)
    (y : W A) (u : B → Vec A) : sumPV I world ev (QuantumComp.pure y) u = sumWeight (fun h => ev h ⟨A,y⟩) u := by
  apply Finset.sum_congr rfl
  intro h _
  exact Purify.pv_pure I (world h) y (ev h) (u h)

omit [DecidableEq T] in
include hN in
theorem leaf_price {A : QReg} (Q n : ℕ) (v : State A) :
    (Real.sqrt (bad p v) + (2*Real.sqrt (4/N))*Real.sqrt (total v))^2 ≤ potential p (price N Q n) v := by
    unfold potential price
    apply (sq_le_sq₀ (by positivity) (by positivity)).mpr
    apply add_le_add le_rfl
    apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
    exact le_add_of_nonneg_left (by positivity)

end Reduction.Compression.Recording.Compile
