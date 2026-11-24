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

private noncomputable def decodedWorld {A : QReg} (v : State A) (h : Full) :=
  tensor v (fun j => some (h j))

noncomputable def score {A : QReg} (x : Prog A) (v : State A) :=
  sumPV I (project a) (fun h t => reports p (pick t.2) h) x (decodedWorld v)

noncomputable def price (Q n : ℕ) := 4*(n:ℝ)*Real.sqrt ((Q:ℝ)/N) + 2*Real.sqrt (4/N)
private theorem price_nn (Q n : ℕ) : 0 ≤ price N Q n := by unfold price; positivity

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

omit [DecidableEq T] in
private theorem score_kraus {A : QReg} (o : L.Op A) (b : L.Outcome o) (c : (L.next o b × Unit) × (A × Unit))
    (x : Prog (L.next o b)) (v : State A) :
    sumPV I (project a) (fun h t => reports p (pick t.2) h) x (fun h => Purify.primKraus I o b c (decodedWorld v h)) = score p I a pick x (kraus I o b c v) := by
  apply congrArg (sumPV I (project a) (fun h t => reports p (pick t.2) h) x)
  exact funext fun h => (tensor_kraus I o b c v (fun y => some (h y))).symm

private theorem at_local {A : QReg} (o : L.Op A) (k : (b : L.Outcome o) → Prog (L.next o b))
    (v : State A) (K : ℝ) (hK : 0 ≤ K)
    (hc : ∀ b c, score p I a pick (k b) (kraus I o b c v) ≤ potential p K (kraus I o b c v)) :
    score p I a pick (QuantumComp.primBind o k) v ≤ potential p K v := by
  exact aggregate_program I o k (project a) (fun H t => reports p (pick t.2) H)
    (decodedWorld v) (fun b c => potential p K (kraus I o b c v))
    (potential p K v) (fun b c => (score_kraus p I a pick o b c (k b) v).le.trans (hc b c))
    (fun s => kraus_potential p I o s v K hK)

omit [DecidableEq T] in
private theorem at_query {A U : QReg} (l : A ≃ (Input × Output) × U)
    (k : (qromSpec Input Output).Result () → Prog _) (v : State A) :
    score p I a pick (QuantumComp.queryBind () U l k) v =
      score p I a pick (k ()) (called a l v) := by
  simp only [score,sumPV,decodedWorld,Purify.pv_queryBind]
  apply Finset.sum_congr rfl
  intro h _
  exact congrArg (Purify.pv I (project a h) (k ()) (fun t => reports p (pick t.2) h)) (tensor_called a l v h).symm

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
private theorem score_ret {A : QReg} (y : α) (v : State A) :
    score p I a pick (QuantumComp.pure y) v = sumWeight (reports p (pick y)) (fun H => tensor v (fun j => some (H j))) :=
  sumPV_ret I (project a) (fun h t => reports p (pick t.2) h) (W := fun _ => α) y (decodedWorld v)

omit [DecidableEq T] in
include hN in
private theorem leaf_price {A : QReg} (Q n : ℕ) (v : State A) :
    (Real.sqrt (bad p v) + (2*Real.sqrt (4/N))*Real.sqrt (total v))^2 ≤ potential p (price N Q n) v := by
    unfold potential price
    apply (sq_le_sq₀ (by positivity) (by positivity)).mpr
    apply add_le_add le_rfl
    apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
    exact le_add_of_nonneg_left (by positivity)

include hN uniform in
private theorem ret_bound {A : QReg} (y : α) (Q n : ℕ) (v : State A) :
    score p I a pick (QuantumComp.pure y) v ≤ potential p (price N Q n) v := by
    have h := leaf_amp p N hN uniform (pick y) v
    have h' : sumWeight (reports p (pick y)) (fun H => tensor v (fun j => some (H j))) ≤
        (Real.sqrt (bad p v) + (2*Real.sqrt (4/N))*Real.sqrt (total v))^2 := by
      exact (Real.sqrt_le_iff.mp h).2
    rw [score_ret]
    exact h'.trans (leaf_price p N hN Q n v)

include hN uniform in
private theorem query_bound {A U : QReg} (l : A ≃ (Input × Output) × U) (k : (qromSpec Input Output).Result () → Prog _)
    (Q n t : ℕ)
    (ih : t+1+n ≤ Q → ∀ w : State _, sparse (t+1) w → score p I a pick (k ()) w ≤ potential p (price N Q n) w)
    (ht : t+(n+1) ≤ Q) (v : State A) (hs : sparse t v) :
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
    (v : State A) (hs : sparse t v) : score p I a pick x v ≤ potential p (price N Q n) v := by
  refine clocked (P := fun {A} x n t => t+n ≤ Q → ∀ v : State A, sparse t v →
    score p I a pick x v ≤ potential p (price N Q n) v) ?_ ?_ ?_ x n t hQ ht v hs <;> clear hs v ht
  · intro A y n t _ v _
    exact ret_bound p N hN uniform I a pick y Q n v
  · intro A o k n t ih ht v hs
    apply at_local p I a pick o k v _ (price_nn N Q n)
    intro b c
    exact ih b ht _ (kraus_sparse I o b c v t hs)
  · intro A U l k n t ih ht v hs
    exact query_bound p N hN uniform I a pick l k Q n t ih ht v hs

include hN uniform in
theorem pure_mean {A : QReg} (x : Prog A) (q : ℕ) (hx : QueryBounded x q) (u : Vec A) :
    (∑ h : Full, (Fintype.card Full : ℝ)⁻¹ * Purify.pv I (project a h) x
      (fun t => reports p (pick t.2) h) u) ≤ 16*((q:ℝ)+1)^3/N * ‖u‖^2 := by
  have hh := native_bound p N hN uniform I a pick x q q 0 hx (by omega) (initialState u) (initial_sparse u)
  unfold score sumPV decodedWorld potential price bad total at hh
  simp only [initial_pv,initial_bad,initial_mass] at hh
  exact hh.trans (initial_numeric q N hN _ (sq_nonneg _))

end Reduction.Compression.Recording.Compile
#print axioms Reduction.Compression.Recording.Compile.native_bound

#print axioms Reduction.Compression.Recording.Compile.pure_mean
