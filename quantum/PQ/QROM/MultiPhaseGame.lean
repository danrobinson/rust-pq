import PQ.QROM.MultiPhase
import PQ.QROM.TwoPhaseGame
import PQ.QROM.Product

/-!
# Multi-phase reprogramming at fresh randomizers, in the QROM

The setting of games in which a challenger hands out fresh uniform *randomizers* `R₀, R₁, …`
one at a time, on classical requests of the adversary, while the adversary has quantum access to
a uniformly random function `H : K × M → Y` keyed by a randomizer (VCVio's ITSR game is the
instance treated in `PQ/QROM/ExactItsr.lean`).

## Model

* **Hash.** `H : K × M → Y` uniformly random; quantum access throughout.
* **Adversary.** An interactive adversary `x : IAdv L (qromSpec (K × M) Y) Req K Out s A`
  (`PQ/QROM/TwoPhaseAdv.lean`): quantum segments over the SINGLE-port signature, separated by at
  most `s` classical requests `req : Req`; each request is answered with a randomizer in `K`;
  the quantum register is kept across requests.  At most `q` quantum queries in total on every
  path (`IAdv.IsQueryBound s x fun _ ↦ q`), split between the phases in any adaptive way.
* **Challenger.** `rndCh Rs`: its state is the transcript `t : List Req` of the requests made so
  far; the `i`-th request (`i = t.length`) is answered with `Rs i`, where `Rs : Fin s → K` is
  uniform (pre-sampled, i.e. averaged outside; this is the same as sampling `Rs i` when the
  `i`-th request arrives, because the challenger uses `Rs i` only then).
* **Experiment.** `mpExp`: the uniform average over `Rs` and `H` of the Born probability
  (`qprob`) that the single-port flattening `IAdv.flat (rndCh Rs)` of the adversary, run against
  the oracle unitary of `H`, ends in a leaf satisfying `win Rs H`.  The leaf carries the output
  and the final transcript.  The winning condition is arbitrary.

## Phase discipline

For the proof the same run is written over the signature `qromNSpec (List Req) (K × M) Y` with
one port per transcript: the calls of the segment executed after the requests `t` go to port `t`
(`IAdv.pflat`, `mpComp`).  With every port answered by `H` this is the same run
(`mpExp_eq`).  The adversary is port-agnostic; the retargeting is done by the game.

## Result

`mp_reprogram`: `√mpExp ≤ √mpHybExp + 2 q √(s / |K|)` (and conversely, `mp_reprogram'`), where
in the hybrid experiment `mpHybExp` the function is built from two independent uniform
functions (`Φ : (K × M) × Bool → Y`): the segment after `i` requests sees `Φ (·, true)` on the
rows of the randomizers `R₀ … R_{i-1}` issued so far and `Φ (·, false)` on all other rows
(`mpFn Rs Φ i`).  In particular the row of a randomizer is fresh (independent of everything the
adversary has seen) at the moment the randomizer is issued.  The winning condition is evaluated
with the final function `mpFn Rs Φ s` (all `s` rows reprogrammed) in both experiments.

Proof: the square-root hybrid bound between the two families of port functions; the families
differ at port `t` only on the rows of the not-yet-issued randomizers `R_j`, `j ≥ |t|`; the
query masses of port `t` do not depend on these randomizers (`mpMass_update`, from the locality
lemma `pflat_queryWeight_congr`), which are uniform: the expected mass on their rows is at most
`(s / |K|) ·` (total mass) `≤ s q / |K|`.

The term `2 q √(s/|K|)` (i.e. an additive `≈ 4 q √(s/|K|)`, or `4 q² s/|K|` after squaring) is
what this hybrid argument gives.  It is weak for a large number `s` of randomizers: with
`|K| = 2^128` it is vacuous for `s = 2^64`, `q ≥ 2^32`, and about `2^-26` for `s = 2^20`,
`q = 2^40`.  Whether the true distance is smaller is not analysed here.
-/

open MeasureTheory ENNReal Quantum Matrix
open scoped Kronecker ComplexOrder

universe u v w w₂ w₃

namespace PQ.QROM

/-! ## Averages: auxiliary facts -/

section AvgAux

variable {T : Type} [Fintype T]

theorem avg_finset_sum {ι : Type} (S : Finset ι) (f : T → ι → ℝ≥0∞) :
    avg (fun t ↦ ∑ i ∈ S, f t i) = ∑ i ∈ S, avg fun t ↦ f t i := by
  unfold avg
  simp only [Finset.mul_sum]
  exact Finset.sum_comm

theorem avg_add (f g : T → ℝ≥0∞) : avg (fun t ↦ f t + g t) = avg f + avg g := by
  unfold avg
  simp only [mul_add, Finset.sum_add_distrib]

theorem avg_const [Nonempty T] (c : ℝ≥0∞) : avg (fun _ : T ↦ c) = c := by
  unfold avg
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
    ENNReal.mul_inv_cancel (by simp) (ENNReal.natCast_ne_top _), one_mul]

/-- Selecting, pointwise, one of two independent uniform functions gives a uniform function. -/
theorem avg_select {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y]
    (b : X → Bool) (g : (X → Y) → ℝ≥0∞) :
    avg g = avg fun Φ : X × Bool → Y ↦ g fun z ↦ Φ (z, b z) := by
  let e : (X × Bool → Y) ≃ (X → Y) × (X → Y) :=
    { toFun := fun Φ ↦ (fun z ↦ Φ (z, b z), fun z ↦ Φ (z, !b z))
      invFun := fun fg y ↦ if y.2 = b y.1 then fg.1 y.1 else fg.2 y.1
      left_inv := fun Φ ↦ by
        funext ⟨z, c⟩
        by_cases h : c = b z
        · simp [h]
        · have hc : c = !b z := by
            cases c <;> cases hb : b z <;> simp_all
          simp [hc]
      right_inv := fun fg ↦ by
        refine Prod.ext (funext fun z ↦ ?_) (funext fun z ↦ ?_) <;> simp }
  have hsum : ∑ Φ : X × Bool → Y, g (fun z ↦ Φ (z, b z)) =
      (Fintype.card (X → Y) : ℝ≥0∞) * ∑ f : X → Y, g f := by
    rw [← Equiv.sum_comp e.symm, Fintype.sum_prod_type]
    have : ∀ (f h : X → Y), (fun z ↦ e.symm (f, h) (z, b z)) = f := fun f h ↦ by
      funext z
      simp [e]
    simp only [this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [Finset.mul_sum]
  have hcard : (Fintype.card (X × Bool → Y) : ℝ≥0∞) =
      (Fintype.card (X → Y) : ℝ≥0∞) * (Fintype.card (X → Y) : ℝ≥0∞) := by
    rw [Fintype.card_congr e, Fintype.card_prod]
    push_cast
    rfl
  have h0 : (Fintype.card (X → Y) : ℝ≥0∞) ≠ 0 := by
    simp [Fintype.card_ne_zero]
  have ht : (Fintype.card (X → Y) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  unfold avg
  rw [← Finset.mul_sum, ← Finset.mul_sum, hsum, hcard, ENNReal.mul_inv (Or.inl h0) (Or.inl ht),
    mul_assoc, ← mul_assoc _ (Fintype.card (X → Y) : ℝ≥0∞), ENNReal.inv_mul_cancel h0 ht,
    one_mul]

/-- Averaging the indicator of the value of one coordinate against a function that does not
depend on this coordinate. -/
theorem avg_coord_eq {ι K : Type} [Fintype ι] [DecidableEq ι] [Fintype K] [DecidableEq K]
    (j : ι) (k : K) (f : (ι → K) → ℝ≥0∞)
    (hf : ∀ Rs r, f (Function.update Rs j r) = f Rs) :
    avg (fun Rs : ι → K ↦ if Rs j = k then f Rs else 0) =
      (Fintype.card K : ℝ≥0∞)⁻¹ * avg f := by
  have : Nonempty K := ⟨k⟩
  have h := sum_coord_change j (fun _ : K ↦ ()) (fun _ : K ↦ ())
    (fun r ↦ if r = k then (1 : ℝ≥0∞) else 0) (fun _ ↦ (Fintype.card K : ℝ≥0∞)⁻¹)
    (by
      intro z
      simp only [Finset.filter_true_of_mem, Finset.mem_univ, implies_true,
        Finset.sum_ite_eq', ite_true, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      exact (ENNReal.mul_inv_cancel (by simp) (ENNReal.natCast_ne_top _)).symm)
    (fun _ Rs ↦ f Rs) (fun _ Rs t ↦ hf Rs t)
  unfold avg
  calc ∑ Rs : ι → K, (Fintype.card (ι → K) : ℝ≥0∞)⁻¹ * (if Rs j = k then f Rs else 0)
      = (Fintype.card (ι → K) : ℝ≥0∞)⁻¹ *
          ∑ Rs : ι → K, (if Rs j = k then (1 : ℝ≥0∞) else 0) * f Rs := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun Rs _ ↦ ?_
        split_ifs <;> simp
    _ = (Fintype.card (ι → K) : ℝ≥0∞)⁻¹ *
          ∑ Rs : ι → K, (Fintype.card K : ℝ≥0∞)⁻¹ * f Rs := by rw [h]
    _ = _ := by
        rw [Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun Rs _ ↦ mul_left_comm _ _ _

end AvgAux

/-! ## The run over transcript ports is the single-port run -/

section Bridge

variable {P X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
  {L : LocalSig.{u, v}} {W : QReg → Type w} {W₂ : QReg → Type w₂} {A : QReg}
  {Req Resp St : Type} {Out : QReg → Type w}

theorem run_retarget_bind_eq (I : L.Interp) (H : X → Y) (p : P)
    (seg : QuantumComp L (qromSpec X Y) W A)
    (k : ∀ u, W u → QuantumComp L (qromSpec X Y) W₂ u)
    (k' : ∀ u, W u → QuantumComp L (qromNSpec P X Y) W₂ u)
    (h : ∀ u y, (nRuntime fun _ : P ↦ H).run I (k' u y) =
      (additiveOracleRuntime H).run I (k u y)) :
    (nRuntime fun _ : P ↦ H).run I ((retarget p seg).bind k') =
      (additiveOracleRuntime H).run I (seg.bind k) := by
  induction seg using QuantumComp.inductionOn with
  | pure _ y => exact h _ y
  | primBind _ o k₀ ih =>
    rw [retarget_primBind, QuantumComp.primBind_bind, QuantumComp.primBind_bind,
      QuantumRuntime.run_primBind, QuantumRuntime.run_primBind]
    exact congrArg (((I o).frame (QReg.of Unit)).bind) (funext ih)
  | queryBind _ i B e k₀ ih =>
    rw [retarget_queryBind, QuantumComp.queryBind_bind, QuantumComp.queryBind_bind,
      QuantumRuntime.run_queryBind, QuantumRuntime.run_queryBind]
    exact congrArg (DSubInstrument.bind ((additiveOracleRuntime H).queryStep i B e)) (funext ih)

/-- With every port answered by the same function, the phase-retargeted run is the single-port
run. -/
theorem pflat_run_eq_flat (I : L.Interp) (H : X → Y) (ch : Req → St → Resp × St) (n : ℕ)
    {A : QReg} (s : St) (x : IAdv L (qromSpec X Y) Req Resp Out n A) :
    (nRuntime fun _ : St ↦ H).run I (IAdv.pflat ch n s x) =
      (additiveOracleRuntime H).run I
        (IAdv.flat ch (IAdv.stop (L := L) (spec := qromSpec X Y)) n s x) := by
  induction n generalizing A s with
  | zero => exact run_retarget_bind_eq (W := Out) I H s x _ _ fun u y ↦ rfl
  | succ n ih =>
    refine run_retarget_bind_eq
      (W := fun u ↦ Out u ⊕ (Req × (Resp → IAdv L (qromSpec X Y) Req Resp Out n u)))
      I H s x _ _ fun u y ↦ ?_
    cases y with
    | inl o => rfl
    | inr rc => exact ih _ _

/-- The Born probability of an event of the single-port run, as a leaf probability of the
phase-retargeted run with every port answered by `H`. -/
theorem qprob_flat_eq (I : L.Interp) (H : X → Y) (ch : Req → St → Resp × St) (n : ℕ)
    (s : St) (x : IAdv L (qromSpec X Y) Req Resp Out n A) (ρ : SubState A)
    (E : (Σ u, Out u × St) → Prop) :
    qprob I H (IAdv.flat ch (IAdv.stop (L := L) (spec := qromSpec X Y)) n s x) ρ E =
      leafProb (nRuntime fun _ : St ↦ H) I (IAdv.pflat ch n s x) (joint ρ) E := by
  unfold qprob
  rw [evalDistMap_eq_leafProb]
  unfold leafProb
  rw [pflat_run_eq_flat]
  rfl

end Bridge

/-! ## The randomizer challenger -/

section Chal

variable {K Req : Type} {s : ℕ}

/-- The `j`-th randomizer.  (Beyond `s` an arbitrary value: an adversary with at most `s`
requests never receives it.) -/
noncomputable def rndAt [Nonempty K] (Rs : Fin s → K) (j : ℕ) : K :=
  if h : j < s then Rs ⟨j, h⟩ else Classical.arbitrary K

/-- The challenger that answers the `i`-th request with the randomizer `Rs i` and records the
request.  Its state is the transcript of the requests so far. -/
noncomputable def rndCh [Nonempty K] (Rs : Fin s → K) : Req → List Req → K × List Req :=
  fun req t ↦ (rndAt Rs t.length, t ++ [req])

theorem rndCh_step [Nonempty K] (Rs : Fin s → K) (req : Req) (t t' : List Req)
    (h : (rndCh Rs req t).2 <+: t') : t <+: t' :=
  (List.prefix_append t [req]).trans h

theorem rndAt_update [Nonempty K] [DecidableEq (Fin s)] (Rs : Fin s → K) (j : Fin s) (r : K)
    {i : ℕ} (hi : i ≠ j.1) : rndAt (Function.update Rs j r) i = rndAt Rs i := by
  unfold rndAt
  split_ifs with h
  · exact Function.update_of_ne (fun heq ↦ hi (by rw [← heq])) _ _
  · rfl

/-- The randomizer `r` is among the first `m` randomizers. -/
def issued (Rs : Fin s → K) (m : ℕ) (r : K) : Prop := ∃ j : Fin s, j.1 < m ∧ Rs j = r

instance [DecidableEq K] (Rs : Fin s → K) (m : ℕ) (r : K) : Decidable (issued Rs m r) := by
  unfold issued; infer_instance

theorem issued_update [DecidableEq K] (Rs : Fin s → K) (j : Fin s) (r r' : K) {m : ℕ}
    (hm : m ≤ j.1) : issued (Function.update Rs j r') m r ↔ issued Rs m r := by
  unfold issued
  refine exists_congr fun i ↦ and_congr_right fun hi ↦ ?_
  have : i ≠ j := fun h ↦ by rw [h] at hi; omega
  rw [Function.update_of_ne this]

variable {M Y : Type}

/-- The function after `m` randomizers have been issued, built from two functions
`Φ (·, false)` and `Φ (·, true)`: the rows of the first `m` randomizers are those of
`Φ (·, true)`, all other rows those of `Φ (·, false)`. -/
def mpFn [DecidableEq K] (Rs : Fin s → K) (Φ : (K × M) × Bool → Y) (m : ℕ) : K × M → Y :=
  fun z ↦ Φ (z, decide (issued Rs m z.1))

theorem mpFn_update [DecidableEq K] (Rs : Fin s → K) (Φ : (K × M) × Bool → Y) (j : Fin s)
    (r : K) {m : ℕ} (hm : m ≤ j.1) : mpFn (Function.update Rs j r) Φ m = mpFn Rs Φ m := by
  funext z
  unfold mpFn
  simp only [issued_update Rs j z.1 r hm]

/-- Where the final function and the function after `m` randomizers differ, the row is that of
a randomizer that has not been issued yet. -/
theorem mpFn_ne [DecidableEq K] {Rs : Fin s → K} {Φ : (K × M) × Bool → Y} {m : ℕ} {z : K × M}
    (h : mpFn Rs Φ s z ≠ mpFn Rs Φ m z) : ∃ j : Fin s, m ≤ j.1 ∧ Rs j = z.1 := by
  by_contra hne
  push Not at hne
  refine h ?_
  unfold mpFn
  have : issued Rs s z.1 ↔ issued Rs m z.1 := by
    constructor
    · rintro ⟨j, _, hj⟩
      by_contra hni
      refine hne j ?_ hj
      by_contra hlt
      exact hni ⟨j, by omega, hj⟩
    · rintro ⟨j, _, hj⟩
      exact ⟨j, j.2, hj⟩
  simp only [this]

end Chal

/-! ## The game -/

section Game

variable {K M Y Req : Type} [Fintype K] [DecidableEq K] [Nonempty K] [Fintype M] [DecidableEq M]
  [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
  {L : LocalSig.{u, v}} {Out : QReg → Type w} {A : QReg}

variable (I : L.Interp) (ρ : SubState A) (s : ℕ)
  (x : IAdv L (qromSpec (K × M) Y) Req K Out s A)
  (win : (Fin s → K) → (K × M → Y) → (Σ u, Out u × List Req) → Prop)

/-- The whole run as one program over transcript ports: the adversary against the randomizer
challenger, the calls of the segment after the requests `t` sent to port `t`. -/
noncomputable def mpComp (Rs : Fin s → K) :
    QuantumComp L (qromNSpec (List Req) (K × M) Y) (fun u ↦ Out u × List Req) A :=
  IAdv.pflat (rndCh Rs) s [] x

/-- **The experiment**: `Rs` and `H` uniform; the adversary (single-port program) runs against
the randomizer challenger with quantum access to `H`. -/
noncomputable def mpExp : ℝ≥0∞ :=
  avg fun Rs : Fin s → K ↦ avg fun H : K × M → Y ↦
    qprob I H (IAdv.flat (rndCh Rs) (IAdv.stop (L := L) (spec := qromSpec (K × M) Y)) s [] x) ρ
      (win Rs H)

/-- The experiment, over transcript ports all answered by `H`. -/
theorem mpExp_eq : mpExp I ρ s x win =
    avg fun Rs : Fin s → K ↦ avg fun H : K × M → Y ↦
      leafProb (nRuntime fun _ ↦ H) I (mpComp s x Rs) (joint ρ) (win Rs H) :=
  avg_congr fun Rs ↦ avg_congr fun H ↦ qprob_flat_eq I H (rndCh Rs) s [] x ρ (win Rs H)

/-- **The hybrid experiment**: `Rs` and `Φ` uniform; the segment after the requests `t` has
quantum access to `mpFn Rs Φ t.length`; the winning condition is evaluated with the final
function `mpFn Rs Φ s`. -/
noncomputable def mpHybExp : ℝ≥0∞ :=
  avg fun Rs : Fin s → K ↦ avg fun Φ : (K × M) × Bool → Y ↦
    leafProb (nRuntime fun t : List Req ↦ mpFn Rs Φ t.length) I (mpComp s x Rs) (joint ρ)
      (win Rs (mpFn Rs Φ s))

/-- The experiment with the function written as the final function of the hybrid. -/
theorem mpExp_eq' [Nonempty Y] : mpExp I ρ s x win =
    avg fun Rs : Fin s → K ↦ avg fun Φ : (K × M) × Bool → Y ↦
      leafProb (nRuntime fun _ ↦ mpFn Rs Φ s) I (mpComp s x Rs) (joint ρ)
        (win Rs (mpFn Rs Φ s)) := by
  rw [mpExp_eq]
  exact avg_congr fun Rs ↦ avg_select (fun z : K × M ↦ decide (issued Rs s z.1)) _

/-- Mass of the hybrid run on the pair `c` of a transcript port and a query input. -/
noncomputable def mpMass (Rs : Fin s → K) (Φ : (K × M) × Bool → Y)
    (c : Σ _ : List Req, K × M) : ℝ≥0∞ :=
  massN I (fun t : List Req ↦ mpFn Rs Φ t.length) (mpComp s x Rs) (joint ρ) c

variable {I ρ s x win} {q : ℕ}

omit [AddCommGroup Y] in
theorem mpComp_isTotalBound (hx : IAdv.IsQueryBound s x (fun _ ↦ q)) (Rs : Fin s → K) :
    IsTotalBound (mpComp s x Rs) q :=
  IAdv.pflat_isTotalBound (rndCh Rs) [] hx

theorem tsum_mpMass_le (hx : IAdv.IsQueryBound s x (fun _ ↦ q)) (Rs : Fin s → K)
    (Φ : (K × M) × Bool → Y) : ∑' c, mpMass I ρ s x Rs Φ c ≤ q :=
  (tsum_massN_le I _ (joint_posSemidef ρ) (mpComp_isTotalBound hx Rs)).trans
    ((mul_le_mul' le_rfl (ofReal_trace_joint_le_one ρ)).trans (mul_one _).le)

/-- **The masses of a port do not depend on the randomizers that are not issued yet.** -/
theorem mpMass_update (Rs : Fin s → K) (Φ : (K × M) × Bool → Y) (j : Fin s) (r : K)
    (c : Σ _ : List Req, K × M) (hc : c.1.length ≤ j.1) :
    mpMass I ρ s x (Function.update Rs j r) Φ c = mpMass I ρ s x Rs Φ c := by
  classical
  unfold mpMass massN QuantumRuntime.indexMass QuantumRuntime.indexMassAt mpComp
  refine tsum_congr fun i ↦ ?_
  refine pflat_queryWeight_congr I (D := QReg.of Unit) (σ₁ := SubState.basis ())
    (σ₂ := SubState.basis ())
    (s₁ := fun t : List Req ↦ (oracleQuery (mpFn (Function.update Rs j r) Φ t.length)).frame Unit)
    (s₂ := fun t : List Req ↦ (oracleQuery (mpFn Rs Φ t.length)).frame Unit)
    (rndCh (Function.update Rs j r)) (rndCh Rs) (fun p t ↦ p <+: t)
    (fun req t t' ↦ rndCh_step _ req t t') (fun req t t' ↦ rndCh_step _ req t t') c.1
    (fun req t ↦ ?_) (fun p hp ↦ ?_) (fun p hp σ ↦ ?_) s [] x _ i
  · by_cases ht : t.length = j.1
    · right
      have hlen : ¬ (t ++ [req]) <+: c.1 := fun h ↦ by
        have := h.length_le
        simp at this
        omega
      exact ⟨hlen, hlen⟩
    · left
      unfold rndCh
      rw [rndAt_update Rs j r ht]
  · have hle : p.length ≤ j.1 := hp.length_le.trans hc
    simp only [mpFn_update Rs Φ j r hle]
  · have hne : p ≠ c.1 := fun h ↦ hp (h ▸ List.prefix_refl _)
    have : ∀ k : K × M, (⟨p, k⟩ : Σ _ : List Req, K × M) ≠ c := fun k h ↦ hne (by rw [← h])
    simp [this]

/-- The masses on the pairs where the real and the hybrid port functions differ. -/
theorem mp_diffMass_le (Rs : Fin s → K) (Φ : (K × M) × Bool → Y) :
    diffMass I (fun _ ↦ mpFn Rs Φ s) (fun t : List Req ↦ mpFn Rs Φ t.length) (mpComp s x Rs)
        (joint ρ) ≤
      ∑ j : Fin s, ∑' c : Σ _ : List Req, K × M,
        if c.1.length ≤ j.1 then (if Rs j = c.2.1 then mpMass I ρ s x Rs Φ c else 0) else 0 := by
  unfold diffMass
  rw [← Summable.tsum_finsetSum fun _ _ ↦ CompleteLattice.summable]
  refine tsum_le_tsum fun c ↦ ?_
  split_ifs with h
  · obtain ⟨j, hj, hR⟩ := mpFn_ne h
    refine le_trans ?_ (Finset.single_le_sum (fun _ _ ↦ zero_le) (Finset.mem_univ j))
    simp only [hj, hR, ↓reduceIte]
    rfl
  · exact zero_le

/-- The averaged mass term of the reprogramming step. -/
theorem avg_mp_mass_le (hx : IAdv.IsQueryBound s x (fun _ ↦ q)) :
    (avg fun Rs : Fin s → K ↦ avg fun Φ : (K × M) × Bool → Y ↦
      4 * (q : ℝ≥0∞) * diffMass I (fun _ ↦ mpFn Rs Φ s)
        (fun t : List Req ↦ mpFn Rs Φ t.length) (mpComp s x Rs) (joint ρ)) ^ (2⁻¹ : ℝ) ≤
      2 * q * ((s : ℝ≥0∞) * (Fintype.card K : ℝ≥0∞)⁻¹) ^ (2⁻¹ : ℝ) := by
  rw [← sqrt_four_mul]
  refine sqrt_le_sqrt ?_
  simp only [avg_mul_left]
  refine mul_le_mul' le_rfl ?_
  refine (avg_mono fun Rs ↦ avg_mono fun Φ ↦ mp_diffMass_le Rs Φ).trans ?_
  rw [avg_comm]
  refine avg_le fun Φ ↦ ?_
  rw [avg_finset_sum]
  have hj : ∀ j : Fin s, (avg fun Rs : Fin s → K ↦ ∑' c : Σ _ : List Req, K × M,
      if c.1.length ≤ j.1 then (if Rs j = c.2.1 then mpMass I ρ s x Rs Φ c else 0) else 0) ≤
      (Fintype.card K : ℝ≥0∞)⁻¹ * q := by
    intro j
    rw [avg_tsum]
    have hc : ∀ c : Σ _ : List Req, K × M,
        (avg fun Rs : Fin s → K ↦
          if c.1.length ≤ j.1 then (if Rs j = c.2.1 then mpMass I ρ s x Rs Φ c else 0) else 0) ≤
        (Fintype.card K : ℝ≥0∞)⁻¹ * avg fun Rs : Fin s → K ↦ mpMass I ρ s x Rs Φ c := by
      intro c
      by_cases hlen : c.1.length ≤ j.1
      · simp only [hlen, ↓reduceIte]
        exact (avg_coord_eq j c.2.1 (fun Rs ↦ mpMass I ρ s x Rs Φ c)
          fun Rs r ↦ mpMass_update Rs Φ j r c hlen).le
      · simp only [hlen, ↓reduceIte]
        exact (avg_le (c := 0) fun _ ↦ le_rfl).trans zero_le
    refine (tsum_le_tsum hc).trans ?_
    rw [ENNReal.tsum_mul_left, ← avg_tsum]
    exact mul_le_mul' le_rfl (avg_le fun Rs ↦ tsum_mpMass_le hx Rs Φ)
  refine (Finset.sum_le_sum fun j _ ↦ hj j).trans ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_assoc]

/-- **Multi-phase reprogramming at fresh randomizers.**  For an interactive adversary making at
most `q` quantum queries in total and at most `s` requests, each answered with a fresh uniform
randomizer, and for every winning condition:
`√(real) ≤ √(hybrid) + 2 q √(s / |K|)`, where in the hybrid experiment the rows of the
randomizers that are not issued yet are independent of what the adversary sees. -/
theorem mp_reprogram [Nonempty Y] (hx : IAdv.IsQueryBound s x (fun _ ↦ q)) :
    mpExp I ρ s x win ^ (2⁻¹ : ℝ) ≤
      mpHybExp I ρ s x win ^ (2⁻¹ : ℝ) +
        2 * q * ((s : ℝ≥0∞) * (Fintype.card K : ℝ≥0∞)⁻¹) ^ (2⁻¹ : ℝ) := by
  rw [mpExp_eq']
  exact (sqrt_avg_le _ _ _ fun Rs ↦ sqrt_avg_le _ _ _ fun Φ ↦
    (nRuntime_sqrt_le I (fun _ ↦ mpFn Rs Φ s) (fun t : List Req ↦ mpFn Rs Φ t.length)
      (joint_posSemidef ρ) (mpComp_isTotalBound hx Rs) (win Rs (mpFn Rs Φ s))).1).trans
    (add_le_add le_rfl (avg_mp_mass_le hx))

/-- **Multi-phase reprogramming, converse direction**:
`√(hybrid) ≤ √(real) + 2 q √(s / |K|)`. -/
theorem mp_reprogram' [Nonempty Y] (hx : IAdv.IsQueryBound s x (fun _ ↦ q)) :
    mpHybExp I ρ s x win ^ (2⁻¹ : ℝ) ≤
      mpExp I ρ s x win ^ (2⁻¹ : ℝ) +
        2 * q * ((s : ℝ≥0∞) * (Fintype.card K : ℝ≥0∞)⁻¹) ^ (2⁻¹ : ℝ) := by
  rw [mpExp_eq']
  exact (sqrt_avg_le _ _ _ fun Rs ↦ sqrt_avg_le _ _ _ fun Φ ↦
    (nRuntime_sqrt_le I (fun _ ↦ mpFn Rs Φ s) (fun t : List Req ↦ mpFn Rs Φ t.length)
      (joint_posSemidef ρ) (mpComp_isTotalBound hx Rs) (win Rs (mpFn Rs Φ s))).2).trans
    (add_le_add le_rfl (avg_mp_mass_le hx))

end Game

end PQ.QROM

#print axioms PQ.QROM.mpExp_eq
#print axioms PQ.QROM.mp_reprogram
#print axioms PQ.QROM.mp_reprogram'
