import PQ.QROM.ExactUdTightTwoPort
import PQ.QROM.ExactUdClosed
import PQ.QROM.MultiPhaseGame
import PQ.QROM.ExactPrfTight

/-!
# The exact SM-DT-UD game in the QROM: tight bound without seed hiding

For the adaptive two-phase SM-DT-UD game of `PQ/QROM/ExactUd.lean` (the EXISTING definitions
`udReal`, `udIdeal`: two-port runtime, phase 1 with at most `q₁` quantum queries and `n`
classical requests, phase 2 — which is given the seed — with at most `q₂` quantum queries):

`ud_exact_tight : |udReal.toReal − udIdeal.toReal| ≤ (16 (q₁ + q₂)² + 2 n) / |Msg|`,

with no `1/√|Sd|` seed-hiding term and independently of the number of targets
(`ud_exact_tight_real_le_ideal_add`, `ud_exact_tight_ideal_le_real_add`: one-sided, `ℝ≥0∞`).
Compare `ud_exact_real_le_ideal_add` (`PQ/QROM/ExactUdClosed.lean`):
`4 q₂ / √|Msg| + 8 q₁ / √|Sd|`.

## Proof

The hidden data are the planted messages `xs`, which are never revealed.  Fix the seed `P`.
Worlds `(xs, ys, Th)` uniform; `Th' = udRepP P xs ys Th` is `Th` reprogrammed to `ys t` at the
planted points `(P, t, xs t)`.  By the change of variables `avg_udRepP`, the real world is: oracle
`Th'`, challenge answers `ys`, collection answers from the row of `Th'`.

* **Middle world**: oracle `Th'`, challenge answers `ys`, collection answers from the row of
  `Th`.  Its program is the program of the ideal world (determined by the view `(ys, Th)`), and
  the oracles differ only at the planted points, each hidden with probability `1/|Msg|` given
  the view: `ud_mid_ideal_tight`, `|mid − ideal| ≤ 8 (q₁+q₂)² / |Msg|`, by the tight hidden-set
  bound for two-port programs (`leafProb2_tightAvgBound`, `PQ/QROM/ExactUdTightTwoPort.lean`).
* **Real vs middle**: by leaf locality (`udProg_branch_congr`) the two runs have the same
  post-state at every leaf whose collection history contains no planted point
  (`udLP_real_le_mid_add`, `udLP_mid_le_real_add`); so they differ by at most the probability of
  the bad event `udBad` in the real, resp. middle, world.
* **Bad event, real world** (`avg_udLP_bad_le`): at most `n / |Msg|`, classically — collection
  requests are only accepted on non-target tweaks, whose planted messages are independent of the
  leaf (`avg_bad_le`).
* **Bad event, middle world** (`avg_udLP_mid_bad_le`): at most `(2 n + 8 (q₁+q₂)²) / |Msg|`, by
  the square-root hybrid for the two-port runtime with a world-dependent event, from the ideal
  world, where the bad event again has probability at most `n / |Msg|`.
-/

open MeasureTheory ENNReal Quantum Matrix
open PQ.QROM.Tight
open scoped Kronecker ComplexOrder

universe u v u₁ v₁ w w₂

set_option linter.unusedSectionVars false

namespace PQ.QROM

/-! ## Locality for runs with a state-recording continuation -/

section LocalityK

variable {L : LocalSig.{u, v}} {spec : QuantumOracleSpec.{u₁, v₁}} {Req Resp : Type}
  {Out : QReg → Type w} {St Res : Type} (R : QuantumRuntime spec) (I : L.Interp)

/-- A continuation records the challenger state: its leaves carry the state it was started
with. -/
def RecordsState (K : ∀ u, Out u → St → QuantumComp L spec (fun _ ↦ Res × St) u) : Prop :=
  ∀ (u : QReg) (o : Out u) (s : St) (c : Σ _ : QReg, Res × St), c.2.2 ≠ s →
    (R.run I (K u o s)).branch c = 0

theorem flatK_branch_eq_zero (ch : Req → St → Resp × St)
    {K : ∀ u, Out u → St → QuantumComp L spec (fun _ ↦ Res × St) u} (hK : RecordsState R I K)
    (ext : St → St → Prop) (hrefl : ∀ s, ext s s)
    (hstep : ∀ req s t, ext (ch req s).2 t → ext s t)
    (n : ℕ) {A : QReg} (s : St) (x : IAdv L spec Req Resp Out n A) (c : Σ _ : QReg, Res × St)
    (h : ¬ ext s c.2.2) : (R.run I (IAdv.flat ch K n s x)).branch c = 0 := by
  induction n generalizing A s with
  | zero =>
    refine run_bind_branch_eq_zero R I (W := Out) x _ _ fun p ↦ ?_
    exact hK _ _ _ c fun heq ↦ h (heq ▸ hrefl _)
  | succ n ih =>
    refine run_bind_branch_eq_zero R I
      (W := fun u ↦ Out u ⊕ (Req × (Resp → IAdv L spec Req Resp Out n u))) x _ _ fun p ↦ ?_
    obtain ⟨u', r⟩ := p
    cases r with
    | inl o' => exact hK _ _ _ c fun heq ↦ h (heq ▸ hrefl _)
    | inr rc => exact ih _ _ fun h' ↦ h (hstep _ _ _ h')

theorem flatK_branch_congr (ch ch' : Req → St → Resp × St)
    {K : ∀ u, Out u → St → QuantumComp L spec (fun _ ↦ Res × St) u} (hK : RecordsState R I K)
    (ext : St → St → Prop) (hrefl : ∀ s, ext s s)
    (hstep : ∀ req s t, ext (ch req s).2 t → ext s t)
    (hstep' : ∀ req s t, ext (ch' req s).2 t → ext s t) (c : Σ _ : QReg, Res × St)
    (hloc : ∀ req s, ch req s = ch' req s ∨
      (¬ ext (ch req s).2 c.2.2 ∧ ¬ ext (ch' req s).2 c.2.2))
    (n : ℕ) {A : QReg} (s : St) (x : IAdv L spec Req Resp Out n A) :
    (R.run I (IAdv.flat ch K n s x)).branch c = (R.run I (IAdv.flat ch' K n s x)).branch c := by
  induction n generalizing A s with
  | zero => rfl
  | succ n ih =>
    refine run_bind_branch_congr R I
      (W := fun u ↦ Out u ⊕ (Req × (Resp → IAdv L spec Req Resp Out n u))) x _ _ _ fun p ↦ ?_
    obtain ⟨u', r⟩ := p
    cases r with
    | inl o' => rfl
    | inr rc =>
      rcases hloc rc.1 s with heq | ⟨h1, h2⟩
      · simp only [heq]
        exact ih _ _
      · simp only
        rw [flatK_branch_eq_zero R I ch hK ext hrefl hstep n _ _ c h1,
          flatK_branch_eq_zero R I ch' hK ext hrefl hstep' n _ _ c h2]

/-- A leaf whose recorded state needs more than `n` steps (measured by `μ`) is not reached. -/
theorem flatK_branch_eq_zero_of_lt (ch : Req → St → Resp × St)
    {K : ∀ u, Out u → St → QuantumComp L spec (fun _ ↦ Res × St) u} (hK : RecordsState R I K)
    (μ : St → ℕ) (hμ : ∀ req s, μ (ch req s).2 ≤ μ s + 1)
    (n : ℕ) {A : QReg} (s : St) (x : IAdv L spec Req Resp Out n A) (c : Σ _ : QReg, Res × St)
    (h : μ s + n < μ c.2.2) : (R.run I (IAdv.flat ch K n s x)).branch c = 0 := by
  induction n generalizing A s with
  | zero =>
    refine run_bind_branch_eq_zero R I (W := Out) x _ _ fun p ↦ ?_
    exact hK _ _ _ c fun heq ↦ by rw [heq] at h; omega
  | succ n ih =>
    refine run_bind_branch_eq_zero R I
      (W := fun u ↦ Out u ⊕ (Req × (Resp → IAdv L spec Req Resp Out n u))) x _ _ fun p ↦ ?_
    obtain ⟨u', r⟩ := p
    cases r with
    | inl o' => exact hK _ _ _ c fun heq ↦ by rw [heq] at h; omega
    | inr rc =>
      refine ih _ _ ?_
      have := hμ rc.1 s
      omega

end LocalityK

/-- Two programs whose branches agree outside an event `B` have probabilities differing by at
most the probability of `B`. -/
theorem leafProb_le_add_of_branch_eq {L : LocalSig.{u, v}} {spec : QuantumOracleSpec.{u₁, v₁}}
    {W : QReg → Type w} {A : QReg} (R : QuantumRuntime spec)
    (I : L.Interp) (x₁ x₂ : QuantumComp L spec W A)
    (σ : Matrix (A × R.D) (A × R.D) ℂ) (E B : (Σ u, W u) → Prop)
    (h : ∀ p, ¬ B p → (R.run I x₁).branch p σ = (R.run I x₂).branch p σ) :
    leafProb R I x₁ σ E ≤ leafProb R I x₂ σ E + leafProb R I x₁ σ B := by
  unfold leafProb
  rw [← tsum_add]
  refine tsum_le_tsum fun p ↦ ?_
  by_cases hB : B p
  · rw [ind_of_true hB, mul_one]
    exact (mul_le_mul' le_rfl (ind_le_one _)).trans ((mul_one _).le.trans le_add_self)
  · rw [h p hB]
    exact le_self_add

/-! ## The game -/

section UD

variable {Sd Tw Msg Y : Type} [Fintype Sd] [DecidableEq Sd] [Fintype Tw] [DecidableEq Tw]
  [Fintype Msg] [DecidableEq Msg] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
  {L : LocalSig.{u, v}} {Out : QReg → Type w} {A : QReg}

variable (I : L.Interp) (ρ : SubState A) (cap n : ℕ)
  (x : IAdv L (qrom2Spec (Dom Sd Tw Msg) Y) (Tw ⊕ (Tw × Msg)) (Option Y) Out n A)
  (ph2 : Sd → ∀ u, Out u → QuantumComp L (qrom2Spec (Dom Sd Tw Msg) Y) (fun _ ↦ Bool) u)

/-- The whole run (phase 1 against the challenger with challenge table `y` and collection table
`a`, then phase 2 with the seed `P`) as one program. -/
def udProg (P : Sd) (y : Tw → Y) (a : Tw × Msg → Y) :
    QuantumComp L (qrom2Spec (Dom Sd Tw Msg) Y) (fun _ ↦ Bool × PreState Tw Msg) A :=
  composite (preChT cap y a) preInit n x ph2 P

/-- Probability of a leaf event of the run with tables `y`, `a`, both phases having quantum
access to `H`. -/
noncomputable def udLP (P : Sd) (H : Dom Sd Tw Msg → Y) (y : Tw → Y) (a : Tw × Msg → Y)
    (E : (Σ _ : QReg, Bool × PreState Tw Msg) → Prop) : ℝ≥0∞ :=
  leafProb (twoRuntime fun _ ↦ H) I (udProg cap n x ph2 P y a) (joint ρ) E

/-- The output bit is `true`. -/
def udBit : (Σ _ : QReg, Bool × PreState Tw Msg) → Prop := fun p ↦ p.2.1 = true

/-- Bad event: an accepted collection request hit a planted message. -/
def udBad (xs : Tw → Msg) : (Σ _ : QReg, Bool × PreState Tw Msg) → Prop :=
  fun p ↦ ∃ tm ∈ p.2.2.coll, tm.2 = xs tm.1

/-- The targets of the real world. -/
def udTgt (P : Sd) (xs : Tw → Msg) (Th : Dom Sd Tw Msg → Y) : Tw → Y := fun t ↦ Th (P, (t, xs t))

/-- `Th` reprogrammed to `ys t` at the planted points `(P, t, xs t)`. -/
def udRepP (P : Sd) (xs : Tw → Msg) (ys : Tw → Y) (Th : Dom Sd Tw Msg → Y) : Dom Sd Tw Msg → Y :=
  fun z ↦ if z.1 = P ∧ z.2.2 = xs z.2.1 then ys z.2.1 else Th z

theorem udReal_eq : udReal I ρ cap n x ph2 =
    avg fun xs : Tw → Msg ↦ avg fun P : Sd ↦ avg fun Th : Dom Sd Tw Msg → Y ↦
      udLP I ρ cap n x ph2 P Th (udTgt P xs Th) (rowOf Th P) udBit := rfl

theorem udIdeal_eq : udIdeal I ρ cap n x ph2 =
    avg fun ys : Tw → Y ↦ avg fun P : Sd ↦ avg fun Th : Dom Sd Tw Msg → Y ↦
      udLP I ρ cap n x ph2 P Th ys (rowOf Th P) udBit := rfl

theorem recordsState_phase2K (R : QuantumRuntime (qrom2Spec (Dom Sd Tw Msg) Y)) (P : Sd) :
    RecordsState (St := PreState Tw Msg) R I (phase2K ph2 P) := by
  intro u o s c hc
  unfold phase2K
  refine run_bind_branch_eq_zero R I (W := fun _ ↦ Bool) (ph2 P u o) _ _ fun p ↦ ?_
  rw [QuantumRuntime.run_pure]
  refine DSubInstrument.branch_ret_of_ne _ fun heq ↦ hc ?_
  cases heq
  rfl

/-- **Locality**: the post-state of a leaf only depends on the challenge table at its target
tweaks and on the collection table at its collection queries. -/
theorem udProg_branch_congr (R : QuantumRuntime (qrom2Spec (Dom Sd Tw Msg) Y)) (P : Sd)
    (y y' : Tw → Y) (a a' : Tw × Msg → Y) (c : Σ _ : QReg, Bool × PreState Tw Msg)
    (hy : ∀ tw ∈ c.2.2.chal, y tw = y' tw) (ha : ∀ tm ∈ c.2.2.coll, a tm = a' tm) :
    (R.run I (udProg cap n x ph2 P y a)).branch c =
      (R.run I (udProg cap n x ph2 P y' a')).branch c :=
  flatK_branch_congr R I _ _ (recordsState_phase2K I ph2 R P) PreState.Ext
    (fun _ ↦ ⟨List.prefix_refl _, List.prefix_refl _⟩)
    (fun req s t ↦ preChT_ext cap _ _ req s t) (fun req s t ↦ preChT_ext cap _ _ req s t) c
    (preChT_loc cap y y' a a' c.2.2 hy ha) n preInit x

/-- A leaf with more than `n` accepted collection queries is not reached. -/
theorem udProg_branch_eq_zero (R : QuantumRuntime (qrom2Spec (Dom Sd Tw Msg) Y)) (P : Sd)
    (y : Tw → Y) (a : Tw × Msg → Y) (c : Σ _ : QReg, Bool × PreState Tw Msg)
    (h : n < c.2.2.coll.length) : (R.run I (udProg cap n x ph2 P y a)).branch c = 0 := by
  refine flatK_branch_eq_zero_of_lt R I _ (recordsState_phase2K I ph2 R P)
    (fun s ↦ s.coll.length) (fun req s ↦ ?_) n preInit x c (by simpa [preInit] using h)
  cases req with
  | inl t =>
    simp only [preChT]
    split_ifs <;> simp
  | inr tm =>
    simp only [preChT]
    split_ifs <;> simp

variable {I ρ cap n x ph2}

/-- **Real vs middle world**, one world: identical unless a planted message was collected. -/
theorem udLP_real_le_mid_add (P : Sd) (xs : Tw → Msg) (ys : Tw → Y) (Th : Dom Sd Tw Msg → Y) :
    udLP I ρ cap n x ph2 P (udRepP P xs ys Th) ys (rowOf (udRepP P xs ys Th) P) udBit ≤
      udLP I ρ cap n x ph2 P (udRepP P xs ys Th) ys (rowOf Th P) udBit +
        udLP I ρ cap n x ph2 P (udRepP P xs ys Th) ys (rowOf (udRepP P xs ys Th) P)
          (udBad xs) := by
  refine leafProb_le_add_of_branch_eq _ I _ _ _ _ _ fun p hp ↦ ?_
  refine DFunLike.congr_fun (udProg_branch_congr I cap n x ph2 _ P ys ys _ _ p (fun _ _ ↦ rfl)
    fun tm htm ↦ ?_) _
  have hne : ¬ tm.2 = xs tm.1 := fun h ↦ hp ⟨tm, htm, h⟩
  simp [rowOf, udRepP, hne]

theorem udLP_mid_le_real_add (P : Sd) (xs : Tw → Msg) (ys : Tw → Y) (Th : Dom Sd Tw Msg → Y) :
    udLP I ρ cap n x ph2 P (udRepP P xs ys Th) ys (rowOf Th P) udBit ≤
      udLP I ρ cap n x ph2 P (udRepP P xs ys Th) ys (rowOf (udRepP P xs ys Th) P) udBit +
        udLP I ρ cap n x ph2 P (udRepP P xs ys Th) ys (rowOf Th P) (udBad xs) := by
  refine leafProb_le_add_of_branch_eq _ I _ _ _ _ _ fun p hp ↦ ?_
  refine DFunLike.congr_fun (udProg_branch_congr I cap n x ph2 _ P ys ys _ _ p (fun _ _ ↦ rfl)
    fun tm htm ↦ ?_) _
  have hne : ¬ tm.2 = xs tm.1 := fun h ↦ hp ⟨tm, htm, h⟩
  simp [rowOf, udRepP, hne]

theorem udLP_le_one (P : Sd) (H : Dom Sd Tw Msg → Y) (y : Tw → Y) (a : Tw × Msg → Y)
    (E : (Σ _ : QReg, Bool × PreState Tw Msg) → Prop) : udLP I ρ cap n x ph2 P H y a E ≤ 1 :=
  (leafProb_le _ (joint_posSemidef ρ) E).trans (ofReal_trace_joint_le_one ρ)

/-! ### The coupling -/

/-- Exchange the values at the planted points of the row `P` with `ys`. -/
def udSwapP (P : Sd) (xs : Tw → Msg) (v : (Tw → Y) × (Dom Sd Tw Msg → Y)) :
    (Tw → Y) × (Dom Sd Tw Msg → Y) :=
  (udTgt P xs v.2, udRepP P xs v.1 v.2)

theorem udTgt_udRepP (P : Sd) (xs : Tw → Msg) (ys : Tw → Y) (Th : Dom Sd Tw Msg → Y) :
    udTgt P xs (udRepP P xs ys Th) = ys := by
  funext t
  simp [udTgt, udRepP]

theorem udSwapP_involutive (P : Sd) (xs : Tw → Msg) :
    Function.Involutive (udSwapP (Y := Y) P xs) := by
  rintro ⟨ys, Th⟩
  refine Prod.ext (udTgt_udRepP P xs ys Th) (funext fun z ↦ ?_)
  obtain ⟨P', t, m⟩ := z
  by_cases h : P' = P ∧ m = xs t
  · obtain ⟨rfl, rfl⟩ := h
    simp [udSwapP, udRepP, udTgt]
  · simp [udSwapP, udRepP, h]

/-- **Change of variables.**  Reprogramming a uniform `Th` at the planted points to uniform
independent `ys` gives a uniform function whose targets are `ys`. -/
theorem avg_udRepP (P : Sd) (xs : Tw → Msg) (g : (Tw → Y) → (Dom Sd Tw Msg → Y) → ℝ≥0∞) :
    (avg fun ys : Tw → Y ↦ avg fun Th : Dom Sd Tw Msg → Y ↦ g ys (udRepP P xs ys Th)) =
      avg fun Th : Dom Sd Tw Msg → Y ↦ g (udTgt P xs Th) Th := by
  have h := Equiv.sum_comp (udSwapP_involutive (Y := Y) P xs).toPerm
    (fun v ↦ ((Fintype.card (Tw → Y) : ℝ≥0∞)⁻¹ * (Fintype.card (Dom Sd Tw Msg → Y) : ℝ≥0∞)⁻¹) *
      g (udTgt P xs v.2) v.2)
  have e1 : (avg fun ys : Tw → Y ↦ avg fun Th : Dom Sd Tw Msg → Y ↦ g ys (udRepP P xs ys Th)) =
      ∑ v : (Tw → Y) × (Dom Sd Tw Msg → Y),
        ((Fintype.card (Tw → Y) : ℝ≥0∞)⁻¹ * (Fintype.card (Dom Sd Tw Msg → Y) : ℝ≥0∞)⁻¹) *
          g (udTgt P xs (udSwapP P xs v).2) (udSwapP P xs v).2 := by
    unfold avg
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun ys _ ↦ ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun Th _ ↦ ?_
    change _ = _ * g (udTgt P xs (udRepP P xs ys Th)) (udRepP P xs ys Th)
    rw [udTgt_udRepP, mul_assoc]
  simp only [Function.Involutive.coe_toPerm] at h
  rw [e1, h, Fintype.sum_prod_type]
  have e2 : ∀ ys : Tw → Y, ∑ Th : Dom Sd Tw Msg → Y,
      ((Fintype.card (Tw → Y) : ℝ≥0∞)⁻¹ * (Fintype.card (Dom Sd Tw Msg → Y) : ℝ≥0∞)⁻¹) *
        g (udTgt P xs Th) Th =
      (Fintype.card (Tw → Y) : ℝ≥0∞)⁻¹ * avg fun Th : Dom Sd Tw Msg → Y ↦ g (udTgt P xs Th) Th :=
    fun ys ↦ by
      unfold avg
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun Th _ ↦ mul_assoc _ _ _
  rw [Finset.sum_congr rfl fun ys _ ↦ e2 ys]
  exact avg_const (T := Tw → Y) _

/-! ### The bad event is unlikely when the planted messages are not seen -/

/-- **Independence.**  If the weight of every leaf depends on the planted messages only at the
target tweaks of the leaf, and leaves with more than `n` collection queries have weight zero,
then the bad leaves carry at most an `n / |Msg|` fraction of the weight: the collection queries
are on non-target tweaks, whose planted messages are independent of the leaf. -/
theorem avg_bad_le (wt : (Tw → Msg) → (Σ _ : QReg, Bool × PreState Tw Msg) → ℝ≥0∞)
    (h1 : ∀ (xs xs' : Tw → Msg) (p : Σ _ : QReg, Bool × PreState Tw Msg),
      (∀ t ∈ p.2.2.chal, xs t = xs' t) → wt xs p = wt xs' p)
    (h2 : ∀ (xs : Tw → Msg) (p : Σ _ : QReg, Bool × PreState Tw Msg),
      n < p.2.2.coll.length → wt xs p = 0) :
    (avg fun xs : Tw → Msg ↦ ∑' p, wt xs p * ind (udBad xs p)) ≤
      (n : ℝ≥0∞) * (Fintype.card Msg : ℝ≥0∞)⁻¹ * avg fun xs : Tw → Msg ↦ ∑' p, wt xs p := by
  classical
  rw [avg_tsum, avg_tsum, ← ENNReal.tsum_mul_left]
  refine tsum_le_tsum fun p ↦ ?_
  by_cases hlen : n < p.2.2.coll.length
  · simp [h2 _ p hlen, avg]
  have hind : ∀ xs : Tw → Msg, ind (udBad xs p) ≤
      ∑ tm ∈ p.2.2.coll.toFinset, (if xs tm.1 = tm.2 then (1 : ℝ≥0∞) else 0) := by
    intro xs
    by_cases hb : udBad xs p
    · obtain ⟨tm, hmem, he⟩ := hb
      refine le_trans ?_ (Finset.single_le_sum
        (f := fun tm : Tw × Msg ↦ if xs tm.1 = tm.2 then (1 : ℝ≥0∞) else 0)
        (fun _ _ ↦ zero_le) (List.mem_toFinset.2 hmem))
      simp only [he, ite_true]
      exact ind_le_one _
    · rw [ind_of_false hb]
      exact zero_le
  calc (avg fun xs : Tw → Msg ↦ wt xs p * ind (udBad xs p))
      ≤ avg fun xs : Tw → Msg ↦ ∑ tm ∈ p.2.2.coll.toFinset,
          if xs tm.1 = tm.2 then wt xs p else 0 :=
        avg_mono fun xs ↦ (mul_le_mul' le_rfl (hind xs)).trans (le_of_eq (by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun tm _ ↦ by split_ifs <;> simp))
    _ = ∑ tm ∈ p.2.2.coll.toFinset, avg fun xs : Tw → Msg ↦
          if xs tm.1 = tm.2 then wt xs p else 0 := avg_finset_sum _ _
    _ = ∑ tm ∈ p.2.2.coll.toFinset,
          (Fintype.card Msg : ℝ≥0∞)⁻¹ * avg fun xs : Tw → Msg ↦ wt xs p :=
        Finset.sum_congr rfl fun tm htm ↦
          avg_coord_eq tm.1 tm.2 (fun xs ↦ wt xs p) fun Rs r ↦ h1 _ _ p fun t ht ↦ by
            rw [Function.update_of_ne]
            rintro rfl
            exact p.2.2.disj tm (List.mem_toFinset.1 htm) ht
    _ = (p.2.2.coll.toFinset.card : ℝ≥0∞) *
          ((Fintype.card Msg : ℝ≥0∞)⁻¹ * avg fun xs : Tw → Msg ↦ wt xs p) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (n : ℝ≥0∞) * ((Fintype.card Msg : ℝ≥0∞)⁻¹ * avg fun xs : Tw → Msg ↦ wt xs p) := by
        refine mul_le_mul' ?_ le_rfl
        have h := (List.toFinset_card_le p.2.2.coll).trans (not_lt.1 hlen)
        exact_mod_cast h
    _ = _ := by rw [mul_assoc]

/-- The bad event has probability at most `n / |Msg|` whenever the oracle and the collection
table do not depend on the planted messages and the challenge table depends on them only
through the planted messages of the target tweaks. -/
theorem avg_udLP_bad_le (P : Sd) (H : Dom Sd Tw Msg → Y) (y : (Tw → Msg) → Tw → Y)
    (a : Tw × Msg → Y) (hy : ∀ (xs xs' : Tw → Msg) (t : Tw), xs t = xs' t → y xs t = y xs' t) :
    (avg fun xs : Tw → Msg ↦ udLP I ρ cap n x ph2 P H (y xs) a (udBad xs)) ≤
      (n : ℝ≥0∞) * (Fintype.card Msg : ℝ≥0∞)⁻¹ := by
  have h := avg_bad_le (n := n)
    (fun xs p ↦ ENNReal.ofReal ((((twoRuntime fun _ ↦ H).run I
      (udProg cap n x ph2 P (y xs) a)).branch p (joint ρ)).trace.re))
    (fun xs xs' p hp ↦ by
      simp only
      rw [udProg_branch_congr I cap n x ph2 _ P (y xs) (y xs') a a p
        (fun tw htw ↦ hy xs xs' tw (hp tw htw)) (fun _ _ ↦ rfl)])
    (fun xs p hp ↦ by
      simp only
      rw [udProg_branch_eq_zero I cap n x ph2 _ P (y xs) a p hp]
      simp)
  refine h.trans ?_
  refine (mul_le_mul' le_rfl (avg_le fun xs ↦ ?_)).trans (mul_one _).le
  exact (tsum_leaf_le _ (joint_posSemidef ρ)).trans (ofReal_trace_joint_le_one ρ)

/-! ### The bad event in the middle world -/

theorem le_two_mul_add_of_sqrt_le {a b c : ℝ≥0∞}
    (h : a ^ (2⁻¹ : ℝ) ≤ b ^ (2⁻¹ : ℝ) + c ^ (2⁻¹ : ℝ)) : a ≤ 2 * b + 2 * c := by
  have key : ∀ u v : ℝ≥0∞, u ≤ v → (u + v) ^ 2 ≤ 2 * u ^ 2 + 2 * v ^ 2 := by
    intro u v huv
    obtain ⟨t, rfl⟩ := exists_add_of_le huv
    have e : (u + (u + t)) ^ 2 + t ^ 2 = 2 * u ^ 2 + 2 * (u + t) ^ 2 := by ring
    rw [← e]
    exact le_self_add
  have h2 : (b ^ (2⁻¹ : ℝ) + c ^ (2⁻¹ : ℝ)) ^ 2 ≤ 2 * b + 2 * c := by
    rcases le_total (b ^ (2⁻¹ : ℝ)) (c ^ (2⁻¹ : ℝ)) with hbc | hbc
    · have := key _ _ hbc
      rwa [sq_sqrt, sq_sqrt] at this
    · have := key _ _ hbc
      rw [sq_sqrt, sq_sqrt] at this
      rw [add_comm (b ^ (2⁻¹ : ℝ)), add_comm (2 * b)]
      exact this
  calc a = (a ^ (2⁻¹ : ℝ)) ^ 2 := (sq_sqrt a).symm
    _ ≤ (b ^ (2⁻¹ : ℝ) + c ^ (2⁻¹ : ℝ)) ^ 2 := pow_le_pow_left' h 2
    _ ≤ _ := h2

variable {q₁ q₂ : ℕ}

theorem udProg_isQueryBound (hx : IAdv.IsQueryBound n x (firstBudget q₁))
    (h2 : ∀ P u o, (ph2 P u o).IsQueryBound (secondBudget q₂)) (P : Sd) (y : Tw → Y)
    (a : Tw × Msg → Y) :
    (udProg cap n x ph2 P y a).IsQueryBound (firstBudget q₁ + secondBudget q₂) :=
  IAdv.flat_isQueryBound _ preInit hx (phase2K_isQueryBound h2 P)

theorem budget_total (q₁ q₂ : ℕ) :
    (firstBudget q₁ + secondBudget q₂) false + (firstBudget q₁ + secondBudget q₂) true =
      q₁ + q₂ := by
  simp [firstBudget, secondBudget]

/-- **The bad event in the middle world** (oracle reprogrammed at the planted points, program of
the ideal world): square-root hybrid from the ideal world, where the planted messages are
independent of everything. -/
theorem avg_udLP_mid_bad_le [Nonempty Msg] (hx : IAdv.IsQueryBound n x (firstBudget q₁))
    (h2 : ∀ P u o, (ph2 P u o).IsQueryBound (secondBudget q₂)) (P : Sd) (ys : Tw → Y)
    (Th : Dom Sd Tw Msg → Y) :
    (avg fun xs : Tw → Msg ↦
        udLP I ρ cap n x ph2 P (udRepP P xs ys Th) ys (rowOf Th P) (udBad xs)) ≤
      2 * ((n : ℝ≥0∞) * (Fintype.card Msg : ℝ≥0∞)⁻¹) +
        2 * (4 * ((q₁ + q₂ : ℕ) : ℝ≥0∞) * ((Fintype.card Msg : ℝ≥0∞)⁻¹ *
          ((q₁ + q₂ : ℕ) : ℝ≥0∞))) := by
  classical
  have hb := udProg_isQueryBound (cap := cap) hx h2 P ys (rowOf Th P)
  set prog := udProg cap n x ph2 P ys (rowOf Th P) with hprog
  set M : Dom Sd Tw Msg → ℝ≥0∞ := fun k ↦
    mass2 I (fun _ ↦ Th) prog (joint ρ) false k + mass2 I (fun _ ↦ Th) prog (joint ρ) true k
    with hM
  have hs : ∀ xs : Tw → Msg,
      udLP I ρ cap n x ph2 P (udRepP P xs ys Th) ys (rowOf Th P) (udBad xs) ^ (2⁻¹ : ℝ) ≤
        udLP I ρ cap n x ph2 P Th ys (rowOf Th P) (udBad xs) ^ (2⁻¹ : ℝ) +
          (4 * ((q₁ + q₂ : ℕ) : ℝ≥0∞) *
            ∑ k, if k.1 = P ∧ xs k.2.1 = k.2.2 then M k else 0) ^ (2⁻¹ : ℝ) := by
    intro xs
    have h1 := twoRuntime_sqrt_le_kraus I (fun _ ↦ udRepP P xs ys Th) (fun _ ↦ Th) prog
      (joint_posSemidef ρ) (udBad xs)
    have h3 := tsum_rpow_queryWeight2_le I (fun _ ↦ udRepP P xs ys Th) (fun _ ↦ Th)
      (x := prog) (joint_posSemidef ρ) hb
    rw [budget_total] at h3
    refine h1.trans (add_le_add le_rfl (h3.trans (sqrt_le_sqrt (mul_le_mul' le_rfl ?_))))
    rw [← Finset.sum_add_distrib, Finset.sum_filter]
    refine Finset.sum_le_sum fun k _ ↦ ?_
    by_cases hk : k.1 = P ∧ xs k.2.1 = k.2.2
    · simp only [hk, and_self, ite_true, hM]
      split_ifs <;> simp
    · have : udRepP P xs ys Th k = Th k := by
        unfold udRepP
        simp only [ite_eq_right_iff]
        exact fun h ↦ absurd ⟨h.1, h.2.symm⟩ hk
      simp [this, hk]
  have hsq := le_two_mul_add_of_sqrt_le (sqrt_avg_le _ _ _ hs)
  refine hsq.trans (add_le_add (mul_le_mul' le_rfl ?_) (mul_le_mul' le_rfl ?_))
  · exact avg_udLP_bad_le P Th (fun _ ↦ ys) (rowOf Th P) fun _ _ _ _ ↦ rfl
  · rw [avg_mul_left]
    refine mul_le_mul' le_rfl ?_
    rw [avg_finset_sum]
    have hk : ∀ k : Dom Sd Tw Msg, (avg fun xs : Tw → Msg ↦
        if k.1 = P ∧ xs k.2.1 = k.2.2 then M k else 0) ≤
        (Fintype.card Msg : ℝ≥0∞)⁻¹ * M k := by
      intro k
      by_cases hP : k.1 = P
      · simp only [hP, true_and]
        rw [avg_coord_eq k.2.1 k.2.2 (fun _ : Tw → Msg ↦ M k) (fun _ _ ↦ rfl), avg_const]
      · simp [hP, avg]
    refine (Finset.sum_le_sum fun k _ ↦ hk k).trans ?_
    rw [← Finset.mul_sum]
    refine mul_le_mul' le_rfl ?_
    rw [hM, Finset.sum_add_distrib]
    have m1 := sum_mass2_le I (fun _ ↦ Th) (x := prog) (joint_posSemidef ρ) (hb false)
    have m2 := sum_mass2_le I (fun _ ↦ Th) (x := prog) (joint_posSemidef ρ) (hb true)
    have ht := ofReal_trace_joint_le_one ρ
    calc _ ≤ ((firstBudget q₁ + secondBudget q₂) false : ℝ≥0∞) * 1 +
          ((firstBudget q₁ + secondBudget q₂) true : ℝ≥0∞) * 1 :=
        add_le_add (m1.trans (mul_le_mul' le_rfl ht)) (m2.trans (mul_le_mul' le_rfl ht))
      _ = _ := by
        rw [mul_one, mul_one, ← Nat.cast_add, budget_total]

/-! ### Assembly -/

theorem toReal_avg {T : Type} [Fintype T] (f : T → ℝ≥0∞) (hf : ∀ t, f t ≤ 1) :
    (avg f).toReal = ∑ t, (Fintype.card T : ℝ)⁻¹ * (f t).toReal := by
  unfold avg
  rw [ENNReal.toReal_sum fun t _ ↦ ENNReal.mul_ne_top
    (ENNReal.inv_ne_top.2 (Nat.cast_ne_zero.2 (Fintype.card_pos_iff.2 ⟨t⟩).ne'))
    (ne_top_of_le_ne_top one_ne_top (hf t))]
  exact Finset.sum_congr rfl fun t _ ↦ by
    rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast]

theorem toReal_avg3 {T₁ T₂ T₃ : Type} [Fintype T₁] [Fintype T₂] [Fintype T₃]
    (g : T₁ → T₂ → T₃ → ℝ≥0∞) (hg : ∀ a b c, g a b c ≤ 1) :
    (avg fun a ↦ avg fun b ↦ avg fun c ↦ g a b c).toReal =
      ∑ ω : T₁ × (T₂ × T₃), ((Fintype.card T₁ : ℝ)⁻¹ *
        ((Fintype.card T₂ : ℝ)⁻¹ * (Fintype.card T₃ : ℝ)⁻¹)) * (g ω.1 ω.2.1 ω.2.2).toReal := by
  rw [toReal_avg _ fun a ↦ avg_le fun b ↦ avg_le fun c ↦ hg a b c, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [toReal_avg _ fun b ↦ avg_le fun c ↦ hg a b c, Finset.mul_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  rw [toReal_avg _ fun c ↦ hg a b c, Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun c _ ↦ by ring

/-- The planted points of the row `P`. -/
def udMarkedP (P : Sd) (xs : Tw → Msg) : Finset (Dom Sd Tw Msg) :=
  Finset.univ.filter fun z ↦ z.1 = P ∧ z.2.2 = xs z.2.1

/-- **Middle vs ideal world: the tight step.**  Same program (determined by the view
`(ys, Th)`), oracles differing only at the planted points, each of which is hidden with
probability `1/|Msg|` given the view. -/
theorem ud_mid_ideal_tight [Nonempty Msg] (hx : IAdv.IsQueryBound n x (firstBudget q₁))
    (h2 : ∀ P u o, (ph2 P u o).IsQueryBound (secondBudget q₂)) (P : Sd) :
    |(avg fun xs : Tw → Msg ↦ avg fun ys : Tw → Y ↦ avg fun Th : Dom Sd Tw Msg → Y ↦
          udLP I ρ cap n x ph2 P (udRepP P xs ys Th) ys (rowOf Th P) udBit).toReal -
        (avg fun _xs : Tw → Msg ↦ avg fun ys : Tw → Y ↦ avg fun Th : Dom Sd Tw Msg → Y ↦
          udLP I ρ cap n x ph2 P Th ys (rowOf Th P) udBit).toReal| ≤
      8 * ((q₁ + q₂ : ℕ) : ℝ) ^ 2 / Fintype.card Msg := by
  classical
  rw [toReal_avg3 _ fun _ _ _ ↦ udLP_le_one _ _ _ _ _, toReal_avg3 _ fun _ _ _ ↦ udLP_le_one _ _ _ _ _]
  set κ : ℝ := (Fintype.card (Tw → Msg) : ℝ)⁻¹ * ((Fintype.card (Tw → Y) : ℝ)⁻¹ *
    (Fintype.card (Dom Sd Tw Msg → Y) : ℝ)⁻¹) with hκdef
  have hκ : 0 ≤ κ := by positivity
  have hS : ∀ z : Dom Sd Tw Msg, ∑ xs : Tw → Msg,
      (if z ∈ udMarkedP P xs then (1 : ℝ) else 0) ≤
      (Fintype.card Msg : ℝ)⁻¹ * Fintype.card (Tw → Msg) := by
    intro z
    by_cases hz : z.1 = P
    · refine le_of_eq (Eq.trans (Finset.sum_congr rfl fun xs _ ↦ ?_) (sum_udMarked_real z.2))
      simp [udMarkedP, udMarked, hz]
    · have : ∀ xs : Tw → Msg, z ∉ udMarkedP P xs := fun xs ↦ by simp [udMarkedP, hz]
      simp only [this, ite_false, Finset.sum_const_zero]
      positivity
  have h := tight_view_of (Ω := (Tw → Msg) × ((Tw → Y) × (Dom Sd Tw Msg → Y)))
    (fun _ ↦ κ) (fun _ ↦ hκ) (fun _ ↦ 1) (fun _ ↦ zero_le_one) (fun _ ↦ le_rfl)
    (fun ω ↦ ω.2) (fun ω ↦ udMarkedP P ω.1) (Fintype.card Msg : ℝ)⁻¹ (by positivity)
    (hidden_indep_real κ _ hκ _ hS)
    ((firstBudget q₁ + secondBudget q₂) false + (firstBudget q₁ + secondBudget q₂) true)
    (fun v H ↦ (udLP I ρ cap n x ph2 P H v.1 (rowOf v.2 P) udBit).toReal)
    (fun v ↦ leafProb2_tightAvgBound I (udProg cap n x ph2 P v.1 (rowOf v.2 P)) ρ _
      (udProg_isQueryBound hx h2 P _ _) udBit)
    (fun ω ↦ udRepP P ω.1 ω.2.1 ω.2.2) (fun v ↦ v.2)
    (fun ω z hne ↦ by
      by_contra hz
      refine hne ?_
      simp only [udMarkedP, Finset.mem_filter, Finset.mem_univ, true_and] at hz
      simp [udRepP, hz])
  have hsum : ∑ _ω : (Tw → Msg) × ((Tw → Y) × (Dom Sd Tw Msg → Y)), κ = 1 := by
    have i1 := card_ne_zero_real (Tw → Msg)
    have i2 := card_ne_zero_real (Tw → Y)
    have i3 := card_ne_zero_real (Dom Sd Tw Msg → Y)
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_prod, Nat.cast_mul,
      hκdef]
    field_simp
  rw [hsum, budget_total] at h
  simp only [mul_one] at h
  rwa [div_eq_mul_inv]

/-- **Exact SM-DT-UD for a fixed seed, tight.** -/
theorem ud_tight_fixedSeed [Nonempty Msg] (hx : IAdv.IsQueryBound n x (firstBudget q₁))
    (h2 : ∀ P u o, (ph2 P u o).IsQueryBound (secondBudget q₂)) (P : Sd) :
    |(avg fun xs : Tw → Msg ↦ avg fun Th : Dom Sd Tw Msg → Y ↦
          udLP I ρ cap n x ph2 P Th (udTgt P xs Th) (rowOf Th P) udBit).toReal -
        (avg fun ys : Tw → Y ↦ avg fun Th : Dom Sd Tw Msg → Y ↦
          udLP I ρ cap n x ph2 P Th ys (rowOf Th P) udBit).toReal| ≤
      (16 * ((q₁ + q₂ : ℕ) : ℝ) ^ 2 + 2 * n) / Fintype.card Msg := by
  set RealP : ℝ≥0∞ := avg fun xs : Tw → Msg ↦ avg fun ys : Tw → Y ↦
    avg fun Th : Dom Sd Tw Msg → Y ↦
      udLP I ρ cap n x ph2 P (udRepP P xs ys Th) ys (rowOf (udRepP P xs ys Th) P) udBit
    with hRealP
  set MidP : ℝ≥0∞ := avg fun xs : Tw → Msg ↦ avg fun ys : Tw → Y ↦
    avg fun Th : Dom Sd Tw Msg → Y ↦
      udLP I ρ cap n x ph2 P (udRepP P xs ys Th) ys (rowOf Th P) udBit with hMidP
  set IdealP : ℝ≥0∞ := avg fun _xs : Tw → Msg ↦ avg fun ys : Tw → Y ↦
    avg fun Th : Dom Sd Tw Msg → Y ↦ udLP I ρ cap n x ph2 P Th ys (rowOf Th P) udBit
    with hIdealP
  have eR : (avg fun xs : Tw → Msg ↦ avg fun Th : Dom Sd Tw Msg → Y ↦
      udLP I ρ cap n x ph2 P Th (udTgt P xs Th) (rowOf Th P) udBit) = RealP :=
    avg_congr fun xs ↦ (avg_udRepP P xs fun ys H ↦
      udLP I ρ cap n x ph2 P H ys (rowOf H P) udBit).symm
  have eI : (avg fun ys : Tw → Y ↦ avg fun Th : Dom Sd Tw Msg → Y ↦
      udLP I ρ cap n x ph2 P Th ys (rowOf Th P) udBit) = IdealP := (avg_const _).symm
  rw [eR, eI]
  have hR1 : RealP ≤ 1 := avg_le fun _ ↦ avg_le fun _ ↦ avg_le fun _ ↦ udLP_le_one _ _ _ _ _
  have hM1 : MidP ≤ 1 := avg_le fun _ ↦ avg_le fun _ ↦ avg_le fun _ ↦ udLP_le_one _ _ _ _ _
  -- real ≤ mid + bad(real)
  have E1 : RealP ≤ MidP + (n : ℝ≥0∞) * (Fintype.card Msg : ℝ≥0∞)⁻¹ := by
    have hb : (avg fun xs : Tw → Msg ↦ avg fun ys : Tw → Y ↦ avg fun Th : Dom Sd Tw Msg → Y ↦
        udLP I ρ cap n x ph2 P (udRepP P xs ys Th) ys (rowOf (udRepP P xs ys Th) P)
          (udBad xs)) ≤ (n : ℝ≥0∞) * (Fintype.card Msg : ℝ≥0∞)⁻¹ := by
      have e : (avg fun xs : Tw → Msg ↦ avg fun ys : Tw → Y ↦ avg fun Th : Dom Sd Tw Msg → Y ↦
          udLP I ρ cap n x ph2 P (udRepP P xs ys Th) ys (rowOf (udRepP P xs ys Th) P)
            (udBad xs)) =
          avg fun xs : Tw → Msg ↦ avg fun Th : Dom Sd Tw Msg → Y ↦
            udLP I ρ cap n x ph2 P Th (udTgt P xs Th) (rowOf Th P) (udBad xs) :=
        avg_congr fun xs ↦ avg_udRepP P xs fun ys H ↦
          udLP I ρ cap n x ph2 P H ys (rowOf H P) (udBad xs)
      rw [e, avg_comm]
      exact avg_le fun Th ↦ avg_udLP_bad_le P Th (fun xs ↦ udTgt P xs Th) (rowOf Th P)
        fun xs xs' t h ↦ by simp [udTgt, h]
    refine le_trans ?_ (add_le_add le_rfl hb)
    rw [hMidP, ← avg_add]
    refine avg_mono fun xs ↦ ?_
    rw [← avg_add]
    refine avg_mono fun ys ↦ ?_
    rw [← avg_add]
    exact avg_mono fun Th ↦ udLP_real_le_mid_add P xs ys Th
  -- mid ≤ real + bad(mid)
  have E2 : MidP ≤ RealP + (2 * ((n : ℝ≥0∞) * (Fintype.card Msg : ℝ≥0∞)⁻¹) +
      2 * (4 * ((q₁ + q₂ : ℕ) : ℝ≥0∞) * ((Fintype.card Msg : ℝ≥0∞)⁻¹ *
        ((q₁ + q₂ : ℕ) : ℝ≥0∞)))) := by
    have hb : (avg fun xs : Tw → Msg ↦ avg fun ys : Tw → Y ↦ avg fun Th : Dom Sd Tw Msg → Y ↦
        udLP I ρ cap n x ph2 P (udRepP P xs ys Th) ys (rowOf Th P) (udBad xs)) ≤
        2 * ((n : ℝ≥0∞) * (Fintype.card Msg : ℝ≥0∞)⁻¹) +
          2 * (4 * ((q₁ + q₂ : ℕ) : ℝ≥0∞) * ((Fintype.card Msg : ℝ≥0∞)⁻¹ *
            ((q₁ + q₂ : ℕ) : ℝ≥0∞))) := by
      rw [avg_comm]
      refine avg_le fun ys ↦ ?_
      rw [avg_comm]
      exact avg_le fun Th ↦ avg_udLP_mid_bad_le hx h2 P ys Th
    refine le_trans ?_ (add_le_add le_rfl hb)
    rw [hRealP, ← avg_add]
    refine avg_mono fun xs ↦ ?_
    rw [← avg_add]
    refine avg_mono fun ys ↦ ?_
    rw [← avg_add]
    exact avg_mono fun Th ↦ udLP_mid_le_real_add P xs ys Th
  have hT := ud_mid_ideal_tight (I := I) (ρ := ρ) (cap := cap) hx h2 P
  rw [← hMidP, ← hIdealP] at hT
  have hc : (Fintype.card Msg : ℝ≥0∞)⁻¹ ≠ ⊤ :=
    ENNReal.inv_ne_top.2 (Nat.cast_ne_zero.2 Fintype.card_ne_zero)
  have hMsg : (0 : ℝ) < Fintype.card Msg := by exact_mod_cast Fintype.card_pos
  have r1 : RealP.toReal ≤ MidP.toReal + n / Fintype.card Msg := by
    have h := ENNReal.toReal_mono (ENNReal.add_ne_top.2
      ⟨ne_top_of_le_ne_top one_ne_top hM1, ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hc⟩) E1
    rwa [ENNReal.toReal_add (ne_top_of_le_ne_top one_ne_top hM1)
      (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hc), ENNReal.toReal_mul,
      ENNReal.toReal_inv, ENNReal.toReal_natCast, ENNReal.toReal_natCast,
      ← div_eq_mul_inv] at h
  have r2 : MidP.toReal ≤ RealP.toReal + (2 * n + 8 * ((q₁ + q₂ : ℕ) : ℝ) ^ 2) /
      Fintype.card Msg := by
    have hfin : (2 * ((n : ℝ≥0∞) * (Fintype.card Msg : ℝ≥0∞)⁻¹) +
        2 * (4 * ((q₁ + q₂ : ℕ) : ℝ≥0∞) * ((Fintype.card Msg : ℝ≥0∞)⁻¹ *
          ((q₁ + q₂ : ℕ) : ℝ≥0∞)))) ≠ ⊤ := by
      refine ENNReal.add_ne_top.2 ⟨?_, ?_⟩ <;>
        simp [ENNReal.mul_eq_top, hc]
    have h := ENNReal.toReal_mono (ENNReal.add_ne_top.2
      ⟨ne_top_of_le_ne_top one_ne_top hR1, hfin⟩) E2
    rw [ENNReal.toReal_add (ne_top_of_le_ne_top one_ne_top hR1) hfin] at h
    refine h.trans (add_le_add le_rfl (le_of_eq ?_))
    rw [ENNReal.toReal_add (by simp [ENNReal.mul_eq_top, hc])
      (by simp [ENNReal.mul_eq_top, hc])]
    simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
      ENNReal.toReal_ofNat]
    field_simp
    ring
  have hq0 : (0 : ℝ) ≤ ((q₁ + q₂ : ℕ) : ℝ) ^ 2 := sq_nonneg _
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hdiv : (16 * ((q₁ + q₂ : ℕ) : ℝ) ^ 2 + 2 * n) / Fintype.card Msg =
      8 * ((q₁ + q₂ : ℕ) : ℝ) ^ 2 / Fintype.card Msg +
        (2 * n + 8 * ((q₁ + q₂ : ℕ) : ℝ) ^ 2) / Fintype.card Msg := by ring
  have hn1 : (n : ℝ) / Fintype.card Msg ≤
      (2 * n + 8 * ((q₁ + q₂ : ℕ) : ℝ) ^ 2) / Fintype.card Msg :=
    div_le_div_of_nonneg_right (by linarith) hMsg.le
  rw [hdiv, abs_le]
  have := abs_le.1 hT
  constructor <;> linarith

/-- **Exact SM-DT-UD in the QROM, tight bound, no seed-hiding term.**  For the adaptive two-phase
game of `PQ/QROM/ExactUd.lean` (phase 1: at most `q₁` quantum queries and `n` classical requests;
phase 2, given the seed: at most `q₂` quantum queries):
`|Pr[real outputs 1] − Pr[ideal outputs 1]| ≤ (16 (q₁ + q₂)² + 2 n) / |Msg|`,
independently of the number of targets and of `|Sd|`. -/
theorem ud_exact_tight [Nonempty Msg] (hx : IAdv.IsQueryBound n x (firstBudget q₁))
    (h2 : ∀ P u o, (ph2 P u o).IsQueryBound (secondBudget q₂)) :
    |(udReal I ρ cap n x ph2).toReal - (udIdeal I ρ cap n x ph2).toReal| ≤
      (16 * ((q₁ + q₂ : ℕ) : ℝ) ^ 2 + 2 * n) / Fintype.card Msg := by
  have hMsg : (0 : ℝ) < Fintype.card Msg := by exact_mod_cast Fintype.card_pos
  have hbound : (0 : ℝ) ≤ (16 * ((q₁ + q₂ : ℕ) : ℝ) ^ 2 + 2 * n) / Fintype.card Msg := by
    positivity
  rw [udReal_eq, udIdeal_eq, avg_comm, avg_comm (T := Tw → Y),
    toReal_avg _ fun P ↦ avg_le fun _ ↦ avg_le fun _ ↦ udLP_le_one _ _ _ _ _,
    toReal_avg _ fun P ↦ avg_le fun _ ↦ avg_le fun _ ↦ udLP_le_one _ _ _ _ _,
    ← Finset.sum_sub_distrib]
  rcases isEmpty_or_nonempty Sd with hSd | hSd
  · simpa using hbound
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ P : Sd, |(Fintype.card Sd : ℝ)⁻¹ *
      (avg fun xs : Tw → Msg ↦ avg fun Th : Dom Sd Tw Msg → Y ↦
        udLP I ρ cap n x ph2 P Th (udTgt P xs Th) (rowOf Th P) udBit).toReal -
      (Fintype.card Sd : ℝ)⁻¹ *
        (avg fun ys : Tw → Y ↦ avg fun Th : Dom Sd Tw Msg → Y ↦
          udLP I ρ cap n x ph2 P Th ys (rowOf Th P) udBit).toReal| ≤
      (Fintype.card Sd : ℝ)⁻¹ *
        ((16 * ((q₁ + q₂ : ℕ) : ℝ) ^ 2 + 2 * n) / Fintype.card Msg) := by
    intro P
    rw [← mul_sub, abs_mul, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (ud_tight_fixedSeed hx h2 P) (by positivity)
  refine (Finset.sum_le_sum fun P _ ↦ hterm P).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
    mul_inv_cancel₀ (card_ne_zero_real Sd), one_mul]

/-- **Exact SM-DT-UD, tight, real ≤ ideal** (in `ℝ≥0∞`). -/
theorem ud_exact_tight_real_le_ideal_add [Nonempty Msg]
    (hx : IAdv.IsQueryBound n x (firstBudget q₁))
    (h2 : ∀ P u o, (ph2 P u o).IsQueryBound (secondBudget q₂)) :
    udReal I ρ cap n x ph2 ≤ udIdeal I ρ cap n x ph2 +
      ENNReal.ofReal ((16 * ((q₁ + q₂ : ℕ) : ℝ) ^ 2 + 2 * n) / Fintype.card Msg) :=
  le_add_ofReal_of_abs_toReal (avg_le fun _ ↦ twoPhaseExp_le_one)
    (avg_le fun _ ↦ twoPhaseExp_le_one) (ud_exact_tight hx h2)

/-- **Exact SM-DT-UD, tight, ideal ≤ real** (in `ℝ≥0∞`). -/
theorem ud_exact_tight_ideal_le_real_add [Nonempty Msg]
    (hx : IAdv.IsQueryBound n x (firstBudget q₁))
    (h2 : ∀ P u o, (ph2 P u o).IsQueryBound (secondBudget q₂)) :
    udIdeal I ρ cap n x ph2 ≤ udReal I ρ cap n x ph2 +
      ENNReal.ofReal ((16 * ((q₁ + q₂ : ℕ) : ℝ) ^ 2 + 2 * n) / Fintype.card Msg) :=
  le_add_ofReal_of_abs_toReal (avg_le fun _ ↦ twoPhaseExp_le_one)
    (avg_le fun _ ↦ twoPhaseExp_le_one)
    (by rw [abs_sub_comm]; exact ud_exact_tight hx h2)

end UD

end PQ.QROM

#print axioms PQ.QROM.ud_mid_ideal_tight
#print axioms PQ.QROM.ud_exact_tight
#print axioms PQ.QROM.ud_exact_tight_real_le_ideal_add
#print axioms PQ.QROM.ud_exact_tight_ideal_le_real_add
