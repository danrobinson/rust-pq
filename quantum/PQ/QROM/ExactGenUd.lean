import PQ.QROM.ExactUdTight

/-!
# The exact SM-DT-UD game with a planted subspace and a collection family: tight bound

The UD problem of the reduction (VCVio `SM_DT_UD_Problem`, `…/TweakableHash/SMDTUD.lean`) plants
its hidden inputs in a subspace `Mp ↪ Msg` of the message space of the attacked member, and its
collection oracle evaluates the OTHER members of the tweakable-hash collection (`thColl`), never
the attacked member.  `PQ/QROM/ExactUd.lean` hard-wires `Mp = Msg` and a collection oracle on the
attacked member.  This file defines the game in the shape of VCVio's:

* one uniformly random function `Th : Sd × (Tw × (Msg ⊕ C)) → Y` (as in
  `PQ/QROM/ExactGenColl.lean`): the attacked member is the `Sum.inl` part, the collection is the
  `Sum.inr` part (`C := Σ i, MsgC i` for an indexed family with message types `MsgC i`);
* state `(challenge tweaks, collection tweaks)`, both in issue order (`SM_DT_UD_State`);
* challenge request `t` (`genUdChT`): refused iff the target cap is reached, or `t` is in the
  challenge history, or `t` was spent on the collection oracle (`TweakFresh`); otherwise answered
  `Th (P, t, inl (emb (xs t)))` for planted uniform `xs : Tw → Mp` (real, `genUdReal`) or by a
  uniform `ys t` (ideal, `genUdIdeal`), and `t` is appended to the challenge history;
* collection request `(t, c)`: refused iff `t` is in the challenge history (`TweakReserved`);
  otherwise answered `Th (P, t, inr c)` and `t` is appended to the collection tweaks (repeated
  collection tweaks are accepted);
* phase 1: quantum access to `Th`, at most `q₁` quantum queries and `n` classical requests;
  phase 2 gets the seed `P`, at most `q₂` quantum queries, outputs a bit.

`gen_ud_exact_tight : |genUdReal.toReal − genUdIdeal.toReal| ≤ 8 (q₁ + q₂)² / |Mp|`

with no seed-hiding term, no dependence on the number of targets, and — unlike
`ud_exact_tight` — no dependence on the number `n` of classical requests: the collection oracle
never evaluates the attacked member, so it cannot hit a planted point, and after the change of
variables `avg_genUdRep` the real world runs the SAME program as the ideal world against an
oracle reprogrammed at the planted points `(P, t, inl (emb (xs t)))`, each hidden with
probability `1/|Mp|` given the view.  (`gen_ud_exact_tight_real_le_ideal_add`,
`gen_ud_exact_tight_ideal_le_real_add`: one-sided, `ℝ≥0∞`.)

The game of `PQ/QROM/ExactUd.lean` (collection oracle on the attacked member) is NOT a special
case of this one; its tight bound is `ud_exact_tight`.
-/

open MeasureTheory ENNReal Quantum Matrix
open PQ.QROM.Tight
open scoped Kronecker ComplexOrder

universe u v w

set_option linter.unusedSectionVars false

namespace PQ.QROM

variable {Sd Tw Msg Mp C Y : Type}

/-- The two classical oracles of SM-DT-UD with a collection family: challenge table `y`,
collection answers from the `Sum.inr` part of the row `a`. -/
def genUdChT [DecidableEq Tw] (cap : ℕ) (y : Tw → Y) (a : Tw × (Msg ⊕ C) → Y) :
    Tw ⊕ (Tw × C) → List Tw × List Tw → Option Y × (List Tw × List Tw)
  | .inl t, s =>
    if cap ≤ s.1.length ∨ t ∈ s.1 ∨ t ∈ s.2 then (none, s) else (some (y t), (s.1 ++ [t], s.2))
  | .inr tc, s =>
    if tc.1 ∈ s.1 then (none, s) else (some (a (tc.1, Sum.inr tc.2)), (s.1, s.2 ++ [tc.1]))

/-- The real-world oracles: the challenge `t` is answered by the image of the planted input. -/
def genUdCh [DecidableEq Tw] (cap : ℕ) (emb : Mp ↪ Msg) (xs : Tw → Mp)
    (a : Tw × (Msg ⊕ C) → Y) :
    Tw ⊕ (Tw × C) → List Tw × List Tw → Option Y × (List Tw × List Tw) :=
  genUdChT cap (fun t ↦ a (t, Sum.inl (emb (xs t)))) a

/-- The collection oracle only reads the `Sum.inr` part of the row. -/
theorem genUdChT_congr [DecidableEq Tw] (cap : ℕ) (y : Tw → Y) (a a' : Tw × (Msg ⊕ C) → Y)
    (h : ∀ (t : Tw) (c : C), a (t, Sum.inr c) = a' (t, Sum.inr c)) :
    genUdChT cap y a = genUdChT cap y a' := by
  funext req s
  cases req with
  | inl t => rfl
  | inr tc => simp only [genUdChT, h]

section Exp

variable [Fintype Sd] [DecidableEq Sd] [Fintype Tw] [DecidableEq Tw] [Fintype Msg]
  [DecidableEq Msg] [Fintype Mp] [DecidableEq Mp] [Fintype C] [DecidableEq C] [Fintype Y]
  [DecidableEq Y] [AddCommGroup Y]
  {L : LocalSig.{u, v}} {Out : QReg → Type w} {A : QReg}

variable (I : L.Interp) (ρ : SubState A) (cap n : ℕ) (emb : Mp ↪ Msg)
  (x : IAdv L (qrom2Spec (Dom Sd Tw (Msg ⊕ C)) Y) (Tw ⊕ (Tw × C)) (Option Y) Out n A)
  (ph2 : Sd → ∀ u, Out u →
    QuantumComp L (qrom2Spec (Dom Sd Tw (Msg ⊕ C)) Y) (fun _ ↦ Bool) u)

/-- The UD experiment outputs the bit of phase 2. -/
def genUdWin (_ : Tw × (Msg ⊕ C) → Y) (b : Bool) (_ : List Tw × List Tw) : Prop := b = true

/-- **SM-DT-UD with planted subspace and collection family, real world.** -/
noncomputable def genUdReal : ℝ≥0∞ :=
  avg fun xs : Tw → Mp ↦
    twoPhaseExp I ρ (genUdCh (C := C) cap emb xs) ([], []) n x ph2 genUdWin

/-- **SM-DT-UD with planted subspace and collection family, ideal world.** -/
noncomputable def genUdIdeal : ℝ≥0∞ :=
  avg fun ys : Tw → Y ↦
    twoPhaseExp I ρ (fun a ↦ genUdChT (Msg := Msg) (C := C) cap ys a) ([], []) n x ph2 genUdWin

/-- Probability that the run with challenge table `y` and row `a` (for the collection answers),
both phases having quantum access to `H`, outputs `true`. -/
noncomputable def genUdLP (P : Sd) (H : Dom Sd Tw (Msg ⊕ C) → Y) (y : Tw → Y)
    (a : Tw × (Msg ⊕ C) → Y) : ℝ≥0∞ :=
  leafProb (twoRuntime fun _ ↦ H) I
    (composite (genUdChT cap y a) (([], []) : List Tw × List Tw) n x ph2 P) (joint ρ)
    (fun p ↦ p.2.1 = true)

/-- The targets of the real world. -/
def genUdTgt (P : Sd) (xs : Tw → Mp) (Th : Dom Sd Tw (Msg ⊕ C) → Y) : Tw → Y :=
  fun t ↦ Th (P, (t, Sum.inl (emb (xs t))))

/-- `Th` reprogrammed to `ys t` at the planted points `(P, t, inl (emb (xs t)))`. -/
def genUdRep (P : Sd) (xs : Tw → Mp) (ys : Tw → Y) (Th : Dom Sd Tw (Msg ⊕ C) → Y) :
    Dom Sd Tw (Msg ⊕ C) → Y :=
  fun z ↦ if z.1 = P ∧ z.2.2 = Sum.inl (emb (xs z.2.1)) then ys z.2.1 else Th z

/-- The planted points of the row `P`. -/
def genUdMarked (P : Sd) (xs : Tw → Mp) : Finset (Dom Sd Tw (Msg ⊕ C)) :=
  Finset.univ.filter fun z ↦ z.1 = P ∧ z.2.2 = Sum.inl (emb (xs z.2.1))

theorem genUdReal_eq : genUdReal I ρ cap n emb x ph2 =
    avg fun xs : Tw → Mp ↦ avg fun P : Sd ↦ avg fun Th : Dom Sd Tw (Msg ⊕ C) → Y ↦
      genUdLP I ρ cap n x ph2 P Th (genUdTgt emb P xs Th) (rowOf Th P) := rfl

theorem genUdIdeal_eq : genUdIdeal I ρ cap n x ph2 =
    avg fun ys : Tw → Y ↦ avg fun P : Sd ↦ avg fun Th : Dom Sd Tw (Msg ⊕ C) → Y ↦
      genUdLP I ρ cap n x ph2 P Th ys (rowOf Th P) := rfl

variable {I ρ cap n emb x ph2}

theorem genUdLP_le_one (P : Sd) (H : Dom Sd Tw (Msg ⊕ C) → Y) (y : Tw → Y)
    (a : Tw × (Msg ⊕ C) → Y) : genUdLP I ρ cap n x ph2 P H y a ≤ 1 :=
  (leafProb_le _ (joint_posSemidef ρ) _).trans (ofReal_trace_joint_le_one ρ)

theorem genUdTgt_genUdRep (P : Sd) (xs : Tw → Mp) (ys : Tw → Y)
    (Th : Dom Sd Tw (Msg ⊕ C) → Y) : genUdTgt emb P xs (genUdRep emb P xs ys Th) = ys := by
  funext t
  simp [genUdTgt, genUdRep]

/-- Exchange the values at the planted points of the row `P` with `ys`. -/
def genUdSwap (emb : Mp ↪ Msg) (P : Sd) (xs : Tw → Mp)
    (v : (Tw → Y) × (Dom Sd Tw (Msg ⊕ C) → Y)) : (Tw → Y) × (Dom Sd Tw (Msg ⊕ C) → Y) :=
  (genUdTgt emb P xs v.2, genUdRep emb P xs v.1 v.2)

theorem genUdSwap_involutive (P : Sd) (xs : Tw → Mp) :
    Function.Involutive (genUdSwap (C := C) (Y := Y) emb P xs) := by
  rintro ⟨ys, Th⟩
  refine Prod.ext (genUdTgt_genUdRep P xs ys Th) (funext fun z ↦ ?_)
  obtain ⟨P', t, m⟩ := z
  by_cases h : P' = P ∧ m = Sum.inl (emb (xs t))
  · obtain ⟨rfl, rfl⟩ := h
    simp [genUdSwap, genUdRep, genUdTgt]
  · simp [genUdSwap, genUdRep, h]

/-- **Change of variables.** -/
theorem avg_genUdRep (P : Sd) (xs : Tw → Mp)
    (g : (Tw → Y) → (Dom Sd Tw (Msg ⊕ C) → Y) → ℝ≥0∞) :
    (avg fun ys : Tw → Y ↦ avg fun Th : Dom Sd Tw (Msg ⊕ C) → Y ↦
        g ys (genUdRep emb P xs ys Th)) =
      avg fun Th : Dom Sd Tw (Msg ⊕ C) → Y ↦ g (genUdTgt emb P xs Th) Th := by
  have h := Equiv.sum_comp (genUdSwap_involutive (emb := emb) (C := C) (Y := Y) P xs).toPerm
    (fun v ↦ ((Fintype.card (Tw → Y) : ℝ≥0∞)⁻¹ *
      (Fintype.card (Dom Sd Tw (Msg ⊕ C) → Y) : ℝ≥0∞)⁻¹) * g (genUdTgt emb P xs v.2) v.2)
  have e1 : (avg fun ys : Tw → Y ↦ avg fun Th : Dom Sd Tw (Msg ⊕ C) → Y ↦
      g ys (genUdRep emb P xs ys Th)) =
      ∑ v : (Tw → Y) × (Dom Sd Tw (Msg ⊕ C) → Y),
        ((Fintype.card (Tw → Y) : ℝ≥0∞)⁻¹ *
          (Fintype.card (Dom Sd Tw (Msg ⊕ C) → Y) : ℝ≥0∞)⁻¹) *
          g (genUdTgt emb P xs (genUdSwap emb P xs v).2) (genUdSwap emb P xs v).2 := by
    unfold avg
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun ys _ ↦ ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun Th _ ↦ ?_
    change _ = _ * g (genUdTgt emb P xs (genUdRep emb P xs ys Th)) (genUdRep emb P xs ys Th)
    rw [genUdTgt_genUdRep, mul_assoc]
  simp only [Function.Involutive.coe_toPerm] at h
  rw [e1, h, Fintype.sum_prod_type]
  have e2 : ∀ ys : Tw → Y, ∑ Th : Dom Sd Tw (Msg ⊕ C) → Y,
      ((Fintype.card (Tw → Y) : ℝ≥0∞)⁻¹ * (Fintype.card (Dom Sd Tw (Msg ⊕ C) → Y) : ℝ≥0∞)⁻¹) *
        g (genUdTgt emb P xs Th) Th =
      (Fintype.card (Tw → Y) : ℝ≥0∞)⁻¹ *
        avg fun Th : Dom Sd Tw (Msg ⊕ C) → Y ↦ g (genUdTgt emb P xs Th) Th :=
    fun ys ↦ by
      unfold avg
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun Th _ ↦ mul_assoc _ _ _
  rw [Finset.sum_congr rfl fun ys _ ↦ e2 ys]
  exact avg_const (T := Tw → Y) _

/-- The collection answers are not affected by the reprogramming: the real world, after the
change of variables, runs the program of the ideal world. -/
theorem genUdLP_rep_row (P : Sd) (xs : Tw → Mp) (ys : Tw → Y) (Th H : Dom Sd Tw (Msg ⊕ C) → Y) :
    genUdLP I ρ cap n x ph2 P H ys (rowOf (genUdRep emb P xs ys Th) P) =
      genUdLP I ρ cap n x ph2 P H ys (rowOf Th P) := by
  unfold genUdLP
  rw [genUdChT_congr cap ys (rowOf (genUdRep emb P xs ys Th) P) (rowOf Th P) fun t c ↦ by
    simp [rowOf, genUdRep]]

variable {q₁ q₂ : ℕ}

/-- **Exact SM-DT-UD with planted subspace and collection family, fixed seed, tight.** -/
theorem gen_ud_tight_fixedSeed [Nonempty Mp] (hx : IAdv.IsQueryBound n x (firstBudget q₁))
    (h2 : ∀ P u o, (ph2 P u o).IsQueryBound (secondBudget q₂)) (P : Sd) :
    |(avg fun xs : Tw → Mp ↦ avg fun Th : Dom Sd Tw (Msg ⊕ C) → Y ↦
          genUdLP I ρ cap n x ph2 P Th (genUdTgt emb P xs Th) (rowOf Th P)).toReal -
        (avg fun ys : Tw → Y ↦ avg fun Th : Dom Sd Tw (Msg ⊕ C) → Y ↦
          genUdLP I ρ cap n x ph2 P Th ys (rowOf Th P)).toReal| ≤
      8 * ((q₁ + q₂ : ℕ) : ℝ) ^ 2 / Fintype.card Mp := by
  classical
  have eR : (avg fun xs : Tw → Mp ↦ avg fun Th : Dom Sd Tw (Msg ⊕ C) → Y ↦
      genUdLP I ρ cap n x ph2 P Th (genUdTgt emb P xs Th) (rowOf Th P)) =
      avg fun xs : Tw → Mp ↦ avg fun ys : Tw → Y ↦ avg fun Th : Dom Sd Tw (Msg ⊕ C) → Y ↦
        genUdLP I ρ cap n x ph2 P (genUdRep emb P xs ys Th) ys (rowOf Th P) :=
    avg_congr fun xs ↦ ((avg_genUdRep (emb := emb) P xs fun ys H ↦
      genUdLP I ρ cap n x ph2 P H ys (rowOf H P)).symm.trans
      (avg_congr fun ys ↦ avg_congr fun Th ↦ genUdLP_rep_row P xs ys Th _))
  have eI : (avg fun ys : Tw → Y ↦ avg fun Th : Dom Sd Tw (Msg ⊕ C) → Y ↦
      genUdLP I ρ cap n x ph2 P Th ys (rowOf Th P)) =
      avg fun _xs : Tw → Mp ↦ avg fun ys : Tw → Y ↦ avg fun Th : Dom Sd Tw (Msg ⊕ C) → Y ↦
        genUdLP I ρ cap n x ph2 P Th ys (rowOf Th P) := (avg_const _).symm
  rw [eR, eI, toReal_avg3 _ fun _ _ _ ↦ genUdLP_le_one _ _ _ _,
    toReal_avg3 _ fun _ _ _ ↦ genUdLP_le_one _ _ _ _]
  set κ : ℝ := (Fintype.card (Tw → Mp) : ℝ)⁻¹ * ((Fintype.card (Tw → Y) : ℝ)⁻¹ *
    (Fintype.card (Dom Sd Tw (Msg ⊕ C) → Y) : ℝ)⁻¹) with hκdef
  have hκ : 0 ≤ κ := by positivity
  have hS : ∀ z : Dom Sd Tw (Msg ⊕ C), ∑ xs : Tw → Mp,
      (if z ∈ genUdMarked emb P xs then (1 : ℝ) else 0) ≤
      (Fintype.card Mp : ℝ)⁻¹ * Fintype.card (Tw → Mp) := by
    intro z
    have hnn : (0 : ℝ) ≤ (Fintype.card Mp : ℝ)⁻¹ * Fintype.card (Tw → Mp) := by positivity
    obtain ⟨P', t, m⟩ := z
    by_cases hz : P' = P ∧ ∃ m₀ : Mp, m = Sum.inl (emb m₀)
    · obtain ⟨rfl, m₀, rfl⟩ := hz
      refine le_of_eq (Eq.trans (Finset.sum_congr rfl fun xs _ ↦ ?_)
        (sum_udMarked_real (T := Tw) (Msg := Mp) (t, m₀)))
      simp [genUdMarked, udMarked]
    · have : ∀ xs : Tw → Mp, (P', t, m) ∉ genUdMarked emb P xs := fun xs h ↦ by
        simp only [genUdMarked, Finset.mem_filter, Finset.mem_univ, true_and] at h
        exact hz ⟨h.1, xs t, h.2⟩
      simp only [this, ite_false, Finset.sum_const_zero]
      exact hnn
  have hb : ∀ (y : Tw → Y) (a : Tw × (Msg ⊕ C) → Y),
      (composite (genUdChT cap y a) (([], []) : List Tw × List Tw) n x ph2 P).IsQueryBound
        (firstBudget q₁ + secondBudget q₂) := fun y a ↦
    IAdv.flat_isQueryBound _ _ hx (phase2K_isQueryBound h2 P)
  have h := tight_view_of (Ω := (Tw → Mp) × ((Tw → Y) × (Dom Sd Tw (Msg ⊕ C) → Y)))
    (fun _ ↦ κ) (fun _ ↦ hκ) (fun _ ↦ 1) (fun _ ↦ zero_le_one) (fun _ ↦ le_rfl)
    (fun ω ↦ ω.2) (fun ω ↦ genUdMarked emb P ω.1) (Fintype.card Mp : ℝ)⁻¹ (by positivity)
    (hidden_indep_real κ _ hκ _ hS)
    ((firstBudget q₁ + secondBudget q₂) false + (firstBudget q₁ + secondBudget q₂) true)
    (fun v H ↦ (genUdLP I ρ cap n x ph2 P H v.1 (rowOf v.2 P)).toReal)
    (fun v ↦ leafProb2_tightAvgBound I _ ρ _ (hb v.1 (rowOf v.2 P)) _)
    (fun ω ↦ genUdRep emb P ω.1 ω.2.1 ω.2.2) (fun v ↦ v.2)
    (fun ω z hne ↦ by
      by_contra hz
      refine hne ?_
      simp only [genUdMarked, Finset.mem_filter, Finset.mem_univ, true_and] at hz
      simp [genUdRep, hz])
  have hsum : ∑ _ω : (Tw → Mp) × ((Tw → Y) × (Dom Sd Tw (Msg ⊕ C) → Y)), κ = 1 := by
    have i1 := card_ne_zero_real (Tw → Mp)
    have i2 := card_ne_zero_real (Tw → Y)
    have i3 := card_ne_zero_real (Dom Sd Tw (Msg ⊕ C) → Y)
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_prod, Nat.cast_mul,
      hκdef]
    field_simp
  rw [hsum, budget_total] at h
  simp only [mul_one] at h
  rwa [div_eq_mul_inv]

/-- **Exact SM-DT-UD with planted subspace `Mp ↪ Msg` and a collection family, tight bound, no
seed-hiding term**: `|Pr[real outputs 1] − Pr[ideal outputs 1]| ≤ 8 (q₁ + q₂)² / |Mp|`,
independently of the number of targets, of the number of classical requests and of `|Sd|`. -/
theorem gen_ud_exact_tight [Nonempty Mp] (hx : IAdv.IsQueryBound n x (firstBudget q₁))
    (h2 : ∀ P u o, (ph2 P u o).IsQueryBound (secondBudget q₂)) :
    |(genUdReal I ρ cap n emb x ph2).toReal - (genUdIdeal I ρ cap n x ph2).toReal| ≤
      8 * ((q₁ + q₂ : ℕ) : ℝ) ^ 2 / Fintype.card Mp := by
  have hMp : (0 : ℝ) < Fintype.card Mp := by exact_mod_cast Fintype.card_pos
  have hbound : (0 : ℝ) ≤ 8 * ((q₁ + q₂ : ℕ) : ℝ) ^ 2 / Fintype.card Mp := by positivity
  rw [genUdReal_eq, genUdIdeal_eq, avg_comm, avg_comm (T := Tw → Y),
    toReal_avg _ fun P ↦ avg_le fun _ ↦ avg_le fun _ ↦ genUdLP_le_one _ _ _ _,
    toReal_avg _ fun P ↦ avg_le fun _ ↦ avg_le fun _ ↦ genUdLP_le_one _ _ _ _,
    ← Finset.sum_sub_distrib]
  rcases isEmpty_or_nonempty Sd with hSd | hSd
  · simpa using hbound
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ P : Sd, |(Fintype.card Sd : ℝ)⁻¹ *
      (avg fun xs : Tw → Mp ↦ avg fun Th : Dom Sd Tw (Msg ⊕ C) → Y ↦
        genUdLP I ρ cap n x ph2 P Th (genUdTgt emb P xs Th) (rowOf Th P)).toReal -
      (Fintype.card Sd : ℝ)⁻¹ *
        (avg fun ys : Tw → Y ↦ avg fun Th : Dom Sd Tw (Msg ⊕ C) → Y ↦
          genUdLP I ρ cap n x ph2 P Th ys (rowOf Th P)).toReal| ≤
      (Fintype.card Sd : ℝ)⁻¹ * (8 * ((q₁ + q₂ : ℕ) : ℝ) ^ 2 / Fintype.card Mp) := by
    intro P
    rw [← mul_sub, abs_mul, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (gen_ud_tight_fixedSeed hx h2 P) (by positivity)
  refine (Finset.sum_le_sum fun P _ ↦ hterm P).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
    mul_inv_cancel₀ (card_ne_zero_real Sd), one_mul]

/-- **Tight, real ≤ ideal** (in `ℝ≥0∞`). -/
theorem gen_ud_exact_tight_real_le_ideal_add [Nonempty Mp]
    (hx : IAdv.IsQueryBound n x (firstBudget q₁))
    (h2 : ∀ P u o, (ph2 P u o).IsQueryBound (secondBudget q₂)) :
    genUdReal I ρ cap n emb x ph2 ≤ genUdIdeal I ρ cap n x ph2 +
      ENNReal.ofReal (8 * ((q₁ + q₂ : ℕ) : ℝ) ^ 2 / Fintype.card Mp) :=
  le_add_ofReal_of_abs_toReal (avg_le fun _ ↦ twoPhaseExp_le_one)
    (avg_le fun _ ↦ twoPhaseExp_le_one) (gen_ud_exact_tight hx h2)

/-- **Tight, ideal ≤ real** (in `ℝ≥0∞`). -/
theorem gen_ud_exact_tight_ideal_le_real_add [Nonempty Mp]
    (hx : IAdv.IsQueryBound n x (firstBudget q₁))
    (h2 : ∀ P u o, (ph2 P u o).IsQueryBound (secondBudget q₂)) :
    genUdIdeal I ρ cap n x ph2 ≤ genUdReal I ρ cap n emb x ph2 +
      ENNReal.ofReal (8 * ((q₁ + q₂ : ℕ) : ℝ) ^ 2 / Fintype.card Mp) :=
  le_add_ofReal_of_abs_toReal (avg_le fun _ ↦ twoPhaseExp_le_one)
    (avg_le fun _ ↦ twoPhaseExp_le_one)
    (by rw [abs_sub_comm]; exact gen_ud_exact_tight hx h2)

/-- Classical first phase (`q₁ = 0`): `|Pr[real] − Pr[ideal]| ≤ 8 q₂² / |Mp|`. -/
theorem gen_ud_exact_tight_zeroPre [Nonempty Mp] (hx : IAdv.IsQueryBound n x (firstBudget 0))
    (h2 : ∀ P u o, (ph2 P u o).IsQueryBound (secondBudget q₂)) :
    |(genUdReal I ρ cap n emb x ph2).toReal - (genUdIdeal I ρ cap n x ph2).toReal| ≤
      8 * (q₂ : ℝ) ^ 2 / Fintype.card Mp := by
  have h := gen_ud_exact_tight (I := I) (ρ := ρ) (cap := cap) (emb := emb) hx h2
  rwa [zero_add] at h

end Exp

end PQ.QROM

#print axioms PQ.QROM.gen_ud_exact_tight
#print axioms PQ.QROM.gen_ud_exact_tight_real_le_ideal_add
#print axioms PQ.QROM.gen_ud_exact_tight_ideal_le_real_add
#print axioms PQ.QROM.gen_ud_exact_tight_zeroPre
