import PQ.QROM.ExactPre
import PQ.QROM.ExactGenPreGiven

/-!
# The exact SM-DT-PRE game in the QROM, planted inputs of a separate type

`PQ/QROM/ExactPre.lean` formalises VCVio's `TweakableHash.SM_DT_PRE_Experiment`
(`VCVio/CryptoFoundations/HardnessAssumptions/TweakableHash/SMDTPRE.lean`) with the planted
message type hard-wired to the message type (`M' = M`, `emb = id`).  This file removes that
deviation: the planted inputs live in a separate type `Mp` (VCVio's `M'`) with an injective
`emb : Mp ↪ Msg`.

## Correspondence with `SM_DT_PRE_Experiment`

As in the header of `ExactPre.lean`, except:

* The challenge oracle `SM_DT_PRE_challengeOracle` draws, at each accepted query `t`, a planted
  input `x ← M'` uniformly and answers `th.eval pk t (emb x)`.  Here the planted inputs are drawn
  up front, `xs : Tw → Mp` uniform and independent of `P` and `Th`, and the accepted query `t`
  is answered `some (Th (P, (t, emb (xs t))))` (`genPreCh`).  Since a tweak is accepted at most
  once this is the same distribution.
* Win (`genPreWin`): the `j`-th entry `t` of the challenge history exists and
  `Th (P, (t, m)) = Th (P, (t, emb (xs t)))`, for the adversary's `(j, m) : ℕ × Msg`.
* VCVio's `emb : M' → M` with `emb_injective` is the embedding `emb : Mp ↪ Msg`.
* In VCVio `adv.invert` returns `(j, m) : ℕ × M'` and the win is
  `th.eval pk t (emb m) = th.eval pk t (emb x)`.  The game `genPreExp` lets the second phase
  return an arbitrary `m : Msg` (a stronger adversary); the literal shape, with the result in
  `ℕ × Mp`, is `genPreSubExp` (`gen_pre_sub_exact_le`, same bound).

The challenger state (`PreState`, `preInit`), the table-driven challenger `preChT`, and the
generic two-phase infrastructure are those of `ExactPre.lean`.

## Result

`gen_pre_exact_le`: `Pr[win] ≤ (√((2 q₂ + 1)² (1/|Y| + 1/|Mp|)) + 2 q₁ / √|Sd|)²`.

`genPreExp_refl`: at `Mp = Msg`, `emb = Function.Embedding.refl Msg` the game is `preExp`.
-/

open MeasureTheory ENNReal Quantum Matrix
open scoped Kronecker ComplexOrder

universe u v w

set_option linter.unusedSectionVars false

namespace PQ.QROM

variable {Sd Tw Msg Mp Y : Type}

/-- The two classical oracles of SM-DT-PRE for the planted inputs `xs : Tw → Mp`, embedded into
the messages by `emb`, and the row `a` of the hash at the seed: an accepted challenge query `t`
is answered `a (t, emb (xs t))`. -/
def genPreCh [DecidableEq Tw] (cap : ℕ) (emb : Mp ↪ Msg) (xs : Tw → Mp) (a : Tw × Msg → Y) :
    Tw ⊕ (Tw × Msg) → PreState Tw Msg → Option Y × PreState Tw Msg :=
  preChT cap (fun t ↦ a (t, emb (xs t))) a

/-- The winning condition of SM-DT-PRE: the result `(j, m)` names a recorded target tweak `t`
and a message with the image of the embedded planted input of `t` under the row `a`. -/
def genPreWin (emb : Mp ↪ Msg) (xs : Tw → Mp) (a : Tw × Msg → Y) (r : ℕ × Msg)
    (s : PreState Tw Msg) : Prop :=
  ∃ t, s.chal[r.1]? = some t ∧ a (t, r.2) = a (t, emb (xs t))

/-! ## The experiment -/

section Exp

variable [Fintype Sd] [DecidableEq Sd] [Fintype Tw] [DecidableEq Tw] [Fintype Msg]
  [DecidableEq Msg] [Fintype Mp] [DecidableEq Mp] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
  {L : LocalSig.{u, v}} {Out : QReg → Type w} {A : QReg}

/-- **The exact SM-DT-PRE experiment in the QROM** (target cap `cap`), with planted inputs of
type `Mp` embedded by `emb`: the probability, over the uniform planted inputs `xs : Tw → Mp`, the uniform seed `P`, the uniform hash `Th` and the run, that
the two-phase quantum adversary `(x, ph2)` started on `ρ` wins. -/
noncomputable def genPreExp (I : L.Interp) (ρ : SubState A) (cap n : ℕ) (emb : Mp ↪ Msg)
    (x : IAdv L (qrom2Spec (Dom Sd Tw Msg) Y) (Tw ⊕ (Tw × Msg)) (Option Y) Out n A)
    (ph2 : Sd → ∀ u, Out u →
      QuantumComp L (qrom2Spec (Dom Sd Tw Msg) Y) (fun _ ↦ ℕ × Msg) u) : ℝ≥0∞ :=
  avg fun xs : Tw → Mp ↦
    twoPhaseExp I ρ (genPreCh cap emb xs) preInit n x ph2 (genPreWin emb xs)

variable {I : L.Interp} {ρ : SubState A} {cap n q₁ q₂ : ℕ} {emb : Mp ↪ Msg}
  {x : IAdv L (qrom2Spec (Dom Sd Tw Msg) Y) (Tw ⊕ (Tw × Msg)) (Option Y) Out n A}
  {ph2 : Sd → ∀ u, Out u → QuantumComp L (qrom2Spec (Dom Sd Tw Msg) Y) (fun _ ↦ ℕ × Msg) u}

/-- What the leaf with histories `t` has seen: the target values of its target tweaks and the
values of the row at its collection queries. -/
def genPreSeen (t : PreState Tw Msg) (yv : Tw → Option Y) (R : Tw × Msg → Y) (_ : Tw → Mp) :
    (Tw → Y) × (Tw × Msg → Y) :=
  (fun tw ↦ if tw ∈ t.chal then (yv tw).getD 0 else 0, fun tm ↦ if tm ∈ t.coll then R tm else 0)

theorem genPre_postOf_eq_seen (F : Dom Sd Tw Msg → Y) (R : Tw × Msg → Y) (xs : Tw → Mp)
    (p : Σ u, Out u × PreState Tw Msg) :
    postOf I ρ (genPreCh cap emb xs) preInit n x F R p =
      prePost I ρ cap n x F p
        (genPreSeen p.2.2 (tvals (fun tw ↦ decide (tw ∈ p.2.2.chal)) R (emb ∘ xs)) R xs) := by
  obtain ⟨u, o, t⟩ := p
  unfold postOf prePost genPreCh
  exact DFunLike.congr_fun (flat_branch_congr (twoRuntime fun _ ↦ F) I
    (preChT cap (fun tw ↦ R (tw, emb (xs tw))) R)
    (preChT cap _ _) PreState.Ext (fun _ ↦ ⟨List.prefix_refl _, List.prefix_refl _⟩)
    (fun req s t ↦ preChT_ext cap _ _ req s t) (fun req s t ↦ preChT_ext cap _ _ req s t) t
    (preChT_loc cap _ _ _ _ t (fun tw htw ↦ by simp [genPreSeen, tvals, htw])
      (fun tm htm ↦ by simp [genPreSeen, htm])) n preInit x u o) (joint ρ)

/-- **The preimage step.** In the hybrid game the adversary wins with probability at most
`(2 q₂ + 1)² (1/|Y| + 1/|Mp|)`, on average over the planted inputs. -/
theorem avg_twoPhaseHyb_genPre_le [Inhabited Tw] {Res : Type} (d : Res → ℕ × Msg)
    {ph2 : Sd → ∀ u, Out u → QuantumComp L (qrom2Spec (Dom Sd Tw Msg) Y) (fun _ ↦ Res) u}
    (hx : IAdv.IsQueryBound n x (firstBudget q₁))
    (h2 : ∀ P u o, (ph2 P u o).IsQueryBound (secondBudget q₂)) :
    (avg fun xs : Tw → Mp ↦
      twoPhaseHyb I ρ (genPreCh cap emb xs) preInit n x ph2
        (fun a r s ↦ genPreWin emb xs a (d r) s)) ≤
      (2 * (q₂ : ℝ≥0∞) + 1) ^ 2 *
        ((Fintype.card Y : ℝ≥0∞)⁻¹ + (Fintype.card Mp : ℝ≥0∞)⁻¹) := by
  refine avg_twoPhaseHyb_le_of_leaf (ch := fun xs : Tw → Mp ↦ genPreCh cap emb xs)
    (win := fun xs a r s ↦ genPreWin emb xs a (d r) s)
    hx fun P F p ↦ ?_
  have hτ : ∀ ya, (prePost I ρ cap n x F p ya).PosSemidef := fun ya ↦
    ((twoRuntime fun _ ↦ F).run I
      (phase1 (preChT cap ya.1 ya.2) preInit n x)).posSemidef_branch_apply p (joint_posSemidef ρ)
  let M : (Tw → Y) × (Tw × Msg → Y) → HybridModel (Dom Sd Tw Msg) Y Res q₂ := fun ya ↦
    HybridModel.ofSecondPort I F (ph2 P p.1 p.2.1) (prePost I ρ cap n x F p ya) (hτ ya) q₂
      (h2 P p.1 p.2.1) Sigma.snd
  let out : (Tw → Y) × (Tw × Msg → Y) → Res → Tw × Msg := fun _ l ↦
    ((p.2.2.chal[(d l).1]?).getD default, (d l).2)
  have h := gen_pre_embedded_obs_weighted_le emb (rowEmb P) F (fun tw ↦ decide (tw ∈ p.2.2.chal))
    (genPreSeen p.2.2)
    (fun k hk yv R xs v ↦ by
      have hk' : k.1 ∈ p.2.2.chal := by simpa using hk
      unfold genPreSeen
      refine Prod.ext rfl ?_
      funext tm
      simp only
      split_ifs with hm
      · exact Function.update_of_ne (fun heq ↦ p.2.2.disj tm hm (by rw [heq]; exact hk')) _ _
      · rfl)
    (fun _ _ _ _ _ _ ↦ rfl) M out fun ya ↦ ENNReal.ofReal (prePost I ρ cap n x F p ya).trace.re
  have hconv : ∀ f : (Tw × Msg → Y) → (Tw → Mp) → ℝ≥0∞,
      (avg fun xs : Tw → Mp ↦ avg fun R : Tw × Msg → Y ↦ f R xs) =
        ∑ R : Tw × Msg → Y, ∑ xs : Tw → Mp,
          ((Fintype.card (Tw × Msg → Y) : ℝ≥0∞)⁻¹ * (Fintype.card (Tw → Mp) : ℝ≥0∞)⁻¹) *
            f R xs := by
    intro f
    unfold avg
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun R _ ↦ Finset.sum_congr rfl fun xs _ ↦ by
      rw [← mul_assoc, mul_comm (Fintype.card (Tw → Mp) : ℝ≥0∞)⁻¹]
  rw [hconv, hconv]
  refine le_trans (Finset.sum_le_sum fun R _ ↦ Finset.sum_le_sum fun xs _ ↦
    mul_le_mul' le_rfl ?_) (le_trans h (le_of_eq ?_))
  · rw [HybridModel.ofSecondPort_prob, genPre_postOf_eq_seen, ← patchRow_eq_patch]
    refine leafProb_mono _ _ fun l hl ↦ ?_
    obtain ⟨t, hget, heq⟩ := hl
    have hmem : t ∈ p.2.2.chal := List.mem_of_getElem? hget
    refine ⟨?_, ?_⟩
    · simp only [out, hget, Option.getD_some]
      simpa using hmem
    · simp only [out, hget, Option.getD_some]
      exact heq
  · congr 1
    exact Finset.sum_congr rfl fun R _ ↦ Finset.sum_congr rfl fun xs _ ↦ by
      rw [genPre_postOf_eq_seen]

/-- Square-root form for an arbitrary result type `Res` decoded by `d : Res → ℕ × Msg`. -/
theorem genPre_dec_exact_sqrt_le [Inhabited Tw] {Res : Type} (d : Res → ℕ × Msg)
    {ph2 : Sd → ∀ u, Out u → QuantumComp L (qrom2Spec (Dom Sd Tw Msg) Y) (fun _ ↦ Res) u}
    (hx : IAdv.IsQueryBound n x (firstBudget q₁))
    (h2 : ∀ P u o, (ph2 P u o).IsQueryBound (secondBudget q₂)) :
    (avg fun xs : Tw → Mp ↦ twoPhaseExp I ρ (genPreCh cap emb xs) preInit n x ph2
        (fun a r s ↦ genPreWin emb xs a (d r) s)) ^ (2⁻¹ : ℝ) ≤
      ((2 * (q₂ : ℝ≥0∞) + 1) ^ 2 *
        ((Fintype.card Y : ℝ≥0∞)⁻¹ + (Fintype.card Mp : ℝ≥0∞)⁻¹)) ^ (2⁻¹ : ℝ) +
        2 * q₁ * ((Fintype.card Sd : ℝ≥0∞)⁻¹) ^ (2⁻¹ : ℝ) := by
  have h := sqrt_avg_le
    (fun xs : Tw → Mp ↦ twoPhaseExp I ρ (genPreCh cap emb xs) preInit n x ph2
      (fun a r s ↦ genPreWin emb xs a (d r) s))
    (fun xs ↦ twoPhaseHyb I ρ (genPreCh cap emb xs) preInit n x ph2
      (fun a r s ↦ genPreWin emb xs a (d r) s))
    (fun _ ↦ (2 * (q₁ : ℝ≥0∞) * ((Fintype.card Sd : ℝ≥0∞)⁻¹) ^ (2⁻¹ : ℝ)) ^ 2)
    (fun xs ↦ by rw [sqrt_sq]; exact seed_hiding hx h2)
  refine h.trans (add_le_add (sqrt_le_sqrt (avg_twoPhaseHyb_genPre_le d hx h2)) ?_)
  refine (sqrt_le_sqrt (avg_le fun _ ↦ le_rfl)).trans ?_
  rw [sqrt_sq]

/-- **SM-DT-PRE in the QROM, exact adaptive two-phase game, planted inputs in `Mp`**,
square-root form. -/
theorem gen_pre_exact_sqrt_le [Inhabited Tw]
    (hx : IAdv.IsQueryBound n x (firstBudget q₁))
    (h2 : ∀ P u o, (ph2 P u o).IsQueryBound (secondBudget q₂)) :
    genPreExp I ρ cap n emb x ph2 ^ (2⁻¹ : ℝ) ≤
      ((2 * (q₂ : ℝ≥0∞) + 1) ^ 2 *
        ((Fintype.card Y : ℝ≥0∞)⁻¹ + (Fintype.card Mp : ℝ≥0∞)⁻¹)) ^ (2⁻¹ : ℝ) +
        2 * q₁ * ((Fintype.card Sd : ℝ≥0∞)⁻¹) ^ (2⁻¹ : ℝ) :=
  genPre_dec_exact_sqrt_le (I := I) (ρ := ρ) (cap := cap) (emb := emb) id hx h2

/-- **SM-DT-PRE in the QROM, exact adaptive two-phase game, planted inputs in `Mp`**:
`Pr[win] ≤ (√((2 q₂ + 1)² (1/|Y| + 1/|Mp|)) + 2 q₁ / √|Sd|)²`. -/
theorem gen_pre_exact_le [Inhabited Tw]
    (hx : IAdv.IsQueryBound n x (firstBudget q₁))
    (h2 : ∀ P u o, (ph2 P u o).IsQueryBound (secondBudget q₂)) :
    genPreExp I ρ cap n emb x ph2 ≤
      (((2 * (q₂ : ℝ≥0∞) + 1) ^ 2 *
        ((Fintype.card Y : ℝ≥0∞)⁻¹ + (Fintype.card Mp : ℝ≥0∞)⁻¹)) ^ (2⁻¹ : ℝ) +
        2 * q₁ * ((Fintype.card Sd : ℝ≥0∞)⁻¹) ^ (2⁻¹ : ℝ)) ^ 2 := by
  have h := gen_pre_exact_sqrt_le (I := I) (ρ := ρ) (cap := cap) (emb := emb) hx h2
  calc genPreExp I ρ cap n emb x ph2 = (genPreExp I ρ cap n emb x ph2 ^ (2⁻¹ : ℝ)) ^ 2 :=
        (sq_sqrt _).symm
    _ ≤ _ := pow_le_pow_left' h 2

/-- The experiment is a probability. -/
theorem genPreExp_le_one : genPreExp I ρ cap n emb x ph2 ≤ 1 :=
  avg_le fun _ ↦ twoPhaseExp_le_one

/-- At `Mp = Msg` and `emb` the identity embedding, the generalised game is the game `preExp` of
`ExactPre.lean`. -/
theorem genPreExp_refl
    (I : L.Interp) (ρ : SubState A) (cap n : ℕ)
    (x : IAdv L (qrom2Spec (Dom Sd Tw Msg) Y) (Tw ⊕ (Tw × Msg)) (Option Y) Out n A)
    (ph2 : Sd → ∀ u, Out u →
      QuantumComp L (qrom2Spec (Dom Sd Tw Msg) Y) (fun _ ↦ ℕ × Msg) u) :
    genPreExp I ρ cap n (Function.Embedding.refl Msg) x ph2 = preExp I ρ cap n x ph2 :=
  rfl

/-! ## The literal VCVio shape: the adversary's preimage is an element of `Mp`

In `SM_DT_PRE_Experiment` the second phase returns `(j, m) : ℕ × M'` and the win is
`th.eval pk t (emb m) = th.eval pk t (emb x)`.  This is the game `genPreExp` restricted to
adversaries whose preimage lies in the range of `emb`; it is stated separately here. -/

/-- The winning condition of SM-DT-PRE with the adversary's preimage in `Mp`. -/
def genPreSubWin (emb : Mp ↪ Msg) (xs : Tw → Mp) (a : Tw × Msg → Y) (r : ℕ × Mp)
    (s : PreState Tw Msg) : Prop :=
  ∃ t, s.chal[r.1]? = some t ∧ a (t, emb r.2) = a (t, emb (xs t))

/-- **The exact SM-DT-PRE experiment in the QROM, the adversary's preimage in `Mp`**: as
`genPreExp`, the second phase returning `(j, m) : ℕ × Mp` and winning iff
`Th (P, (t, emb m)) = Th (P, (t, emb (xs t)))` for the `j`-th target tweak `t`. -/
noncomputable def genPreSubExp (I : L.Interp) (ρ : SubState A) (cap n : ℕ) (emb : Mp ↪ Msg)
    (x : IAdv L (qrom2Spec (Dom Sd Tw Msg) Y) (Tw ⊕ (Tw × Msg)) (Option Y) Out n A)
    (ph2 : Sd → ∀ u, Out u →
      QuantumComp L (qrom2Spec (Dom Sd Tw Msg) Y) (fun _ ↦ ℕ × Mp) u) : ℝ≥0∞ :=
  avg fun xs : Tw → Mp ↦
    twoPhaseExp I ρ (genPreCh cap emb xs) preInit n x ph2 (genPreSubWin emb xs)

variable {ph2' : Sd → ∀ u, Out u → QuantumComp L (qrom2Spec (Dom Sd Tw Msg) Y) (fun _ ↦ ℕ × Mp) u}

/-- Square-root form of `gen_pre_sub_exact_le`. -/
theorem gen_pre_sub_exact_sqrt_le [Inhabited Tw]
    (hx : IAdv.IsQueryBound n x (firstBudget q₁))
    (h2 : ∀ P u o, (ph2' P u o).IsQueryBound (secondBudget q₂)) :
    genPreSubExp I ρ cap n emb x ph2' ^ (2⁻¹ : ℝ) ≤
      ((2 * (q₂ : ℝ≥0∞) + 1) ^ 2 *
        ((Fintype.card Y : ℝ≥0∞)⁻¹ + (Fintype.card Mp : ℝ≥0∞)⁻¹)) ^ (2⁻¹ : ℝ) +
        2 * q₁ * ((Fintype.card Sd : ℝ≥0∞)⁻¹) ^ (2⁻¹ : ℝ) :=
  genPre_dec_exact_sqrt_le (I := I) (ρ := ρ) (cap := cap) (emb := emb)
    (fun r : ℕ × Mp ↦ (r.1, emb r.2)) hx h2

/-- **SM-DT-PRE in the QROM, exact adaptive two-phase game, the adversary's preimage in `Mp`**:
`Pr[win] ≤ (√((2 q₂ + 1)² (1/|Y| + 1/|Mp|)) + 2 q₁ / √|Sd|)²`. -/
theorem gen_pre_sub_exact_le [Inhabited Tw]
    (hx : IAdv.IsQueryBound n x (firstBudget q₁))
    (h2 : ∀ P u o, (ph2' P u o).IsQueryBound (secondBudget q₂)) :
    genPreSubExp I ρ cap n emb x ph2' ≤
      (((2 * (q₂ : ℝ≥0∞) + 1) ^ 2 *
        ((Fintype.card Y : ℝ≥0∞)⁻¹ + (Fintype.card Mp : ℝ≥0∞)⁻¹)) ^ (2⁻¹ : ℝ) +
        2 * q₁ * ((Fintype.card Sd : ℝ≥0∞)⁻¹) ^ (2⁻¹ : ℝ)) ^ 2 := by
  have h := gen_pre_sub_exact_sqrt_le (I := I) (ρ := ρ) (cap := cap) (emb := emb) hx h2
  calc genPreSubExp I ρ cap n emb x ph2' = (genPreSubExp I ρ cap n emb x ph2' ^ (2⁻¹ : ℝ)) ^ 2 :=
        (sq_sqrt _).symm
    _ ≤ _ := pow_le_pow_left' h 2

/-- The experiment is a probability. -/
theorem genPreSubExp_le_one : genPreSubExp I ρ cap n emb x ph2' ≤ 1 :=
  avg_le fun _ ↦ twoPhaseExp_le_one

end Exp

end PQ.QROM

#print axioms PQ.QROM.avg_twoPhaseHyb_genPre_le
#print axioms PQ.QROM.gen_pre_exact_sqrt_le
#print axioms PQ.QROM.gen_pre_exact_le
#print axioms PQ.QROM.genPreExp_le_one
#print axioms PQ.QROM.genPreExp_refl
#print axioms PQ.QROM.gen_pre_sub_exact_sqrt_le
#print axioms PQ.QROM.gen_pre_sub_exact_le
#print axioms PQ.QROM.genPreSubExp_le_one
