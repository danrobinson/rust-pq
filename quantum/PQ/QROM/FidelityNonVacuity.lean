import PQ.QROM.ExactPre

/-!
# Positive-probability non-vacuity of the exact games

A one-request adversary: phase 1 sends one classical request and stops; phase 2 outputs a fixed
result.  Its winning probability in a two-phase game is computed exactly
(`fidNv_realProb`), which gives, on the trivial register with no quantum query at all:

* `fidNv_tcrExp`: the adversary that asks for the target `(t₀, m₀)` and outputs `(0, m₁)`,
  `m₁ ≠ m₀`, wins the exact SM-DT-TCR game with the probability that `Th (P, t₀, m₁) =
  Th (P, t₀, m₀)`; this is `1` when `|Y| = 1` (`fidNv_tcrExp_eq_one`) and positive for every `Y`
  (`fidNv_tcrExp_pos`).
* `fidNv_preExp`, `fidNv_preExp_eq_one`, `fidNv_preExp_pos`: the same for the exact SM-DT-PRE
  game and the adversary that asks for the tweak `t₀` and outputs `(0, m)`.

So the winning conditions of the exact games are satisfiable and the experiments are not
identically zero.
-/

open MeasureTheory ENNReal Quantum Matrix
open scoped Kronecker ComplexOrder

universe u v

set_option linter.unusedSectionVars false

namespace PQ.QROM

variable {Sd Tw Msg Y : Type} [Fintype Sd] [DecidableEq Sd] [Fintype Tw] [DecidableEq Tw]
  [Fintype Msg] [DecidableEq Msg] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
  {L : LocalSig.{u, v}} {Req Resp St Res : Type}

/-- Phase 1 of the one-request adversary: send `req`, ignore the response, stop. -/
def fidNvAdv (L : LocalSig.{u, v}) (Sd Tw Msg Y : Type) [Fintype Sd] [DecidableEq Sd]
    [Fintype Tw] [DecidableEq Tw] [Fintype Msg] [DecidableEq Msg] [Fintype Y] [DecidableEq Y]
    {Resp : Type} (req : Req) :
    IAdv L (qrom2Spec (Dom Sd Tw Msg) Y) Req Resp (fun _ ↦ Unit) 1 (QReg.of Unit) :=
  QuantumComp.pure (X := fun u ↦ Unit ⊕ (Req × (Resp →
    IAdv L (qrom2Spec (Dom Sd Tw Msg) Y) Req Resp (fun _ ↦ Unit) 0 u)))
    (.inr (req, fun _ ↦ QuantumComp.pure (X := fun _ ↦ Unit) ()))

/-- Phase 2 of the one-request adversary: output `r`. -/
def fidNvPh2 (L : LocalSig.{u, v}) (Sd Tw Msg Y : Type) [Fintype Sd] [DecidableEq Sd]
    [Fintype Tw] [DecidableEq Tw] [Fintype Msg] [DecidableEq Msg] [Fintype Y] [DecidableEq Y]
    (r : Res) : Sd → ∀ u, Unit → QuantumComp L (qrom2Spec (Dom Sd Tw Msg) Y) (fun _ ↦ Res) u :=
  fun _ _ _ ↦ QuantumComp.pure r

theorem fidNv_trace : ENNReal.ofReal (joint (A := QReg.of Unit) (SubState.basis ())).trace.re = 1 := by
  unfold joint
  rw [SubState.matrix_basis, Matrix.single_kronecker_single, one_mul,
    Matrix.trace_single_eq_same, Complex.one_re, ENNReal.ofReal_one]

/-- The one-request adversary wins exactly when the result `r` wins against the challenger
state after the request. -/
theorem fidNv_realProb (I : L.Interp) (ch : (Tw × Msg → Y) → Req → St → Resp × St) (s₀ : St)
    (win : (Tw × Msg → Y) → Res → St → Prop) (req : Req) (r : Res) (P : Sd)
    (Th : Dom Sd Tw Msg → Y) :
    realProb I (A := QReg.of Unit) (SubState.basis ()) ch s₀ 1 (fidNvAdv L Sd Tw Msg Y req)
        (fidNvPh2 L Sd Tw Msg Y r) win P Th =
      ind (win (rowOf Th P) r (ch (rowOf Th P) req s₀).2) := by
  unfold realProb
  have e : composite (ch (rowOf Th P)) s₀ 1 (fidNvAdv L Sd Tw Msg Y req)
      (fidNvPh2 L Sd Tw Msg Y r) P =
      QuantumComp.pure (X := fun _ ↦ Res × St) (r, (ch (rowOf Th P) req s₀).2) := rfl
  rw [e, leafProb_pure, fidNv_trace, one_mul]
  rfl

theorem fidNv_avg_one {T : Type} [Fintype T] [Nonempty T] : avg (fun _ : T ↦ (1 : ℝ≥0∞)) = 1 := by
  unfold avg
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    ENNReal.mul_inv_cancel (by simp) (ENNReal.natCast_ne_top _)]

theorem fidNv_avg_pos {T : Type} [Fintype T] {f : T → ℝ≥0∞} (t : T) (h : 0 < f t) :
    0 < avg f := by
  unfold avg
  refine lt_of_lt_of_le ?_ (Finset.single_le_sum (fun _ _ ↦ zero_le) (Finset.mem_univ t))
  exact ENNReal.mul_pos (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top _)) h.ne'

/-! ## SM-DT-TCR -/

/-- **The exact SM-DT-TCR game, computed on a one-target adversary**: ask for the target
`(t₀, m₀)`, output `(0, m₁)` with `m₁ ≠ m₀`. -/
theorem fidNv_tcrExp (I : L.Interp) {cap : ℕ} (hcap : 0 < cap) (t₀ : Tw) {m₀ m₁ : Msg}
    (hm : m₁ ≠ m₀) :
    tcrExp I (A := QReg.of Unit) (SubState.basis ()) cap 1
        (fidNvAdv L Sd Tw Msg Y (Sum.inl (t₀, m₀))) (fidNvPh2 L Sd Tw Msg Y (0, m₁)) =
      avg fun P : Sd ↦ avg fun Th : Dom Sd Tw Msg → Y ↦
        ind (Th (P, (t₀, m₁)) = Th (P, (t₀, m₀))) := by
  unfold tcrExp twoPhaseExp
  refine avg_congr fun P ↦ avg_congr fun Th ↦ ?_
  rw [fidNv_realProb]
  have hs : (tcrCh cap (rowOf Th P) (Sum.inl (t₀, m₀)) tcrInit).2.chal = [(t₀, m₀)] := by
    simp [tcrCh, tcrInit, Nat.not_le.2 hcap]
  by_cases h : Th (P, (t₀, m₁)) = Th (P, (t₀, m₀))
  · rw [ind_of_true h, ind_of_true]
    exact ⟨t₀, m₀, by rw [hs]; rfl, hm, h⟩
  · rw [ind_of_false h, ind_of_false]
    rintro ⟨t, mj, hget, -, heq⟩
    rw [hs] at hget
    simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hget
    obtain ⟨rfl, rfl⟩ := hget
    exact h heq

/-- With one hash value the one-target adversary wins the exact SM-DT-TCR game with
probability one. -/
theorem fidNv_tcrExp_eq_one [Subsingleton Y] [Nonempty Sd] (I : L.Interp) {cap : ℕ}
    (hcap : 0 < cap) (t₀ : Tw) {m₀ m₁ : Msg} (hm : m₁ ≠ m₀) :
    tcrExp I (A := QReg.of Unit) (SubState.basis ()) cap 1
        (fidNvAdv L Sd Tw Msg Y (Sum.inl (t₀, m₀))) (fidNvPh2 L Sd Tw Msg Y (0, m₁)) = 1 := by
  rw [fidNv_tcrExp I hcap t₀ hm]
  simp only [ind_of_true (Subsingleton.elim _ _), fidNv_avg_one]

/-- The exact SM-DT-TCR experiment is positive on the one-target adversary, for every `Y`. -/
theorem fidNv_tcrExp_pos [Nonempty Sd] (I : L.Interp) {cap : ℕ}
    (hcap : 0 < cap) (t₀ : Tw) {m₀ m₁ : Msg} (hm : m₁ ≠ m₀) :
    0 < tcrExp I (A := QReg.of Unit) (SubState.basis ()) cap 1
        (fidNvAdv L Sd Tw Msg Y (Sum.inl (t₀, m₀))) (fidNvPh2 L Sd Tw Msg Y (0, m₁)) := by
  rw [fidNv_tcrExp I hcap t₀ hm]
  obtain ⟨P⟩ := ‹Nonempty Sd›
  refine fidNv_avg_pos P (fidNv_avg_pos (fun _ ↦ (0 : Y)) ?_)
  rw [ind_of_true rfl]
  exact one_pos

/-! ## SM-DT-PRE -/

/-- **The exact SM-DT-PRE game, computed on a one-target adversary**: ask for the tweak `t₀`,
output `(0, m)`. -/
theorem fidNv_preExp (I : L.Interp) {cap : ℕ} (hcap : 0 < cap) (t₀ : Tw) (m : Msg) :
    preExp I (A := QReg.of Unit) (SubState.basis ()) cap 1
        (fidNvAdv L Sd Tw Msg Y (Sum.inl t₀)) (fidNvPh2 L Sd Tw Msg Y (0, m)) =
      avg fun xs : Tw → Msg ↦ avg fun P : Sd ↦ avg fun Th : Dom Sd Tw Msg → Y ↦
        ind (Th (P, (t₀, m)) = Th (P, (t₀, xs t₀))) := by
  unfold preExp twoPhaseExp
  refine avg_congr fun xs ↦ avg_congr fun P ↦ avg_congr fun Th ↦ ?_
  rw [fidNv_realProb]
  have hs : (preCh cap xs (rowOf Th P) (Sum.inl t₀) preInit).2.chal = [t₀] := by
    simp [preCh, preChT, preInit, Nat.not_le.2 hcap]
  by_cases h : Th (P, (t₀, m)) = Th (P, (t₀, xs t₀))
  · rw [ind_of_true h, ind_of_true]
    exact ⟨t₀, by rw [hs]; rfl, h⟩
  · rw [ind_of_false h, ind_of_false]
    rintro ⟨t, hget, heq⟩
    rw [hs] at hget
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
    subst hget
    exact h heq

/-- With one hash value the one-target adversary wins the exact SM-DT-PRE game with
probability one. -/
theorem fidNv_preExp_eq_one [Subsingleton Y] [Nonempty Sd] [Nonempty Msg] (I : L.Interp)
    {cap : ℕ} (hcap : 0 < cap) (t₀ : Tw) (m : Msg) :
    preExp I (A := QReg.of Unit) (SubState.basis ()) cap 1
        (fidNvAdv L Sd Tw Msg Y (Sum.inl t₀)) (fidNvPh2 L Sd Tw Msg Y (0, m)) = 1 := by
  rw [fidNv_preExp I hcap t₀ m]
  simp only [ind_of_true (Subsingleton.elim _ _), fidNv_avg_one]

/-- The exact SM-DT-PRE experiment is positive on the one-target adversary, for every `Y`. -/
theorem fidNv_preExp_pos [Nonempty Sd] (I : L.Interp) {cap : ℕ} (hcap : 0 < cap) (t₀ : Tw)
    (m : Msg) :
    0 < preExp I (A := QReg.of Unit) (SubState.basis ()) cap 1
        (fidNvAdv L Sd Tw Msg Y (Sum.inl t₀)) (fidNvPh2 L Sd Tw Msg Y (0, m)) := by
  rw [fidNv_preExp I hcap t₀ m]
  obtain ⟨P⟩ := ‹Nonempty Sd›
  refine fidNv_avg_pos (fun _ ↦ m) (fidNv_avg_pos P (fidNv_avg_pos (fun _ ↦ (0 : Y)) ?_))
  rw [ind_of_true rfl]
  exact one_pos

end PQ.QROM

#print axioms PQ.QROM.fidNv_tcrExp
#print axioms PQ.QROM.fidNv_tcrExp_eq_one
#print axioms PQ.QROM.fidNv_tcrExp_pos
#print axioms PQ.QROM.fidNv_preExp
#print axioms PQ.QROM.fidNv_preExp_eq_one
#print axioms PQ.QROM.fidNv_preExp_pos
