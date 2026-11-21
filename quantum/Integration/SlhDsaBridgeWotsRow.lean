import Integration.SlhDsaComposedEnc
import Reduction.Open.Phase1Wots
import PQ.QROM.HybridPullback

/-!
# Rows of the `F`-component of `Thash` (shared by the WOTS-chain PRE and UD bridges)

NOT part of the default target; compiled as `scripts/check-integration.sh` step 3 does.

Own copies (names prefixed `wq`) of the row machinery of `Integration/SlhDsaBridgeTcr.lean` /
`Integration/SlhDsaBridgeTcrT.lean` (agent `qtcr`, files in flux), specialised where convenient:

* `wqRowT T pk R`: the `Thash` table `T` with its arity-one row at seed `pk` replaced by the
  `F`-row `R : Bytes 22 × BN → BN`; `wqRowOf`; `avΩ_wq_resample`: resampling that row does not
  change a uniform average over the worlds.
* `wqRowEmb`, `encΩ_wq_row_local`: the row embeds into the port domain, and the port function of
  `ω` with row `H` differs from that with row `G` only on the image of the points where `H ≠ G`
  (the locality hypothesis of `HybridModel.pullback`).
* `wq_kernel_rfl`: close an equation by `Eq.refl`, leaving the definitional check to the kernel.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal PQ.Interactive PQ.QROM Quantum
open scoped ComplexOrder

set_option linter.unusedSectionVars false

namespace Reduction

/-- `Thash` tables of the bounded world. -/
abbrev WqTab (c : Caps) : Type := BN → Bytes 22 → BList BN c.tl → BN

/-- Replace the `Thash` component. -/
abbrev FinFns.wqWithThash {p : Params} {c : Caps} (ω : FinFns p c)
    (T : Bytes p.n → Bytes 22 → BList (Bytes p.n) c.tl → Bytes p.n) : FinFns p c :=
  { ω with thash := T }

lemma wq_BList_ofList_congr {α : Type} {L : ℕ} {xs ys : List α} (h₁ : xs.length ≤ L)
    (h₂ : ys.length ≤ L) (h : xs = ys) : BList.ofList xs h₁ = BList.ofList ys h₂ := by
  subst h
  rfl

lemma wq_BList_ofList_ofFn {α : Type} {L : ℕ} (b : BList α L) (h : (List.ofFn b.2).length ≤ L) :
    BList.ofList (List.ofFn b.2) h = b := by
  obtain ⟨⟨k, hk⟩, f⟩ := b
  unfold BList.ofList
  have hl : (List.ofFn f).length = k := List.length_ofFn
  refine Sigma.ext (Fin.ext hl) ?_
  refine (Fin.heq_fun_iff hl).2 fun i ↦ ?_
  simp

/-- The value of a list of length one (its head). -/
def wqHead (xs : List BN) : BN := xs.headD default

/-- The table `T` with its arity-one row at seed `pk` replaced by `R`. -/
def wqRowT {c : Caps} (T : WqTab c) (pk : BN) (R : Bytes 22 × BN → BN) : WqTab c :=
  fun pk' a b ↦
    if pk' = pk ∧ (List.ofFn b.2).length = 1 then R (a, wqHead (List.ofFn b.2)) else T pk' a b

/-- The arity-one row of `T` at seed `pk`. -/
def wqRowOf {c : Caps} (hn : 1 ≤ c.tl) (T : WqTab c) (pk : BN) : Bytes 22 × BN → BN :=
  fun x ↦ T pk x.1 (BList.ofList [x.2] (by simpa using hn))

lemma wqRowT_single {c : Caps} (hn : 1 ≤ c.tl) (T : WqTab c) (pk : BN) (R : Bytes 22 × BN → BN)
    (a : Bytes 22) (y : BN) :
    wqRowT T pk R pk a (BList.ofList [y] (by simpa using hn)) = R (a, y) := by
  have hx : List.ofFn (BList.ofList (L := c.tl) [y] (by simpa using hn)).2 = [y] :=
    BList.ofFn_ofList _ _
  unfold wqRowT
  rw [if_pos ⟨rfl, by rw [hx]; rfl⟩, hx]
  rfl

lemma wqRowOf_wqRowT {c : Caps} (hn : 1 ≤ c.tl) (T : WqTab c) (pk : BN) (R : Bytes 22 × BN → BN) :
    wqRowOf hn (wqRowT T pk R) pk = R := by
  funext x
  exact wqRowT_single hn T pk R x.1 x.2

lemma wqRowT_wqRowOf {c : Caps} (hn : 1 ≤ c.tl) (T : WqTab c) (pk : BN) (R : Bytes 22 × BN → BN) :
    wqRowT (wqRowT T pk R) pk (wqRowOf hn T pk) = T := by
  funext pk' a b
  unfold wqRowT
  by_cases h : pk' = pk ∧ (List.ofFn b.2).length = 1
  · rw [if_pos h]
    obtain ⟨rfl, h2⟩ := h
    unfold wqRowOf
    dsimp only
    have hb : [wqHead (List.ofFn b.2)] = List.ofFn b.2 := by
      match hm : List.ofFn b.2, h2 with
      | [y], _ => rfl
    have hb' : BList.ofList [wqHead (List.ofFn b.2)] (by simpa using hn) = b :=
      (wq_BList_ofList_congr _ (by rw [← hb]; simpa using hn) hb).trans
        (wq_BList_ofList_ofFn b _)
    rw [hb']
  · rw [if_neg h, if_neg h]

/-- Resampling one `F`-row of `Thash` does not change a uniform average. -/
theorem avΩ_wq_resample (c : Caps) (hn : 1 ≤ c.tl) (pk : BN) (f : Ω128 c → ℝ≥0∞) :
    avΩ c f = avΩ c fun ω ↦ ∑ R : Bytes 22 × BN → BN,
      (Fintype.card (Bytes 22 × BN → BN) : ℝ≥0∞)⁻¹ * f (ω.wqWithThash (wqRowT ω.thash pk R)) := by
  classical
  unfold avΩ
  set u : ℝ≥0∞ := (Fintype.card (Ω128 c) : ℝ≥0∞)⁻¹ with hu
  have hw : ∀ ω : Ω128 c, unifW (Ω128 c) ω = u := fun _ ↦ rfl
  simp only [hw]
  set cG : ℝ≥0∞ := (Fintype.card (Bytes 22 × BN → BN) : ℝ≥0∞) with hcG
  have hne : cG ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hnt : cG ≠ ⊤ := ENNReal.natCast_ne_top _
  let Φ : Ω128 c × (Bytes 22 × BN → BN) → Ω128 c × (Bytes 22 × BN → BN) :=
    fun p ↦ (p.1.wqWithThash (wqRowT p.1.thash pk p.2), wqRowOf hn p.1.thash pk)
  have hΦ : Function.Involutive Φ := by
    rintro ⟨ω, R⟩
    simp only [Φ, FinFns.wqWithThash, wqRowOf_wqRowT, wqRowT_wqRowOf]
  have h := Equiv.sum_comp hΦ.toPerm fun p : Ω128 c × (Bytes 22 × BN → BN) ↦ f p.1
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type] at h
  have h' : ∑ ω : Ω128 c, ∑ R : Bytes 22 × BN → BN, f (ω.wqWithThash (wqRowT ω.thash pk R)) =
      cG * ∑ ω : Ω128 c, f ω := by
    refine h.trans ?_
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Finset.mul_sum, hcG]
  calc ∑ ω : Ω128 c, u * f ω = u * (cG⁻¹ * (cG * ∑ ω : Ω128 c, f ω)) := by
        rw [← mul_assoc cG⁻¹, ENNReal.inv_mul_cancel hne hnt, one_mul, Finset.mul_sum]
    _ = _ := by
        rw [← h', Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun ω _ ↦ ?_
        rw [Finset.mul_sum, Finset.mul_sum]

elab "wq_kernel_rfl" : tactic => Lean.Elab.Tactic.withMainContext do
  let g ← Lean.Elab.Tactic.getMainGoal
  let t := (← Lean.instantiateMVars (← g.getType)).consumeMData
  let some (_, a, _) := t.eq? | throwError "wq_kernel_rfl: not an equality"
  let pf ← Lean.Meta.mkEqRefl a
  g.assign pf
  Lean.Elab.Tactic.replaceMainGoal []

section rows

variable (c : Caps)

theorem wq_thash_rowT (ω : Ω128 c) (pk : BN) (R : Bytes 22 × BN → BN) (pk' : BN) (a : Bytes 22)
    (xs : List BN) :
    (primsΩ (ω.wqWithThash (wqRowT ω.thash pk R))).Thash pk' a xs =
      if h : xs.length ≤ c.tl then wqRowT ω.thash pk R pk' a (BList.ofList xs h) else default :=
  rfl

/-- `F` at the row world, on the row's seed, is the row. -/
theorem wq_F_row (hn : 1 ≤ c.tl) (ω : Ω128 c) (pk : BN) (R : Bytes 22 × BN → BN) (a : Bytes 22)
    (y : BN) : (primsΩ (ω.wqWithThash (wqRowT ω.thash pk R))).Thash pk a [y] = R (a, y) := by
  rw [wq_thash_rowT, dif_pos (by simpa using hn)]
  exact wqRowT_single hn ω.thash pk R a y

/-- `Thash` at the row world reads the row at tweak `a` only through `R (a, ·)`. -/
theorem wq_thash_row_local (ω : Ω128 c) (pk : BN) (R R' : Bytes 22 × BN → BN) (a : Bytes 22)
    (xs : List BN) (h : ∀ m, R (a, m) = R' (a, m)) :
    (primsΩ (ω.wqWithThash (wqRowT ω.thash pk R))).Thash pk a xs =
      (primsΩ (ω.wqWithThash (wqRowT ω.thash pk R'))).Thash pk a xs := by
  rw [wq_thash_rowT, wq_thash_rowT]
  split_ifs with hl
  · unfold wqRowT
    split_ifs with h2
    · exact h _
    · rfl
  · rfl

/-- The `F`-row embedding into the port domain. -/
def wqRowEmb (hn : 1 ≤ c.tl) (pk : BN) : Bytes 22 × BN ↪ EncX c where
  toFun x := Sum.inl (pk, x.1, BList.ofList [x.2] (by simpa using hn))
  inj' := by
    rintro ⟨a, x⟩ ⟨b, y⟩ h
    simp only [Sum.inl.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl, h⟩ := h
    have h1 := congrArg (fun z : BList BN c.tl ↦ List.ofFn z.2) h
    simp only [BList.ofFn_ofList, List.cons.injEq, and_true] at h1
    rw [h1]

theorem encΩ_wq_row_local (hn : 1 ≤ c.tl) (ω : Ω128 c) (pk : BN) (H G : Bytes 22 × BN → BN)
    (x : EncX c)
    (h : encΩ (ω.wqWithThash (wqRowT ω.thash pk H)) x ≠ encΩ (ω.wqWithThash (wqRowT ω.thash pk G)) x) :
    ∃ x', wqRowEmb c hn pk x' = x ∧ H x' ≠ G x' := by
  rcases x with ⟨pk', a, b⟩ | x | x | x
  · change (wqRowT ω.thash pk H pk' a b, (0 : Bytes Link.vp.params.m)) ≠
      (wqRowT ω.thash pk G pk' a b, 0) at h
    unfold wqRowT at h
    split_ifs at h with hc
    · obtain ⟨rfl, hl⟩ := hc
      refine ⟨(a, wqHead (List.ofFn b.2)), ?_, fun he ↦ h (by rw [he])⟩
      change Sum.inl (pk', a, BList.ofList [wqHead (List.ofFn b.2)] _) = Sum.inl (pk', a, b)
      have hb : [wqHead (List.ofFn b.2)] = List.ofFn b.2 := by
        match hm : List.ofFn b.2, hl with
        | [y], _ => rfl
      rw [(wq_BList_ofList_congr _ (by rw [← hb]; simpa using hn) hb).trans
        (wq_BList_ofList_ofFn b _)]
    · exact absurd rfl h
  · exact absurd rfl h
  · exact absurd rfl h
  · exact absurd rfl h

end rows

end Reduction

#print axioms Reduction.avΩ_wq_resample
#print axioms Reduction.wq_F_row
#print axioms Reduction.wq_thash_row_local
#print axioms Reduction.encΩ_wq_row_local
