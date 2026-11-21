import Ideal.Games.MsgPrfBad

/-!
# PRF security of the HMAC-shaped keyed function in the ideal-compression model

`Ideal.macAdvantageI_le`: for

`mac_g(k, d) = out (g (g (IV, ok k), ob (mdFold g (g (IV, ik k)) (b₁ :: rest))))`, `(b₁, rest) = ib d`,

with `g` a uniformly random compression table that the distinguisher can query, a distinguisher
making at most `q` compression queries and `qO` function queries, each with at most `L` inner
blocks after the first one, has advantage at most

`2 q / |K| + (3 q + qO (1 + 3 L) + 3 + (q + qO (1 + L))²) / |St|`.

Proof.
* `prT_real_le_hyb`, `prT_badGame1_le` (files `MsgPrfHop`, `MsgPrfBad`): the real game is the
  hybrid game, in which the function oracle is `d ↦ out (TO (ob (mdFold g (TI b₁) rest)))` for
  private uniform row tables `TI`, `TO`, up to the bad event.
* `prT_lazy_rename_le` (file `MsgPrfLazy`): for fixed `g`, `TI` the hybrid oracle is a lazy
  random function unless two distinct queried inputs have the same inner digest.
* `collB_of_collφ` (Merkle–Damgård, `coll_of_chainI_eq`): such inputs read two distinct cells of
  `(g, TI)` with the same value; `prT_collφ_chain_le`: birthday bound `Prf.prT_coll_le` for the
  table-level program `HP.chainToT`.
* The same bound for the negated distinguisher gives the other direction of the distance.
-/

open OracleComp OracleSpec ENNReal PRFScheme

namespace Ideal.MsgPrf

open Ideal.HP Ideal.Prf

variable {St Blk K P M Y : Type}

theorem prT_swap3 {α β γ : Type} (ma : ProbComp α) (mb : ProbComp β) (mc : ProbComp γ)
    (f : α → β → γ → ProbComp Bool) :
    prT (ma >>= fun a => mb >>= fun b => mc >>= fun c => f a b c) =
      prT (mb >>= fun b => mc >>= fun c => ma >>= fun a => f a b c) := by
  rw [prT_swap]
  exact prT_bind_congr _ _ _ fun b _ => prT_swap _ _ _

/-! ## Inner-digest collisions are collisions of the tables -/

theorem collB_of_collφ [DecidableEq St] [DecidableEq Blk] [DecidableEq P] [DecidableEq M]
    (ib : P × M → Blk × List Blk) (hib : Function.Injective ib) (ob : St → Blk)
    (hob : Function.Injective ob) (g : CF St Blk) (TI : Blk → St)
    (l : List ((St × Blk) ⊕ (P × M))) (h : collφ (phi ib ob g TI) (dq l) = true) :
    collB (Sum.elim g TI) ((l.flatMap fun t => cellsQ g TI (toC ib t)).map id) = true := by
  simp only [collφ, decide_eq_true_eq] at h
  obtain ⟨d, hd, d', hd', hne, heq⟩ := h
  have hch : chainI g TI (ib d) = chainI g TI (ib d') := hob heq
  have hne' : ((ib d).1, (ib d).2) ≠ ((ib d').1, (ib d').2) := fun e =>
    hne (hib (Prod.ext (Prod.mk.inj e).1 (Prod.mk.inj e).2))
  obtain ⟨c, hc, c', hc', hcc, hJ⟩ :=
    coll_of_chainI_eq g TI (ib d).2 (ib d).1 (ib d').1 (ib d').2 hne' hch
  simp only [collB, decide_eq_true_eq, List.map_id]
  exact ⟨c, List.mem_flatMap.mpr ⟨.inr d, (mem_dq l d).mp hd, hc⟩,
    c', List.mem_flatMap.mpr ⟨.inr d', (mem_dq l d').mp hd', hc'⟩, hcc, hJ⟩

section Bound

variable [Fintype St] [DecidableEq St] [SampleableType St] [Fintype Blk] [DecidableEq Blk]
  [SampleableType (CF St Blk)] [DecidableEq P] [DecidableEq M]

/-- For a fixed outer row table, two queried inputs of the hybrid run have the same inner digest
with probability at most `(q + qO (1 + L))² / |St|` over `(g, TI)`. -/
theorem prT_collφ_chain_le (ib : P × M → Blk × List Blk) (hib : Function.Injective ib)
    (ob : St → Blk) (hob : Function.Injective ob) (out : St → Y) (A : PrfAdvI St Blk P M Y)
    (q qO L : ℕ) (hq : IsQueryBoundP A (fun i => isCompQ i = true) q)
    (hO : IsQueryBoundP A (fun i => isPrfQ i = true) qO)
    (hL : AllQueriesSatisfy A (ibLenLe ib L)) (TO : Blk → St) :
    prT ($ᵗ (CF St Blk) >>= fun g => $ᵗ (Blk → St) >>= fun TI =>
      (simulateQ (trImpl (hybAns ib ob out g TI TO)) A).run [] >>= fun z =>
        pure (collφ (phi ib ob g TI) (dq z.2))) ≤
      (((q + qO * (1 + L)) ^ 2 : ℕ) : ℝ≥0∞) * (Fintype.card St : ℝ≥0∞)⁻¹ := by
  have hn := isQueryBoundP_chainToT (chainProg ib ob out TO A) q qO L
    (chainProg_pub ib ob out TO A q hq) (chainProg_chain ib ob out TO A qO hO)
    (chainProg_len ib ob out TO A L hL)
  have hc := prT_coll_le (C := (St × Blk) ⊕ Blk) (V := St) (spec := hS St Blk + tS St Blk) id
    (fun J => tbl (fun q => J (.inl q)) (fun b => J (.inr b)))
    (fun J J' t h => by rcases t with q | b <;> exact h)
    (simulateQ chainToT (chainProg ib ob out TO A)) _ hn
  rw [prT_sumTable] at hc
  refine le_trans ?_ hc
  refine prT_bind_mono _ _ _ fun g _ => prT_bind_mono _ _ _ fun TI _ => ?_
  have e : (tbl (fun q => Sum.elim g TI (.inl q)) fun b => Sum.elim g TI (.inr b)) = tbl g TI :=
    rfl
  rw [e, run_trImpl_cells, bind_map_left]
  exact prT_bind_pure_mono _ _ _ fun z hz => collB_of_collφ ib hib ob hob g TI z.2 hz

/-- The hybrid game returns `true` at most as often as the ideal game, plus the collision
bound. -/
theorem prT_hyb_le_ideal [SampleableType Y] (ib : P × M → Blk × List Blk)
    (hib : Function.Injective ib) (ob : St → Blk) (hob : Function.Injective ob) (out : St → Y)
    (hout : ∀ p : Y → Prop, Pr{let u ← $ᵗ St}[p (out u)] = Pr{let y ← $ᵗ Y}[p y])
    (A : PrfAdvI St Blk P M Y) (q qO L : ℕ)
    (hq : IsQueryBoundP A (fun i => isCompQ i = true) q)
    (hO : IsQueryBoundP A (fun i => isPrfQ i = true) qO)
    (hL : AllQueriesSatisfy A (ibLenLe ib L)) :
    prT (hybGame ib ob out A) ≤ prT (prfIdealGameI A) +
      (((q + qO * (1 + L)) ^ 2 : ℕ) : ℝ≥0∞) * (Fintype.card St : ℝ≥0∞)⁻¹ := by
  have hg : ∀ (g : CF St Blk) (TI : Blk → St),
      prT ($ᵗ (Blk → St) >>= fun TO => simulateQ (ansImpl (hybAns ib ob out g TI TO)) A) ≤
        prT (prfIdealExperiment (A.inst g)) +
          prT ($ᵗ (Blk → St) >>= fun TO =>
            (simulateQ (trImpl (hybAns ib ob out g TI TO)) A).run [] >>= fun z =>
              pure (collφ (phi ib ob g TI) (dq z.2))) := fun g TI =>
    prT_lazy_rename_le g (phi ib ob g TI) out hout A
  have h1 : prT (hybGame ib ob out A) = prT ($ᵗ (CF St Blk) >>= fun g =>
      $ᵗ (Blk → St) >>= fun TI => $ᵗ (Blk → St) >>= fun TO =>
        simulateQ (ansImpl (hybAns ib ob out g TI TO)) A) := prT_swap3 _ _ _ _
  rw [h1]
  refine (prT_bind_le_add _ _ _ _ fun g => prT_bind_le_add _ _ _ _ fun TI => hg g TI).trans
    (add_le_add (le_of_eq ?_) ?_)
  · unfold prfIdealGameI
    exact prT_bind_congr _ _ _ fun g _ => prT_bind_const _ _
  · rw [← prT_swap3]
    exact prT_bind_le_of_forall_le _ _ fun TO _ =>
      prT_collφ_chain_le ib hib ob hob out A q qO L hq hO hL TO

variable [Fintype K] [SampleableType K] [SampleableType Y]

/-- **One-sided bound**: the real experiment returns `true` at most as often as the ideal one,
plus the bound. -/
theorem prT_macReal_le (IV : St) (ik ok : K → Blk) (hik : Function.Injective ik)
    (hok : Function.Injective ok) (hne : ∀ k, ik k ≠ ok k) (ib : P × M → Blk × List Blk)
    (hib : Function.Injective ib) (ob : St → Blk) (hob : Function.Injective ob) (out : St → Y)
    (hout : ∀ p : Y → Prop, Pr{let u ← $ᵗ St}[p (out u)] = Pr{let y ← $ᵗ Y}[p y])
    (A : PrfAdvI St Blk P M Y) (q qO L : ℕ)
    (hq : IsQueryBoundP A (fun i => isCompQ i = true) q)
    (hO : IsQueryBoundP A (fun i => isPrfQ i = true) qO)
    (hL : AllQueriesSatisfy A (ibLenLe ib L)) :
    prT (macRealGameI IV ik ok ib ob out A) ≤ prT (prfIdealGameI A) +
      (2 * (q : ℝ≥0∞) * (Fintype.card K : ℝ≥0∞)⁻¹ +
        ((3 * q + qO * (1 + 3 * L) + 3 + (q + qO * (1 + L)) ^ 2 : ℕ) : ℝ≥0∞) *
          (Fintype.card St : ℝ≥0∞)⁻¹) := by
  refine (prT_real_le_hyb IV ik ok ib ob out hne A).trans ?_
  refine (add_le_add (prT_hyb_le_ideal ib hib ob hob out hout A q qO L hq hO hL)
    (prT_badGame1_le IV ik ok hik hok ib ob out A q qO L hq hO hL)).trans (le_of_eq ?_)
  push_cast
  ring

end Bound

/-! ## Negating the distinguisher -/

theorem macRealGameI_not [SampleableType K] [SampleableType (CF St Blk)] [SampleableType Y]
    [DecidableEq P] [DecidableEq M] (IV : St) (ik ok : K → Blk) (ib : P × M → Blk × List Blk)
    (ob : St → Blk) (out : St → Y) (A : PrfAdvI St Blk P M Y) :
    macRealGameI IV ik ok ib ob out (negAdv A) = not <$> macRealGameI IV ik ok ib ob out A := by
  simp only [macRealGameI, negAdv, PrfAdvI.inst, prfRealExperiment, simulateQ_map, map_bind]

end Ideal.MsgPrf

namespace Ideal

open Ideal.HP Ideal.Prf Ideal.MsgPrf

variable {St Blk K P M Y : Type}

/-- **PRF security of the HMAC-shaped keyed function in the ideal-compression model.**  Let
`mac_g(k, d) = out (g (g (IV, ok k), ob (mdFold g (g (IV, ik k)) (b₁ :: rest))))` with
`(b₁, rest) = ib d`, where the key-block maps `ik`, `ok` are injective with `ik k ≠ ok k`, the
block maps `ib`, `ob` are injective and `out` of a uniform chaining value is uniform.  A
distinguisher making at most `q` compression queries and `qO` function queries, each with at most
`L` inner blocks after the first one, has advantage at most
`2 q / |K| + (3 q + qO (1 + 3 L) + 3 + (q + qO (1 + L))²) / |St|`. -/
theorem macAdvantageI_le [Fintype St] [DecidableEq St] [SampleableType St] [Fintype Blk]
    [DecidableEq Blk] [SampleableType (CF St Blk)] [DecidableEq P] [DecidableEq M] [Fintype K]
    [SampleableType K] [SampleableType Y]
    (IV : St) (ik ok : K → Blk) (hik : Function.Injective ik) (hok : Function.Injective ok)
    (hne : ∀ k, ik k ≠ ok k) (ib : P × M → Blk × List Blk) (hib : Function.Injective ib)
    (ob : St → Blk) (hob : Function.Injective ob) (out : St → Y)
    (hout : ∀ p : Y → Prop, Pr{let u ← $ᵗ St}[p (out u)] = Pr{let y ← $ᵗ Y}[p y])
    (A : PrfAdvI St Blk P M Y) (q qO L : ℕ)
    (hq : IsQueryBoundP A (fun i => isCompQ i = true) q)
    (hO : IsQueryBoundP A (fun i => isPrfQ i = true) qO)
    (hL : AllQueriesSatisfy A (ibLenLe ib L)) :
    macAdvantageI IV ik ok ib ob out A ≤
      2 * (q : ℝ≥0∞) * (Fintype.card K : ℝ≥0∞)⁻¹ +
        ((3 * q + qO * (1 + 3 * L) + 3 + (q + qO * (1 + L)) ^ 2 : ℕ) : ℝ≥0∞) *
          (Fintype.card St : ℝ≥0∞)⁻¹ := by
  unfold macAdvantageI
  refine MeasureTheory.Measure.boolDist_le_of_apply_le _ _ fun b => ?_
  cases b
  · have h := prT_macReal_le IV ik ok hik hok hne ib hib ob hob out hout (negAdv A) q qO L
      ((isQueryBoundP_map_iff _ _ _).mpr hq) ((isQueryBoundP_map_iff _ _ _).mpr hO) (by
        unfold AllQueriesSatisfy at hL ⊢
        exact (isQueryBound_map_iff _ _ _ _ _).mpr hL)
    rwa [macRealGameI_not, prfIdealGameI_not, prT_not_map, prT_not_map] at h
  · have h := prT_macReal_le IV ik ok hik hok hne ib hib ob hob out hout A q qO L hq hO hL
    rwa [prT_eq, prT_eq] at h

/-- The two one-sided forms of `macAdvantageI_le`. -/
theorem prT_mac_two_sided [Fintype St] [DecidableEq St] [SampleableType St] [Fintype Blk]
    [DecidableEq Blk] [SampleableType (CF St Blk)] [DecidableEq P] [DecidableEq M] [Fintype K]
    [SampleableType K] [SampleableType Y]
    (IV : St) (ik ok : K → Blk) (hik : Function.Injective ik) (hok : Function.Injective ok)
    (hne : ∀ k, ik k ≠ ok k) (ib : P × M → Blk × List Blk) (hib : Function.Injective ib)
    (ob : St → Blk) (hob : Function.Injective ob) (out : St → Y)
    (hout : ∀ p : Y → Prop, Pr{let u ← $ᵗ St}[p (out u)] = Pr{let y ← $ᵗ Y}[p y])
    (A : PrfAdvI St Blk P M Y) (q qO L : ℕ)
    (hq : IsQueryBoundP A (fun i => isCompQ i = true) q)
    (hO : IsQueryBoundP A (fun i => isPrfQ i = true) qO)
    (hL : AllQueriesSatisfy A (ibLenLe ib L)) :
    prT (macRealGameI IV ik ok ib ob out A) ≤ prT (prfIdealGameI A) +
        (2 * (q : ℝ≥0∞) * (Fintype.card K : ℝ≥0∞)⁻¹ +
          ((3 * q + qO * (1 + 3 * L) + 3 + (q + qO * (1 + L)) ^ 2 : ℕ) : ℝ≥0∞) *
            (Fintype.card St : ℝ≥0∞)⁻¹) ∧
      prT (prfIdealGameI A) ≤ prT (macRealGameI IV ik ok ib ob out A) +
        (2 * (q : ℝ≥0∞) * (Fintype.card K : ℝ≥0∞)⁻¹ +
          ((3 * q + qO * (1 + 3 * L) + 3 + (q + qO * (1 + L)) ^ 2 : ℕ) : ℝ≥0∞) *
            (Fintype.card St : ℝ≥0∞)⁻¹) := by
  have h := macAdvantageI_le IV ik ok hik hok hne ib hib ob hob out hout A q qO L hq hO hL
  unfold macAdvantageI at h
  rw [prT_eq, prT_eq]
  constructor
  · exact (MeasureTheory.Measure.apply_true_le_add_boolDist _ _).trans (add_le_add le_rfl h)
  · rw [MeasureTheory.Measure.boolDist_comm] at h
    exact (MeasureTheory.Measure.apply_true_le_add_boolDist _ _).trans (add_le_add le_rfl h)

end Ideal

#print axioms Ideal.macAdvantageI_le
#print axioms Ideal.prT_mac_two_sided
