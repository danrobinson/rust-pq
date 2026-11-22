import Ideal.Games.MsgPrf

/-!
# PRF security of the HMAC-shaped keyed function with finer accounting (shape marking)

`Ideal.macAdvantageI_le_marked`: the bound of `Ideal.macAdvantageI_le` with the key-guessing
term `2 q / |K|` replaced by `2 qM / |K|`, where `qM` bounds only the compression queries whose
block is an inner or outer key block, `∃ k, B = ik k ∨ B = ok k` (`MsgPrf.markK`).  The terms
over `|St|` still count every compression query.

Why: of the bad events charged to a compression query (`MsgPrf.Wev1`), the only one whose
probability involves the key is "the query is the cell `(IV, ik k)` or `(IV, ok k)`"; a query
whose block is neither an inner nor an outer key block, for any key, never satisfies it.
-/

open OracleComp OracleSpec ENNReal PRFScheme

namespace Ideal.MsgPrf

open Ideal.HP Ideal.Prf

variable {St Blk K P M Y : Type}

/-- A compression query at an inner or outer key block. -/
def markK (ik ok : K → Blk) : ℕ ⊕ ((St × Blk) ⊕ (P × M)) → Prop
  | .inr (.inl q) => ∃ k, q.2 = ik k ∨ q.2 = ok k
  | _ => False

noncomputable instance (ik ok : K → Blk) : DecidablePred (markK (St := St) (P := P) (M := M) ik ok) :=
  fun _ => Classical.propDecidable _

section Fixed

variable [Fintype St] [DecidableEq St] [DecidableEq Blk] [SampleableType St] [Fintype K]
  [SampleableType K]

open Classical in
/-- The weight charged to a traced query, marked form. -/
noncomputable def wt1M (K St : Type) [Fintype K] [Fintype St] {Blk : Type}
    (ik ok : K → Blk) (ib : P × M → Blk × List Blk) : (St × Blk) ⊕ (P × M) → ℝ≥0∞
  | .inl q => (if (∃ k, q.2 = ik k ∨ q.2 = ok k) then
        ((Fintype.card K : ℝ≥0∞)⁻¹ + (Fintype.card K : ℝ≥0∞)⁻¹) else 0) +
      ((Fintype.card St : ℝ≥0∞)⁻¹ + (Fintype.card St : ℝ≥0∞)⁻¹)
  | .inr d => ((ib d).2.length : ℝ≥0∞) * (Fintype.card St : ℝ≥0∞)⁻¹ +
      ((ib d).2.length : ℝ≥0∞) * (Fintype.card St : ℝ≥0∞)⁻¹

omit [DecidableEq Blk] in
theorem prEvent_Wev1_le_marked (IV : St) (ik ok : K → Blk) (hik : Function.Injective ik)
    (hok : Function.Injective ok) (ib : P × M → Blk × List Blk) (g : CF St Blk) (TI : Blk → St)
    (t : (St × Blk) ⊕ (P × M)) :
    Pr{let r ← sec K St}[Wev1 IV ik ok ib g TI r t] ≤ wt1M K St ik ok ib t := by
  have hγ : ∀ s : K, Pr{let s' ← $ᵗ K}[s' = s] ≤ (Fintype.card K : ℝ≥0∞)⁻¹ := fun s =>
    (SampleableType.prEvent_uniformSample_eq_singleton s).le
  rcases t with q | d
  · simp only [Wev1, wt1M]
    refine (prEvent_or_le _ _ _).trans (add_le_add ?_ ?_)
    · split_ifs with hm
      · refine (prEvent_or_le _ _ _).trans (add_le_add ?_ ?_)
        · exact prEvent_rho_fst _ (fun s : K × St => q = (IV, ik s.1))
            (prEvent_rho_fst _ (fun s : K => q = (IV, ik s))
              (prEvent_seed_cell IV ik hik ($ᵗ K) _ hγ q))
        · exact prEvent_rho_fst _ (fun s : K × St => q = (IV, ok s.1))
            (prEvent_rho_fst _ (fun s : K => q = (IV, ok s))
              (prEvent_seed_cell IV ok hok ($ᵗ K) _ hγ q))
      · refine le_of_eq (prEvent_eq_zero_of_forall_not _ _ fun r hr => hm ?_)
        rcases hr with h | h
        · exact ⟨r.1.1, Or.inl (congrArg Prod.snd h)⟩
        · exact ⟨r.1.1, Or.inr (congrArg Prod.snd h)⟩
    · refine (prEvent_or_le _ _ _).trans (add_le_add ?_ ?_)
      · exact prEvent_rho_snd _ (fun cv => q.1 = cv)
          (SampleableType.prEvent_uniformSample_eq_singleton' q.1).le
      · exact prEvent_rho_fst _ (fun s : K × St => q.1 = s.2)
          (prEvent_rho_snd _ (fun cv => q.1 = cv)
            (SampleableType.prEvent_uniformSample_eq_singleton' q.1).le)
  · simp only [Wev1, wt1M]
    refine (prEvent_or_le _ _ _).trans (add_le_add ?_ ?_)
    · exact prEvent_rho_snd _ (fun cv => cvHit cv g (TI (ib d).1) (ib d).2 = true)
        (prEvent_cvHit g _ _)
    · exact prEvent_rho_fst _ (fun s : K × St => cvHit s.2 g (TI (ib d).1) (ib d).2 = true)
        (prEvent_rho_snd _ (fun cv => cvHit cv g (TI (ib d).1) (ib d).2 = true)
          (prEvent_cvHit g _ _))

omit [DecidableEq St] [DecidableEq Blk] [SampleableType St] [SampleableType K] in
theorem sum_wt1M_le (ik ok : K → Blk) (ib : P × M → Blk × List Blk) (L : ℕ)
    (l : List ((St × Blk) ⊕ (P × M)))
    (hl : ∀ t ∈ l, ibLenLe ib L (.inr t)) :
    (l.map (wt1M K St ik ok ib)).sum ≤
      (l.countP (fun t => decide (markK ik ok (.inr t))) : ℝ≥0∞) *
          ((Fintype.card K : ℝ≥0∞)⁻¹ + (Fintype.card K : ℝ≥0∞)⁻¹) +
        (l.countP (fun t => decide (isCompQ (.inr t) = true)) : ℝ≥0∞) *
          ((Fintype.card St : ℝ≥0∞)⁻¹ + (Fintype.card St : ℝ≥0∞)⁻¹) +
        (l.countP (fun t => decide (isPrfQ (.inr t) = true)) : ℝ≥0∞) *
          ((L : ℝ≥0∞) * (Fintype.card St : ℝ≥0∞)⁻¹ + (L : ℝ≥0∞) * (Fintype.card St : ℝ≥0∞)⁻¹) := by
  induction l with
  | nil => simp
  | cons t l ih =>
    have ih' := ih fun t' ht' => hl t' (by simp [ht'])
    rw [List.map_cons, List.sum_cons, List.countP_cons, List.countP_cons, List.countP_cons]
    set a := List.countP (fun t => decide (markK (St := St) ik ok (Sum.inr t))) l
    set b := List.countP (fun t => decide (isCompQ (Sum.inr t) = true)) l
    set c := List.countP (fun t => decide (isPrfQ (Sum.inr t) = true)) l
    rcases t with q | d
    · by_cases hm : ∃ k, q.2 = ik k ∨ q.2 = ok k
      · have hm' : decide (markK (St := St) (P := P) (M := M) ik ok (.inr (.inl q))) = true :=
          decide_eq_true hm
        simp only [wt1M, hm', hm, isCompQ, isPrfQ, decide_true, ite_true,
          Bool.false_eq_true, decide_false, ite_false, Nat.cast_add, Nat.cast_one, add_zero,
          add_mul, one_mul]
        refine (add_le_add le_rfl ih').trans (le_of_eq ?_)
        ring
      · have hm' : decide (markK (St := St) (P := P) (M := M) ik ok (.inr (.inl q))) = false :=
          decide_eq_false hm
        simp only [wt1M, hm', hm, isCompQ, isPrfQ, decide_true, ite_true,
          Bool.false_eq_true, decide_false, ite_false, Nat.cast_add, Nat.cast_one, add_zero,
          zero_add, add_mul, one_mul]
        refine (add_le_add le_rfl ih').trans (le_of_eq ?_)
        ring
    · have hq : (ib d).2.length ≤ L := hl (.inr d) (by simp)
      have hq' : ((ib d).2.length : ℝ≥0∞) * (Fintype.card St : ℝ≥0∞)⁻¹ ≤
          (L : ℝ≥0∞) * (Fintype.card St : ℝ≥0∞)⁻¹ := by gcongr
      have hm' : decide (markK (St := St) (P := P) (M := M) ik ok (.inr (.inr d))) = false :=
        decide_eq_false fun h => h
      simp only [wt1M, hm', isCompQ, isPrfQ, decide_true, ite_true, Bool.false_eq_true,
        decide_false, ite_false, Nat.cast_add, Nat.cast_one, add_zero, add_mul, one_mul]
      refine (add_le_add (add_le_add hq' hq') ih').trans (le_of_eq ?_)
      ring

/-- For a fixed trace none of whose chaining values is `IV`, the bad event over the secrets,
marked form. -/
theorem prEvent_bad1_fixed_le_marked (IV : St) (ik ok : K → Blk) (hik : Function.Injective ik)
    (hok : Function.Injective ok) (ib : P × M → Blk × List Blk) (g : CF St Blk) (TI : Blk → St)
    (qM q qO L : ℕ) (l : List ((St × Blk) ⊕ (P × M)))
    (hqM : l.countP (fun t => decide (markK ik ok (.inr t))) ≤ qM)
    (hq : l.countP (fun t => decide (isCompQ (.inr t) = true)) ≤ q)
    (hO : l.countP (fun t => decide (isPrfQ (.inr t) = true)) ≤ qO)
    (hL : ∀ t ∈ l, ibLenLe ib L (.inr t)) (hno : l.any (ivQ IV ib g TI) = false) :
    Pr{let r ← sec K St}[(glob IV r.2 r.1.2 ||
        l.any (bad1 IV ib (ik r.1.1) (ok r.1.1) r.2 r.1.2 g TI)) = true] ≤
      ((Fintype.card St : ℝ≥0∞)⁻¹ +
          ((Fintype.card St : ℝ≥0∞)⁻¹ + (Fintype.card St : ℝ≥0∞)⁻¹)) +
        ((qM : ℝ≥0∞) * ((Fintype.card K : ℝ≥0∞)⁻¹ + (Fintype.card K : ℝ≥0∞)⁻¹) +
          (q : ℝ≥0∞) * ((Fintype.card St : ℝ≥0∞)⁻¹ + (Fintype.card St : ℝ≥0∞)⁻¹) +
          (qO : ℝ≥0∞) * ((L : ℝ≥0∞) * (Fintype.card St : ℝ≥0∞)⁻¹ +
            (L : ℝ≥0∞) * (Fintype.card St : ℝ≥0∞)⁻¹)) := by
  refine (prEvent_mono _ _
    (fun r => (r.2 = IV ∨ (r.1.2 = IV ∨ r.2 = r.1.2)) ∨ ∃ t ∈ l, Wev1 IV ik ok ib g TI r t)
    fun r hr => bad1_imp IV ik ok ib g TI r l hno hr).trans ?_
  refine (prEvent_or_le _ _ _).trans (add_le_add ?_ ?_)
  · refine (prEvent_or_le _ _ _).trans (add_le_add ?_ ?_)
    · exact prEvent_rho_snd _ (fun cv => cv = IV)
        (SampleableType.prEvent_uniformSample_eq_singleton IV).le
    · refine (prEvent_or_le _ _ _).trans (add_le_add ?_ ?_)
      · exact prEvent_rho_fst _ (fun s : K × St => s.2 = IV)
          (prEvent_rho_snd _ (fun cv => cv = IV)
            (SampleableType.prEvent_uniformSample_eq_singleton IV).le)
      · exact prEvent_rho_snd' _ (fun (s : K × St) cv => cv = s.2) fun s =>
          (SampleableType.prEvent_uniformSample_eq_singleton s.2).le
  · refine (prEvent_list_exists_le _ _ (wt1M K St ik ok ib) l fun t _ =>
      prEvent_Wev1_le_marked IV ik ok hik hok ib g TI t).trans ?_
    refine (sum_wt1M_le ik ok ib L l hL).trans (add_le_add (add_le_add ?_ ?_) ?_)
    · gcongr
    · gcongr
    · gcongr

end Fixed

theorem prT_badGame1_le_marked [Fintype St] [DecidableEq St] [DecidableEq Blk] [SampleableType St]
    [Fintype Blk] [SampleableType (CF St Blk)] [Fintype K] [SampleableType K]
    (IV : St) (ik ok : K → Blk) (hik : Function.Injective ik) (hok : Function.Injective ok)
    (ib : P × M → Blk × List Blk) (ob : St → Blk) (out : St → Y) (A : PrfAdvI St Blk P M Y)
    (qM q qO L : ℕ) (hqM : IsQueryBoundP A (markK ik ok) qM)
    (hq : IsQueryBoundP A (fun i => isCompQ i = true) q)
    (hO : IsQueryBoundP A (fun i => isPrfQ i = true) qO)
    (hL : AllQueriesSatisfy A (ibLenLe ib L)) :
    prT (badGame1 IV ik ok ib ob out A) ≤
      ((q + qO * (1 + L) : ℕ) : ℝ≥0∞) * (Fintype.card St : ℝ≥0∞)⁻¹ +
        (((Fintype.card St : ℝ≥0∞)⁻¹ +
            ((Fintype.card St : ℝ≥0∞)⁻¹ + (Fintype.card St : ℝ≥0∞)⁻¹)) +
          ((qM : ℝ≥0∞) * ((Fintype.card K : ℝ≥0∞)⁻¹ + (Fintype.card K : ℝ≥0∞)⁻¹) +
            (q : ℝ≥0∞) * ((Fintype.card St : ℝ≥0∞)⁻¹ + (Fintype.card St : ℝ≥0∞)⁻¹) +
            (qO : ℝ≥0∞) * ((L : ℝ≥0∞) * (Fintype.card St : ℝ≥0∞)⁻¹ +
              (L : ℝ≥0∞) * (Fintype.card St : ℝ≥0∞)⁻¹))) := by
  have hbad : badGame1 IV ik ok ib ob out A = sec K St >>= fun r =>
      $ᵗ (Blk → St) >>= fun TO => packTr ib ob out A TO >>= fun y =>
        pure (glob IV r.2 r.1.2 ||
          y.2.2.any (bad1 IV ib (ik r.1.1) (ok r.1.1) r.2 r.1.2 y.1 y.2.1)) := by
    simp only [badGame1, sec, rho, packTr, bind_assoc, pure_bind, bind_map_left]
  rw [hbad, prT_swap]
  refine prT_bind_le_of_forall_le _ _ fun TO _ => ?_
  rw [prT_swap]
  have hflag : Pr{let y ← packTr ib ob out A TO}[y.2.2.any (ivQ IV ib y.1 y.2.1) = true] ≤
      ((q + qO * (1 + L) : ℕ) : ℝ≥0∞) * (Fintype.card St : ℝ≥0∞)⁻¹ := by
    have e : Pr{let y ← packTr ib ob out A TO}[y.2.2.any (ivQ IV ib y.1 y.2.1) = true] =
        prT ($ᵗ (CF St Blk) >>= fun g => $ᵗ (Blk → St) >>= fun TI =>
          (simulateQ (trImpl (hybAns ib ob out g TI TO)) A).run [] >>= fun z =>
            pure (z.2.any (ivQ IV ib g TI))) := by
      rw [← prT_bind_pure]
      simp only [packTr, bind_assoc, pure_bind]
    rw [e]
    refine le_trans ?_ (prEvent_trace_hasIV_le IV
      (chainProg ib ob out TO A) q qO L (chainProg_pub ib ob out TO A q hq)
      (chainProg_chain ib ob out TO A qO hO) (chainProg_len ib ob out TO A L hL))
    refine prT_bind_mono _ _ _ fun g _ => prT_bind_mono _ _ _ fun TI _ => ?_
    rw [run_trImpl_chainProg, bind_map_left]
    exact prT_bind_pure_mono _ _ _ fun z hz => hasIV_of_ivQ IV ib g TI z.2 hz
  refine (prT_bind_le_prEvent_add (packTr ib ob out A TO) _
    (fun y => y.2.2.any (ivQ IV ib y.1 y.2.1) = true) ?_).trans (add_le_add hflag le_rfl)
  rintro ⟨g, TI, l⟩ hy hno
  simp only [packTr, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hy
  obtain ⟨g', -, T', -, z', hz, heq⟩ := hy
  obtain ⟨rfl, rfl, rfl⟩ := Prod.mk.inj heq |>.imp id fun h => Prod.mk.inj h
  rw [prT_bind_pure]
  have h0 := trace_countP_le (hybAns ib ob out g TI TO) (markK ik ok) A qM hqM [] z' hz
  have h1 := trace_countP_le (hybAns ib ob out g TI TO) (fun i => isCompQ i = true) A q hq [] z' hz
  have h2 := trace_countP_le (hybAns ib ob out g TI TO) (fun i => isPrfQ i = true) A qO hO [] z' hz
  have h3 := trace_forall (hybAns ib ob out g TI TO) (ibLenLe ib L) A hL [] (by simp) z' hz
  exact prEvent_bad1_fixed_le_marked IV ik ok hik hok ib g TI qM q qO L z'.2 (by simpa using h0)
    (by simpa using h1) (by simpa using h2) h3 (by simpa using hno)

section Bound

variable [Fintype St] [DecidableEq St] [SampleableType St] [Fintype Blk] [DecidableEq Blk]
  [SampleableType (CF St Blk)] [DecidableEq P] [DecidableEq M]
variable [Fintype K] [SampleableType K] [SampleableType Y]

/-- **One-sided bound, marked form.** -/
theorem prT_macReal_le_marked (IV : St) (ik ok : K → Blk) (hik : Function.Injective ik)
    (hok : Function.Injective ok) (hne : ∀ k, ik k ≠ ok k) (ib : P × M → Blk × List Blk)
    (hib : Function.Injective ib) (ob : St → Blk) (hob : Function.Injective ob) (out : St → Y)
    (hout : ∀ p : Y → Prop, Pr{let u ← $ᵗ St}[p (out u)] = Pr{let y ← $ᵗ Y}[p y])
    (A : PrfAdvI St Blk P M Y) (qM q qO L : ℕ) (hqM : IsQueryBoundP A (markK ik ok) qM)
    (hq : IsQueryBoundP A (fun i => isCompQ i = true) q)
    (hO : IsQueryBoundP A (fun i => isPrfQ i = true) qO)
    (hL : AllQueriesSatisfy A (ibLenLe ib L)) :
    prT (macRealGameI IV ik ok ib ob out A) ≤ prT (prfIdealGameI A) +
      (2 * (qM : ℝ≥0∞) * (Fintype.card K : ℝ≥0∞)⁻¹ +
        ((3 * q + qO * (1 + 3 * L) + 3 + (q + qO * (1 + L)) ^ 2 : ℕ) : ℝ≥0∞) *
          (Fintype.card St : ℝ≥0∞)⁻¹) := by
  refine (prT_real_le_hyb IV ik ok ib ob out hne A).trans ?_
  refine (add_le_add (prT_hyb_le_ideal ib hib ob hob out hout A q qO L hq hO hL)
    (prT_badGame1_le_marked IV ik ok hik hok ib ob out A qM q qO L hqM hq hO hL)).trans
      (le_of_eq ?_)
  push_cast
  ring

end Bound

end Ideal.MsgPrf

namespace Ideal

open Ideal.HP Ideal.Prf Ideal.MsgPrf

variable {St Blk K P M Y : Type}

/-- **PRF security of the HMAC-shaped keyed function, marked form.**  As `macAdvantageI_le`,
with the key-guessing term charged only to the `qM` compression queries at inner or outer key
blocks (`MsgPrf.markK`). -/
theorem macAdvantageI_le_marked [Fintype St] [DecidableEq St] [SampleableType St] [Fintype Blk]
    [DecidableEq Blk] [SampleableType (CF St Blk)] [DecidableEq P] [DecidableEq M] [Fintype K]
    [SampleableType K] [SampleableType Y]
    (IV : St) (ik ok : K → Blk) (hik : Function.Injective ik) (hok : Function.Injective ok)
    (hne : ∀ k, ik k ≠ ok k) (ib : P × M → Blk × List Blk) (hib : Function.Injective ib)
    (ob : St → Blk) (hob : Function.Injective ob) (out : St → Y)
    (hout : ∀ p : Y → Prop, Pr{let u ← $ᵗ St}[p (out u)] = Pr{let y ← $ᵗ Y}[p y])
    (A : PrfAdvI St Blk P M Y) (qM q qO L : ℕ) (hqM : IsQueryBoundP A (markK ik ok) qM)
    (hq : IsQueryBoundP A (fun i => isCompQ i = true) q)
    (hO : IsQueryBoundP A (fun i => isPrfQ i = true) qO)
    (hL : AllQueriesSatisfy A (ibLenLe ib L)) :
    macAdvantageI IV ik ok ib ob out A ≤
      2 * (qM : ℝ≥0∞) * (Fintype.card K : ℝ≥0∞)⁻¹ +
        ((3 * q + qO * (1 + 3 * L) + 3 + (q + qO * (1 + L)) ^ 2 : ℕ) : ℝ≥0∞) *
          (Fintype.card St : ℝ≥0∞)⁻¹ := by
  unfold macAdvantageI
  refine MeasureTheory.Measure.boolDist_le_of_apply_le _ _ fun b => ?_
  cases b
  · have h := prT_macReal_le_marked IV ik ok hik hok hne ib hib ob hob out hout (negAdv A) qM q
      qO L ((isQueryBoundP_map_iff _ _ _).mpr hqM)
      ((isQueryBoundP_map_iff _ _ _).mpr hq) ((isQueryBoundP_map_iff _ _ _).mpr hO) (by
        unfold AllQueriesSatisfy at hL ⊢
        exact (isQueryBound_map_iff _ _ _ _ _).mpr hL)
    rwa [macRealGameI_not, prfIdealGameI_not, prT_not_map, prT_not_map] at h
  · have h := prT_macReal_le_marked IV ik ok hik hok hne ib hib ob hob out hout A qM q qO L hqM
      hq hO hL
    rwa [prT_eq, prT_eq] at h

/-- The two one-sided forms of `macAdvantageI_le_marked`. -/
theorem prT_mac_two_sided_marked [Fintype St] [DecidableEq St] [SampleableType St] [Fintype Blk]
    [DecidableEq Blk] [SampleableType (CF St Blk)] [DecidableEq P] [DecidableEq M] [Fintype K]
    [SampleableType K] [SampleableType Y]
    (IV : St) (ik ok : K → Blk) (hik : Function.Injective ik) (hok : Function.Injective ok)
    (hne : ∀ k, ik k ≠ ok k) (ib : P × M → Blk × List Blk) (hib : Function.Injective ib)
    (ob : St → Blk) (hob : Function.Injective ob) (out : St → Y)
    (hout : ∀ p : Y → Prop, Pr{let u ← $ᵗ St}[p (out u)] = Pr{let y ← $ᵗ Y}[p y])
    (A : PrfAdvI St Blk P M Y) (qM q qO L : ℕ) (hqM : IsQueryBoundP A (markK ik ok) qM)
    (hq : IsQueryBoundP A (fun i => isCompQ i = true) q)
    (hO : IsQueryBoundP A (fun i => isPrfQ i = true) qO)
    (hL : AllQueriesSatisfy A (ibLenLe ib L)) :
    prT (macRealGameI IV ik ok ib ob out A) ≤ prT (prfIdealGameI A) +
        (2 * (qM : ℝ≥0∞) * (Fintype.card K : ℝ≥0∞)⁻¹ +
          ((3 * q + qO * (1 + 3 * L) + 3 + (q + qO * (1 + L)) ^ 2 : ℕ) : ℝ≥0∞) *
            (Fintype.card St : ℝ≥0∞)⁻¹) ∧
      prT (prfIdealGameI A) ≤ prT (macRealGameI IV ik ok ib ob out A) +
        (2 * (qM : ℝ≥0∞) * (Fintype.card K : ℝ≥0∞)⁻¹ +
          ((3 * q + qO * (1 + 3 * L) + 3 + (q + qO * (1 + L)) ^ 2 : ℕ) : ℝ≥0∞) *
            (Fintype.card St : ℝ≥0∞)⁻¹) := by
  have h := macAdvantageI_le_marked IV ik ok hik hok hne ib hib ob hob out hout A qM q qO L hqM
    hq hO hL
  unfold macAdvantageI at h
  rw [prT_eq, prT_eq]
  constructor
  · exact (MeasureTheory.Measure.apply_true_le_add_boolDist _ _).trans (add_le_add le_rfl h)
  · rw [MeasureTheory.Measure.boolDist_comm] at h
    exact (MeasureTheory.Measure.apply_true_le_add_boolDist _ _).trans (add_le_add le_rfl h)

end Ideal

#print axioms Ideal.MsgPrf.prT_badGame1_le_marked
#print axioms Ideal.macAdvantageI_le_marked
#print axioms Ideal.prT_mac_two_sided_marked
