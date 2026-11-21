import Ideal.Games.MsgPrfHop

/-!
# The HMAC-shaped PRF: the bad event of the hop to the hybrid

`prT_badGame1_le`: the key `k` and the hidden chaining values `cvO`, `cvI`, drawn after the
hybrid run (which does not depend on them), make a traced query bad with probability at most

`(q + qO (1 + L)) / |St| + 3 / |St| + q (2 / |K| + 2 / |St|) + qO (2 L / |St|)`.

The hybrid run is a run of the chain-oracle program `chainProg` against `(g, TI)`
(`HP.pairAns g (HP.chainI g TI)`), so the event that one of its chaining values equals `IV` is
bounded by `HP.prEvent_trace_hasIV_le`.
-/

open OracleComp OracleSpec ENNReal PRFScheme

namespace Ideal.MsgPrf

open Ideal.HP Ideal.Prf

variable {St Blk K P M Y : Type}

/-! ## The hybrid as a chain-oracle program -/

/-- A function query as a chain query. -/
def toC (ib : P × M → Blk × List Blk) : (St × Blk) ⊕ (P × M) → (St × Blk) ⊕ (Blk × List Blk) :=
  Sum.map id ib

/-- Post-processing of the chain answer: the outer row table and the output map. -/
def postC (ib : P × M → Blk × List Blk) (ob : St → Blk) (out : St → Y) (TO : Blk → St) :
    (t : (St × Blk) ⊕ (P × M)) → (hS St Blk + chainS St Blk).Range (toC ib t) →
      (hS St Blk + ((P × M) →ₒ Y)).Range t
  | .inl _ => fun u => u
  | .inr _ => fun c => out (TO (ob c))

/-- The distinguisher as a program with a chain oracle, for a fixed outer row table. -/
def chainProg (ib : P × M → Blk × List Blk) (ob : St → Blk) (out : St → Y) (TO : Blk → St)
    {α : Type} (A : OracleComp (unifSpec + (hS St Blk + ((P × M) →ₒ Y))) α) :
    OracleComp (unifSpec + (hS St Blk + chainS St Blk)) α :=
  simulateQ (relabelImpl (toC ib) (postC ib ob out TO)) A

theorem hybAns_eq (ib : P × M → Blk × List Blk) (ob : St → Blk) (out : St → Y) (g : CF St Blk)
    (TI TO : Blk → St) :
    (fun t => postC ib ob out TO t (pairAns g (chainI g TI) (toC ib t))) =
      hybAns ib ob out g TI TO := by
  funext t
  rcases t with q | d <;> rfl

/-- The trace of the chain-oracle program. -/
theorem run_trImpl_chainProg (ib : P × M → Blk × List Blk) (ob : St → Blk) (out : St → Y)
    (g : CF St Blk) (TI TO : Blk → St) {α : Type}
    (A : OracleComp (unifSpec + (hS St Blk + ((P × M) →ₒ Y))) α) :
    (simulateQ (trImpl (pairAns g (chainI g TI))) (chainProg ib ob out TO A)).run [] =
      (fun z => (z.1, z.2.map (toC ib))) <$>
        (simulateQ (trImpl (hybAns ib ob out g TI TO)) A).run [] := by
  unfold chainProg
  rw [simulateQ_stImpl_relabel, hybAns_eq,
    run_stImpl_append_eq_trace (hybAns ib ob out g TI TO) (fun t => [toC ib t])]
  have e : ∀ l : List ((St × Blk) ⊕ (P × M)),
      List.flatMap (fun t => [toC ib t]) l = l.map (toC ib) := fun l => by
    induction l with
    | nil => rfl
    | cons a l ih => simp [ih]
  simp only [e]

/-- The trace of the table-level program: the cells of the traced queries. -/
theorem run_trImpl_cells (ib : P × M → Blk × List Blk) (ob : St → Blk) (out : St → Y)
    (g : CF St Blk) (TI TO : Blk → St) {α : Type}
    (A : OracleComp (unifSpec + (hS St Blk + ((P × M) →ₒ Y))) α) :
    (simulateQ (trImpl (tbl g TI)) (simulateQ chainToT (chainProg ib ob out TO A))).run [] =
      (fun z => (z.1, z.2.flatMap fun t => cellsQ g TI (toC ib t))) <$>
        (simulateQ (trImpl (hybAns ib ob out g TI TO)) A).run [] := by
  unfold chainProg
  rw [simulateQ_trImpl_chainToT, simulateQ_stImpl_relabel, hybAns_eq,
    run_stImpl_append_eq_trace]

theorem chainProg_pub (ib : P × M → Blk × List Blk) (ob : St → Blk) (out : St → Y)
    (TO : Blk → St) {α : Type} (A : OracleComp (unifSpec + (hS St Blk + ((P × M) →ₒ Y))) α)
    (q : ℕ) (hq : IsQueryBoundP A (fun i => isCompQ i = true) q) :
    IsQueryBoundP (chainProg ib ob out TO A) (fun i => isPub i = true) q := by
  refine isQueryBoundP_relabel _ _ _ A q (IsQueryBoundP.of_imp (fun t ht => ?_) hq)
  rcases t with n | q | d <;> exact ht

theorem chainProg_chain (ib : P × M → Blk × List Blk) (ob : St → Blk) (out : St → Y)
    (TO : Blk → St) {α : Type} (A : OracleComp (unifSpec + (hS St Blk + ((P × M) →ₒ Y))) α)
    (qO : ℕ) (hO : IsQueryBoundP A (fun i => isPrfQ i = true) qO) :
    IsQueryBoundP (chainProg ib ob out TO A) (fun i => isChain i = true) qO := by
  refine isQueryBoundP_relabel _ _ _ A qO (IsQueryBoundP.of_imp (fun t ht => ?_) hO)
  rcases t with n | q | d <;> exact ht

theorem chainProg_len (ib : P × M → Blk × List Blk) (ob : St → Blk) (out : St → Y)
    (TO : Blk → St) {α : Type} (A : OracleComp (unifSpec + (hS St Blk + ((P × M) →ₒ Y))) α)
    (L : ℕ) (hL : AllQueriesSatisfy A (ibLenLe ib L)) :
    AllQueriesSatisfy (chainProg ib ob out TO A) (chainLenLe L) := by
  refine allQueriesSatisfy_relabel _ _ _ A ?_
  have e : (fun i => chainLenLe L (Sum.map id (toC ib) i)) = ibLenLe (St := St) ib L := by
    funext t
    rcases t with n | q | d <;> rfl
  rw [e]
  exact hL

/-! ## Chaining values equal to `IV` -/

section IV

variable [DecidableEq St]

/-- Some chaining value of a function query that is used as a row equals `IV`. -/
def ivQ (IV : St) (ib : P × M → Blk × List Blk) (g : CF St Blk) (TI : Blk → St) :
    (St × Blk) ⊕ (P × M) → Bool
  | .inl _ => false
  | .inr d => cvHit IV g (TI (ib d).1) (ib d).2

theorem cvHit_imp_restIV (cv : St) (g : CF St Blk) (c : St) (bs : List Blk)
    (h : cvHit cv g c bs = true) : (decide (c = cv) || restIV cv g c bs) = true := by
  induction bs generalizing c with
  | nil => simp [cvHit] at h
  | cons b bs ih =>
    simp only [cvHit, Bool.or_eq_true, decide_eq_true_eq] at h
    rcases h with h | h
    · simp [h]
    · have := ih _ h
      simp only [restIV, Bool.or_eq_true, decide_eq_true_eq] at this ⊢
      exact Or.inr this

theorem hasIV_of_ivQ (IV : St) (ib : P × M → Blk × List Blk) (g : CF St Blk) (TI : Blk → St)
    (l : List ((St × Blk) ⊕ (P × M))) (h : l.any (ivQ IV ib g TI) = true) :
    (l.map (toC ib)).any (hasIV IV g TI) = true := by
  rw [List.any_eq_true] at h
  obtain ⟨t, ht, hb⟩ := h
  rw [List.any_eq_true]
  refine ⟨toC ib t, List.mem_map_of_mem ht, ?_⟩
  rcases t with q | d
  · simp [ivQ] at hb
  · exact cvHit_imp_restIV IV g _ _ hb

end IV

/-! ## The key and the hidden chaining values -/

theorem prEvent_rho_snd' [SampleableType St] {S : Type} (seedGen : ProbComp S)
    (p : S → St → Prop) {ε : ℝ≥0∞} (h : ∀ s, Pr{let cv ← $ᵗ St}[p s cv] ≤ ε) :
    Pr{let r ← rho (St := St) seedGen}[p r.1 r.2] ≤ ε := by
  unfold rho
  refine prEvent_bind_le_of_forall_le seedGen _ (fun r : S × St => p r.1 r.2) fun a => ?_
  rw [prEvent_map]
  exact h a

section Fixed

variable [Fintype St] [DecidableEq St] [DecidableEq Blk] [SampleableType St] [Fintype K]
  [SampleableType K]

/-- The secrets `((k, cvO), cvI)`, drawn after the hybrid run. -/
noncomputable abbrev sec (K St : Type) [SampleableType St] [SampleableType K] :
    ProbComp ((K × St) × St) :=
  rho (St := St) (rho (St := St) ($ᵗ K))

/-- The event over the secrets charged to a traced query. -/
def Wev1 (IV : St) (ik ok : K → Blk) (ib : P × M → Blk × List Blk) (g : CF St Blk)
    (TI : Blk → St) (r : (K × St) × St) : (St × Blk) ⊕ (P × M) → Prop
  | .inl q => (q = (IV, ik r.1.1) ∨ q = (IV, ok r.1.1)) ∨ (q.1 = r.2 ∨ q.1 = r.1.2)
  | .inr d => cvHit r.2 g (TI (ib d).1) (ib d).2 = true ∨
      cvHit r.1.2 g (TI (ib d).1) (ib d).2 = true

/-- The weight charged to a traced query. -/
noncomputable def wt1 (K St : Type) [Fintype K] [Fintype St] {Blk : Type}
    (ib : P × M → Blk × List Blk) : (St × Blk) ⊕ (P × M) → ℝ≥0∞
  | .inl _ => ((Fintype.card K : ℝ≥0∞)⁻¹ + (Fintype.card K : ℝ≥0∞)⁻¹) +
      ((Fintype.card St : ℝ≥0∞)⁻¹ + (Fintype.card St : ℝ≥0∞)⁻¹)
  | .inr d => ((ib d).2.length : ℝ≥0∞) * (Fintype.card St : ℝ≥0∞)⁻¹ +
      ((ib d).2.length : ℝ≥0∞) * (Fintype.card St : ℝ≥0∞)⁻¹

omit [DecidableEq Blk] in
theorem prEvent_Wev1_le (IV : St) (ik ok : K → Blk) (hik : Function.Injective ik)
    (hok : Function.Injective ok) (ib : P × M → Blk × List Blk) (g : CF St Blk) (TI : Blk → St)
    (t : (St × Blk) ⊕ (P × M)) :
    Pr{let r ← sec K St}[Wev1 IV ik ok ib g TI r t] ≤ wt1 K St ib t := by
  have hγ : ∀ s : K, Pr{let s' ← $ᵗ K}[s' = s] ≤ (Fintype.card K : ℝ≥0∞)⁻¹ := fun s =>
    (SampleableType.prEvent_uniformSample_eq_singleton s).le
  rcases t with q | d
  · simp only [Wev1, wt1]
    refine (prEvent_or_le _ _ _).trans (add_le_add ?_ ?_)
    · refine (prEvent_or_le _ _ _).trans (add_le_add ?_ ?_)
      · exact prEvent_rho_fst _ (fun s : K × St => q = (IV, ik s.1))
          (prEvent_rho_fst _ (fun s : K => q = (IV, ik s))
            (prEvent_seed_cell IV ik hik ($ᵗ K) _ hγ q))
      · exact prEvent_rho_fst _ (fun s : K × St => q = (IV, ok s.1))
          (prEvent_rho_fst _ (fun s : K => q = (IV, ok s))
            (prEvent_seed_cell IV ok hok ($ᵗ K) _ hγ q))
    · refine (prEvent_or_le _ _ _).trans (add_le_add ?_ ?_)
      · exact prEvent_rho_snd _ (fun cv => q.1 = cv)
          (SampleableType.prEvent_uniformSample_eq_singleton' q.1).le
      · exact prEvent_rho_fst _ (fun s : K × St => q.1 = s.2)
          (prEvent_rho_snd _ (fun cv => q.1 = cv)
            (SampleableType.prEvent_uniformSample_eq_singleton' q.1).le)
  · simp only [Wev1, wt1]
    refine (prEvent_or_le _ _ _).trans (add_le_add ?_ ?_)
    · exact prEvent_rho_snd _ (fun cv => cvHit cv g (TI (ib d).1) (ib d).2 = true)
        (prEvent_cvHit g _ _)
    · exact prEvent_rho_fst _ (fun s : K × St => cvHit s.2 g (TI (ib d).1) (ib d).2 = true)
        (prEvent_rho_snd _ (fun cv => cvHit cv g (TI (ib d).1) (ib d).2 = true)
          (prEvent_cvHit g _ _))

omit [DecidableEq St] [DecidableEq Blk] [SampleableType St] [SampleableType K] in
theorem sum_wt1_le (ib : P × M → Blk × List Blk) (L : ℕ) (l : List ((St × Blk) ⊕ (P × M)))
    (hl : ∀ t ∈ l, ibLenLe ib L (.inr t)) :
    (l.map (wt1 K St ib)).sum ≤
      (l.countP (fun t => decide (isCompQ (.inr t) = true)) : ℝ≥0∞) *
          (((Fintype.card K : ℝ≥0∞)⁻¹ + (Fintype.card K : ℝ≥0∞)⁻¹) +
            ((Fintype.card St : ℝ≥0∞)⁻¹ + (Fintype.card St : ℝ≥0∞)⁻¹)) +
        (l.countP (fun t => decide (isPrfQ (.inr t) = true)) : ℝ≥0∞) *
          ((L : ℝ≥0∞) * (Fintype.card St : ℝ≥0∞)⁻¹ + (L : ℝ≥0∞) * (Fintype.card St : ℝ≥0∞)⁻¹) := by
  induction l with
  | nil => simp
  | cons t l ih =>
    have ih' := ih fun t' ht' => hl t' (by simp [ht'])
    rw [List.map_cons, List.sum_cons, List.countP_cons, List.countP_cons]
    set a := List.countP (fun t => decide (isCompQ (Sum.inr t) = true)) l
    set b := List.countP (fun t => decide (isPrfQ (Sum.inr t) = true)) l
    rcases t with q | d
    · simp only [wt1, isCompQ, isPrfQ, decide_true, ite_true, Bool.false_eq_true, decide_false,
        ite_false, Nat.cast_add, Nat.cast_one, add_zero, add_mul, one_mul]
      refine (add_le_add le_rfl ih').trans (le_of_eq ?_)
      ring
    · have hq : (ib d).2.length ≤ L := hl (.inr d) (by simp)
      have hq' : ((ib d).2.length : ℝ≥0∞) * (Fintype.card St : ℝ≥0∞)⁻¹ ≤
          (L : ℝ≥0∞) * (Fintype.card St : ℝ≥0∞)⁻¹ := by gcongr
      simp only [wt1, isCompQ, isPrfQ, decide_true, ite_true, Bool.false_eq_true, decide_false,
        ite_false, Nat.cast_add, Nat.cast_one, add_zero, add_mul, one_mul]
      refine (add_le_add (add_le_add hq' hq') ih').trans (le_of_eq ?_)
      ring

omit [Fintype St] [SampleableType St] [Fintype K] [SampleableType K] in
theorem bad1_imp (IV : St) (ik ok : K → Blk) (ib : P × M → Blk × List Blk) (g : CF St Blk)
    (TI : Blk → St) (r : (K × St) × St) (l : List ((St × Blk) ⊕ (P × M)))
    (hno : l.any (ivQ IV ib g TI) = false)
    (h : (glob IV r.2 r.1.2 ||
      l.any (bad1 IV ib (ik r.1.1) (ok r.1.1) r.2 r.1.2 g TI)) = true) :
    (r.2 = IV ∨ (r.1.2 = IV ∨ r.2 = r.1.2)) ∨ ∃ t ∈ l, Wev1 IV ik ok ib g TI r t := by
  simp only [Bool.or_eq_true, List.any_eq_true] at h
  rcases h with h | ⟨t, ht, hb⟩
  · simp only [glob, Bool.or_eq_true, decide_eq_true_eq] at h
    exact Or.inl h
  · refine Or.inr ⟨t, ht, ?_⟩
    have hno' : ivQ IV ib g TI t = false := by
      rw [List.any_eq_false] at hno
      simpa using hno t ht
    rcases t with q | d
    · simp only [bad1, Bool.or_eq_true, decide_eq_true_eq] at hb
      exact hb
    · simp only [bad1, Bool.or_eq_true] at hb
      simp only [ivQ] at hno'
      rcases hb with hb | hb
      · rw [hno'] at hb
        exact absurd hb (by simp)
      · exact hb

/-- For a fixed trace none of whose chaining values is `IV`, the bad event over the secrets. -/
theorem prEvent_bad1_fixed_le (IV : St) (ik ok : K → Blk) (hik : Function.Injective ik)
    (hok : Function.Injective ok) (ib : P × M → Blk × List Blk) (g : CF St Blk) (TI : Blk → St)
    (q qO L : ℕ) (l : List ((St × Blk) ⊕ (P × M)))
    (hq : l.countP (fun t => decide (isCompQ (.inr t) = true)) ≤ q)
    (hO : l.countP (fun t => decide (isPrfQ (.inr t) = true)) ≤ qO)
    (hL : ∀ t ∈ l, ibLenLe ib L (.inr t)) (hno : l.any (ivQ IV ib g TI) = false) :
    Pr{let r ← sec K St}[(glob IV r.2 r.1.2 ||
        l.any (bad1 IV ib (ik r.1.1) (ok r.1.1) r.2 r.1.2 g TI)) = true] ≤
      ((Fintype.card St : ℝ≥0∞)⁻¹ +
          ((Fintype.card St : ℝ≥0∞)⁻¹ + (Fintype.card St : ℝ≥0∞)⁻¹)) +
        ((q : ℝ≥0∞) * (((Fintype.card K : ℝ≥0∞)⁻¹ + (Fintype.card K : ℝ≥0∞)⁻¹) +
            ((Fintype.card St : ℝ≥0∞)⁻¹ + (Fintype.card St : ℝ≥0∞)⁻¹)) +
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
  · refine (prEvent_list_exists_le _ _ (wt1 K St ib) l fun t _ =>
      prEvent_Wev1_le IV ik ok hik hok ib g TI t).trans ?_
    refine (sum_wt1_le ib L l hL).trans (add_le_add ?_ ?_)
    · gcongr
    · gcongr

end Fixed

/-! ## The bad game -/

/-- The tables and the trace of the hybrid run, for a fixed outer row table. -/
noncomputable def packTr [SampleableType St] [Fintype Blk] [DecidableEq Blk]
    [SampleableType (CF St Blk)] (ib : P × M → Blk × List Blk) (ob : St → Blk) (out : St → Y)
    (A : PrfAdvI St Blk P M Y) (TO : Blk → St) :
    ProbComp (CF St Blk × (Blk → St) × List ((St × Blk) ⊕ (P × M))) :=
  $ᵗ (CF St Blk) >>= fun g => $ᵗ (Blk → St) >>= fun TI =>
    (simulateQ (trImpl (hybAns ib ob out g TI TO)) A).run [] >>= fun z => pure (g, TI, z.2)

theorem prT_badGame1_le [Fintype St] [DecidableEq St] [DecidableEq Blk] [SampleableType St]
    [Fintype Blk] [SampleableType (CF St Blk)] [Fintype K] [SampleableType K]
    (IV : St) (ik ok : K → Blk) (hik : Function.Injective ik) (hok : Function.Injective ok)
    (ib : P × M → Blk × List Blk) (ob : St → Blk) (out : St → Y) (A : PrfAdvI St Blk P M Y)
    (q qO L : ℕ) (hq : IsQueryBoundP A (fun i => isCompQ i = true) q)
    (hO : IsQueryBoundP A (fun i => isPrfQ i = true) qO)
    (hL : AllQueriesSatisfy A (ibLenLe ib L)) :
    prT (badGame1 IV ik ok ib ob out A) ≤
      ((q + qO * (1 + L) : ℕ) : ℝ≥0∞) * (Fintype.card St : ℝ≥0∞)⁻¹ +
        (((Fintype.card St : ℝ≥0∞)⁻¹ +
            ((Fintype.card St : ℝ≥0∞)⁻¹ + (Fintype.card St : ℝ≥0∞)⁻¹)) +
          ((q : ℝ≥0∞) * (((Fintype.card K : ℝ≥0∞)⁻¹ + (Fintype.card K : ℝ≥0∞)⁻¹) +
              ((Fintype.card St : ℝ≥0∞)⁻¹ + (Fintype.card St : ℝ≥0∞)⁻¹)) +
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
  have h1 := trace_countP_le (hybAns ib ob out g TI TO) (fun i => isCompQ i = true) A q hq [] z' hz
  have h2 := trace_countP_le (hybAns ib ob out g TI TO) (fun i => isPrfQ i = true) A qO hO [] z' hz
  have h3 := trace_forall (hybAns ib ob out g TI TO) (ibLenLe ib L) A hL [] (by simp) z' hz
  exact prEvent_bad1_fixed_le IV ik ok hik hok ib g TI q qO L z'.2 (by simpa using h1)
    (by simpa using h2) h3 (by simpa using hno)

end Ideal.MsgPrf

#print axioms Ideal.MsgPrf.prT_badGame1_le
