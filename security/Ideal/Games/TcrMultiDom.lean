import Ideal.Games.TcrMultiSym
import Ideal.Games.TcrMultiBuild

/-!
# Multi-block SM-TCR: the eager symbolic phase one is dominated by the real phase one

`dominated_symE`: read through `fbuild`, every step of the eager symbolic game `symE` from a
state satisfying `SInv` and `Nice`, conjoined with a `Nice` post-state, has at most the mass of
the step of the real game `conG` from the built state.
-/

open OracleComp OracleSpec ENNReal

namespace Ideal

open TweakableHash

variable {St Blk PkSeed Tweak M Y ι : Type}

namespace MD

/-! ## Keys of the entries, and `build` under updates -/

theorem pubCells_nil_right (vals : List St) : pubCells vals ([] : List Blk) = [] := by
  unfold pubCells
  split <;> simp_all

theorem pubCells_key (bs : List Blk) (vals : List St) (e : Cell St Blk × St)
    (h : e ∈ pubCells vals bs) : ∃ c b, e.1 = .inl (c, b) ∧ c ∈ vals.dropLast := by
  induction bs generalizing vals with
  | nil => rw [pubCells_nil_right] at h; simp at h
  | cons b bs ih =>
    match vals, h with
    | c :: c' :: t, h =>
      rw [MB.pubCells_cons_cons] at h
      rcases List.mem_cons.mp h with rfl | h
      · exact ⟨c, b, rfl, by simp⟩
      · obtain ⟨c₀, b₀, h1, h2⟩ := ih _ h
        exact ⟨c₀, b₀, h1, by rw [List.dropLast_cons_cons]; exact List.mem_cons_of_mem _ h2⟩
    | [], h => simp [pubCells] at h
    | [c], h => simp [pubCells] at h

theorem chainCells_key (X : Blk × List Blk) (vals : List St) (e : Cell St Blk × St)
    (h : e ∈ chainCells X vals) :
    e.1 = .inr X.1 ∨ ∃ c b, e.1 = .inl (c, b) ∧ c ∈ vals.dropLast := by
  cases vals with
  | nil => simp [chainCells] at h
  | cons c t =>
    simp only [chainCells] at h
    rcases List.mem_cons.mp h with rfl | h
    · exact .inl rfl
    · exact .inr (pubCells_key _ _ _ h)

variable (F : THFam St Blk PkSeed Tweak M Y ι)

theorem tgtVals_dropLast (κ : Cell St Blk → Option St) (tm : Tweak × M) (h : List St)
    (c : St) (hc : c ∈ (tgtVals F κ tm h).dropLast) : c ∈ h := by
  unfold tgtVals at hc
  split at hc
  · simpa using hc
  · simp at hc

theorem entries_key (κ : Cell St Blk → Option St) (qs : List (Tweak × M))
    (hs : List (List St)) (e : Cell St Blk × St) (h : e ∈ entries F κ qs hs) :
    (∃ tm ∈ qs, e.1 = .inr (F.tch tm.1 tm.2).1) ∨
      ∃ c b, e.1 = .inl (c, b) ∧ c ∈ hs.flatten := by
  unfold entries at h
  obtain ⟨p, hp, he⟩ := List.mem_flatMap.mp h
  have hp' := List.of_mem_zip hp
  rcases chainCells_key _ _ _ he with h1 | ⟨c, b, h1, h2⟩
  · exact .inl ⟨p.1, hp'.1, h1⟩
  · exact .inr ⟨c, b, h1, List.mem_flatten.mpr ⟨p.2, hp'.2, tgtVals_dropLast F κ _ _ c h2⟩⟩

/-- A cell is no key of the symbolic state. -/
def NonKey (qs : List (Tweak × M)) (hs : List (List St)) (x : Cell St Blk) : Prop :=
  (∀ tm ∈ qs, x ≠ .inr (F.tch tm.1 tm.2).1) ∧ ∀ c b, x = .inl (c, b) → c ∉ hs.flatten

variable {F}

theorem NonKey.not_mem {qs : List (Tweak × M)} {hs : List (List St)} {x : Cell St Blk}
    (hx : NonKey F qs hs x) (κ : Cell St Blk → Option St) (w : St) :
    (x, w) ∉ entries F κ qs hs := by
  intro h
  rcases entries_key F κ qs hs _ h with ⟨tm, htm, h1⟩ | ⟨c, b, h1, h2⟩
  · exact hx.1 tm htm h1
  · exact hx.2 c b h1 h2

theorem nonKey_inl {qs : List (Tweak × M)} {hs : List (List St)} {q : St × Blk}
    (h : q.1 ∉ hs.flatten) : NonKey F qs hs (.inl q) :=
  ⟨fun _ _ h' => by simp at h', fun c b h' => by
    obtain rfl : q = (c, b) := Sum.inl.inj h'
    exact h⟩

theorem nonKey_inr {qs : List (Tweak × M)} {hs : List (List St)} {B : Blk}
    (h : ∀ tm ∈ qs, (F.tch tm.1 tm.2).1 ≠ B) : NonKey F qs hs (.inr B) :=
  ⟨fun tm htm h' => h tm htm (Sum.inr.inj h').symm, fun c b h' => by simp at h'⟩

section Upd

variable [DecidableEq St] [DecidableEq Blk]

theorem build_of_nonKey {qs : List (Tweak × M)} {hs : List (List St)} {x : Cell St Blk}
    (hx : NonKey F qs hs x) (κ : Cell St Blk → Option St) : build F κ qs hs x = κ x :=
  MB.writeAll_of_not_mem _ _ _ fun w => hx.not_mem κ w

theorem writeAll_update (es : List (Cell St Blk × St)) (κ : Cell St Blk → Option St)
    (x : Cell St Blk) (v : Option St) (hx : ∀ w, (x, w) ∉ es) :
    writeAll es (Function.update κ x v) = Function.update (writeAll es κ) x v := by
  induction es generalizing κ with
  | nil => rfl
  | cons e es ih =>
    have hne : e.1 ≠ x := fun h => hx e.2 (by rw [← h]; exact List.mem_cons_self)
    rw [MB.writeAll_cons, MB.writeAll_cons, Function.update_comm hne.symm,
      ih _ fun w hw => hx w (List.mem_cons_of_mem _ hw)]

theorem writeAll_append (es es' : List (Cell St Blk × St)) (κ : Cell St Blk → Option St) :
    writeAll (es ++ es') κ = writeAll es' (writeAll es κ) := by
  simp [writeAll, List.foldl_append]

omit [DecidableEq St] [DecidableEq Blk] in
theorem entries_congr (κ κ' : Cell St Blk → Option St) (qs : List (Tweak × M))
    (hs : List (List St))
    (h : ∀ tm ∈ qs, κ' (.inr (F.tch tm.1 tm.2).1) = κ (.inr (F.tch tm.1 tm.2).1)) :
    entries F κ' qs hs = entries F κ qs hs := by
  unfold entries
  have key : ∀ T : List ((Tweak × M) × List St), (∀ p ∈ T, p.1 ∈ qs) →
      (T.flatMap fun p => chainCells (F.tch p.1.1 p.1.2) (tgtVals F κ' p.1 p.2)) =
        T.flatMap fun p => chainCells (F.tch p.1.1 p.1.2) (tgtVals F κ p.1 p.2) := by
    intro T
    induction T with
    | nil => intro _; rfl
    | cons p T ih =>
      intro hT
      rw [List.flatMap_cons, List.flatMap_cons, ih fun p hp => hT p (List.mem_cons_of_mem _ hp)]
      have : tgtVals F κ' p.1 p.2 = tgtVals F κ p.1 p.2 := by
        unfold tgtVals
        rw [h p.1 (hT p List.mem_cons_self)]
      rw [this]
  exact key _ fun p hp => (List.of_mem_zip hp).1

theorem build_update {qs : List (Tweak × M)} {hs : List (List St)} {x : Cell St Blk}
    (hx : NonKey F qs hs x) (κ : Cell St Blk → Option St) (u : St) :
    build F (Function.update κ x (some u)) qs hs =
      Function.update (build F κ qs hs) x (some u) := by
  unfold build
  rw [entries_congr κ (Function.update κ x (some u)) qs hs fun tm htm =>
    Function.update_of_ne (hx.1 tm htm).symm _ _]
  exact writeAll_update _ _ _ _ fun w => hx.not_mem κ w

/-- The built cache after a new target `tm` with hidden values `h` whose row cell gets `v`. -/
theorem build_append {qs : List (Tweak × M)} {hs : List (List St)} (hlen : hs.length = qs.length)
    (tm : Tweak × M) (hrow : ∀ tm' ∈ qs, (F.tch tm'.1 tm'.2).1 ≠ (F.tch tm.1 tm.2).1)
    (κ : Cell St Blk → Option St) (h : List St) (v c₁ : St) (t : List St)
    (hv : h ++ [v] = c₁ :: t) :
    build F (Function.update κ (.inr (F.tch tm.1 tm.2).1) (some v)) (qs ++ [tm]) (hs ++ [h]) =
      writeAll (pubCells (c₁ :: t) (F.tch tm.1 tm.2).2)
        (Function.update (build F κ qs hs) (.inr (F.tch tm.1 tm.2).1) (some c₁)) := by
  have hnk : NonKey F qs hs (.inr (F.tch tm.1 tm.2).1) := nonKey_inr hrow
  set κ₁ := Function.update κ (.inr (F.tch tm.1 tm.2).1) (some v) with hκ₁
  have he : entries F κ₁ (qs ++ [tm]) (hs ++ [h]) =
      entries F κ qs hs ++ chainCells (F.tch tm.1 tm.2) (c₁ :: t) := by
    have h1 : entries F κ₁ (qs ++ [tm]) (hs ++ [h]) =
        entries F κ₁ qs hs ++ chainCells (F.tch tm.1 tm.2) (tgtVals F κ₁ tm h) := by
      unfold entries
      rw [List.zip_append hlen.symm, List.flatMap_append]
      simp
    rw [h1, entries_congr κ κ₁ qs hs fun tm' htm' =>
      Function.update_of_ne (hnk.1 tm' htm').symm _ _]
    have : tgtVals F κ₁ tm h = c₁ :: t := by
      unfold tgtVals
      rw [hκ₁, Function.update_self]
      exact hv
    rw [this]
  unfold build
  rw [he, writeAll_append, writeAll_update _ _ _ _ fun w => hnk.not_mem κ w]
  simp only [chainCells]
  rw [MB.writeAll_cons, Function.update_idem]

omit [DecidableEq St] [DecidableEq Blk] in
theorem nice_of_cle {κ κ' : Cell St Blk → Option St} {hs : List (List St)}
    (h : Nice κ' hs) (hle : CLe κ κ') : Nice κ hs := by
  refine ⟨h.1, fun x hx b => ?_⟩
  cases hk : κ (.inl (x, b)) with
  | none => rfl
  | some v =>
    have := h.2 x hx b
    rw [hle _ _ hk] at this
    exact absurd this (by simp)

end Upd

/-! ## Drawing -/

theorem drawV_succ_snoc [SampleableType St] (n : ℕ) :
    drawV (St := St) (n + 1) =
      drawV n >>= fun h => ($ᵗ St : ProbComp St) >>= fun v => pure (h ++ [v]) := by
  induction n with
  | zero => simp [drawV]
  | succ n ih =>
    conv_lhs => rw [drawV, ih]
    conv_rhs => rw [drawV]
    simp [bind_assoc]

/-! ## Probability plumbing -/

theorem prE_pure_le {α β : Type} (a : α) (b : β) (P : α → Prop) (Q : β → Prop)
    (h : P a → Q b) :
    Pr{let x ← (pure a : ProbComp α)}[P x] ≤ Pr{let y ← (pure b : ProbComp β)}[Q y] := by
  classical
  rw [prEvent_pure, prEvent_pure]
  split_ifs with h1 h2
  · exact le_rfl
  · exact absurd (h h1) h2
  · exact zero_le
  · exact le_rfl

theorem prEvent_pure_eq_zero {α : Type} (a : α) (P : α → Prop) (h : ¬ P a) :
    Pr{let x ← (pure a : ProbComp α)}[P x] = 0 := by
  classical
  rw [prEvent_pure]
  simp [h]

/-! ## Folds of public queries in the lazy oracle -/

section RO

variable [DecidableEq St] [DecidableEq Blk] [SampleableType St]

/-- A fold of public queries, run in the lazy oracle. -/
noncomputable def foldRO (bs : List Blk) (c₀ : St) (C : Cache St Blk) :
    ProbComp (St × Cache St Blk) :=
  (simulateQ (hS St Blk + tS St Blk).romImpl
    (bs.foldlM (fun c b => (unifSpec + (hS St Blk + tS St Blk)).query (.inr (.inl (c, b))))
      c₀)).run C

theorem foldRO_nil (c₀ : St) (C : Cache St Blk) : foldRO [] c₀ C = pure (c₀, C) := by
  simp [foldRO]

theorem foldRO_cons (b : Blk) (bs : List Blk) (c₀ : St) (C : Cache St Blk) :
    foldRO (b :: bs) c₀ C =
      ((hS St Blk + tS St Blk).randomOracle (.inl (c₀, b))).run C >>= fun y =>
        foldRO bs y.1 y.2 := by
  simp [foldRO, List.foldlM_cons]

theorem ro_pub_run (κ : Cell St Blk → Option St) (q : St × Blk) :
    ((hS St Blk + tS St Blk).randomOracle (.inl q)).run (ofLook κ) =
      match κ (.inl q) with
      | some v => pure (v, ofLook κ)
      | none => (fun u : St => (u, ofLook (Function.update κ (.inl q) (some u)))) <$>
          ($ᵗ St : ProbComp St) := by
  rcases randomOracle_run_pub_cases q (ofLook κ) with ⟨v, hv, h⟩ | ⟨hn, h⟩
  · have hv' : κ (.inl q) = some v := hv
    rw [h, hv']
  · have hn' : κ (.inl q) = none := hn
    rw [h, hn']
    simp only [ofLook_update_inl]

theorem ro_row_run (κ : Cell St Blk → Option St) (B : Blk) :
    ((hS St Blk + tS St Blk).randomOracle (.inr B)).run (ofLook κ) =
      match κ (.inr B) with
      | some v => pure (v, ofLook κ)
      | none => (fun u : St => (u, ofLook (Function.update κ (.inr B) (some u)))) <$>
          ($ᵗ St : ProbComp St) := by
  rcases randomOracle_run_row_cases B (ofLook κ) with ⟨v, hv, h⟩ | ⟨hn, h⟩
  · have hv' : κ (.inr B) = some v := hv
    rw [h, hv']
  · have hn' : κ (.inr B) = none := hn
    rw [h, hn']
    simp only [ofLook_update_inr]

theorem ro_pub_support (q : St × Blk) (C : Cache St Blk) {y : St × Cache St Blk}
    (hy : y ∈ support (((hS St Blk + tS St Blk).randomOracle (.inl q)).run C)) :
    CLe (look C) (look y.2) ∧ look y.2 (.inl q) = some y.1 := by
  rcases randomOracle_run_pub_cases q C with ⟨v, hv, h⟩ | ⟨hn, h⟩
  · rw [h, support_pure, Set.mem_singleton_iff] at hy
    subst hy
    exact ⟨fun _ _ h => h, hv⟩
  · rw [h, support_map] at hy
    obtain ⟨u, -, rfl⟩ := hy
    refine ⟨fun x v hx => ?_, ?_⟩
    · rw [look_cacheQuery_inl, Function.update_of_ne, hx]
      rintro rfl
      rw [look_inl, hn] at hx
      exact absurd hx (by simp)
    · rw [look_cacheQuery_inl, Function.update_self]

theorem foldRO_support (bs : List Blk) (c₀ : St) (C : Cache St Blk) {z : St × Cache St Blk}
    (hz : z ∈ support (foldRO bs c₀ C)) : CLe (look C) (look z.2) := by
  induction bs generalizing c₀ C with
  | nil =>
    rw [foldRO_nil, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact fun _ _ h => h
  | cons b bs ih =>
    rw [foldRO_cons, mem_support_bind_iff] at hz
    obtain ⟨y, hy, hz⟩ := hz
    exact fun x v hx => ih _ _ hz x v ((ro_pub_support _ _ hy).1 x v hx)

theorem foldRO_cons_cached (b : Blk) (bs : List Blk) (c₀ : St) (C : Cache St Blk)
    {z : St × Cache St Blk} (hz : z ∈ support (foldRO (b :: bs) c₀ C)) :
    ∃ v, look z.2 (.inl (c₀, b)) = some v := by
  rw [foldRO_cons, mem_support_bind_iff] at hz
  obtain ⟨y, hy, hz⟩ := hz
  exact ⟨y.1, foldRO_support _ _ _ hz _ _ (ro_pub_support _ _ hy).2⟩

/-- The cells are pairwise distinct and uncached. -/
def FreshK (κ : Cell St Blk → Option St) (es : List (Cell St Blk × St)) : Prop :=
  (es.map Prod.fst).Nodup ∧ ∀ e ∈ es, κ e.1 = none

/-- A fold of public queries all of whose cells are fresh draws independent uniform values and
writes them. -/
theorem fold_dom (bs : List Blk) : ∀ (c₀ : St) (κ : Cell St Blk → Option St)
    (Q : St × Cache St Blk → Prop),
    Pr{let t ← drawV (St := St) bs.length}[
      Q (t.getLastD c₀, ofLook (writeAll (pubCells (c₀ :: t) bs) κ)) ∧
        FreshK κ (pubCells (c₀ :: t) bs)] ≤
      Pr{let z ← foldRO bs c₀ (ofLook κ)}[Q z] := by
  induction bs with
  | nil =>
    intro c₀ κ Q
    rw [foldRO_nil]
    simp only [List.length_nil, drawV]
    refine prE_pure_le _ _ _ _ fun h => ?_
    simpa [pubCells_nil_right, writeAll] using h.1
  | cons b bs ih =>
    intro c₀ κ Q
    rw [List.length_cons, drawV, foldRO_cons, ro_pub_run]
    cases hk : κ (.inl (c₀, b)) with
    | some w =>
      refine le_trans (le_of_eq ?_) zero_le
      refine le_antisymm (prEvent_bind_le_of_forall_le _ _ _ fun h => ?_) zero_le
      refine prEvent_bind_le_of_forall_le _ _ _ fun t => ?_
      refine le_of_eq (prEvent_pure_eq_zero _ _ fun hP => ?_)
      have := hP.2.2 (.inl (c₀, b), h) (by rw [MB.pubCells_cons_cons]; exact List.mem_cons_self)
      rw [hk] at this
      exact absurd this (by simp)
    | none =>
      dsimp only
      rw [bind_map_left]
      refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun h => ?_
      simp only [bind_pure_comp]
      rw [prEvent_map]
      refine le_trans (prEvent_mono _ _ _ fun t ht => ?_)
        (ih h (Function.update κ (.inl (c₀, b)) (some h)) Q)
      simp only [MB.pubCells_cons_cons, MB.writeAll_cons, List.getLastD_cons]
        at ht
      obtain ⟨h1, h2, h3⟩ := ht
      rw [List.map_cons, List.nodup_cons] at h2
      refine ⟨h1, h2.2, fun e he => ?_⟩
      rw [Function.update_of_ne, h3 e (List.mem_cons_of_mem _ he)]
      intro heq
      exact h2.1 (by rw [← heq]; exact List.mem_map.mpr ⟨e, he, rfl⟩)

variable (F : THFam St Blk PkSeed Tweak M Y ι)

/-- A fold of public queries on the symbolic cache, read through `build` and conjoined with a
nice final state, is dominated by the fold on the built cache. -/
theorem fold_sym_dom (qs : List (Tweak × M)) (hs : List (List St)) (bs : List Blk) :
    ∀ (c₀ : St) (κ : Cell St Blk → Option St) (Q : St × Cache St Blk → Prop),
    Pr{let z ← foldRO bs c₀ (ofLook κ)}[
      Q (z.1, ofLook (build F (look z.2) qs hs)) ∧ Nice (look z.2) hs] ≤
      Pr{let z ← foldRO bs c₀ (ofLook (build F κ qs hs))}[Q z] := by
  induction bs with
  | nil =>
    intro c₀ κ Q
    rw [foldRO_nil, foldRO_nil]
    refine prE_pure_le _ _ _ _ fun h => ?_
    simpa using h.1
  | cons b bs ih =>
    intro c₀ κ Q
    by_cases hc : c₀ ∈ hs.flatten
    · rw [prEvent_eq_zero_of_forall_mem_support _ _ fun z hz hP => ?_]
      · exact zero_le
      · obtain ⟨v, hv⟩ := foldRO_cons_cached _ _ _ _ hz
        rw [hP.2.2 c₀ hc b] at hv
        exact absurd hv (by simp)
    · have hnk : NonKey F qs hs (.inl (c₀, b)) := nonKey_inl (q := (c₀, b)) hc
      rw [foldRO_cons, foldRO_cons, ro_pub_run, ro_pub_run, build_of_nonKey hnk]
      cases hk : κ (.inl (c₀, b)) with
      | some w =>
        simp only [pure_bind]
        exact ih w κ Q
      | none =>
        dsimp only
        rw [bind_map_left, bind_map_left]
        refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun u => ?_
        rw [← build_update hnk]
        exact ih u _ Q

/-- A chain query run in the lazy oracle. -/
noncomputable def chainRun (X : Blk × List Blk) (C : Cache St Blk) :
    ProbComp (St × Cache St Blk) :=
  ((chainRO (St := St) (Blk := Blk)) (.inr (.inr X))).run C

theorem chainRun_eq (X : Blk × List Blk) (C : Cache St Blk) :
    chainRun X C = ((hS St Blk + tS St Blk).randomOracle (.inr X.1)).run C >>= fun z =>
      foldRO X.2 z.1 z.2 :=
  chainRO_run_chain X C

/-- A chain query whose row cell is no target row: the run on the symbolic cache, read through
`build` and conjoined with a nice final state, is dominated by the run on the built cache. -/
theorem chain_sym_dom (qs : List (Tweak × M)) (hs : List (List St)) (X : Blk × List Blk)
    (hX : ∀ tm ∈ qs, (F.tch tm.1 tm.2).1 ≠ X.1) (κ : Cell St Blk → Option St)
    (Q : St × Cache St Blk → Prop) :
    Pr{let z ← chainRun X (ofLook κ)}[
      Q (z.1, ofLook (build F (look z.2) qs hs)) ∧ Nice (look z.2) hs] ≤
      Pr{let z ← chainRun X (ofLook (build F κ qs hs))}[Q z] := by
  have hnk : NonKey F qs hs (.inr X.1) := nonKey_inr hX
  rw [chainRun_eq, chainRun_eq, ro_row_run, ro_row_run, build_of_nonKey hnk]
  cases hk : κ (.inr X.1) with
  | some w =>
    simp only [pure_bind]
    exact fold_sym_dom F qs hs X.2 w κ Q
  | none =>
    dsimp only
    rw [bind_map_left, bind_map_left]
    refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun u => ?_
    rw [← build_update hnk]
    exact fold_sym_dom F qs hs X.2 u _ Q

end RO

section Steps

variable [DecidableEq St] [DecidableEq Blk] [SampleableType St]

theorem chainRun_nil_fresh (B : Blk) (κ : Cell St Blk → Option St) (h : κ (.inr B) = none) :
    chainRun (B, []) (ofLook κ) =
      (fun u : St => (u, ofLook (Function.update κ (.inr B) (some u)))) <$>
        ($ᵗ St : ProbComp St) := by
  rw [chainRun_eq, ro_row_run, h]
  simp [foldRO_nil]

theorem chainRun_fresh (X : Blk × List Blk) (κ : Cell St Blk → Option St)
    (h : κ (.inr X.1) = none) :
    chainRun X (ofLook κ) = ($ᵗ St : ProbComp St) >>= fun c₁ =>
      foldRO X.2 c₁ (ofLook (Function.update κ (.inr X.1) (some c₁))) := by
  rw [chainRun_eq, ro_row_run, h]
  dsimp only
  rw [bind_map_left]

/-- The event that a list of drawn values, read as the chaining values of a fresh chain through
the blocks `rest`, has fresh public cells and satisfies `Q'` after they are written. -/
def RV (Q' : St × Cache St Blk → Prop) (rest : List Blk)
    (κC : St → Cell St Blk → Option St) : List St → Prop
  | [] => False
  | c₁ :: t => Q' (t.getLastD c₁, ofLook (writeAll (pubCells (c₁ :: t) rest) (κC c₁))) ∧
      FreshK (κC c₁) (pubCells (c₁ :: t) rest)

theorem chain_fresh_dom (Q' : St × Cache St Blk → Prop) (rest : List Blk)
    (κC : St → Cell St Blk → Option St) :
    Pr{let vals ← drawV (St := St) (rest.length + 1)}[RV Q' rest κC vals] ≤
      Pr{let z ← ($ᵗ St : ProbComp St) >>= fun c₁ => foldRO rest c₁ (ofLook (κC c₁))}[Q' z] := by
  rw [drawV]
  refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun c₁ => ?_
  simp only [bind_pure_comp]
  rw [prEvent_map]
  exact fold_dom rest c₁ (κC c₁) Q'

variable (F : THFam St Blk PkSeed Tweak M Y ι)

theorem pub_sym_dom (qs : List (Tweak × M)) (hs : List (List St)) (q : St × Blk)
    (κ : Cell St Blk → Option St) (Q : St × Cache St Blk → Prop) :
    Pr{let z ← ((hS St Blk + tS St Blk).randomOracle (.inl q)).run (ofLook κ)}[
      Q (z.1, ofLook (build F (look z.2) qs hs)) ∧ Nice (look z.2) hs] ≤
      Pr{let z ← ((hS St Blk + tS St Blk).randomOracle (.inl q)).run (ofLook (build F κ qs hs))}[Q z] := by
  have := fold_sym_dom F qs hs [q.2] q.1 κ Q
  simpa [foldRO_cons, foldRO_nil] using this

variable [DecidableEq Tweak]

theorem symE_run (L : ℕ) (t : F.advS.Domain)
    (S : (SM_DT_TCR_State Tweak M × Cache St Blk) × List (List St)) :
    (symE F L t).run S =
      if accepts F t S.1.1 then
        drawV L >>= fun h => (fun z => (z.1, (z.2, S.2 ++ [h]))) <$> (symD F t).run S.1
      else (fun z => (z.1, (z.2, S.2))) <$> (symD F t).run S.1 := rfl

theorem symD_run (t : F.advS.Domain) (s : SM_DT_TCR_State Tweak M) (c : Cache St Blk) :
    (symD F t).run (s, c) = (fun y => (y.1.1, (y.1.2, y.2))) <$>
      (simulateQ chainRO ((tcrGameM F.single t).run s)).run c := rfl

theorem conG_run (t : F.advS.Domain) (s : SM_DT_TCR_State Tweak M) (c : Cache St Blk) :
    (conG F t).run (s, c) = (fun y => (y.1.1, (y.1.2, y.2))) <$>
      (simulateQ chainRO ((tcrGameM F t).run s)).run c := rfl

end Steps

end MD

open MD in
/-- **Domination of the eager symbolic phase one by the real phase one.** -/
theorem dominated_symE [DecidableEq St] [DecidableEq Blk] [SampleableType St] [DecidableEq Tweak]
    (F : THFam St Blk PkSeed Tweak M Y ι) (L : ℕ) (hlen : ∀ t m, (F.tch t m).2.length = L)
    (btw : Blk → Tweak) (hbtwT : ∀ t m, btw (F.tch t m).1 = t)
    (hbtwC : ∀ i t m, btw (F.cch i t m).1 = t) :
    QueryImpl.DominatedUntilBad (symE F L) (conG F) (fbuild F)
      (fun S => SInv F btw L S.1.1 S.1.2 S.2) (fun S => ¬ Nice (look S.1.2) S.2) := by
  rintro t ⟨⟨⟨qs, tw⟩, c⟩, hs⟩ hinv hbad Q
  obtain ⟨κ, rfl⟩ : ∃ κ, c = ofLook κ := ⟨look c, (ofLook_look c).symm⟩
  dsimp only at hinv hbad
  have hf : fbuild F (((qs, tw), ofLook κ), hs) =
      ((qs, tw), ofLook (build F κ qs hs)) := by simp [fbuild]
  rw [hf]
  rcases t with n | q | tm | q
  · have hacc : ¬ accepts F (.inl n) (qs, tw) := fun h => h
    rw [symE_run, if_neg hacc, symD_run, conG_run, run_tcrGameM_inl, run_tcrGameM_inl,
      chainRO_run_inl, chainRO_run_inl]
    simp only [Functor.map_map]
    exact prEvent_mono _ _ _ fun u hu => by rw [← hf]; exact hu.1
  · have hacc : ¬ accepts F (.inr (.inl q)) (qs, tw) := fun h => h
    rw [symE_run, if_neg hacc, symD_run, conG_run, run_tcrGameM_pub, run_tcrGameM_pub,
      chainRO_run_pub, chainRO_run_pub]
    simp only [Functor.map_map]
    refine le_trans (prEvent_mono _ _ _ fun z hz => ?_)
      (pub_sym_dom F qs hs q κ fun z => Q (z.1, ((qs, tw), z.2)))
    exact ⟨hz.1, not_not.mp hz.2⟩
  · rw [symE_run, symD_run, conG_run, run_tcrGameM_chal, run_tcrGameM_chal]
    by_cases hcond : F.numTargets ≤ qs.length ∨ ¬ TweakFresh Prod.fst qs tw tm.1
    · have hacc : ¬ accepts F (.inr (.inr (.inl tm))) (qs, tw) := fun h => h hcond
      rw [if_neg hacc, if_pos hcond, if_pos hcond]
      simp only [map_pure]
      exact prE_pure_le _ _ _ _ fun h => by rw [← hf]; exact h.1
    · have hacc : accepts F (.inr (.inr (.inl tm))) (qs, tw) := hcond
      rw [if_pos hacc, if_neg hcond, if_neg hcond]
      have hfresh : TweakFresh Prod.fst qs tw tm.1 := by
        by_contra h
        exact hcond (.inr h)
      have hrowne : ∀ tm' ∈ qs, (F.tch tm'.1 tm'.2).1 ≠ (F.tch tm.1 tm.2).1 := by
        intro tm' htm' heq
        have := congrArg btw heq
        rw [hbtwT, hbtwT] at this
        exact hfresh.1 ⟨tm', htm', this⟩
      have hrow : κ (.inr (F.tch tm.1 tm.2).1) = none := by
        cases hk : κ (.inr (F.tch tm.1 tm.2).1) with
        | none => rfl
        | some w =>
          exfalso
          have hsome : ((ofLook κ) (.inr (F.tch tm.1 tm.2).1)).isSome := by
            rw [show (ofLook κ) (.inr (F.tch tm.1 tm.2).1) = κ (.inr (F.tch tm.1 tm.2).1) from rfl,
              hk]
            rfl
          rcases hinv.tcr.2.2.1 (F.tch tm.1 tm.2).1 hsome with ⟨m, hm, -⟩ | h
          · rw [hbtwT] at hm
            exact hfresh.1 ⟨_, hm, rfl⟩
          · rw [hbtwT] at h
            exact hfresh.2 h
      have hrowC : build F κ qs hs (.inr (F.tch tm.1 tm.2).1) = none := by
        rw [build_of_nonKey (nonKey_inr hrowne), hrow]
      have e1 := chainRun_nil_fresh (F.tch tm.1 tm.2).1 κ hrow
      have e2 := chainRun_fresh (F.tch tm.1 tm.2) (build F κ qs hs) hrowC
      unfold chainRun at e1 e2
      dsimp only [THFam.single]
      rw [e1, e2]
      simp only [Functor.map_map]
      have step2 := chain_fresh_dom (fun z => Q (some (F.out z.1), ((qs ++ [tm], tw), z.2)))
        (F.tch tm.1 tm.2).2
        fun c₁ => Function.update (build F κ qs hs) (.inr (F.tch tm.1 tm.2).1) (some c₁)
      rw [hlen] at step2
      refine le_trans ?_ step2
      rw [drawV_succ_snoc]
      refine prEvent_bind_mono_of_forall_le_of_support _ _ _ _ _ fun h hh => ?_
      have hhl : h.length = L := MB.length_of_mem_support_drawV L h hh
      simp only [bind_pure_comp, prEvent_map]
      refine prEvent_mono _ _ _ fun v hv => ?_
      obtain ⟨c₁, t, hct⟩ : ∃ c₁ t, h ++ [v] = c₁ :: t := by
        cases h with
        | nil => exact ⟨v, [], rfl⟩
        | cons a h' => exact ⟨a, h' ++ [v], rfl⟩
      have hN : Nice (Function.update κ (.inr (F.tch tm.1 tm.2).1) (some v)) (hs ++ [h]) := by
        have := not_not.mp hv.2
        simpa using this
      have hb := build_append hinv.len tm hrowne κ h v c₁ t hct
      have hlast : t.getLastD c₁ = v := by
        have := congrArg List.getLast? hct
        simpa [List.getLast?_cons] using this.symm
      have hdl : (c₁ :: t).dropLast = h := by rw [← hct]; simp
      have htl : t.length = (F.tch tm.1 tm.2).2.length := by
        have := congrArg List.length hct
        simp at this
        rw [hlen]
        omega
      have hnd : (hs.flatten ++ h).Nodup := by simpa using hN.1
      have hnd' := List.nodup_append.mp hnd
      show RV _ _ _ (h ++ [v])
      rw [hct]
      refine ⟨?_, ?_, ?_⟩
      · rw [hlast, ← hb]
        simpa [fbuild] using hv.1
      · have hG := MB.pubCells_G (F.tch tm.1 tm.2).2 c₁ t htl
        rw [hdl] at hG
        have h2 : (h.map (Sum.inl : St → St ⊕ Blk)).Nodup := hnd'.2.1.map Sum.inl_injective
        rw [← hG] at h2
        have h3 : (((pubCells (c₁ :: t) (F.tch tm.1 tm.2).2).map Prod.fst).map MB.G).Nodup := by
          rw [List.map_map]
          exact h2
        exact h3.of_map _
      · intro e he
        obtain ⟨c₀, b₀, he1, he2⟩ := pubCells_key _ _ e he
        rw [hdl] at he2
        have hc₀ : c₀ ∉ hs.flatten := fun hmem => hnd'.2.2 c₀ hmem c₀ he2 rfl
        rw [he1]
        dsimp only
        rw [Function.update_of_ne (by simp),
          build_of_nonKey (nonKey_inl (q := (c₀, b₀)) hc₀)]
        have := hN.2 c₀ (by simp [he2]) b₀
        rwa [Function.update_of_ne (by simp)] at this
  · have hacc : ¬ accepts F (.inr (.inr (.inr q))) (qs, tw) := fun h => h
    rw [symE_run, if_neg hacc, symD_run, conG_run, run_tcrGameM_coll, run_tcrGameM_coll]
    by_cases hres : TweakReserved (Q := Tweak × M) Prod.fst qs q.2.1
    · rw [if_pos hres, if_pos hres]
      simp only [map_pure]
      exact prE_pure_le _ _ _ _ fun h => by rw [← hf]; exact h.1
    · rw [if_neg hres, if_neg hres]
      simp only [Functor.map_map]
      have hX : ∀ tm ∈ qs, (F.tch tm.1 tm.2).1 ≠ (F.cch q.1 q.2.1 q.2.2).1 := by
        intro tm' htm' heq
        have := congrArg btw heq
        rw [hbtwT, hbtwC] at this
        exact hres ⟨tm', htm', this⟩
      refine le_trans (prEvent_mono _ _ _ fun z hz => ?_)
        (chain_sym_dom F qs hs (F.cch q.1 q.2.1 q.2.2) hX κ
          fun z => Q (some (F.cout q.1 z.1), ((qs, tw ++ [q.2.1]), z.2)))
      exact ⟨hz.1, not_not.mp hz.2⟩

end Ideal

#print axioms Ideal.dominated_symE
