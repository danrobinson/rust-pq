import Ideal.Games.TcrMultiBasic

/-!
# Multi-block SM-TCR: the cache built from a symbolic state

* `build_good`: if the symbolic state satisfies its deterministic invariant `SInv`, the symbolic
  cache is injective and holds no `IV`, and the hidden values are fresh (`FillNice`), the built
  cache satisfies the phase-one invariant `MInv` and has at most `N + #targets * (L + 1)` cells.
* `prEvent_drawN_not_fillNice`: freshly drawn hidden values fail `FillNice` with probability at
  most `(n L) (n L + 2 N + 1) / |St|`.
-/

open OracleComp OracleSpec ENNReal

namespace Ideal

open TweakableHash

variable {St Blk PkSeed Tweak M Y ι : Type}

namespace MB

/-! ## `writeAll` -/

section WriteAll

variable [DecidableEq St] [DecidableEq Blk]

theorem writeAll_cons (e : Cell St Blk × St) (es : List (Cell St Blk × St))
    (κ : Cell St Blk → Option St) :
    writeAll (e :: es) κ = writeAll es (Function.update κ e.1 (some e.2)) := rfl

/-- A cell that is no key keeps its base value. -/
theorem writeAll_of_not_mem (es : List (Cell St Blk × St)) (κ : Cell St Blk → Option St)
    (x : Cell St Blk) (hx : ∀ w, (x, w) ∉ es) : writeAll es κ x = κ x := by
  induction es generalizing κ with
  | nil => rfl
  | cons e es ih =>
    rw [writeAll_cons, ih _ (fun w hw => hx w (List.mem_cons_of_mem _ hw))]
    exact Function.update_of_ne (fun h => hx e.2 (by rw [h]; exact List.mem_cons_self)) _ _

/-- A value of the written cache is an entry, or the base value at a cell that is no key. -/
theorem writeAll_cases (es : List (Cell St Blk × St)) (κ : Cell St Blk → Option St)
    (x : Cell St Blk) (w : St) (h : writeAll es κ x = some w) :
    (x, w) ∈ es ∨ (κ x = some w ∧ ∀ w', (x, w') ∉ es) := by
  induction es generalizing κ with
  | nil => exact .inr ⟨h, fun _ h => by simp at h⟩
  | cons e es ih =>
    rw [writeAll_cons] at h
    rcases ih _ h with h1 | ⟨h1, h2⟩
    · exact .inl (List.mem_cons_of_mem _ h1)
    · by_cases hx : x = e.1
      · subst hx
        rw [Function.update_self] at h1
        obtain rfl := Option.some.inj h1
        exact .inl List.mem_cons_self
      · rw [Function.update_of_ne hx] at h1
        refine .inr ⟨h1, fun w' hw' => ?_⟩
        rcases List.mem_cons.mp hw' with h3 | h3
        · exact hx (congrArg Prod.fst h3)
        · exact h2 w' h3

/-- Every entry of a functional list of entries is present in the written cache. -/
theorem writeAll_mem (es : List (Cell St Blk × St)) (κ : Cell St Blk → Option St)
    (hf : ∀ x w w', (x, w) ∈ es → (x, w') ∈ es → w = w') (x : Cell St Blk) (w : St)
    (h : (x, w) ∈ es) : writeAll es κ x = some w := by
  induction es generalizing κ w with
  | nil => simp at h
  | cons e es ih =>
    rw [writeAll_cons]
    by_cases hk : ∃ w', (x, w') ∈ es
    · obtain ⟨w', hw'⟩ := hk
      rw [ih _ (fun x w w' h1 h2 => hf x w w' (List.mem_cons_of_mem _ h1)
        (List.mem_cons_of_mem _ h2)) w' hw']
      exact congrArg some (hf x w' w (List.mem_cons_of_mem _ hw') h)
    · rw [writeAll_of_not_mem _ _ _ fun w' hw' => hk ⟨w', hw'⟩]
      rcases List.mem_cons.mp h with h3 | h3
      · subst h3
        exact Function.update_self ..
      · exact absurd ⟨w, h3⟩ hk

end WriteAll

/-! ## The cells of a chain -/

/-- The row of a cell: the chaining value of a public cell, the block of a private-row cell. -/
def G : Cell St Blk → St ⊕ Blk
  | .inl q => .inl q.1
  | .inr B => .inr B

theorem pubCells_cons_cons (c c' : St) (t : List St) (b : Blk) (bs : List Blk) :
    pubCells (c :: c' :: t) (b :: bs) = (.inl (c, b), c') :: pubCells (c' :: t) bs := by
  simp [pubCells]

theorem pubCells_snd (bs : List Blk) (c : St) (t : List St) (h : t.length = bs.length) :
    (pubCells (c :: t) bs).map Prod.snd = t := by
  induction bs generalizing c t with
  | nil =>
    obtain rfl := List.length_eq_zero_iff.mp h
    simp [pubCells]
  | cons b bs ih =>
    cases t with
    | nil => simp at h
    | cons c' t =>
      rw [pubCells_cons_cons, List.map_cons, ih c' t (by simpa using h)]

theorem pubCells_G (bs : List Blk) (c : St) (t : List St) (h : t.length = bs.length) :
    (pubCells (c :: t) bs).map (fun e => G e.1) = ((c :: t).dropLast).map Sum.inl := by
  induction bs generalizing c t with
  | nil =>
    obtain rfl := List.length_eq_zero_iff.mp h
    simp [pubCells]
  | cons b bs ih =>
    cases t with
    | nil => simp at h
    | cons c' t =>
      rw [pubCells_cons_cons, List.map_cons, ih c' t (by simpa using h)]
      simp [G]

theorem chainCells_snd (X : Blk × List Blk) (vals : List St)
    (h : vals.length = X.2.length + 1) : (chainCells X vals).map Prod.snd = vals := by
  cases vals with
  | nil => simp at h
  | cons c t =>
    simp only [chainCells, List.map_cons]
    rw [pubCells_snd _ _ _ (by simpa using h)]

theorem chainCells_G (X : Blk × List Blk) (vals : List St)
    (h : vals.length = X.2.length + 1) :
    (chainCells X vals).map (fun e => G e.1) = .inr X.1 :: vals.dropLast.map Sum.inl := by
  cases vals with
  | nil => simp at h
  | cons c t =>
    simp only [chainCells, List.map_cons]
    rw [pubCells_G _ _ _ (by simpa using h)]
    rfl

/-! ## Walking along a chain -/

theorem walk_complete (κ : Cell St Blk → Option St) (bs : List Blk) (c : St) (t : List St)
    (h : t.length = bs.length) (hc : ∀ e ∈ pubCells (c :: t) bs, κ e.1 = some e.2) :
    (walk κ c bs).isSome := by
  induction bs generalizing c t with
  | nil => simp [walk]
  | cons b bs ih =>
    cases t with
    | nil => simp at h
    | cons c' t =>
      rw [pubCells_cons_cons] at hc
      have h1 : κ (.inl (c, b)) = some c' := hc _ List.mem_cons_self
      simp only [walk, h1, Option.bind_some]
      exact ih c' t (by simpa using h) fun e he => hc e (List.mem_cons_of_mem _ he)

theorem walk_unique (κ : Cell St Blk → Option St) (bs : List Blk) (c : St) (t : List St)
    (bs' : List Blk) (h : t.length = bs.length) (h' : bs'.length = bs.length)
    (hc : ∀ c₀ b c', (Sum.inl (c₀, b), c') ∈ pubCells (c :: t) bs →
      ∀ b' w', κ (.inl (c₀, b')) = some w' → b' = b ∧ w' = c')
    (hw : (walk κ c bs').isSome) : bs' = bs := by
  induction bs generalizing c t bs' with
  | nil => exact List.length_eq_zero_iff.mp h'
  | cons b bs ih =>
    cases t with
    | nil => simp at h
    | cons c' t =>
      cases bs' with
      | nil => simp at h'
      | cons b' bs' =>
        rw [pubCells_cons_cons] at hc
        simp only [walk] at hw
        cases hκ : κ (.inl (c, b')) with
        | none => simp [hκ] at hw
        | some w' =>
          simp only [hκ, Option.bind_some] at hw
          obtain ⟨rfl, rfl⟩ := hc c b c' List.mem_cons_self b' w' hκ
          rw [ih w' t bs' (by simpa using h) (by simpa using h')
            (fun c₀ b₀ c₁ he => hc c₀ b₀ c₁ (List.mem_cons_of_mem _ he)) hw]

/-! ## Lists -/

theorem length_flatMap_const {α β : Type} (l : List α) (f : α → List β) (k : ℕ)
    (h : ∀ a ∈ l, (f a).length = k) : (l.flatMap f).length = l.length * k := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.flatMap_cons, List.length_append, h a List.mem_cons_self,
      ih fun a ha => h a (List.mem_cons_of_mem _ ha), List.length_cons]
    ring

/-! ## The entries of all targets -/

section Core

variable (F : THFam St Blk PkSeed Tweak M Y ι) (κ : Cell St Blk → Option St)

/-- The entries of a list of targets with their hidden values. -/
def ent (T : List ((Tweak × M) × List St)) : List (Cell St Blk × St) :=
  T.flatMap fun p => chainCells (F.tch p.1.1 p.1.2) (tgtVals F κ p.1 p.2)

variable {F κ}

theorem tgtVals_eq {p : (Tweak × M) × List St} {v : St}
    (hv : κ (.inr (F.tch p.1.1 p.1.2).1) = some v) : tgtVals F κ p.1 p.2 = p.2 ++ [v] := by
  simp [tgtVals, hv]

/-- Distinct entries have distinct rows and distinct values. -/
theorem ent_nodup (T : List ((Tweak × M) × List St))
    (hrow : ∀ p ∈ T, ∃ v, κ (.inr (F.tch p.1.1 p.1.2).1) = some v)
    (hL : ∀ p ∈ T, p.2.length = (F.tch p.1.1 p.1.2).2.length)
    (hrowinj : T.Pairwise fun p p' => (F.tch p.1.1 p.1.2).1 ≠ (F.tch p'.1.1 p'.1.2).1)
    (hnd : (T.flatMap Prod.snd).Nodup) (hinj : CInj κ)
    (hhid : ∀ p ∈ T, ∀ h ∈ p.2, ∀ x, κ x ≠ some h) :
    ((ent F κ T).map fun e => G e.1).Nodup ∧ ((ent F κ T).map Prod.snd).Nodup := by
  rw [List.nodup_flatMap] at hnd
  obtain ⟨hnd1, hnd2⟩ := hnd
  have hpw := hrowinj.and hnd2
  unfold ent
  rw [List.map_flatMap, List.map_flatMap, List.nodup_flatMap, List.nodup_flatMap]
  refine ⟨⟨fun p hp => ?_, hpw.imp_of_mem fun {p p'} hp hp' hR => ?_⟩,
    ⟨fun p hp => ?_, hpw.imp_of_mem fun {p p'} hp hp' hR => ?_⟩⟩
  · obtain ⟨v, hv⟩ := hrow p hp
    rw [tgtVals_eq hv, chainCells_G _ _ (by simp [hL p hp]), List.dropLast_concat]
    refine List.nodup_cons.mpr ⟨by simp, (hnd1 p hp).map Sum.inl_injective⟩
  · obtain ⟨v, hv⟩ := hrow p hp
    obtain ⟨v', hv'⟩ := hrow p' hp'
    simp only [Function.onFun] at hR ⊢
    rw [tgtVals_eq hv, tgtVals_eq hv', chainCells_G _ _ (by simp [hL p hp]),
      chainCells_G _ _ (by simp [hL p' hp']), List.dropLast_concat, List.dropLast_concat]
    intro a h1 h2
    rcases List.mem_cons.mp h1 with rfl | h1
    · rcases List.mem_cons.mp h2 with h2 | h2
      · exact hR.1 (Sum.inr.inj h2)
      · simp at h2
    · rcases List.mem_cons.mp h2 with rfl | h2
      · simp at h1
      · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h1
        obtain ⟨y, hy, hxy⟩ := List.mem_map.mp h2
        obtain rfl := Sum.inl.inj hxy
        exact hR.2 hx hy
  · obtain ⟨v, hv⟩ := hrow p hp
    rw [tgtVals_eq hv, chainCells_snd _ _ (by simp [hL p hp])]
    refine List.nodup_append.mpr ⟨hnd1 p hp, List.nodup_singleton v, ?_⟩
    intro a ha b hb
    obtain rfl := List.mem_singleton.mp hb
    rintro rfl
    exact hhid p hp a ha _ hv
  · obtain ⟨v, hv⟩ := hrow p hp
    obtain ⟨v', hv'⟩ := hrow p' hp'
    simp only [Function.onFun] at hR ⊢
    rw [tgtVals_eq hv, tgtVals_eq hv', chainCells_snd _ _ (by simp [hL p hp]),
      chainCells_snd _ _ (by simp [hL p' hp'])]
    intro a h1 h2
    rcases List.mem_append.mp h1 with h1 | h1
    · rcases List.mem_append.mp h2 with h2 | h2
      · exact hR.2 h1 h2
      · obtain rfl := List.mem_singleton.mp h2
        exact hhid p hp a h1 _ hv'
    · obtain rfl := List.mem_singleton.mp h1
      rcases List.mem_append.mp h2 with h2 | h2
      · exact hhid p' hp' a h2 _ hv
      · obtain rfl := List.mem_singleton.mp h2
        exact hR.1 (Sum.inr.inj (hinj _ _ _ hv hv'))

end Core

/-! ## Drawing fresh values -/

section Prob

variable [Fintype St] [SampleableType St]

/-- The values `t` are pairwise distinct and avoid the list `S`. -/
def Fresh (S : List St) (t : List St) : Prop := t.Nodup ∧ ∀ h ∈ t, h ∉ S

/-- The chaining value of a public cell. -/
def rowOf : Cell St Blk → Option St
  | .inl q => some q.1
  | .inr _ => none

theorem prEvent_uniform_mem_le (S : List St) :
    Pr{let u ← ($ᵗ St : ProbComp St)}[u ∈ S] ≤
      (S.length : ℕ) * (Fintype.card St : ℝ≥0∞)⁻¹ := by
  induction S with
  | nil =>
    rw [prEvent_eq_zero_of_forall_not _ _ (by simp)]
    exact zero_le
  | cons a S ih =>
    refine (prEvent_mono _ _ (fun u => u = a ∨ u ∈ S) (by simp)).trans ?_
    refine (prEvent_or_le _ _ _).trans ?_
    rw [SampleableType.prEvent_uniformSample_eq_singleton]
    refine (add_le_add le_rfl ih).trans (le_of_eq ?_)
    push_cast [List.length_cons]
    ring

theorem prEvent_drawV_not_fresh (k : ℕ) (S : List St) :
    Pr{let t ← drawV (St := St) k}[¬ Fresh S t] ≤
      (k * (k + S.length) : ℕ) * (Fintype.card St : ℝ≥0∞)⁻¹ := by
  classical
  induction k generalizing S with
  | zero =>
    simp only [drawV]
    rw [prEvent_pure]
    simp [Fresh]
  | succ k ih =>
    simp only [drawV]
    refine (prEvent_bind_le_prEvent_add _ _ (fun h => h ∈ S) _
      (ε := (k * (k + (S.length + 1)) : ℕ) * (Fintype.card St : ℝ≥0∞)⁻¹) fun h hh => ?_).trans ?_
    · simp only [bind_pure_comp]
      rw [prEvent_map]
      refine (prEvent_mono _ _ (fun t => ¬ Fresh (h :: S) t) fun t ht hf => ht ?_).trans
        ((ih (h :: S)).trans (le_of_eq (by simp)))
      refine ⟨List.nodup_cons.mpr ⟨fun hm => hf.2 h hm List.mem_cons_self, hf.1⟩, fun x hx => ?_⟩
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hh
      · exact fun hxS => hf.2 x hx (List.mem_cons_of_mem _ hxS)
    · refine (add_le_add (prEvent_uniform_mem_le S) le_rfl).trans ?_
      rw [← add_mul, ← Nat.cast_add]
      refine mul_le_mul' (Nat.cast_le.mpr ?_) le_rfl
      nlinarith [Nat.zero_le k, Nat.zero_le S.length]

omit [Fintype St] in
theorem length_of_mem_support_drawV (k : ℕ) (t : List St)
    (h : t ∈ support (drawV (St := St) k)) : t.length = k := by
  induction k generalizing t with
  | zero =>
    simp only [drawV, support_pure, Set.mem_singleton_iff] at h
    rw [h]; rfl
  | succ k ih =>
    simp only [drawV, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at h
    obtain ⟨a, -, t', ht', rfl⟩ := h
    simp [ih t' ht']

omit [Fintype St] in
theorem length_flatten_of_mem_support_drawN (L n : ℕ) (hs : List (List St))
    (h : hs ∈ support (drawN (St := St) L n)) : hs.flatten.length = n * L := by
  induction n generalizing hs with
  | zero =>
    simp only [drawN, support_pure, Set.mem_singleton_iff] at h
    rw [h]; simp
  | succ n ih =>
    simp only [drawN, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at h
    obtain ⟨hs', hhs', t, ht, rfl⟩ := h
    rw [List.flatten_append, List.length_append, ih hs' hhs']
    simp [length_of_mem_support_drawV L t ht]
    ring

theorem prEvent_drawN_not_fresh (L n : ℕ) (S : List St) :
    Pr{let hs ← drawN (St := St) L n}[¬ Fresh S hs.flatten] ≤
      ((n * L) * (n * L + S.length) : ℕ) * (Fintype.card St : ℝ≥0∞)⁻¹ := by
  classical
  induction n with
  | zero =>
    simp only [drawN]
    rw [prEvent_pure]
    simp [Fresh]
  | succ n ih =>
    simp only [drawN]
    refine (prEvent_bind_le_prEvent_add_of_support _ _ (fun hs => ¬ Fresh S hs.flatten) _
      (ε := (L * (L + (n * L + S.length)) : ℕ) * (Fintype.card St : ℝ≥0∞)⁻¹)
      fun hs hsupp hh => ?_).trans ?_
    · rw [not_not] at hh
      simp only [bind_pure_comp]
      rw [prEvent_map]
      refine (prEvent_mono _ _ (fun t => ¬ Fresh (hs.flatten ++ S) t) fun t ht hf => ht ?_).trans
        ((prEvent_drawV_not_fresh L (hs.flatten ++ S)).trans (le_of_eq ?_))
      · have hfl : (hs ++ [t]).flatten = hs.flatten ++ t := by simp
        refine ⟨?_, fun x hx => ?_⟩
        · rw [hfl]
          refine List.nodup_append.mpr ⟨hh.1, hf.1, ?_⟩
          rintro a ha b hb rfl
          exact hf.2 a hb (List.mem_append_left _ ha)
        · rw [hfl] at hx
          rcases List.mem_append.mp hx with hx | hx
          · exact hh.2 x hx
          · exact fun hxS => hf.2 x hx (List.mem_append_right _ hxS)
      · rw [List.length_append, length_flatten_of_mem_support_drawN L n hs hsupp]
    · refine (add_le_add ih le_rfl).trans ?_
      rw [← add_mul, ← Nat.cast_add]
      refine mul_le_mul' (Nat.cast_le.mpr ?_) le_rfl
      nlinarith [Nat.zero_le (n * L), Nat.zero_le L, Nat.zero_le S.length]

end Prob

end MB

open MB in
/-- **The built cache is good.**  From the deterministic invariant of the symbolic state, an
injective symbolic cache without `IV` and fresh hidden values, the built cache satisfies the
phase-one invariant and has at most `N + #targets * (L + 1)` cells. -/
theorem build_good [DecidableEq St] [DecidableEq Blk] [SampleableType St]
    {F : THFam St Blk PkSeed Tweak M Y ι} (L : ℕ) (hlen : ∀ t m, (F.tch t m).2.length = L)
    (btw : Blk → Tweak) (hbtwT : ∀ t m, btw (F.tch t m).1 = t)
    {s : SM_DT_TCR_State Tweak M} {c : Cache St Blk} {hs : List (List St)} {N : ℕ}
    (hS : SInv F btw L s c hs) (hinj : CInj (look c)) (hiv : ∀ x, look c x ≠ some F.IV)
    (hN : FillNice F.IV (look c) hs) (hfin : CFin (look c) N) :
    MInv F btw L s.1 (build F (look c) s.1 hs) ∧
      CFin (build F (look c) s.1 hs) (N + s.1.length * (L + 1)) := by
  classical
  obtain ⟨qs, tw⟩ := s
  obtain ⟨⟨ha, hb, hc, hd⟩, hndq, hlenhs, hlenL⟩ := hS
  dsimp only at ha hb hc hd hndq hlenhs
  show MInv F btw L qs (build F (look c) qs hs) ∧
    CFin (build F (look c) qs hs) (N + qs.length * (L + 1))
  obtain ⟨hnd, hfill⟩ := hN
  generalize hκ : look c = κ at hinj hiv hfill hfin ⊢
  have hb' : ∀ t m, (t, m) ∈ qs → ∃ v, κ (.inr (F.tch t m).1) = some v := fun t m hm => by
    rw [← hκ]; exact Option.isSome_iff_exists.mp (hb t m hm)
  have hc' : ∀ B v, κ (.inr B) = some v →
      (∃ m, (btw B, m) ∈ qs ∧ B = (F.tch (btw B) m).1) ∨ btw B ∈ tw := fun B v hv => by
    rw [← hκ] at hv
    exact hc B (by rw [show c (.inr B) = some v from hv]; rfl)
  clear hb hc hκ
  let T := List.zip qs hs
  have hT1 : T.map Prod.fst = qs := List.map_fst_zip (by omega)
  have hT2 : T.map Prod.snd = hs := List.map_snd_zip (by omega)
  have hmem1 : ∀ p ∈ T, p.1 ∈ qs := fun p hp => by
    rw [← hT1]; exact List.mem_map_of_mem hp
  have hmem2 : ∀ p ∈ T, p.2 ∈ hs := fun p hp => by
    rw [← hT2]; exact List.mem_map_of_mem hp
  have hrow : ∀ p ∈ T, ∃ v, κ (.inr (F.tch p.1.1 p.1.2).1) = some v := fun p hp =>
    hb' p.1.1 p.1.2 (hmem1 p hp)
  have hL : ∀ p ∈ T, p.2.length = (F.tch p.1.1 p.1.2).2.length := fun p hp => by
    rw [hlenL _ (hmem2 p hp), hlen]
  have hpw1 : T.Pairwise fun p p' => p.1.1 ≠ p'.1.1 := by
    have h1 : T.map (fun p => p.1.1) = qs.map Prod.fst := by
      rw [← hT1, List.map_map]; rfl
    have h2 : (T.map fun p => p.1.1).Nodup := by rw [h1]; exact hndq
    exact List.pairwise_map.mp h2
  have hrowinj : T.Pairwise fun p p' =>
      (F.tch p.1.1 p.1.2).1 ≠ (F.tch p'.1.1 p'.1.2).1 :=
    hpw1.imp fun {p p'} h e => h (by have := congrArg btw e; rwa [hbtwT, hbtwT] at this)
  have hflat : T.flatMap Prod.snd = hs.flatten := by
    rw [← hT2, List.flatMap_def]
  have hhidmem : ∀ p ∈ T, ∀ h ∈ p.2, h ∈ hs.flatten := fun p hp h hh =>
    List.mem_flatten.mpr ⟨p.2, hmem2 p hp, hh⟩
  have hhid : ∀ p ∈ T, ∀ h ∈ p.2, ∀ x, κ x ≠ some h := fun p hp h hh =>
    (hfill h (hhidmem p hp h hh)).2.1
  obtain ⟨hND1, hND2⟩ := ent_nodup T hrow hL hrowinj (hflat ▸ hnd) hinj hhid
  have hBE : build F κ qs hs = writeAll (ent F κ T) κ := rfl
  generalize hE : ent F κ T = E at hND1 hND2 hBE
  have hEmem : ∀ e, e ∈ E ↔ ∃ p ∈ T,
      e ∈ chainCells (F.tch p.1.1 p.1.2) (tgtVals F κ p.1 p.2) := fun e => by
    rw [← hE]; exact List.mem_flatMap
  have hfun : ∀ x w w', (x, w) ∈ E → (x, w') ∈ E → w = w' := fun x w w' h1 h2 =>
    congrArg Prod.snd (List.inj_on_of_nodup_map hND1 h1 h2 rfl)
  have hval : ∀ x w y, (x, w) ∈ E → (y, w) ∈ E → x = y := fun x w y h1 h2 =>
    congrArg Prod.fst (List.inj_on_of_nodup_map hND2 h1 h2 rfl)
  have hent : ∀ e ∈ E, ∃ p ∈ T, ∃ v, κ (.inr (F.tch p.1.1 p.1.2).1) = some v ∧
      e ∈ chainCells (F.tch p.1.1 p.1.2) (p.2 ++ [v]) := by
    intro e he
    obtain ⟨p, hp, hpe⟩ := (hEmem e).mp he
    obtain ⟨v, hv⟩ := hrow p hp
    exact ⟨p, hp, v, hv, by rwa [tgtVals_eq hv] at hpe⟩
  have hentof : ∀ p ∈ T, ∀ v, κ (.inr (F.tch p.1.1 p.1.2).1) = some v →
      ∀ e ∈ chainCells (F.tch p.1.1 p.1.2) (p.2 ++ [v]), e ∈ E := by
    intro p hp v hv e he
    exact (hEmem e).mpr ⟨p, hp, by rw [tgtVals_eq hv]; exact he⟩
  have hlenv : ∀ p ∈ T, ∀ v : St,
      (p.2 ++ [v]).length = (F.tch p.1.1 p.1.2).2.length + 1 := by
    intro p hp v; simp [hL p hp]
  have hentval : ∀ x w, (x, w) ∈ E →
      w ∈ hs.flatten ∨ ∃ p ∈ T, κ (.inr (F.tch p.1.1 p.1.2).1) = some w := by
    intro x w he
    obtain ⟨p, hp, v, hv, hpe⟩ := hent _ he
    have h1 : w ∈ (chainCells (F.tch p.1.1 p.1.2) (p.2 ++ [v])).map Prod.snd :=
      List.mem_map_of_mem (f := Prod.snd) hpe
    rw [chainCells_snd _ _ (hlenv p hp v)] at h1
    rcases List.mem_append.mp h1 with h | h
    · exact .inl (hhidmem p hp w h)
    · obtain rfl := List.mem_singleton.mp h
      exact .inr ⟨p, hp, hv⟩
  have hrowkey : ∀ p ∈ T, ∃ w, (Sum.inr (F.tch p.1.1 p.1.2).1, w) ∈ E := by
    intro p hp
    obtain ⟨v, hv⟩ := hrow p hp
    cases hvals : p.2 ++ [v] with
    | nil => simp at hvals
    | cons c1 t =>
      exact ⟨c1, hentof p hp v hv _ (by rw [hvals]; simp [chainCells])⟩
  have hentG : ∀ x w, (x, w) ∈ E → (∃ p ∈ T, x = .inr (F.tch p.1.1 p.1.2).1) ∨
      (∃ c b, x = .inl (c, b) ∧ c ∈ hs.flatten) := by
    intro x w he
    obtain ⟨p, hp, v, hv, hpe⟩ := hent _ he
    have h1 : G x ∈ (chainCells (F.tch p.1.1 p.1.2) (p.2 ++ [v])).map (fun e => G e.1) :=
      List.mem_map_of_mem (f := fun e => G e.1) hpe
    rw [chainCells_G _ _ (hlenv p hp v), List.dropLast_concat] at h1
    rcases List.mem_cons.mp h1 with h | h
    · cases x with
      | inl q => simp [G] at h
      | inr B => exact .inl ⟨p, hp, by simpa [G] using h⟩
    · obtain ⟨c0, hc0, h⟩ := List.mem_map.mp h
      cases x with
      | inl q =>
        have hq : c0 = q.1 := by simpa [G] using h
        exact .inr ⟨q.1, q.2, rfl, hq ▸ hhidmem p hp c0 hc0⟩
      | inr B => simp [G] at h
  have hB : ∀ x w, build F κ qs hs x = some w →
      (x, w) ∈ E ∨ (κ x = some w ∧ ∀ w', (x, w') ∉ E) := fun x w h => by
    rw [hBE] at h; exact writeAll_cases _ _ _ _ h
  have hBmem : ∀ x w, (x, w) ∈ E → build F κ qs hs x = some w := fun x w h => by
    rw [hBE]; exact writeAll_mem _ _ hfun _ _ h
  have key : ∀ x y w, (x, w) ∈ E → κ y = some w → (∀ w', (y, w') ∉ E) → False := by
    intro x y w h1 h2 h2'
    rcases hentval x w h1 with h | ⟨p, hp, hv⟩
    · exact (hfill w h).2.1 y h2
    · have hy := hinj _ _ _ h2 hv
      obtain ⟨w', hw'⟩ := hrowkey p hp
      exact h2' w' (hy ▸ hw')
  refine ⟨⟨?_, ?_, ha, ?_⟩, ?_⟩
  · intro x y w hx hy
    rcases hB x w hx with h1 | ⟨h1, h1'⟩ <;> rcases hB y w hy with h2 | ⟨h2, h2'⟩
    · exact hval x w y h1 h2
    · exact (key x y w h1 h2 h2').elim
    · exact (key y x w h2 h1 h1').elim
    · exact hinj x y w h1 h2
  · intro x hx
    rcases hB x F.IV hx with h | ⟨h, -⟩
    · rcases hentval x _ h with h' | ⟨p, hp, hv⟩
      · exact (hfill _ h').1 rfl
      · exact hiv _ hv
    · exact hiv x h
  · intro t m hm
    obtain ⟨⟨⟨t', m'⟩, h⟩, hp, hp1⟩ := List.mem_map.mp (by rw [hT1]; exact hm :
      (t, m) ∈ T.map Prod.fst)
    cases hp1
    obtain ⟨v, hv⟩ := hrow _ hp
    have hlv := hlenv _ hp v
    have hof := hentof _ hp v hv
    dsimp only at hv hlv hof
    cases hvals : h ++ [v] with
    | nil => simp at hvals
    | cons c1 tl =>
      rw [hvals] at hlv hof
      have hrowB : build F κ qs hs (.inr (F.tch t m).1) = some c1 :=
        hBmem _ _ (hof _ (by simp [chainCells]))
      have hpub : ∀ e ∈ pubCells (c1 :: tl) (F.tch t m).2, e ∈ E := fun e he =>
        hof e (by simp [chainCells, he])
      have htl : tl.length = (F.tch t m).2.length := by simpa using hlv
      refine ⟨?_, ?_⟩
      · simp only [chainVal, hrowB, Option.bind_some]
        exact walk_complete _ _ _ _ htl fun e he => hBmem _ _ (hpub e he)
      · intro X hXl hXt hXs
        have h1 : X.1 = (F.tch t m).1 := by
          cases hr : build F κ qs hs (.inr X.1) with
          | none => simp [chainVal, hr] at hXs
          | some c0 =>
            rcases hB _ _ hr with he | ⟨hk, -⟩
            · rcases hentG _ _ he with ⟨p', hp', hx⟩ | ⟨c, b, hx, -⟩
              · have hx' : X.1 = (F.tch p'.1.1 p'.1.2).1 := Sum.inr.inj hx
                have ht' : p'.1.1 = t := by rw [← hXt, hx', hbtwT]
                have hm' : p'.1.2 = m := ha t _ _ (by rw [← ht']; exact hmem1 p' hp') hm
                rw [hx', ht', hm']
              · cases hx
            · rcases hc' X.1 c0 hk with ⟨m', hm', hx⟩ | htw
              · rw [hXt] at hm' hx
                rw [hx, ha t m' m hm' hm]
              · exact absurd hm (hd t (hXt ▸ htw) m)
        have h2 : X.2 = (F.tch t m).2 := by
          have hw : (walk (build F κ qs hs) c1 X.2).isSome := by
            simpa [chainVal, h1, hrowB] using hXs
          refine walk_unique _ _ c1 tl X.2 htl (by rw [hXl, hlen]) ?_ hw
          intro c₀ b c' he b' w' hκ'
          have he' := hpub _ he
          have hc₀ : c₀ ∈ hs.flatten := by
            rcases hentG _ _ he' with ⟨p', -, hx⟩ | ⟨c, b₁, hx, hc⟩
            · cases hx
            · obtain ⟨rfl, -⟩ := Prod.mk.inj (Sum.inl.inj hx)
              exact hc
          rcases hB _ _ hκ' with h3 | ⟨h3, -⟩
          · have h4 := List.inj_on_of_nodup_map hND1 h3 he' rfl
            simpa using h4
          · rw [(hfill c₀ hc₀).2.2 b'] at h3
            cases h3
        exact Prod.ext h1 h2
  · obtain ⟨l, hl, hlmem⟩ := hfin
    refine ⟨l ++ E.map Prod.fst, ?_, ?_⟩
    · rw [List.length_append, List.length_map]
      have h1 : E.length = T.length * (L + 1) := by
        rw [← hE]
        refine length_flatMap_const _ _ _ fun p hp => ?_
        obtain ⟨v, hv⟩ := hrow p hp
        rw [tgtVals_eq hv, ← List.length_map (f := Prod.snd),
          chainCells_snd _ _ (hlenv p hp v)]
        simp [hlenL _ (hmem2 p hp)]
      have hTl : T.length = qs.length := by simp [T, hlenhs]
      rw [h1, hTl]
      omega
    · intro x hx
      obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp hx
      rcases hB x w hw with h | ⟨h, -⟩
      · exact List.mem_append_right _ (List.mem_map_of_mem (f := Prod.fst) h)
      · exact List.mem_append_left _ (hlmem x (by rw [h]; rfl))

open MB in
/-- **Fresh hidden values.**  `n` lists of `L` uniform chaining values fail `FillNice` relative
to a cache of at most `N` cells with probability at most `(n L) (n L + 2 N + 1) / |St|`. -/
theorem prEvent_drawN_not_fillNice [Fintype St] [SampleableType St] (IV : St)
    (κ : Cell St Blk → Option St) (N L n : ℕ) (hfin : CFin κ N) :
    Pr{let hs ← drawN (St := St) L n}[¬ FillNice IV κ hs] ≤
      ((n * L) * (n * L + 2 * N + 1) : ℕ) * (Fintype.card St : ℝ≥0∞)⁻¹ := by
  obtain ⟨l, hl, hlm⟩ := hfin
  let S : List St := IV :: (l.filterMap κ ++ l.filterMap rowOf)
  have hS : S.length ≤ 2 * N + 1 := by
    have h1 := List.length_filterMap_le κ l
    have h2 := List.length_filterMap_le (rowOf (St := St) (Blk := Blk)) l
    simp only [S, List.length_cons, List.length_append]
    omega
  have hle : ((n * L * (n * L + S.length) : ℕ) : ℝ≥0∞) * (Fintype.card St : ℝ≥0∞)⁻¹ ≤
      ((n * L) * (n * L + 2 * N + 1) : ℕ) * (Fintype.card St : ℝ≥0∞)⁻¹ :=
    mul_le_mul' (Nat.cast_le.mpr (Nat.mul_le_mul_left _ (by omega))) le_rfl
  refine (prEvent_mono _ _ (fun hs => ¬ Fresh S hs.flatten) fun hs hh hf => hh ?_).trans
    ((prEvent_drawN_not_fresh L n S).trans hle)
  · refine ⟨hf.1, fun h hh => ⟨fun e => hf.2 h hh (e ▸ List.mem_cons_self), fun x hx => ?_,
      fun b => ?_⟩⟩
    · exact hf.2 h hh (List.mem_cons_of_mem _ (List.mem_append_left _
        (List.mem_filterMap.mpr ⟨x, hlm x (by rw [hx]; rfl), hx⟩)))
    · by_contra hne
      obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.mp hne
      exact hf.2 h hh (List.mem_cons_of_mem _ (List.mem_append_right _
        (List.mem_filterMap.mpr ⟨.inl (h, b), hlm _ (by rw [hw]; rfl), rfl⟩)))

end Ideal

#print axioms Ideal.build_good
#print axioms Ideal.prEvent_drawN_not_fillNice
