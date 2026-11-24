import Ideal.Games.ItsrDefs

/-!
# ITSR in the ideal-compression model: reduction to a tape of independent uniform digests

`itsr_le`: for a uniformly random compression table, the ITSR experiment for
`H_g(k, x) = od (MD_g (ob (k, x) (MD_g (ib (k, x)))))` (two-block outer hash) is won with
probability at most

`Pr[covB idx (tape)] + Q² / |St|`,

where `tape` is a list of `n` independent uniform digests, `covB idx` says that some entry of the
list has all its indices among the indices of the *other* entries, `n` bounds the *marked*
compression calls of the experiment `gameProg` (the adversary's calls and two calls per hash of
the final check) and `Q` bounds all its compression calls.

Proof.  The experiment is run on the marked compression oracle, recording all distinct cells
read (`a`) and the cells whose first read was a marked call (`s`, the log).

* Unless two cells of `a` have the same value or a cell of `a` has value `IV` (`badV`, at most
  `Q² / |St|` by `prT_tape_le` and `prT_tape_bad_le`), distinct hash inputs have distinct final
  cells (Merkle–Damgård walk-back `md_inj`, injectivity of the block maps), and the final cell of
  every hash of the final check is in the log (`key_true`: a cell `(g (IV, b₀), b₁)` that was
  first read by an unmarked call exhibits a bad table, by the invariant `Inv`).
* So a win exhibits a logged cell (the final cell of the candidate) whose digest indices are
  covered by the digests of other logged cells (final cells of targets): `win_imp`, `win_log`.
* The digests of the logged cells are dominated by a tape of `n` independent uniform digests
  (`prT_tape_le_marked`).

Why two marked calls per hash: the inner and the outer hash are not domain separated, so the
final cell `(g (IV, b₀), b₁)` of one input may be read as the position-1 cell of the *inner*
iteration of another input; marking every position-1 call makes such a cell logged at its first
read.
-/

open OracleComp OracleSpec ENNReal KeyedHash

namespace Ideal.Itsr

open Ideal.HP Ideal.Prf AnswerTape

variable {St Blk K X Y Index : Type}

/-! ## Coverage of a list of digests -/

/-- Some entry of the list has all its indices among the indices of the other entries. -/
def CovP (idx : Y → List Index) (l : List Y) : Prop :=
  ∃ pre y post, l = pre ++ y :: post ∧ ∀ i ∈ idx y, ∃ z ∈ pre ++ post, i ∈ idx z

open Classical in
/-- `CovP` as a Boolean. -/
noncomputable def covB (idx : Y → List Index) (l : List Y) : Bool := decide (CovP idx l)

theorem covP_mono (idx : Y → List Index) (l l' : List Y) (h : l.Sublist l') (hc : CovP idx l) :
    CovP idx l' := by
  obtain ⟨pre, y, post, rfl, hcov⟩ := hc
  obtain ⟨r₁, r₂, rfl, h₁, h₂⟩ := List.append_sublist_iff.mp h
  obtain ⟨u, v, rfl, hy, h₃⟩ := List.cons_sublist_iff.mp h₂
  obtain ⟨u₁, u₂, rfl⟩ := List.append_of_mem hy
  refine ⟨r₁ ++ u₁, y, u₂ ++ v, by simp, fun i hi => ?_⟩
  obtain ⟨z, hz, hiz⟩ := hcov i hi
  refine ⟨z, ?_, hiz⟩
  rcases List.mem_append.mp hz with hz | hz
  · have := h₁.subset hz
    simp [this]
  · have := h₃.subset hz
    simp [this]

theorem covB_mono (idx : Y → List Index) (l l' : List Y) (h : l.Sublist l')
    (hc : covB idx l = true) : covB idx l' = true := by
  simp only [covB, decide_eq_true_eq] at hc ⊢
  exact covP_mono idx l l' h hc

/-! ## Merkle–Damgård cells -/

/-- The cells read by the iteration from `c` through `bs`. -/
def mdCells (g : CF St Blk) : St → List Blk → List (St × Blk)
  | _, [] => []
  | c, b :: bs => (c, b) :: mdCells g (g (c, b)) bs

theorem mdCells_append (g : CF St Blk) (c : St) (bs : List Blk) (b : Blk) :
    mdCells g c (bs ++ [b]) = mdCells g c bs ++ [(mdFold g c bs, b)] := by
  induction bs generalizing c with
  | nil => rfl
  | cons a bs ih => simp only [List.cons_append, mdCells, ih]; rfl

theorem mdFold_append (g : CF St Blk) (c : St) (bs : List Blk) (b : Blk) :
    mdFold g c (bs ++ [b]) = g (mdFold g c bs, b) := by
  simp [mdFold]

/-- **Merkle–Damgård walk-back.**  If `g` is injective on a set `s` of cells containing the cells
of two iterations from `c₀`, and no cell of `s` has value `c₀`, then equal chain values come from
equal block lists. -/
theorem md_inj (g : CF St Blk) (c₀ : St) (s : List (St × Blk))
    (hinj : ∀ c ∈ s, ∀ c' ∈ s, g c = g c' → c = c') (hIV : ∀ c ∈ s, g c ≠ c₀) (bs : List Blk) :
    ∀ bs' : List Blk, (∀ c ∈ mdCells g c₀ bs, c ∈ s) → (∀ c ∈ mdCells g c₀ bs', c ∈ s) →
      mdFold g c₀ bs = mdFold g c₀ bs' → bs = bs' := by
  induction bs using List.reverseRecOn with
  | nil =>
    intro bs' _ h' h
    rcases List.eq_nil_or_concat bs' with rfl | ⟨L, b, hL⟩
    · rfl
    · rw [List.concat_eq_append] at hL; subst hL
      rw [mdFold_append] at h
      exact absurd h.symm (hIV _ (h' _ (by simp [mdCells_append])))
  | append_singleton as a ih =>
    intro bs' h1 h' h
    rcases List.eq_nil_or_concat bs' with rfl | ⟨L, b, hL⟩
    · rw [mdFold_append] at h
      exact absurd h (hIV _ (h1 _ (by simp [mdCells_append])))
    · rw [List.concat_eq_append] at hL; subst hL
      rw [mdFold_append, mdFold_append] at h
      have hc := hinj _ (h1 _ (by simp [mdCells_append])) _ (h' _ (by simp [mdCells_append])) h
      obtain ⟨hm, hab⟩ := Prod.mk.inj hc
      rw [hab, ih L (fun c hcm => h1 c (by simp [mdCells_append, hcm]))
        (fun c hcm => h' c (by simp [mdCells_append, hcm])) hm]

/-- The cells read by the computation of `H_g(k, x)`. -/
def cellsH (IV : St) (ib : K × X → List Blk) (ob : K × X → St → List Blk) (g : CF St Blk)
    (kx : K × X) : List (St × Blk) :=
  mdCells g IV (ib kx) ++ mdCells g IV (ob kx (mdFold g IV (ib kx)))

/-! ## A win exhibits a covered digest or a bad table -/

/-- If the cells `a` contain the cells of the candidate and of the targets, and — unless `g` is
bad on `a` — the log `s` contains their final cells, a win exhibits coverage among the digests
of the logged cells or a bad table. -/
theorem win_imp [DecidableEq St] (IV : St) (ib : K × X → List Blk)
    (ob : K × X → St → List Blk) (od : St → Y) (idx : Y → List Index)
    (hib : Function.Injective ib) (hob : ∀ kx kx' s s', ob kx s = ob kx' s' → s = s')
    (hobne : ∀ kx s, ob kx s ≠ []) (g : CF St Blk) (a s : List (St × Blk))
    (cand : K × X) (targets : List (K × X))
    (hc : ∀ c ∈ cellsH IV ib ob g cand, c ∈ a)
    (ht : ∀ kx ∈ targets, ∀ c ∈ cellsH IV ib ob g kx, c ∈ a)
    (hlog : ¬ badV IV (a.map g) = true → ∀ kx, kx = cand ∨ kx ∈ targets → ∀ as b,
      ob kx (mdFold g IV (ib kx)) = as ++ [b] → (mdFold g IV as, b) ∈ s)
    (hfresh : cand ∉ targets)
    (hwin : ∀ i ∈ idx (hashG IV ib ob od g cand),
      i ∈ (targets.map (hashG IV ib ob od g)).flatMap idx) :
    CovP idx (s.map fun c => od (g c)) ∨ badV IV (a.map g) = true := by
  by_cases hb : badV IV (a.map g) = true
  · exact Or.inr hb
  refine Or.inl ?_
  have hlog' := hlog hb
  simp only [badV, decide_eq_true_eq, not_or, not_not] at hb
  have hinj : ∀ c ∈ a, ∀ c' ∈ a, g c = g c' → c = c' := fun c hc c' hc' h =>
    List.inj_on_of_nodup_map hb.1 hc hc' h
  have hIV : ∀ c ∈ a, g c ≠ IV := fun c hc h => hb.2 (h ▸ List.mem_map_of_mem hc)
  -- final cells
  have hfin : ∀ kx : K × X, (kx = cand ∨ kx ∈ targets) → (∀ c ∈ cellsH IV ib ob g kx, c ∈ a) →
      ∃ as b, ob kx (mdFold g IV (ib kx)) = as ++ [b] ∧ (mdFold g IV as, b) ∈ s ∧
        (∀ c ∈ mdCells g IV as, c ∈ a) ∧ (∀ c ∈ mdCells g IV (ib kx), c ∈ a) ∧
        hashG IV ib ob od g kx = od (g (mdFold g IV as, b)) := by
    intro kx hmem hkx
    rcases List.eq_nil_or_concat (ob kx (mdFold g IV (ib kx))) with h | ⟨as, b, h⟩
    · exact absurd h (hobne _ _)
    · rw [List.concat_eq_append] at h
      refine ⟨as, b, h, hlog' kx hmem as b h, fun c hcm => hkx _ ?_, fun c hcm => hkx _ ?_, ?_⟩
      · simp [cellsH, h, mdCells_append, hcm]
      · simp [cellsH, hcm]
      · simp only [hashG, h, mdFold_append]
  have hdist : ∀ kx kx' : K × X, ∀ as b as' b',
      ob kx (mdFold g IV (ib kx)) = as ++ [b] → ob kx' (mdFold g IV (ib kx')) = as' ++ [b'] →
      (∀ c ∈ mdCells g IV as, c ∈ a) → (∀ c ∈ mdCells g IV as', c ∈ a) →
      (∀ c ∈ mdCells g IV (ib kx), c ∈ a) → (∀ c ∈ mdCells g IV (ib kx'), c ∈ a) →
      (mdFold g IV as, b) = (mdFold g IV as', b') → kx = kx' := by
    intro kx kx' as b as' b' h h' hs hs' hi hi' he
    obtain ⟨hm, hbb⟩ := Prod.mk.inj he
    have e1 : as = as' := md_inj g IV a hinj hIV as as' hs hs' hm
    have e2 : mdFold g IV (ib kx) = mdFold g IV (ib kx') :=
      hob _ _ _ _ (by rw [h, h', e1, hbb])
    exact hib (md_inj g IV a hinj hIV _ _ hi hi' e2)
  obtain ⟨as, b, hoa, hF, hs, hi, hH⟩ := hfin cand (Or.inl rfl) hc
  obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hF
  refine ⟨pre.map (fun c => od (g c)), od (g (mdFold g IV as, b)), post.map (fun c => od (g c)),
    by rw [hsplit]; simp, fun i hi' => ?_⟩
  rw [← hH] at hi'
  obtain ⟨d, hd, hid⟩ := List.mem_flatMap.mp (hwin i hi')
  obtain ⟨kx, hkx, rfl⟩ := List.mem_map.mp hd
  obtain ⟨as', b', hoa', hF', hs', hi2, hH'⟩ := hfin kx (Or.inr hkx) (ht kx hkx)
  have hne : (mdFold g IV as', b') ≠ (mdFold g IV as, b) := fun e =>
    hfresh (by rw [← hdist kx cand as' b' as b hoa' hoa hs' hs hi2 hi e]; exact hkx)
  refine ⟨od (g (mdFold g IV as', b')), ?_, by rw [← hH']; exact hid⟩
  rw [hsplit] at hF'
  rcases List.mem_append.mp hF' with hm | hm
  · exact List.mem_append_left _ (List.mem_map_of_mem hm)
  · rcases List.mem_cons.mp hm with hm | hm
    · exact absurd hm hne
    · exact List.mem_append_right _ (List.mem_map_of_mem hm)

/-! ## The marked run -/

section Log

set_option linter.unusedSectionVars false

variable [DecidableEq St] [DecidableEq Blk]

/-- Run against the table `g`, recording the distinct cells read and, among them, those whose
first read was a marked query. -/
abbrev mImpl (g : CF St Blk) :
    QueryImpl (unifSpec + mS St Blk) (StateT (List (St × Blk) × List (St × Blk)) ProbComp) :=
  stImpl (spec := mS St Blk) (fun t => g t.1) (logM Prod.fst Prod.snd)

/-- One recording step. -/
abbrev stepM (t : (St × Blk) × Bool) (st : List (St × Blk) × List (St × Blk)) :
    List (St × Blk) × List (St × Blk) := logM Prod.fst Prod.snd t st

/-- The recorded state only grows. -/
def Mono (st st' : List (St × Blk) × List (St × Blk)) : Prop :=
  st.1.Sublist st'.1 ∧ ∀ c ∈ st.2, c ∈ st'.2

theorem Mono.refl (st : List (St × Blk) × List (St × Blk)) : Mono st st :=
  ⟨List.Sublist.refl _, fun _ h => h⟩

theorem Mono.trans {st st' st'' : List (St × Blk) × List (St × Blk)} (h : Mono st st')
    (h' : Mono st' st'') : Mono st st'' :=
  ⟨h.1.trans h'.1, fun c hc => h'.2 c (h.2 c hc)⟩

theorem mono_stepM (t : (St × Blk) × Bool) (st : List (St × Blk) × List (St × Blk)) :
    Mono st (stepM t st) := by
  constructor
  · show st.1.Sublist (logU Prod.fst t st.1)
    unfold logU
    split
    · exact List.Sublist.refl _
    · exact List.sublist_append_left _ _
  · intro c hc
    show c ∈ (if t.2 = true ∧ t.1 ∉ st.1 then st.2 ++ [t.1] else st.2)
    split
    · exact List.mem_append_left _ hc
    · exact hc

theorem mem_stepM (t : (St × Blk) × Bool) (st : List (St × Blk) × List (St × Blk)) :
    t.1 ∈ (stepM t st).1 := mem_logU Prod.fst t st.1

/-- `c` is the value of a cell of `a` whose chaining value is itself the value of a cell of
`a`. -/
def Val2 (g : CF St Blk) (a : List (St × Blk)) (c : St) : Prop :=
  ∃ c' ∈ a, g c' = c ∧ ∃ c'' ∈ a, g c'' = c'.1

theorem Val2.mono {g : CF St Blk} {a a' : List (St × Blk)} {c : St} (h : Val2 g a c)
    (hs : a.Sublist a') : Val2 g a' c := by
  obtain ⟨c', hc', e, c'', hc'', e'⟩ := h
  exact ⟨c', hs.subset hc', e, c'', hs.subset hc'', e'⟩

/-- Invariant: the log is among the cells read, and every cell read but not logged has chaining
value `IV` or a chaining value at depth at least two. -/
def Inv (IV : St) (g : CF St Blk) (st : List (St × Blk) × List (St × Blk)) : Prop :=
  (∀ c ∈ st.2, c ∈ st.1) ∧ ∀ c ∈ st.1, c ∉ st.2 → c.1 = IV ∨ Val2 g st.1 c.1

theorem inv_nil (IV : St) (g : CF St Blk) : Inv IV g ([], []) := by
  constructor <;> simp

theorem inv_stepM_true (IV : St) (g : CF St Blk) (c : St × Blk)
    (st : List (St × Blk) × List (St × Blk)) (h : Inv IV g st) :
    Inv IV g (stepM (c, true) st) := by
  have hm := mono_stepM (c, true) st
  by_cases hc : c ∈ st.1
  · have e : stepM (c, true) st = st := by
      simp [stepM, logM, logU_of_mem (cell := Prod.fst) (t := (c, true)) hc, hc]
    rw [e]; exact h
  · have e : stepM (c, true) st = (st.1 ++ [c], st.2 ++ [c]) := by
      simp [stepM, logM, logU_of_not_mem (cell := Prod.fst) (t := (c, true)) hc, hc]
    rw [e]
    constructor
    · intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact List.mem_append_left _ (h.1 x hx)
      · exact List.mem_append_right _ hx
    · intro x hx hxs
      rcases List.mem_append.mp hx with hx | hx
      · rcases h.2 x hx (fun h' => hxs (List.mem_append_left _ h')) with h1 | h1
        · exact Or.inl h1
        · exact Or.inr (h1.mono (List.sublist_append_left _ _))
      · exact absurd (List.mem_append_right _ hx) hxs

theorem inv_stepM_false (IV : St) (g : CF St Blk) (c : St × Blk)
    (st : List (St × Blk) × List (St × Blk)) (h : Inv IV g st)
    (hf : c.1 = IV ∨ Val2 g st.1 c.1) : Inv IV g (stepM (c, false) st) := by
  by_cases hc : c ∈ st.1
  · have e : stepM (c, false) st = st := by
      simp [stepM, logM, logU_of_mem (cell := Prod.fst) (t := (c, false)) hc]
    rw [e]; exact h
  · have e : stepM (c, false) st = (st.1 ++ [c], st.2) := by
      simp [stepM, logM, logU_of_not_mem (cell := Prod.fst) (t := (c, false)) hc]
    rw [e]
    constructor
    · exact fun x hx => List.mem_append_left _ (h.1 x hx)
    · intro x hx hxs
      rcases List.mem_append.mp hx with hx | hx
      · rcases h.2 x hx hxs with h1 | h1
        · exact Or.inl h1
        · exact Or.inr (h1.mono (List.sublist_append_left _ _))
      · rw [List.mem_singleton.mp hx]
        rcases hf with h1 | h1
        · exact Or.inl h1
        · exact Or.inr (h1.mono (List.sublist_append_left _ _))

/-- A marked read of a cell `(g c₀, b)` with `c₀ = (IV, ·)` already read: the cell is in the log
afterwards, or the table is bad on the cells read. -/
theorem key_true (IV : St) (g : CF St Blk) (c₀ : St × Blk) (b : Blk)
    (st : List (St × Blk) × List (St × Blk)) (h : Inv IV g st) (hc₀ : c₀ ∈ st.1)
    (hIV : c₀.1 = IV) :
    (g c₀, b) ∈ (stepM ((g c₀, b), true) st).2 ∨ badV IV (st.1.map g) = true := by
  by_cases hs : (g c₀, b) ∈ st.2
  · exact Or.inl ((mono_stepM _ st).2 _ hs)
  by_cases hc : (g c₀, b) ∈ st.1
  · refine Or.inr ?_
    simp only [badV, decide_eq_true_eq]
    by_contra hb
    simp only [not_or, not_not] at hb
    rcases h.2 _ hc hs with h1 | ⟨c', hc', e, c'', hc'', e'⟩
    · exact hb.2 (List.mem_map.mpr ⟨c₀, hc₀, h1⟩)
    · have : c' = c₀ := List.inj_on_of_nodup_map hb.1 hc' hc₀ e
      rw [this, hIV] at e'
      exact hb.2 (List.mem_map.mpr ⟨c'', hc'', e'⟩)
  · refine Or.inl ?_
    have e : stepM ((g c₀, b), true) st = (st.1 ++ [(g c₀, b)], st.2 ++ [(g c₀, b)]) := by
      simp [stepM, logM, logU_of_not_mem (cell := Prod.fst) (t := ((g c₀, b), true)) hc, hc]
    rw [e]
    simp

theorem run_cq_bind {α : Type} (g : CF St Blk) (c : St) (b : Blk) (m : Bool)
    (k : St → OracleComp (unifSpec + mS St Blk) α) (st : List (St × Blk) × List (St × Blk)) :
    (simulateQ (mImpl g) (cq c b m >>= k)).run st =
      (simulateQ (mImpl g) (k (g (c, b)))).run (stepM ((c, b), m) st) :=
  run_stImpl_inr_bind (spec := mS St Blk) (fun t => g t.1) _ ((c, b), m) k st

theorem run_cq (g : CF St Blk) (c : St) (b : Blk) (m : Bool)
    (st : List (St × Blk) × List (St × Blk)) :
    (simulateQ (mImpl g) (cq c b m)).run st = pure (g (c, b), stepM ((c, b), m) st) := by
  have h := run_cq_bind g c b m pure st
  simpa using h

theorem run_mdMF (IV : St) (g : CF St Blk) (bs : List Blk) :
    ∀ (c : St) (st : List (St × Blk) × List (St × Blk)), Inv IV g st → Val2 g st.1 c →
      ∃ st', (simulateQ (mImpl g) (mdMF c bs)).run st = pure (mdFold g c bs, st') ∧
        Inv IV g st' ∧ Mono st st' ∧ ∀ x ∈ mdCells g c bs, x ∈ st'.1 := by
  induction bs with
  | nil =>
    intro c st hI _
    exact ⟨st, by simp [mdMF, mdFold], hI, Mono.refl _, by simp [mdCells]⟩
  | cons b bs ih =>
    intro c st hI hv
    have hI1 := inv_stepM_false IV g (c, b) st hI (Or.inr hv)
    have hm1 := mono_stepM ((c, b), false) st
    have hv1 : Val2 g (stepM ((c, b), false) st).1 (g (c, b)) := by
      obtain ⟨c', hc', e, -⟩ := hv
      exact ⟨(c, b), mem_stepM ((c, b), false) st, rfl, c', hm1.1.subset hc', e⟩
    obtain ⟨st', hrun, hI', hm', hcells⟩ := ih (g (c, b)) _ hI1 hv1
    refine ⟨st', ?_, hI', hm1.trans hm', fun x hx => ?_⟩
    · rw [mdMF, run_cq_bind, hrun]; rfl
    · simp only [mdCells, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hm'.1.subset (mem_stepM ((c, b), false) st)
      · exact hcells x hx

theorem run_mdM (IV : St) (g : CF St Blk) (bs : List Blk)
    (st : List (St × Blk) × List (St × Blk)) (hI : Inv IV g st) :
    ∃ st', (simulateQ (mImpl g) (mdM IV bs)).run st = pure (mdFold g IV bs, st') ∧
      Inv IV g st' ∧ Mono st st' ∧ (∀ x ∈ mdCells g IV bs, x ∈ st'.1) ∧
      ∀ b₀ b₁ rest, bs = b₀ :: b₁ :: rest →
        (g (IV, b₀), b₁) ∈ st'.2 ∨ badV IV (st'.1.map g) = true := by
  match bs with
  | [] =>
    exact ⟨st, by simp [mdM, mdFold], hI, Mono.refl _, by simp [mdCells], by simp⟩
  | [b₀] =>
    refine ⟨stepM ((IV, b₀), false) st, ?_, inv_stepM_false IV g (IV, b₀) st hI (Or.inl rfl),
      mono_stepM _ st, fun x hx => ?_, by simp⟩
    · rw [mdM, run_cq]; rfl
    · simp only [mdCells, List.mem_cons, List.not_mem_nil, or_false] at hx
      rw [hx]
      exact mem_stepM ((IV, b₀), false) st
  | b₀ :: b₁ :: rest =>
    have hI1 := inv_stepM_false IV g (IV, b₀) st hI (Or.inl rfl)
    have hm1 := mono_stepM ((IV, b₀), false) st
    have h0 := mem_stepM ((IV, b₀), false) st
    set st₁ := stepM ((IV, b₀), false) st with hst₁
    have hI2 := inv_stepM_true IV g (g (IV, b₀), b₁) st₁ hI1
    have hm2 := mono_stepM ((g (IV, b₀), b₁), true) st₁
    have h1 := mem_stepM ((g (IV, b₀), b₁), true) st₁
    have hk := key_true IV g (IV, b₀) b₁ st₁ hI1 h0 rfl
    set st₂ := stepM ((g (IV, b₀), b₁), true) st₁ with hst₂
    have hv : Val2 g st₂.1 (g (g (IV, b₀), b₁)) :=
      ⟨(g (IV, b₀), b₁), h1, rfl, (IV, b₀), hm2.1.subset h0, rfl⟩
    obtain ⟨st', hrun, hI', hm', hcells⟩ := run_mdMF IV g rest _ st₂ hI2 hv
    refine ⟨st', ?_, hI', (hm1.trans hm2).trans hm', fun x hx => ?_, fun b₀' b₁' rest' e => ?_⟩
    · rw [mdM, run_cq_bind, run_cq_bind, hrun]; rfl
    · simp only [mdCells, List.mem_cons] at hx
      rcases hx with rfl | rfl | hx
      · exact (hm2.trans hm').1.subset h0
      · exact hm'.1.subset h1
      · exact hcells x hx
    · obtain ⟨rfl, e2⟩ := List.cons.inj e
      obtain ⟨rfl, -⟩ := List.cons.inj e2
      rcases hk with hk | hk
      · exact Or.inl (hm'.2 _ hk)
      · exact Or.inr (badV_mono IV _ _ ((hm2.trans hm').1.map g) hk)

/-- The property of the final cell of an input in a recorded state: it is in the log or the
table is bad on the cells read. -/
def FinOK (IV : St) (ib : K × X → List Blk) (ob : K × X → St → List Blk) (g : CF St Blk)
    (kx : K × X) (st : List (St × Blk) × List (St × Blk)) : Prop :=
  ∀ as b, ob kx (mdFold g IV (ib kx)) = as ++ [b] →
    (mdFold g IV as, b) ∈ st.2 ∨ badV IV (st.1.map g) = true

theorem FinOK.mono {IV : St} {ib : K × X → List Blk} {ob : K × X → St → List Blk}
    {g : CF St Blk} {kx : K × X} {st st' : List (St × Blk) × List (St × Blk)}
    (h : FinOK IV ib ob g kx st) (hm : Mono st st') : FinOK IV ib ob g kx st' := by
  intro as b e
  rcases h as b e with h | h
  · exact Or.inl (hm.2 _ h)
  · exact Or.inr (badV_mono IV _ _ (hm.1.map g) h)

theorem run_hashM (IV : St) (ib : K × X → List Blk) (ob : K × X → St → List Blk) (od : St → Y)
    (hob2 : ∀ kx s, (ob kx s).length = 2)
    (g : CF St Blk) (kx : K × X) (st : List (St × Blk) × List (St × Blk)) (hI : Inv IV g st) :
    ∃ st', (simulateQ (mImpl g) (hashM IV ib ob od kx)).run st =
        pure (hashG IV ib ob od g kx, st') ∧
      Inv IV g st' ∧ Mono st st' ∧ (∀ c ∈ cellsH IV ib ob g kx, c ∈ st'.1) ∧
      FinOK IV ib ob g kx st' := by
  obtain ⟨st₁, hr1, hI1, hm1, hc1, -⟩ := run_mdM IV g (ib kx) st hI
  obtain ⟨st₂, hr2, hI2, hm2, hc2, hk⟩ :=
    run_mdM IV g (ob kx (mdFold g IV (ib kx))) st₁ hI1
  refine ⟨st₂, ?_, hI2, hm1.trans hm2, fun c hc => ?_, fun as b e => ?_⟩
  · simp only [hashM, simulateQ_bind, StateT.run_bind, hr1, pure_bind, hr2, simulateQ_pure,
      StateT.run_pure, hashG]
  · rcases List.mem_append.mp hc with h | h
    · exact hm2.1.subset (hc1 c h)
    · exact hc2 c h
  · have hl := hob2 kx (mdFold g IV (ib kx))
    rw [e] at hl
    obtain ⟨b₀, rfl⟩ := List.length_eq_one_iff.mp (show as.length = 1 by simpa using hl)
    exact hk b₀ b [] e

theorem run_hashAllM (IV : St) (ib : K × X → List Blk) (ob : K × X → St → List Blk)
    (od : St → Y) (hob2 : ∀ kx s, (ob kx s).length = 2) (g : CF St Blk) (l : List (K × X)) :
    ∀ st : List (St × Blk) × List (St × Blk), Inv IV g st →
      ∃ st', (simulateQ (mImpl g) (hashAllM IV ib ob od l)).run st =
          pure (l.map (hashG IV ib ob od g), st') ∧
        Inv IV g st' ∧ Mono st st' ∧
        ∀ kx ∈ l, (∀ c ∈ cellsH IV ib ob g kx, c ∈ st'.1) ∧ FinOK IV ib ob g kx st' := by
  induction l with
  | nil =>
    intro st hI
    exact ⟨st, by simp [hashAllM], hI, Mono.refl _, by simp⟩
  | cons kx l ih =>
    intro st hI
    obtain ⟨st₁, hr1, hI1, hm1, hc1, hf1⟩ := run_hashM IV ib ob od hob2 g kx st hI
    obtain ⟨st₂, hr2, hI2, hm2, hall⟩ := ih st₁ hI1
    refine ⟨st₂, ?_, hI2, hm1.trans hm2, fun kx' hkx' => ?_⟩
    · simp only [hashAllM, simulateQ_bind, StateT.run_bind, hr1, pure_bind, hr2, simulateQ_pure,
        StateT.run_pure, List.map_cons]
    · rcases List.mem_cons.mp hkx' with rfl | h
      · exact ⟨fun c hc => hm2.1.subset (hc1 c hc), hf1.mono hm2⟩
      · exact hall kx' h

theorem run_stImpl_liftM {ι : Type} {spec : OracleSpec ι} {τ α β : Type}
    (a : (t : ι) → spec.Range t) (u : ι → τ → τ) (pc : ProbComp α)
    (k : α → OracleComp (unifSpec + spec) β) (s : τ) :
    (simulateQ (stImpl a u) ((liftM pc : OracleComp (unifSpec + spec) α) >>= k)).run s =
      pc >>= fun x => (simulateQ (stImpl a u) (k x)).run s := by
  induction pc using OracleComp.inductionOn with
  | pure x => simp
  | query_bind n f ih =>
    simp only [liftM_bind, bind_assoc]
    refine (run_stImpl_inl_bind a u n (fun x => liftM (f x) >>= k) s).trans ?_
    exact bind_congr fun x => ih x

/-- The adversary phase preserves every state predicate preserved by marked reads. -/
theorem adv_inv [SampleableType K] (g : CF St Blk)
    (P : List (St × Blk) × List (St × Blk) → Prop)
    (hP : ∀ c st, P st → P (stepM (c, true) st)) (A : ItsrAdvI St Blk K X) :
    ∀ (s₀ : List (K × X)) (st : List (St × Blk) × List (St × Blk)), P st →
      ∀ z ∈ support ((simulateQ (mImpl g) ((simulateQ tgtImpl A).run s₀)).run st), P z.2 := by
  induction A using OracleComp.inductionOn with
  | pure x =>
    intro s₀ st hst z hz
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact hst
  | query_bind t k ih =>
    intro s₀ st hst z hz
    rcases t with n | q | x
    · have e : (simulateQ tgtImpl
          (liftM ((unifSpec + (hS St Blk + ITSRTargetSpec X K)).query (.inl n)) >>= k)).run s₀ =
          (liftM ((unifSpec + mS St Blk).query (.inl n)) : OracleComp (unifSpec + mS St Blk) _) >>=
            fun u => (simulateQ tgtImpl (k u)).run s₀ := by
        simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, tgtImpl, StateT.run_mk,
          bind_map_left]
        rfl
      rw [e, run_stImpl_inl_bind, mem_support_bind_iff] at hz
      obtain ⟨u, -, hz⟩ := hz
      exact ih u s₀ st hst z hz
    · have e : (simulateQ tgtImpl
          (liftM ((unifSpec + (hS St Blk + ITSRTargetSpec X K)).query (.inr (.inl q))) >>= k)).run
            s₀ =
          (liftM ((unifSpec + mS St Blk).query (.inr (q, true))) :
            OracleComp (unifSpec + mS St Blk) _) >>=
            fun u => (simulateQ tgtImpl (k u)).run s₀ := by
        simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, tgtImpl, StateT.run_mk,
          bind_map_left]
        rfl
      rw [e, run_stImpl_inr_bind] at hz
      exact ih _ s₀ _ (hP q st hst) z hz
    · have e : (simulateQ tgtImpl
          (liftM ((unifSpec + (hS St Blk + ITSRTargetSpec X K)).query (.inr (.inr x))) >>= k)).run
            s₀ =
          (liftM ($ᵗ K : ProbComp K) : OracleComp (unifSpec + mS St Blk) K) >>=
            fun k' => (simulateQ tgtImpl (k k')).run (s₀ ++ [(k', x)]) := by
        simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, tgtImpl, StateT.run_mk,
          bind_map_left]
      rw [e, run_stImpl_liftM, mem_support_bind_iff] at hz
      obtain ⟨k', -, hz⟩ := hz
      exact ih k' _ st hst z hz

/-- **A winning run logs a covered digest or reads a bad table.** -/
theorem win_log [SampleableType K] [DecidableEq K] [DecidableEq X] [DecidableEq Index]
    (IV : St) (ib : K × X → List Blk) (ob : K × X → St → List Blk) (od : St → Y)
    (idx : Y → List Index)
    (hib : Function.Injective ib) (hob : ∀ kx kx' s s', ob kx s = ob kx' s' → s = s')
    (hob2 : ∀ kx s, (ob kx s).length = 2) (g : CF St Blk) (A : ItsrAdvI St Blk K X) :
    ∀ z ∈ support ((simulateQ (mImpl g) (gameProg IV ib ob od idx A)).run ([], [])),
      z.1 = true →
        covB idx (z.2.2.map fun c => od (g c)) = true ∨ badV IV (z.2.1.map g) = true := by
  intro z hz hwin
  simp only [gameProg, simulateQ_bind, StateT.run_bind] at hz
  rw [mem_support_bind_iff] at hz
  obtain ⟨w, hw, hz⟩ := hz
  have hI := adv_inv g (Inv IV g) (inv_stepM_true IV g) A [] ([], []) (inv_nil IV g) w hw
  obtain ⟨st₁, hr1, hI1, -, hall⟩ := run_hashAllM IV ib ob od hob2 g w.1.2 w.2 hI
  obtain ⟨st₂, hr2, -, hm2, hc2, hf2⟩ := run_hashM IV ib ob od hob2 g w.1.1 st₁ hI1
  simp only [finM, simulateQ_bind, StateT.run_bind, hr1, pure_bind, hr2, simulateQ_pure,
    StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
  subst hz
  simp only [decide_eq_true_eq] at hwin
  have hobne : ∀ kx s, ob kx s ≠ [] := fun kx s h => by
    have := hob2 kx s
    rw [h] at this
    simp at this
  have h := win_imp IV ib ob od idx hib hob hobne g st₂.1 st₂.2 w.1.1 w.1.2 hc2
    (fun kx hkx c hc => hm2.1.subset ((hall kx hkx).1 c hc))
    (fun hb kx hkx as b e => by
      have hf : FinOK IV ib ob g kx st₂ := by
        rcases hkx with rfl | hkx
        · exact hf2
        · exact (hall kx hkx).2.mono hm2
      exact (hf as b e).resolve_right hb)
    hwin.1 hwin.2
  rcases h with h | h
  · exact Or.inl (by simpa [covB] using h)
  · exact Or.inr h

end Log

/-! ## The bound -/

theorem prT_pure_or_le (a b : Bool) :
    prT (pure (a || b)) ≤ prT (pure a) + prT (pure b) := by
  cases a <;> cases b <;> simp [prT_pure]

/-- **ITSR in the ideal-compression model, reduced to a tape of independent uniform digests.**
`n` bounds the marked compression calls of the experiment `gameProg` (the adversary's calls and
two calls per hash of the final check) and `Q` all its compression calls.  The experiment is won
with probability at most the probability that a tape of `n` independent uniform digests has an
entry whose indices are all covered by the other entries, plus `Q² / |St|`.

Repeated randomizers need no separate term.  The proof never uses freshness or distinctness of
the target keys: every compression cell first read by a marked call (all of the adversary's own
calls, two per hash of the final check) is one coordinate of the log, whatever key it belongs to
and whether it was read before or after that key was issued; the adversary's adaptivity only
decides WHICH inputs are evaluated; and the tape event lets ANY other coordinate act as a
coverer, not only the actual targets.  A digest the adversary computes for an already revealed
(possibly repeated) key is therefore a coordinate like any other.  The price: the bound is the
non-adaptive coverage bound for `n = q + 2 (qs + 1)` digests, in which the adversary's own `q`
digests count as potential coverers (loose when `q ≫ qs`; an adaptive bound with only the `qs`
target digests as coverers needs the re-randomising hybrid of `quantum/PQ/QROM/ExactItsr4.lean`). -/
theorem itsr_le [DecidableEq St] [DecidableEq Blk] [Fintype St] [Finite Blk]
    [SampleableType St] [SampleableType Y] [SampleableType (CF St Blk)]
    [SampleableType K] [DecidableEq K] [DecidableEq X] [DecidableEq Index]
    (IV : St) (ib : K × X → List Blk) (ob : K × X → St → List Blk) (od : St → Y)
    (idx : Y → List Index)
    (hib : Function.Injective ib) (hob : ∀ kx kx' s s', ob kx s = ob kx' s' → s = s')
    (hob2 : ∀ kx s, (ob kx s).length = 2)
    (hod : ∀ p : Y → Prop, Pr{let u ← $ᵗ St}[p (od u)] = Pr{let y ← $ᵗ Y}[p y])
    (A : ItsrAdvI St Blk K X) (n Q : ℕ)
    (hn : IsQueryBoundP (gameProg IV ib ob od idx A) (fun i => lgB Prod.snd i = true) n)
    (hQ : IsQueryBoundP (gameProg IV ib ob od idx A) (fun i => i.isRight = true) Q) :
    prT ($ᵗ (CF St Blk) >>= fun g => ITSRExperiment (A.inst (probI IV ib ob od idx g) g)) ≤
      prT (tapeList Y n >>= fun r => pure (covB idx r)) +
        ((Q ^ 2 : ℕ) : ℝ≥0∞) * (Fintype.card St : ℝ≥0∞)⁻¹ := by
  have h1 : prT ($ᵗ (CF St Blk) >>= fun g =>
        ITSRExperiment (A.inst (probI IV ib ob od idx g) g)) ≤
      prT ($ᵗ (CF St Blk) >>= fun g =>
        (simulateQ (mImpl g) (gameProg IV ib ob od idx A)).run ([], []) >>= fun z =>
          pure (covB idx (z.2.2.map fun c => od (g c)) || badV IV (z.2.1.map g))) := by
    refine prT_bind_mono _ _ _ fun g _ => ?_
    rw [← simulateQ_gameProg, markImpl_eq,
      ← fst_map_run_stImpl (spec := mS St Blk) (fun t => g t.1) (logM Prod.fst Prod.snd) _
        (([], []) : List (St × Blk) × List (St × Blk)),
      map_eq_bind_pure_comp]
    refine prT_bind_mono _ _ _ fun z hz => ?_
    simp only [Function.comp, prT_pure]
    have := win_log IV ib ob od idx hib hob hob2 g A z hz
    cases hz1 : z.1
    · simp
    · rcases this hz1 with h | h <;> simp [h]
  refine h1.trans ?_
  refine (prT_bind_le_add _ _ _ _ fun g => prT_bind_le_add _ _ _ _ fun z =>
    prT_pure_or_le _ _).trans (add_le_add ?_ ?_)
  · exact prT_tape_le_marked (spec := mS St Blk) Prod.fst Prod.snd (fun g t => g t.1)
      (fun g g' t h => h) od hod (covB idx) (covB_mono idx) _ n hn
  · have e : ∀ g : CF St Blk,
        ((simulateQ (mImpl g) (gameProg IV ib ob od idx A)).run ([], []) >>= fun z =>
          pure (badV IV (z.2.1.map g))) =
        ((simulateQ (stImpl (spec := mS St Blk) (fun t => g t.1) (logU Prod.fst))
          (gameProg IV ib ob od idx A)).run [] >>= fun z => pure (badV IV (z.2.map g))) := by
      intro g
      rw [← fst_run_logM (spec := mS St Blk) (fun t => g t.1) Prod.fst Prod.snd _
        (([], []) : List (St × Blk) × List (St × Blk)), bind_map_left]
    simp only [e]
    refine (prT_tape_le (spec := mS St Blk) Prod.fst (fun g t => g t.1) (fun g g' t h => h) id
      (fun p => rfl) (badV IV) (badV_mono IV) _ Q hQ).trans ?_
    exact prT_tape_bad_le IV Q

/-! ## Query bounds of the experiment -/

section Bounds

variable {p : ℕ ⊕ ((St × Blk) × Bool) → Prop} [DecidablePred p]

theorem isQueryBoundP_cq_bind_succ {α : Type} (c : St) (b : Blk) (m : Bool)
    (k : St → OracleComp (unifSpec + mS St Blk) α) (n : ℕ)
    (h : ∀ u, IsQueryBoundP (k u) p n) : IsQueryBoundP (cq c b m >>= k) p (n + 1) := by
  unfold cq
  rw [isQueryBoundP_query_bind_iff]
  refine ⟨Or.inr (Nat.succ_pos n), fun u => ?_⟩
  split
  · simpa using h u
  · exact (h u).mono (Nat.le_succ n)

theorem isQueryBoundP_cq_bind_of_not {α : Type} (c : St) (b : Blk) (m : Bool)
    (k : St → OracleComp (unifSpec + mS St Blk) α) (n : ℕ)
    (hnp : ¬ p (.inr ((c, b), m))) (h : ∀ u, IsQueryBoundP (k u) p n) :
    IsQueryBoundP (cq c b m >>= k) p n := by
  unfold cq
  rw [isQueryBoundP_query_bind_iff]
  refine ⟨Or.inl hnp, fun u => ?_⟩
  simpa [hnp] using h u

theorem mdMF_bound (c : St) (bs : List Blk) : IsQueryBoundP (mdMF c bs) p bs.length := by
  induction bs generalizing c with
  | nil => simp [mdMF]
  | cons b bs ih => exact isQueryBoundP_cq_bind_succ c b false _ _ fun u => ih u

theorem mdMF_bound0 (h0 : ∀ t, ¬ p (.inr (t, false))) (c : St) (bs : List Blk) :
    IsQueryBoundP (mdMF c bs) p 0 := by
  induction bs generalizing c with
  | nil => simp [mdMF]
  | cons b bs ih => exact isQueryBoundP_cq_bind_of_not c b false _ _ (h0 _) fun u => ih u

theorem mdM_bound (c : St) (bs : List Blk) : IsQueryBoundP (mdM c bs) p bs.length := by
  match bs with
  | [] => simp [mdM]
  | [b₀] =>
    have := isQueryBoundP_cq_bind_succ (p := p) c b₀ false pure 0 (fun u => by simp)
    simpa [mdM] using this
  | b₀ :: b₁ :: bs =>
    exact isQueryBoundP_cq_bind_succ c b₀ false _ _ fun u =>
      isQueryBoundP_cq_bind_succ u b₁ true _ _ fun u' => mdMF_bound u' bs

theorem mdM_bound1 (h0 : ∀ t, ¬ p (.inr (t, false))) (c : St) (bs : List Blk) :
    IsQueryBoundP (mdM c bs) p 1 := by
  match bs with
  | [] => simp [mdM]
  | [b₀] =>
    have := isQueryBoundP_cq_bind_succ (p := p) c b₀ false pure 0 (fun u => by simp)
    simpa [mdM] using this
  | b₀ :: b₁ :: bs =>
    exact isQueryBoundP_cq_bind_of_not c b₀ false _ _ (h0 _) fun u =>
      isQueryBoundP_cq_bind_succ u b₁ true _ _ fun u' => mdMF_bound0 h0 u' bs

theorem hashM_bound (IV : St) (ib : K × X → List Blk) (ob : K × X → St → List Blk)
    (od : St → Y) (kx : K × X) (L : ℕ) (hL : ∀ s, (ib kx).length + (ob kx s).length ≤ L) :
    IsQueryBoundP (hashM IV ib ob od kx) p L := by
  unfold hashM
  refine (isQueryBoundP_bind (m := L - (ib kx).length) (mdM_bound IV (ib kx)) fun s _ =>
    ((isQueryBoundP_bind (m := 0) (mdM_bound IV (ob kx s)) fun o _ => by simp).mono ?_)).mono ?_
  · have := hL s
    omega
  · have := hL IV
    omega

theorem hashM_bound2 (h0 : ∀ t, ¬ p (.inr (t, false))) (IV : St) (ib : K × X → List Blk)
    (ob : K × X → St → List Blk) (od : St → Y) (kx : K × X) :
    IsQueryBoundP (hashM IV ib ob od kx) p 2 := by
  unfold hashM
  exact isQueryBoundP_bind (m := 1) (mdM_bound1 h0 IV (ib kx)) fun s _ =>
    isQueryBoundP_bind (m := 0) (mdM_bound1 h0 IV (ob kx s)) fun o _ => by simp

theorem hashAllM_bound (IV : St) (ib : K × X → List Blk) (ob : K × X → St → List Blk)
    (od : St → Y) (c : ℕ) (l : List (K × X))
    (hc : ∀ kx ∈ l, IsQueryBoundP (hashM IV ib ob od kx) p c) :
    IsQueryBoundP (hashAllM IV ib ob od l) p (l.length * c) := by
  induction l with
  | nil => simp [hashAllM]
  | cons kx l ih =>
    unfold hashAllM
    refine (isQueryBoundP_bind (hc kx (by simp)) fun d _ =>
      isQueryBoundP_bind (m := 0) (ih fun kx' h => hc kx' (by simp [h])) fun ds _ => by
        simp).mono ?_
    simp only [List.length_cons, Nat.succ_mul]
    omega

/-- A compression query of the adversary. -/
def isCompI : ℕ ⊕ ((St × Blk) ⊕ X) → Bool
  | .inr (.inl _) => true
  | _ => false

/-- A target query of the adversary. -/
def isTgtI : ℕ ⊕ ((St × Blk) ⊕ X) → Bool
  | .inr (.inr _) => true
  | _ => false

/-- Every target query `x` satisfies `OK (k, x)` for all keys `k`. -/
def tgtOK (OK : K × X → Prop) : ℕ ⊕ ((St × Blk) ⊕ X) → Prop
  | .inr (.inr x) => ∀ k, OK (k, x)
  | _ => True

/-- Target selection with an arbitrary final check costing at most one budget per input. -/
theorem targetRun_bound [SampleableType K] (hpl : ∀ n, ¬ p (.inl n))
    (c : ℕ) (OK : K × X → Prop)
    (finish : (K × X) × List (K × X) → OracleComp (unifSpec + mS St Blk) Bool)
    (hfinish : ∀ x s, OK x → (∀ t ∈ s, OK t) → IsQueryBoundP (finish (x,s)) p ((s.length + 1) * c))
    (A : OracleComp (unifSpec + (hS St Blk + ITSRTargetSpec X K)) (K × X)) :
    ∀ (q qs : ℕ) (s : List (K × X)),
      IsQueryBoundP A (fun i => isCompI i = true) q →
      IsQueryBoundP A (fun i => isTgtI i = true) qs →
      AllQueriesSatisfy A (tgtOK OK) →
      (∀ kx ∈ support A, OK kx) → (∀ kx ∈ s, OK kx) →
      IsQueryBoundP ((simulateQ tgtImpl A).run s >>= finish) p
        (q + (qs + s.length + 1) * c) := by
  induction A using OracleComp.inductionOn with
  | pure x =>
    intro q qs s _ _ _ hout hs
    simp only [simulateQ_pure, StateT.run_pure, pure_bind]
    apply (hfinish x s (hout x (by simp)) hs).mono
    rw [Nat.add_assoc qs s.length 1, Nat.add_mul qs (s.length + 1) c]
    omega
  | query_bind t k ih =>
    intro q qs s hq hqs htgt hout hs
    rw [isQueryBoundP_query_bind_iff] at hq hqs
    rw [allQueriesSatisfy_query_bind_iff] at htgt
    have hout' : ∀ u, ∀ kx ∈ support (k u), OK kx := fun u kx h =>
      hout kx ((mem_support_bind_iff _ _ _).2 ⟨u, by simp, h⟩)
    rcases t with n | q₀ | x
    · have e : (simulateQ tgtImpl
          (liftM ((unifSpec + (hS St Blk + ITSRTargetSpec X K)).query (.inl n)) >>= k)).run s =
          (liftM ((unifSpec + mS St Blk).query (.inl n)) : OracleComp (unifSpec + mS St Blk) _) >>=
            fun u => (simulateQ tgtImpl (k u)).run s := by
        simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, tgtImpl, StateT.run_mk,
          bind_map_left]
        rfl
      rw [e, bind_assoc, isQueryBoundP_query_bind_iff]
      refine ⟨Or.inl (hpl n), fun u => ?_⟩
      simp only [hpl n, ↓reduceIte]
      exact ih u q qs s (hq.2 u) (hqs.2 u) (htgt.2 u) (hout' u) hs
    · have e : (simulateQ tgtImpl
          (liftM ((unifSpec + (hS St Blk + ITSRTargetSpec X K)).query (.inr (.inl q₀))) >>= k)).run
            s =
          (liftM ((unifSpec + mS St Blk).query (.inr (q₀, true))) :
            OracleComp (unifSpec + mS St Blk) _) >>=
            fun u => (simulateQ tgtImpl (k u)).run s := by
        simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, tgtImpl, StateT.run_mk,
          bind_map_left]
        rfl
      have hpos : 0 < q := hq.1.resolve_left (fun h => h rfl)
      rw [e, bind_assoc, isQueryBoundP_query_bind_iff]
      refine ⟨Or.inr (by omega), fun u => ?_⟩
      have := ih u (q - 1) qs s (hq.2 u) (hqs.2 u) (htgt.2 u) (hout' u) hs
      refine this.mono ?_
      split <;> omega
    · have e : (simulateQ tgtImpl
          (liftM ((unifSpec + (hS St Blk + ITSRTargetSpec X K)).query (.inr (.inr x))) >>= k)).run
            s =
          (liftM ($ᵗ K : ProbComp K) : OracleComp (unifSpec + mS St Blk) K) >>=
            fun k' => (simulateQ tgtImpl (k k')).run (s ++ [(k', x)]) := by
        simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, tgtImpl, StateT.run_mk,
          bind_map_left]
      have hpos : 0 < qs := hqs.1.resolve_left (fun h => h rfl)
      have h0 : IsQueryBoundP (liftM ($ᵗ K : ProbComp K) : OracleComp (unifSpec + mS St Blk) K)
          p 0 :=
        IsQueryBoundP.of_imp (p' := fun t => t.isRight)
          (fun t ht => by
            rcases t with n | t
            · exact absurd ht (hpl n)
            · rfl)
          (isQueryBoundP_liftM_isRight _)
      rw [e, bind_assoc]
      refine (isQueryBoundP_bind (m := q + (qs + s.length + 1) * c) h0 fun k' _ =>
        (ih k' q (qs - 1) (s ++ [(k', x)]) (hq.2 k') (hqs.2 k') (htgt.2 k') (hout' k')
          (fun kx h => by
            rcases List.mem_append.mp h with h | h
            · exact hs kx h
            · rw [List.mem_singleton.mp h]; exact htgt.1 k')).mono ?_).mono (by omega)
      simp only [List.length_append, List.length_cons, List.length_nil]
      have : qs - 1 + (s.length + (0 + 1)) + 1 = qs + s.length + 1 := by omega
      rw [this]

theorem gameProg_bound_aux [SampleableType K] [DecidableEq K] [DecidableEq X]
    [DecidableEq Index] (hpl : ∀ n, ¬ p (.inl n))
    (IV : St) (ib : K × X → List Blk) (ob : K × X → St → List Blk) (od : St → Y)
    (idx : Y → List Index) (c : ℕ) (OK : K × X → Prop)
    (hOK : ∀ kx, OK kx → IsQueryBoundP (hashM IV ib ob od kx) p c)
    (A : OracleComp (unifSpec + (hS St Blk + ITSRTargetSpec X K)) (K × X)) :
    ∀ (q qs : ℕ) (s : List (K × X)),
      IsQueryBoundP A (fun i => isCompI i = true) q →
      IsQueryBoundP A (fun i => isTgtI i = true) qs →
      AllQueriesSatisfy A (tgtOK OK) →
      (∀ kx ∈ support A, OK kx) → (∀ kx ∈ s, OK kx) →
      IsQueryBoundP ((simulateQ tgtImpl A).run s >>= finM IV ib ob od idx) p
        (q + (qs + s.length + 1) * c) := by
  apply targetRun_bound hpl c OK _ _ A
  intro x s hx hs
  unfold finM
  refine (isQueryBoundP_bind (hashAllM_bound IV ib ob od c s fun kx h => hOK kx (hs kx h))
    fun ds _ => isQueryBoundP_bind (m := 0) (hOK x hx) fun d _ => by simp).mono ?_
  simp [Nat.add_mul]

/-- **Query bound of the experiment.**  If the adversary makes at most `q` compression queries
and `qs` target queries, all its target queries and candidates satisfy `OK`, and hashing an `OK`
input makes at most `c` `p`-queries, then the whole experiment makes at most
`q + (qs + 1) * c` `p`-queries. -/
theorem gameProg_bound [SampleableType K] [DecidableEq K] [DecidableEq X]
    [DecidableEq Index] (hpl : ∀ n, ¬ p (.inl n))
    (IV : St) (ib : K × X → List Blk) (ob : K × X → St → List Blk) (od : St → Y)
    (idx : Y → List Index) (c : ℕ) (OK : K × X → Prop)
    (hOK : ∀ kx, OK kx → IsQueryBoundP (hashM IV ib ob od kx) p c)
    (A : OracleComp (unifSpec + (hS St Blk + ITSRTargetSpec X K)) (K × X))
    (q qs : ℕ) (hq : IsQueryBoundP A (fun i => isCompI i = true) q)
    (hqs : IsQueryBoundP A (fun i => isTgtI i = true) qs)
    (htgt : AllQueriesSatisfy A (tgtOK OK))
    (hout : ∀ kx ∈ support A, OK kx) :
    IsQueryBoundP (gameProg IV ib ob od idx A) p (q + (qs + 1) * c) := by
  have h := gameProg_bound_aux hpl IV ib ob od idx c OK hOK A q qs [] hq hqs htgt hout (by simp)
  simpa [gameProg] using h

end Bounds

end Ideal.Itsr

#print axioms Ideal.Itsr.md_inj
#print axioms Ideal.Itsr.win_imp
#print axioms Ideal.Itsr.win_log
#print axioms Ideal.Itsr.itsr_le
#print axioms Ideal.Itsr.gameProg_bound
