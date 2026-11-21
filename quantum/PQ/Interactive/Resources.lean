import PQ.Interactive.Approx
import PQ.Interactive.Examples
import VCVio.OracleComp.QueryTracking.QueryBound.Basic

/-!
# Quantum and classical resources of machines, and their behaviour under black-box wrappers

The model has no cost notion, and every classical `ProbComp` adversary embeds into quantum
machines (`liftQ`).  Statements about what a reduction machine does to the workspace are therefore
expressed by theorems about the machine terms.  This file provides one such family (instrument
traces) and classical query counts; see the section on what the trace inclusions do and do not
say.

## What `instrTraces ⊆` says, and what it does not (audit F5)

`instrTraces X ⊆ instrTraces Q` says: along every root-to-leaf path of `X`, the SEQUENCE OF
INSTRUMENT INDICES is the sequence of instrument indices of some path of `Q`.  It bounds the number
and the identity (and order) of the quantum operations on every path; in particular a path of `X`
cannot contain the instruments of two runs of `Q` unless some single path of `Q` has that sequence.
It does NOT say that `X` follows the path of `Q` determined by the outcomes actually obtained (a
machine that continues "as if a different outcome had occurred" has the same traces whenever the
two subtrees have the same instrument sequences), and it does not exclude classical simulation:
classical code is not counted, and a classical program may carry a density matrix (the samplers of
`Approx.lean` do).  The statement that the wrapped machine IS the classical wrapper code around
the program of `Q` is the syntactic one: for EVERY sampler `s`,
`toProbCompWith s (wrap implB Q t) ρ = (simulateQ implB (toProbCompWith s Q ρ)).run t`
(`Approx.lean`; collected for the SLH-DSA machines in `Integration/SlhDsaAllCertificate.lean`).

## Quantum resources

* `instrTraces Q : Set (List (InstrIdx W))` — the sequences of instrument indices along the
  root-to-leaf paths of the control tree of `Q` (all classical answers, all outcomes);
* `NoInstr Q`, `InstrPathBound Q n`, `InstrOnly P Q` — derived measures (no instrument at all, at
  most `n` instruments on every path, every applied instrument satisfies `P`);
* calculus: `instrTraces_pure`, `mem_instrTraces_bind`, `instrTraces_liftQ` (classical code applies
  no instrument), and the **embedding theorems**
  `instrTraces_wrap_subset`, `instrTraces_wrap0_subset`, `instrTraces_close_subset`,
  `instrTraces_map_subset`, `instrTraces_qReduction_subset`, `instrTraces_qRunForger_subset`,
  `instrTraces_liftQ_bind_subset`, `instrTraces_bind_liftQ_subset`: the instrument sequence of any
  path of the wrapped machine is the instrument sequence of a path of `Q`.
* `UsesOnly P` (`Examples.lean`) is preserved by the same wrappers, and implies `InstrOnly P`.

## Classical query counts

* `ClassicalQueryBound X p n` — VCVio's `IsQueryBoundP` on the machine `X` (a machine is an
  `OracleComp`), counting the classical queries whose index satisfies `p` and no instrument node;
* `unifSamp` — the sampler that draws the outcome of an instrument with `j.1 + 1` outcomes
  uniformly; `toProbCompWith unifSamp X ρ` is the control tree of `X` with every instrument node
  relabelled as a uniform query;
* **transfer** (`classicalQueryBound_iff_unif`): if `p` does not count uniform-sampling queries,
  `ClassicalQueryBound X p n ↔ IsQueryBoundP (toProbCompWith unifSamp X ρ) p n`.  Since the
  wrappers commute with `toProbCompWith` for every sampler (`Approx.lean`), every classical
  query-count theorem about a reduction `B(A)` valid for all classical `A` transfers to the
  machine "`B` around `Q`".
* `isQueryBoundP_toProbCompWith`: for every sampler, the classical strategy makes at most the
  classical `p`-queries of the machine.
-/

open OracleComp OracleSpec ENNReal Quantum

namespace PQ.Interactive

variable {W : Type} [Fintype W] {α β γ : Type}
variable {ι : Type} {spec : OracleSpec ι} {ι' : Type} {spec' : OracleSpec ι'} {σ τ : Type}

/-! ## Instrument traces -/

/-- The set of sequences of instrument indices along the root-to-leaf paths of the control tree of
the machine `Q` (over all classical answers and all instrument outcomes): the sequences of instrument
indices that occur along the paths of `Q` (a syntactic notion: paths of Born weight zero are
included, outcomes are not recorded). -/
def instrTraces (Q : QOC W spec α) : Set (List (InstrIdx W)) :=
  OracleComp.construct (C := fun _ ↦ Set (List (InstrIdx W))) (fun _ ↦ {[]})
    (fun t _ ih ↦
      match t, ih with
      | .inl j, ih => {l | ∃ i, ∃ l' ∈ ih i, l = j :: l'}
      | .inr _, ih => ⋃ u, ih u) Q

@[simp] lemma instrTraces_pure (a : α) : instrTraces (pure a : QOC W spec α) = {[]} := rfl

lemma mem_instrTraces_instr_bind (j : InstrIdx W) (k : Fin (j.1 + 1) → QOC W spec α)
    (l : List (InstrIdx W)) :
    l ∈ instrTraces (liftM ((instrSpec W + spec).query (Sum.inl j)) >>= k) ↔
      ∃ i, ∃ l' ∈ instrTraces (k i), l = j :: l' := Iff.rfl

lemma mem_instrTraces_query_bind (t : spec.Domain) (k : spec.Range t → QOC W spec α)
    (l : List (InstrIdx W)) :
    l ∈ instrTraces (liftM ((instrSpec W + spec).query (Sum.inr t)) >>= k) ↔
      ∃ u, l ∈ instrTraces (k u) := by
  change l ∈ ⋃ u, instrTraces (k u) ↔ _
  exact Set.mem_iUnion

/-- A path of a composite is a path of the first machine followed by a path of a continuation. -/
theorem mem_instrTraces_bind (X : QOC W spec α) (f : α → QOC W spec β) {l : List (InstrIdx W)}
    (h : l ∈ instrTraces (X >>= f)) :
    ∃ a ∈ instrTraces X, ∃ x, ∃ b ∈ instrTraces (f x), l = a ++ b := by
  induction X using OracleComp.inductionOn generalizing l with
  | pure x => exact ⟨[], rfl, x, l, by simpa using h, rfl⟩
  | query_bind t k ih =>
    rcases t with j | t
    · rw [bind_assoc, mem_instrTraces_instr_bind] at h
      obtain ⟨i, l', hl', rfl⟩ := h
      obtain ⟨a, ha, x, b, hb, rfl⟩ := ih i hl'
      exact ⟨j :: a, (mem_instrTraces_instr_bind j k _).2 ⟨i, a, ha, rfl⟩, x, b, hb, rfl⟩
    · rw [bind_assoc, mem_instrTraces_query_bind] at h
      obtain ⟨u, hu⟩ := h
      obtain ⟨a, ha, x, b, hb, rfl⟩ := ih u hu
      exact ⟨a, (mem_instrTraces_query_bind t k _).2 ⟨u, ha⟩, x, b, hb, rfl⟩

/-- **Classical code applies no instrument.** -/
theorem instrTraces_liftQ (ob : OracleComp spec α) :
    instrTraces (liftQ ob : QOC W spec α) ⊆ {[]} := by
  induction ob using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    intro l hl
    rw [liftQ_query_bind, mem_instrTraces_query_bind] at hl
    obtain ⟨u, hu⟩ := hl
    exact ih u hu

/-- Classical probabilistic code inside a closed machine applies no instrument. -/
theorem instrTraces_liftU (oa : ProbComp α) : instrTraces (liftU oa : Closed W α) ⊆ {[]} :=
  instrTraces_liftQ (spec := unifSpec) oa

/-- Classical pre-processing adds no instrument. -/
theorem instrTraces_liftQ_bind_subset (ob : OracleComp spec γ) (F : γ → QOC W spec α) :
    instrTraces (liftQ ob >>= F) ⊆ ⋃ x, instrTraces (F x) := by
  intro l hl
  obtain ⟨a, ha, x, b, hb, rfl⟩ := mem_instrTraces_bind _ _ hl
  rw [instrTraces_liftQ ob ha]
  exact Set.mem_iUnion.2 ⟨x, hb⟩

/-- Classical post-processing adds no instrument. -/
theorem instrTraces_bind_liftQ_subset (Q : QOC W spec α) (post : α → OracleComp spec β) :
    instrTraces (Q >>= fun a ↦ liftQ (post a)) ⊆ instrTraces Q := by
  intro l hl
  obtain ⟨a, ha, x, b, hb, rfl⟩ := mem_instrTraces_bind _ _ hl
  rw [instrTraces_liftQ (post x) hb, List.append_nil]
  exact ha

theorem instrTraces_liftU_bind_subset (oa : ProbComp γ) (F : γ → Closed W α) :
    instrTraces (liftU oa >>= F) ⊆ ⋃ x, instrTraces (F x) :=
  instrTraces_liftQ_bind_subset (spec := unifSpec) oa F

theorem instrTraces_bind_liftU_subset (X : Closed W α) (post : α → ProbComp β) :
    instrTraces (X >>= fun a ↦ liftU (post a)) ⊆ instrTraces X :=
  instrTraces_bind_liftQ_subset (spec := unifSpec) X post

/-- Chaining forms: a set `S` of traces that contains the traces of every continuation (resp. of
the machine) contains those of the composite with classical pre- (resp. post-) processing. -/
theorem instrTraces_liftQ_bind_subset_of {S : Set (List (InstrIdx W))} (ob : OracleComp spec γ)
    (F : γ → QOC W spec α) (h : ∀ x, instrTraces (F x) ⊆ S) : instrTraces (liftQ ob >>= F) ⊆ S :=
  (instrTraces_liftQ_bind_subset ob F).trans (Set.iUnion_subset h)

theorem instrTraces_bind_liftQ_subset_of {S : Set (List (InstrIdx W))} (Q : QOC W spec α)
    (post : α → OracleComp spec β) (h : instrTraces Q ⊆ S) :
    instrTraces (Q >>= fun a ↦ liftQ (post a)) ⊆ S :=
  (instrTraces_bind_liftQ_subset Q post).trans h

theorem instrTraces_liftU_bind_subset_of {S : Set (List (InstrIdx W))} (oa : ProbComp γ)
    (F : γ → Closed W α) (h : ∀ x, instrTraces (F x) ⊆ S) : instrTraces (liftU oa >>= F) ⊆ S :=
  (instrTraces_liftU_bind_subset oa F).trans (Set.iUnion_subset h)

theorem instrTraces_bind_liftU_subset_of {S : Set (List (InstrIdx W))} (X : Closed W α)
    (post : α → ProbComp β) (h : instrTraces X ⊆ S) :
    instrTraces (X >>= fun a ↦ liftU (post a)) ⊆ S :=
  (instrTraces_bind_liftU_subset X post).trans h

/-- Relabelling the output changes no instrument. -/
theorem instrTraces_map_subset (f : α → β) (Q : QOC W spec α) :
    instrTraces (f <$> Q) ⊆ instrTraces Q := by
  have e : f <$> Q = Q >>= fun a ↦ liftQ (pure (f a) : OracleComp spec β) := by
    simp only [liftQ_pure]; exact map_eq_pure_bind f Q
  rw [e]
  exact instrTraces_bind_liftQ_subset Q _

/-- **Embedding theorem for stateful wrappers.**  The instrument-index sequence of every path of
the machine "`implB`'s classical code around `Q`" is the instrument-index sequence of a path of
`Q` (an inclusion of trace sets; see the file header for what this does not say). -/
theorem instrTraces_wrap_subset
    (implB : QueryImpl spec (StateT τ (OracleComp (unifSpec + spec')))) (Q : QOC W spec α)
    (t : τ) : instrTraces (wrap implB Q t) ⊆ instrTraces Q := by
  induction Q using OracleComp.inductionOn generalizing t with
  | pure a => simp
  | query_bind q k ih =>
    intro l hl
    rcases q with j | q
    · rw [wrap_instr_bind, mem_instrTraces_instr_bind] at hl
      obtain ⟨i, l', hl', rfl⟩ := hl
      exact (mem_instrTraces_instr_bind j k _).2 ⟨i, l', ih i t hl', rfl⟩
    · rw [wrap_query_bind] at hl
      obtain ⟨x, hx⟩ := Set.mem_iUnion.1 (instrTraces_liftQ_bind_subset _ _ hl)
      exact (mem_instrTraces_query_bind q k _).2 ⟨x.1, ih x.1 x.2 hx⟩

/-- **Embedding theorem for stateless wrappers.** -/
theorem instrTraces_wrap0_subset (h : QueryImpl spec (OracleComp (unifSpec + spec')))
    (Q : QOC W spec α) : instrTraces (wrap0 h Q) ⊆ instrTraces Q := by
  induction Q using OracleComp.inductionOn with
  | pure a => simp
  | query_bind q k ih =>
    intro l hl
    rcases q with j | q
    · rw [wrap0_instr_bind, mem_instrTraces_instr_bind] at hl
      obtain ⟨i, l', hl', rfl⟩ := hl
      exact (mem_instrTraces_instr_bind j k _).2 ⟨i, l', ih i hl', rfl⟩
    · rw [wrap0_query_bind] at hl
      obtain ⟨x, hx⟩ := Set.mem_iUnion.1 (instrTraces_liftQ_bind_subset _ _ hl)
      exact (mem_instrTraces_query_bind q k _).2 ⟨x, ih x hx⟩

/-- **Embedding theorem for closing.**  Answering the classical queries of `Q` by classical
stateful probabilistic code: every instrument trace of the closed machine is an instrument
trace of `Q`. -/
theorem instrTraces_close_subset (impl : QueryImpl spec (StateT σ ProbComp)) (Q : QOC W spec α)
    (s : σ) : instrTraces (close impl Q s) ⊆ instrTraces Q := by
  induction Q using OracleComp.inductionOn generalizing s with
  | pure a => simp
  | query_bind q k ih =>
    intro l hl
    rcases q with j | q
    · rw [close_instr_bind, mem_instrTraces_instr_bind] at hl
      obtain ⟨i, l', hl', rfl⟩ := hl
      exact (mem_instrTraces_instr_bind j k _).2 ⟨i, l', ih i s hl', rfl⟩
    · rw [close_query_bind] at hl
      obtain ⟨x, hx⟩ := Set.mem_iUnion.1 (instrTraces_liftU_bind_subset _ _ hl)
      exact (mem_instrTraces_query_bind q k _).2 ⟨x.1, ih x.1 x.2 hx⟩

/-- **Embedding theorem for reductions.**  The machine of a straight-line black-box reduction
(classical pre-processing, `Q a` run inside classical simulation code, classical post-processing)
has, along every path, the instrument-index sequence of a path of a single `Q a` (inclusion
of trace sets). -/
theorem instrTraces_qReduction_subset (pre : OracleComp (unifSpec + spec') γ)
    (implB : γ → QueryImpl (unifSpec + spec) (StateT τ (OracleComp (unifSpec + spec'))))
    (t₀ : γ → τ) (post : γ → α × τ → OracleComp (unifSpec + spec') β)
    (Q : γ → QOC W (unifSpec + spec) α) :
    instrTraces (qReduction pre implB t₀ post Q) ⊆ ⋃ a, instrTraces (Q a) := by
  intro l hl
  obtain ⟨a, ha⟩ := Set.mem_iUnion.1 (instrTraces_liftQ_bind_subset _ _ hl)
  exact Set.mem_iUnion.2 ⟨a, instrTraces_wrap_subset _ _ _ (instrTraces_bind_liftQ_subset _ _ ha)⟩

/-- Every instrument trace of the forger harness is an instrument trace of the forger. -/
theorem instrTraces_qRunForger_subset {Msg Sig : Type} (Q : QOC W (unifSpec + (Msg →ₒ Sig)) α)
    (sign : Msg → OracleComp (unifSpec + spec') Sig) :
    instrTraces (qRunForger Q sign) ⊆ instrTraces Q :=
  instrTraces_wrap_subset _ Q []

/-! ### Derived measures -/

/-- The machine applies no instrument on any path (it is classical code). -/
def NoInstr (Q : QOC W spec α) : Prop := instrTraces Q ⊆ {[]}

/-- Every path of the machine applies at most `n` instruments. -/
def InstrPathBound (Q : QOC W spec α) (n : ℕ) : Prop := ∀ l ∈ instrTraces Q, l.length ≤ n

/-- Every instrument applied on some path of the machine satisfies `P`. -/
def InstrOnly (P : InstrIdx W → Prop) (Q : QOC W spec α) : Prop :=
  ∀ l ∈ instrTraces Q, ∀ j ∈ l, P j

theorem noInstr_liftQ (ob : OracleComp spec α) : NoInstr (liftQ ob : QOC W spec α) :=
  instrTraces_liftQ ob

theorem noInstr_liftU (oa : ProbComp α) : NoInstr (liftU oa : Closed W α) :=
  instrTraces_liftU oa

theorem noInstr_iff_instrPathBound_zero (Q : QOC W spec α) : NoInstr Q ↔ InstrPathBound Q 0 := by
  constructor
  · intro h l hl
    rw [h hl]; rfl
  · intro h l hl
    exact List.length_eq_zero_iff.1 (Nat.le_zero.1 (h l hl))

/-- All three measures are monotone in the set of traces, hence inherited through every
embedding theorem above. -/
theorem InstrPathBound.of_subset {ι₂ : Type} {spec₂ : OracleSpec ι₂} {Q : QOC W spec α}
    {Q' : QOC W spec₂ β} {n : ℕ} (h : InstrPathBound Q n) (hs : instrTraces Q' ⊆ instrTraces Q) :
    InstrPathBound Q' n := fun l hl ↦ h l (hs hl)

theorem InstrOnly.of_subset {ι₂ : Type} {spec₂ : OracleSpec ι₂} {P : InstrIdx W → Prop}
    {Q : QOC W spec α} {Q' : QOC W spec₂ β} (h : InstrOnly P Q)
    (hs : instrTraces Q' ⊆ instrTraces Q) : InstrOnly P Q' := fun l hl ↦ h l (hs hl)

theorem NoInstr.of_subset {ι₂ : Type} {spec₂ : OracleSpec ι₂} {Q : QOC W spec α}
    {Q' : QOC W spec₂ β} (h : NoInstr Q) (hs : instrTraces Q' ⊆ instrTraces Q) : NoInstr Q' :=
  hs.trans h

theorem instrPathBound_wrap
    (implB : QueryImpl spec (StateT τ (OracleComp (unifSpec + spec')))) {Q : QOC W spec α}
    {n : ℕ} (h : InstrPathBound Q n) (t : τ) : InstrPathBound (wrap implB Q t) n :=
  h.of_subset (instrTraces_wrap_subset implB Q t)

theorem instrPathBound_wrap0 (h : QueryImpl spec (OracleComp (unifSpec + spec')))
    {Q : QOC W spec α} {n : ℕ} (hQ : InstrPathBound Q n) : InstrPathBound (wrap0 h Q) n :=
  hQ.of_subset (instrTraces_wrap0_subset h Q)

theorem instrPathBound_close (impl : QueryImpl spec (StateT σ ProbComp)) {Q : QOC W spec α}
    {n : ℕ} (h : InstrPathBound Q n) (s : σ) : InstrPathBound (close impl Q s) n :=
  h.of_subset (instrTraces_close_subset impl Q s)

theorem instrPathBound_qReduction (pre : OracleComp (unifSpec + spec') γ)
    (implB : γ → QueryImpl (unifSpec + spec) (StateT τ (OracleComp (unifSpec + spec'))))
    (t₀ : γ → τ) (post : γ → α × τ → OracleComp (unifSpec + spec') β)
    {Q : γ → QOC W (unifSpec + spec) α} {n : ℕ} (h : ∀ a, InstrPathBound (Q a) n) :
    InstrPathBound (qReduction pre implB t₀ post Q) n := by
  intro l hl
  obtain ⟨a, ha⟩ := Set.mem_iUnion.1 (instrTraces_qReduction_subset pre implB t₀ post Q hl)
  exact h a l ha

/-- The tree predicate `UsesOnly P` of `Examples.lean` implies the path predicate. -/
theorem UsesOnly.instrOnly {P : InstrIdx W → Prop} {Q : QOC W spec α} (h : UsesOnly P Q) :
    InstrOnly P Q := by
  induction Q using OracleComp.inductionOn with
  | pure a =>
    intro l hl j hj
    rw [instrTraces_pure, Set.mem_singleton_iff] at hl
    simp [hl] at hj
  | query_bind t k ih =>
    intro l hl j' hj'
    rcases t with j | t
    · rw [usesOnly_instr_bind] at h
      rw [mem_instrTraces_instr_bind] at hl
      obtain ⟨i, l', hl', rfl⟩ := hl
      rcases List.mem_cons.1 hj' with rfl | hj'
      · exact h.1
      · exact ih i (h.2 i) l' hl' j' hj'
    · rw [usesOnly_query_bind] at h
      rw [mem_instrTraces_query_bind] at hl
      obtain ⟨u, hu⟩ := hl
      exact ih u (h u) l hu j' hj'

/-! ### `UsesOnly` through the wrappers -/

lemma usesOnly_liftQ_bind (P : InstrIdx W → Prop) (ob : OracleComp spec γ)
    (F : γ → QOC W spec α) (h : ∀ x, UsesOnly P (F x)) : UsesOnly P (liftQ ob >>= F) := by
  induction ob using OracleComp.inductionOn with
  | pure a => simpa using h a
  | query_bind t k ih =>
    rw [liftQ_query_bind, bind_assoc, usesOnly_query_bind]
    exact ih

lemma usesOnly_liftQ (P : InstrIdx W → Prop) (ob : OracleComp spec α) :
    UsesOnly P (liftQ ob : QOC W spec α) := by
  simpa using usesOnly_liftQ_bind P ob (pure : α → QOC W spec α) (by simp)

theorem usesOnly_wrap (P : InstrIdx W → Prop)
    (implB : QueryImpl spec (StateT τ (OracleComp (unifSpec + spec')))) (Q : QOC W spec α)
    (t : τ) (h : UsesOnly P Q) : UsesOnly P (wrap implB Q t) := by
  induction Q using OracleComp.inductionOn generalizing t with
  | pure a => simp
  | query_bind q k ih =>
    rcases q with j | q
    · rw [usesOnly_instr_bind] at h
      rw [wrap_instr_bind, usesOnly_instr_bind]
      exact ⟨h.1, fun i ↦ ih i _ (h.2 i)⟩
    · rw [usesOnly_query_bind] at h
      rw [wrap_query_bind]
      exact usesOnly_liftQ_bind _ _ _ fun x ↦ ih _ _ (h _)

theorem usesOnly_wrap0 (P : InstrIdx W → Prop)
    (h : QueryImpl spec (OracleComp (unifSpec + spec'))) (Q : QOC W spec α)
    (hQ : UsesOnly P Q) : UsesOnly P (wrap0 h Q) := by
  induction Q using OracleComp.inductionOn with
  | pure a => simp
  | query_bind q k ih =>
    rcases q with j | q
    · rw [usesOnly_instr_bind] at hQ
      rw [wrap0_instr_bind, usesOnly_instr_bind]
      exact ⟨hQ.1, fun i ↦ ih i (hQ.2 i)⟩
    · rw [usesOnly_query_bind] at hQ
      rw [wrap0_query_bind]
      exact usesOnly_liftQ_bind _ _ _ fun x ↦ ih _ (hQ _)

theorem usesOnly_close (P : InstrIdx W → Prop) (impl : QueryImpl spec (StateT σ ProbComp))
    (Q : QOC W spec α) (s : σ) (h : UsesOnly P Q) : UsesOnly P (close impl Q s) := by
  induction Q using OracleComp.inductionOn generalizing s with
  | pure a => simp
  | query_bind q k ih =>
    rcases q with j | q
    · rw [usesOnly_instr_bind] at h
      rw [close_instr_bind, usesOnly_instr_bind]
      exact ⟨h.1, fun i ↦ ih i _ (h.2 i)⟩
    · rw [usesOnly_query_bind] at h
      rw [close_query_bind]
      exact usesOnly_liftQ_bind (spec := unifSpec) _ _ _ fun x ↦ ih _ _ (h _)

theorem usesOnly_qReduction (P : InstrIdx W → Prop) (pre : OracleComp (unifSpec + spec') γ)
    (implB : γ → QueryImpl (unifSpec + spec) (StateT τ (OracleComp (unifSpec + spec'))))
    (t₀ : γ → τ) (post : γ → α × τ → OracleComp (unifSpec + spec') β)
    (Q : γ → QOC W (unifSpec + spec) α) (hQ : ∀ a, UsesOnly P (Q a)) :
    UsesOnly P (qReduction pre implB t₀ post Q) :=
  usesOnly_liftQ_bind _ _ _ fun a ↦
    usesOnly_bind _ _ _ (usesOnly_wrap _ _ _ _ (hQ a)) fun _ ↦ usesOnly_liftQ _ _

/-! ## Classical query counts of machines -/

/-- The predicate on the query indices of a machine that selects the classical queries whose
index satisfies `p` (and no instrument node). -/
def classicalPred (W : Type) [Fintype W] (p : ι → Prop) : InstrIdx W ⊕ ι → Prop
  | .inl _ => False
  | .inr t => p t

instance (p : ι → Prop) [DecidablePred p] : DecidablePred (classicalPred W p)
  | .inl _ => isFalse fun h ↦ h
  | .inr t => inferInstanceAs (Decidable (p t))

/-- Every path of the machine `X` makes at most `n` classical queries whose index satisfies `p`:
VCVio's `IsQueryBoundP` on the control tree of the machine. -/
def ClassicalQueryBound (X : QOC W spec α) (p : ι → Prop) [DecidablePred p] (n : ℕ) : Prop :=
  IsQueryBoundP X (classicalPred W p) n

lemma classicalQueryBound_instr_bind (p : ι → Prop) [DecidablePred p] (j : InstrIdx W)
    (k : Fin (j.1 + 1) → QOC W spec α) (n : ℕ) :
    ClassicalQueryBound (liftM ((instrSpec W + spec).query (Sum.inl j)) >>= k) p n ↔
      ∀ i, ClassicalQueryBound (k i) p n := by
  unfold ClassicalQueryBound
  rw [isQueryBoundP_query_bind_iff]
  have hf : ¬ classicalPred W p (Sum.inl j) := fun h ↦ h
  simp only [hf, not_false_eq_true, true_or, true_and, ite_false]
  rfl

lemma classicalQueryBound_query_bind (p : ι → Prop) [DecidablePred p] (t : spec.Domain)
    (k : spec.Range t → QOC W spec α) (n : ℕ) :
    ClassicalQueryBound (liftM ((instrSpec W + spec).query (Sum.inr t)) >>= k) p n ↔
      (¬ p t ∨ 0 < n) ∧ ∀ u, ClassicalQueryBound (k u) p (if p t then n - 1 else n) := by
  unfold ClassicalQueryBound
  rw [isQueryBoundP_query_bind_iff]
  rfl

/-- The uniform sampler: the outcome of an instrument with `j.1 + 1` outcomes is drawn with one
uniform query (every outcome is reachable). -/
def unifSamp : Sampler W := fun j _ ↦ liftM (unifSpec.query j.1)

lemma liftL_query_bind (m : ℕ) (k : Fin (m + 1) → ProbComp γ) :
    (liftL (liftM (unifSpec.query m) >>= k) : OracleComp (unifSpec + spec') γ) =
      liftM ((unifSpec + spec').query (Sum.inl m)) >>= fun i ↦ liftL (k i) := by
  simp [liftL]

/-- Classical sampling code followed by a continuation: if `p` does not count uniform queries,
the bound of the continuations is the bound of the composite. -/
lemma isQueryBoundP_liftL_bind (p : ℕ ⊕ ι' → Prop) [DecidablePred p] (hp : ∀ m, ¬ p (Sum.inl m))
    (oa : ProbComp γ) (K : γ → OracleComp (unifSpec + spec') α) (n : ℕ)
    (h : ∀ x, IsQueryBoundP (K x) p n) : IsQueryBoundP (liftL oa >>= K) p n := by
  induction oa using OracleComp.inductionOn with
  | pure a => simpa [liftL] using h a
  | query_bind m k ih =>
    rw [liftL_query_bind, bind_assoc, isQueryBoundP_query_bind_iff]
    simp only [hp m, not_false_eq_true, true_or, true_and, ite_false]
    exact ih

/-- **For every sampler, the classical strategy of a machine makes at most the classical
`p`-queries of the machine** (for `p` not counting uniform sampling). -/
theorem isQueryBoundP_toProbCompWith (s : Sampler W) (p : ℕ ⊕ ι' → Prop) [DecidablePred p]
    (hp : ∀ m, ¬ p (Sum.inl m)) (X : QOC W (unifSpec + spec') α) (n : ℕ) (ρ : Matrix W W ℂ)
    (h : ClassicalQueryBound X p n) : IsQueryBoundP (toProbCompWith s X ρ) p n := by
  induction X using OracleComp.inductionOn generalizing n ρ with
  | pure a => exact isQueryBoundP_pure _ _ _
  | query_bind t k ih =>
    rcases t with j | t
    · rw [classicalQueryBound_instr_bind] at h
      rw [toProbCompWith_instr_bind]
      exact isQueryBoundP_liftL_bind p hp _ _ n fun i ↦ ih i n _ (h i)
    · rw [classicalQueryBound_query_bind] at h
      rw [toProbCompWith_query_bind, isQueryBoundP_query_bind_iff]
      exact ⟨h.1, fun u ↦ ih u _ ρ (h.2 u)⟩

/-- **Transfer of classical query counts.**  For a predicate `p` that does not count uniform
sampling, the classical `p`-query count of a machine is the `p`-query count of its control tree
with the instrument nodes relabelled as uniform queries (`toProbCompWith unifSamp`). -/
theorem classicalQueryBound_iff_unif (p : ℕ ⊕ ι' → Prop) [DecidablePred p]
    (hp : ∀ m, ¬ p (Sum.inl m)) (X : QOC W (unifSpec + spec') α) (n : ℕ) (ρ : Matrix W W ℂ) :
    ClassicalQueryBound X p n ↔ IsQueryBoundP (toProbCompWith unifSamp X ρ) p n := by
  refine ⟨isQueryBoundP_toProbCompWith unifSamp p hp X n ρ, fun h ↦ ?_⟩
  induction X using OracleComp.inductionOn generalizing n ρ with
  | pure a => exact isQueryBoundP_pure _ _ _
  | query_bind t k ih =>
    rcases t with j | t
    · rw [classicalQueryBound_instr_bind]
      rw [toProbCompWith_instr_bind] at h
      have e : (liftL (unifSamp j ρ) : OracleComp (unifSpec + spec') _) =
          liftM ((unifSpec + spec').query (Sum.inl j.1)) := by
        simp [liftL, unifSamp]
      rw [e, isQueryBoundP_query_bind_iff] at h
      simp only [hp j.1, ite_false] at h
      exact fun i ↦ ih i n _ (h.2 i)
    · rw [classicalQueryBound_query_bind]
      rw [toProbCompWith_query_bind, isQueryBoundP_query_bind_iff] at h
      exact ⟨h.1, fun u ↦ ih u _ ρ (h.2 u)⟩

/-- **Transfer principle.**  If the uniform-sampler classicalisation of the machine `X` is the
classical program `B` (as it is for "reduction `B(·)` around `Q`", by the commutation lemmas of
`Approx.lean`), every `p`-query bound of `B` is a classical `p`-query bound of the machine. -/
theorem classicalQueryBound_of_eq (p : ℕ ⊕ ι' → Prop) [DecidablePred p]
    (hp : ∀ m, ¬ p (Sum.inl m)) (X : QOC W (unifSpec + spec') α) (ρ : Matrix W W ℂ)
    {B : OracleComp (unifSpec + spec') α} (hB : toProbCompWith unifSamp X ρ = B) {n : ℕ}
    (h : IsQueryBoundP B p n) : ClassicalQueryBound X p n :=
  (classicalQueryBound_iff_unif p hp X n ρ).2 (hB ▸ h)

end PQ.Interactive

open PQ.Interactive in
#print axioms mem_instrTraces_bind
open PQ.Interactive in
#print axioms instrTraces_wrap_subset
open PQ.Interactive in
#print axioms instrTraces_wrap0_subset
open PQ.Interactive in
#print axioms instrTraces_close_subset
open PQ.Interactive in
#print axioms instrTraces_qReduction_subset
open PQ.Interactive in
#print axioms UsesOnly.instrOnly
open PQ.Interactive in
#print axioms usesOnly_qReduction
open PQ.Interactive in
#print axioms isQueryBoundP_toProbCompWith
open PQ.Interactive in
#print axioms classicalQueryBound_iff_unif
