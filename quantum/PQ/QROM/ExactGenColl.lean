import PQ.QROM.ExactTcr

/-!
# The exact SM-DT-TCR game in the QROM, with a general collection

`PQ/QROM/ExactTcr.lean` formalises VCVio's `TweakableHash.SM_DT_TCR_Experiment`
(`VCVio/CryptoFoundations/HardnessAssumptions/TweakableHash/SMDTTCR.lean`) with one deviation:
its collection oracle evaluates the attacked function itself.  In VCVio the collection is a
`TweakableHashCollection ι PkSeed Tweak Y`, an indexed family
`eval : (i : ι) → PkSeed → Tweak → Msg i → Y` of OTHER tweakable hashes at the same seed, and a
collection query is `⟨i, t, m⟩` with `m : thColl.Msg i`.  This file removes the deviation.

## Model

* `ι` is a finite index type, `MsgC : ι → Type` a family of finite message types,
  `C := Σ i, MsgC i` and `MsgT := Msg ⊕ C`.  There is ONE uniformly random function
  `Th : Sd × (Tw × MsgT) → Y`.  Equivalently: the attacked hash `Th (P, (t, .inl m))` together
  with the members `Th (P, (t, .inr ⟨i, m⟩))`, `i : ι`, of the collection; all of them are
  independent uniformly random functions, at the same seed `P` and over the same tweak space.
* The adversary is an `IAdv` over `qrom2Spec (Dom Sd Tw MsgT) Y`: in both phases it has quantum
  access to the whole of `Th` (attacked member and collection, at every seed); phase 1 does not
  receive the seed and additionally sends classical requests to the two oracles of the game;
  phase 2 receives the seed and returns `(j, m) : ℕ × Msg`.
* The challenger is `genCollChOf κ cap a`, where `a = rowOf Th P : Tw × MsgT → Y` is the row at
  the seed and `κ : Cq → MsgT` says which point of the row a collection query names (`Cq` is the
  type of collection queries without their tweak).  Its rules are exactly those of VCVio:
  - `Sum.inl (t, m)` (`SM_DT_TCR_challengeOracle`): rejected (`none`, state unchanged) iff the
    cap is reached (`cap ≤ chal.length`), or `t` occurs in the challenge history
    (`TweakReserved`), or `t` occurs among the collection tweaks (together: `¬ TweakFresh`);
    otherwise answered `some (a (t, .inl m))`, and `(t, m)` is appended to the challenge
    history.
  - `Sum.inr (t, c)` (`collectionOracle`): rejected iff `t` occurs in the challenge history
    (`TweakReserved`); otherwise answered `some (a (t, κ c))` and the query is appended to the
    collection history.  Repeated collection tweaks are accepted, as in VCVio.
  The lemmas `genCollChOf_inl_fst`, `genCollChOf_inl_chal`, `genCollChOf_inl_tweaks`,
  `genCollChOf_inr_fst`, `genCollChOf_inr_chal`, `genCollChOf_inr_tweaks` state these rules on
  VCVio's state shape `(chal, collection tweaks)`.
* State (`GenCollState`): the challenge history `List (Tw × Msg)` as in VCVio, and the
  collection history.  VCVio keeps the collection TWEAKS only (`List Tweak`); here the whole
  accepted collection query `(t, c)` is kept (`coll : List (Tw × Cq)`), and VCVio's list is
  `GenCollState.tweaks = coll.map Prod.fst`.  The extra component is used only by the locality
  lemma (`genCollChOf_loc`: the answers depend on the row only at the recorded points); every
  accept/reject decision reads `coll` through `coll.map Prod.fst` only, so no answer changes.
* Win (`genCollWin`): the `j`-th entry `(t, mj)` of the challenge history exists, `m ≠ mj` and
  `a (t, .inl m) = a (t, .inl mj)`.

## The three instances (choice of the request type)

The challenger and the theorems are stated for an arbitrary `κ : Cq → Msg ⊕ C`
(`genCollTcrExpOf`, `gen_coll_tcr_exact_of_le`); this costs nothing in the proof, which only
uses that the answers are values of the row at recorded points.  The instances are:

* `genCollTcrExp` (`κ = Sum.inr`, `Cq = C = Σ i, MsgC i`): VCVio's game for a collection
  `thColl` with `thColl.Msg = MsgC` of hashes distinct from the attacked one.  Collection
  requests are `(t, ⟨i, m⟩)`, VCVio's `⟨i, t, m⟩`.  Theorems `gen_coll_tcr_exact_sqrt_le`,
  `gen_coll_tcr_exact_le`, `genCollTcrExp_le_one`.
* The stand-alone game (`TweakableHashCollection.empty`, `SM_DT_TCR_Problem.standalone`) is
  `genCollTcrExp` at `ι = Empty`: the type of collection requests is empty
  (`genColl_isEmpty_collReq`, the analogue of `isEmpty_domain_collectionSpec_empty`), and the
  bound is `gen_coll_tcr_exact_standalone_le`.
* `genCollConsTcrExp` (`TweakableHashCollection.cons th thColl`, HK22's `Th_m ∈ Th_λ`): the
  collection is indexed by `Option ι`, with the attacked member at index `none`
  (`genCollConsMsg`), and `κ = genCollConsEmb` sends `⟨none, m⟩` to `.inl m` (the attacked
  function, `genCollConsEmb_none`, the analogue of `cons_eval_none`) and `⟨some i, m⟩` to
  `.inr ⟨i, m⟩` (`genCollConsEmb_some`).  So the attacked function can be evaluated classically
  at tweaks that are not targets.  Theorem `gen_coll_cons_tcr_exact_le`.  The game of
  `ExactTcr.lean` is the sub-case `ι = Empty` of this one, up to the relabelling of requests.

## Result

`Pr[win] ≤ (√((2 q₂ + 1)² / |Y|) + 2 q₁ / √|Sd|)²` in all cases, independently of the
collection, of the number of targets and of the number of classical requests.  The proof is the
one of `ExactTcr.lean`: `seed_hiding` and `twoPhaseHyb_le_of_leaf` are generic in the
challenger, and `spr_embedded_obs_weighted_le` is applied at the message type `MsgT`, with
targets `(t, .inl mj)` and the output `(j, m)` decoded as `(t_j, .inl m)`.
-/

open MeasureTheory ENNReal Quantum Matrix
open scoped Kronecker ComplexOrder

universe u v w

set_option linter.unusedSectionVars false

namespace PQ.QROM

variable {Sd Tw Msg C Cq Y : Type}

/-! ## The challenger -/

/-- The state of the SM-DT-TCR game with a collection: the challenge history (accepted targets,
in issue order) and the collection history (accepted collection queries, in issue order).
VCVio's state is `(chal, tweaks)`.  By construction the target tweaks are pairwise distinct and
no collection query is on a target tweak. -/
structure GenCollState (Tw Msg Cq : Type) where
  /-- The accepted targets, in issue order. -/
  chal : List (Tw × Msg)
  /-- The accepted collection queries, in issue order. -/
  coll : List (Tw × Cq)
  /-- The target tweaks are pairwise distinct. -/
  nodup : (chal.map Prod.fst).Nodup
  /-- No collection query is on a target tweak. -/
  disj : ∀ p ∈ coll, p.1 ∉ chal.map Prod.fst

/-- The collection tweaks: the second component of VCVio's state. -/
def GenCollState.tweaks (s : GenCollState Tw Msg Cq) : List Tw := s.coll.map Prod.fst

/-- The empty histories. -/
def genCollInit : GenCollState Tw Msg Cq := ⟨[], [], List.nodup_nil, fun _ h ↦ by simp at h⟩

/-- The two classical oracles of SM-DT-TCR with a collection, for the row `a` of the random
function at the seed, with target cap `cap`.  `Sum.inl (t, m)`: challenge oracle, answering with
the attacked member `a (t, .inl m)`.  `Sum.inr (t, c)`: collection oracle, answering with
`a (t, κ c)`. -/
def genCollChOf [DecidableEq Tw] (κ : Cq → Msg ⊕ C) (cap : ℕ) (a : Tw × (Msg ⊕ C) → Y) :
    (Tw × Msg) ⊕ (Tw × Cq) → GenCollState Tw Msg Cq → Option Y × GenCollState Tw Msg Cq
  | .inl tm, s =>
    if h : cap ≤ s.chal.length ∨ tm.1 ∈ s.chal.map Prod.fst ∨ tm.1 ∈ s.coll.map Prod.fst then
      (none, s)
    else (some (a (tm.1, Sum.inl tm.2)), ⟨s.chal ++ [tm], s.coll, by
        rw [List.map_append, List.map_singleton]
        exact List.Nodup.append s.nodup (List.nodup_singleton _) (by
          intro t ht ht'
          rw [List.mem_singleton] at ht'
          exact h (Or.inr (Or.inl (ht' ▸ ht)))), by
        intro p hp hmem
        rw [List.map_append, List.map_singleton, List.mem_append, List.mem_singleton] at hmem
        rcases hmem with hmem | hmem
        · exact s.disj p hp hmem
        · exact h (Or.inr (Or.inr (hmem ▸ List.mem_map.2 ⟨p, hp, rfl⟩)))⟩)
  | .inr tc, s =>
    if h : tc.1 ∈ s.chal.map Prod.fst then (none, s)
    else (some (a (tc.1, κ tc.2)), ⟨s.chal, s.coll ++ [tc], s.nodup, by
        intro p hp
        rw [List.mem_append, List.mem_singleton] at hp
        rcases hp with hp | hp
        · exact s.disj p hp
        · rw [hp]; exact h⟩)

/-- The winning condition of SM-DT-TCR: the result `(j, m)` names a recorded target
`(t, mj)` and a message `m ≠ mj` colliding with it under the attacked member of the row `a`. -/
def genCollWin (a : Tw × (Msg ⊕ C) → Y) (r : ℕ × Msg) (s : GenCollState Tw Msg Cq) : Prop :=
  ∃ t mj, s.chal[r.1]? = some (t, mj) ∧ r.2 ≠ mj ∧
    a (t, Sum.inl r.2) = a (t, Sum.inl mj)

section Challenger

variable [DecidableEq Tw]

/-! ### The rules, on VCVio's state shape `(chal, tweaks)` -/

/-- Challenge oracle, answer: `none` iff the cap is reached or the tweak is not fresh (reserved
by the challenge history, or spent on the collection oracle); else the attacked hash. -/
theorem genCollChOf_inl_fst (κ : Cq → Msg ⊕ C) (cap : ℕ) (a : Tw × (Msg ⊕ C) → Y) (tm : Tw × Msg)
    (s : GenCollState Tw Msg Cq) :
    (genCollChOf κ cap a (.inl tm) s).1 =
      if cap ≤ s.chal.length ∨ ¬ ((¬ ∃ e ∈ s.chal, e.1 = tm.1) ∧ tm.1 ∉ s.tweaks) then none
      else some (a (tm.1, Sum.inl tm.2)) := by
  have hiff : (cap ≤ s.chal.length ∨ ¬ ((¬ ∃ e ∈ s.chal, e.1 = tm.1) ∧ tm.1 ∉ s.tweaks)) ↔
      (cap ≤ s.chal.length ∨ tm.1 ∈ s.chal.map Prod.fst ∨ tm.1 ∈ s.coll.map Prod.fst) := by
    simp only [GenCollState.tweaks, List.mem_map, not_and_or, not_not]
  simp only [genCollChOf]
  by_cases h : cap ≤ s.chal.length ∨ tm.1 ∈ s.chal.map Prod.fst ∨ tm.1 ∈ s.coll.map Prod.fst
  · rw [dite_eq_left_of_eq_true (eq_true h), ite_eq_left_of_eq_true _ _ (eq_true (hiff.2 h))]
  · rw [dite_eq_right_of_eq_false (eq_false h),
      ite_eq_right_of_eq_false _ _ (eq_false fun h' ↦ h (hiff.1 h'))]

/-- Challenge oracle, challenge history: unchanged on rejection, else the query is appended. -/
theorem genCollChOf_inl_chal (κ : Cq → Msg ⊕ C) (cap : ℕ) (a : Tw × (Msg ⊕ C) → Y)
    (tm : Tw × Msg) (s : GenCollState Tw Msg Cq) :
    (genCollChOf κ cap a (.inl tm) s).2.chal =
      if cap ≤ s.chal.length ∨ ¬ ((¬ ∃ e ∈ s.chal, e.1 = tm.1) ∧ tm.1 ∉ s.tweaks) then s.chal
      else s.chal ++ [tm] := by
  have hiff : (cap ≤ s.chal.length ∨ ¬ ((¬ ∃ e ∈ s.chal, e.1 = tm.1) ∧ tm.1 ∉ s.tweaks)) ↔
      (cap ≤ s.chal.length ∨ tm.1 ∈ s.chal.map Prod.fst ∨ tm.1 ∈ s.coll.map Prod.fst) := by
    simp only [GenCollState.tweaks, List.mem_map, not_and_or, not_not]
  simp only [genCollChOf]
  by_cases h : cap ≤ s.chal.length ∨ tm.1 ∈ s.chal.map Prod.fst ∨ tm.1 ∈ s.coll.map Prod.fst
  · rw [dite_eq_left_of_eq_true (eq_true h), ite_eq_left_of_eq_true _ _ (eq_true (hiff.2 h))]
  · rw [dite_eq_right_of_eq_false (eq_false h),
      ite_eq_right_of_eq_false _ _ (eq_false fun h' ↦ h (hiff.1 h'))]

/-- The challenge oracle never changes the collection tweaks. -/
theorem genCollChOf_inl_tweaks (κ : Cq → Msg ⊕ C) (cap : ℕ) (a : Tw × (Msg ⊕ C) → Y)
    (tm : Tw × Msg) (s : GenCollState Tw Msg Cq) :
    (genCollChOf κ cap a (.inl tm) s).2.tweaks = s.tweaks := by
  simp only [genCollChOf]
  split_ifs <;> rfl

/-- Collection oracle, answer: `none` iff the tweak is reserved by the challenge history; else
the value of the queried member. -/
theorem genCollChOf_inr_fst (κ : Cq → Msg ⊕ C) (cap : ℕ) (a : Tw × (Msg ⊕ C) → Y) (tc : Tw × Cq)
    (s : GenCollState Tw Msg Cq) :
    (genCollChOf κ cap a (.inr tc) s).1 =
      if ∃ e ∈ s.chal, e.1 = tc.1 then none else some (a (tc.1, κ tc.2)) := by
  have hiff : (∃ e ∈ s.chal, e.1 = tc.1) ↔ tc.1 ∈ s.chal.map Prod.fst := by
    simp only [List.mem_map]
  simp only [genCollChOf]
  by_cases h : tc.1 ∈ s.chal.map Prod.fst
  · rw [dite_eq_left_of_eq_true (eq_true h), ite_eq_left_of_eq_true _ _ (eq_true (hiff.2 h))]
  · rw [dite_eq_right_of_eq_false (eq_false h),
      ite_eq_right_of_eq_false _ _ (eq_false fun h' ↦ h (hiff.1 h'))]

/-- The collection oracle never changes the challenge history. -/
theorem genCollChOf_inr_chal (κ : Cq → Msg ⊕ C) (cap : ℕ) (a : Tw × (Msg ⊕ C) → Y)
    (tc : Tw × Cq) (s : GenCollState Tw Msg Cq) :
    (genCollChOf κ cap a (.inr tc) s).2.chal = s.chal := by
  simp only [genCollChOf]
  split_ifs <;> rfl

/-- Collection oracle, collection tweaks: unchanged on rejection, else the tweak is appended
(also when it is a repeated collection tweak). -/
theorem genCollChOf_inr_tweaks (κ : Cq → Msg ⊕ C) (cap : ℕ) (a : Tw × (Msg ⊕ C) → Y)
    (tc : Tw × Cq) (s : GenCollState Tw Msg Cq) :
    (genCollChOf κ cap a (.inr tc) s).2.tweaks =
      if ∃ e ∈ s.chal, e.1 = tc.1 then s.tweaks else s.tweaks ++ [tc.1] := by
  have hiff : (∃ e ∈ s.chal, e.1 = tc.1) ↔ tc.1 ∈ s.chal.map Prod.fst := by
    simp only [List.mem_map]
  simp only [genCollChOf]
  by_cases h : tc.1 ∈ s.chal.map Prod.fst
  · rw [dite_eq_left_of_eq_true (eq_true h), ite_eq_left_of_eq_true _ _ (eq_true (hiff.2 h))]
  · rw [dite_eq_right_of_eq_false (eq_false h),
      ite_eq_right_of_eq_false _ _ (eq_false fun h' ↦ h (hiff.1 h'))]
    simp [GenCollState.tweaks]

/-! ### Locality -/

/-- The targets of a history, as a partial function of the tweak, in the message type
`Msg ⊕ C` of the random function. -/
def genCollTargets (s : GenCollState Tw Msg Cq) : Tw → Option (Msg ⊕ C) :=
  fun t ↦ ((s.chal.find? fun e ↦ decide (e.1 = t)).map Prod.snd).map Sum.inl

theorem genCollTargets_of_mem (s : GenCollState Tw Msg Cq) {t : Tw} {m : Msg}
    (h : (t, m) ∈ s.chal) : genCollTargets (C := C) s t = some (Sum.inl m) := by
  unfold genCollTargets
  rw [find_of_mem s.nodup h]
  rfl

/-- A tweak with a target occurs in the challenge history. -/
theorem genColl_mem_of_targets (s : GenCollState Tw Msg Cq) {t : Tw} {m : Msg ⊕ C}
    (h : genCollTargets s t = some m) : t ∈ s.chal.map Prod.fst := by
  unfold genCollTargets at h
  cases hf : s.chal.find? fun e ↦ decide (e.1 = t) with
  | none => rw [hf] at h; simp at h
  | some e =>
    have h1 := List.find?_some hf
    have h2 := List.mem_of_find?_eq_some hf
    exact List.mem_map.2 ⟨e, h2, by simpa using h1⟩

/-- `t` extends `s`: both histories of `s` are prefixes of those of `t`. -/
def GenCollState.Ext (s t : GenCollState Tw Msg Cq) : Prop :=
  s.chal <+: t.chal ∧ s.coll <+: t.coll

/-- The points of the row recorded by the histories `t`: the targets (in the attacked member)
and the accepted collection queries. -/
def genCollSeen (κ : Cq → Msg ⊕ C) (t : GenCollState Tw Msg Cq) (z : Tw × (Msg ⊕ C)) : Prop :=
  (∃ p ∈ t.chal, (p.1, Sum.inl p.2) = z) ∨ (∃ p ∈ t.coll, (p.1, κ p.2) = z)

/-- Every step of the challenger extends the histories. -/
theorem genCollChOf_ext (κ : Cq → Msg ⊕ C) (cap : ℕ) (a : Tw × (Msg ⊕ C) → Y)
    (req : (Tw × Msg) ⊕ (Tw × Cq)) (s t : GenCollState Tw Msg Cq)
    (h : (genCollChOf κ cap a req s).2.Ext t) : s.Ext t := by
  cases req with
  | inl tm =>
    simp only [genCollChOf] at h
    split_ifs at h with hc
    · exact h
    · exact ⟨(List.prefix_append _ _).trans h.1, h.2⟩
  | inr tm =>
    simp only [genCollChOf] at h
    split_ifs at h with hc
    · exact h
    · exact ⟨h.1, (List.prefix_append _ _).trans h.2⟩

/-- Two rows that agree on the recorded points of the histories `t` are answered in the same
way, except after requests that make `t` unreachable. -/
theorem genCollChOf_loc (κ : Cq → Msg ⊕ C) (cap : ℕ) (a a' : Tw × (Msg ⊕ C) → Y)
    (t : GenCollState Tw Msg Cq) (haa : ∀ z, genCollSeen κ t z → a z = a' z)
    (req : (Tw × Msg) ⊕ (Tw × Cq)) (s : GenCollState Tw Msg Cq) :
    genCollChOf κ cap a req s = genCollChOf κ cap a' req s ∨
      (¬ (genCollChOf κ cap a req s).2.Ext t ∧ ¬ (genCollChOf κ cap a' req s).2.Ext t) := by
  cases req with
  | inl tm =>
    simp only [genCollChOf]
    split_ifs with hc
    · exact Or.inl rfl
    · by_cases he : a (tm.1, Sum.inl tm.2) = a' (tm.1, Sum.inl tm.2)
      · left
        rw [he]
      · right
        have hn : ¬ (s.chal ++ [tm]) <+: t.chal := fun hp ↦
          he (haa _ (Or.inl ⟨tm, hp.subset (by simp), rfl⟩))
        exact ⟨fun h ↦ hn h.1, fun h ↦ hn h.1⟩
  | inr tc =>
    simp only [genCollChOf]
    split_ifs with hc
    · exact Or.inl rfl
    · by_cases he : a (tc.1, κ tc.2) = a' (tc.1, κ tc.2)
      · left
        rw [he]
      · right
        have hn : ¬ (s.coll ++ [tc]) <+: t.coll := fun hp ↦
          he (haa _ (Or.inr ⟨tc, hp.subset (by simp), rfl⟩))
        exact ⟨fun h ↦ hn h.2, fun h ↦ hn h.2⟩

end Challenger

/-! ## The experiment -/

section Exp

variable [Fintype Sd] [DecidableEq Sd] [Fintype Tw] [DecidableEq Tw] [Fintype Msg]
  [DecidableEq Msg] [Fintype C] [DecidableEq C] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
  {L : LocalSig.{u, v}} {Out : QReg → Type w} {A : QReg}

/-- **The exact SM-DT-TCR experiment in the QROM with a collection**, general form (target cap
`cap`, collection queries `c : Cq` naming the point `κ c` of the row): the probability, over the
uniform seed `P`, the uniform function `Th : Sd × (Tw × (Msg ⊕ C)) → Y` and the run, that the
two-phase quantum adversary `(x, ph2)` started on `ρ` wins. -/
noncomputable def genCollTcrExpOf (κ : Cq → Msg ⊕ C) (I : L.Interp) (ρ : SubState A)
    (cap n : ℕ)
    (x : IAdv L (qrom2Spec (Dom Sd Tw (Msg ⊕ C)) Y) ((Tw × Msg) ⊕ (Tw × Cq)) (Option Y) Out n A)
    (ph2 : Sd → ∀ u, Out u →
      QuantumComp L (qrom2Spec (Dom Sd Tw (Msg ⊕ C)) Y) (fun _ ↦ ℕ × Msg) u) : ℝ≥0∞ :=
  twoPhaseExp I ρ (genCollChOf κ cap) genCollInit n x ph2 genCollWin

open Classical in
/-- What the leaf with histories `t` has seen of the row `R`: its values at the recorded
points (and `0` elsewhere). -/
noncomputable def genCollSeenOf (κ : Cq → Msg ⊕ C) (t : GenCollState Tw Msg Cq)
    (R : Tw × (Msg ⊕ C) → Y) : Tw × (Msg ⊕ C) → Y :=
  fun z ↦ if genCollSeen κ t z then R z else 0

/-- Changing the row at a non-target point of a target tweak is not seen. -/
theorem genCollSeenOf_update (κ : Cq → Msg ⊕ C) (t : GenCollState Tw Msg Cq)
    (k : Tw × (Msg ⊕ C)) (m : Msg ⊕ C) (hc : genCollTargets t k.1 = some m) (hk : k.2 ≠ m)
    (R : Tw × (Msg ⊕ C) → Y) (v : Y) :
    genCollSeenOf κ t (Function.update R k v) = genCollSeenOf κ t R := by
  funext z
  unfold genCollSeenOf
  split_ifs with h
  · refine Function.update_of_ne (fun heq ↦ ?_) _ _
    subst heq
    rcases h with ⟨p, hp, hz⟩ | ⟨p, hp, hz⟩
    · subst hz
      have h1 := genCollTargets_of_mem (C := C) t (t := p.1) (m := p.2) hp
      exact hk (Option.some.inj (h1.symm.trans hc))
    · subst hz
      exact t.disj p hp (genColl_mem_of_targets t hc)
  · rfl

/-- **Locality of the classical oracles.** The post-state of a leaf of phase 1 with histories
`t` only depends on the values of the row at the recorded points of `t`. -/
theorem genColl_branch_congr (κ : Cq → Msg ⊕ C)
    (R : QuantumRuntime (qrom2Spec (Dom Sd Tw (Msg ⊕ C)) Y)) (I : L.Interp) (cap n : ℕ)
    (x : IAdv L (qrom2Spec (Dom Sd Tw (Msg ⊕ C)) Y) ((Tw × Msg) ⊕ (Tw × Cq)) (Option Y) Out n A)
    (a a' : Tw × (Msg ⊕ C) → Y) (u : QReg) (o : Out u) (t : GenCollState Tw Msg Cq)
    (haa : ∀ z, genCollSeen κ t z → a z = a' z) :
    (R.run I (phase1 (genCollChOf κ cap a) genCollInit n x)).branch ⟨u, (o, t)⟩ =
      (R.run I (phase1 (genCollChOf κ cap a') genCollInit n x)).branch ⟨u, (o, t)⟩ :=
  flat_branch_congr R I (genCollChOf κ cap a) (genCollChOf κ cap a') GenCollState.Ext
    (fun _ ↦ ⟨List.prefix_refl _, List.prefix_refl _⟩)
    (fun req s t ↦ genCollChOf_ext κ cap a req s t)
    (fun req s t ↦ genCollChOf_ext κ cap a' req s t) t (genCollChOf_loc κ cap a a' t haa) n
    genCollInit x u o

variable {κ : Cq → Msg ⊕ C} {I : L.Interp} {ρ : SubState A} {cap n q₁ q₂ : ℕ}
  {x : IAdv L (qrom2Spec (Dom Sd Tw (Msg ⊕ C)) Y) ((Tw × Msg) ⊕ (Tw × Cq)) (Option Y) Out n A}
  {ph2 : Sd → ∀ u, Out u →
    QuantumComp L (qrom2Spec (Dom Sd Tw (Msg ⊕ C)) Y) (fun _ ↦ ℕ × Msg) u}

theorem genColl_postOf_eq_seen (F : Dom Sd Tw (Msg ⊕ C) → Y) (R : Tw × (Msg ⊕ C) → Y)
    (p : Σ u, Out u × GenCollState Tw Msg Cq) :
    postOf I ρ (genCollChOf κ cap) genCollInit n x F R p =
      postOf I ρ (genCollChOf κ cap) genCollInit n x F (genCollSeenOf κ p.2.2 R) p := by
  obtain ⟨u, o, t⟩ := p
  unfold postOf
  rw [genColl_branch_congr κ (twoRuntime fun _ ↦ F) I cap n x R (genCollSeenOf κ t R) u o t
    fun z hz ↦ by simp [genCollSeenOf, hz]]

/-- **The collision step.** In the hybrid game, where the row of the random function at the
seed is independent of what phase 1 saw except for the answers of the classical oracles, the
adversary wins with probability at most `(2 q₂ + 1)² / |Y|`. -/
theorem genColl_twoPhaseHyb_le [Inhabited Tw]
    (hx : IAdv.IsQueryBound n x (firstBudget q₁))
    (h2 : ∀ P u o, (ph2 P u o).IsQueryBound (secondBudget q₂)) :
    twoPhaseHyb I ρ (genCollChOf κ cap) genCollInit n x ph2 genCollWin ≤
      (2 * (q₂ : ℝ≥0∞) + 1) ^ 2 / (Fintype.card Y : ℝ≥0∞) := by
  refine twoPhaseHyb_le_of_leaf hx fun P F p ↦ ?_
  let τ : (Tw × (Msg ⊕ C) → Y) → Matrix (p.1 × Unit) (p.1 × Unit) ℂ :=
    fun a ↦ postOf I ρ (genCollChOf κ cap) genCollInit n x F a p
  have hτ : ∀ a, (τ a).PosSemidef := fun a ↦ postOf_posSemidef F a p
  let M : (Tw × (Msg ⊕ C) → Y) → HybridModel (Dom Sd Tw (Msg ⊕ C)) Y (ℕ × Msg) q₂ := fun a ↦
    HybridModel.ofSecondPort I F (ph2 P p.1 p.2.1) (τ a) (hτ a) q₂ (h2 P p.1 p.2.1) Sigma.snd
  let out : (Tw × (Msg ⊕ C) → Y) → ℕ × Msg → Tw × (Msg ⊕ C) := fun _ l ↦
    (((p.2.2.chal[l.1]?).map Prod.fst).getD default, Sum.inl l.2)
  have hpost : ∀ R : Tw × (Msg ⊕ C) → Y,
      postOf I ρ (genCollChOf κ cap) genCollInit n x F R p = τ (genCollSeenOf κ p.2.2 R) :=
    fun R ↦ genColl_postOf_eq_seen F R p
  have h := spr_embedded_obs_weighted_le (rowEmb P) F (genCollTargets p.2.2)
    (genCollSeenOf κ p.2.2)
    (fun k m hc hk R v ↦ genCollSeenOf_update κ p.2.2 k m hc hk R v) M out
    fun a ↦ ENNReal.ofReal (τ a).trace.re
  refine le_trans (avg_mono fun R ↦ ?_) (le_trans h (le_of_eq ?_))
  · rw [HybridModel.ofSecondPort_prob, hpost R, ← patchRow_eq_patch]
    refine leafProb_mono _ _ fun l hl ↦ ?_
    obtain ⟨t, mj, hget, hne, heq⟩ := hl
    have hmem : (t, mj) ∈ p.2.2.chal := List.mem_of_getElem? hget
    refine ⟨Sum.inl mj, ?_, ?_, ?_⟩
    · simp only [out, hget, Option.map_some, Option.getD_some]
      exact genCollTargets_of_mem p.2.2 hmem
    · simp only [out]
      exact fun h ↦ hne (Sum.inl.inj h)
    · simp only [out, hget, Option.map_some, Option.getD_some]
      exact heq
  · congr 1
    exact Finset.sum_congr rfl fun R _ ↦ by beta_reduce; rw [hpost R]

/-- General form, square-root form:
`√Pr[win] ≤ √((2 q₂ + 1)² / |Y|) + 2 q₁ / √|Sd|`. -/
theorem gen_coll_tcr_exact_of_sqrt_le [Inhabited Tw]
    (hx : IAdv.IsQueryBound n x (firstBudget q₁))
    (h2 : ∀ P u o, (ph2 P u o).IsQueryBound (secondBudget q₂)) :
    genCollTcrExpOf κ I ρ cap n x ph2 ^ (2⁻¹ : ℝ) ≤
      ((2 * (q₂ : ℝ≥0∞) + 1) ^ 2 / (Fintype.card Y : ℝ≥0∞)) ^ (2⁻¹ : ℝ) +
        2 * q₁ * ((Fintype.card Sd : ℝ≥0∞)⁻¹) ^ (2⁻¹ : ℝ) :=
  (seed_hiding hx h2).trans
    (add_le_add (sqrt_le_sqrt (genColl_twoPhaseHyb_le hx h2)) le_rfl)

/-- General form: `Pr[win] ≤ (√((2 q₂ + 1)² / |Y|) + 2 q₁ / √|Sd|)²`, for every map `κ` from
collection queries to points of the row. -/
theorem gen_coll_tcr_exact_of_le [Inhabited Tw]
    (hx : IAdv.IsQueryBound n x (firstBudget q₁))
    (h2 : ∀ P u o, (ph2 P u o).IsQueryBound (secondBudget q₂)) :
    genCollTcrExpOf κ I ρ cap n x ph2 ≤
      (((2 * (q₂ : ℝ≥0∞) + 1) ^ 2 / (Fintype.card Y : ℝ≥0∞)) ^ (2⁻¹ : ℝ) +
        2 * q₁ * ((Fintype.card Sd : ℝ≥0∞)⁻¹) ^ (2⁻¹ : ℝ)) ^ 2 := by
  have h := gen_coll_tcr_exact_of_sqrt_le (κ := κ) (I := I) (ρ := ρ) (cap := cap) hx h2
  calc genCollTcrExpOf κ I ρ cap n x ph2
      = (genCollTcrExpOf κ I ρ cap n x ph2 ^ (2⁻¹ : ℝ)) ^ 2 := (sq_sqrt _).symm
    _ ≤ _ := pow_le_pow_left' h 2

/-- The experiment is a probability. -/
theorem genCollTcrExpOf_le_one : genCollTcrExpOf κ I ρ cap n x ph2 ≤ 1 :=
  twoPhaseExp_le_one

end Exp

/-! ## VCVio's game: an indexed collection of further random functions -/

section Indexed

variable {ι : Type} {MsgC : ι → Type}

/-- The challenger of VCVio's SM-DT-TCR game for a collection indexed by `ι` with message types
`MsgC`: collection requests are `(t, ⟨i, m⟩)` with `m : MsgC i`, answered with the member `i`
of the collection, `a (t, .inr ⟨i, m⟩)`. -/
def genCollCh [DecidableEq Tw] (cap : ℕ) (a : Tw × (Msg ⊕ (Σ i, MsgC i)) → Y) :
    (Tw × Msg) ⊕ (Tw × (Σ i, MsgC i)) → GenCollState Tw Msg (Σ i, MsgC i) →
      Option Y × GenCollState Tw Msg (Σ i, MsgC i) :=
  genCollChOf Sum.inr cap a

/-- With the empty collection (`ι = Empty`: the stand-alone game) there is no collection
request. -/
theorem genColl_isEmpty_collReq (Tw : Type) (MsgC : Empty → Type) :
    IsEmpty (Tw × (Σ i, MsgC i)) :=
  ⟨fun q ↦ q.2.1.elim⟩

variable [Fintype Sd] [DecidableEq Sd] [Fintype Tw] [DecidableEq Tw] [Fintype Msg]
  [DecidableEq Msg] [Fintype ι] [DecidableEq ι] [∀ i, Fintype (MsgC i)]
  [∀ i, DecidableEq (MsgC i)] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
  {L : LocalSig.{u, v}} {Out : QReg → Type w} {A : QReg}

/-- **The exact SM-DT-TCR experiment in the QROM, with a collection of further independent
random functions** (indexed by `ι`, message types `MsgC`, target cap `cap`): the probability,
over the uniform seed `P`, the uniform function `Th : Sd × (Tw × (Msg ⊕ Σ i, MsgC i)) → Y`
(attacked member `Th (P, (t, .inl m))`, collection members `Th (P, (t, .inr ⟨i, m⟩))`) and the
run, that the two-phase quantum adversary `(x, ph2)` started on `ρ` wins. -/
noncomputable def genCollTcrExp (I : L.Interp) (ρ : SubState A) (cap n : ℕ)
    (x : IAdv L (qrom2Spec (Dom Sd Tw (Msg ⊕ (Σ i, MsgC i))) Y)
      ((Tw × Msg) ⊕ (Tw × (Σ i, MsgC i))) (Option Y) Out n A)
    (ph2 : Sd → ∀ u, Out u →
      QuantumComp L (qrom2Spec (Dom Sd Tw (Msg ⊕ (Σ i, MsgC i))) Y) (fun _ ↦ ℕ × Msg) u) :
    ℝ≥0∞ :=
  twoPhaseExp I ρ (genCollCh cap) genCollInit n x ph2 genCollWin

variable {I : L.Interp} {ρ : SubState A} {cap n q₁ q₂ : ℕ}
  {x : IAdv L (qrom2Spec (Dom Sd Tw (Msg ⊕ (Σ i, MsgC i))) Y)
    ((Tw × Msg) ⊕ (Tw × (Σ i, MsgC i))) (Option Y) Out n A}
  {ph2 : Sd → ∀ u, Out u →
    QuantumComp L (qrom2Spec (Dom Sd Tw (Msg ⊕ (Σ i, MsgC i))) Y) (fun _ ↦ ℕ × Msg) u}

theorem genCollTcrExp_eq :
    genCollTcrExp I ρ cap n x ph2 = genCollTcrExpOf Sum.inr I ρ cap n x ph2 :=
  rfl

/-- **SM-DT-TCR with a collection in the QROM, exact adaptive two-phase game**, square-root
form: `√Pr[win] ≤ √((2 q₂ + 1)² / |Y|) + 2 q₁ / √|Sd|`. -/
theorem gen_coll_tcr_exact_sqrt_le [Inhabited Tw]
    (hx : IAdv.IsQueryBound n x (firstBudget q₁))
    (h2 : ∀ P u o, (ph2 P u o).IsQueryBound (secondBudget q₂)) :
    genCollTcrExp I ρ cap n x ph2 ^ (2⁻¹ : ℝ) ≤
      ((2 * (q₂ : ℝ≥0∞) + 1) ^ 2 / (Fintype.card Y : ℝ≥0∞)) ^ (2⁻¹ : ℝ) +
        2 * q₁ * ((Fintype.card Sd : ℝ≥0∞)⁻¹) ^ (2⁻¹ : ℝ) :=
  gen_coll_tcr_exact_of_sqrt_le (κ := Sum.inr) hx h2

/-- **SM-DT-TCR with a collection in the QROM, exact adaptive two-phase game**:
`Pr[win] ≤ (√((2 q₂ + 1)² / |Y|) + 2 q₁ / √|Sd|)²`, for every two-phase quantum adversary with
at most `q₁` queries before and `q₂` queries after the seed is revealed, any number of
adaptively chosen targets, any collection and any number of collection queries. -/
theorem gen_coll_tcr_exact_le [Inhabited Tw]
    (hx : IAdv.IsQueryBound n x (firstBudget q₁))
    (h2 : ∀ P u o, (ph2 P u o).IsQueryBound (secondBudget q₂)) :
    genCollTcrExp I ρ cap n x ph2 ≤
      (((2 * (q₂ : ℝ≥0∞) + 1) ^ 2 / (Fintype.card Y : ℝ≥0∞)) ^ (2⁻¹ : ℝ) +
        2 * q₁ * ((Fintype.card Sd : ℝ≥0∞)⁻¹) ^ (2⁻¹ : ℝ)) ^ 2 :=
  gen_coll_tcr_exact_of_le (κ := Sum.inr) hx h2

/-- The experiment is a probability. -/
theorem genCollTcrExp_le_one : genCollTcrExp I ρ cap n x ph2 ≤ 1 :=
  twoPhaseExp_le_one

end Indexed

/-! ## The stand-alone game: the empty collection -/

section Standalone

variable {MsgC : Empty → Type}
  [Fintype Sd] [DecidableEq Sd] [Fintype Tw] [DecidableEq Tw] [Fintype Msg]
  [DecidableEq Msg] [∀ i, Fintype (MsgC i)] [∀ i, DecidableEq (MsgC i)]
  [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
  {L : LocalSig.{u, v}} {Out : QReg → Type w} {A : QReg}
  {I : L.Interp} {ρ : SubState A} {cap n q₁ q₂ : ℕ}
  {x : IAdv L (qrom2Spec (Dom Sd Tw (Msg ⊕ (Σ i, MsgC i))) Y)
    ((Tw × Msg) ⊕ (Tw × (Σ i, MsgC i))) (Option Y) Out n A}
  {ph2 : Sd → ∀ u, Out u →
    QuantumComp L (qrom2Spec (Dom Sd Tw (Msg ⊕ (Σ i, MsgC i))) Y) (fun _ ↦ ℕ × Msg) u}

/-- **Stand-alone SM-DT-TCR** (`ι = Empty`: no collection request exists,
`genColl_isEmpty_collReq`): the same bound. -/
theorem gen_coll_tcr_exact_standalone_le [Inhabited Tw]
    (hx : IAdv.IsQueryBound n x (firstBudget q₁))
    (h2 : ∀ P u o, (ph2 P u o).IsQueryBound (secondBudget q₂)) :
    genCollTcrExp I ρ cap n x ph2 ≤
      (((2 * (q₂ : ℝ≥0∞) + 1) ^ 2 / (Fintype.card Y : ℝ≥0∞)) ^ (2⁻¹ : ℝ) +
        2 * q₁ * ((Fintype.card Sd : ℝ≥0∞)⁻¹) ^ (2⁻¹ : ℝ)) ^ 2 :=
  gen_coll_tcr_exact_le hx h2

end Standalone

/-! ## The attacked member inside the collection (`TweakableHashCollection.cons`) -/

section Cons

variable {ι : Type} {MsgC : ι → Type}

/-- The message types of the collection extended with the attacked member at index `none`
(`TweakableHashCollection.cons`). -/
def genCollConsMsg (Msg : Type) (MsgC : ι → Type) : Option ι → Type
  | none => Msg
  | some i => MsgC i

/-- The point of the row named by a query to the extended collection: index `none` is the
attacked member, index `some i` the member `i` of the collection. -/
def genCollConsEmb : (Σ o, genCollConsMsg Msg MsgC o) → Msg ⊕ (Σ i, MsgC i)
  | ⟨none, m⟩ => Sum.inl m
  | ⟨some i, m⟩ => Sum.inr ⟨i, m⟩

@[simp] theorem genCollConsEmb_none (m : Msg) :
    genCollConsEmb (MsgC := MsgC) ⟨none, m⟩ = Sum.inl m := rfl

@[simp] theorem genCollConsEmb_some (i : ι) (m : MsgC i) :
    genCollConsEmb (Msg := Msg) (MsgC := MsgC) ⟨some i, m⟩ = Sum.inr ⟨i, m⟩ := rfl

/-- Every point of the row, in the attacked member or in the collection, is named by a query to
the extended collection. -/
theorem genCollConsEmb_bijective :
    Function.Bijective (genCollConsEmb (Msg := Msg) (MsgC := MsgC)) := by
  constructor
  · rintro ⟨_ | i, m⟩ ⟨_ | j, m'⟩ h
    · exact congrArg _ (Sum.inl.inj h)
    · exact absurd h (by simp [genCollConsEmb])
    · exact absurd h (by simp [genCollConsEmb])
    · have h' := Sum.inr.inj h
      cases h'
      rfl
  · rintro (m | ⟨i, m⟩)
    · exact ⟨⟨none, m⟩, rfl⟩
    · exact ⟨⟨some i, m⟩, rfl⟩

/-- The challenger of the game whose collection contains the attacked member: a collection
request `(t, ⟨none, m⟩)` is answered with the attacked function `a (t, .inl m)` (if `t` is not
a target tweak), a request `(t, ⟨some i, m⟩)` with the member `i`. -/
def genCollConsCh [DecidableEq Tw] (cap : ℕ) (a : Tw × (Msg ⊕ (Σ i, MsgC i)) → Y) :
    (Tw × Msg) ⊕ (Tw × (Σ o, genCollConsMsg Msg MsgC o)) →
      GenCollState Tw Msg (Σ o, genCollConsMsg Msg MsgC o) →
      Option Y × GenCollState Tw Msg (Σ o, genCollConsMsg Msg MsgC o) :=
  genCollChOf genCollConsEmb cap a

variable [Fintype Sd] [DecidableEq Sd] [Fintype Tw] [DecidableEq Tw] [Fintype Msg]
  [DecidableEq Msg] [Fintype ι] [DecidableEq ι] [∀ i, Fintype (MsgC i)]
  [∀ i, DecidableEq (MsgC i)] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
  {L : LocalSig.{u, v}} {Out : QReg → Type w} {A : QReg}

/-- The exact SM-DT-TCR experiment in the QROM whose collection is the family `MsgC` of further
random functions extended with the attacked function itself. -/
noncomputable def genCollConsTcrExp (I : L.Interp) (ρ : SubState A) (cap n : ℕ)
    (x : IAdv L (qrom2Spec (Dom Sd Tw (Msg ⊕ (Σ i, MsgC i))) Y)
      ((Tw × Msg) ⊕ (Tw × (Σ o, genCollConsMsg Msg MsgC o))) (Option Y) Out n A)
    (ph2 : Sd → ∀ u, Out u →
      QuantumComp L (qrom2Spec (Dom Sd Tw (Msg ⊕ (Σ i, MsgC i))) Y) (fun _ ↦ ℕ × Msg) u) :
    ℝ≥0∞ :=
  twoPhaseExp I ρ (genCollConsCh cap) genCollInit n x ph2 genCollWin

variable {I : L.Interp} {ρ : SubState A} {cap n q₁ q₂ : ℕ}
  {x : IAdv L (qrom2Spec (Dom Sd Tw (Msg ⊕ (Σ i, MsgC i))) Y)
    ((Tw × Msg) ⊕ (Tw × (Σ o, genCollConsMsg Msg MsgC o))) (Option Y) Out n A}
  {ph2 : Sd → ∀ u, Out u →
    QuantumComp L (qrom2Spec (Dom Sd Tw (Msg ⊕ (Σ i, MsgC i))) Y) (fun _ ↦ ℕ × Msg) u}

/-- Square-root form of `gen_coll_cons_tcr_exact_le`. -/
theorem gen_coll_cons_tcr_exact_sqrt_le [Inhabited Tw]
    (hx : IAdv.IsQueryBound n x (firstBudget q₁))
    (h2 : ∀ P u o, (ph2 P u o).IsQueryBound (secondBudget q₂)) :
    genCollConsTcrExp I ρ cap n x ph2 ^ (2⁻¹ : ℝ) ≤
      ((2 * (q₂ : ℝ≥0∞) + 1) ^ 2 / (Fintype.card Y : ℝ≥0∞)) ^ (2⁻¹ : ℝ) +
        2 * q₁ * ((Fintype.card Sd : ℝ≥0∞)⁻¹) ^ (2⁻¹ : ℝ) :=
  gen_coll_tcr_exact_of_sqrt_le (κ := genCollConsEmb) hx h2

/-- **SM-DT-TCR in the QROM with the attacked member in its own collection**
(`TweakableHashCollection.cons`, HK22's `Th_m ∈ Th_λ`): the same bound. -/
theorem gen_coll_cons_tcr_exact_le [Inhabited Tw]
    (hx : IAdv.IsQueryBound n x (firstBudget q₁))
    (h2 : ∀ P u o, (ph2 P u o).IsQueryBound (secondBudget q₂)) :
    genCollConsTcrExp I ρ cap n x ph2 ≤
      (((2 * (q₂ : ℝ≥0∞) + 1) ^ 2 / (Fintype.card Y : ℝ≥0∞)) ^ (2⁻¹ : ℝ) +
        2 * q₁ * ((Fintype.card Sd : ℝ≥0∞)⁻¹) ^ (2⁻¹ : ℝ)) ^ 2 :=
  gen_coll_tcr_exact_of_le (κ := genCollConsEmb) hx h2

/-- The experiment is a probability. -/
theorem genCollConsTcrExp_le_one : genCollConsTcrExp I ρ cap n x ph2 ≤ 1 :=
  twoPhaseExp_le_one

end Cons

end PQ.QROM

#print axioms PQ.QROM.genColl_twoPhaseHyb_le
#print axioms PQ.QROM.gen_coll_tcr_exact_of_sqrt_le
#print axioms PQ.QROM.gen_coll_tcr_exact_of_le
#print axioms PQ.QROM.genCollTcrExpOf_le_one
#print axioms PQ.QROM.gen_coll_tcr_exact_sqrt_le
#print axioms PQ.QROM.gen_coll_tcr_exact_le
#print axioms PQ.QROM.genCollTcrExp_le_one
#print axioms PQ.QROM.gen_coll_tcr_exact_standalone_le
#print axioms PQ.QROM.gen_coll_cons_tcr_exact_sqrt_le
#print axioms PQ.QROM.gen_coll_cons_tcr_exact_le
#print axioms PQ.QROM.genCollConsTcrExp_le_one
