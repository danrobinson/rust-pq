/-
Work package OPEN, O9: the second phase of the answer-storing class adversary `bTcrArA n A` as an
open program, and its hash count.

* `storeForgeOpen A L S pk = simulateQ (memoImpl pk S) (memoForgeOpen A L pk)`: the open program
  of `bTcrArM`'s second phase with every `Thash` query at the seed `pk` first looked up in the
  store `S` — a hit is answered WITHOUT a query, a miss is a hash query.  `H_msg` is a query.
* `bTcrArA_forge_open`: for EVERY state `(tbl, (L, S))` (sound or not) the second phase of
  `bTcrArA n A` is the `tblImpl` interpretation of `storeForgeOpen A L S pk`, then `classOut`.
* Counting.  A lookup-with-fallback program has no hash bound that holds for arbitrary oracle
  answers (with wrong answers the simulation asks for pairs that are not stored).  The count is
  therefore stated for the program with the secret reads and the hash answers PINNED to the real
  ones: `simulateQ (pinImpl tbl) P` reads secrets from `tbl` and still ISSUES every hash query of
  `P`, but continues with the real value `PublicHash.impl prims q` (`pinImpl_tbl`: same
  interpretation).  `storeForgeOpen_hashes_of_cover`: on a sound store that contains the entries
  of `L`, IF the pinned key generation makes no hash query outside the store (`hKeygen`) and each
  pinned signature at most one (`hSign`; the `H_msg`), then the pinned second phase makes at
  most `qs + (1 + verifyHashes vp)` hash queries.  `hKeygen`, `hSign` are proved in
  `Reduction/Open/TcrStoreCover.lean`.
-/
import Reduction.Open.TcrStore

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal

namespace Reduction
namespace Open

open TweakableHash

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- Close a goal `a = b` by `Eq.refl a`, the definitional equality being checked by the kernel
only (the elaborator's unifier does not unfold stuck `match` auxiliaries whose parameters differ,
here `prims` vs `withTH prims T H`).  No axiom is involved. -/
elab "o9_kernel_rfl" : tactic => Lean.Elab.Tactic.withMainContext do
  let g ← Lean.Elab.Tactic.getMainGoal
  let t ← Lean.instantiateMVars (← g.getType)
  let some (_, a, _) := t.eq? | throwError "o9_kernel_rfl: not an equality"
  let pf ← Lean.Meta.mkEqRefl a
  g.assign pf
  Lean.Elab.Tactic.replaceMainGoal []

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]
variable {optRand : PublicKeyCore prims.core → ProbComp prims.Y}
  {pkSeedDist : ProbComp prims.PkSeed}
variable {ι : Type} {gspec : OracleSpec ι}

attribute [local irreducible] arityTargets tcrTargets
attribute [local instance] Lazy.openQ Lazy.closedQ

/-! ## The open second-phase program -/

/-- **The lookup handler.**  A `Thash` query at the seed `pk` whose `(tweak, input)` is in the
store is answered by the stored value — no query; every other query is forwarded unchanged. -/
def memoImpl (pk : prims.PkSeed) (S : Store prims) :
    QueryImpl (Lazy.OSpec prims gspec) (OracleComp (Lazy.OSpec prims gspec))
  | .inl n => liftM ((Lazy.OSpec prims gspec).query (.inl n))
  | .inr (.inl t) => liftM ((Lazy.OSpec prims gspec).query (.inr (.inl t)))
  | .inr (.inr (.inl i)) => liftM ((Lazy.OSpec prims gspec).query (.inr (.inr (.inl i))))
  | .inr (.inr (.inr (.hmsg r pk' root m))) =>
      liftM ((Lazy.OSpec prims gspec).query (.inr (.inr (.inr (.hmsg r pk' root m)))))
  | .inr (.inr (.inr (.thash pk' key xs))) =>
      if pk' = pk then
        match S.lookup (key, xs) with
        | some y => pure y
        | none => liftM ((Lazy.OSpec prims gspec).query (.inr (.inr (.inr (.thash pk' key xs)))))
      else liftM ((Lazy.OSpec prims gspec).query (.inr (.inr (.inr (.thash pk' key xs)))))

/-- **Phase 2 of `bTcrArA n A` as an open program** (before the hash-free `classOut`): the open
program `memoForgeOpen A L pk` of `bTcrArM` (key generation, the forger's run with open signing,
`H_msg` of the forgery, verification of the forgery with the collision search) run through the
lookup handler: `Thash` evaluations found in the store `S` are not queries. -/
noncomputable def storeForgeOpen (A : Forger vp prims optRand pkSeedDist)
    (L : List (prims.AdrsKey × List prims.Y)) (S : Store prims) (pkSeed : prims.PkSeed) :
    OracleComp (Lazy.OSpec prims gspec) (ℕ × List prims.Y) :=
  simulateQ (memoImpl (gspec := gspec) pkSeed S) (Resources2.memoForgeOpen (gspec := gspec) A L pkSeed)

/-- The table interpretation after the lookup handler is the table interpretation with the hash
oracle `lkT pk S` (lookup, hash on a miss). -/
theorem tbl_memoImpl (tbl : SecretTable vp prims) (pk : prims.PkSeed) (S : Store prims)
    (t : (Lazy.OSpec prims gspec).Domain) :
    simulateQ (Lazy.tblImpl (gspec := gspec) (PublicHash.impl prims) tbl)
        (memoImpl (gspec := gspec) pk S t) =
      Lazy.tblImpl (gspec := gspec) (PublicHash.impl (withTH prims (lkT pk S) prims.Hmsg)) tbl t := by
  rcases t with n | t | i | q
  · simp only [memoImpl, simulateQ_spec_query]; rfl
  · simp only [memoImpl, simulateQ_spec_query]; rfl
  · simp only [memoImpl, simulateQ_spec_query]; rfl
  · cases q with
    | hmsg r pk' root m => simp only [memoImpl, simulateQ_spec_query]; rfl
    | thash pk' key xs =>
      show _ = pure (lkT pk S pk' key xs)
      unfold lkT
      by_cases hpk : pk' = pk
      · subst hpk
        simp only [memoImpl, ↓reduceIte]
        cases S.lookup (key, xs) with
        | none => simp only [simulateQ_spec_query]; rfl
        | some y => simp only [simulateQ_pure]
      · simp only [memoImpl, hpk, ↓reduceIte, simulateQ_spec_query]; rfl

theorem tbl_memoImpl_simulateQ {α : Type} (tbl : SecretTable vp prims) (pk : prims.PkSeed)
    (S : Store prims) (P : OracleComp (Lazy.OSpec prims gspec) α) :
    simulateQ (Lazy.tblImpl (gspec := gspec) (PublicHash.impl prims) tbl)
        (simulateQ (memoImpl (gspec := gspec) pk S) P) =
      simulateQ (Lazy.tblImpl (gspec := gspec)
        (PublicHash.impl (withTH prims (lkT pk S) prims.Hmsg)) tbl) P :=
  QueryImpl.simulateQ_simulateQ_eq_of_apply (fun t => tbl_memoImpl tbl pk S t) P

/-- The open program of `bTcrArM`'s second phase and the output translation do not depend on the
hash functions (they are the same terms over `withTH prims T H`). -/
theorem memoForgeOpen_withTH' (T : prims.PkSeed → prims.AdrsKey → List prims.Y → prims.Y)
    (H : prims.Y → prims.PkSeed → prims.Y → List Byte → Bytes vp.params.m)
    (A : Forger vp prims optRand pkSeedDist) (L : List (prims.AdrsKey × List prims.Y))
    (pkSeed : prims.PkSeed) :
    Resources2.memoForgeOpen (gspec := gspec) (castForger T H A) L pkSeed =
      Resources2.memoForgeOpen (gspec := gspec) A L pkSeed := by
  o9_kernel_rfl

theorem classOut_withTH' (T : prims.PkSeed → prims.AdrsKey → List prims.Y → prims.Y)
    (H : prims.Y → prims.PkSeed → prims.Y → List Byte → Bytes vp.params.m) (n : ℕ)
    (L : List (prims.AdrsKey × List prims.Y)) (jm : ℕ × List prims.Y) :
    classOut (withTH prims T H) n L jm = classOut prims n L jm := by
  o9_kernel_rfl

/-- **Interpretation, every state.**  For every state `(tbl, (L, S))` — the store need not be
sound — and every game spec, phase 2 of `bTcrArA n A` is the table interpretation (secrets from
`tbl`, hash queries evaluated by `prims`) of the open program `storeForgeOpen A L S pk`,
followed by the hash-free output translation `classOut`. -/
theorem bTcrArA_forge_open (n : ℕ) (A : Forger vp prims optRand pkSeedDist)
    (tbl : SecretTable vp prims) (L : List (prims.AdrsKey × List prims.Y)) (S : Store prims)
    (pk : prims.PkSeed) :
    (liftM ((bTcrArA n A).forge (tbl, (L, S)) pk) : OracleComp (unifSpec + gspec) _) =
      simulateQ (Lazy.tblImpl (gspec := gspec) (PublicHash.impl prims) tbl)
        (storeForgeOpen (gspec := gspec) A L S pk) >>= fun jm => pure (classOut prims n L jm) := by
  have h := Resources2.bTcrArM_forge_open (gspec := gspec)
    (prims := withTH prims (lkT pk S) prims.Hmsg) n (castForger (lkT pk S) prims.Hmsg A) tbl L pk
  unfold storeForgeOpen
  rw [tbl_memoImpl_simulateQ, ← memoForgeOpen_withTH' (lkT pk S) prims.Hmsg A L pk]
  refine Eq.trans ?_ (h.trans ?_)
  · rfl
  · refine bind_congr fun jm => ?_
    rw [classOut_withTH']

/-! ## Pinned execution and the generic counting lemmas -/

/-- **Pinning.**  Secret reads are answered from `tbl` (no query); a hash query is still ISSUED
but the program continues with the real value `PublicHash.impl prims q`; uniform bits and game
queries are forwarded.  `simulateQ (pinImpl tbl) P` is the execution of `P` in which the two
deterministic oracles answer as in the actual adversary. -/
def pinImpl (tbl : SecretTable vp prims) :
    QueryImpl (Lazy.OSpec prims gspec) (OracleComp (Lazy.OSpec prims gspec))
  | .inl n => liftM ((Lazy.OSpec prims gspec).query (.inl n))
  | .inr (.inl t) => liftM ((Lazy.OSpec prims gspec).query (.inr (.inl t)))
  | .inr (.inr (.inl i)) => pure (tbl i)
  | .inr (.inr (.inr q)) =>
      liftM ((Lazy.OSpec prims gspec).query (.inr (.inr (.inr q)))) >>= fun _ =>
        pure (PublicHash.impl prims q)

/-- Pinning does not change the interpretation: the pinned program is the same adversary. -/
theorem pinImpl_tbl {α : Type} (tbl : SecretTable vp prims)
    (P : OracleComp (Lazy.OSpec prims gspec) α) :
    simulateQ (Lazy.tblImpl (gspec := gspec) (PublicHash.impl prims) tbl)
        (simulateQ (pinImpl (gspec := gspec) tbl) P) =
      simulateQ (Lazy.tblImpl (gspec := gspec) (PublicHash.impl prims) tbl) P :=
  QueryImpl.simulateQ_simulateQ_eq_of_apply (fun t => by
    rcases t with n | t | i | q
    · simp only [pinImpl, simulateQ_spec_query]
    · simp only [pinImpl, simulateQ_spec_query]
    · simp only [pinImpl, simulateQ_pure]; rfl
    · simp only [pinImpl, simulateQ_bind, simulateQ_spec_query, simulateQ_pure]
      show (pure (PublicHash.impl prims q) >>= fun _ => pure (PublicHash.impl prims q) :
        OracleComp (unifSpec + gspec) _) = pure (PublicHash.impl prims q)
      rw [pure_bind]) P

/-- Is the query a `Thash` query at the seed `pk` whose `(tweak, input)` is in the store? -/
def hitB (pk : prims.PkSeed) (S : Store prims) :
    ℕ ⊕ (ι ⊕ (SecIdx ⊕ PublicHashQuery prims.PkSeed prims.AdrsKey prims.Y)) → Bool
  | .inr (.inr (.inr (.thash pk' key xs))) => decide (pk' = pk) && (S.lookup (key, xs)).isSome
  | _ => false

/-- A hash query that is not found in the store ("non-hit": a miss or an `H_msg` query). -/
abbrev NH (pk : prims.PkSeed) (S : Store prims)
    (t : ℕ ⊕ (ι ⊕ (SecIdx ⊕ PublicHashQuery prims.PkSeed prims.AdrsKey prims.Y))) : Prop :=
  Lazy.kind t = .hash ∧ hitB pk S t = false

/-- Pinning never adds queries. -/
theorem pin_mono (tbl : SecretTable vp prims)
    (p : ℕ ⊕ (ι ⊕ (SecIdx ⊕ PublicHashQuery prims.PkSeed prims.AdrsKey prims.Y)) → Prop)
    [DecidablePred p] {α : Type} (P : OracleComp (Lazy.OSpec prims gspec) α) (n : ℕ)
    (h : IsQueryBoundP P p n) :
    IsQueryBoundP (simulateQ (pinImpl (gspec := gspec) tbl) P) p n := by
  induction P using OracleComp.inductionOn generalizing n with
  | pure a => simp
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at h
    rw [simulateQ_bind, simulateQ_spec_query]
    rcases t with m | t | i | q
    · show IsQueryBoundP (liftM ((Lazy.OSpec prims gspec).query (.inl m)) >>= _) p n
      rw [isQueryBoundP_query_bind_iff]
      exact ⟨h.1, fun u => ih u _ (h.2 u)⟩
    · show IsQueryBoundP (liftM ((Lazy.OSpec prims gspec).query (.inr (.inl t))) >>= _) p n
      rw [isQueryBoundP_query_bind_iff]
      exact ⟨h.1, fun u => ih u _ (h.2 u)⟩
    · show IsQueryBoundP (pure (tbl i) >>= _) p n
      rw [pure_bind]
      refine ih _ _ ((h.2 _).mono ?_)
      split_ifs <;> omega
    · show IsQueryBoundP ((liftM ((Lazy.OSpec prims gspec).query (.inr (.inr (.inr q)))) >>=
        fun _ => pure (PublicHash.impl prims q)) >>= _) p n
      rw [bind_assoc, isQueryBoundP_query_bind_iff]
      refine ⟨h.1, fun u => ?_⟩
      rw [pure_bind]
      exact ih _ _ (h.2 _)

/-- **Lookups remove exactly the hits.**  On a sound store: if the pinned program `P` makes at
most `n` hash queries that are not hits, then the pinned program `P` run through the lookup
handler makes at most `n` hash queries. -/
theorem pin_memo_bound (tbl : SecretTable vp prims) (pk : prims.PkSeed) (S : Store prims)
    (hS : Sound pk S) {α : Type} (P : OracleComp (Lazy.OSpec prims gspec) α) (n : ℕ)
    (h : IsQueryBoundP (simulateQ (pinImpl (gspec := gspec) tbl) P) (NH pk S) n) :
    IsQueryBoundP (simulateQ (pinImpl (gspec := gspec) tbl)
      (simulateQ (memoImpl (gspec := gspec) pk S) P)) (fun t => Lazy.kind t = .hash) n := by
  induction P using OracleComp.inductionOn generalizing n with
  | pure a => simp
  | query_bind t k ih =>
    rw [simulateQ_bind, simulateQ_spec_query] at h
    rw [simulateQ_bind, simulateQ_spec_query, simulateQ_bind]
    rcases t with m | t | i | q
    · have h' : IsQueryBoundP (liftM ((Lazy.OSpec prims gspec).query (.inl m)) >>= fun u =>
          simulateQ (pinImpl (gspec := gspec) tbl) (k u)) (NH pk S) n := h
      rw [isQueryBoundP_query_bind_iff] at h'
      show IsQueryBoundP (simulateQ (pinImpl (gspec := gspec) tbl)
        (liftM ((Lazy.OSpec prims gspec).query (.inl m))) >>= _) _ n
      rw [simulateQ_spec_query]
      show IsQueryBoundP (liftM ((Lazy.OSpec prims gspec).query (.inl m)) >>= _) _ n
      rw [isQueryBoundP_query_bind_iff]
      refine ⟨Or.inl (fun hk => Lazy.Kind.noConfusion hk), fun u => ?_⟩
      have h2 := h'.2 u
      rw [ite_eq_right (fun hk => Lazy.Kind.noConfusion hk.1)] at h2
      rw [ite_eq_right (fun hk => Lazy.Kind.noConfusion hk)]
      exact ih u n h2
    · have h' : IsQueryBoundP (liftM ((Lazy.OSpec prims gspec).query (.inr (.inl t))) >>= fun u =>
          simulateQ (pinImpl (gspec := gspec) tbl) (k u)) (NH pk S) n := h
      rw [isQueryBoundP_query_bind_iff] at h'
      show IsQueryBoundP (simulateQ (pinImpl (gspec := gspec) tbl)
        (liftM ((Lazy.OSpec prims gspec).query (.inr (.inl t)))) >>= _) _ n
      rw [simulateQ_spec_query]
      show IsQueryBoundP (liftM ((Lazy.OSpec prims gspec).query (.inr (.inl t))) >>= _) _ n
      rw [isQueryBoundP_query_bind_iff]
      refine ⟨Or.inl (fun hk => Lazy.Kind.noConfusion hk), fun u => ?_⟩
      have h2 := h'.2 u
      rw [ite_eq_right (fun hk => Lazy.Kind.noConfusion hk.1)] at h2
      rw [ite_eq_right (fun hk => Lazy.Kind.noConfusion hk)]
      exact ih u n h2
    · have h' : IsQueryBoundP (pure (tbl i) >>= fun u =>
          simulateQ (pinImpl (gspec := gspec) tbl) (k u)) (NH pk S) n := h
      rw [pure_bind] at h'
      show IsQueryBoundP (simulateQ (pinImpl (gspec := gspec) tbl)
        (liftM ((Lazy.OSpec prims gspec).query (.inr (.inr (.inl i))))) >>= _) _ n
      rw [simulateQ_spec_query]
      show IsQueryBoundP (pure (tbl i) >>= _) _ n
      rw [pure_bind]
      exact ih _ n h'
    · have h' : IsQueryBoundP ((liftM ((Lazy.OSpec prims gspec).query (.inr (.inr (.inr q)))) >>=
          fun _ => pure (PublicHash.impl prims q)) >>= fun u =>
          simulateQ (pinImpl (gspec := gspec) tbl) (k u)) (NH pk S) n := h
      rw [bind_assoc, isQueryBoundP_query_bind_iff] at h'
      have hcont : ∀ u, IsQueryBoundP (simulateQ (pinImpl (gspec := gspec) tbl)
          (k (PublicHash.impl prims q))) (NH pk S)
          (if NH (ι := ι) pk S (.inr (.inr (.inr q))) then n - 1 else n) := fun u => by
        have := h'.2 u
        rwa [pure_bind] at this
      -- the forwarded case: the lookup handler forwards `q`
      have hfwd : memoImpl (gspec := gspec) pk S (.inr (.inr (.inr q))) =
            liftM ((Lazy.OSpec prims gspec).query (.inr (.inr (.inr q)))) →
          hitB (ι := ι) pk S (.inr (.inr (.inr q))) = false →
          IsQueryBoundP (simulateQ (pinImpl (gspec := gspec) tbl)
            (memoImpl (gspec := gspec) pk S (.inr (.inr (.inr q)))) >>= fun u =>
              simulateQ (pinImpl (gspec := gspec) tbl)
                (simulateQ (memoImpl (gspec := gspec) pk S) (k u)))
            (fun t => Lazy.kind t = .hash) n := by
        intro hm hh
        have hnh : NH (ι := ι) pk S (.inr (.inr (.inr q))) := ⟨rfl, hh⟩
        rw [hm, simulateQ_spec_query]
        show IsQueryBoundP ((liftM ((Lazy.OSpec prims gspec).query (.inr (.inr (.inr q)))) >>=
          fun _ => pure (PublicHash.impl prims q)) >>= _) _ n
        rw [bind_assoc, isQueryBoundP_query_bind_iff]
        have hpos : 0 < n := h'.1.resolve_left (not_not.mpr hnh)
        refine ⟨Or.inr hpos, fun u => ?_⟩
        rw [pure_bind]
        have h2 := hcont u
        rw [ite_eq_left hnh] at h2
        split_ifs with hk
        · exact ih _ _ h2
        · exact absurd rfl hk
      cases q with
      | hmsg r pk' root m => exact hfwd rfl rfl
      | thash pk' key xs =>
        by_cases hpk : pk' = pk
        · subst hpk
          cases hl : S.lookup (key, xs) with
          | none =>
            refine hfwd ?_ ?_
            · simp only [memoImpl, ↓reduceIte, hl]
            · simp only [hitB, hl, Option.isSome_none, Bool.and_false]
          | some y =>
            have hm : memoImpl (gspec := gspec) pk' S
                (.inr (.inr (.inr (PublicHashQuery.thash pk' key xs)))) = pure y := by
              simp only [memoImpl, ↓reduceIte, hl]
            have hy : y = prims.Thash pk' key xs := hS _ (lookup_mem S (key, xs) y hl)
            have hnh : ¬ NH (ι := ι) pk' S
                (.inr (.inr (.inr (PublicHashQuery.thash pk' key xs)))) := by
              intro hh
              have := hh.2
              simp [hitB, hl] at this
            rw [hm, simulateQ_pure, pure_bind, hy]
            have h2 := hcont (prims.Thash pk' key xs)
            rw [ite_eq_right hnh] at h2
            exact ih _ _ h2
        · refine hfwd ?_ ?_
          · simp only [memoImpl, hpk, ↓reduceIte]
          · simp only [hitB, hpk, decide_false, Bool.false_and]

/-- `IsQueryBoundP.simulateQ_run_of_step_le` with an outer handler applied to the result (the
proof is the same induction). -/
theorem run_of_step_le_under {ι₁ ι₂ ι₃ : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    {spec₃ : OracleSpec ι₃} {σ α : Type} {p : ι₁ → Prop} [DecidablePred p] {q : ι₃ → Prop}
    [DecidablePred q] (so : QueryImpl spec₂ (OracleComp spec₃))
    {impl : QueryImpl spec₁ (StateT σ (OracleComp spec₂))} {oa : OracleComp spec₁ α} {n cost : ℕ}
    (h : IsQueryBoundP oa p n)
    (hstep_p : ∀ t, p t → ∀ s, IsQueryBoundP (simulateQ so ((impl t).run s)) q cost)
    (hstep_np : ∀ t, ¬ p t → ∀ s, IsQueryBoundP (simulateQ so ((impl t).run s)) q 0)
    (s : σ) : IsQueryBoundP (simulateQ so ((simulateQ impl oa).run s)) q (n * cost) := by
  induction oa using OracleComp.inductionOn generalizing n s with
  | pure value => simp
  | query_bind t next ih =>
    rw [isQueryBoundP_query_bind_iff] at h
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, simulateQ_bind]
    by_cases hp : p t
    · have hn : 0 < n := h.1.resolve_left (not_not.mpr hp)
      have hrest : ∀ output : spec₁.Range t × σ,
          IsQueryBoundP (simulateQ so ((simulateQ impl (next output.1)).run output.2)) q
            ((n - 1) * cost) :=
        fun output => ih output.1 (n := n - 1) (by simpa [hp] using h.2 output.1) output.2
      have hbound := isQueryBoundP_bind (hstep_p t hp s) (fun output _ => hrest output)
      have hcost : cost + (n - 1) * cost = n * cost := by
        calc cost + (n - 1) * cost = ((n - 1) + 1) * cost := by
              simp [Nat.add_mul, Nat.add_comm]
          _ = n * cost := by rw [Nat.sub_add_cancel hn]
      simpa only [hcost] using hbound
    · have hrest : ∀ output : spec₁.Range t × σ,
          IsQueryBoundP (simulateQ so ((simulateQ impl (next output.1)).run output.2)) q
            (n * cost) :=
        fun output => ih output.1 (n := n) (by simpa [hp] using h.2 output.1) output.2
      simpa using isQueryBoundP_bind (hstep_np t hp s) (fun output _ => hrest output)

/-! ## The count -/

/-- One step of the collision-search callback `collO` makes at most ONE hash query outside the
store when the store contains the entries of `L`: the query at the verification call itself;
the comparison value of the stored target is a hit. -/
theorem collO_step_NH (pk : prims.PkSeed) (L : List (prims.AdrsKey × List prims.Y))
    (S : Store prims) (hL : ∀ c ∈ L, (S.lookup c).isSome = true)
    (t : prims.AdrsKey × List prims.Y) (r : Option (ℕ × List prims.Y)) :
    IsQueryBoundP ((Resources2.collO (gspec := gspec) pk L t).run r) (NH pk S) 1 := by
  have hq : ∀ (key : prims.AdrsKey) (xs : List prims.Y),
      IsQueryBoundP (Resources2.hashQ (gspec := gspec) pk key xs) (NH pk S) 1 :=
    fun _ _ => (isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos
  unfold Resources2.collO
  simp only [StateT.run_mk]
  refine Lazy.qb_bind (NH pk S) (m := 0) (hq _ _) fun y => ?_
  cases ho : L[L.findIdx fun q => decide (q.1 = t.1)]? with
  | none => exact (isQueryBoundP_pure _ _ _).mono (Nat.zero_le _)
  | some q =>
    have hmem : q ∈ L := List.mem_of_getElem? ho
    show IsQueryBoundP (if t.2 ≠ q.2 then _ else _) _ _
    by_cases hne : t.2 ≠ q.2
    · rw [ite_eq_left hne]
      have h0 : IsQueryBoundP (Resources2.hashQ (gspec := gspec) pk q.1 q.2) (NH pk S) 0 := by
        refine (isQueryBoundP_query_iff _ _ _).2 fun hnh => ?_
        have h1 := hnh.2
        have h2 := hL q hmem
        simp [hitB, h2] at h1
      exact Lazy.qb_bind (NH pk S) (m := 0) h0 fun y' => isQueryBoundP_pure _ _ _
    · rw [ite_eq_right hne]
      exact (isQueryBoundP_pure _ _ _).mono (Nat.zero_le _)

/-- A lifted `ProbComp`, pinned, makes no hash query. -/
theorem pin_liftM_NH (tbl : SecretTable vp prims) (pk : prims.PkSeed) (S : Store prims)
    {β : Type} (ob : ProbComp β) :
    IsQueryBoundP (simulateQ (pinImpl (gspec := gspec) tbl)
      (liftM ob : OracleComp (Lazy.OSpec prims gspec) β)) (NH pk S) 0 :=
  pin_mono tbl _ _ _ (IsQueryBoundP.of_imp (fun t ht => ht.1)
    (Lazy.liftM_kindBound (gspec := gspec) (D := SecIdx) (V := prims.Y)
      (hspec := publicHashSpec prims.core) .hash (by decide) ob))

/-- **Hash queries of the pinned second phase of `bTcrArA n A`, given coverage.**  Let the store
`S` be sound at `pk` and contain the entries of `L`.  If the pinned key generation makes no hash
query outside the store (`hKeygen`) and every pinned signature at most one (`hSign`), then the
pinned open second phase `storeForgeOpen A L S pk` makes at most

`qs + (1 + verifyHashes vp)`

hash queries: one `H_msg` per signing query, the `H_msg` of the forgery, and the `Thash`
evaluations of verifying the forgery (`verifyHashes vp = k·(1+a) + 1 + d·(len·(w-1) + 1 + h')`).
No key generation, no tree recomputation, no second hash in the collision test. -/
theorem storeForgeOpen_hashes_of_cover (A : Forger vp prims optRand pkSeedDist) (qs : ℕ)
    (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs)
    (tbl : SecretTable vp prims) (L : List (prims.AdrsKey × List prims.Y)) (S : Store prims)
    (pk : prims.PkSeed) (hS : Sound pk S) (hL : ∀ c ∈ L, (S.lookup c).isSome = true)
    (hKeygen : IsQueryBoundP (simulateQ (pinImpl (gspec := gspec) tbl)
      (Lazy.openKeygen prims gspec pk)) (NH pk S) 0)
    (hSign : ∀ (m : List Byte) (root R : prims.Y),
      IsQueryBoundP (simulateQ (pinImpl (gspec := gspec) tbl)
        (Lazy.openSign prims gspec m pk root R)) (NH pk S) 1) :
    IsQueryBoundP (simulateQ (pinImpl (gspec := gspec) tbl)
        (storeForgeOpen (gspec := gspec) A L S pk)) (fun t => Lazy.kind t = .hash)
      (qs + (1 + Resources2.verifyHashes vp)) := by
  have hrun : ∀ root : prims.Y,
      IsQueryBoundP (simulateQ (pinImpl (gspec := gspec) tbl)
        (runForgerLog (spec := gspec + ((SecIdx →ₒ prims.Y) + publicHashSpec prims.core))
          A ⟨pk, root⟩ lazyRandomizerLift
          (fun m R => Lazy.openSign prims gspec m pk root R))) (NH pk S) (qs * 1) := by
    intro root
    unfold runForgerLog
    refine run_of_step_le_under (pinImpl (gspec := gspec) tbl) (hA _) (fun t ht s => ?_)
      (fun t ht s => ?_) []
    · cases t with
      | inl n => simp at ht
      | inr m =>
        have hstep := Lazy.qb_bind (NH pk S)
          (pin_liftM_NH (gspec := gspec) tbl pk S (optRand ⟨pk, root⟩)) fun addrnd =>
          Lazy.qb_bind (NH pk S)
            (pin_liftM_NH (gspec := gspec) tbl pk S (lazyRandomizer s m addrnd)) fun R =>
            Lazy.qb_bind (NH pk S) (m := 0) (hSign m root R)
              fun sig => isQueryBoundP_pure _ (sig, s ++ [(m, addrnd, R)]) _
        simpa [logSignOracle, lazyRandomizerLift] using hstep
    · cases t with
      | inl n =>
        simp only [QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply, StateT.run_monadLift]
        have h0 := Lazy.qb_bind (fun t => Lazy.kind t = Lazy.Kind.hash) (m := 0)
          (Lazy.liftM_kindBound (gspec := gspec) (D := SecIdx) (V := prims.Y)
            (hspec := publicHashSpec prims.core) .hash (by decide)
            (liftM (unifSpec.query n) : ProbComp _)) fun x => isQueryBoundP_pure _ (x, s) _
        exact pin_mono tbl _ _ _ (IsQueryBoundP.of_imp (fun t ht => ht.1) h0)
      | inr m => simp at ht
  have hver : ∀ (parts : DigestParts vp.params) (sig : GeneralScheme.SignatureCore vp prims.core),
      IsQueryBoundP (simulateQ (pinImpl (gspec := gspec) tbl)
        ((simulateQ (Resources2.collO (gspec := gspec) pk L)
          (Resources2.verifyFree pk parts sig)).run none)) (NH pk S)
        (Resources2.verifyHashes vp * 1) := fun parts sig =>
    pin_mono tbl _ _ _ (IsQueryBoundP.simulateQ_run_of_step_le (cost := 1) (q := NH pk S)
      (Resources2.verifyFree_bound pk parts sig) (fun t ht s => collO_step_NH pk L S hL t s)
      (fun t ht s => absurd trivial ht) none)
  have hmsg : ∀ (R root : prims.Y) (m : List Byte),
      IsQueryBoundP (simulateQ (pinImpl (gspec := gspec) tbl)
        (PublicHash.hmsg prims.core R pk root m :
          OracleComp (Lazy.OSpec prims gspec) (Bytes vp.params.m))) (NH pk S) 1 :=
    fun R root m => pin_mono tbl _ _ _ ((isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos)
  refine pin_memo_bound tbl pk S hS _ _ ?_
  unfold Resources2.memoForgeOpen
  simp only [simulateQ_bind, simulateQ_pure]
  exact (Lazy.qb_bind _ hKeygen fun root =>
    Lazy.qb_bind _ (hrun root) fun z =>
      Lazy.qb_bind _ (hmsg _ _ _) fun dg =>
        Lazy.qb_bind _ (m := 0) (hver _ _) fun c => isQueryBoundP_pure _ _ _).mono (by omega)

end Open

#print axioms Open.bTcrArA_forge_open
#print axioms Open.pinImpl_tbl
#print axioms Open.pin_memo_bound
#print axioms Open.storeForgeOpen_hashes_of_cover
#print axioms Open.storeForgeOpen
#print axioms Open.memoImpl

end Reduction
