import Ideal.Realize.TcrCount
import Reduction.Open.TcrStoreCover

/-!
# Answer-storing class-TCR realisers, generic part (`status/TIGHT.md` §7.2, step 1 of round 3)

The class-TCR realisers of `Ideal/Realize/Tcr.lean` recompute every honest signature in their
second phase by compression queries (`≈ 2.0·10^6` hash calls per signing query).  The
answer-storing adversaries `Reduction.Open.bTcrArA n A` keep the challenger's phase-one answers
instead (`Reduction/Open/TcrStore.lean`); this file supplies the generic pieces to realise them
in the ideal model WITHOUT any compression query for key regeneration and signing:

* `lkImpl pk S` — the **no-fallback lookup handler**: a `Thash` query at the seed `pk` whose
  `(tweak, input)` is stored is answered by the stored value, every other `Thash` query by
  `default`; no `Thash` query is ever forwarded.  Uniform bits, game, secret and `H_msg` queries
  are forwarded.
* `lk_tbl_eq` — on a sound store, a program whose pinned execution makes no `Thash` query outside
  the store (`missB`) is interpreted by the table in the same way with and without `lkImpl`.
  `miss_keygen`, `miss_sign`: the coverage lemmas of `Reduction/Open/TcrStoreCover.lean` give
  exactly that for key regeneration and signing, at the store `ann … pk (honestCalls tbl pk)`.
* `tcrMOpenPS optRand mainP L S pk` — the open second-phase program `tcrMOpenP` with key
  regeneration and the signing oracle run through `lkImpl pk S`; verification of the forgery and
  the collision search unchanged.  `tcrMOpenPS_tbl`: at the phase-one store it is interpreted by
  the table exactly as `tcrMOpenP`.  `tcrMOpenPS_withTH`, `tcrMOpenP_withTH`: hash-free terms.
* counts: `tcrMOpenPS_port` (`≤ qf`), `tcrMOpenPS_th` (`Thash` queries `≤ 2·verifyHashes`, all
  in the verification), `tcrMOpenPS_hmsg` (`≤ qs + 1`), `tcrMOpenPS_bad` (none too long).
* the hash-free recording router `routeHFA` (`= routeA`, `routeA_eq_routeHFA`), the recording
  first phase `tcrPhase1A` (`= (bTcrArA n A).choose`, `bTcrArA_choose_eq_A`) and its counts
  `routeHFA_cap`, `routeHFA_len`.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security TweakableHash

namespace Ideal.Realize

open Reduction Reduction.Open Reduction.Lazy

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! ## The no-fallback lookup handler -/

section Lookup

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]
variable {ι : Type} {gspec : OracleSpec ι}

attribute [local instance] Lazy.openQ

/-- **The no-fallback lookup handler.**  A `Thash` query at the seed `pk` whose `(tweak, input)`
is in the store is answered by the stored value; every other `Thash` query by `default`.  No
`Thash` query is forwarded; all other queries are. -/
def lkImpl (pk : prims.PkSeed) (S : Store prims) :
    QueryImpl (Lazy.OSpec prims gspec) (OracleComp (Lazy.OSpec prims gspec))
  | .inl n => liftM ((Lazy.OSpec prims gspec).query (.inl n))
  | .inr (.inl t) => liftM ((Lazy.OSpec prims gspec).query (.inr (.inl t)))
  | .inr (.inr (.inl i)) => liftM ((Lazy.OSpec prims gspec).query (.inr (.inr (.inl i))))
  | .inr (.inr (.inr (.hmsg r pk' root m))) =>
      liftM ((Lazy.OSpec prims gspec).query (.inr (.inr (.inr (.hmsg r pk' root m)))))
  | .inr (.inr (.inr (.thash pk' key xs))) =>
      (pure ((if pk' = pk then (S.lookup (key, xs)).getD (default : prims.Y) else
        (default : prims.Y)) : prims.Y) : OracleComp (Lazy.OSpec prims gspec) prims.Y)

/-- A `Thash` query that is not answered from the store (other seed, or not stored). -/
def missB (pk : prims.PkSeed) (S : Store prims) :
    ℕ ⊕ (ι ⊕ (SecIdx ⊕ PublicHashQuery prims.PkSeed prims.AdrsKey prims.Y)) → Bool
  | .inr (.inr (.inr (.thash pk' key xs))) =>
      !(decide (pk' = pk) && (S.lookup (key, xs)).isSome)
  | _ => false

theorem missB_NH (pk : prims.PkSeed) (S : Store prims)
    (t : ℕ ⊕ (ι ⊕ (SecIdx ⊕ PublicHashQuery prims.PkSeed prims.AdrsKey prims.Y)))
    (h : missB pk S t = true) : NH pk S t := by
  rcases t with n | t | i | q
  · simp [missB] at h
  · simp [missB] at h
  · simp [missB] at h
  · cases q with
    | hmsg r pk' root m => simp [missB] at h
    | thash pk' key xs =>
      refine ⟨rfl, ?_⟩
      simp only [missB, Bool.not_eq_true'] at h
      simpa [hitB] using h

/-- **Lookups change nothing on covered programs.**  On a store sound at `pk`: if the pinned
execution of `P` makes no `Thash` query outside the store, then `P` run through `lkImpl pk S`
is interpreted by the table exactly as `P`. -/
theorem lk_tbl_eq (tbl : SecretTable vp prims) (pk : prims.PkSeed) (S : Store prims)
    (hS : Sound pk S) {α : Type} (P : OracleComp (Lazy.OSpec prims gspec) α)
    (h : IsQueryBoundP (simulateQ (pinImpl (gspec := gspec) tbl) P)
      (fun t => missB pk S t = true) 0) :
    simulateQ (Lazy.tblImpl (gspec := gspec) (PublicHash.impl prims) tbl)
        (simulateQ (lkImpl (gspec := gspec) pk S) P) =
      simulateQ (Lazy.tblImpl (gspec := gspec) (PublicHash.impl prims) tbl) P := by
  induction P using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    rw [simulateQ_bind, simulateQ_spec_query] at h
    rw [simulateQ_bind, simulateQ_spec_query, simulateQ_bind, simulateQ_bind,
      simulateQ_spec_query]
    rcases t with m | t | i | q
    · have h' : IsQueryBoundP (liftM ((Lazy.OSpec prims gspec).query (.inl m)) >>= fun u =>
          simulateQ (pinImpl (gspec := gspec) tbl) (k u)) _ 0 := h
      rw [isQueryBoundP_query_bind_iff] at h'
      show simulateQ _ (liftM ((Lazy.OSpec prims gspec).query (.inl m))) >>= _ = _
      rw [simulateQ_spec_query]
      exact bind_congr fun u => ih u (by simpa [missB] using h'.2 u)
    · have h' : IsQueryBoundP (liftM ((Lazy.OSpec prims gspec).query (.inr (.inl t))) >>= fun u =>
          simulateQ (pinImpl (gspec := gspec) tbl) (k u)) _ 0 := h
      rw [isQueryBoundP_query_bind_iff] at h'
      show simulateQ _ (liftM ((Lazy.OSpec prims gspec).query (.inr (.inl t)))) >>= _ = _
      rw [simulateQ_spec_query]
      exact bind_congr fun u => ih u (by simpa [missB] using h'.2 u)
    · have h' : IsQueryBoundP (pure (tbl i) >>= fun u =>
          simulateQ (pinImpl (gspec := gspec) tbl) (k u)) _ 0 := h
      rw [pure_bind] at h'
      show simulateQ _ (liftM ((Lazy.OSpec prims gspec).query (.inr (.inr (.inl i))))) >>= _ =
        (pure (tbl i) : OracleComp (unifSpec + gspec) _) >>= _
      rw [simulateQ_spec_query, pure_bind]
      show (pure (tbl i) : OracleComp (unifSpec + gspec) _) >>= _ = _
      rw [pure_bind]
      exact ih _ h'
    · have h' : IsQueryBoundP ((liftM ((Lazy.OSpec prims gspec).query (.inr (.inr (.inr q)))) >>=
          fun _ => pure (PublicHash.impl prims q)) >>= fun u =>
          simulateQ (pinImpl (gspec := gspec) tbl) (k u)) _ 0 := h
      rw [bind_assoc, isQueryBoundP_query_bind_iff] at h'
      have hnm : ¬ missB pk S (.inr (.inr (.inr q))) = true := h'.1.resolve_right (Nat.lt_irrefl 0)
      have hk : IsQueryBoundP (simulateQ (pinImpl (gspec := gspec) tbl)
          (k (PublicHash.impl prims q))) (fun t => missB pk S t = true) 0 := by
        have := h'.2 (PublicHash.impl prims q)
        rw [pure_bind] at this
        simpa [hnm] using this
      cases q with
      | hmsg r pk' root msg =>
        show simulateQ _ (liftM ((Lazy.OSpec prims gspec).query
            (.inr (.inr (.inr (.hmsg r pk' root msg)))))) >>= _ =
          (pure (PublicHash.impl prims (.hmsg r pk' root msg)) :
            OracleComp (unifSpec + gspec) _) >>= _
        rw [simulateQ_spec_query]
        show (pure (PublicHash.impl prims (.hmsg r pk' root msg)) :
            OracleComp (unifSpec + gspec) _) >>= _ = _
        rw [pure_bind, pure_bind]
        exact ih _ hk
      | thash pk' key xs =>
        have hpk : pk' = pk := by
          by_contra hne
          exact hnm (by simp [missB, hne])
        subst hpk
        obtain ⟨y, hy⟩ : ∃ y, S.lookup (key, xs) = some y := by
          cases hl : S.lookup (key, xs) with
          | none => exact absurd (by simp [missB, hl]) hnm
          | some y => exact ⟨y, rfl⟩
        have hyv : y = prims.Thash pk' key xs := hS _ (lookup_mem S (key, xs) y hy)
        have hl : (lkImpl (gspec := gspec) pk' S (.inr (.inr (.inr (.thash pk' key xs)))) :
            OracleComp (Lazy.OSpec prims gspec) prims.Y) = pure y := by
          simp [lkImpl, hy]
        have ht : (Lazy.tblImpl (gspec := gspec) (PublicHash.impl prims) tbl
            (.inr (.inr (.inr (.thash pk' key xs)))) : OracleComp (unifSpec + gspec) prims.Y) =
            pure (prims.Thash pk' key xs) := rfl
        rw [hl, ht, simulateQ_pure, pure_bind, pure_bind, hyv]
        exact ih _ hk

variable {pkSeedDist : ProbComp prims.PkSeed}

/-- **Coverage, key regeneration**: no `Thash` query outside the phase-one store. -/
theorem miss_keygen (tbl : SecretTable vp prims) (pk : prims.PkSeed) :
    IsQueryBoundP (simulateQ (pinImpl (gspec := gspec) tbl) (Lazy.openKeygen prims gspec pk))
      (fun t => missB pk (ann (thashList vp prims pkSeedDist) pk (honestCalls tbl pk)) t = true)
      0 :=
  IsQueryBoundP.of_imp (fun t ht => missB_NH _ _ t ht) (cover_keygen tbl pk)

/-- **Coverage, signing**: no `Thash` query outside the phase-one store (any message, root,
randomizer). -/
theorem miss_sign (tbl : SecretTable vp prims) (pk : prims.PkSeed) (m : List Byte)
    (root R : prims.Y) :
    IsQueryBoundP (simulateQ (pinImpl (gspec := gspec) tbl)
        (Lazy.openSign prims gspec m pk root R))
      (fun t => missB pk (ann (thashList vp prims pkSeedDist) pk (honestCalls tbl pk)) t = true)
      0 := by
  rw [pin_openSign_eq]
  refine Lazy.qb_bind _ (m := 0) (pin_mono tbl _ _ _
    ((isQueryBoundP_query_iff _ _ _).2 fun h => by simp [missB] at h)) fun dg => ?_
  exact IsQueryBoundP.of_imp (fun t ht => missB_NH _ _ t ht)
    (emb_NH pk _ _ fun c hc => lookup_ann_isSome pk _ c (wSign_subset tbl pk R _ c hc))

/-! ### Counting through `lkImpl` -/

/-- `lkImpl` never issues a `Thash` query. -/
theorem lk_noTh (pk : prims.PkSeed) (S : Store prims) {α : Type}
    (P : OracleComp (Lazy.OSpec prims gspec) α) :
    IsQueryBoundP (simulateQ (lkImpl (gspec := gspec) pk S) P)
      (fun t => Tcr.isThIdx t = true) 0 := by
  induction P using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    rw [simulateQ_bind, simulateQ_spec_query]
    rcases t with m | t | i | q
    · exact isQueryBoundP_bind_zero _ _
        ((isQueryBoundP_query_iff _ _ _).2 fun h => by simp [Tcr.isThIdx] at h) ih
    · exact isQueryBoundP_bind_zero _ _
        ((isQueryBoundP_query_iff _ _ _).2 fun h => by simp [Tcr.isThIdx] at h) ih
    · exact isQueryBoundP_bind_zero _ _
        ((isQueryBoundP_query_iff _ _ _).2 fun h => by simp [Tcr.isThIdx] at h) ih
    · cases q with
      | hmsg r pk' root m =>
        exact isQueryBoundP_bind_zero _ _
          ((isQueryBoundP_query_iff _ _ _).2 fun h => by simp [Tcr.isThIdx] at h) ih
      | thash pk' key xs =>
        exact isQueryBoundP_bind_zero _ _ (isQueryBoundP_pure _ _ _) ih

/-- `lkImpl` issues no query outside the class of the source query it answers: every query
bound of the source program holds for the looked-up program. -/
theorem lk_bound (pk : prims.PkSeed) (S : Store prims)
    (p : ℕ ⊕ (ι ⊕ (SecIdx ⊕ PublicHashQuery prims.PkSeed prims.AdrsKey prims.Y)) → Prop)
    [DecidablePred p] {α : Type} (P : OracleComp (Lazy.OSpec prims gspec) α) (n : ℕ)
    (h : IsQueryBoundP P p n) :
    IsQueryBoundP (simulateQ (lkImpl (gspec := gspec) pk S) P) p n := by
  refine IsQueryBoundP.simulateQ_of_step h (fun t ht => ?_) (fun t ht => ?_)
  · rcases t with m | t | i | q
    · exact (isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos
    · exact (isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos
    · exact (isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos
    · cases q with
      | hmsg r pk' root m => exact (isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos
      | thash pk' key xs => exact (isQueryBoundP_pure _ _ _).mono (Nat.zero_le _)
  · rcases t with m | t | i | q
    · exact (isQueryBoundP_query_iff _ _ _).2 fun h' => absurd h' ht
    · exact (isQueryBoundP_query_iff _ _ _).2 fun h' => absurd h' ht
    · exact (isQueryBoundP_query_iff _ _ _).2 fun h' => absurd h' ht
    · cases q with
      | hmsg r pk' root m => exact (isQueryBoundP_query_iff _ _ _).2 fun h' => absurd h' ht
      | thash pk' key xs => exact isQueryBoundP_pure _ _ _

end Lookup

/-! ## The open second phase with lookups -/

section OpenS

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]
variable {ι : Type}

attribute [local instance] Lazy.openQ

/-- `stdImpl` with an arbitrary signer `sg` (`stdImpl` is the case `sg = openSign`). -/
noncomputable def stdImplG (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (gspec : OracleSpec ι) (pkSeed : prims.PkSeed) (root : prims.Y)
    (sg : List Byte → prims.Y →
      OracleComp (Lazy.OSpec prims gspec) (GeneralScheme.SignatureCore vp prims.core)) :
    QueryImpl (unifSpec + (List Byte →ₒ GeneralScheme.SignatureCore vp prims.core))
      (StateT (G2Log prims) (OracleComp (Lazy.OSpec prims gspec))) :=
  (QueryImpl.ofLift unifSpec (OracleComp (Lazy.OSpec prims gspec))).liftTarget
      (StateT (G2Log prims) (OracleComp (Lazy.OSpec prims gspec))) +
    logSignOracle optRand ⟨pkSeed, root⟩ lazyRandomizerLift sg

/-- `portImpl` with an arbitrary signer. -/
noncomputable def portImplG (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (pkSeed : prims.PkSeed) (root : prims.Y)
    (sg : List Byte → prims.Y → OracleComp (Lazy.OSpec prims (hS St Blk))
      (GeneralScheme.SignatureCore vp prims.core)) :
    QueryImpl (FSpecP (GeneralScheme.SignatureCore vp prims.core))
      (StateT (G2Log prims) (OracleComp (Lazy.OSpec prims (hS St Blk))))
  | .inl n => stdImplG optRand (hS St Blk) pkSeed root sg (.inl n)
  | .inr (.inl q) => (liftM (Lazy.gameQ prims (hS St Blk) q) :
      StateT (G2Log prims) (OracleComp (Lazy.OSpec prims (hS St Blk))) St)
  | .inr (.inr m) => stdImplG optRand (hS St Blk) pkSeed root sg (.inr m)

/-- Signing with every `Thash` evaluation looked up in the store. -/
noncomputable def lkSign (S : Store prims) (pkSeed : prims.PkSeed) (root : prims.Y)
    (m : List Byte) (R : prims.Y) :
    OracleComp (Lazy.OSpec prims (hS St Blk)) (GeneralScheme.SignatureCore vp prims.core) :=
  simulateQ (lkImpl (gspec := hS St Blk) pkSeed S) (Lazy.openSign prims (hS St Blk) m pkSeed root R)

/-- The forger's run with signatures computed from the store. -/
noncomputable def portRunS (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (mainP : PortForgerProg vp prims) (S : Store prims) (pkSeed : prims.PkSeed) (root : prims.Y) :
    OracleComp (Lazy.OSpec prims (hS St Blk))
      ((List Byte × GeneralScheme.SignatureCore vp prims.core) × G2Log prims) :=
  (simulateQ (portImplG optRand pkSeed root (lkSign S pkSeed root)) (mainP ⟨pkSeed, root⟩)).run []

/-- `tcrMOpenR` with the key regeneration abstracted. -/
noncomputable def tcrMOpenRK (gspec : OracleSpec ι)
    (kg : OracleComp (Lazy.OSpec prims gspec) prims.Y)
    (run : prims.Y → OracleComp (Lazy.OSpec prims gspec)
      ((List Byte × GeneralScheme.SignatureCore vp prims.core) × G2Log prims))
    (L : List (prims.AdrsKey × List prims.Y)) (pkSeed : prims.PkSeed) :
    OracleComp (Lazy.OSpec prims gspec) (ℕ × List prims.Y) := do
  let root ← kg
  let z ← run root
  let dg ← (PublicHash.hmsg prims.core z.1.2.randomness pkSeed root z.1.1 :
    OracleComp (Lazy.OSpec prims gspec) (Bytes vp.params.m))
  let c ← (simulateQ (Resources2.collO (gspec := gspec) pkSeed L)
    (Resources2.verifyFree pkSeed (splitDigest vp.params dg) z.1.2)).run none
  return c.2.getD (0, [])

theorem tcrMOpenR_eq_RK (gspec : OracleSpec ι)
    (run : prims.Y → OracleComp (Lazy.OSpec prims gspec)
      ((List Byte × GeneralScheme.SignatureCore vp prims.core) × G2Log prims))
    (L : List (prims.AdrsKey × List prims.Y)) (pkSeed : prims.PkSeed) :
    tcrMOpenR gspec run L pkSeed =
      tcrMOpenRK gspec (Lazy.openKeygen prims gspec pkSeed) run L pkSeed := rfl

/-- **The open second phase of the answer-storing realiser**: `tcrMOpenP` with key regeneration
and every signature computed through `lkImpl pk S` (no `Thash` query); `H_msg` of the signed
messages and of the forgery, and the verification of the forgery with the collision search,
as in `tcrMOpenP`. -/
noncomputable def tcrMOpenPS (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (mainP : PortForgerProg vp prims) (L : List (prims.AdrsKey × List prims.Y)) (S : Store prims)
    (pkSeed : prims.PkSeed) : OracleComp (Lazy.OSpec prims (hS St Blk)) (ℕ × List prims.Y) :=
  tcrMOpenRK (hS St Blk)
    (simulateQ (lkImpl (gspec := hS St Blk) pkSeed S) (Lazy.openKeygen prims (hS St Blk) pkSeed))
    (portRunS optRand mainP S pkSeed) L pkSeed

/-- Stateful runs through two handlers agree under `φ` if they agree at every step. -/
theorem run_congr_step {ι₁ ι₂ : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    {σ α : Type} {m : Type → Type} [Monad m] [LawfulMonad m] (φ : QueryImpl spec₂ m)
    (h h' : QueryImpl spec₁ (StateT σ (OracleComp spec₂)))
    (hstep : ∀ t s, simulateQ φ ((h t).run s) = simulateQ φ ((h' t).run s))
    (oa : OracleComp spec₁ α) (s : σ) :
    simulateQ φ ((simulateQ h oa).run s) = simulateQ φ ((simulateQ h' oa).run s) := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure x => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, hstep, ih]

/-- Signing oracles with signers agreeing under `φ` agree under `φ`. -/
theorem logSign_congr {gspec : OracleSpec ι} {m : Type → Type} [Monad m] [LawfulMonad m]
    (φ : QueryImpl (Lazy.OSpec prims gspec) m)
    (optRand : PublicKeyCore prims.core → ProbComp prims.Y) (pk : PublicKeyCore prims.core)
    (sg sg' : List Byte → prims.Y →
      OracleComp (Lazy.OSpec prims gspec) (GeneralScheme.SignatureCore vp prims.core))
    (hsg : ∀ msg R, simulateQ φ (sg msg R) = simulateQ φ (sg' msg R))
    (msg : List Byte) (s : G2Log prims) :
    simulateQ φ ((logSignOracle optRand pk lazyRandomizerLift sg msg).run s) =
      simulateQ φ ((logSignOracle optRand pk lazyRandomizerLift sg' msg).run s) := by
  simp only [logSignOracle, StateT.run_bind, StateT.run_monadLift, StateT.run_get,
    StateT.run_pure, StateT.run_set, simulateQ_bind, simulateQ_pure, bind_assoc,
    pure_bind]
  refine bind_congr fun _ => bind_congr fun R => ?_
  show simulateQ φ (sg msg R) >>= _ = simulateQ φ (sg' msg R) >>= _
  rw [hsg]

variable {pkSeedDist : ProbComp prims.PkSeed}

/-- **At the phase-one store, the lookup program is the recomputing program** (table
interpretation, every `L`, every forger with port). -/
theorem tcrMOpenPS_tbl (tbl : SecretTable vp prims) (pk : prims.PkSeed)
    (L : List (prims.AdrsKey × List prims.Y)) (mainP : PortForgerProg vp prims)
    (optRand : PublicKeyCore prims.core → ProbComp prims.Y) :
    simulateQ (Lazy.tblImpl (gspec := hS St Blk) (PublicHash.impl prims) tbl)
        (tcrMOpenPS optRand mainP L
          (ann (thashList vp prims pkSeedDist) pk (honestCalls tbl pk)) pk) =
      simulateQ (Lazy.tblImpl (gspec := hS St Blk) (PublicHash.impl prims) tbl)
        (tcrMOpenP optRand mainP L pk) := by
  have hSd := sound_ann (vp := vp) (prims := prims) (pkSeedDist := pkSeedDist) pk
    (honestCalls tbl pk)
  unfold tcrMOpenPS tcrMOpenP
  rw [tcrMOpenR_eq_RK]
  unfold tcrMOpenRK
  simp only [simulateQ_bind]
  rw [lk_tbl_eq tbl pk _ hSd _ (miss_keygen tbl pk)]
  refine bind_congr fun root => ?_
  have hrun : simulateQ (Lazy.tblImpl (gspec := hS St Blk) (PublicHash.impl prims) tbl)
      (portRunS optRand mainP (ann (thashList vp prims pkSeedDist) pk (honestCalls tbl pk))
        pk root) =
      simulateQ (Lazy.tblImpl (gspec := hS St Blk) (PublicHash.impl prims) tbl)
        (portRun optRand mainP pk root) := by
    unfold portRunS portRun
    refine run_congr_step _ _ _ (fun t s => ?_) _ _
    rcases t with n | q | msg
    · rfl
    · rfl
    · exact logSign_congr _ optRand _ _ _
        (fun msg R => lk_tbl_eq tbl pk _ hSd _ (miss_sign tbl pk msg root R)) msg s
  rw [hrun]

/-- The lookup program is hash-free as a term. -/
theorem tcrMOpenPS_withTH (T : prims.PkSeed → prims.AdrsKey → List prims.Y → prims.Y)
    (H : prims.Y → prims.PkSeed → prims.Y → List Byte → Bytes vp.params.m)
    (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (mainP : PortForgerProg vp prims) (L : List (prims.AdrsKey × List prims.Y)) (S : Store prims)
    (pkSeed : prims.PkSeed) :
    tcrMOpenPS (prims := withTH prims T H) optRand mainP L S pkSeed =
      tcrMOpenPS optRand mainP L S pkSeed := by
  o9_kernel_rfl

/-- The recomputing port program is hash-free as a term. -/
theorem tcrMOpenP_withTH (T : prims.PkSeed → prims.AdrsKey → List prims.Y → prims.Y)
    (H : prims.Y → prims.PkSeed → prims.Y → List Byte → Bytes vp.params.m)
    (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (mainP : PortForgerProg vp prims) (L : List (prims.AdrsKey × List prims.Y))
    (pkSeed : prims.PkSeed) :
    tcrMOpenP (prims := withTH prims T H) optRand mainP L pkSeed =
      tcrMOpenP optRand mainP L pkSeed := by
  o9_kernel_rfl

end OpenS

/-! ## Counts of the lookup program -/

section CountsS

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]
variable {ι : Type} {gspec : OracleSpec ι}

attribute [local instance] Lazy.openQ

variable (p : ℕ ⊕ (ι ⊕ (SecIdx ⊕ PublicHashQuery prims.PkSeed prims.AdrsKey prims.Y)) → Prop)
  [DecidablePred p]

/-- Queries of `tcrMOpenRK`, from those of its four parts. -/
theorem tcrMOpenRK_bound (kg : OracleComp (Lazy.OSpec prims gspec) prims.Y)
    (run : prims.Y → OracleComp (Lazy.OSpec prims gspec)
      ((List Byte × GeneralScheme.SignatureCore vp prims.core) × G2Log prims))
    (L : List (prims.AdrsKey × List prims.Y)) (pkSeed : prims.PkSeed) (a b c d : ℕ)
    (hk : IsQueryBoundP kg p a)
    (hrun : ∀ root, IsQueryBoundP (run root) p b)
    (hm : ∀ root, ∀ z ∈ support (run root),
      IsQueryBoundP (PublicHash.hmsg prims.core z.1.2.randomness pkSeed root z.1.1 :
        OracleComp (Lazy.OSpec prims gspec) (Bytes vp.params.m)) p c)
    (hv : ∀ (parts : DigestParts vp.params) (sig : GeneralScheme.SignatureCore vp prims.core),
      IsQueryBoundP ((simulateQ (Resources2.collO (gspec := gspec) pkSeed L)
        (Resources2.verifyFree pkSeed parts sig)).run none) p d) :
    IsQueryBoundP (tcrMOpenRK gspec kg run L pkSeed) p (a + b + c + d) := by
  unfold tcrMOpenRK
  exact (isQueryBoundP_bind hk fun root _ =>
    isQueryBoundP_bind (hrun root) fun z hz =>
      isQueryBoundP_bind (hm root z hz) fun dg _ =>
        isQueryBoundP_bind (m := 0) (hv _ _) fun c _ => isQueryBoundP_pure _ _ _).mono (by omega)

variable (optRand : PublicKeyCore prims.core → ProbComp prims.Y)

theorem unifStepG_np (hu : ∀ n, ¬ p (.inl n)) (pkSeed : prims.PkSeed) (root : prims.Y)
    (sg : List Byte → prims.Y →
      OracleComp (Lazy.OSpec prims gspec) (GeneralScheme.SignatureCore vp prims.core))
    (n : ℕ) (s : G2Log prims) :
    IsQueryBoundP ((stdImplG optRand gspec pkSeed root sg (.inl n)).run s) p 0 := by
  unfold stdImplG
  simp only [QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply, StateT.run_monadLift]
  exact isQueryBoundP_bind_zero _ _
    (liftM_np (gspec := gspec) p hu (liftM (unifSpec.query n) : ProbComp _)) fun x =>
      isQueryBoundP_pure _ (x, s) _

theorem signStepG_bound (hu : ∀ n, ¬ p (.inl n)) (pkSeed : prims.PkSeed) (root : prims.Y)
    (sg : List Byte → prims.Y →
      OracleComp (Lazy.OSpec prims gspec) (GeneralScheme.SignatureCore vp prims.core))
    (msg : List Byte) (c : ℕ) (hsign : ∀ R, IsQueryBoundP (sg msg R) p c) (s : G2Log prims) :
    IsQueryBoundP ((stdImplG optRand gspec pkSeed root sg (.inr msg)).run s) p c := by
  have hstep := isQueryBoundP_bind (liftM_np (gspec := gspec) p hu (optRand ⟨pkSeed, root⟩))
    fun addrnd _ => isQueryBoundP_bind
      (liftM_np (gspec := gspec) p hu (lazyRandomizer s msg addrnd)) fun R _ =>
        isQueryBoundP_bind (m := 0) (hsign R)
          fun sig _ => isQueryBoundP_pure _ (sig, s ++ [(msg, addrnd, R)]) _
  simpa [stdImplG, logSignOracle, lazyRandomizerLift] using hstep

end CountsS

section PortCountsS

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]

attribute [local instance] Lazy.openQ

variable (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
  (mainP : PortForgerProg vp prims) (L : List (prims.AdrsKey × List prims.Y)) (S : Store prims)
  (pkSeed : prims.PkSeed)

/-- The run of the port forger, for a class of open-program queries: sampling and port steps
cost what they cost in `tcrMOpenP`, a signing step at most `c`. -/
theorem portRunS_bound
    (p : ℕ ⊕ ((St × Blk) ⊕ (SecIdx ⊕ PublicHashQuery prims.PkSeed prims.AdrsKey prims.Y)) → Prop)
    [DecidablePred p] (hu : ∀ n, ¬ p (.inl n)) (hg : ∀ q, ¬ p (.inr (.inl q)))
    (c : ℕ) (hsign : ∀ root msg R, IsQueryBoundP (lkSign S pkSeed root msg R) p c)
    (qs : ℕ)
    (hqs : ∀ pk, IsQueryBoundP (mainP pk)
      (fun i => isSignQ (S := GeneralScheme.SignatureCore vp prims.core) i = true) qs)
    (root : prims.Y) :
    IsQueryBoundP (portRunS optRand mainP S pkSeed root) p (qs * c) := by
  unfold portRunS
  exact IsQueryBoundP.simulateQ_run_of_step_le (q := p)
    (impl := portImplG optRand pkSeed root (lkSign S pkSeed root)) (hqs ⟨pkSeed, root⟩)
    (fun t ht s => by
      rcases t with n | q | msg
      · simp [isSignQ] at ht
      · simp [isSignQ] at ht
      · exact signStepG_bound p optRand hu pkSeed root _ msg c (hsign root msg) s)
    (fun t ht s => by
      rcases t with n | q | msg
      · exact unifStepG_np p optRand hu pkSeed root _ n s
      · show IsQueryBoundP ((liftM (Lazy.gameQ prims (hS St Blk) q) :
          StateT (G2Log prims) (OracleComp (Lazy.OSpec prims (hS St Blk))) St).run s) _ 0
        rw [StateT.run_monadLift]
        exact isQueryBoundP_bind_zero _ _ ((isQueryBoundP_query_iff _ _ _).2 fun h =>
          absurd h (hg q)) fun x => isQueryBoundP_pure _ (x, s) _
      · exact absurd rfl ht) []

/-- **Port queries of the lookup program**: at most the forger's compression queries. -/
theorem tcrMOpenPS_port (qf : ℕ)
    (hqf : ∀ pk, IsQueryBoundP (mainP pk)
      (fun i => isPortQ (S := GeneralScheme.SignatureCore vp prims.core) i = true) qf) :
    IsQueryBoundP (tcrMOpenPS optRand mainP L S pkSeed) (fun t => Lazy.kind t = .game) qf := by
  have hu : ∀ n : ℕ, ¬ Lazy.kind (ι := St × Blk) (D := SecIdx)
      (κ := PublicHashQuery prims.PkSeed prims.AdrsKey prims.Y) (.inl n) = .game := by
    intro n; simp [Lazy.kind]
  have hsec : ∀ d : SecIdx, ¬ Lazy.kind (ι := St × Blk) (D := SecIdx)
      (κ := PublicHashQuery prims.PkSeed prims.AdrsKey prims.Y) (.inr (.inr (.inl d))) = .game := by
    intro d; simp [Lazy.kind]
  have hth : ∀ (pk : prims.PkSeed) (key : prims.AdrsKey) (xs : List prims.Y),
      ¬ Lazy.kind (thIdx prims (St × Blk) pk key xs) = .game := by
    intro pk key xs; simp [Lazy.kind]
  have hhm : ∀ (R : prims.Y) (pk : prims.PkSeed) (root : prims.Y) (m : List Byte),
      ¬ Lazy.kind (hmIdx prims (St × Blk) R pk root m) = .game := by
    intro R pk root m; simp [Lazy.kind]
  have h := tcrMOpenRK_bound (gspec := hS St Blk) (fun t => Lazy.kind t = .game)
    _ (portRunS optRand mainP S pkSeed) L pkSeed 0 qf 0 0
    (lk_bound pkSeed S _ _ 0 (np_openKeygen _ pkSeed hsec fun key xs _ => hth _ _ _))
    (fun root => by
      unfold portRunS
      exact IsQueryBoundP.simulateQ_run_of_step (q := fun t => Lazy.kind t = .game)
        (impl := portImplG optRand pkSeed root (lkSign S pkSeed root)) (hqf ⟨pkSeed, root⟩)
        (fun t ht s => by
          rcases t with n | q | msg
          · simp [isPortQ] at ht
          · show IsQueryBoundP ((liftM (Lazy.gameQ prims (hS St Blk) q) :
              StateT (G2Log prims) (OracleComp (Lazy.OSpec prims (hS St Blk))) St).run s) _ 1
            rw [StateT.run_monadLift]
            exact isQueryBoundP_bind (m := 0) ((isQueryBoundP_query_iff _ _ _).2 fun _ =>
              Nat.one_pos) fun x _ => isQueryBoundP_pure _ (x, s) _
          · simp [isPortQ] at ht)
        (fun t ht s => by
          rcases t with n | q | msg
          · exact unifStepG_np _ optRand hu pkSeed root _ n s
          · exact absurd rfl ht
          · exact signStepG_bound _ optRand hu pkSeed root _ msg 0
              (fun R => lk_bound pkSeed S _ _ 0
                (np_openSign _ msg pkSeed root R hsec (fun key xs _ => hth _ _ _)
                  (hhm _ _ _ _))) s) [])
    (fun root z _ => (isQueryBoundP_query_iff _ _ _).2 fun h => absurd h (hhm _ _ _ _))
    (fun parts sig => np_collO_run _ pkSeed L (fun key xs _ => hth _ _ _)
      (fun q _ => hth _ _ _) parts sig none)
  exact h.mono (by omega)

/-- **`Thash` queries of the lookup program**: only those of verifying the forgery
(`≤ 2·verifyHashes`: the verification call and the comparison value). -/
theorem tcrMOpenPS_th (qs : ℕ)
    (hqs : ∀ pk, IsQueryBoundP (mainP pk)
      (fun i => isSignQ (S := GeneralScheme.SignatureCore vp prims.core) i = true) qs) :
    IsQueryBoundP (tcrMOpenPS optRand mainP L S pkSeed) (fun t => Tcr.isThIdx t = true)
      (Resources2.verifyHashes vp * 2) := by
  have hu : ∀ n : ℕ, ¬ Tcr.isThIdx (ι := St × Blk) (P := prims.PkSeed) (K := prims.AdrsKey)
      (Y := prims.Y) (.inl n) = true := by
    intro n; simp [Tcr.isThIdx]
  have h := tcrMOpenRK_bound (gspec := hS St Blk) (fun t => Tcr.isThIdx t = true)
    (simulateQ (lkImpl (gspec := hS St Blk) pkSeed S) (Lazy.openKeygen prims (hS St Blk) pkSeed))
    (portRunS optRand mainP S pkSeed) L pkSeed 0 0 0 (Resources2.verifyHashes vp * 2)
    (lk_noTh pkSeed S (Lazy.openKeygen prims (hS St Blk) pkSeed))
    (fun root => by
      have := portRunS_bound optRand mainP S pkSeed (fun t => Tcr.isThIdx t = true) hu
        (fun q => by simp [Tcr.isThIdx]) 0 (fun root msg R => lk_noTh pkSeed S (Lazy.openSign prims (hS St Blk) msg pkSeed root R)) qs hqs root
      simpa using this)
    (fun root z _ => (isQueryBoundP_query_iff _ _ _).2 fun h => by simp [Tcr.isThIdx] at h)
    (fun parts sig => IsQueryBoundP.simulateQ_run_of_step_le (cost := 2)
      (q := fun t => Tcr.isThIdx t = true)
      (Resources2.verifyFree_bound pkSeed parts sig)
      (fun t ht s => IsQueryBoundP.of_imp (fun t ht => Tcr.isThIdx_kind t ht)
        (Resources2.collO_step_bound pkSeed L .hash t s))
      (fun t ht s => absurd trivial ht) none)
  exact h.mono (by omega)

/-- **`H_msg` queries of the lookup program**: one per signing query and one for the forgery. -/
theorem tcrMOpenPS_hmsg (qs : ℕ)
    (hqs : ∀ pk, IsQueryBoundP (mainP pk)
      (fun i => isSignQ (S := GeneralScheme.SignatureCore vp prims.core) i = true) qs) :
    IsQueryBoundP (tcrMOpenPS optRand mainP L S pkSeed) (fun t => isHmsgIdx t = true) (qs + 1) := by
  have hu : ∀ n : ℕ, ¬ isHmsgIdx (ι := St × Blk) (P := prims.PkSeed) (K := prims.AdrsKey)
      (Y := prims.Y) (.inl n) = true := by
    intro n; simp [isHmsgIdx]
  have hsec : ∀ d : SecIdx, ¬ isHmsgIdx (ι := St × Blk) (P := prims.PkSeed) (K := prims.AdrsKey)
      (Y := prims.Y) (.inr (.inr (.inl d))) = true := by
    intro d; simp [isHmsgIdx]
  have hth : ∀ (pk : prims.PkSeed) (key : prims.AdrsKey) (xs : List prims.Y),
      ¬ isHmsgIdx (thIdx prims (St × Blk) pk key xs) = true := by
    intro pk key xs; simp [isHmsgIdx]
  have h := tcrMOpenRK_bound (gspec := hS St Blk) (fun t => isHmsgIdx t = true)
    (simulateQ (lkImpl (gspec := hS St Blk) pkSeed S) (Lazy.openKeygen prims (hS St Blk) pkSeed))
    (portRunS optRand mainP S pkSeed) L pkSeed 0 (qs * 1) 1 0
    (lk_bound pkSeed S _ _ 0 (np_openKeygen _ pkSeed hsec fun key xs _ => hth _ _ _))
    (fun root => portRunS_bound optRand mainP S pkSeed (fun t => isHmsgIdx t = true) hu
      (fun q => by simp [isHmsgIdx]) 1
      (fun root msg R => lk_bound pkSeed S _ _ 1
        (openSign_one _ msg pkSeed root R hsec fun key xs _ => hth _ _ _)) qs hqs root)
    (fun root z _ => (isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos)
    (fun parts sig => np_collO_run _ pkSeed L (fun key xs _ => hth _ _ _)
      (fun q _ => hth _ _ _) parts sig none)
  exact h.mono (by omega)

/-- **No long hash query in the lookup program** (as `tcrMOpenP_bad`). -/
theorem tcrMOpenPS_bad (B ℓ : ℕ) (hB : ∀ xs : List prims.Y, OkLen vp xs → xs.length ≤ B)
    (hL : ∀ q ∈ L, q.2.length ≤ B)
    (hlong : ∀ pk, IsQueryBoundP (mainP pk)
      (fun i => isLongQ (S := GeneralScheme.SignatureCore vp prims.core) ℓ i = true) 0)
    (hout : ∀ pk, ∀ z ∈ support (mainP pk), z.1.length ≤ ℓ) :
    IsQueryBoundP (tcrMOpenPS optRand mainP L S pkSeed) (fun t => isBadIdx B ℓ t = true) 0 := by
  have hu : ∀ n : ℕ, ¬ isBadIdx (ι := St × Blk) (P := prims.PkSeed) (K := prims.AdrsKey)
      (Y := prims.Y) B ℓ (.inl n) = true := by
    intro n; simp [isBadIdx]
  have hsec : ∀ d : SecIdx, ¬ isBadIdx (ι := St × Blk) (P := prims.PkSeed) (K := prims.AdrsKey)
      (Y := prims.Y) B ℓ (.inr (.inr (.inl d))) = true := by
    intro d; simp [isBadIdx]
  have hth : ∀ (pk : prims.PkSeed) (key : prims.AdrsKey) (xs : List prims.Y), xs.length ≤ B →
      ¬ isBadIdx B ℓ (thIdx prims (St × Blk) pk key xs) = true := by
    intro pk key xs h; simp [isBadIdx]; omega
  have hhm : ∀ (R : prims.Y) (pk : prims.PkSeed) (root : prims.Y) (m : List Byte),
      m.length ≤ ℓ → ¬ isBadIdx B ℓ (hmIdx prims (St × Blk) R pk root m) = true := by
    intro R pk root m h; simp [isBadIdx]; omega
  have h := tcrMOpenRK_bound (gspec := hS St Blk) (fun t => isBadIdx B ℓ t = true)
    (simulateQ (lkImpl (gspec := hS St Blk) pkSeed S) (Lazy.openKeygen prims (hS St Blk) pkSeed))
    (portRunS optRand mainP S pkSeed) L pkSeed 0 0 0 0
    (lk_bound pkSeed S _ _ 0 (np_openKeygen _ pkSeed hsec fun key xs hx => hth _ _ _ (hB xs hx)))
    (fun root => qb_simulateQ_run_zero
        (p := fun i => isLongQ (S := GeneralScheme.SignatureCore vp prims.core) ℓ i = true)
        (impl := portImplG optRand pkSeed root (lkSign S pkSeed root))
        (fun t ht s => by
          rcases t with n | q | msg
          · exact unifStepG_np _ optRand hu pkSeed root _ n s
          · show IsQueryBoundP ((liftM (Lazy.gameQ prims (hS St Blk) q) :
              StateT (G2Log prims) (OracleComp (Lazy.OSpec prims (hS St Blk))) St).run s) _ 0
            rw [StateT.run_monadLift]
            exact isQueryBoundP_bind_zero _ _ ((isQueryBoundP_query_iff _ _ _).2 fun h => by
              simp [isBadIdx] at h) fun x => isQueryBoundP_pure _ (x, s) _
          · have hm : msg.length ≤ ℓ := by
              simp only [isLongQ, decide_eq_true_eq, not_lt] at ht
              exact ht
            exact signStepG_bound _ optRand hu pkSeed root _ msg 0
              (fun R => lk_bound pkSeed S _ _ 0 (np_openSign _ msg pkSeed root R hsec
                (fun key xs hx => hth _ _ _ (hB xs hx)) (hhm _ _ _ _ hm))) s)
        (hlong ⟨pkSeed, root⟩) [])
    (fun root z hz => (isQueryBoundP_query_iff _ _ _).2 fun h => by
      refine absurd h (hhm _ _ _ _ (hout ⟨pkSeed, root⟩ z.1 ?_))
      have hz' : z.1 ∈ support ((simulateQ (portImplG optRand pkSeed root (lkSign S pkSeed root))
          (mainP ⟨pkSeed, root⟩)).run' []) := by
        rw [StateT.run'_eq, support_map]
        exact ⟨z, hz, rfl⟩
      exact support_simulateQ_run'_subset _ _ _ hz')
    (fun parts sig => np_collO_run _ pkSeed L (fun key xs hx => hth _ _ _ (hB xs hx))
      (fun q hq => hth _ _ _ (hL q hq)) parts sig none)
  exact h

end PortCountsS

/-! ## The recording first phase -/

section RouteA

variable {PkSeed Tweak Y : Type} [DecidableEq Tweak] (P : List Y → Prop) [DecidablePred P] (N : ℕ)
  {α : Type}

/-- `recAns` without its (unused) hash argument. -/
def recAnsHF : (q : (Spec0 PkSeed Tweak Y).Domain) → (Spec0 PkSeed Tweak Y).Range q →
    List ((Tweak × List Y) × Y) → List ((Tweak × List Y) × Y)
  | .inl _, _, S => S
  | .inr (.inl c), some y, S => S ++ [(c, y)]
  | .inr (.inl _), none, S => S
  | .inr (.inr _), _, S => S

/-- `routeStepA` without its (unused) hash argument. -/
def routeStepHFA (q : (Spec0 PkSeed Tweak Y).Domain)
    (s : List (Tweak × List Y) × List ((Tweak × List Y) × Y)) :
    OracleComp (Spec1 Tweak Y P)
      ((Spec0 PkSeed Tweak Y).Range q × (List (Tweak × List Y) × List ((Tweak × List Y) × Y))) :=
  (fun z => (z.1, (z.2, recAnsHF q z.1 s.2))) <$> routeStepHF P N q s.1

/-- **The hash-free recording router** (`= routeA`, `routeA_eq_routeHFA`). -/
def routeHFA : QueryImpl (Spec0 PkSeed Tweak Y)
    (StateT (List (Tweak × List Y) × List ((Tweak × List Y) × Y)) (OracleComp (Spec1 Tweak Y P))) :=
  fun q => StateT.mk (routeStepHFA (PkSeed := PkSeed) P N q)

theorem routeA_eq_routeHFA (th : TweakableHash PkSeed Tweak (List Y) Y) :
    routeA th P N =
      (routeHFA P N : QueryImpl (Spec0 PkSeed Tweak Y)
        (StateT (List (Tweak × List Y) × List ((Tweak × List Y) × Y))
          (OracleComp (Spec1 Tweak Y P)))) := by
  funext q
  rcases q with q | ⟨t, xs⟩ | q
  · rfl
  · show StateT.mk (routeStepA th P N _) = StateT.mk (routeStepHFA P N _)
    congr 1
    funext s
    unfold routeStepA routeStepHFA
    have h : TcrSplit.routeStep th P N (.inr (.inl (t, xs))) s.1 =
        routeStepHF (PkSeed := PkSeed) P N (.inr (.inl (t, xs))) s.1 := rfl
    rw [h]
    congr 1
    funext z
    rcases z with ⟨r, L⟩
    cases r <;> rfl
  · exact q.1.elim

theorem runA_query_bind (t : (Spec0 PkSeed Tweak Y).Domain)
    (k : (Spec0 PkSeed Tweak Y).Range t → OracleComp (Spec0 PkSeed Tweak Y) α)
    (L : List (Tweak × List Y)) (S : List ((Tweak × List Y) × Y)) :
    (simulateQ (routeHFA (PkSeed := PkSeed) P N)
        (liftM ((Spec0 PkSeed Tweak Y).query t) >>= k)).run (L, S) =
      routeStepHF P N t L >>= fun z =>
        (simulateQ (routeHFA (PkSeed := PkSeed) P N) (k z.1)).run (z.2, recAnsHF t z.1 S) := by
  rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
  show ((fun z => (z.1, (z.2, recAnsHF t z.1 S))) <$> routeStepHF P N t L) >>= _ = _
  rw [bind_map_left]

theorem routeStepHF_unif' (n : ℕ) (L : List (Tweak × List Y)) :
    routeStepHF (PkSeed := PkSeed) P N (.inl n) L =
      (fun u => (u, L)) <$> liftM ((Spec1 Tweak Y P).query (.inl n)) := rfl

theorem routeStepHF_chal' (tw : Tweak) (xs : List Y) (L : List (Tweak × List Y)) :
    routeStepHF (PkSeed := PkSeed) P N (.inr (.inl (tw, xs))) L =
      if N ≤ L.length ∨ tw ∈ L.map Prod.fst then pure (none, L)
      else if h : P xs then
        (fun r => (r, L ++ [(tw, xs)])) <$>
          liftM ((Spec1 Tweak Y P).query (.inr (.inl (tw, ⟨xs, h⟩))))
      else
        (fun r => (r, L ++ [(tw, xs)])) <$>
          liftM ((Spec1 Tweak Y P).query (.inr (.inr ⟨(), tw, xs⟩))) := rfl

/-- **The recording router issues at most `N - |L|` game queries** (as `routeHF_cap`). -/
theorem routeHFA_cap (oa : OracleComp (Spec0 PkSeed Tweak Y) α) (L : List (Tweak × List Y))
    (S : List ((Tweak × List Y) × Y)) :
    IsQueryBoundP ((simulateQ (routeHFA (PkSeed := PkSeed) P N) oa).run (L, S))
      (fun t => t.isRight = true) (N - L.length) := by
  induction oa using OracleComp.inductionOn generalizing L S with
  | pure x => simp
  | query_bind t k ih =>
    rw [runA_query_bind]
    rcases t with n | ⟨tw, xs⟩ | q
    · rw [routeStepHF_unif', bind_map_left]
      exact (isQueryBoundP_bind (p := fun t : (Spec1 Tweak Y P).Domain => t.isRight = true)
        (n := 0) (m := N - L.length)
        ((isQueryBoundP_query_iff _ _ _).2 fun h => Bool.noConfusion h)
        fun u _ => ih u L _).mono (by omega)
    · rw [routeStepHF_chal']
      by_cases h1 : N ≤ L.length ∨ tw ∈ L.map Prod.fst
      · rw [ite_eq_left h1, pure_bind]
        exact ih _ _ _
      · rw [ite_eq_right h1]
        have hlt : L.length < N := by
          by_contra hc
          exact h1 (Or.inl (Nat.le_of_not_lt hc))
        by_cases h2 : P xs
        · rw [dite_eq_left h2, bind_map_left]
          refine (isQueryBoundP_bind (p := fun t : (Spec1 Tweak Y P).Domain => t.isRight = true)
            (n := 1) (m := N - (L ++ [(tw, xs)]).length)
            ((isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos)
            fun r _ => ih r (L ++ [(tw, xs)]) _).mono ?_
          simp only [List.length_append, List.length_singleton]
          omega
        · rw [dite_eq_right h2, bind_map_left]
          refine (isQueryBoundP_bind (p := fun t : (Spec1 Tweak Y P).Domain => t.isRight = true)
            (n := 1) (m := N - (L ++ [(tw, xs)]).length)
            ((isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos)
            fun r _ => ih r (L ++ [(tw, xs)]) _).mono ?_
          simp only [List.length_append, List.length_singleton]
          omega
    · exact q.1.elim

/-- **The recording router issues no game query on more than `B` values** (as `routeHF_len`). -/
theorem routeHFA_len (B : ℕ) (oa : OracleComp (Spec0 PkSeed Tweak Y) α)
    (h : IsQueryBoundP oa (fun t => bad0 B t = true) 0)
    (s : List (Tweak × List Y) × List ((Tweak × List Y) × Y)) :
    IsQueryBoundP ((simulateQ (routeHFA (PkSeed := PkSeed) P N) oa).run s)
      (fun t => bad1 P B t = true) 0 := by
  refine qb_simulateQ_run_zero (fun t ht s => ?_) h s
  show IsQueryBoundP (routeStepHFA P N t s) _ 0
  unfold routeStepHFA
  rw [isQueryBoundP_map_iff]
  rcases t with n | ⟨tw, xs⟩ | q
  · rw [routeStepHF_unif', isQueryBoundP_map_iff]
    exact (isQueryBoundP_query_iff _ _ _).2 fun h => by simp [bad1] at h
  · have hxs : xs.length ≤ B := by
      simp only [bad0, decide_eq_true_eq, not_lt] at ht
      exact ht
    rw [routeStepHF_chal']
    by_cases h1 : N ≤ s.1.length ∨ tw ∈ s.1.map Prod.fst
    · rw [ite_eq_left h1]
      exact isQueryBoundP_pure _ _ _
    · rw [ite_eq_right h1]
      by_cases h2 : P xs
      · rw [dite_eq_left h2, isQueryBoundP_map_iff]
        exact (isQueryBoundP_query_iff _ _ _).2 fun h => by
          simp only [bad1, decide_eq_true_eq] at h
          omega
      · rw [dite_eq_right h2, isQueryBoundP_map_iff]
        exact (isQueryBoundP_query_iff _ _ _).2 fun h => by
          simp only [bad1, decide_eq_true_eq] at h
          omega
  · exact q.1.elim

end RouteA

section Phase1A

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]

attribute [local irreducible] arityTargets tcrTargets

/-- State handed from the first to the second phase of the answer-storing adversary: sparse
table, recorded calls, stored answers. -/
abbrev TcrP1StateA (vp : ValidatedParams) (prims : Primitives vp.params) : Type :=
  SecretTable vp prims × (List (prims.AdrsKey × List prims.Y) × Store prims)

variable (vp prims) in
/-- **The recording first phase**: the structure walk `tcrChooseHF`, routed to the class game
and recording every call AND every oracle answer.  Hash-free (`tcrPhase1A_withTH`). -/
noncomputable def tcrPhase1A (n : ℕ) : OracleComp (TcrP1Spec prims n) (TcrP1StateA vp prims) :=
  (simulateQ (routeHFA (fun xs : List prims.Y => xs.length = n) (tcrTargets vp))
    (tcrChooseHF vp prims)).run ([], [])

/-- **The first phase of `bTcrArA n A` is `tcrPhase1A`.** -/
theorem bTcrArA_choose_eq_A {optRand : PublicKeyCore prims.core → ProbComp prims.Y}
    {pkSeedDist : ProbComp prims.PkSeed} (n : ℕ) (A : Forger vp prims optRand pkSeedDist) :
    ((bTcrArA n A).choose : OracleComp (TcrP1Spec prims n) (TcrP1StateA vp prims)) =
      tcrPhase1A vp prims n := by
  unfold bTcrArA tcrPhase1A
  dsimp only
  rw [routeA_eq_routeHFA]
  rfl

theorem tcrPhase1A_withTH (T : prims.PkSeed → prims.AdrsKey → List prims.Y → prims.Y)
    (H : prims.Y → prims.PkSeed → prims.Y → List Byte → Bytes vp.params.m) (n : ℕ) :
    (tcrPhase1A vp (withTH prims T H) n : OracleComp (TcrP1Spec prims n) (TcrP1StateA vp prims)) =
      tcrPhase1A vp prims n := rfl

end Phase1A

end Ideal.Realize
