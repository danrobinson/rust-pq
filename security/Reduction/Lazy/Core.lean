import Reduction.Tables

/-!
# Lazy secret sampling with an explicit cache, and a resource-explicit program format

Phase 2, package A.  This file is generic (no SLH-DSA content).

## The format

A reduction adversary is first written as an *open program*

`P : OracleComp (RSpec gspec D V hspec) α`,  `RSpec gspec D V hspec = unifSpec + (gspec + ((D →ₒ V) + hspec))`

whose only effects are queries to four oracles:

* `unifSpec` — private uniform bits (this is also how the forger's own randomness and the lifted
  samplers `pkSeedDist`, `optRand` appear);
* `gspec` — the oracles of the security game the adversary plays;
* `D →ₒ V` — the *secret oracle*: "give me the secret value at address `d`";
* `hspec` — a *deterministic* local computation that we want to count (the scheme's public hash
  functions), interpreted by a fixed `hI : QueryImpl hspec Id`.

`lazyRes P` answers the secret oracle lazily from an association-list cache `List (D × V)`,
issuing one query to a *draw oracle* `Unit →ₒ V` on every cache miss, and leaves everything else
untouched: it is a program over `RSpec gspec Unit V hspec`, in which game queries, fresh draws
and hash evaluations are all explicit, countable queries.  The actual adversary is its
interpretation

`lazyRun hI P = simulateQ (interp hI) (lazyRes P) : OracleComp (unifSpec + gspec) α`

(draw ↦ `$ᵗ V`, hash query `q` ↦ `hI q`).

## Results

* `lazyRun_eq` — `lazyRun` is the direct lazy handler `lazyImpl` (cache, sample on miss).
* `evalDist_lazyRun_eq_table` (stateful outer handler) and `evalDist_lazyRun_eq_table'`
  (stateless) — **lazy = eager under an arbitrary game**: for every handler `G` of the game
  oracles, running `lazyRun hI P` under `G` has the same law as sampling a uniform table
  `g : D → V` and running the *eager* program `simulateQ (tblImpl hI g) P` under `G`.  No
  side condition on `P`.
* resource transfer: bounds on the secret / game / hash queries of `P` become bounds on the
  draw / game / hash queries of `lazyRes P` (`lazyRes_bound_*`), and game-query bounds pass to
  `lazyRun` (`lazyRun_gameBound`).  A cache miss stores exactly one entry and a hit none
  (`lazyImplR_sec_run_hit`, `lazyImplR_sec_run_miss`), so the cache never has more entries than
  draws were made.
-/

open OracleComp OracleSpec ENNReal

namespace Reduction
namespace Lazy

universe u

variable {ι κ : Type} {gspec : OracleSpec ι} {hspec : OracleSpec κ} {D V α : Type}

/-- Oracle interface of an open program: private uniform bits, the game's oracles, the secret
oracle `D →ₒ V`, and a deterministic local-computation oracle `hspec`. -/
abbrev RSpec (gspec : OracleSpec ι) (D V : Type) (hspec : OracleSpec κ) :
    OracleSpec (ℕ ⊕ (ι ⊕ (D ⊕ κ))) :=
  unifSpec + (gspec + ((D →ₒ V) + hspec))

/-- The four kinds of query of an open program. -/
inductive Kind
  | unif | game | sec | hash
deriving DecidableEq, Repr

/-- The kind of a query index of `RSpec`. -/
def kind : ℕ ⊕ (ι ⊕ (D ⊕ κ)) → Kind
  | .inl _ => .unif
  | .inr (.inl _) => .game
  | .inr (.inr (.inl _)) => .sec
  | .inr (.inr (.inr _)) => .hash

/-! ## Handlers -/

/-- The lazy cache, resource-explicit form: unif / game / hash queries are forwarded unchanged;
a secret query at `d` is answered from the association list if `d` is present, and otherwise by
ONE query to the draw oracle `Unit →ₒ V`, whose answer is stored at the head of the list. -/
def lazyImplR [DecidableEq D] :
    QueryImpl (RSpec gspec D V hspec)
      (StateT (List (D × V)) (OracleComp (RSpec gspec Unit V hspec)))
  | .inl n => (liftM ((RSpec gspec Unit V hspec).query (.inl n)) :
      OracleComp (RSpec gspec Unit V hspec) _)
  | .inr (.inl t) => (liftM ((RSpec gspec Unit V hspec).query (.inr (.inl t))) :
      OracleComp (RSpec gspec Unit V hspec) _)
  | .inr (.inr (.inr q)) => (liftM ((RSpec gspec Unit V hspec).query (.inr (.inr (.inr q)))) :
      OracleComp (RSpec gspec Unit V hspec) _)
  | .inr (.inr (.inl d)) => do
      let c ← get
      match c.lookup d with
      | some v => pure v
      | none => do
        let v ← (liftM (liftM ((RSpec gspec Unit V hspec).query (.inr (.inr (.inl ())))) :
            OracleComp (RSpec gspec Unit V hspec) V) :
          StateT (List (D × V)) (OracleComp (RSpec gspec Unit V hspec)) V)
        set ((d, v) :: c)
        pure v

/-- Interpretation of a resource-explicit program: a draw is a fresh uniform sample, a hash
query is evaluated by `hI`; uniform bits and game queries are forwarded. -/
noncomputable def interp [SampleableType V] (hI : QueryImpl hspec Id) :
    QueryImpl (RSpec gspec Unit V hspec) (OracleComp (unifSpec + gspec))
  | .inl n => (liftM ((unifSpec + gspec).query (.inl n)) : OracleComp (unifSpec + gspec) _)
  | .inr (.inl t) => (liftM ((unifSpec + gspec).query (.inr t)) : OracleComp (unifSpec + gspec) _)
  | .inr (.inr (.inl _)) => (liftM ($ᵗ V : ProbComp V) : OracleComp (unifSpec + gspec) V)
  | .inr (.inr (.inr q)) => pure (hI q)

/-- The lazy cache in one step (`interp` after `lazyImplR`, see `simulateQ_interp_lazyImplR`):
sample on a miss, look up on a hit. -/
noncomputable def lazyImpl [DecidableEq D] [SampleableType V] (hI : QueryImpl hspec Id) :
    QueryImpl (RSpec gspec D V hspec) (StateT (List (D × V)) (OracleComp (unifSpec + gspec)))
  | .inl n => (liftM ((unifSpec + gspec).query (.inl n)) : OracleComp (unifSpec + gspec) _)
  | .inr (.inl t) => (liftM ((unifSpec + gspec).query (.inr t)) : OracleComp (unifSpec + gspec) _)
  | .inr (.inr (.inr q)) => pure (hI q)
  | .inr (.inr (.inl d)) => do
      let c ← get
      match c.lookup d with
      | some v => pure v
      | none => do
        let v ← (liftM (liftM ($ᵗ V : ProbComp V) : OracleComp (unifSpec + gspec) V) :
          StateT (List (D × V)) (OracleComp (unifSpec + gspec)) V)
        set ((d, v) :: c)
        pure v

/-- The eager handler: the secret oracle is the fixed function `h` (a table). -/
def tblImpl (hI : QueryImpl hspec Id) (h : D → V) :
    QueryImpl (RSpec gspec D V hspec) (OracleComp (unifSpec + gspec))
  | .inl n => (liftM ((unifSpec + gspec).query (.inl n)) : OracleComp (unifSpec + gspec) _)
  | .inr (.inl t) => (liftM ((unifSpec + gspec).query (.inr t)) : OracleComp (unifSpec + gspec) _)
  | .inr (.inr (.inl d)) => pure (h d)
  | .inr (.inr (.inr q)) => pure (hI q)

/-- The resource-explicit program of an open program: secret oracle replaced by the lazy cache
(started empty) over a draw oracle. -/
def lazyRes [DecidableEq D] (P : OracleComp (RSpec gspec D V hspec) α) :
    OracleComp (RSpec gspec Unit V hspec) α :=
  (simulateQ lazyImplR P).run' []

/-- The lazy adversary of an open program. -/
noncomputable def lazyRun [DecidableEq D] [SampleableType V] (hI : QueryImpl hspec Id)
    (P : OracleComp (RSpec gspec D V hspec) α) : OracleComp (unifSpec + gspec) α :=
  simulateQ (interp hI) (lazyRes P)

/-! ## Step equations of the cache -/

section Steps

variable [DecidableEq D]

/-- Cache hit: no draw, cache unchanged. -/
theorem lazyImplR_sec_run_hit (d : D) (c : List (D × V)) (v : V) (hc : c.lookup d = some v) :
    ((lazyImplR (gspec := gspec) (hspec := hspec) (.inr (.inr (.inl d)))).run c) =
      pure (v, c) := by
  simp [lazyImplR, hc]

/-- Cache miss: exactly one draw, and the cache grows by exactly one entry. -/
theorem lazyImplR_sec_run_miss (d : D) (c : List (D × V)) (hc : c.lookup d = none) :
    ((lazyImplR (gspec := gspec) (hspec := hspec) (.inr (.inr (.inl d)))).run c) =
      (liftM ((RSpec gspec Unit V hspec).query (.inr (.inr (.inl ())))) :
        OracleComp (RSpec gspec Unit V hspec) V) >>= fun v => pure (v, (d, v) :: c) := by
  simp [lazyImplR, hc]

end Steps

/-! ## `interp ∘ lazyImplR = lazyImpl` -/

section Compose

variable [DecidableEq D] [SampleableType V]

theorem simulateQ_interp_lazyImplR (hI : QueryImpl hspec Id)
    (P : OracleComp (RSpec gspec D V hspec) α) (c : List (D × V)) :
    simulateQ (interp hI) ((simulateQ lazyImplR P).run c) = (simulateQ (lazyImpl hI) P).run c := by
  induction P using OracleComp.inductionOn generalizing c with
  | pure a => simp
  | query_bind t k ih =>
      rcases t with n | t | d | q
      · simp [lazyImplR, lazyImpl, interp, StateT.run_bind, ih]
      · simp [lazyImplR, lazyImpl, interp, StateT.run_bind, ih]
      · rcases hc : c.lookup d with _ | v
        · simp [lazyImplR, lazyImpl, interp, StateT.run_bind, ih, hc]
        · simp [lazyImplR, lazyImpl, interp, StateT.run_bind, ih, hc]
      · simp [lazyImplR, lazyImpl, interp, StateT.run_bind, ih]

/-- `lazyRun` is the one-step lazy handler started from the empty cache. -/
theorem lazyRun_eq (hI : QueryImpl hspec Id) (P : OracleComp (RSpec gspec D V hspec) α) :
    lazyRun hI P = (simulateQ (lazyImpl hI) P).run' [] := by
  unfold lazyRun lazyRes
  simp only [StateT.run'_eq, simulateQ_map]
  rw [simulateQ_interp_lazyImplR]

end Compose

/-! ## Lazy = eager under an arbitrary outer handler -/

/-- A table overlaid by a cache. -/
def overlay [DecidableEq D] (c : List (D × V)) (g : D → V) (d : D) : V :=
  (c.lookup d).getD (g d)

@[simp] theorem overlay_nil [DecidableEq D] (g : D → V) : overlay ([] : List (D × V)) g = g := by
  funext d
  simp [overlay]

theorem overlay_cons [DecidableEq D] (c : List (D × V)) (g : D → V) (d : D) (v : V)
    (hc : c.lookup d = none) :
    overlay ((d, v) :: c) g = overlay c (Function.update g d v) := by
  funext d'
  unfold overlay
  by_cases h : d' = d
  · subst h; simp [hc]
  · have : (d' == d) = false := by simpa using h
    simp [List.lookup_cons, this, Function.update_of_ne h]

section LazyEager

variable [DecidableEq D] [Fintype D] [SampleableType V] [Tables.UniformSampler D V]

/-- **Lazy = eager, stateful game, cache-parametrised.**  `G` is any handler of the adversary's
interface `unifSpec + gspec` in `StateT σ ProbComp` that treats a lifted uniform sample of `V`
as that sample (`hG`; true of every game handler that forwards `unifSpec`). -/
theorem evalDist_lazyImpl_eq_table {σ : Type} [MeasurableSpace (α × σ)]
    (hI : QueryImpl hspec Id)
    (G : QueryImpl (unifSpec + gspec) (StateT σ ProbComp))
    (hG : ∀ s, (simulateQ G (liftM ($ᵗ V : ProbComp V) : OracleComp (unifSpec + gspec) V)).run s =
      (fun v => (v, s)) <$> ($ᵗ V : ProbComp V))
    (P : OracleComp (RSpec gspec D V hspec) α) (c : List (D × V)) (s : σ) :
    𝒟[(simulateQ G ((simulateQ (lazyImpl hI) P).run' c)).run s] =
      𝒟[Tables.uniformTable D V >>= fun g =>
        (simulateQ G (simulateQ (tblImpl hI (overlay c g)) P)).run s] := by
  induction P using OracleComp.inductionOn generalizing c s with
  | pure a =>
      simp only [simulateQ_pure, StateT.run'_eq, StateT.run_pure, map_pure]
      rw [OracleComp.evalDist_bind_const]
  | query_bind t k ih =>
      rcases t with n | t | d | q
      · have hL : (simulateQ G ((simulateQ (lazyImpl hI)
              (liftM ((RSpec gspec D V hspec).query (.inl n)) >>= k)).run' c)).run s =
            (G (.inl n)).run s >>= fun p =>
              (simulateQ G ((simulateQ (lazyImpl hI) (k p.1)).run' c)).run p.2 := by
          simp [lazyImpl, StateT.run'_eq, StateT.run_bind]
        have hR : ∀ h : D → V, (simulateQ G (simulateQ (tblImpl hI h)
              (liftM ((RSpec gspec D V hspec).query (.inl n)) >>= k))).run s =
            (G (.inl n)).run s >>= fun p =>
              (simulateQ G (simulateQ (tblImpl hI h) (k p.1))).run p.2 := by
          intro h
          simp [tblImpl, StateT.run_bind]
        rw [hL]
        simp_rw [hR]
        exact (evalDist_bind_congr_of_support _ _ _ fun p _ => ih p.1 c p.2).trans
          (OracleComp.evalDist_bind_bind_swap _ _ _)
      · have hL : (simulateQ G ((simulateQ (lazyImpl hI)
              (liftM ((RSpec gspec D V hspec).query (.inr (.inl t))) >>= k)).run' c)).run s =
            (G (.inr t)).run s >>= fun p =>
              (simulateQ G ((simulateQ (lazyImpl hI) (k p.1)).run' c)).run p.2 := by
          simp [lazyImpl, StateT.run'_eq, StateT.run_bind]
        have hR : ∀ h : D → V, (simulateQ G (simulateQ (tblImpl hI h)
              (liftM ((RSpec gspec D V hspec).query (.inr (.inl t))) >>= k))).run s =
            (G (.inr t)).run s >>= fun p =>
              (simulateQ G (simulateQ (tblImpl hI h) (k p.1))).run p.2 := by
          intro h
          simp [tblImpl, StateT.run_bind]
        rw [hL]
        simp_rw [hR]
        exact (evalDist_bind_congr_of_support _ _ _ fun p _ => ih p.1 c p.2).trans
          (OracleComp.evalDist_bind_bind_swap _ _ _)
      · have hR : ∀ h : D → V, (simulateQ G (simulateQ (tblImpl hI h)
              (liftM ((RSpec gspec D V hspec).query (.inr (.inr (.inl d)))) >>= k))).run s =
            (simulateQ G (simulateQ (tblImpl hI h) (k (h d)))).run s := by
          intro h
          simp [tblImpl]
        simp_rw [hR]
        rcases hc : c.lookup d with _ | v
        · have hL : (simulateQ G ((simulateQ (lazyImpl hI)
                (liftM ((RSpec gspec D V hspec).query (.inr (.inr (.inl d)))) >>= k)).run' c)).run s =
              ($ᵗ V : ProbComp V) >>= fun v =>
                (simulateQ G ((simulateQ (lazyImpl hI) (k v)).run' ((d, v) :: c))).run s := by
            simp [lazyImpl, StateT.run'_eq, StateT.run_bind, hc, hG]
          rw [hL]
          set ψ : (D → V) → ProbComp (α × σ) := fun g =>
            (simulateQ G (simulateQ (tblImpl hI (overlay c g)) (k (overlay c g d)))).run s with hψ
          have hfun : ∀ v : V, (fun g : D → V =>
                (simulateQ G (simulateQ (tblImpl hI (overlay ((d, v) :: c) g)) (k v))).run s) =
              fun g => ψ (Function.update g d v) := by
            intro v
            funext g
            have hv : overlay c (Function.update g d v) d = v := by simp [overlay, hc]
            simp only [hψ, overlay_cons c g d v hc, hv]
          refine (evalDist_bind_congr_of_support _ _ _ fun v _ =>
            (ih v ((d, v) :: c) s).trans (by rw [hfun v])).trans ?_
          exact Tables.evalDist_resample_cell d ψ
        · have hL : (simulateQ G ((simulateQ (lazyImpl hI)
                (liftM ((RSpec gspec D V hspec).query (.inr (.inr (.inl d)))) >>= k)).run' c)).run s =
              (simulateQ G ((simulateQ (lazyImpl hI) (k v)).run' c)).run s := by
            simp [lazyImpl, StateT.run'_eq, StateT.run_bind, hc]
          rw [hL, ih v c s]
          simp [overlay, hc]
      · have hL : (simulateQ G ((simulateQ (lazyImpl hI)
              (liftM ((RSpec gspec D V hspec).query (.inr (.inr (.inr q)))) >>= k)).run' c)).run s =
            (simulateQ G ((simulateQ (lazyImpl hI) (k (hI q))).run' c)).run s := by
          simp [lazyImpl, StateT.run'_eq, StateT.run_bind]
        have hR : ∀ h : D → V, (simulateQ G (simulateQ (tblImpl hI h)
              (liftM ((RSpec gspec D V hspec).query (.inr (.inr (.inr q)))) >>= k))).run s =
            (simulateQ G (simulateQ (tblImpl hI h) (k (hI q)))).run s := by
          intro h
          simp [tblImpl]
        rw [hL]
        simp_rw [hR]
        exact ih (hI q) c s

/-- **Lazy = eager, stateful game.**  For every game handler `G` (forwarding uniform samples,
`hG`) and initial game state `s`: the lazy adversary `lazyRun hI P` under `G` has the law of the
eager adversary `simulateQ (tblImpl hI g) P` under `G`, for a uniform table `g`. -/
theorem evalDist_lazyRun_eq_table {σ : Type} [MeasurableSpace (α × σ)]
    (hI : QueryImpl hspec Id)
    (G : QueryImpl (unifSpec + gspec) (StateT σ ProbComp))
    (hG : ∀ s, (simulateQ G (liftM ($ᵗ V : ProbComp V) : OracleComp (unifSpec + gspec) V)).run s =
      (fun v => (v, s)) <$> ($ᵗ V : ProbComp V))
    (P : OracleComp (RSpec gspec D V hspec) α) (s : σ) :
    𝒟[(simulateQ G (lazyRun hI P)).run s] =
      𝒟[Tables.uniformTable D V >>= fun g =>
        (simulateQ G (simulateQ (tblImpl hI g) P)).run s] := by
  rw [lazyRun_eq]
  simpa using evalDist_lazyImpl_eq_table hI G hG P [] s

/-- **Lazy = eager, stateless game**, cache-parametrised. -/
theorem evalDist_lazyImpl_eq_table' [MeasurableSpace α]
    (hI : QueryImpl hspec Id)
    (G : QueryImpl (unifSpec + gspec) ProbComp)
    (hG : simulateQ G (liftM ($ᵗ V : ProbComp V) : OracleComp (unifSpec + gspec) V) =
      ($ᵗ V : ProbComp V))
    (P : OracleComp (RSpec gspec D V hspec) α) (c : List (D × V)) :
    𝒟[simulateQ G ((simulateQ (lazyImpl hI) P).run' c)] =
      𝒟[Tables.uniformTable D V >>= fun g =>
        simulateQ G (simulateQ (tblImpl hI (overlay c g)) P)] := by
  induction P using OracleComp.inductionOn generalizing c with
  | pure a =>
      simp only [simulateQ_pure, StateT.run'_eq, StateT.run_pure, map_pure]
      rw [OracleComp.evalDist_bind_const]
  | query_bind t k ih =>
      rcases t with n | t | d | q
      · have hL : simulateQ G ((simulateQ (lazyImpl hI)
              (liftM ((RSpec gspec D V hspec).query (.inl n)) >>= k)).run' c) =
            G (.inl n) >>= fun u => simulateQ G ((simulateQ (lazyImpl hI) (k u)).run' c) := by
          simp [lazyImpl, StateT.run'_eq, StateT.run_bind]
        have hR : ∀ h : D → V, simulateQ G (simulateQ (tblImpl hI h)
              (liftM ((RSpec gspec D V hspec).query (.inl n)) >>= k)) =
            G (.inl n) >>= fun u => simulateQ G (simulateQ (tblImpl hI h) (k u)) := by
          intro h
          simp [tblImpl]
        rw [hL]
        simp_rw [hR]
        exact (evalDist_bind_congr_of_support _ _ _ fun u _ => ih u c).trans
          (OracleComp.evalDist_bind_bind_swap _ _ _)
      · have hL : simulateQ G ((simulateQ (lazyImpl hI)
              (liftM ((RSpec gspec D V hspec).query (.inr (.inl t))) >>= k)).run' c) =
            G (.inr t) >>= fun u => simulateQ G ((simulateQ (lazyImpl hI) (k u)).run' c) := by
          simp [lazyImpl, StateT.run'_eq, StateT.run_bind]
        have hR : ∀ h : D → V, simulateQ G (simulateQ (tblImpl hI h)
              (liftM ((RSpec gspec D V hspec).query (.inr (.inl t))) >>= k)) =
            G (.inr t) >>= fun u => simulateQ G (simulateQ (tblImpl hI h) (k u)) := by
          intro h
          simp [tblImpl]
        rw [hL]
        simp_rw [hR]
        exact (evalDist_bind_congr_of_support _ _ _ fun u _ => ih u c).trans
          (OracleComp.evalDist_bind_bind_swap _ _ _)
      · have hR : ∀ h : D → V, simulateQ G (simulateQ (tblImpl hI h)
              (liftM ((RSpec gspec D V hspec).query (.inr (.inr (.inl d)))) >>= k)) =
            simulateQ G (simulateQ (tblImpl hI h) (k (h d))) := by
          intro h
          simp [tblImpl]
        simp_rw [hR]
        rcases hc : c.lookup d with _ | v
        · have hL : simulateQ G ((simulateQ (lazyImpl hI)
                (liftM ((RSpec gspec D V hspec).query (.inr (.inr (.inl d)))) >>= k)).run' c) =
              ($ᵗ V : ProbComp V) >>= fun v =>
                simulateQ G ((simulateQ (lazyImpl hI) (k v)).run' ((d, v) :: c)) := by
            simp [lazyImpl, StateT.run'_eq, StateT.run_bind, hc, hG]
          rw [hL]
          set ψ : (D → V) → ProbComp α := fun g =>
            simulateQ G (simulateQ (tblImpl hI (overlay c g)) (k (overlay c g d))) with hψ
          have hfun : ∀ v : V, (fun g : D → V =>
                simulateQ G (simulateQ (tblImpl hI (overlay ((d, v) :: c) g)) (k v))) =
              fun g => ψ (Function.update g d v) := by
            intro v
            funext g
            have hv : overlay c (Function.update g d v) d = v := by simp [overlay, hc]
            simp only [hψ, overlay_cons c g d v hc, hv]
          refine (evalDist_bind_congr_of_support _ _ _ fun v _ =>
            (ih v ((d, v) :: c)).trans (by rw [hfun v])).trans ?_
          exact Tables.evalDist_resample_cell d ψ
        · have hL : simulateQ G ((simulateQ (lazyImpl hI)
                (liftM ((RSpec gspec D V hspec).query (.inr (.inr (.inl d)))) >>= k)).run' c) =
              simulateQ G ((simulateQ (lazyImpl hI) (k v)).run' c) := by
            simp [lazyImpl, StateT.run'_eq, StateT.run_bind, hc]
          rw [hL, ih v c]
          simp [overlay, hc]
      · have hL : simulateQ G ((simulateQ (lazyImpl hI)
              (liftM ((RSpec gspec D V hspec).query (.inr (.inr (.inr q)))) >>= k)).run' c) =
            simulateQ G ((simulateQ (lazyImpl hI) (k (hI q))).run' c) := by
          simp [lazyImpl, StateT.run'_eq, StateT.run_bind]
        have hR : ∀ h : D → V, simulateQ G (simulateQ (tblImpl hI h)
              (liftM ((RSpec gspec D V hspec).query (.inr (.inr (.inr q)))) >>= k)) =
            simulateQ G (simulateQ (tblImpl hI h) (k (hI q))) := by
          intro h
          simp [tblImpl]
        rw [hL]
        simp_rw [hR]
        exact ih (hI q) c

/-- **Lazy = eager, stateless game.** -/
theorem evalDist_lazyRun_eq_table' [MeasurableSpace α]
    (hI : QueryImpl hspec Id)
    (G : QueryImpl (unifSpec + gspec) ProbComp)
    (hG : simulateQ G (liftM ($ᵗ V : ProbComp V) : OracleComp (unifSpec + gspec) V) =
      ($ᵗ V : ProbComp V))
    (P : OracleComp (RSpec gspec D V hspec) α) :
    𝒟[simulateQ G (lazyRun hI P)] =
      𝒟[Tables.uniformTable D V >>= fun g => simulateQ G (simulateQ (tblImpl hI g) P)] := by
  rw [lazyRun_eq]
  simpa using evalDist_lazyImpl_eq_table' hI G hG P []

end LazyEager

/-! ## Resource transfer -/

section Resources

variable [DecidableEq D]

/-- Generic transfer through the cache: if the kind `K` of source queries is bounded by `n` in
`P`, the same kind is bounded by `n` in `lazyRes P` (for `K = .sec` the target queries are the
draws). -/
theorem lazyRes_bound (K : Kind) (P : OracleComp (RSpec gspec D V hspec) α) (n : ℕ)
    (h : IsQueryBoundP P (fun t => kind t = K) n) :
    IsQueryBoundP (lazyRes P) (fun t => kind t = K) n := by
  unfold lazyRes
  rw [StateT.run'_eq, isQueryBoundP_map_iff]
  refine IsQueryBoundP.simulateQ_run_of_step h (fun t ht s => ?_) (fun t ht s => ?_) []
  · rcases t with n | t | d | q
    · simp [lazyImplR]
    · simp [lazyImplR]
    · simp only [kind] at ht
      subst ht
      rcases hc : s.lookup d with _ | v
      · rw [lazyImplR_sec_run_miss d s hc]
        simp [kind]
      · rw [lazyImplR_sec_run_hit d s v hc]
        simp
    · simp [lazyImplR]
  · rcases t with n | t | d | q
    · simp [lazyImplR, kind] at ht ⊢
      simpa [kind] using ht
    · simp [lazyImplR, kind] at ht ⊢
      simpa [kind] using ht
    · simp only [kind] at ht
      rcases hc : s.lookup d with _ | v
      · rw [lazyImplR_sec_run_miss d s hc]
        simp [kind]
        exact fun h => ht h
      · rw [lazyImplR_sec_run_hit d s v hc]
        simp
    · simp [lazyImplR, kind] at ht ⊢
      simpa [kind] using ht

/-- Fresh draws of `lazyRes P` are bounded by the secret reads of `P`. -/
theorem lazyRes_bound_draws (P : OracleComp (RSpec gspec D V hspec) α) (n : ℕ)
    (h : IsQueryBoundP P (fun t => kind t = .sec) n) :
    IsQueryBoundP (lazyRes P) (fun t => kind t = .sec) n := lazyRes_bound .sec P n h

/-- Game queries pass through the cache one for one. -/
theorem lazyRes_bound_game (P : OracleComp (RSpec gspec D V hspec) α) (n : ℕ)
    (h : IsQueryBoundP P (fun t => kind t = .game) n) :
    IsQueryBoundP (lazyRes P) (fun t => kind t = .game) n := lazyRes_bound .game P n h

/-- Hash evaluations pass through the cache one for one. -/
theorem lazyRes_bound_hash (P : OracleComp (RSpec gspec D V hspec) α) (n : ℕ)
    (h : IsQueryBoundP P (fun t => kind t = .hash) n) :
    IsQueryBoundP (lazyRes P) (fun t => kind t = .hash) n := lazyRes_bound .hash P n h

/-- Game queries of the interpreted adversary: one per game query of the resource-explicit
program (draws and hash evaluations make none). -/
theorem interp_gameBound [SampleableType V] (hI : QueryImpl hspec Id)
    (R : OracleComp (RSpec gspec Unit V hspec) α) (n : ℕ)
    (h : IsQueryBoundP R (fun t => kind t = .game) n) :
    IsQueryBoundP (simulateQ (interp hI) R) (fun i => i.isRight = true) n := by
  refine IsQueryBoundP.simulateQ_of_step h (fun t ht => ?_) (fun t ht => ?_)
  · rcases t with n | t | d | q
    · simp [kind] at ht
    · simp [interp]
    · simp [kind] at ht
    · simp [kind] at ht
  · rcases t with n | t | d | q
    · simp [interp]
    · simp [kind] at ht
    · simp only [interp]
      exact isQueryBoundP_liftM_isRight (hs := gspec) ($ᵗ V : ProbComp V)
    · simp [interp]

/-- Game queries of `lazyRun hI P` are bounded by the game queries of `P`. -/
theorem lazyRun_gameBound [SampleableType V] (hI : QueryImpl hspec Id)
    (P : OracleComp (RSpec gspec D V hspec) α) (n : ℕ)
    (h : IsQueryBoundP P (fun t => kind t = .game) n) :
    IsQueryBoundP (lazyRun hI P) (fun i => i.isRight = true) n :=
  interp_gameBound hI _ n (lazyRes_bound_game P n h)

end Resources

end Lazy
end Reduction

#print axioms Reduction.Lazy.simulateQ_interp_lazyImplR
#print axioms Reduction.Lazy.evalDist_lazyRun_eq_table
#print axioms Reduction.Lazy.evalDist_lazyRun_eq_table'
#print axioms Reduction.Lazy.lazyRes_bound
#print axioms Reduction.Lazy.lazyRun_gameBound
