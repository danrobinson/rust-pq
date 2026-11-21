import Ideal.Realize.Port
import Reduction.Open.MsgV
import Reduction.Open.Prf

/-!
# Generic layer of the `PRF` / `PRF_msg` realisers: port harness, port interpretation, lazy cache

* `instImpl_liftM`, `cEmb`, `instImpl_cEmb`: probabilistic computations and programs over
  `CSpec = unifSpec + hS` read inside `unifSpec + (hS + X)`, and their instantiation at a table.
* `harnP port so`: the harness handler by which an open program runs a forger WITH compression
  port (sampling forwarded, a compression query becomes the program's own `port q`, signing by
  `so`); `harnP_fusion`: under an interpretation `φ` that answers `port q` by `g q`, the run is the
  ordinary harness run (`runForger`/`runForgerSig` shape) of the forger with its port answered
  by `g`.  `sigSignOracle_fusion`, `harnessSignOracle_fusion`: the two signing oracles.
* `portR g`: interpretation of an open program over `RSpec (hS + G) D V H` answering the port by
  `g` (everything else forwarded); `lazyImplR_portR`: it commutes with the lazy cache.
* `interpC hC`: interpretation of the resource-explicit program, hash queries issued as
  compression programs `hC`; `interp_portR`, `lazyRun_portR`: answering the port and the
  compression queries by `g` gives `lazyRun hI` of the port-answered program, if `hC` computes
  `hI` at `g`.
* `liftP`, `lazyRes_bound_liftP`: query bounds on game / hash queries pass through the cache.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security

namespace Ideal.Realize.Msg

open Reduction Reduction.Lazy

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! ## Instantiation lemmas -/

section Inst

variable {ι : Type} {X : OracleSpec ι} {α : Type}

theorem instImpl_liftM (g : CF St Blk) (ob : ProbComp α) :
    simulateQ (instImpl g) (liftM ob : OracleComp (unifSpec + (hS St Blk + X)) α) =
      (liftM ob : OracleComp (unifSpec + X) α) := by
  induction ob using OracleComp.inductionOn with
  | pure a => simp
  | query_bind n k ih =>
    rw [liftM_bind, liftM_bind, simulateQ_bind]
    simp only [ih]
    have : simulateQ (instImpl g)
        (liftM (liftM (unifSpec.query n) : ProbComp _) :
          OracleComp (unifSpec + (hS St Blk + X)) _) =
        (liftM (liftM (unifSpec.query n) : ProbComp _) : OracleComp (unifSpec + X) _) := by
      show simulateQ (instImpl g) (liftM ((unifSpec + (hS St Blk + X)).query (.inl n))) = _
      rw [simulateQ_spec_query]
      rfl
    rw [this]

/-- A program over uniform bits and compression queries, read inside `unifSpec + (hS + X)`. -/
def cEmb : QueryImpl CSpec (OracleComp (unifSpec + (hS St Blk + X)))
  | .inl n => (liftM ((unifSpec + (hS St Blk + X)).query (.inl n)) :
      OracleComp (unifSpec + (hS St Blk + X)) _)
  | .inr q => (liftM ((unifSpec + (hS St Blk + X)).query (.inr (.inl q))) :
      OracleComp (unifSpec + (hS St Blk + X)) _)

theorem instImpl_cEmb (g : CF St Blk) (oa : OracleComp CSpec α) :
    simulateQ (instImpl g) (simulateQ (cEmb (X := X)) oa) =
      (liftM (simulateQ (instImpl₀ g) oa) : OracleComp (unifSpec + X) α) := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    rw [simulateQ_bind, simulateQ_bind, simulateQ_bind, liftM_bind]
    simp only [ih, simulateQ_spec_query]
    rcases t with n | q
    · have h1 : simulateQ (instImpl g) (cEmb (X := X) (.inl n)) =
          (liftM (liftM (unifSpec.query n) : ProbComp _) : OracleComp (unifSpec + X) _) := by
        show simulateQ (instImpl g) (liftM ((unifSpec + (hS St Blk + X)).query (.inl n))) = _
        rw [simulateQ_spec_query]
        rfl
      rw [h1]
      rfl
    · have h1 : simulateQ (instImpl g) (cEmb (X := X) (.inr q)) = pure (g q) := by
        show simulateQ (instImpl g) (liftM ((unifSpec + (hS St Blk + X)).query (.inr (.inl q)))) = _
        rw [simulateQ_spec_query]
        rfl
      rw [h1, pure_bind]
      show _ = liftM (pure (g q) : ProbComp St) >>= _
      rw [liftM_pure, pure_bind]

/-- Compression queries of an embedded `CSpec` program: those of the program. -/
theorem cEmb_bound (oa : OracleComp CSpec α) (n : ℕ)
    (h : IsQueryBoundP oa (fun i => i.isRight = true) n)
    (q : ℕ ⊕ ((St × Blk) ⊕ ι) → Prop) [DecidablePred q]
    (hq : ∀ c : St × Blk, q (.inr (.inl c))) (hq0 : ∀ m : ℕ, ¬ q (.inl m)) :
    IsQueryBoundP (simulateQ (cEmb (X := X)) oa) q n := by
  refine IsQueryBoundP.simulateQ_of_step h (fun t ht => ?_) (fun t ht => ?_)
  · rcases t with m | c
    · simp at ht
    · exact (isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos
  · rcases t with m | c
    · exact (isQueryBoundP_query_iff _ _ _).2 fun h' => absurd h' (hq0 m)
    · simp at ht

end Inst

/-! ## The port harness -/

section Harness

variable {ι ι' : Type} {X : OracleSpec ι} {Y : OracleSpec ι'} {σ Sig β : Type}

/-- The harness by which an open program over `unifSpec + X` runs a forger WITH compression port:
sampling forwarded, a compression query `q` becomes the program `port q`, signing by `so`. -/
def harnP (port : St × Blk → OracleComp (unifSpec + X) St)
    (so : QueryImpl (List Byte →ₒ Sig) (StateT σ (OracleComp (unifSpec + X)))) :
    QueryImpl (FSpecP Sig) (StateT σ (OracleComp (unifSpec + X)))
  | .inl n => (monadLift (liftM ((unifSpec + X).query (.inl n)) : OracleComp (unifSpec + X) _) :
      StateT σ (OracleComp (unifSpec + X)) _)
  | .inr (.inl q) => (monadLift (port q) : StateT σ (OracleComp (unifSpec + X)) St)
  | .inr (.inr m) => so m

/-- **Fusion for the port harness.**  Under an interpretation `φ` forwarding sampling and
answering `port q` by `g q`, the port run is the ordinary harness run of the forger with its port
answered by `g`. -/
theorem harnP_fusion (φ : QueryImpl (unifSpec + X) (OracleComp (unifSpec + Y))) (g : CF St Blk)
    (hu : ∀ n, φ (.inl n) = (liftM ((unifSpec + Y).query (.inl n)) : OracleComp (unifSpec + Y) _))
    (port : St × Blk → OracleComp (unifSpec + X) St)
    (hp : ∀ q, simulateQ φ (port q) = pure (g q))
    (so : QueryImpl (List Byte →ₒ Sig) (StateT σ (OracleComp (unifSpec + X))))
    (so' : QueryImpl (List Byte →ₒ Sig) (StateT σ (OracleComp (unifSpec + Y))))
    (hso : ∀ m s, simulateQ φ ((so m).run s) = (so' m).run s)
    (oa : OracleComp (FSpecP Sig) β) (s : σ) :
    simulateQ φ ((simulateQ (harnP port so) oa).run s) =
      (simulateQ ((QueryImpl.ofLift unifSpec (OracleComp (unifSpec + Y))).liftTarget
          (StateT σ (OracleComp (unifSpec + Y))) + so')
        (simulateQ (instImpl g) oa)).run s := by
  refine (simulateQ_run_simulateQ_eq_of_step (instImpl g) _ (harnP port so) φ
    (fun t s => ?_) oa s).symm
  rcases t with n | q | m
  · simp only [instImpl, harnP, StateT.run_monadLift, simulateQ_bind, simulateQ_pure]
    rw [simulateQ_spec_query]
    simp only [QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply, StateT.run_monadLift,
      monadLift_self]
    rw [simulateQ_spec_query, hu]
    rfl
  · simp only [instImpl, harnP, StateT.run_monadLift, simulateQ_bind, simulateQ_pure]
    simp [hp]
  · simp only [instImpl, harnP]
    rw [simulateQ_spec_query]
    exact (hso m s).symm

theorem sigSignOracle_fusion {vp : ValidatedParams} {prims : Primitives vp.params}
    (φ : QueryImpl (unifSpec + X) (OracleComp (unifSpec + Y)))
    (sign : List Byte → OracleComp (unifSpec + X) (GeneralScheme.SignatureCore vp prims.core))
    (m : List Byte) (s : SigLog vp prims) :
    simulateQ φ ((sigSignOracle sign m).run s) =
      (sigSignOracle (fun m => simulateQ φ (sign m)) m).run s := by
  simp [sigSignOracle, run_appendLog_apply]

theorem harnessSignOracle_fusion {vp : ValidatedParams} {prims : Primitives vp.params}
    (φ : QueryImpl (unifSpec + X) (OracleComp (unifSpec + Y)))
    (sign : List Byte → OracleComp (unifSpec + X) (GeneralScheme.SignatureCore vp prims.core))
    (m : List Byte) (s : List (List Byte)) :
    simulateQ φ ((harnessSignOracle (vp := vp) (prims := prims) sign m).run s) =
      (harnessSignOracle (vp := vp) (prims := prims) (fun m => simulateQ φ (sign m)) m).run s := by
  simp [harnessSignOracle]

end Harness

/-! ## Answering the port of an open program -/

section PortR

variable {ι κ : Type} {G : OracleSpec ι} {H : OracleSpec κ} {D V α : Type}

/-- Answer the port (`hS` part of the game slot) of an open program by `g`; forward the rest. -/
def portR (g : CF St Blk) : QueryImpl (RSpec (hS St Blk + G) D V H) (OracleComp (RSpec G D V H))
  | .inl n => (liftM ((RSpec G D V H).query (.inl n)) : OracleComp (RSpec G D V H) _)
  | .inr (.inl (.inl q)) => pure (g q)
  | .inr (.inl (.inr t)) => (liftM ((RSpec G D V H).query (.inr (.inl t))) :
      OracleComp (RSpec G D V H) _)
  | .inr (.inr t) => (liftM ((RSpec G D V H).query (.inr (.inr t))) :
      OracleComp (RSpec G D V H) _)

theorem portR_liftM (g : CF St Blk) (ob : ProbComp α) :
    simulateQ (portR (G := G) (H := H) (D := D) (V := V) g)
        (liftM ob : OracleComp (RSpec (hS St Blk + G) D V H) α) =
      (liftM ob : OracleComp (RSpec G D V H) α) := by
  induction ob using OracleComp.inductionOn with
  | pure a => simp
  | query_bind n k ih =>
    rw [liftM_bind, liftM_bind, simulateQ_bind]
    simp only [ih]
    have : simulateQ (portR (G := G) (H := H) (D := D) (V := V) g)
        (liftM (liftM (unifSpec.query n) : ProbComp _) :
          OracleComp (RSpec (hS St Blk + G) D V H) _) =
        (liftM (liftM (unifSpec.query n) : ProbComp _) : OracleComp (RSpec G D V H) _) := by
      show simulateQ (portR g) (liftM ((RSpec (hS St Blk + G) D V H).query (.inl n))) = _
      rw [simulateQ_spec_query]
      rfl
    rw [this]

/-- The port interpretation commutes with the lazy cache. -/
theorem lazyImplR_portR [DecidableEq D] (g : CF St Blk)
    (P : OracleComp (RSpec (hS St Blk + G) D V H) α) (c : List (D × V)) :
    (simulateQ lazyImplR (simulateQ (portR g) P)).run c =
      simulateQ (portR g) ((simulateQ lazyImplR P).run c) := by
  refine simulateQ_run_simulateQ_eq_of_step (portR g) lazyImplR lazyImplR (portR g)
    (fun t s => ?_) P c
  rcases t with n | (q | t) | (d | t)
  · simp only [portR, lazyImplR]
    rw [simulateQ_spec_query]
    simp [portR]; rfl
  · simp [portR, lazyImplR]
  · simp only [portR, lazyImplR]
    rw [simulateQ_spec_query]
    simp [portR]; rfl
  · simp only [portR]
    rw [simulateQ_spec_query]
    rcases hc : s.lookup d with _ | v
    · rw [lazyImplR_sec_run_miss d s hc, lazyImplR_sec_run_miss d s hc]
      simp [portR]
    · rw [lazyImplR_sec_run_hit d s v hc, lazyImplR_sec_run_hit d s v hc]
      simp
  · simp only [portR, lazyImplR]
    rw [simulateQ_spec_query]
    simp [portR]; rfl

theorem lazyRes_portR [DecidableEq D] (g : CF St Blk)
    (P : OracleComp (RSpec (hS St Blk + G) D V H) α) :
    lazyRes (simulateQ (portR g) P) = simulateQ (portR g) (lazyRes P) := by
  unfold lazyRes
  rw [StateT.run'_eq, StateT.run'_eq, lazyImplR_portR, simulateQ_map]

/-- Interpretation of a resource-explicit program with a port: uniform bits, port and game
queries forwarded, a draw is a uniform sample, a hash query is the compression program `hC q`. -/
noncomputable def interpC [SampleableType V] (hC : QueryImpl H (OracleComp CSpec)) :
    QueryImpl (RSpec (hS St Blk + G) Unit V H) (OracleComp (unifSpec + (hS St Blk + G)))
  | .inl n => (liftM ((unifSpec + (hS St Blk + G)).query (.inl n)) :
      OracleComp (unifSpec + (hS St Blk + G)) _)
  | .inr (.inl t) => (liftM ((unifSpec + (hS St Blk + G)).query (.inr t)) :
      OracleComp (unifSpec + (hS St Blk + G)) _)
  | .inr (.inr (.inl _)) => (liftM ($ᵗ V : ProbComp V) : OracleComp (unifSpec + (hS St Blk + G)) V)
  | .inr (.inr (.inr q)) => simulateQ (cEmb (X := G)) (hC q)

theorem interp_portR [SampleableType V] (g : CF St Blk) (hI : QueryImpl H Id)
    (hC : QueryImpl H (OracleComp CSpec))
    (hH : ∀ q, simulateQ (instImpl₀ g) (hC q) = pure (f := ProbComp) (α := H.Range q) (hI q))
    (R : OracleComp (RSpec (hS St Blk + G) Unit V H) α) :
    simulateQ (interp hI) (simulateQ (portR g) R) =
      simulateQ (instImpl g) (simulateQ (interpC hC) R) := by
  refine simulateQ_comm_of_step _ _ _ _ (fun t => ?_) R
  rcases t with n | (q | t) | (d | t)
  · simp only [portR, interpC]
    rw [simulateQ_spec_query, simulateQ_spec_query]
    rfl
  · simp only [portR, interpC, simulateQ_pure]
    rw [simulateQ_spec_query]
    rfl
  · simp only [portR, interpC]
    rw [simulateQ_spec_query, simulateQ_spec_query]
    rfl
  · simp only [portR, interpC]
    rw [simulateQ_spec_query, instImpl_liftM]
    rfl
  · simp only [portR, interpC]
    rw [simulateQ_spec_query, instImpl_cEmb, hH, liftM_pure]
    rfl

/-- **Lazy run of a port-answered open program**: it is the instantiation at `g` of ONE
program, `interpC hC (lazyRes P)`, if `hC` computes `hI` at `g`. -/
theorem lazyRun_portR [DecidableEq D] [SampleableType V] (g : CF St Blk) (hI : QueryImpl H Id)
    (hC : QueryImpl H (OracleComp CSpec))
    (hH : ∀ q, simulateQ (instImpl₀ g) (hC q) = pure (f := ProbComp) (α := H.Range q) (hI q))
    (P : OracleComp (RSpec (hS St Blk + G) D V H) α) :
    lazyRun hI (simulateQ (portR g) P) =
      simulateQ (instImpl g) (simulateQ (interpC hC) (lazyRes P)) := by
  unfold lazyRun
  rw [lazyRes_portR, interp_portR g hI hC hH]

end PortR

/-! ## Query bounds through the cache -/

section Bounds

variable {ι κ : Type} {G : OracleSpec ι} {H : OracleSpec κ} {D V α : Type}

/-- A predicate on the game and hash queries of an open program (never on uniform bits or
secret reads / draws). -/
def liftP (pg : ι → Prop) (ph : κ → Prop) {D : Type} : ℕ ⊕ (ι ⊕ (D ⊕ κ)) → Prop
  | .inl _ => False
  | .inr (.inl t) => pg t
  | .inr (.inr (.inl _)) => False
  | .inr (.inr (.inr q)) => ph q

instance (pg : ι → Prop) (ph : κ → Prop) [DecidablePred pg] [DecidablePred ph] {D : Type} :
    DecidablePred (liftP pg ph (D := D)) := fun t => by
  rcases t with n | t | d | q <;> simp only [liftP] <;> infer_instance

/-- Bounds on game / hash queries pass through the lazy cache. -/
theorem lazyRes_bound_liftP [DecidableEq D] (pg : ι → Prop) (ph : κ → Prop) [DecidablePred pg]
    [DecidablePred ph] (P : OracleComp (RSpec G D V H) α) (n : ℕ)
    (h : IsQueryBoundP P (liftP pg ph) n) :
    IsQueryBoundP (lazyRes P) (liftP pg ph) n := by
  unfold lazyRes
  rw [StateT.run'_eq, isQueryBoundP_map_iff]
  refine IsQueryBoundP.simulateQ_run_of_step h (fun t ht s => ?_) (fun t ht s => ?_) []
  · rcases t with n | t | d | q
    · simp [liftP] at ht
    · simp only [lazyImplR, StateT.run_monadLift]
      exact isQueryBoundP_bind (m := 0) ((isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos)
        fun x _ => isQueryBoundP_pure _ _ _
    · simp [liftP] at ht
    · simp only [lazyImplR, StateT.run_monadLift]
      exact isQueryBoundP_bind (m := 0) ((isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos)
        fun x _ => isQueryBoundP_pure _ _ _
  · rcases t with n | t | d | q
    · simp only [lazyImplR, StateT.run_monadLift]
      exact isQueryBoundP_bind_zero _ _ ((isQueryBoundP_query_iff _ _ _).2 fun h => by
        simp [liftP] at h) fun x => isQueryBoundP_pure _ _ _
    · simp only [lazyImplR, StateT.run_monadLift]
      exact isQueryBoundP_bind_zero _ _ ((isQueryBoundP_query_iff _ _ _).2 fun h' => (ht h').elim)
        fun x => isQueryBoundP_pure _ _ _
    · rcases hc : s.lookup d with _ | v
      · rw [lazyImplR_sec_run_miss d s hc]
        exact isQueryBoundP_bind_zero _ _ ((isQueryBoundP_query_iff _ _ _).2 fun h => by
          simp [liftP] at h) fun x => isQueryBoundP_pure _ _ _
      · rw [lazyImplR_sec_run_hit d s v hc]
        exact isQueryBoundP_pure _ _ _
    · simp only [lazyImplR, StateT.run_monadLift]
      exact isQueryBoundP_bind_zero _ _ ((isQueryBoundP_query_iff _ _ _).2 fun h' => (ht h').elim)
        fun x => isQueryBoundP_pure _ _ _

end Bounds

end Ideal.Realize.Msg

#print axioms Ideal.Realize.Msg.instImpl_cEmb
#print axioms Ideal.Realize.Msg.harnP_fusion
#print axioms Ideal.Realize.Msg.lazyImplR_portR
#print axioms Ideal.Realize.Msg.lazyRun_portR
#print axioms Ideal.Realize.Msg.lazyRes_bound_liftP
