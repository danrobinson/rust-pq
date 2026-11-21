import Integration.SlhDsaBridgeMachItsr
import PQ.Interactive.QromBridgeEvalIAdv

/-!
# The ITSR adversary as ONE interactive adversary over the port oracle

NOT part of the default target; compiled by hand like `scripts/check-integration.sh` step 3.

`itsr_iadv`: from the `PUE` family `itsrMach` (`SlhDsaBridgeMachItsr.lean`) and the compiler
`PUE.exists_iadv_qprob` (`PQ/Interactive/QromBridgeEvalIAdv.lean`): one
`IAdv LocalSig.instruments (qromSpec (EncX c) EncY) (ItsrIn _) _ _ qs (progReg …)` with at most
`q + itsrHashes Link.vp qs` port calls and at most `qs` requests, whose run against any
deterministic challenger equals `qbItsrL (internalΩ … {ω₀ with hmsg := T})` closed with that
challenger, for every `T`.  The request count is `itsrMach_games` (at most one target query per
signing query, through every wrapper layer: `WCount.compileQ/.wrap0/.wrap`).
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal PQ.Interactive PQ.QROM Quantum
open scoped ComplexOrder Kronecker

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Reduction

section generic

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]
  [Fintype prims.Y]

/-- One step of the ITSR signing harness makes at most one target query per signing query. -/
theorem itsr_step_games (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (pkSeed : prims.PkSeed) (root : prims.Y)
    (t : (unifSpec + (List Byte →ₒ GeneralScheme.SignatureCore vp prims.core)).Domain)
    (s : G2Log prims) :
    IsQueryBoundP ((((QueryImpl.ofLift unifSpec (OracleComp (Lazy.OSpec prims (Lazy.itsrG prims)))).liftTarget
          (StateT (G2Log prims) (OracleComp (Lazy.OSpec prims (Lazy.itsrG prims)))) +
        logSignOracle optRand ⟨pkSeed, root⟩ (Lazy.itsrRandomizerO pkSeed root)
          (fun m R ↦ Lazy.openSign prims (Lazy.itsrG prims) m pkSeed root R)) t).run s)
      (fun t ↦ Lazy.kind t = .game) (sgnW 1 t) := by
  cases t with
  | inl n =>
    simp only [QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply, StateT.run_monadLift]
    exact Lazy.qb_bind (fun t ↦ Lazy.kind t = .game) (m := 0)
      (Lazy.liftM_kindBound (gspec := Lazy.itsrG prims) (D := SecIdx) (V := prims.Y)
        (hspec := publicHashSpec prims.core) .game (by decide)
        (liftM (unifSpec.query n) : ProbComp _)) fun x ↦ isQueryBoundP_pure _ (x, s) _
  | inr m =>
    have hstep := Lazy.qb_bind (fun t ↦ Lazy.kind t = .game)
      (Lazy.liftM_kindBound (gspec := Lazy.itsrG prims) (D := SecIdx) (V := prims.Y)
        (hspec := publicHashSpec prims.core) .game (by decide) (optRand ⟨pkSeed, root⟩))
      fun addrnd ↦
      Lazy.qb_bind (fun t ↦ Lazy.kind t = .game)
        (Lazy.itsrRandomizerO_kindBound .game pkSeed root s m addrnd) fun R ↦
        Lazy.qb_bind (fun t ↦ Lazy.kind t = .game) (m := 0)
          (Lazy.openSign_kindBound (gspec := Lazy.itsrG prims) .game m pkSeed root R)
          fun sig ↦ isQueryBoundP_pure _ (sig, s ++ [(m, addrnd, R)]) _
    refine (by simpa [logSignOracle] using hstep : IsQueryBoundP _ _ _).mono ?_
    simp [Lazy.ind, Lazy.signB_game]

theorem keygen_gamesG (pkSeed : prims.PkSeed) :
    IsQueryBoundP (Lazy.openKeygen prims (Lazy.itsrG prims) pkSeed) (fun t ↦ Lazy.kind t = .game)
      0 :=
  (Lazy.openKeygen_kindBound .game pkSeed).mono (by simp [Lazy.ind, Lazy.keygenB_game])

end generic

section mach

variable {E : Type} [Fintype E] [DecidableEq E] (c : Caps)
  (optRand₀ : Bytes Link.vp.params.n → Bytes Link.vp.params.n → ProbComp (Bytes Link.vp.params.n))
  (pkSeedDist₀ : ProbComp (Bytes Link.vp.params.n))
  (F : PortForger (EncX c) EncY E)

abbrev sgnI (ω₀ : Ω128 c) :=
  sgnW (M := List Byte) (S := GeneralScheme.SignatureCore Link.vp (primsΩ ω₀).core) 1
abbrev sgnE (ω₀ : Ω128 c) :=
  sgnW (M := List Byte × List Byte)
    (S := Except External.Error (GeneralScheme.SignatureCore Link.vp (primsΩ ω₀).core)) 1
abbrev sgnB := sgnW (M := List Byte × List Byte) (S := Option (List Byte)) 1

/-- Signing queries of the internal forger: at most `qs`. -/
theorem qmForger_signs (ω₀ : Ω128 c) (qs : ℕ)
    (hqs : ∀ pk, CountBound isSign (F.main pk) qs) (H : EncX c → EncY)
    (pk : PublicKeyCore (primsΩ ω₀).core) :
    WCount (qw (WS (EncX c) EncY E) (sgnI c ω₀)) (qmForger c F ω₀ H pk) qs := by
  unfold qmForger
  have h0 := (countBound_iff_wCount _ _ _).1 (hqs (encodePublicKey (codecR ω₀.toRand) pk))
  have h1 : WCount (qw ((EncX c × EncY) × E) (Sum.elim (fun _ ↦ 0) sgnB))
      (F.main (encodePublicKey (codecR ω₀.toRand) pk)) qs :=
    WCount.wmono (fun t ↦ by rcases t with j | u | n | m <;> simp [isSign]) h0
  refine WCount.map (WCount.wrap0 _ (w := sgnE c ω₀) ?_ (WCount.map (WCount.wrap0 _ (w := sgnB) ?_
    (WCount.compileQ H h1)) _)) _
  · intro t
    rcases t with n | e
    · exact wCount_liftM_query _ _ le_rfl
    · simp only [Guarded.signingImpl]
      split
      · exact trivial
      · exact WCount.map (wCount_liftM_query _ _ le_rfl) _
  · intro t
    rcases t with n | m
    · exact wCount_liftM_query _ _ le_rfl
    · exact WCount.map (wCount_liftM_query _ _ le_rfl) _

/-- Game weight on the open interface. -/
abbrev gameWI (ω₀ : Ω128 c) : (Lazy.OSpec (primsΩ ω₀) (Lazy.itsrG (primsΩ ω₀))).Domain → ℕ :=
  fun t ↦ if Lazy.kind t = .game then 1 else 0

abbrev gameWU (ω₀ : Ω128 c) :
    (Lazy.RSpec (Lazy.itsrG (primsΩ ω₀)) Unit (primsΩ ω₀).Y
      (publicHashSpec (primsΩ ω₀).core)).Domain → ℕ :=
  fun t ↦ if Lazy.kind t = .game then 1 else 0

set_option maxHeartbeats 1000000 in
/-- **At most `qs` target queries** on every path of the ITSR family, for every port function. -/
theorem itsrMach_games (ω₀ : Ω128 c) (qs : ℕ) (hqs : ∀ pk, CountBound isSign (F.main pk) qs)
    (H : EncX c → EncY) :
    CountBound (isGameQ (Req := ItsrIn (primsΩ ω₀)) (Resp := (primsΩ ω₀).Y))
      (itsrMach c optRand₀ pkSeedDist₀ F ω₀ H) qs := by
  refine (countBound_iff_wCount _ _ _).2 (WCount.wmono (w' := qw (WS (EncX c) EncY E)
    (fun t ↦ if t.isRight = true then 1 else 0)) (fun t ↦ by
      rcases t with j | n | r <;> simp [isGameQ]) ?_)
  unfold itsrMach qLazyRun
  refine WCount.wrap0 _ (w := gameWU c ω₀) ?_ (WCount.map ?_ _)
  · intro t
    rcases t with n | t | d | hq'
    · exact wCount_liftM_query _ _ (by simp [Lazy.kind, gameWU])
    · exact wCount_liftM_query _ _ (by simp [Lazy.kind, gameWU])
    · exact (wCount_of_isQueryBoundP _ _ _ (isQueryBoundP_liftM_isRight _)).mono (Nat.zero_le _)
    · exact trivial
  refine WCount.wrap _ (w := gameWI c ω₀) ?_ ?_ []
  · intro t s
    refine wCount_of_isQueryBoundP _ _ _ ?_
    rcases t with n | t | d | hq'
    · simp [Lazy.lazyImplR, Lazy.kind]
    · simp [Lazy.lazyImplR, Lazy.kind, gameWI, gameWU]
    · rcases hc : s.lookup d with _ | v
      · rw [Lazy.lazyImplR_sec_run_miss d s hc]
        simp [Lazy.kind]
      · rw [Lazy.lazyImplR_sec_run_hit d s v hc]
        simp
    · simp [Lazy.lazyImplR, Lazy.kind]
  unfold qmItsrOpen
  have h0 : WCount (gameWI c ω₀) (liftM pkSeedDist₀ :
      OracleComp (Lazy.OSpec (primsΩ ω₀) (Lazy.itsrG (primsΩ ω₀))) _) 0 :=
    wCount_of_isQueryBoundP _ _ _ (Lazy.liftM_kindBound .game (by decide) pkSeedDist₀)
  sorry

/-- The ITSR target requests `(PK.seed, PK.root, M)` (`= ItsrIn (primsΩ ω)` for every `ω`). -/
abbrev ItsrInB : Type := BN × BN × List Byte

/-- **(b) The ITSR adversary as one interactive adversary over the port oracle.** -/
theorem itsr_iadv (ω₀ : Ω128 c) (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hqs : ∀ pk, CountBound isSign (F.main pk) qs) :
    ∃ x : IAdv LocalSig.instruments.{0} (qromSpec (EncX c) EncY) ItsrInB BN
        (fun _ ↦ BN × ItsrInB) qs (progReg (EncX c) EncY E),
      IAdv.IsQueryBound qs x (fun _ ↦ q + itsrHashes Link.vp qs) ∧
      ∀ (St : Type) (ch : ItsrInB → St → BN × St) (s : St) (T)
        (ρ : SubState ((EncX c × EncY) × E))
        (Ev : (BN × ItsrInB) × St → Prop) [DecidablePred Ev],
        qprob LocalSig.Interp.instruments (encΩ { ω₀ with hmsg := T })
            (IAdv.flat ch (IAdv.stop (L := LocalSig.instruments.{0})
              (spec := qromSpec (EncX c) EncY)) qs s x) ρ (fun p ↦ Ev p.2) =
          qWeight Ev (PQ.Interactive.close (detImpl ch)
            (qbItsrL (internalΩ c optRand₀ pkSeedDist₀ encΩ F { ω₀ with hmsg := T })) s)
            (ρ.matrix ⊗ₖ (SubState.basis ()).matrix) := by
  haveI hne : Nonempty (BN × ItsrInB) :=
    ⟨((default : Bytes Link.vp.params.n), ((default : Bytes Link.vp.params.n),
      (default : Bytes Link.vp.params.n), ([] : List Byte)))⟩
  obtain ⟨x, hx, hxe⟩ := PUE.exists_iadv_qprob (Req := ItsrInB) (Resp := BN)
    (α := BN × ItsrInB) (pue_itsrMach c optRand₀ pkSeedDist₀ F ω₀ q qs hq hqs) qs
  refine ⟨x, hx, fun St ch s T ρ Ev _ ↦ ?_⟩
  rw [← itsrMach_encΩ c optRand₀ pkSeedDist₀ F ω₀ T]
  exact hxe St ch s Ev _ ρ (itsrMach_games c optRand₀ pkSeedDist₀ F ω₀ qs hqs _)

end mach

end Reduction

#print axioms Reduction.itsrMach_games
#print axioms Reduction.itsr_iadv
