import Integration.SlhDsaSetTcrMach
namespace Reduction.SetOracle
open MLink OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal PQ.Interactive PQ.QROM Quantum
open scoped ComplexOrder Kronecker
set_option linter.unusedSectionVars false
variable (S : Sha2Set)
section mach

variable {E : Type} [Fintype E] [DecidableEq E] (c : Caps)
  (optRand₀ : S.Node → S.Node → ProbComp S.Node)
  (pkSeedDist₀ : ProbComp S.Node)
  (F : PortForger (Input S c) (Output S) E)

theorem impl_worldPrims_withHmsg (ω₀ : FinFns S.vp.params c) (Hm) :
    PublicHash.impl (worldPrims { ω₀ with hmsg := Hm }) = hashH S c ω₀ (oracle S { ω₀ with hmsg := Hm }) := by
  funext q
  cases q <;> rfl

theorem internalΩ_main_withHmsg (ω₀ : FinFns S.vp.params c) (Hm) :
    (internal S c optRand₀ pkSeedDist₀ F { ω₀ with hmsg := Hm }).main =
      fun pk ↦ qmForger S c F ω₀ (oracle S { ω₀ with hmsg := Hm }) pk := by
  funext pk
  simp only [internal, forgerAt, scheme, qPureBytesToInternal, qToInternal, qPureBytesToTyped, QForger.wrapForger,
    PortForger.at, qmCSign_eq, qmCRead_eq, pureBytesView]
  rfl

noncomputable def itsrMach (ω₀ : FinFns S.vp.params c) (H : Input S c → (Output S)) :
    QOC (WS (Input S c) (Output S) E) (unifSpec + Lazy.itsrG (worldPrims ω₀))
      ((worldPrims ω₀).Y × ItsrIn (worldPrims ω₀)) :=
  qLazyRun (hashH S c ω₀ H) (qmItsrOpen (signRand S optRand₀ ω₀) pkSeedDist₀ (qmForger S c F ω₀ H))

set_option maxRecDepth 200000 in

theorem itsrMach_oracle (ω₀ : FinFns S.vp.params c) (Hm) :
    itsrMach S c optRand₀ pkSeedDist₀ F ω₀ (oracle S { ω₀ with hmsg := Hm }) =
      qbItsrL (internal S c optRand₀ pkSeedDist₀ F { ω₀ with hmsg := Hm }) := by
  rw [qbItsrL_eq (signRand S optRand₀ { ω₀ with hmsg := Hm }), internalΩ_main_withHmsg,
    impl_worldPrims_withHmsg]
  unfold itsrMach
  qm_kernel_rfl

abbrev hashWI (ω₀ : FinFns S.vp.params c) : (Lazy.OSpec (worldPrims ω₀) (Lazy.itsrG (worldPrims ω₀))).Domain → ℕ :=
  fun t ↦ if Lazy.kind t = .hash then 1 else 0

abbrev hashWU (ω₀ : FinFns S.vp.params c) :
    (Lazy.RSpec (Lazy.itsrG (worldPrims ω₀)) Unit (worldPrims ω₀).Y
      (publicHashSpec (worldPrims ω₀).core)).Domain → ℕ :=
  fun t ↦ if Lazy.kind t = .hash then 1 else 0

theorem pue_qmItsrOpen (ω₀ : FinFns S.vp.params c) (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hqs : ∀ pk, CountBound isSign (F.main pk) qs) :
    PUE (hashWI S c ω₀) (fun H ↦ qmItsrOpen (signRand S optRand₀ ω₀) pkSeedDist₀
      (qmForger S c F ω₀ H)) (q + itsrHashes S.vp qs) := by
  unfold qmItsrOpen
  have h0 : WCount (hashWI S c ω₀) (liftM pkSeedDist₀ :
      OracleComp (Lazy.OSpec (worldPrims ω₀) (Lazy.itsrG (worldPrims ω₀))) _) 0 :=
    wCount_of_isQueryBoundP _ _ _ (Lazy.liftM_kindBound .hash (by decide) pkSeedDist₀)
  have hk : ∀ pkSeed, WCount (hashWI S c ω₀)
      (Lazy.openKeygen (worldPrims ω₀) (Lazy.itsrG (worldPrims ω₀)) pkSeed) (Lazy.keygenHashes S.vp) :=
    fun pkSeed ↦ wCount_of_isQueryBoundP _ _ _ (keygen_hashesG pkSeed)
  have hrun : ∀ pkSeed root, PUE (hashWI S c ω₀) (fun H ↦
      wrap ((QueryImpl.ofLift unifSpec (OracleComp (Lazy.OSpec (worldPrims ω₀)
          (Lazy.itsrG (worldPrims ω₀))))).liftTarget
          (StateT (G2Log (worldPrims ω₀)) (OracleComp (Lazy.OSpec (worldPrims ω₀)
            (Lazy.itsrG (worldPrims ω₀))))) +
        logSignOracle (signRand S optRand₀ ω₀) ⟨pkSeed, root⟩
          (Lazy.itsrRandomizerO pkSeed root)
          (fun m R ↦ Lazy.openSign (worldPrims ω₀) (Lazy.itsrG (worldPrims ω₀)) m pkSeed root R))
        (qmForger S c F ω₀ H ⟨pkSeed, root⟩) [] >>= fun z ↦
      liftQ (pure (z.1.2.randomness, (pkSeed, root, z.1.1))))
      (q + qs * Lazy.signHashes S.vp + 0) := by
    intro pkSeed root
    refine PUE.bind (PUE.wrap _ (cnt := sgnW (Lazy.signHashes S.vp)) ?_
      (pue_qmForger S c F ω₀ q qs _ hq hqs ⟨pkSeed, root⟩) []) fun z ↦ ?_
    · exact fun t s ↦ wCount_of_isQueryBoundP _ _ _ (itsr_step_hashes _ pkSeed root t s)
    · simp only [liftQ_pure]
      exact PUE.pure _ 0
  have h := PUE.liftQ_bind _ h0 fun pkSeed ↦ PUE.liftQ_bind _ (hk pkSeed) fun root ↦
    hrun pkSeed root
  refine h.mono ?_
  unfold itsrHashes
  omega

theorem evalCostQ_hashH (ω₀ : FinFns S.vp.params c) {ι' : Type} {sp : OracleSpec ι'}
    (cnt : (unifSpec + sp).Domain → ℕ)
    (q : PublicHashQuery (worldPrims ω₀).core.PkSeed (worldPrims ω₀).core.AdrsKey (worldPrims ω₀).core.Y) :
    EvalCostQ E cnt (fun H ↦ (pure (hashH S c ω₀ H q) :
      OracleComp (unifSpec + sp) ((publicHashSpec (worldPrims ω₀).core).Range q))) 1 := by
  cases q with
  | thash pk a xs =>
    by_cases h : xs.length ≤ c.tl
    · have e : (fun H : Input S c → (Output S) ↦ (pure (hashH S c ω₀ H (.thash pk a xs)) :
          OracleComp (unifSpec + sp) (S.Node))) =
          fun H ↦ pure ((fun y : (Output S) ↦ y.1) (H (.inl (pk, a, BList.ofList xs h)))) := by
        funext H
        simp [hashH, h]
      exact e ▸ EvalCostQ.eval _ _
    · have e : (fun H : Input S c → (Output S) ↦ (pure (hashH S c ω₀ H (.thash pk a xs)) :
          OracleComp (unifSpec + sp) (S.Node))) = fun _ ↦ pure default := by
        funext H
        simp [hashH, h]
      exact e ▸ (EvalCostQ.const _ (wCount_pure _ _ _)).mono (Nat.zero_le _)
  | hmsg r pk root m =>
    by_cases h : m.length ≤ c.ml
    · have e : (fun H : Input S c → (Output S) ↦ (pure (hashH S c ω₀ H (.hmsg r pk root m)) :
          OracleComp (unifSpec + sp) (Bytes S.vp.params.m))) =
          fun H ↦ pure ((fun y : (Output S) ↦ y.2) (H (.inr (.inl (r, pk, root, BList.ofList m h))))) := by
        funext H
        simp [hashH, h]
      exact e ▸ EvalCostQ.eval _ _
    · have e : (fun H : Input S c → (Output S) ↦ (pure (hashH S c ω₀ H (.hmsg r pk root m)) :
          OracleComp (unifSpec + sp) (Bytes S.vp.params.m))) = fun _ ↦ pure default := by
        funext H
        simp [hashH, h]
      exact e ▸ (EvalCostQ.const _ (wCount_pure _ _ _)).mono (Nat.zero_le _)

theorem pue_itsrMach (ω₀ : FinFns S.vp.params c) (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hqs : ∀ pk, CountBound isSign (F.main pk) qs) :
    PUE (fun _ ↦ 0) (itsrMach S c optRand₀ pkSeedDist₀ F ω₀) (q + itsrHashes S.vp qs) := by
  unfold itsrMach qLazyRun
  refine PUE.wrap0E (fun H ↦ Lazy.interp (hashH S c ω₀ H)) (cnt := hashWU S c ω₀) ?_
    (PUE.map _ (PUE.wrap _ (cnt := hashWI S c ω₀) ?_ (pue_qmItsrOpen S c optRand₀ pkSeedDist₀ F ω₀ q qs
      hq hqs) []))
  · intro t
    rcases t with n | t | d | hq'
    · exact (EvalCostQ.const _ (wCount_zero _ _)).mono (Nat.zero_le _)
    · exact (EvalCostQ.const _ (wCount_zero _ _)).mono (Nat.zero_le _)
    · exact (EvalCostQ.const _ (wCount_zero _ _)).mono (Nat.zero_le _)
    · exact evalCostQ_hashH S c ω₀ _ hq'
  · intro t s
    refine wCount_of_isQueryBoundP _ _ _ ?_
    rcases t with n | t | d | hq'
    · simp [Lazy.lazyImplR, Lazy.kind]
    · simp [Lazy.lazyImplR, Lazy.kind]
    · rcases hc : s.lookup d with _ | v
      · rw [Lazy.lazyImplR_sec_run_miss d s hc]
        simp [Lazy.kind]
      · rw [Lazy.lazyImplR_sec_run_hit d s v hc]
        simp
    · simp [Lazy.lazyImplR, Lazy.kind, hashWI]

theorem itsr_mach_exists (ω₀ : FinFns S.vp.params c) (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hqs : ∀ pk, CountBound isSign (F.main pk) qs) :
    ∃ Mach : (Input S c → (Output S)) → QOC (WS (Input S c) (Output S) E) (unifSpec + Lazy.itsrG (worldPrims ω₀))
        ((worldPrims ω₀).Y × ItsrIn (worldPrims ω₀)),
      PUE (fun _ ↦ 0) Mach (q + itsrHashes S.vp qs) ∧
      ∀ Hm, Mach (oracle S { ω₀ with hmsg := Hm }) =
        qbItsrL (internal S c optRand₀ pkSeedDist₀ F { ω₀ with hmsg := Hm }) :=
  ⟨itsrMach S c optRand₀ pkSeedDist₀ F ω₀, pue_itsrMach S c optRand₀ pkSeedDist₀ F ω₀ q qs hq hqs,
    fun Hm ↦ itsrMach_oracle S c optRand₀ pkSeedDist₀ F ω₀ Hm⟩

end mach
section mach

variable {E : Type} [Fintype E] [DecidableEq E] (c : Caps)
  (optRand₀ : S.Node → S.Node → ProbComp S.Node)
  (pkSeedDist₀ : ProbComp S.Node)
  (F : PortForger (Input S c) (Output S) E)

abbrev sgnI (ω₀ : FinFns S.vp.params c) :=
  sgnW (M := List Byte) (S := GeneralScheme.SignatureCore S.vp (worldPrims ω₀).core) 1
abbrev sgnE (ω₀ : FinFns S.vp.params c) :=
  sgnW (M := List Byte × List Byte)
    (S := Except External.Error (GeneralScheme.SignatureCore S.vp (worldPrims ω₀).core)) 1
abbrev sgnB := sgnW (M := List Byte × List Byte) (S := Option (List Byte)) 1

theorem qmForger_signs (ω₀ : FinFns S.vp.params c) (qs : ℕ)
    (hqs : ∀ pk, CountBound isSign (F.main pk) qs) (H : Input S c → (Output S))
    (pk : PublicKeyCore (worldPrims ω₀).core) :
    WCount (qw (WS (Input S c) (Output S) E) (sgnI S c ω₀)) (qmForger S c F ω₀ H pk) qs := by
  unfold qmForger
  have h0 := (countBound_iff_wCount _ _ _).1 (hqs (encodePublicKey (codecFor S ω₀.toRand) pk))
  have h1 : WCount (qw ((Input S c × (Output S)) × E) (Sum.elim (fun _ ↦ 0) sgnB))
      (F.main (encodePublicKey (codecFor S ω₀.toRand) pk)) qs :=
    WCount.wmono (fun t ↦ by rcases t with j | u | n | m <;> simp [isSign]) h0
  refine WCount.map (WCount.wrap0 _ (w := sgnE S c ω₀) ?_ (WCount.map (WCount.wrap0 _ (w := sgnB) ?_
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

abbrev gameWI (ω₀ : FinFns S.vp.params c) : (Lazy.OSpec (worldPrims ω₀) (Lazy.itsrG (worldPrims ω₀))).Domain → ℕ :=
  fun t ↦ if Lazy.kind t = .game then 1 else 0

abbrev gameWU (ω₀ : FinFns S.vp.params c) :
    (Lazy.RSpec (Lazy.itsrG (worldPrims ω₀)) Unit (worldPrims ω₀).Y
      (publicHashSpec (worldPrims ω₀).core)).Domain → ℕ :=
  fun t ↦ if Lazy.kind t = .game then 1 else 0

theorem qmItsrOpen_games (ω₀ : FinFns S.vp.params c) (qs : ℕ) (hqs : ∀ pk, CountBound isSign (F.main pk) qs)
    (H : Input S c → (Output S)) :
    WCount (qw (WS (Input S c) (Output S) E) (gameWI S c ω₀))
      (qmItsrOpen (signRand S optRand₀ ω₀) pkSeedDist₀ (qmForger S c F ω₀ H)) qs := by
  unfold qmItsrOpen
  have h0 : WCount (gameWI S c ω₀) (liftM pkSeedDist₀ :
      OracleComp (Lazy.OSpec (worldPrims ω₀) (Lazy.itsrG (worldPrims ω₀))) _) 0 :=
    wCount_of_isQueryBoundP _ _ _ (Lazy.liftM_kindBound .game (by decide) pkSeedDist₀)
  have hk : ∀ pkSeed, WCount (gameWI S c ω₀)
      (Lazy.openKeygen (worldPrims ω₀) (Lazy.itsrG (worldPrims ω₀)) pkSeed) 0 :=
    fun pkSeed ↦ wCount_of_isQueryBoundP _ _ _ (keygen_gamesG pkSeed)
  have hst : ∀ pkSeed root t s, WCount (gameWI S c ω₀)
      ((((QueryImpl.ofLift unifSpec (OracleComp (Lazy.OSpec (worldPrims ω₀)
          (Lazy.itsrG (worldPrims ω₀))))).liftTarget
          (StateT (G2Log (worldPrims ω₀)) (OracleComp (Lazy.OSpec (worldPrims ω₀)
            (Lazy.itsrG (worldPrims ω₀))))) +
        logSignOracle (signRand S optRand₀ ω₀) ⟨pkSeed, root⟩
          (Lazy.itsrRandomizerO pkSeed root)
          (fun m R ↦ Lazy.openSign (worldPrims ω₀) (Lazy.itsrG (worldPrims ω₀)) m pkSeed root R)) t).run s)
      (sgnI S c ω₀ t) :=
    fun pkSeed root t s ↦ wCount_of_isQueryBoundP _ _ _ (itsr_step_games _ pkSeed root t s)
  refine (WCount.bind (m := qs) (WCount.liftQ (W := WS (Input S c) (Output S) E) h0) fun pkSeed ↦ ?_).mono
    (by omega)
  refine (WCount.bind (m := qs) (WCount.liftQ (W := WS (Input S c) (Output S) E) (hk pkSeed))
    fun root ↦ ?_).mono (by omega)
  refine (WCount.bind (m := 0) (WCount.wrap _ (w := sgnI S c ω₀) (hst pkSeed root)
    (qmForger_signs S c F ω₀ qs hqs H ⟨pkSeed, root⟩) []) fun z ↦ ?_).mono (by omega)
  simp only [liftQ_pure]
  exact trivial

set_option maxHeartbeats 1000000 in

theorem itsrMach_games (ω₀ : FinFns S.vp.params c) (qs : ℕ) (hqs : ∀ pk, CountBound isSign (F.main pk) qs)
    (H : Input S c → (Output S)) :
    CountBound (isGameQ (Req := ItsrIn (worldPrims ω₀)) (Resp := (worldPrims ω₀).Y))
      (itsrMach S c optRand₀ pkSeedDist₀ F ω₀ H) qs := by
  refine (countBound_iff_wCount _ _ _).2 (WCount.wmono (w' := qw (WS (Input S c) (Output S) E)
    (fun t ↦ if t.isRight = true then 1 else 0)) (fun t ↦ by
      rcases t with j | n | r <;> simp [isGameQ]) ?_)
  unfold itsrMach qLazyRun
  refine WCount.wrap0 _ (w := gameWU S c ω₀) ?_ (WCount.map ?_ _)
  · intro t
    rcases t with n | t | d | hq'
    · exact wCount_liftM_query _ _ (by simp [Lazy.kind, gameWU])
    · exact wCount_liftM_query _ _ (by simp [Lazy.kind, gameWU])
    · exact (wCount_of_isQueryBoundP _ _ _ (isQueryBoundP_liftM_isRight _)).mono (Nat.zero_le _)
    · exact trivial
  refine WCount.wrap _ (w := gameWI S c ω₀) ?_ (qmItsrOpen_games S c optRand₀ pkSeedDist₀ F ω₀ qs hqs H) []
  · intro t s
    refine wCount_of_isQueryBoundP _ _ _ ?_
    rcases t with n | t | d | hq'
    · simp [Lazy.lazyImplR, Lazy.kind]
    · simp [Lazy.lazyImplR, Lazy.kind, gameWI]
    · rcases hc : s.lookup d with _ | v
      · rw [Lazy.lazyImplR_sec_run_miss d s hc]
        simp [Lazy.kind]
      · rw [Lazy.lazyImplR_sec_run_hit d s v hc]
        simp
    · simp [Lazy.lazyImplR, Lazy.kind]

theorem itsr_iadv (ω₀ : FinFns S.vp.params c) (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hqs : ∀ pk, CountBound isSign (F.main pk) qs) :
    ∃ x : IAdv LocalSig.instruments.{0} (qromSpec (Input S c) (Output S)) (S.Node × S.Node × List Byte) S.Node
        (fun _ ↦ S.Node × (S.Node × S.Node × List Byte)) qs (progReg (Input S c) (Output S) E),
      IAdv.IsQueryBound qs x (fun _ ↦ q + itsrHashes S.vp qs) ∧
      ∀ (St : Type) (ch : (S.Node × S.Node × List Byte) → St → S.Node × St) (s : St) (T)
        (ρ : SubState ((Input S c × (Output S)) × E))
        (Ev : (S.Node × (S.Node × S.Node × List Byte)) × St → Prop) [DecidablePred Ev],
        qprob LocalSig.Interp.instruments (oracle S { ω₀ with hmsg := T })
            (IAdv.flat ch (IAdv.stop (L := LocalSig.instruments.{0})
              (spec := qromSpec (Input S c) (Output S))) qs s x) ρ (fun p ↦ Ev p.2) =
          qWeight Ev (PQ.Interactive.close (detImpl ch)
            (qbItsrL (internal S c optRand₀ pkSeedDist₀ F { ω₀ with hmsg := T })) s)
            (ρ.matrix ⊗ₖ (SubState.basis ()).matrix) := by
  have hne : Nonempty (S.Node × (S.Node × S.Node × List Byte)) :=
    ⟨((default : S.Node), ((default : S.Node),
      (default : S.Node), ([] : List Byte)))⟩
  obtain ⟨x, hx, hxe⟩ := PUE.exists_iadv_qprob (Req := (S.Node × S.Node × List Byte)) (Resp := S.Node)
    (α := S.Node × (S.Node × S.Node × List Byte)) (pue_itsrMach S c optRand₀ pkSeedDist₀ F ω₀ q qs hq hqs) qs
  refine ⟨x, hx, fun St ch s T ρ Ev _ ↦ ?_⟩
  rw [← itsrMach_oracle S c optRand₀ pkSeedDist₀ F ω₀ T]
  exact hxe St ch s Ev _ ρ (itsrMach_games S c optRand₀ pkSeedDist₀ F ω₀ qs hqs _)

theorem itsr_hPort (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hqs : ∀ pk, CountBound isSign (F.main pk) qs) :
    ∀ ω₀ : FinFns S.vp.params c, ∃ (L : LocalSig.{1, 0}) (A : QReg) (I : L.Interp) (ρ : SubState A)
      (x : IAdv L (qromSpec (Input S c) (Output S)) (S.Node × S.Node × List Byte) S.Node
        (fun _ ↦ Option (S.Node × (S.Node × S.Node × List Byte))) qs A),
      IAdv.IsQueryBound qs x (fun _ ↦ q + itsrHashes S.vp qs) ∧
      ∀ (Hm : S.Node → S.Node → S.Node → BList Byte c.ml → (Bytes S.vp.params.m)) (Rs : Fin qs → S.Node)
        (Ev : Option (S.Node × (S.Node × S.Node × List Byte)) × List (S.Node × S.Node × List Byte) → Prop) [DecidablePred Ev],
        qprob I (oracle S (ω₀.withHmsg Hm))
            (IAdv.flat (rndCh Rs) (IAdv.stop (L := L) (spec := qromSpec (Input S c) (Output S))) qs [] x)
            ρ (fun p ↦ Ev p.2) =
          qWeight (fun z ↦ Ev (some z.1, z.2))
            (PQ.Interactive.close (QItsr.rndImpl (X := (S.Node × S.Node × List Byte)) Rs)
              (qbItsrL (internal S c optRand₀ pkSeedDist₀ F (ω₀.withHmsg Hm))) []) F.ρ₀ := by
  intro ω₀
  obtain ⟨ρ, hρ⟩ := exists_subState F.ρ₀ F.posSemidef F.trace_eq_one
  have hP := PUE.map (some : S.Node × (S.Node × S.Node × List Byte) → Option (S.Node × (S.Node × S.Node × List Byte)))
    (pue_itsrMach S c optRand₀ pkSeedDist₀ F ω₀ q qs hq hqs)
  obtain ⟨x, hx, hxe⟩ := PUE.exists_iadv_qprob (Req := (S.Node × S.Node × List Byte)) (Resp := S.Node)
    (α := Option (S.Node × (S.Node × S.Node × List Byte))) hP qs
  refine ⟨LocalSig.instruments.{0}, progReg (Input S c) (Output S) E, LocalSig.Interp.instruments, ρ, x,
    hx, fun Hm Rs Ev _ ↦ ?_⟩
  have hc : CountBound (isGameQ (Req := (S.Node × S.Node × List Byte)) (Resp := S.Node))
      (some <$> itsrMach S c optRand₀ pkSeedDist₀ F ω₀ (oracle S (ω₀.withHmsg Hm))) qs :=
    (countBound_iff_wCount _ _ _).2 (WCount.map ((countBound_iff_wCount _ _ _).1
      (itsrMach_games S c optRand₀ pkSeedDist₀ F ω₀ qs hqs _)) _)
  have he : itsrMach S c optRand₀ pkSeedDist₀ F ω₀ (oracle S (ω₀.withHmsg Hm)) =
      qbItsrL (internal S c optRand₀ pkSeedDist₀ F (ω₀.withHmsg Hm)) :=
    itsrMach_oracle S c optRand₀ pkSeedDist₀ F ω₀ Hm
  have h := hxe (List (S.Node × S.Node × List Byte)) (rndCh Rs) [] Ev (oracle S (ω₀.withHmsg Hm)) ρ hc
  refine h.trans ?_
  rw [hρ, close_map_out, qWeight_map, he]
  rfl

end mach
end Reduction.SetOracle
#print axioms Reduction.SetOracle.itsr_hPort
