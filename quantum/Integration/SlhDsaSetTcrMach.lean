import Integration.SlhDsaSetOracle

namespace Reduction.SetOracle
open MLink OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal PQ.Interactive PQ.QROM Quantum
open scoped ComplexOrder Kronecker

set_option linter.unusedSectionVars false

abbrev worldPrims {p : Params} {c : Caps} (g : FinFns p c) := randPrims g.toRand

abbrev signRand (S : Sha2Set) (r : S.Node → S.Node → ProbComp S.Node)
    {c : Caps} (g : FinFns S.vp.params c) : PublicKeyCore (worldPrims g).core → ProbComp S.Node :=
  fun pk => r pk.pkSeed pk.pkRoot

noncomputable abbrev internal (S : Sha2Set) (c : Caps) (r : S.Node → S.Node → ProbComp S.Node)
    (seeds : ProbComp S.Node) {E : Type} [Fintype E] [DecidableEq E]
    (F : PortForger (Input S c) (Output S) E) (g : FinFns S.vp.params c) :=
  qPureBytesToInternal (forgerAt S c r seeds F g)

section mach

variable (S : Sha2Set) {E : Type} [Fintype E] [DecidableEq E] (c : Caps)
  (optRand₀ : S.Node → S.Node → ProbComp S.Node)
  (pkSeedDist₀ : ProbComp S.Node)
  (F : PortForger (Input S c) (Output S) E)

/-- **Each public-hash query as ONE evaluation of the port function** (`Thash` in the first
coordinate of the `.inl` component, `H_msg` in the second coordinate of the `.inr (.inl _)`
component); out-of-cap inputs get the constant `default`, as in `FinFns.toRand`. -/
def hashH (ω₀ : FinFns S.vp.params c) (H : Input S c → (Output S)) : QueryImpl (publicHashSpec (worldPrims ω₀).core) Id
  | .thash pk a xs =>
      if h : xs.length ≤ c.tl then (H (.inl (pk, a, BList.ofList xs h))).1 else default
  | .hmsg r pk root m =>
      if h : m.length ≤ c.ml then (H (.inr (.inl (r, pk, root, BList.ofList m h)))).2 else default

/-- At the port function of world `{ω₀ with thash := T}`, `hashH` IS the hash interpretation of
that world. -/
theorem impl_worldPrims_withThash (ω₀ : FinFns S.vp.params c) (T) :
    PublicHash.impl (worldPrims { ω₀ with thash := T }) = hashH S c ω₀ (oracle S { ω₀ with thash := T }) := by
  funext q
  cases q <;> rfl

/-- The internal forger of the reduction (`qPureBytesToInternal` around the compiled port
program), written with the world fixed to `ω₀` except for the port function. -/
noncomputable def qmForger (ω₀ : FinFns S.vp.params c) (H : Input S c → (Output S))
    (pk : PublicKeyCore (worldPrims ω₀).core) :
    QOC (WS (Input S c) (Output S) E)
      (unifSpec + (List Byte →ₒ GeneralScheme.SignatureCore S.vp (worldPrims ω₀).core))
      (List Byte × GeneralScheme.SignatureCore S.vp (worldPrims ω₀).core) :=
  Guarded.readForgery pureEncode ([], constSig default) <$>
    wrap0 (Guarded.signingImpl pureEncode)
      (qmCRead (decodePureSig S.vp (worldPrims ω₀) (codecFor S ω₀.toRand))
          (Except.error (External.Error.contextTooLong 0)) <$>
        wrap0 (qmCSign (encodePureSig S.vp (worldPrims ω₀) (codecFor S ω₀.toRand)))
          (compileQ H (F.main (encodePublicKey (codecFor S ω₀.toRand) pk))))

theorem internal_main_withThash (ω₀ : FinFns S.vp.params c) (T) :
    (internal S c optRand₀ pkSeedDist₀ F { ω₀ with thash := T }).main =
      fun pk ↦ qmForger S c F ω₀ (oracle S { ω₀ with thash := T }) pk := by
  funext pk
  simp only [internal, forgerAt, scheme, qPureBytesToInternal, qToInternal, qPureBytesToTyped, QForger.wrapForger,
    PortForger.at, qmCSign_eq, qmCRead_eq, pureBytesView]
  rfl

/-- **The class-TCR second-phase machine family** for the fixed world `ω₀`, arity `n`, state
`st` and seed `pk`, as a function of the port function `H`. -/
noncomputable def tcrMach (ω₀ : FinFns S.vp.params c) (n : ℕ)
    (st : SecretTable S.vp (worldPrims ω₀) ×
      List ((worldPrims ω₀).AdrsKey × List (worldPrims ω₀).Y))
    (pk : (worldPrims ω₀).PkSeed) (H : Input S c → (Output S)) :
    Closed (WS (Input S c) (Output S) E) (ℕ × {xs : List (worldPrims ω₀).Y // xs.length = n}) :=
  qmMach (signRand S optRand₀ ω₀) (hashH S c ω₀ H) n (qmForger S c F ω₀ H) st pk

/-- At the port function of world `{ω₀ with thash := T}`, the family is
the second phase of the quantum class-TCR adversary of that world. -/
theorem tcrMach_oracle (ω₀ : FinFns S.vp.params c) (n : ℕ)
    (st : SecretTable S.vp (worldPrims ω₀) ×
      List ((worldPrims ω₀).AdrsKey × List (worldPrims ω₀).Y))
    (pk : (worldPrims ω₀).PkSeed) (T) :
    tcrMach S c optRand₀ F ω₀ n st pk (oracle S { ω₀ with thash := T }) =
      (qbTcrArM n (internal S c optRand₀ pkSeedDist₀ F { ω₀ with thash := T })).forge st pk := by
  have h1 := qMemoForge_eq_qmMach (signRand S optRand₀ { ω₀ with thash := T }) n
    (internal S c optRand₀ pkSeedDist₀ F { ω₀ with thash := T }) st pk
  rw [internal_main_withThash, impl_worldPrims_withThash] at h1
  refine Eq.trans ?_ h1.symm
  unfold tcrMach
  qm_kernel_rfl

end mach

section pue

variable (S : Sha2Set) {E : Type} [Fintype E] [DecidableEq E] (c : Caps)
  (optRand₀ : S.Node → S.Node → ProbComp S.Node)
  (pkSeedDist₀ : ProbComp S.Node)
  (F : PortForger (Input S c) (Output S) E)

attribute [local instance] Lazy.openQ

/-- One hash answer is at most one evaluation of the port function. -/
theorem evalCost_hashH (ω₀ : FinFns S.vp.params c) (q : PublicHashQuery (worldPrims ω₀).core.PkSeed
    (worldPrims ω₀).core.AdrsKey (worldPrims ω₀).core.Y) :
    EvalCost (fun H ↦ (pure (hashH S c ω₀ H q) : ProbComp ((publicHashSpec (worldPrims ω₀).core).Range q)))
      1 := by
  cases q with
  | thash pk a xs =>
    by_cases h : xs.length ≤ c.tl
    · have e : (fun H : Input S c → (Output S) ↦ (pure (hashH S c ω₀ H (.thash pk a xs)) :
          ProbComp S.Node)) =
          fun H ↦ pure ((fun y : (Output S) ↦ y.1) (H (.inl (pk, a, BList.ofList xs h)))) := by
        funext H
        simp [hashH, h]
      exact e ▸ EvalCost.eval _ _
    · have e : (fun H : Input S c → (Output S) ↦ (pure (hashH S c ω₀ H (.thash pk a xs)) :
          ProbComp S.Node)) = fun _ ↦ pure default := by
        funext H
        simp [hashH, h]
      exact e ▸ (EvalCost.const _).mono (Nat.zero_le _)
  | hmsg r pk root m =>
    by_cases h : m.length ≤ c.ml
    · have e : (fun H : Input S c → (Output S) ↦ (pure (hashH S c ω₀ H (.hmsg r pk root m)) :
          ProbComp (Bytes S.vp.params.m))) =
          fun H ↦ pure ((fun y : (Output S) ↦ y.2) (H (.inr (.inl (r, pk, root, BList.ofList m h))))) := by
        funext H
        simp [hashH, h]
      exact e ▸ EvalCost.eval _ _
    · have e : (fun H : Input S c → (Output S) ↦ (pure (hashH S c ω₀ H (.hmsg r pk root m)) :
          ProbComp (Bytes S.vp.params.m))) = fun _ ↦ pure default := by
        funext H
        simp [hashH, h]
      exact e ▸ (EvalCost.const _).mono (Nat.zero_le _)

/-- Each query of an open program costs its hash weight. -/
theorem evalCost_qmImpl (ω₀ : FinFns S.vp.params c) (tbl : SecretTable S.vp (worldPrims ω₀))
    (t : (Lazy.OSpec (worldPrims ω₀) []ₒ).Domain) :
    EvalCost (fun H ↦ qmImpl (hashH S c ω₀ H) tbl t) (hashW (worldPrims ω₀) t) := by
  rcases t with n | t | d | q
  · exact EvalCost.const _
  · exact PEmpty.elim t
  · exact EvalCost.const _
  · exact evalCost_hashH S c ω₀ q

/-- An open program with at most `k` hash queries costs `k` evaluations. -/
theorem evalCost_open (ω₀ : FinFns S.vp.params c) (tbl : SecretTable S.vp (worldPrims ω₀)) {α : Type}
    (P : OracleComp (Lazy.OSpec (worldPrims ω₀) []ₒ) α) (k : ℕ)
    (hP : IsQueryBoundP P (fun t ↦ Lazy.kind t = .hash) k) :
    EvalCost (fun H ↦ simulateQ (qmImpl (hashH S c ω₀ H) tbl) P) k :=
  EvalCost.simulateQ (fun H ↦ qmImpl (hashH S c ω₀ H) tbl) (hashW (worldPrims ω₀))
    (evalCost_qmImpl S c ω₀ tbl) P k (wCount_of_isQueryBoundP _ P k hP)

theorem keygen_hashes (ω₀ : FinFns S.vp.params c) (pkSeed : (worldPrims ω₀).PkSeed) :
    IsQueryBoundP (Lazy.openKeygen (worldPrims ω₀) []ₒ pkSeed) (fun t ↦ Lazy.kind t = .hash)
      (Lazy.keygenHashes S.vp) :=
  (Lazy.openKeygen_kindBound .hash pkSeed).mono (by simpa [Lazy.ind] using Lazy.keygenB_hash)

theorem sign_hashes (ω₀ : FinFns S.vp.params c) (msg : List Byte) (pkSeed : (worldPrims ω₀).PkSeed)
    (root R : (worldPrims ω₀).Y) :
    IsQueryBoundP (Lazy.openSign (worldPrims ω₀) []ₒ msg pkSeed root R)
      (fun t ↦ Lazy.kind t = .hash) (Lazy.signHashes S.vp) :=
  (Lazy.openSign_kindBound .hash msg pkSeed root R).mono
    (by simpa [Lazy.ind] using Lazy.signB_hash)

theorem tail_hashes (ω₀ : FinFns S.vp.params c) (pkSeed : (worldPrims ω₀).PkSeed)
    (L : List ((worldPrims ω₀).AdrsKey × List (worldPrims ω₀).Y)) (root : (worldPrims ω₀).Y)
    (z : (List Byte × GeneralScheme.SignatureCore S.vp (worldPrims ω₀).core) ×
      G2Log (worldPrims ω₀)) :
    IsQueryBoundP (qmTail pkSeed L root z) (fun t ↦ Lazy.kind t = .hash)
      (1 + Resources2.verifyHashes S.vp * 2) := by
  have hver : ∀ (parts : DigestParts S.vp.params)
      (sig : GeneralScheme.SignatureCore S.vp (worldPrims ω₀).core),
      IsQueryBoundP ((simulateQ (Resources2.collO (gspec := []ₒ) pkSeed L)
        (Resources2.verifyFree pkSeed parts sig)).run none) (fun t ↦ Lazy.kind t = .hash)
        (Resources2.verifyHashes S.vp * 2) := fun parts sig ↦
    IsQueryBoundP.simulateQ_run_of_step_le (cost := 2) (q := fun t ↦ Lazy.kind t = .hash)
      (Resources2.verifyFree_bound pkSeed parts sig)
      (fun t _ s ↦ Resources2.collO_step_bound pkSeed L .hash t s)
      (fun t ht s ↦ absurd trivial ht) none
  have hmsg : ∀ (R root : (worldPrims ω₀).Y) (m : List Byte),
      IsQueryBoundP (PublicHash.hmsg (worldPrims ω₀).core R pkSeed root m :
        OracleComp (Lazy.OSpec (worldPrims ω₀) []ₒ) (Bytes S.vp.params.m))
        (fun t ↦ Lazy.kind t = .hash) 1 :=
    fun R root m ↦ (isQueryBoundP_query_iff _ _ _).2 fun _ ↦ Nat.one_pos
  unfold qmTail
  exact Lazy.qb_bind _ (hmsg _ _ _) fun dg ↦
    Lazy.qb_bind _ (m := 0) (hver _ _) fun c ↦ isQueryBoundP_pure _ _ _

/-- Each answer of the forger's classical interface costs its weight. -/
theorem evalCost_qmImplS (ω₀ : FinFns S.vp.params c) (tbl : SecretTable S.vp (worldPrims ω₀))
    (pkSeed : (worldPrims ω₀).PkSeed) (root : (worldPrims ω₀).Y)
    (t : (unifSpec + (List Byte →ₒ GeneralScheme.SignatureCore S.vp (worldPrims ω₀).core)).Domain)
    (s : G2Log (worldPrims ω₀)) :
    EvalCost (fun H ↦ (qmImplS (signRand S optRand₀ ω₀) (hashH S c ω₀ H) tbl pkSeed root t).run s)
      (sgnW (Lazy.signHashes S.vp) t) := by
  rcases t with n | msg
  · exact EvalCost.const _
  · change EvalCost (fun H ↦ signRand S optRand₀ ω₀ ⟨pkSeed, root⟩ >>= fun addrnd ↦
      lazyRandomizer s msg addrnd >>= fun R ↦
        simulateQ (qmImpl (hashH S c ω₀ H) tbl)
          (Lazy.openSign (worldPrims ω₀) []ₒ msg pkSeed root R) >>= fun sig ↦
          (pure (sig, s ++ [(msg, addrnd, R)]) : ProbComp _)) _
    have h := EvalCost.bind (EvalCost.const (X := Input S c) (Y := (Output S))
        (signRand S optRand₀ ω₀ ⟨pkSeed, root⟩)) fun addrnd ↦
      EvalCost.bind (EvalCost.const (X := Input S c) (Y := (Output S)) (lazyRandomizer s msg addrnd))
        fun R ↦ EvalCost.bind (evalCost_open S c ω₀ tbl _ _ (sign_hashes S c ω₀ msg pkSeed root R))
          fun sig ↦ EvalCost.const (X := Input S c) (Y := (Output S))
            (pure (sig, s ++ [(msg, addrnd, R)]) : ProbComp _)
    exact h.mono (by simp)

/-- The forger family is `PUE`, every signing query weighing `k`. -/
theorem pue_qmForger (ω₀ : FinFns S.vp.params c) (q qs k : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hqs : ∀ pk, CountBound isSign (F.main pk) qs)
    (pk : PublicKeyCore (worldPrims ω₀).core) :
    PUE (sgnW k) (fun H ↦ qmForger S c F ω₀ H pk) (q + qs * k) := by
  unfold qmForger
  refine PUE.map _ (PUE.wrap0 (cnt := sgnW k) _ ?_ (PUE.map _ (PUE.wrap0 (cnt := sgnW k)
    (cnt' := sgnW k) _ ?_ (PUE.compileQ (sgnW k) _ _
    (wCount_of_countBound isPort isSign _ k ?_ _ q qs (hq _) (hqs _))))))
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
  · intro t
    rcases t with j | u | n | m <;> simp [compileW, isPort, isSign]

/-- The class-TCR machine family makes at most `q + tcrMHashes qs` port
calls plus evaluations on every path. -/
theorem pue_tcrMach (ω₀ : FinFns S.vp.params c) (n : ℕ)
    (st : SecretTable S.vp (worldPrims ω₀) ×
      List ((worldPrims ω₀).AdrsKey × List (worldPrims ω₀).Y))
    (pk : (worldPrims ω₀).PkSeed) (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hqs : ∀ pk, CountBound isSign (F.main pk) qs) :
    PUE (spec := unifSpec) cnt0 (tcrMach S c optRand₀ F ω₀ n st pk) (q + tcrMHashes S.vp qs) := by
  unfold tcrMach qmMach
  have hB : ∀ root : (worldPrims ω₀).Y, PUE (spec := unifSpec) cnt0 (fun H ↦
      close (qmImplS (signRand S optRand₀ ω₀) (hashH S c ω₀ H) st.1 pk root)
          (qmForger S c F ω₀ H ⟨pk, root⟩) [] >>= fun z ↦
        liftU (classOut (worldPrims ω₀) n st.2 <$>
          simulateQ (qmImpl (hashH S c ω₀ H) st.1) (qmTail pk st.2 root z)))
      (q + qs * Lazy.signHashes S.vp + (1 + Resources2.verifyHashes S.vp * 2)) := by
    intro root
    refine PUE.bind (PUE.close _ (evalCost_qmImplS S c optRand₀ ω₀ st.1 pk root)
      (pue_qmForger S c F ω₀ q qs _ hq hqs ⟨pk, root⟩) []) fun z ↦ ?_
    have h := PUE.liftU_bind (E := E) (B := fun o _ ↦ (pure o : Closed (WS (Input S c) (Output S) E) _))
      (q := 0)
      ((evalCost_open S c ω₀ st.1 _ _ (tail_hashes S c ω₀ pk st.2 root z)).map
        (classOut (worldPrims ω₀) n st.2)) fun o ↦ PUE.pure o 0
    simpa using h
  have h := PUE.liftU_bind (evalCost_open S c ω₀ st.1 _ _ (keygen_hashes S c ω₀ pk)) hB
  refine h.mono ?_
  unfold tcrMHashes
  omega

end pue

/-! ## Steps 3 and 5: the delivered statements -/

section deliver

variable (S : Sha2Set) {E : Type} [Fintype E] [DecidableEq E] (c : Caps)
  (optRand₀ : S.Node → S.Node → ProbComp S.Node)
  (pkSeedDist₀ : ProbComp S.Node)
  (F : PortForger (Input S c) (Output S) E)

/-- For a fixed world `ω₀`, state `st` and seed `pk`
there is ONE machine family in the port function, `PUE` with budget `q + tcrMHashes qs`, equal at
the port function of `{ω₀ with thash := T}` to the second phase of the quantum class-TCR
adversary of that world, for every `Thash` table `T`. -/
theorem tcr_mach_exists (ω₀ : FinFns S.vp.params c) (n : ℕ)
    (st : SecretTable S.vp (worldPrims ω₀) ×
      List ((worldPrims ω₀).AdrsKey × List (worldPrims ω₀).Y))
    (pk : (worldPrims ω₀).PkSeed) (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hqs : ∀ pk, CountBound isSign (F.main pk) qs) :
    ∃ Mach : (Input S c → (Output S)) →
        Closed (WS (Input S c) (Output S) E) (ℕ × {xs : List (worldPrims ω₀).Y // xs.length = n}),
      PUE (spec := unifSpec) cnt0 Mach (q + tcrMHashes S.vp qs) ∧
      ∀ T, Mach (oracle S { ω₀ with thash := T }) =
        (qbTcrArM n (internal S c optRand₀ pkSeedDist₀ F { ω₀ with thash := T })).forge st pk :=
  ⟨tcrMach S c optRand₀ F ω₀ n st pk, pue_tcrMach S c optRand₀ F ω₀ n st pk q qs hq hqs,
    fun T ↦ tcrMach_oracle S c optRand₀ pkSeedDist₀ F ω₀ n st pk T⟩

/-- **Step 5 (class TCR, every arity `n`): the hybrid model of the forge machine**, for an
initial state `ρ ⊗ |()⟩⟨()|`. -/
theorem tcr_forge_model (ω₀ : FinFns S.vp.params c) (n : ℕ)
    (st : SecretTable S.vp (worldPrims ω₀) ×
      List ((worldPrims ω₀).AdrsKey × List (worldPrims ω₀).Y))
    (pk : (worldPrims ω₀).PkSeed) (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hqs : ∀ pk, CountBound isSign (F.main pk) qs)
    (ρ : SubState ((Input S c × (Output S)) × E)) :
    ∃ Mo : PQ.QROM.HybridModel (Input S c) (Output S) (ℕ × {xs : List (worldPrims ω₀).Y // xs.length = n})
        (q + tcrMHashes S.vp qs),
      ∀ T (Ev : ℕ × {xs : List (worldPrims ω₀).Y // xs.length = n} → Prop) [DecidablePred Ev],
        Mo.prob (oracle S { ω₀ with thash := T }) Ev =
          qWeight Ev ((qbTcrArM n
            (internal S c optRand₀ pkSeedDist₀ F { ω₀ with thash := T })).forge st pk)
            (ρ.matrix ⊗ₖ (SubState.basis ()).matrix) := by
  obtain ⟨Mo, hMo⟩ := (pue_tcrMach S c optRand₀ F ω₀ n st pk q qs hq hqs).exists_model ρ
  refine ⟨Mo, fun T Ev _ ↦ ?_⟩
  rw [hMo, tcrMach_oracle S c optRand₀ pkSeedDist₀ F ω₀ n st pk T]

/-- **Step 5, at the forger's initial state**: the initial state of the class-TCR adversary is
the port forger's `F.ρ₀` (for every world), and the model computes the Born weights of the
forge machine from it. -/
theorem tcr_forge_model_ρ₀ (ω₀ : FinFns S.vp.params c) (n : ℕ)
    (st : SecretTable S.vp (worldPrims ω₀) ×
      List ((worldPrims ω₀).AdrsKey × List (worldPrims ω₀).Y))
    (pk : (worldPrims ω₀).PkSeed) (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hqs : ∀ pk, CountBound isSign (F.main pk) qs) :
    ∃ Mo : PQ.QROM.HybridModel (Input S c) (Output S) (ℕ × {xs : List (worldPrims ω₀).Y // xs.length = n})
        (q + tcrMHashes S.vp qs),
      ∀ T (Ev : ℕ × {xs : List (worldPrims ω₀).Y // xs.length = n} → Prop) [DecidablePred Ev],
        Mo.prob (oracle S { ω₀ with thash := T }) Ev =
          qWeight Ev ((qbTcrArM n
            (internal S c optRand₀ pkSeedDist₀ F { ω₀ with thash := T })).forge st pk)
            (qbTcrArM n (internal S c optRand₀ pkSeedDist₀ F { ω₀ with thash := T })).ρ₀ := by
  obtain ⟨ρ, hρ⟩ := exists_subState F.ρ₀ F.posSemidef F.trace_eq_one
  obtain ⟨Mo, hMo⟩ := tcr_forge_model S c optRand₀ pkSeedDist₀ F ω₀ n st pk q qs hq hqs ρ
  refine ⟨Mo, fun T Ev _ ↦ ?_⟩
  rw [hMo T Ev]
  change _ = qWeight Ev _ F.ρ₀
  rw [hρ]

/-- **The hypothesis `hModel` of agent `qtcr` (`quantum/HANDOFF-qtcr.md`), discharged**, with
`q' = q + tcrMHashes S.vp qs`, for every forger with at most `q` port calls and `qs` signing
queries on every path. -/
theorem tcr_hModel (n q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hqs : ∀ pk, CountBound isSign (F.main pk) qs) :
    ∀ (ω₀ : FinFns S.vp.params c) (st : Open.TcrP1State S.vp (worldPrims ω₀))
      (pk : S.Node),
      ∃ Mo : PQ.QROM.HybridModel (Input S c) (Output S)
          (ℕ × {xs : List (S.Node) // xs.length = n}) (q + tcrMHashes S.vp qs),
        ∀ (T : S.Node → Bytes 22 → BList (S.Node) c.tl →
            S.Node)
          (Ev : ℕ × {xs : List (S.Node) // xs.length = n} → Prop)
          [DecidablePred Ev],
          Mo.prob (oracle S { ω₀ with thash := T }) Ev =
            qWeight Ev ((qbTcrArM n (internal S c optRand₀ pkSeedDist₀ F
              { ω₀ with thash := T })).forge st pk) F.ρ₀ :=
  fun ω₀ st pk ↦ tcr_forge_model_ρ₀ S c optRand₀ pkSeedDist₀ F ω₀ n st pk q qs hq hqs

end deliver
end Reduction.SetOracle

#print axioms Reduction.SetOracle.tcr_hModel
