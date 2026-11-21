import Ideal.Realize.ForsProg

/-!
# Queries of the FORS port program (FORS-leaf realisers, part 5)

For a port forger program `mainP` with at most `qf` compression queries, at most `qs` signing
queries, no signing query on more than `ℓ` bytes and forged messages of at most `ℓ` bytes, the
port program `forsFindOpenP optRand mainP pkSeed ys` makes

* `forsFindOpenP_port`: at most `qf` port queries;
* `forsFindOpenP_hashes`: at most `keygenHashes + qs·forsSignHashes + (1 + qs + k)` hash queries
  (the count of `Reduction.Open.forsFindOpen_hashes`, from the same budget lemmas
  `openKeygen_kindBound`, `forsSignOpen_kindBound`, `findAnswerO_kindBound`);
* `forsFindOpenP_hmsg`: at most `qs + (1 + qs)` `H_msg` queries;
* `forsFindOpenP_bad`: no `Thash` query on more than `B` values and no `H_msg` query on more than
  `ℓ` bytes, if every hash call of the scheme is on at most `B` values.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security

namespace Ideal.Realize.Fors

open Reduction Reduction.Open Reduction.Lazy Reduction.Resources2 Ideal.Realize

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option synthInstance.maxHeartbeats 400000

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]

attribute [local instance] Lazy.openQ

/-- Index type of the port program. -/
abbrev GIdx (prims : Primitives vp.params) :=
  ℕ ⊕ ((ℕ ⊕ (St × Blk)) ⊕ (SecIdx ⊕ PublicHashQuery prims.PkSeed prims.AdrsKey prims.Y))

/-- A port query of the port program. -/
def isPortIdx : GIdx prims → Bool
  | .inr (.inl (.inr _)) => true
  | _ => false

/-! ## Transfer through `liftG` -/

theorem liftG_bound (p : GIdx prims → Prop) [DecidablePred p] {β : Type}
    (oa : OracleComp (OSpec prims (forsG prims)) β) (n : ℕ)
    (h : IsQueryBoundP oa (fun t => p (liftIdx t)) n) :
    IsQueryBoundP (simulateQ liftG oa) p n := by
  refine IsQueryBoundP.simulateQ_of_step h (fun t ht => ?_) (fun t ht => ?_)
  · rcases t with n | i | t <;>
      exact (isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos
  · rcases t with n | i | t <;>
      exact (isQueryBoundP_query_iff _ _ _).2 fun h' => absurd h' ht

theorem liftG_zero (p : GIdx prims → Prop) [DecidablePred p] {β : Type}
    (oa : OracleComp (OSpec prims (forsG prims)) β) (hp : ∀ t, ¬ p (liftIdx t)) :
    IsQueryBoundP (simulateQ liftG oa) p 0 :=
  liftG_bound p oa 0 (IsQueryBoundP.of_imp (fun t ht => (hp t ht).elim) (isQueryBoundP_false oa 0))

theorem kind_liftIdx (t : (OSpec prims (forsG prims)).Domain) :
    Lazy.kind (liftIdx (prims := prims) t) = Lazy.kind t := by
  rcases t with n | i | d | q <;> rfl

theorem hmsg_liftIdx (t : (OSpec prims (forsG prims)).Domain) :
    isHmsgIdx (liftIdx (prims := prims) t) = isHmsgIdx t := by
  rcases t with n | i | d | q
  · rfl
  · rfl
  · rfl
  · cases q <;> rfl

theorem bad_liftIdx (B ℓ : ℕ) (t : (OSpec prims (forsG prims)).Domain) :
    isBadIdx B ℓ (liftIdx (prims := prims) t) = isBadIdx B ℓ t := by
  rcases t with n | i | d | q
  · rfl
  · rfl
  · rfl
  · cases q <;> rfl

theorem port_liftIdx (t : (OSpec prims (forsG prims)).Domain) :
    isPortIdx (liftIdx (prims := prims) t) = false := by
  rcases t with n | i | t <;> rfl

/-! ## The pieces of the open program over `forsG` -/

section Pieces

variable (p : ℕ ⊕ (ℕ ⊕ (SecIdx ⊕ PublicHashQuery prims.PkSeed prims.AdrsKey prims.Y)) → Prop)
  [DecidablePred p]

theorem mapM_bound_mem {κ' : Type} {spec : OracleSpec κ'} (q : κ' → Prop) [DecidablePred q]
    {α β : Type} (f : α → OracleComp spec β) (c : ℕ) :
    ∀ l : List α, (∀ a ∈ l, IsQueryBoundP (f a) q c) → IsQueryBoundP (l.mapM f) q (l.length * c)
  | [], _ => by
      rw [List.mapM_nil]
      exact isQueryBoundP_pure _ _ _
  | a :: l, h => by
      rw [List.mapM_cons]
      refine (Lazy.qb_bind q (h a (List.mem_cons_self ..)) fun b => Lazy.qb_bind q (m := 0)
        (mapM_bound_mem q f c l fun a' ha' => h a' (List.mem_cons_of_mem _ ha')) fun bs =>
          isQueryBoundP_pure _ _ _).mono ?_
      rw [List.length_cons, Nat.succ_mul]
      omega

/-- Open FORS signing makes at most `c` `p`-queries, if its `H_msg` query makes at most `c`, and
`p` holds of no secret read, no opening, and no `Thash` query on `1`, `2`, `len` or `k` values. -/
theorem forsSignOpen_le (pk : PublicKeyCore prims.core) (ys : List prims.Y) (m : List Byte)
    (R : prims.Y) (c : ℕ)
    (hsec : ∀ d, ¬ p (.inr (.inr (.inl d))))
    (hgame : ∀ i, ¬ p (.inr (.inl i)))
    (hth : ∀ key xs, OkLen vp xs → ¬ p (thIdx prims ℕ pk.pkSeed key xs))
    (hm : IsQueryBoundP (PublicHash.hmsg prims.core R pk.pkSeed pk.pkRoot m :
      OracleComp (Lazy.OSpec prims (forsG prims)) _) p c) :
    IsQueryBoundP (forsSignOpen pk ys m R) p c := by
  have hf : ∀ (a : Adrs) (y : prims.core.Y), IsQueryBoundP (PublicHash.f prims.core pk.pkSeed a y :
      OracleComp (OSpec prims (forsG prims)) prims.Y) p 0 :=
    fun _ _ => (isQueryBoundP_query_iff _ _ _).2 fun h => absurd h (hth _ _ (Or.inl rfl))
  have htl : ∀ (a : Adrs) (ys : List prims.core.Y),
      (ys.length = vp.params.len ∨ ys.length = vp.params.k) →
      IsQueryBoundP (PublicHash.tl prims.core pk.pkSeed a ys :
      OracleComp (OSpec prims (forsG prims)) prims.Y) p 0 :=
    fun _ ys hys => (isQueryBoundP_query_iff _ _ _).2 fun h =>
      absurd h (hth _ _ (Or.inr (Or.inr hys)))
  have hh : ∀ (a : Adrs) (l r : prims.core.Y),
      IsQueryBoundP (PublicHash.h prims.core pk.pkSeed a l r :
      OracleComp (OSpec prims (forsG prims)) prims.Y) p 0 :=
    fun _ _ _ => (isQueryBoundP_query_iff _ _ _).2 fun h =>
      absurd h (hth _ _ (Or.inr (Or.inl rfl)))
  have hs : ∀ a : Adrs, IsQueryBoundP (Lazy.secQ prims (forsG prims) a) p 0 :=
    fun _ => (isQueryBoundP_query_iff _ _ _).2 fun h => absurd h (hsec _)
  have himg : ∀ (a : Adrs) (y : prims.core.Y),
      IsQueryBoundP (forsImgHashO pk.pkSeed a y) p 0 := by
    intro a y
    unfold forsImgHashO
    split
    · exact isQueryBoundP_pure _ _ _
    · exact hf a y
  unfold forsSignOpen
  refine (isQueryBoundP_bind (m := 0) hm fun digest _ =>
    isQueryBoundP_bind_zero _ _
      (np_forsSign p prims.core himg hh (fun a => isQueryBoundP_pure _ _ _) _ _) fun img =>
      isQueryBoundP_bind_zero _ _ ((Lazy.qb_ofFnM p _ 0 fun i =>
          isQueryBoundP_bind_zero _ _ ((isQueryBoundP_query_iff _ _ _).2 fun h => absurd h
            (hgame _)) fun x => isQueryBoundP_pure _ _ _).mono (by simp)) fun forsSig =>
        isQueryBoundP_bind_zero _ _ (np_forsPk p prims.core hf htl hh forsSig _ _) fun forsPk =>
          isQueryBoundP_bind_zero _ _ (np_signFromPos p prims.core hf htl hh hs _ _ _ _ _)
            fun htSig => isQueryBoundP_pure _ _ _).mono (by omega)

/-- The answer extraction makes at most `c₀ + |log|·c₁` `p`-queries, if its `H_msg` query for the
forgery makes at most `c₀`, each one for a signed message at most `c₁`, and `p` holds of no
`Thash` query on one value. -/
theorem findAnswerO_le (pk : PublicKeyCore prims.core) (ys : List prims.Y) (log : G2Log prims)
    (msg : List Byte) (sig : GeneralScheme.SignatureCore vp prims.core) (c₀ c₁ : ℕ)
    (hth : ∀ key (y : prims.Y), ¬ p (thIdx prims ℕ pk.pkSeed key [y]))
    (hm₀ : IsQueryBoundP (PublicHash.hmsg prims.core sig.randomness pk.pkSeed pk.pkRoot msg :
      OracleComp (Lazy.OSpec prims (forsG prims)) _) p c₀)
    (hm₁ : ∀ e ∈ G2Log.signed log, IsQueryBoundP (PublicHash.hmsg prims.core e.2 pk.pkSeed
      pk.pkRoot e.1 : OracleComp (Lazy.OSpec prims (forsG prims)) _) p c₁) :
    IsQueryBoundP (findAnswerO pk ys log msg sig) p (c₀ + log.length * c₁) := by
  have hl : (G2Log.signed log).length = log.length := List.length_map _
  have hf : ∀ (a : Adrs) (y : prims.core.Y), IsQueryBoundP (PublicHash.f prims.core pk.pkSeed a y :
      OracleComp (OSpec prims (forsG prims)) prims.Y) p 0 :=
    fun _ _ => (isQueryBoundP_query_iff _ _ _).2 fun h => absurd h (hth _ _)
  unfold findAnswerO
  refine (Lazy.qb_bind _ hm₀ fun digest =>
    Lazy.qb_bind _ (mapM_bound_mem p _ c₁ (G2Log.signed log) fun e he =>
        Lazy.qb_bind _ (m := 0) (hm₁ e he) fun d => isQueryBoundP_pure _ _ _) fun opened =>
      Lazy.qb_bind _ (m := 0) (Lazy.qb_ofFnM _ _ 0 fun i => hf _ _) fun imgs =>
        isQueryBoundP_pure _ _ _).mono ?_
  rw [hl]
  omega

end Pieces

/-! ## The forger's run -/

section Run

variable (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
  (pk : PublicKeyCore prims.core) (ys : List prims.Y)
variable (p : GIdx prims → Prop) [DecidablePred p]

theorem liftM_npG (hu : ∀ n, ¬ p (.inl n)) {β : Type} (ob : ProbComp β) :
    IsQueryBoundP (liftM ob : OracleComp (OSpec prims (GP prims)) β) p 0 :=
  IsQueryBoundP.of_imp (fun t ht => by
      rcases t with n | t
      · exact absurd ht (hu n)
      · rfl)
    (isQueryBoundP_liftM_isRight
      (hs := GP prims + ((SecIdx →ₒ prims.Y) + publicHashSpec prims.core)) ob)

theorem unifStepF (hu : ∀ n, ¬ p (.inl n)) (n : ℕ) (s : G2Log prims) :
    IsQueryBoundP ((portImplF optRand pk ys (.inl n)).run s) p 0 := by
  show IsQueryBoundP ((stdF optRand pk ys (.inl n)).run s) p 0
  unfold stdF
  simp only [QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply, StateT.run_monadLift]
  exact isQueryBoundP_bind_zero _ _ (liftM_npG p hu (liftM (unifSpec.query n) : ProbComp _))
    fun x => isQueryBoundP_pure _ (x, s) _

theorem portStepF (q : St × Blk) (c : ℕ)
    (hq : IsQueryBoundP (Lazy.gameQ prims (GP prims) (.inr q)) p c) (s : G2Log prims) :
    IsQueryBoundP ((portImplF optRand pk ys (.inr (.inl q))).run s) p c := by
  show IsQueryBoundP ((liftM (Lazy.gameQ prims (GP prims) (.inr q)) :
    StateT (G2Log prims) (OracleComp (OSpec prims (GP prims))) St).run s) p c
  rw [StateT.run_monadLift]
  exact isQueryBoundP_bind (m := 0) hq fun x _ => isQueryBoundP_pure _ (x, s) _

theorem signStepF (hu : ∀ n, ¬ p (.inl n)) (msg : List Byte) (c : ℕ)
    (hsign : ∀ R, IsQueryBoundP (simulateQ liftG (forsSignOpen pk ys msg R)) p c)
    (s : G2Log prims) :
    IsQueryBoundP ((portImplF optRand pk ys (.inr (.inr msg))).run s) p c := by
  have hstep := isQueryBoundP_bind (liftM_npG p hu (optRand pk))
    fun addrnd _ => isQueryBoundP_bind
      (liftM_npG p hu (lazyRandomizer s msg addrnd)) fun R _ =>
        isQueryBoundP_bind (m := 0) (hsign R)
          fun sig _ => isQueryBoundP_pure _ (sig, s ++ [(msg, addrnd, R)]) _
  simpa [portImplF, stdF, logSignOracle, lazyRandomizerLift] using hstep

theorem signStepF_support (msg : List Byte) (s : G2Log prims) (z)
    (hz : z ∈ support ((portImplF optRand pk ys (.inr (.inr msg))).run s)) :
    ∃ a R, z.2 = s ++ [(msg, a, R)] := by
  simp [portImplF, stdF, logSignOracle] at hz
  obtain ⟨a, _, R, _, sg, _, rfl⟩ := hz
  exact ⟨a, R, rfl⟩

theorem unifStepF_support (n : ℕ) (s : G2Log prims) (z)
    (hz : z ∈ support ((portImplF optRand pk ys (.inl n)).run s)) : z.2 = s := by
  simp [portImplF, stdF] at hz
  obtain ⟨x, _, rfl⟩ := hz
  rfl

theorem portStepF_support (q : St × Blk) (s : G2Log prims) (z)
    (hz : z ∈ support ((portImplF optRand pk ys (.inr (.inl q))).run s)) : z.2 = s := by
  simp [portImplF, Lazy.gameQ] at hz
  obtain ⟨x, _, rfl⟩ := hz
  rfl

end Run

/-! ## Invariants of the forger's run -/

section Inv

variable (optRand : PublicKeyCore prims.core → ProbComp prims.Y) (mainP : PortForgerProg vp prims)
  (pk : PublicKeyCore prims.core) (ys : List prims.Y)

/-- The transcript of a port forger with at most `qs` signing queries has at most `qs` entries. -/
theorem portRunF_log (qs : ℕ)
    (hqs : IsQueryBoundP (mainP pk)
      (fun i => isSignQ (S := GeneralScheme.SignatureCore vp prims.core) i = true) qs) :
    ∀ z ∈ support (portRunF optRand mainP pk ys), z.2.length ≤ qs := by
  intro z hz
  have h := hqs.cost_le_of_mem_support_run_simulateQ (impl := portImplF optRand pk ys)
    List.length
    (fun t ht s w hw => by
      rcases t with n | q | msg
      · simp [isSignQ] at ht
      · simp [isSignQ] at ht
      · obtain ⟨a, R, h⟩ := signStepF_support optRand pk ys msg s w hw
        rw [h]; simp)
    (fun t ht s w hw => by
      rcases t with n | q | msg
      · rw [unifStepF_support optRand pk ys n s w hw]
      · rw [portStepF_support optRand pk ys q s w hw]
      · simp [isSignQ] at ht) [] z hz
  simpa using h

/-- The number of transcript entries on messages of more than `ℓ` bytes. -/
def longCount (ℓ : ℕ) (log : G2Log prims) : ℕ :=
  (log.filter fun e => decide (ℓ < e.1.length)).length

/-- **Every signed message of the transcript has at most `ℓ` bytes**, if the forger makes no
signing query on more than `ℓ` bytes. -/
theorem portRunF_msgs (ℓ : ℕ)
    (hlong : IsQueryBoundP (mainP pk)
      (fun i => isLongQ (S := GeneralScheme.SignatureCore vp prims.core) ℓ i = true) 0) :
    ∀ z ∈ support (portRunF optRand mainP pk ys), ∀ e ∈ z.2, e.1.length ≤ ℓ := by
  intro z hz
  have h := hlong.cost_le_of_mem_support_run_simulateQ (impl := portImplF optRand pk ys)
    (longCount ℓ)
    (fun t ht s w hw => by
      rcases t with n | q | msg
      · simp [isLongQ] at ht
      · simp [isLongQ] at ht
      · obtain ⟨a, R, h⟩ := signStepF_support optRand pk ys msg s w hw
        rw [h]
        unfold longCount
        rw [List.filter_append, List.length_append]
        exact Nat.add_le_add_left (by simp only [List.filter_singleton]; cases decide (ℓ < msg.length) <;> simp) _)
    (fun t ht s w hw => by
      rcases t with n | q | msg
      · rw [unifStepF_support optRand pk ys n s w hw]
      · rw [portStepF_support optRand pk ys q s w hw]
      · obtain ⟨a, R, h⟩ := signStepF_support optRand pk ys msg s w hw
        have hm : ¬ ℓ < msg.length := by simpa [isLongQ] using ht
        rw [h]
        unfold longCount
        simp [List.filter_append, hm]) [] z hz
  have h0 : longCount ℓ z.2 = 0 := by simpa [longCount] using h
  intro e he
  unfold longCount at h0
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff] at h0
  simpa using h0 e he

/-- The forged message of the run is a forged message of the forger. -/
theorem portRunF_out (ℓ : ℕ) (hout : ∀ z ∈ support (mainP pk), z.1.length ≤ ℓ) :
    ∀ z ∈ support (portRunF optRand mainP pk ys), z.1.1.length ≤ ℓ := by
  intro z hz
  refine hout z.1 ?_
  have hz' : z.1 ∈ support ((simulateQ (portImplF optRand pk ys) (mainP pk)).run' []) := by
    rw [StateT.run'_eq, support_map]
    exact ⟨z, hz, rfl⟩
  exact support_simulateQ_run'_subset _ _ _ hz'

end Inv

/-! ## The four counts -/

section Counts

variable (optRand : PublicKeyCore prims.core → ProbComp prims.Y) (mainP : PortForgerProg vp prims)
  (pkSeed : prims.PkSeed) (ys : List prims.Y)

/-- **Port queries of the port program**: at most the forger's compression queries. -/
theorem forsFindOpenP_port (qf : ℕ)
    (hqf : ∀ pk, IsQueryBoundP (mainP pk)
      (fun i => isPortQ (S := GeneralScheme.SignatureCore vp prims.core) i = true) qf) :
    IsQueryBoundP (forsFindOpenP optRand mainP pkSeed ys) (fun t => isPortIdx t = true) qf := by
  have hu : ∀ n, ¬ isPortIdx (prims := prims) (.inl n) = true := by simp [isPortIdx]
  have hz : ∀ {β : Type} (oa : OracleComp (OSpec prims (forsG prims)) β),
      IsQueryBoundP (simulateQ liftG oa) (fun t => isPortIdx t = true) 0 :=
    fun oa => liftG_zero _ oa fun t => by simp [port_liftIdx]
  unfold forsFindOpenP portRunF
  refine (isQueryBoundP_bind (hz _) fun root _ =>
    isQueryBoundP_bind (n := qf) (m := 0) ?_ fun z _ => hz _).mono (by omega)
  refine IsQueryBoundP.simulateQ_run_of_step (hqf _) (fun t ht s => ?_) (fun t ht s => ?_) []
  · rcases t with n | q | msg
    · simp [isPortQ] at ht
    · exact portStepF optRand _ ys _ q 1 ((isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos) s
    · simp [isPortQ] at ht
  · rcases t with n | q | msg
    · exact unifStepF optRand _ ys _ hu n s
    · simp [isPortQ] at ht
    · exact signStepF optRand _ ys _ hu msg 0 (fun R => hz _) s

/-- **Hash queries of the port program**: `≤ keygenHashes + qs·forsSignHashes + (1 + qs + k)`,
the count of `Reduction.Open.forsFindOpen_hashes`. -/
theorem forsFindOpenP_hashes (qs : ℕ)
    (hqs : ∀ pk, IsQueryBoundP (mainP pk)
      (fun i => isSignQ (S := GeneralScheme.SignatureCore vp prims.core) i = true) qs) :
    IsQueryBoundP (forsFindOpenP optRand mainP pkSeed ys) (fun t => Lazy.kind t = .hash)
      (Lazy.keygenHashes vp + qs * forsSignHashes vp + (1 + qs + vp.params.k)) := by
  have hu : ∀ n, ¬ Lazy.kind (ι := ℕ ⊕ (St × Blk)) (D := SecIdx)
      (κ := PublicHashQuery prims.PkSeed prims.AdrsKey prims.Y) (.inl n) = .hash := by
    intro n; simp [Lazy.kind]
  have hl : ∀ {β : Type} (oa : OracleComp (OSpec prims (forsG prims)) β) (n : ℕ),
      IsQueryBoundP oa (fun t => Lazy.kind t = .hash) n →
      IsQueryBoundP (simulateQ liftG oa) (fun t => Lazy.kind t = .hash) n :=
    fun oa n h => liftG_bound _ oa n (IsQueryBoundP.of_imp (fun t ht => by
      rwa [kind_liftIdx] at ht) h)
  unfold forsFindOpenP
  refine (isQueryBoundP_bind (hl _ _ (Lazy.openKeygen_kindBound .hash pkSeed)) fun root _ =>
    isQueryBoundP_bind (n := qs * forsSignB vp 0 0 1) (m := 1 + qs + vp.params.k) ?_ fun z hz =>
      hl _ _ ((findAnswerO_kindBound .hash ⟨pkSeed, root⟩ ys z.2 z.1.1 z.1.2).mono ?_)).mono ?_
  · unfold portRunF
    refine IsQueryBoundP.simulateQ_run_of_step_le (hqs _) (fun t ht s => ?_) (fun t ht s => ?_) []
    · rcases t with n | q | msg
      · simp [isSignQ] at ht
      · simp [isSignQ] at ht
      · exact signStepF optRand _ ys _ hu msg _ (fun R => hl _ _ (by
          simpa [Lazy.ind] using forsSignOpen_kindBound .hash ⟨pkSeed, root⟩ ys msg R)) s
    · rcases t with n | q | msg
      · exact unifStepF optRand _ ys _ hu n s
      · exact portStepF optRand _ ys _ q 0 ((isQueryBoundP_query_iff _ _ _).2 fun h => by
          simp [Lazy.kind] at h) s
      · simp [isSignQ] at ht
  · have := portRunF_log optRand mainP ⟨pkSeed, root⟩ ys qs (hqs _) z hz
    simp only [Lazy.ind, ↓reduceIte, Nat.mul_one]
    omega
  · have h1 : Lazy.keygenB vp (Lazy.ind .hash .sec) (Lazy.ind .hash .hash) ≤ Lazy.keygenHashes vp := by
      simpa [Lazy.ind] using Lazy.keygenB_hash (vp := vp)
    have h2 : qs * forsSignB vp 0 0 1 ≤ qs * forsSignHashes vp :=
      Nat.mul_le_mul_left _ forsSignB_hash
    omega

/-- **`H_msg` queries of the port program**: one per signing query, one for the forgery, one per
signed message in the answer extraction. -/
theorem forsFindOpenP_hmsg (qs : ℕ)
    (hqs : ∀ pk, IsQueryBoundP (mainP pk)
      (fun i => isSignQ (S := GeneralScheme.SignatureCore vp prims.core) i = true) qs) :
    IsQueryBoundP (forsFindOpenP optRand mainP pkSeed ys) (fun t => isHmsgIdx t = true)
      (qs + (1 + qs)) := by
  have hu : ∀ n, ¬ isHmsgIdx (ι := ℕ ⊕ (St × Blk)) (P := prims.PkSeed) (K := prims.AdrsKey)
      (Y := prims.Y) (.inl n) = true := by intro n; simp [isHmsgIdx]
  have hl : ∀ {β : Type} (oa : OracleComp (OSpec prims (forsG prims)) β) (n : ℕ),
      IsQueryBoundP oa (fun t => isHmsgIdx t = true) n →
      IsQueryBoundP (simulateQ liftG oa) (fun t => isHmsgIdx t = true) n :=
    fun oa n h => liftG_bound _ oa n (IsQueryBoundP.of_imp (fun t ht => by
      rwa [hmsg_liftIdx] at ht) h)
  have hsec : ∀ d : SecIdx, ¬ isHmsgIdx (ι := ℕ) (P := prims.PkSeed) (K := prims.AdrsKey)
      (Y := prims.Y) (.inr (.inr (.inl d))) = true := by intro d; simp [isHmsgIdx]
  have hgame : ∀ i : ℕ, ¬ isHmsgIdx (ι := ℕ) (P := prims.PkSeed) (K := prims.AdrsKey)
      (Y := prims.Y) (.inr (.inl i)) = true := by intro i; simp [isHmsgIdx]
  have hth : ∀ (pk : prims.PkSeed) (key : prims.AdrsKey) (xs : List prims.Y),
      ¬ isHmsgIdx (thIdx prims ℕ pk key xs) = true := by intro pk key xs; simp [isHmsgIdx]
  unfold forsFindOpenP
  refine (isQueryBoundP_bind (hl _ 0 (np_openKeygen _ pkSeed hsec fun key xs _ => hth _ _ _))
    fun root _ => isQueryBoundP_bind (n := qs * 1) (m := 1 + qs) ?_ fun z hz =>
      hl _ _ ((findAnswerO_le _ ⟨pkSeed, root⟩ ys z.2 z.1.1 z.1.2 1 1 (fun key y => hth _ _ _)
        ((isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos)
        (fun e _ => (isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos)).mono ?_)).mono ?_
  · unfold portRunF
    refine IsQueryBoundP.simulateQ_run_of_step_le (hqs _) (fun t ht s => ?_) (fun t ht s => ?_) []
    · rcases t with n | q | msg
      · simp [isSignQ] at ht
      · simp [isSignQ] at ht
      · exact signStepF optRand _ ys _ hu msg _ (fun R => hl _ _
          (forsSignOpen_le _ ⟨pkSeed, root⟩ ys msg R 1 hsec hgame (fun key xs _ => hth _ _ _)
            ((isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos))) s
    · rcases t with n | q | msg
      · exact unifStepF optRand _ ys _ hu n s
      · exact portStepF optRand _ ys _ q 0 ((isQueryBoundP_query_iff _ _ _).2 fun h => by
          simp [isHmsgIdx] at h) s
      · simp [isSignQ] at ht
  · have := portRunF_log optRand mainP ⟨pkSeed, root⟩ ys qs (hqs _) z hz
    simp only [Nat.mul_one]
    omega
  · omega

/-- **No long hash query in the port program**: if every hash call of the scheme is on at most
`B` values, and the forger's signing queries and its forgery are on messages of at most `ℓ`
bytes, then no `Thash` query is on more than `B` values and no `H_msg` query on more than `ℓ`
bytes. -/
theorem forsFindOpenP_bad (B ℓ : ℕ) (hB : ∀ xs : List prims.Y, OkLen vp xs → xs.length ≤ B)
    (hlong : ∀ pk, IsQueryBoundP (mainP pk)
      (fun i => isLongQ (S := GeneralScheme.SignatureCore vp prims.core) ℓ i = true) 0)
    (hout : ∀ pk, ∀ z ∈ support (mainP pk), z.1.length ≤ ℓ) :
    IsQueryBoundP (forsFindOpenP optRand mainP pkSeed ys) (fun t => isBadIdx B ℓ t = true) 0 := by
  have hu : ∀ n, ¬ isBadIdx (ι := ℕ ⊕ (St × Blk)) (P := prims.PkSeed) (K := prims.AdrsKey)
      (Y := prims.Y) B ℓ (.inl n) = true := by intro n; simp [isBadIdx]
  have hl : ∀ {β : Type} (oa : OracleComp (OSpec prims (forsG prims)) β),
      IsQueryBoundP oa (fun t => isBadIdx B ℓ t = true) 0 →
      IsQueryBoundP (simulateQ liftG oa) (fun t => isBadIdx B ℓ t = true) 0 :=
    fun oa h => liftG_bound _ oa 0 (IsQueryBoundP.of_imp (fun t ht => by
      rwa [bad_liftIdx] at ht) h)
  have hsec : ∀ d : SecIdx, ¬ isBadIdx (ι := ℕ) (P := prims.PkSeed) (K := prims.AdrsKey)
      (Y := prims.Y) B ℓ (.inr (.inr (.inl d))) = true := by intro d; simp [isBadIdx]
  have hgame : ∀ i : ℕ, ¬ isBadIdx (ι := ℕ) (P := prims.PkSeed) (K := prims.AdrsKey)
      (Y := prims.Y) B ℓ (.inr (.inl i)) = true := by intro i; simp [isBadIdx]
  have hth : ∀ (pk : prims.PkSeed) (key : prims.AdrsKey) (xs : List prims.Y), xs.length ≤ B →
      ¬ isBadIdx B ℓ (thIdx prims ℕ pk key xs) = true := by
    intro pk key xs h; simp [isBadIdx]; omega
  have hhm : ∀ (R : prims.Y) (pk : prims.PkSeed) (root : prims.Y) (m : List Byte),
      m.length ≤ ℓ → ¬ isBadIdx B ℓ (hmIdx prims ℕ R pk root m) = true := by
    intro R pk root m h; simp [isBadIdx]; omega
  have h1 : ∀ y : prims.Y, [y].length ≤ B := fun y => hB [y] (Or.inl rfl)
  unfold forsFindOpenP
  refine isQueryBoundP_bind_zero _ _ (hl _ (np_openKeygen _ pkSeed hsec fun key xs hx =>
    hth _ _ _ (hB xs hx))) fun root => isQueryBoundP_bind (m := 0) (n := 0) ?_ fun z hz =>
      hl _ ((findAnswerO_le _ ⟨pkSeed, root⟩ ys z.2 z.1.1 z.1.2 0 0
        (fun key y => hth _ _ _ (h1 y))
        ((isQueryBoundP_query_iff _ _ _).2 fun h => absurd h (hhm _ _ _ _
          (portRunF_out optRand mainP ⟨pkSeed, root⟩ ys ℓ (hout _) z hz)))
        (fun e he => (isQueryBoundP_query_iff _ _ _).2 fun h => by
          obtain ⟨e', he', rfl⟩ := List.mem_map.1 he
          exact absurd h (hhm _ _ _ _
            (portRunF_msgs optRand mainP ⟨pkSeed, root⟩ ys ℓ (hlong _) z hz e' he')))).mono
        (by simp))
  unfold portRunF
  refine qb_simulateQ_run_zero (p := fun i => isLongQ (S := GeneralScheme.SignatureCore vp prims.core) ℓ i = true)
    (fun t ht s => ?_) (hlong _) []
  rcases t with n | q | msg
  · exact unifStepF optRand _ ys _ hu n s
  · exact portStepF optRand _ ys _ q 0 ((isQueryBoundP_query_iff _ _ _).2 fun h => by
      simp [isBadIdx] at h) s
  · have hm : msg.length ≤ ℓ := by
      simp only [isLongQ, decide_eq_true_eq, not_lt] at ht
      exact ht
    exact signStepF optRand _ ys _ hu msg 0 (fun R => hl _
      (forsSignOpen_le _ ⟨pkSeed, root⟩ ys msg R 0 hsec hgame
        (fun key xs hx => hth _ _ _ (hB xs hx))
        ((isQueryBoundP_query_iff _ _ _).2 fun h => absurd h (hhm _ _ _ _ hm)))) s

end Counts

end Ideal.Realize.Fors

#print axioms Ideal.Realize.Fors.forsSignOpen_le
#print axioms Ideal.Realize.Fors.findAnswerO_le
#print axioms Ideal.Realize.Fors.portRunF_log
#print axioms Ideal.Realize.Fors.portRunF_msgs
#print axioms Ideal.Realize.Fors.forsFindOpenP_port
#print axioms Ideal.Realize.Fors.forsFindOpenP_hashes
#print axioms Ideal.Realize.Fors.forsFindOpenP_hmsg
#print axioms Ideal.Realize.Fors.forsFindOpenP_bad
