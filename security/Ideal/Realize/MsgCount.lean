import Ideal.Realize.MsgPort

/-!
# Query counts of the open `PRF_msg` port programs

* `qb_run_classes`: weighted budget transfer through a stateful handler (two weighted classes of
  source queries, one forbidden class).
* `harnP_bound`: the port harness run of a forger with at most `qf` compression and `qs` signing
  queries (none on a message of more than `ℓ` bytes) makes at most `qf·w + qs·c` `p`-queries,
  if a port query costs `w` and a signing step `c`.
* `verifyM_bound`: verification makes no `p`-query besides its `H_msg` query, if `p` holds of no
  `Thash` query on `1`, `2`, `len` or `k` values.
* `embR_bound`: a program over the hash oracle, embedded.
* `msgOpenWVP_bound`, `msgOpenVP_bound`: the generic count of the two port programs, and its
  instances `*_port`, `*_msg`, `*_hash`, `*_hm`, `*_bad`.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security

namespace Ideal.Realize.Msg

open Reduction Reduction.Lazy Reduction.Open

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! ## Weighted transfer through a stateful handler -/

section Weighted

variable {ι ι' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'} {α σ : Type}

private theorem step_arith' {P : Prop} [Decidable P] {n c : ℕ} (h : ¬ P ∨ 0 < n) :
    (if P then c else 0) + (if P then n - 1 else n) * c = n * c := by
  by_cases hp : P
  · have hn : 0 < n := h.resolve_left (not_not.mpr hp)
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    simp [hp, Nat.succ_mul, Nat.add_comm]
  · simp [hp]

/-- **Weighted budget transfer, stateful.** -/
theorem qb_run_classes {p₀ p₁ p₂ : ι → Prop} [DecidablePred p₀] [DecidablePred p₁]
    [DecidablePred p₂] {q : ι' → Prop} [DecidablePred q]
    {impl : QueryImpl spec (StateT σ (OracleComp spec'))} (c₁ c₂ : ℕ)
    (hstep : ∀ t, ¬ p₀ t → ∀ s, IsQueryBoundP ((impl t).run s) q
      ((if p₁ t then c₁ else 0) + (if p₂ t then c₂ else 0)))
    {oa : OracleComp spec α} {n₁ n₂ : ℕ}
    (h0 : IsQueryBoundP oa p₀ 0) (h1 : IsQueryBoundP oa p₁ n₁) (h2 : IsQueryBoundP oa p₂ n₂)
    (s : σ) :
    IsQueryBoundP ((simulateQ impl oa).run s) q (n₁ * c₁ + n₂ * c₂) := by
  induction oa using OracleComp.inductionOn generalizing n₁ n₂ s with
  | pure x => simp
  | query_bind t mx ih =>
    rw [isQueryBoundP_query_bind_iff] at h0 h1 h2
    have ht0 : ¬ p₀ t := h0.1.resolve_right (Nat.lt_irrefl 0)
    rw [simulateQ_query_bind, StateT.run_bind]
    simp only [OracleQuery.input_query, OracleQuery.cont_query, monadLift_self, id_eq]
    have hb := isQueryBoundP_bind (hstep t ht0 s) fun u _ =>
      ih u.1 (by simpa [ht0] using h0.2 u.1) (h1.2 u.1) (h2.2 u.1) u.2
    refine hb.mono (le_of_eq ?_)
    have e1 := step_arith' (c := c₁) h1.1
    have e2 := step_arith' (c := c₂) h2.1
    omega

end Weighted

/-! ## The port harness -/

section HarnessBound

variable {ι : Type} {X : OracleSpec ι} {σ Sig β : Type}

/-- **Queries of the port harness run.** -/
theorem harnP_bound (p : ℕ ⊕ ι → Prop) [DecidablePred p] (ℓ w c qf qs : ℕ)
    (hu : ∀ n, ¬ p (.inl n))
    (port : St × Blk → OracleComp (unifSpec + X) St)
    (hport : ∀ q, IsQueryBoundP (port q) p w)
    (so : QueryImpl (List Byte →ₒ Sig) (StateT σ (OracleComp (unifSpec + X))))
    (hso : ∀ m s, m.length ≤ ℓ → IsQueryBoundP ((so m).run s) p c)
    (oa : OracleComp (FSpecP Sig) β)
    (hqf : IsQueryBoundP oa (fun i => isPortQ (S := Sig) i = true) qf)
    (hqs : IsQueryBoundP oa (fun i => isSignQ (S := Sig) i = true) qs)
    (hlong : IsQueryBoundP oa (fun i => isLongQ (S := Sig) ℓ i = true) 0) (s : σ) :
    IsQueryBoundP ((simulateQ (harnP port so) oa).run s) p (qf * w + qs * c) := by
  refine qb_run_classes w c (fun t ht s => ?_) hlong hqf hqs s
  rcases t with n | q | m
  · simp only [isPortQ, isSignQ, harnP, StateT.run_monadLift]
    simp only [Bool.false_eq_true, ite_false, Nat.add_zero]
    exact isQueryBoundP_bind_zero _ _
      ((isQueryBoundP_query_iff _ _ _).2 fun h => absurd h (hu n)) fun x =>
        isQueryBoundP_pure _ _ _
  · simp only [isPortQ, isSignQ, harnP, StateT.run_monadLift]
    simp only [ite_true, Bool.false_eq_true, ite_false, Nat.add_zero]
    exact (isQueryBoundP_bind (m := 0) (hport q) fun x _ => isQueryBoundP_pure _ _ _).mono
      (by omega)
  · have hm : m.length ≤ ℓ := by
      simp only [isLongQ, decide_eq_true_eq, not_lt] at ht
      exact ht
    simp only [isPortQ, isSignQ, harnP]
    simp only [ite_true, Bool.false_eq_true, ite_false, Nat.zero_add]
    exact hso m s hm

end HarnessBound

/-! ## Verification -/

section Verify

variable {vp : ValidatedParams} (core : CorePrimitives vp.params) [DecidableEq core.Y]
variable (ph : PublicHashQuery core.PkSeed core.AdrsKey core.Y → Prop) [DecidablePred ph]

/-- Verification makes at most as many `ph`-queries as its `H_msg` query, if `ph` holds of no
`Thash` query on `1`, `2`, `len` or `k` values. -/
theorem verifyM_bound (msg : List Byte) (sig : GeneralScheme.SignatureCore vp core)
    (pk : PublicKeyCore core) (e : ℕ)
    (hth : ∀ key xs, OkLen vp xs → ¬ ph (.thash pk.pkSeed key xs))
    (hm : IsQueryBoundP (PublicHash.hmsg core sig.randomness pk.pkSeed pk.pkRoot msg :
      OracleComp (publicHashSpec core) _) ph e) :
    IsQueryBoundP (GeneralScheme.verifyInternalM vp core msg sig pk :
      OracleComp (publicHashSpec core) Bool) ph e := by
  have hf : ∀ (a : Adrs) (y : core.Y), IsQueryBoundP (PublicHash.f core pk.pkSeed a y :
      OracleComp (publicHashSpec core) core.Y) ph 0 :=
    fun _ _ => (isQueryBoundP_query_iff _ _ _).2 fun h => absurd h (hth _ _ (Or.inl rfl))
  have htl : ∀ (a : Adrs) (ys : List core.Y),
      (ys.length = vp.params.len ∨ ys.length = vp.params.k) →
      IsQueryBoundP (PublicHash.tl core pk.pkSeed a ys :
      OracleComp (publicHashSpec core) core.Y) ph 0 :=
    fun _ ys hys => (isQueryBoundP_query_iff _ _ _).2 fun h =>
      absurd h (hth _ _ (Or.inr (Or.inr hys)))
  have hh : ∀ (a : Adrs) (l r : core.Y),
      IsQueryBoundP (PublicHash.h core pk.pkSeed a l r :
      OracleComp (publicHashSpec core) core.Y) ph 0 :=
    fun _ _ _ => (isQueryBoundP_query_iff _ _ _).2 fun h =>
      absurd h (hth _ _ (Or.inr (Or.inl rfl)))
  unfold GeneralScheme.verifyInternalM GeneralHypertree.verifyM GeneralHypertree.pkFromSigM
    GeneralHypertree.recoverFromPositionM forsPkFromSigM
  refine (isQueryBoundP_bind (m := 0) hm fun digest _ =>
    isQueryBoundP_bind_zero _ _ (np_forsPk ph core hf htl hh _ _ _) fun forsPk =>
      isQueryBoundP_bind_zero _ _ (np_recover ph core hf htl hh pk.pkSeed vp.params.d _ _ _ _)
        fun root => isQueryBoundP_pure _ _ _).mono (by omega)

end Verify

/-! ## Embedded hash programs -/

section Emb

variable {ι κ : Type} {G : OracleSpec ι} {hspec : OracleSpec κ} {D V α : Type}

theorem embR_bound (pg : ι → Prop) (ph : κ → Prop) [DecidablePred pg] [DecidablePred ph]
    (Q : OracleComp hspec α) (n : ℕ) (h : IsQueryBoundP Q ph n) :
    IsQueryBoundP (embR (gspec := G) (D := D) (V := V) Q) (liftP pg ph) n := by
  refine IsQueryBoundP.simulateQ_of_step h (fun t ht => ?_) (fun t ht => ?_)
  · exact (isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos
  · exact (isQueryBoundP_query_iff _ _ _).2 fun h' => absurd h' ht

end Emb

/-! ## The two port programs -/

section Programs

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]
variable (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
  (pkSeedDist : ProbComp prims.PkSeed)

/-- An index of the port programs. -/
abbrev OIdx (prims : Primitives vp.params) : Type :=
  ℕ ⊕ (((St × Blk) ⊕ (prims.Y × List Byte)) ⊕
    (SecIdx ⊕ PublicHashQuery prims.PkSeed prims.AdrsKey prims.Y))

variable (p : OIdx prims → Prop) [DecidablePred p]

/-- Forger hypotheses, for a port forger program. -/
structure PortBounds (mainP : PortForgerProg vp prims) (qf qs ℓ : ℕ) : Prop where
  qf : ∀ pk, IsQueryBoundP (mainP pk)
    (fun i => isPortQ (S := GeneralScheme.SignatureCore vp prims.core) i = true) qf
  qs : ∀ pk, IsQueryBoundP (mainP pk)
    (fun i => isSignQ (S := GeneralScheme.SignatureCore vp prims.core) i = true) qs
  long : ∀ pk, IsQueryBoundP (mainP pk)
    (fun i => isLongQ (S := GeneralScheme.SignatureCore vp prims.core) ℓ i = true) 0
  out : ∀ pk, ∀ z ∈ support (mainP pk), z.1.length ≤ ℓ

theorem forged_len {σ : Type} (mainP : PortForgerProg vp prims) (ℓ : ℕ)
    (hout : ∀ pk, ∀ z ∈ support (mainP pk), z.1.length ≤ ℓ)
    (impl : QueryImpl (FSpecP (GeneralScheme.SignatureCore vp prims.core))
      (StateT σ (OracleComp (OP prims))))
    (pk : PublicKeyCore prims.core) (s : σ) (z)
    (hz : z ∈ support ((simulateQ impl (mainP pk)).run s)) : z.1.1.length ≤ ℓ := by
  have hz' : z.1 ∈ support ((simulateQ impl (mainP pk)).run' s) := by
    rw [StateT.run'_eq, support_map]
    exact ⟨z, hz, rfl⟩
  exact hout pk z.1 (support_simulateQ_run'_subset _ _ _ hz')

/-- **Generic count of the SUF port program.** -/
theorem msgOpenWVP_bound (wO : WinCheckO vp prims) (mainP : PortForgerProg vp prims)
    (qf qs ℓ a c w d : ℕ) (hF : PortBounds mainP qf qs ℓ)
    (hu : ∀ n, ¬ p (.inl n))
    (hk : ∀ pkSeed, IsQueryBoundP (openKeygen prims (GP prims) pkSeed) p a)
    (hsign : ∀ pk m, m.length ≤ ℓ → IsQueryBoundP (msgSignOP optRand pk m) p c)
    (hport : ∀ q, IsQueryBoundP (portO (prims := prims) q) p w)
    (hcheck : ∀ pk f log, f.1.length ≤ ℓ →
      IsQueryBoundP (embR (gspec := GP prims) (D := SecIdx) (V := prims.Y) (wO pk f log)) p d) :
    IsQueryBoundP (msgOpenWVP optRand pkSeedDist wO mainP) p (a + (qf * w + qs * c) + d) := by
  unfold msgOpenWVP msgPreWP
  simp only [bind_assoc, pure_bind]
  refine (isQueryBoundP_bind (n := 0) (liftM_np (gspec := GP prims) p hu pkSeedDist)
    fun pkSeed _ => isQueryBoundP_bind (hk pkSeed) fun root _ =>
      isQueryBoundP_bind (harnP_bound p ℓ w c qf qs hu _ hport _ (fun m s hm => ?_)
        _ (hF.qf _) (hF.qs _) (hF.long _) []) fun z hz =>
          hcheck _ _ _ (forged_len mainP ℓ hF.out _ _ _ z hz)).mono (by omega)
  simp only [sigSignOracle, run_appendLog_apply]
  exact isQueryBoundP_bind (m := 0) (hsign _ m hm) fun u _ => isQueryBoundP_pure _ _ _

/-- **Generic count of the EUF port program.** -/
theorem msgOpenVP_bound (mainP : PortForgerProg vp prims)
    (qf qs ℓ a c w d : ℕ) (hF : PortBounds mainP qf qs ℓ)
    (hu : ∀ n, ¬ p (.inl n))
    (hk : ∀ pkSeed, IsQueryBoundP (openKeygen prims (GP prims) pkSeed) p a)
    (hsign : ∀ pk m, m.length ≤ ℓ → IsQueryBoundP (msgSignOP optRand pk m) p c)
    (hport : ∀ q, IsQueryBoundP (portO (prims := prims) q) p w)
    (hcheck : ∀ pk msgs (msg : List Byte) sig, msg.length ≤ ℓ →
      IsQueryBoundP (embR (gspec := GP prims) (D := SecIdx) (V := prims.Y)
        (eufCheckO pk msgs msg sig)) p d) :
    IsQueryBoundP (msgOpenVP optRand pkSeedDist mainP) p (a + (qf * w + qs * c) + d) := by
  unfold msgOpenVP msgPreP
  simp only [bind_assoc, pure_bind]
  refine (isQueryBoundP_bind (n := 0) (liftM_np (gspec := GP prims) p hu pkSeedDist)
    fun pkSeed _ => isQueryBoundP_bind (hk pkSeed) fun root _ =>
      isQueryBoundP_bind (harnP_bound p ℓ w c qf qs hu _ hport _ (fun m s hm => ?_)
        _ (hF.qf _) (hF.qs _) (hF.long _) []) fun z hz =>
          hcheck _ _ _ _ (forged_len mainP ℓ hF.out _ _ _ z hz)).mono (by omega)
  simp only [harnessSignOracle, StateT.run_bind, StateT.run_monadLift, bind_assoc]
  exact isQueryBoundP_bind (m := 0) (hsign _ m hm) fun u _ => by simp

end Programs

/-! ## The query classes -/

section Classes

variable {P K Y : Type}

/-- A `Thash` query. -/
def isTh : PublicHashQuery P K Y → Bool
  | .thash _ _ _ => true
  | _ => false

/-- An `H_msg` query. -/
def isHm : PublicHashQuery P K Y → Bool
  | .hmsg _ _ _ _ => true
  | _ => false

/-- A hash query on too many values / bytes. -/
def longH (B ℓ : ℕ) : PublicHashQuery P K Y → Bool
  | .thash _ _ xs => decide (B < xs.length)
  | .hmsg _ _ _ M => decide (ℓ < M.length)

/-- A `PRF_msg` game query on a message of more than `ℓ` bytes. -/
def longG {A : Type} (ℓ : ℕ) : A ⊕ (Y × List Byte) → Bool
  | .inl _ => false
  | .inr d => decide (ℓ < d.2.length)

variable {A D : Type}

/-- Port queries. -/
abbrev pPort : ℕ ⊕ ((A ⊕ (Y × List Byte)) ⊕ (D ⊕ PublicHashQuery P K Y)) → Prop :=
  liftP (fun t => t.isLeft = true) (fun _ => False)
/-- `PRF_msg` game queries. -/
abbrev pMsg : ℕ ⊕ ((A ⊕ (Y × List Byte)) ⊕ (D ⊕ PublicHashQuery P K Y)) → Prop :=
  liftP (fun t => t.isRight = true) (fun _ => False)
/-- Hash queries. -/
abbrev pHash : ℕ ⊕ ((A ⊕ (Y × List Byte)) ⊕ (D ⊕ PublicHashQuery P K Y)) → Prop :=
  liftP (fun _ => False) (fun _ => True)
/-- `Thash` queries. -/
abbrev pTh : ℕ ⊕ ((A ⊕ (Y × List Byte)) ⊕ (D ⊕ PublicHashQuery P K Y)) → Prop :=
  liftP (fun _ => False) (fun q => isTh q = true)
/-- `H_msg` queries. -/
abbrev pHm : ℕ ⊕ ((A ⊕ (Y × List Byte)) ⊕ (D ⊕ PublicHashQuery P K Y)) → Prop :=
  liftP (fun _ => False) (fun q => isHm q = true)
/-- Too long queries. -/
abbrev pBad (B ℓ : ℕ) : ℕ ⊕ ((A ⊕ (Y × List Byte)) ⊕ (D ⊕ PublicHashQuery P K Y)) → Prop :=
  liftP (fun t => longG ℓ t = true) (fun q => longH B ℓ q = true)

theorem pTh_imp (t : ℕ ⊕ ((A ⊕ (Y × List Byte)) ⊕ (D ⊕ PublicHashQuery P K Y))) :
    pTh t → pHash t := by
  rcases t with n | t | d | q <;> simp [liftP]

theorem pHash_kind (t : ℕ ⊕ ((A ⊕ (Y × List Byte)) ⊕ (D ⊕ PublicHashQuery P K Y))) :
    pHash t → Lazy.kind t = .hash := by
  rcases t with n | t | d | q <;> simp [liftP, Lazy.kind]

end Classes

section Instances

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]
variable (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
  (pkSeedDist : ProbComp prims.PkSeed)

theorem msgSignOP_bound (p : OIdx prims → Prop) [DecidablePred p] (hu : ∀ n, ¬ p (.inl n))
    (pk : PublicKeyCore prims.core) (m : List Byte) (cg ch : ℕ)
    (hg : ∀ addrnd, IsQueryBoundP (gameQ prims (GP prims) (.inr (addrnd, m))) p cg)
    (hs : ∀ R, IsQueryBoundP (openSign prims (GP prims) m pk.pkSeed pk.pkRoot R) p ch) :
    IsQueryBoundP (msgSignOP optRand pk m) p (cg + ch) := by
  unfold msgSignOP
  exact (isQueryBoundP_bind (n := 0) (liftM_np (gspec := GP prims) p hu _) fun addrnd _ =>
    isQueryBoundP_bind (hg addrnd) fun R _ => hs R).mono (by omega)

theorem gameQ_bound (p : OIdx prims → Prop) [DecidablePred p] (t : (GP prims).Domain) :
    IsQueryBoundP (gameQ prims (GP prims) t) p (if p (.inr (.inl t)) then 1 else 0) :=
  (isQueryBoundP_query_iff _ _ _).2 fun h => by simp [h]

/-- Forger hypotheses, transferred: a byte-level port forger with at most `qf` compression and
`qs` signing queries, none on more than `ℓ` bytes, and a forged message of at most `ℓ` bytes,
gives a typed port forger with the same bounds. -/
theorem portBounds_typedC (codec : CoreWireCodec vp.params prims.core)
    (mb : List Byte → OracleComp (FSpecP (List Byte)) (List Byte × List Byte)) (qf qs ℓ : ℕ)
    (hqf : ∀ pk, IsQueryBoundP (mb pk) (fun i => isPortQ (S := List Byte) i = true) qf)
    (hqs : ∀ pk, IsQueryBoundP (mb pk) (fun i => isSignQ (S := List Byte) i = true) qs)
    (hlong : ∀ pk, IsQueryBoundP (mb pk) (fun i => isLongQ (S := List Byte) ℓ i = true) 0)
    (hout : ∀ pk, ∀ z ∈ support (mb pk), z.1.length ≤ ℓ) :
    PortBounds (prims := prims) (typedC codec default mb) qf qs ℓ where
  qf pk := typedP_bound (prims := prims) codec (isPortQ (S := List Byte)) isPortQ
    (fun _ _ _ => ⟨rfl, rfl, rfl⟩) mb pk qf (hqf _)
  qs pk := typedP_bound (prims := prims) codec (isSignQ (S := List Byte)) isSignQ
    (fun _ _ _ => ⟨rfl, rfl, rfl⟩) mb pk qs (hqs _)
  long pk := typedP_bound (prims := prims) codec (isLongQ (S := List Byte) ℓ) (isLongQ ℓ)
    (fun _ _ _ => ⟨rfl, rfl, rfl⟩) mb pk 0 (hlong _)
  out pk z hz := by
    obtain ⟨out, hout', he⟩ := typedP_out (prims := prims) codec mb pk z hz
    rw [he]
    exact hout _ out hout'

variable {mainP : PortForgerProg vp prims} {qf qs ℓ : ℕ}

private theorem hsec_l {pg : _ → Prop} {ph : _ → Prop} [DecidablePred pg] [DecidablePred ph] :
    ∀ d : SecIdx, ¬ (liftP pg ph : OIdx prims → Prop) (.inr (.inr (.inl d))) := by
  intro d; simp [liftP]

private theorem hu_l {pg : _ → Prop} {ph : _ → Prop} [DecidablePred pg] [DecidablePred ph] :
    ∀ n : ℕ, ¬ (liftP pg ph : OIdx prims → Prop) (.inl n) := by
  intro n; simp [liftP]

section Suf

variable (hF : PortBounds mainP qf qs ℓ)
include hF

/-- **Port queries of the SUF port program**: at most `qf`. -/
theorem msgOpenWVP_port :
    IsQueryBoundP (msgOpenWVP optRand pkSeedDist sufCheckO mainP) pPort qf := by
  refine (msgOpenWVP_bound optRand pkSeedDist pPort sufCheckO mainP qf qs ℓ 0 0 1 0 hF hu_l
    (fun pkSeed => np_openKeygen _ pkSeed hsec_l fun key xs _ => by simp [liftP])
    (fun pk m _ => (msgSignOP_bound optRand pPort hu_l pk m 0 0
      (fun a => (gameQ_bound _ _).mono (by simp [liftP]))
      (fun R => np_openSign _ m _ _ R hsec_l (fun key xs _ => by simp [liftP])
        (by simp [liftP]))))
    (fun q => (gameQ_bound _ _).mono (by simp [liftP]))
    (fun pk f log _ => embR_bound _ _ _ 0 (IsQueryBoundP.of_imp (fun t ht => ht.elim)
      (isQueryBoundP_false _ 0)))).mono (by omega)

/-- **`PRF_msg` game queries of the SUF port program**: at most `qs`. -/
theorem msgOpenWVP_msg :
    IsQueryBoundP (msgOpenWVP optRand pkSeedDist sufCheckO mainP) pMsg qs := by
  refine (msgOpenWVP_bound optRand pkSeedDist pMsg sufCheckO mainP qf qs ℓ 0 1 0 0 hF hu_l
    (fun pkSeed => np_openKeygen _ pkSeed hsec_l fun key xs _ => by simp [liftP])
    (fun pk m _ => (msgSignOP_bound optRand pMsg hu_l pk m 1 0
      (fun a => (gameQ_bound _ _).mono (by split_ifs <;> omega))
      (fun R => np_openSign _ m _ _ R hsec_l (fun key xs _ => by simp [liftP])
        (by simp [liftP]))))
    (fun q => (gameQ_bound _ _).mono (by simp [liftP]))
    (fun pk f log _ => embR_bound _ _ _ 0 (IsQueryBoundP.of_imp (fun t ht => ht.elim)
      (isQueryBoundP_false _ 0)))).mono (by omega)

/-- **Hash queries of the SUF port program**: `keygenHashes + qs·signHashes + (1 + verifyHashes)`
(the count of `Reduction.Open.msgOpenWV_suf_hashes`). -/
theorem msgOpenWVP_hash :
    IsQueryBoundP (msgOpenWVP optRand pkSeedDist sufCheckO mainP) pHash
      (keygenHashes vp + qs * signHashes vp + (1 + Resources2.verifyHashes vp)) := by
  refine (msgOpenWVP_bound optRand pkSeedDist pHash sufCheckO mainP qf qs ℓ (keygenHashes vp)
    (signHashes vp) 0 (1 + Resources2.verifyHashes vp) hF hu_l
    (fun pkSeed => (IsQueryBoundP.of_imp pHash_kind
      (openKeygen_kindBound (gspec := GP prims) .hash pkSeed)).mono (by
        simpa [ind] using keygenB_hash (vp := vp)))
    (fun pk m _ => (msgSignOP_bound optRand pHash hu_l pk m 0 (signHashes vp)
      (fun a => (gameQ_bound _ _).mono (by simp [liftP]))
      (fun R => (IsQueryBoundP.of_imp pHash_kind
        (openSign_kindBound (gspec := GP prims) .hash m _ _ R)).mono (by
          simpa [ind] using signB_hash (vp := vp)))).mono (by omega))
    (fun q => (gameQ_bound _ _).mono (by simp [liftP]))
    (fun pk f log _ => embR_bound _ _ _ _
      ((sufCheckO_total pk f log).isQueryBoundP (p := fun _ => True)))).mono (by
        simp only [Nat.mul_zero, Nat.zero_add, le_refl])

/-- **`H_msg` queries of the SUF port program**: one per signing query and one for
verification. -/
theorem msgOpenWVP_hm :
    IsQueryBoundP (msgOpenWVP optRand pkSeedDist sufCheckO mainP) pHm (qs + 1) := by
  refine (msgOpenWVP_bound optRand pkSeedDist pHm sufCheckO mainP qf qs ℓ 0 1 0 1 hF hu_l
    (fun pkSeed => np_openKeygen _ pkSeed hsec_l fun key xs _ => by simp [liftP, isHm])
    (fun pk m _ => (msgSignOP_bound optRand pHm hu_l pk m 0 1
      (fun a => (gameQ_bound _ _).mono (by simp [liftP]))
      (fun R => openSign_one _ m _ _ R hsec_l (fun key xs _ => by simp [liftP, isHm]))).mono
        (by omega))
    (fun q => (gameQ_bound _ _).mono (by simp [liftP]))
    (fun pk f log _ => embR_bound _ _ _ 1 (by
      unfold sufCheckO
      rw [isQueryBoundP_map_iff]
      exact verifyM_bound prims.core _ f.1 f.2 pk 1 (fun key xs _ => by simp [isHm])
        ((isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos)))).mono (by omega)

/-- **No too long query in the SUF port program.** -/
theorem msgOpenWVP_bad (B : ℕ) (hB : ∀ xs : List prims.Y, OkLen vp xs → xs.length ≤ B) :
    IsQueryBoundP (msgOpenWVP optRand pkSeedDist sufCheckO mainP) (pBad B ℓ) 0 := by
  refine (msgOpenWVP_bound optRand pkSeedDist (pBad B ℓ) sufCheckO mainP qf qs ℓ 0 0 0 0 hF hu_l
    (fun pkSeed => np_openKeygen _ pkSeed hsec_l fun key xs hx => by
      simp [liftP, longH]; exact hB xs hx)
    (fun pk m hm => (msgSignOP_bound optRand (pBad B ℓ) hu_l pk m 0 0
      (fun a => (gameQ_bound _ _).mono (by simp [liftP, longG]; omega))
      (fun R => np_openSign _ m _ _ R hsec_l (fun key xs hx => by
          simp [liftP, longH]; exact hB xs hx)
        (by simp [liftP, longH]; omega))))
    (fun q => (gameQ_bound _ _).mono (by simp [liftP, longG]))
    (fun pk f log hf => embR_bound _ _ _ 0 (by
      unfold sufCheckO
      rw [isQueryBoundP_map_iff]
      exact verifyM_bound prims.core _ f.1 f.2 pk 0 (fun key xs hx => by
          simp [longH]; exact hB xs hx)
        ((isQueryBoundP_query_iff _ _ _).2 fun h => by simp [longH] at h; omega)))).mono
          (by omega)

end Suf

section Euf

variable (hF : PortBounds mainP qf qs ℓ)
include hF

theorem msgOpenVP_port : IsQueryBoundP (msgOpenVP optRand pkSeedDist mainP) pPort qf := by
  refine (msgOpenVP_bound optRand pkSeedDist pPort mainP qf qs ℓ 0 0 1 0 hF hu_l
    (fun pkSeed => np_openKeygen _ pkSeed hsec_l fun key xs _ => by simp [liftP])
    (fun pk m _ => (msgSignOP_bound optRand pPort hu_l pk m 0 0
      (fun a => (gameQ_bound _ _).mono (by simp [liftP]))
      (fun R => np_openSign _ m _ _ R hsec_l (fun key xs _ => by simp [liftP])
        (by simp [liftP]))))
    (fun q => (gameQ_bound _ _).mono (by simp [liftP]))
    (fun pk msgs msg sig _ => embR_bound _ _ _ 0 (IsQueryBoundP.of_imp (fun t ht => ht.elim)
      (isQueryBoundP_false _ 0)))).mono (by omega)

theorem msgOpenVP_msg : IsQueryBoundP (msgOpenVP optRand pkSeedDist mainP) pMsg qs := by
  refine (msgOpenVP_bound optRand pkSeedDist pMsg mainP qf qs ℓ 0 1 0 0 hF hu_l
    (fun pkSeed => np_openKeygen _ pkSeed hsec_l fun key xs _ => by simp [liftP])
    (fun pk m _ => (msgSignOP_bound optRand pMsg hu_l pk m 1 0
      (fun a => (gameQ_bound _ _).mono (by split_ifs <;> omega))
      (fun R => np_openSign _ m _ _ R hsec_l (fun key xs _ => by simp [liftP])
        (by simp [liftP]))))
    (fun q => (gameQ_bound _ _).mono (by simp [liftP]))
    (fun pk msgs msg sig _ => embR_bound _ _ _ 0 (IsQueryBoundP.of_imp (fun t ht => ht.elim)
      (isQueryBoundP_false _ 0)))).mono (by omega)

theorem msgOpenVP_hash :
    IsQueryBoundP (msgOpenVP optRand pkSeedDist mainP) pHash
      (keygenHashes vp + qs * signHashes vp + (1 + Resources2.verifyHashes vp)) := by
  refine (msgOpenVP_bound optRand pkSeedDist pHash mainP qf qs ℓ (keygenHashes vp)
    (signHashes vp) 0 (1 + Resources2.verifyHashes vp) hF hu_l
    (fun pkSeed => (IsQueryBoundP.of_imp pHash_kind
      (openKeygen_kindBound (gspec := GP prims) .hash pkSeed)).mono (by
        simpa [ind] using keygenB_hash (vp := vp)))
    (fun pk m _ => (msgSignOP_bound optRand pHash hu_l pk m 0 (signHashes vp)
      (fun a => (gameQ_bound _ _).mono (by simp [liftP]))
      (fun R => (IsQueryBoundP.of_imp pHash_kind
        (openSign_kindBound (gspec := GP prims) .hash m _ _ R)).mono (by
          simpa [ind] using signB_hash (vp := vp)))).mono (by omega))
    (fun q => (gameQ_bound _ _).mono (by simp [liftP]))
    (fun pk msgs msg sig _ => embR_bound _ _ _ _
      ((eufCheckO_total pk msgs msg sig).isQueryBoundP (p := fun _ => True)))).mono (by
        simp only [Nat.mul_zero, Nat.zero_add, le_refl])

theorem msgOpenVP_hm : IsQueryBoundP (msgOpenVP optRand pkSeedDist mainP) pHm (qs + 1) := by
  refine (msgOpenVP_bound optRand pkSeedDist pHm mainP qf qs ℓ 0 1 0 1 hF hu_l
    (fun pkSeed => np_openKeygen _ pkSeed hsec_l fun key xs _ => by simp [liftP, isHm])
    (fun pk m _ => (msgSignOP_bound optRand pHm hu_l pk m 0 1
      (fun a => (gameQ_bound _ _).mono (by simp [liftP]))
      (fun R => openSign_one _ m _ _ R hsec_l (fun key xs _ => by simp [liftP, isHm]))).mono
        (by omega))
    (fun q => (gameQ_bound _ _).mono (by simp [liftP]))
    (fun pk msgs msg sig _ => embR_bound _ _ _ 1 (by
      unfold eufCheckO
      rw [isQueryBoundP_map_iff]
      exact verifyM_bound prims.core _ msg sig pk 1 (fun key xs _ => by simp [isHm])
        ((isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos)))).mono (by omega)

theorem msgOpenVP_bad (B : ℕ) (hB : ∀ xs : List prims.Y, OkLen vp xs → xs.length ≤ B) :
    IsQueryBoundP (msgOpenVP optRand pkSeedDist mainP) (pBad B ℓ) 0 := by
  refine (msgOpenVP_bound optRand pkSeedDist (pBad B ℓ) mainP qf qs ℓ 0 0 0 0 hF hu_l
    (fun pkSeed => np_openKeygen _ pkSeed hsec_l fun key xs hx => by
      simp [liftP, longH]; exact hB xs hx)
    (fun pk m hm => (msgSignOP_bound optRand (pBad B ℓ) hu_l pk m 0 0
      (fun a => (gameQ_bound _ _).mono (by simp [liftP, longG]; omega))
      (fun R => np_openSign _ m _ _ R hsec_l (fun key xs hx => by
          simp [liftP, longH]; exact hB xs hx)
        (by simp [liftP, longH]; omega))))
    (fun q => (gameQ_bound _ _).mono (by simp [liftP, longG]))
    (fun pk msgs msg sig hm => embR_bound _ _ _ 0 (by
      unfold eufCheckO
      rw [isQueryBoundP_map_iff]
      exact verifyM_bound prims.core _ msg sig pk 0 (fun key xs hx => by
          simp [longH]; exact hB xs hx)
        ((isQueryBoundP_query_iff _ _ _).2 fun h => by simp [longH] at h; omega)))).mono
          (by omega)

end Euf

end Instances

end Ideal.Realize.Msg

#print axioms Ideal.Realize.Msg.qb_run_classes
#print axioms Ideal.Realize.Msg.harnP_bound
#print axioms Ideal.Realize.Msg.verifyM_bound
#print axioms Ideal.Realize.Msg.msgOpenWVP_bound
#print axioms Ideal.Realize.Msg.msgOpenVP_bound
#print axioms Ideal.Realize.Msg.msgOpenWVP_port
#print axioms Ideal.Realize.Msg.msgOpenWVP_hash
#print axioms Ideal.Realize.Msg.msgOpenWVP_hm
#print axioms Ideal.Realize.Msg.msgOpenWVP_bad
#print axioms Ideal.Realize.Msg.msgOpenVP_bad
