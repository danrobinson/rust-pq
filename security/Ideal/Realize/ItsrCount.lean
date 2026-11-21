import Ideal.Realize.ItsrOpen

/-!
# Queries of the open ITSR port program (ITSR realiser)

For a typed port forger `mainP` with at most `qf` compression queries, at most `qs` signing
queries, signing queries and forgery on messages of at most `ℓ` bytes, the program
`itsrOpenP optRand pkSeedDist mainP` makes

* `itsrOpenP_port`: at most `qf` port queries;
* `itsrOpenP_tgt`: at most `qs` target queries (one per signing query, at most);
* `itsrOpenP_hashes`: at most `keygenHashes + qs·signHashes` hash queries (the count of
  `Reduction.Open.itsrOpen_hashes`);
* `itsrOpenP_hmsg`: at most `qs` `H_msg` queries;
* `itsrOpenP_badKey`: no `Thash` query on other than `1` or `2` values whose key fails a
  predicate `kp` that holds at every `WOTS_PK` / `FORS_ROOTS` address key;
* `itsrOpenP_bad`: no `Thash` query on more than `B` values, no `H_msg` query on more than `ℓ`
  bytes (`Ideal.Realize.isBadIdx`);
* `itsrOpenP_longTgt`: no target query on a message of more than `ℓ` bytes;
* `itsrOpenP_out`: the returned message has at most `ℓ` bytes.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security

namespace Ideal.Realize.Itsr

open Reduction Reduction.Lazy Ideal.Realize

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

section Count

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]

attribute [local instance] Lazy.openQ

/-- Query indices of the open port program. -/
abbrev IdxI (prims : Primitives vp.params) : Type :=
  ℕ ⊕ ((ItsrIn prims ⊕ (St × Blk)) ⊕ (SecIdx ⊕ PublicHashQuery prims.PkSeed prims.AdrsKey prims.Y))

/-- A port (compression) query. -/
def isPortI : IdxI prims → Bool
  | .inr (.inl (.inr _)) => true
  | _ => false

/-- A target query. -/
def isTgtI : IdxI prims → Bool
  | .inr (.inl (.inl _)) => true
  | _ => false

/-- A target query on a message of more than `ℓ` bytes. -/
def isLongTgtI (ℓ : ℕ) : IdxI prims → Bool
  | .inr (.inl (.inl x)) => decide (ℓ < x.2.2.length)
  | _ => false

/-- A `Thash` query on other than one or two values whose key fails `kp`. -/
def isBadKeyI (kp : prims.AdrsKey → Bool) : IdxI prims → Bool
  | .inr (.inr (.inr (.thash _ key xs))) =>
      !(decide (xs.length = 1) || decide (xs.length = 2)) && !kp key
  | _ => false

variable (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
  (pkSeedDist : ProbComp prims.PkSeed) (mainP : PortForgerProg vp prims)
variable (p : IdxI prims → Prop) [DecidablePred p]

/-! ### Steps -/

theorem unifStepI (hu : ∀ n, ¬ p (.inl n)) (pkSeed : prims.PkSeed) (root : prims.Y) (n : ℕ)
    (s : G2Log prims) :
    IsQueryBoundP ((portImplI optRand pkSeed root (.inl n)).run s) p 0 := by
  simp only [portImplI, QueryImpl.liftTarget_apply, StateT.run_monadLift]
  exact isQueryBoundP_bind_zero _ _
    (liftM_np (gspec := gI prims) p hu (liftM (unifSpec.query n) : ProbComp _)) fun x =>
      isQueryBoundP_pure _ (x, s) _

theorem portStepI (pkSeed : prims.PkSeed) (root : prims.Y) (q : St × Blk) (s : G2Log prims)
    (c : ℕ) (h : IsQueryBoundP (gameQ prims (gI prims) (.inr q)) p c) :
    IsQueryBoundP ((portImplI optRand pkSeed root (.inr (.inl q))).run s) p c := by
  show IsQueryBoundP ((liftM (gameQ prims (gI prims) (.inr q)) :
    StateT (G2Log prims) (OracleComp (OSpec prims (gI prims))) St).run s) _ _
  rw [StateT.run_monadLift]
  exact (isQueryBoundP_bind (m := 0) h fun x _ => isQueryBoundP_pure _ (x, s) _).mono (by omega)

theorem randP_bound (pkSeed : prims.PkSeed) (root : prims.Y) (log : G2Log prims) (m : List Byte)
    (a : prims.Y) (c : ℕ)
    (h : IsQueryBoundP (gameQ prims (gI prims) (.inl (pkSeed, root, m))) p c) :
    IsQueryBoundP (randP pkSeed root log m a) p c := by
  unfold randP
  split
  · exact (isQueryBoundP_pure _ _ _).mono (Nat.zero_le _)
  · exact h

theorem signStepI (hu : ∀ n, ¬ p (.inl n)) (pkSeed : prims.PkSeed) (root : prims.Y)
    (m : List Byte) (s : G2Log prims) (c₁ c₂ : ℕ)
    (hr : IsQueryBoundP (gameQ prims (gI prims) (.inl (pkSeed, root, m))) p c₁)
    (hs : ∀ R, IsQueryBoundP (openSign prims (gI prims) m pkSeed root R) p c₂) :
    IsQueryBoundP ((portImplI optRand pkSeed root (.inr (.inr m))).run s) p (c₁ + c₂) := by
  show IsQueryBoundP ((logSignOracle optRand ⟨pkSeed, root⟩ (randP pkSeed root)
    (fun m R => openSign prims (gI prims) m pkSeed root R) m).run s) _ _
  rw [logSignOracle_run]
  exact (isQueryBoundP_bind (liftM_np (gspec := gI prims) p hu _) fun a _ =>
    isQueryBoundP_bind (randP_bound p pkSeed root s m a c₁ hr) fun R _ =>
      isQueryBoundP_bind (m := 0) (hs R) fun sig _ => isQueryBoundP_pure _ _ _).mono (by omega)

theorem query_np {t : IdxI prims} (ht : ¬ p t) :
    IsQueryBoundP (liftM ((OSpec prims (gI prims)).query t) : OracleComp (OSpec prims (gI prims)) _)
      p 0 :=
  (isQueryBoundP_query_iff _ _ _).2 fun h => absurd h ht

theorem query_one (t : IdxI prims) :
    IsQueryBoundP (liftM ((OSpec prims (gI prims)).query t) : OracleComp (OSpec prims (gI prims)) _)
      p 1 :=
  (isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos

/-- Queries of the port program from those of key generation and of the forger's run. -/
theorem itsrOpenP_bound (hu : ∀ n, ¬ p (.inl n)) (a b : ℕ)
    (hk : ∀ pkSeed, IsQueryBoundP (openKeygen prims (gI prims) pkSeed) p a)
    (hrun : ∀ pkSeed root, IsQueryBoundP
      ((simulateQ (portImplI optRand pkSeed root) (mainP ⟨pkSeed, root⟩)).run []) p b) :
    IsQueryBoundP (itsrOpenP optRand pkSeedDist mainP) p (a + b) := by
  unfold itsrOpenP
  exact (isQueryBoundP_bind (liftM_np (gspec := gI prims) p hu pkSeedDist) fun pkSeed _ =>
    isQueryBoundP_bind (hk pkSeed) fun root _ =>
      isQueryBoundP_bind (m := 0) (hrun pkSeed root) fun z _ => isQueryBoundP_pure _ _ _).mono
    (by omega)

/-! ### The counts -/

variable {qf qs ℓ : ℕ}

theorem itsrOpenP_port
    (hqf : ∀ pk, IsQueryBoundP (mainP pk)
      (fun i => isPortQ (S := GeneralScheme.SignatureCore vp prims.core) i = true) qf) :
    IsQueryBoundP (itsrOpenP optRand pkSeedDist mainP) (fun t => isPortI t = true) qf := by
  have hu : ∀ n, ¬ isPortI (prims := prims) (.inl n) = true := by intro n; simp [isPortI]
  refine (itsrOpenP_bound optRand pkSeedDist mainP _ hu 0 qf (fun pkSeed => ?_)
    (fun pkSeed root => ?_)).mono (by omega)
  · exact np_openKeygen _ pkSeed (fun d => by simp [isPortI]) fun key xs _ => by simp [isPortI]
  · refine IsQueryBoundP.simulateQ_run_of_step (hqf _) (fun t ht s => ?_) (fun t ht s => ?_) []
    · rcases t with n | q | m
      · simp [isPortQ] at ht
      · exact portStepI optRand _ pkSeed root q s 1 (query_one _ _)
      · simp [isPortQ] at ht
    · rcases t with n | q | m
      · exact unifStepI optRand _ hu pkSeed root n s
      · exact absurd rfl ht
      · exact (signStepI optRand _ hu pkSeed root m s 0 0 (query_np _ (by simp [isPortI]))
          fun R => np_openSign _ m pkSeed root R (fun d => by simp [isPortI])
            (fun key xs _ => by simp [isPortI]) (by simp [isPortI])).mono (by omega)

theorem itsrOpenP_tgt
    (hqs : ∀ pk, IsQueryBoundP (mainP pk)
      (fun i => isSignQ (S := GeneralScheme.SignatureCore vp prims.core) i = true) qs) :
    IsQueryBoundP (itsrOpenP optRand pkSeedDist mainP) (fun t => isTgtI t = true) qs := by
  have hu : ∀ n, ¬ isTgtI (prims := prims) (.inl n) = true := by intro n; simp [isTgtI]
  refine (itsrOpenP_bound optRand pkSeedDist mainP _ hu 0 qs (fun pkSeed => ?_)
    (fun pkSeed root => ?_)).mono (by omega)
  · exact np_openKeygen _ pkSeed (fun d => by simp [isTgtI]) fun key xs _ => by simp [isTgtI]
  · refine IsQueryBoundP.simulateQ_run_of_step (hqs _) (fun t ht s => ?_) (fun t ht s => ?_) []
    · rcases t with n | q | m
      · simp [isSignQ] at ht
      · simp [isSignQ] at ht
      · exact (signStepI optRand _ hu pkSeed root m s 1 0 (query_one _ _)
          fun R => np_openSign _ m pkSeed root R (fun d => by simp [isTgtI])
            (fun key xs _ => by simp [isTgtI]) (by simp [isTgtI])).mono (by omega)
    · rcases t with n | q | m
      · exact unifStepI optRand _ hu pkSeed root n s
      · exact portStepI optRand _ pkSeed root q s 0 (query_np _ (by simp [isTgtI]))
      · exact absurd rfl ht

theorem itsrOpenP_hashes
    (hqs : ∀ pk, IsQueryBoundP (mainP pk)
      (fun i => isSignQ (S := GeneralScheme.SignatureCore vp prims.core) i = true) qs) :
    IsQueryBoundP (itsrOpenP optRand pkSeedDist mainP) (fun t => Lazy.kind t = .hash)
      (Lazy.keygenHashes vp + qs * Lazy.signHashes vp) := by
  have hu : ∀ n, ¬ Lazy.kind (ι := gI prims |>.Domain) (D := SecIdx)
      (κ := PublicHashQuery prims.PkSeed prims.AdrsKey prims.Y) (.inl n) = .hash := by
    intro n; simp [Lazy.kind]
  refine (itsrOpenP_bound optRand pkSeedDist mainP _ hu _ (qs * Lazy.signB vp 0 1)
    (fun pkSeed => Lazy.openKeygen_kindBound .hash pkSeed) (fun pkSeed root => ?_)).mono ?_
  · refine IsQueryBoundP.simulateQ_run_of_step_le (hqs _) (fun t ht s => ?_)
      (fun t ht s => ?_) []
    · rcases t with n | q | m
      · simp [isSignQ] at ht
      · simp [isSignQ] at ht
      · exact (signStepI optRand _ hu pkSeed root m s 0 _
          (query_np _ (by simp [Lazy.kind]))
          fun R => by
            simpa [Lazy.ind] using
              Lazy.openSign_kindBound (gspec := gI prims) .hash m pkSeed root R).mono
          (by omega)
    · rcases t with n | q | m
      · exact unifStepI optRand _ hu pkSeed root n s
      · exact portStepI optRand _ pkSeed root q s 0 (query_np _ (by simp [Lazy.kind]))
      · exact absurd rfl ht
  · have h1 : Lazy.keygenB vp (Lazy.ind .hash .sec) (Lazy.ind .hash .hash) ≤
        Lazy.keygenHashes vp := by
      simpa [Lazy.ind] using Lazy.keygenB_hash (vp := vp)
    have h2 : qs * Lazy.signB vp 0 1 ≤ qs * Lazy.signHashes vp :=
      Nat.mul_le_mul_left _ Lazy.signB_hash
    omega

theorem itsrOpenP_hmsg
    (hqs : ∀ pk, IsQueryBoundP (mainP pk)
      (fun i => isSignQ (S := GeneralScheme.SignatureCore vp prims.core) i = true) qs) :
    IsQueryBoundP (itsrOpenP optRand pkSeedDist mainP) (fun t => isHmsgIdx t = true) qs := by
  have hu : ∀ n, ¬ isHmsgIdx (ι := ItsrIn prims ⊕ (St × Blk)) (P := prims.PkSeed)
      (K := prims.AdrsKey) (Y := prims.Y) (.inl n) = true := by intro n; simp [isHmsgIdx]
  refine (itsrOpenP_bound optRand pkSeedDist mainP _ hu 0 qs (fun pkSeed => ?_)
    (fun pkSeed root => ?_)).mono (by omega)
  · exact np_openKeygen _ pkSeed (fun d => by simp [isHmsgIdx])
      fun key xs _ => by simp [isHmsgIdx]
  · refine IsQueryBoundP.simulateQ_run_of_step (hqs _) (fun t ht s => ?_) (fun t ht s => ?_) []
    · rcases t with n | q | m
      · simp [isSignQ] at ht
      · simp [isSignQ] at ht
      · exact (signStepI optRand _ hu pkSeed root m s 0 1 (query_np _ (by simp [isHmsgIdx]))
          fun R => openSign_one _ m pkSeed root R (fun d => by simp [isHmsgIdx])
            (fun key xs _ => by simp [isHmsgIdx])).mono (by omega)
    · rcases t with n | q | m
      · exact unifStepI optRand _ hu pkSeed root n s
      · exact portStepI optRand _ pkSeed root q s 0 (query_np _ (by simp [isHmsgIdx]))
      · exact absurd rfl ht

theorem itsrOpenP_badKey (kp : prims.AdrsKey → Bool)
    (hkW : ∀ b, kp (prims.adrsToKey (wotsPkAdrs b)) = true)
    (hkR : ∀ b, kp (prims.adrsToKey (forsPkAdrs b)) = true) :
    IsQueryBoundP (itsrOpenP optRand pkSeedDist mainP) (fun t => isBadKeyI kp t = true) 0 := by
  have hu : ∀ n, ¬ isBadKeyI (prims := prims) kp (.inl n) = true := by intro n; simp [isBadKeyI]
  have hsec : ∀ d, ¬ isBadKeyI (prims := prims) kp (.inr (.inr (.inl d))) = true := by
    intro d; simp [isBadKeyI]
  refine itsrOpenP_bound optRand pkSeedDist mainP _ hu 0 0 (fun pkSeed => ?_)
    (fun pkSeed root => ?_)
  · exact npA_openKeygen _ pkSeed hsec (fun key x => by simp [isBadKeyI])
      (fun key l r => by simp [isBadKeyI]) (fun b xs _ => by simp [isBadKeyI, hkW])
  · refine qb_simulateQ_run_zero (p := fun _ => False) (fun t _ s => ?_)
      (isQueryBoundP_false _ _) []
    rcases t with n | q | m
    · exact unifStepI optRand _ hu pkSeed root n s
    · exact portStepI optRand _ pkSeed root q s 0 (query_np _ (by simp [isBadKeyI]))
    · exact signStepI optRand _ hu pkSeed root m s 0 0 (query_np _ (by simp [isBadKeyI]))
        fun R => npA_openSign _ pkSeed hsec (fun key x => by simp [isBadKeyI])
          (fun key l r => by simp [isBadKeyI]) (fun b xs _ => by simp [isBadKeyI, hkW])
          (fun b xs _ => by simp [isBadKeyI, hkR]) m root R 0
          (query_np _ (by simp [isBadKeyI]))

theorem itsrOpenP_bad (B : ℕ) (hB : ∀ xs : List prims.Y, OkLen vp xs → xs.length ≤ B)
    (hlong : ∀ pk, IsQueryBoundP (mainP pk)
      (fun i => isLongQ (S := GeneralScheme.SignatureCore vp prims.core) ℓ i = true) 0) :
    IsQueryBoundP (itsrOpenP optRand pkSeedDist mainP) (fun t => isBadIdx B ℓ t = true) 0 := by
  have hu : ∀ n, ¬ isBadIdx (ι := ItsrIn prims ⊕ (St × Blk)) (P := prims.PkSeed)
      (K := prims.AdrsKey) (Y := prims.Y) B ℓ (.inl n) = true := by intro n; simp [isBadIdx]
  have hsec : ∀ d, ¬ isBadIdx (ι := ItsrIn prims ⊕ (St × Blk)) (P := prims.PkSeed)
      (K := prims.AdrsKey) (Y := prims.Y) B ℓ (.inr (.inr (.inl d))) = true := by
    intro d; simp [isBadIdx]
  have hth : ∀ (pk : prims.PkSeed) (key : prims.AdrsKey) (xs : List prims.Y), OkLen vp xs →
      ¬ isBadIdx B ℓ (thIdx prims (ItsrIn prims ⊕ (St × Blk)) pk key xs) = true := by
    intro pk key xs h; have := hB xs h; simp [isBadIdx]; omega
  refine itsrOpenP_bound optRand pkSeedDist mainP _ hu 0 0 (fun pkSeed => ?_)
    (fun pkSeed root => ?_)
  · exact np_openKeygen _ pkSeed hsec fun key xs hx => hth _ _ _ hx
  · refine qb_simulateQ_run_zero (p := fun i => isLongQ (S := GeneralScheme.SignatureCore vp prims.core) ℓ i = true)
      (fun t ht s => ?_) (hlong _) []
    rcases t with n | q | m
    · exact unifStepI optRand _ hu pkSeed root n s
    · exact portStepI optRand _ pkSeed root q s 0 (query_np _ (by simp [isBadIdx]))
    · have hm : m.length ≤ ℓ := by
        simp only [isLongQ, decide_eq_true_eq, not_lt] at ht
        exact ht
      exact signStepI optRand _ hu pkSeed root m s 0 0 (query_np _ (by simp [isBadIdx]))
        fun R => np_openSign _ m pkSeed root R hsec (fun key xs hx => hth _ _ _ hx)
          (by simp [isBadIdx]; omega)

theorem itsrOpenP_longTgt
    (hlong : ∀ pk, IsQueryBoundP (mainP pk)
      (fun i => isLongQ (S := GeneralScheme.SignatureCore vp prims.core) ℓ i = true) 0) :
    IsQueryBoundP (itsrOpenP optRand pkSeedDist mainP) (fun t => isLongTgtI ℓ t = true) 0 := by
  have hu : ∀ n, ¬ isLongTgtI (prims := prims) ℓ (.inl n) = true := by
    intro n; simp [isLongTgtI]
  refine itsrOpenP_bound optRand pkSeedDist mainP _ hu 0 0 (fun pkSeed => ?_)
    (fun pkSeed root => ?_)
  · exact np_openKeygen _ pkSeed (fun d => by simp [isLongTgtI])
      fun key xs _ => by simp [isLongTgtI]
  · refine qb_simulateQ_run_zero (p := fun i => isLongQ (S := GeneralScheme.SignatureCore vp prims.core) ℓ i = true)
      (fun t ht s => ?_) (hlong _) []
    rcases t with n | q | m
    · exact unifStepI optRand _ hu pkSeed root n s
    · exact portStepI optRand _ pkSeed root q s 0 (query_np _ (by simp [isLongTgtI]))
    · have hm : m.length ≤ ℓ := by
        simp only [isLongQ, decide_eq_true_eq, not_lt] at ht
        exact ht
      exact signStepI optRand _ hu pkSeed root m s 0 0
        (query_np _ (by simp [isLongTgtI]; omega))
        fun R => np_openSign _ m pkSeed root R (fun d => by simp [isLongTgtI])
          (fun key xs _ => by simp [isLongTgtI]) (by simp [isLongTgtI])

theorem itsrOpenP_out (hout : ∀ pk, ∀ z ∈ support (mainP pk), z.1.length ≤ ℓ)
    (z : prims.Y × ItsrIn prims) (hz : z ∈ support (itsrOpenP optRand pkSeedDist mainP)) :
    z.2.2.2.length ≤ ℓ := by
  unfold itsrOpenP at hz
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
  obtain ⟨pkSeed, _, root, _, w, hw, rfl⟩ := hz
  have hw' : w.1 ∈ support ((simulateQ (portImplI optRand pkSeed root)
      (mainP ⟨pkSeed, root⟩)).run' []) := by
    rw [StateT.run'_eq, support_map]
    exact ⟨w, hw, rfl⟩
  exact hout _ _ (support_simulateQ_run'_subset _ _ _ hw')

end Count

end Ideal.Realize.Itsr

#print axioms Ideal.Realize.Itsr.itsrOpenP_port
#print axioms Ideal.Realize.Itsr.itsrOpenP_tgt
#print axioms Ideal.Realize.Itsr.itsrOpenP_hashes
#print axioms Ideal.Realize.Itsr.itsrOpenP_hmsg
#print axioms Ideal.Realize.Itsr.itsrOpenP_badKey
#print axioms Ideal.Realize.Itsr.itsrOpenP_bad
#print axioms Ideal.Realize.Itsr.itsrOpenP_longTgt
#print axioms Ideal.Realize.Itsr.itsrOpenP_out
