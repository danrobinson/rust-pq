import Ideal.Realize.ForsGuess
import Ideal.Realize.ForsCount
import Ideal.Realize.Phase1
import Reduction.Open.Phase1Fors

/-!
# Compression queries of the ideal-model FORS adversaries (FORS-leaf realisers, part 6)

* `chainImplP_bound`: the chain interpretation of a program over `OSpec P₀ (GP P₀)` with no long
  hash query issues at most `n₁ + n₂·thashCost B + n₃·hmsgCost ℓ` port queries, for `n₁` port,
  `n₂` hash and `n₃` `H_msg` queries of the program (`qb_simulateQ_classes`, `thashC_bound`,
  `hmsgC_bound`);
* `phase2C_bound`: hence the second phase `phase2C` makes at most `q2Fors qf qs ℓ` compression
  queries, `q2Fors qf qs ℓ = qf·1 + forsHashes qs·thashCost len + (qs + (1 + qs))·hmsgCost ℓ`
  (`forsHashes qs` is the count of `Reduction.Open.forsFindOpen_hashes`);
* `forsPhase1_chal`: the first phase makes at most `openPreTargets` challenge queries.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security TweakableHash

namespace Ideal.Realize.Fors

open Reduction Reduction.Open Reduction.Lazy Reduction.Resources2 Ideal.Realize

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option synthInstance.maxHeartbeats 400000

/-- A compression (port) query of `unifSpec + GP P₀`. -/
def isPortI : ℕ ⊕ (ℕ ⊕ (St × Blk)) → Bool
  | .inr (.inr _) => true
  | _ => false

theorem liftCS_bound {β : Type} (X : OracleComp CSpec β) (n : ℕ)
    (h : IsQueryBoundP X (fun i => i.isRight = true) n) :
    IsQueryBoundP (simulateQ liftCS X) (fun t => isPortI t = true) n := by
  refine IsQueryBoundP.simulateQ_of_step h (fun t ht => ?_) (fun t ht => ?_)
  · rcases t with n | q
    · exact (isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos
    · exact (isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos
  · rcases t with n | q
    · exact (isQueryBoundP_query_iff _ _ _).2 fun h' => by simp [isPortI] at h'
    · simp at ht

/-- **Port queries of the chain interpretation.** -/
theorem chainImplP_bound (tbl : SecIdx → P₀.Y) (B ℓ : ℕ) {β : Type}
    (P : OracleComp (OSpec P₀ (GP P₀)) β) {n₁ n₂ n₃ : ℕ}
    (h0 : IsQueryBoundP P (fun t => isBadIdx B ℓ t = true) 0)
    (h1 : IsQueryBoundP P (fun t => isPortIdx t = true) n₁)
    (h2 : IsQueryBoundP P (fun t => Lazy.kind t = .hash) n₂)
    (h3 : IsQueryBoundP P (fun t => isHmsgIdx t = true) n₃) :
    IsQueryBoundP (simulateQ (chainImplP tbl) P) (fun t => isPortI t = true)
      (n₁ * 1 + n₂ * thashCost B + n₃ * hmsgCost ℓ) := by
  refine qb_simulateQ_classes 1 (thashCost B) (hmsgCost ℓ) (fun t ht => ?_) h0 h1 h2 h3
  rcases t with n | (i | q) | d | (⟨pk, a, xs⟩ | ⟨R, pk, root, M⟩)
  · exact ((isQueryBoundP_query_iff _ _ _).2 fun h => by simp [isPortI] at h).mono (Nat.zero_le _)
  · exact ((isQueryBoundP_query_iff _ _ _).2 fun h => by simp [isPortI] at h).mono (Nat.zero_le _)
  · refine ((isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos).mono ?_
    simp only [isPortIdx, ↓reduceIte]
    exact le_trans (Nat.le_add_right 1 _) (Nat.le_add_right _ _)
  · exact (isQueryBoundP_pure _ _ _).mono (Nat.zero_le _)
  · have hxs : xs.length ≤ B := by simpa [isBadIdx] using ht
    refine (liftCS_bound _ _ (thashC_bound pk a xs)).mono (le_trans (thashCost_mono hxs) ?_)
    simp [isPortIdx, Lazy.kind, isHmsgIdx]
  · have hM : M.length ≤ ℓ := by simpa [isBadIdx] using ht
    refine (liftCS_bound _ _ (hmsgC_bound R pk root M)).mono ?_
    simp only [isPortIdx, Lazy.kind, isHmsgIdx]
    have := hmsgCost_mono hM
    simp
    omega

/-- **Compression queries of the opening layer**: one per port query. -/
theorem outerC_bound (tg : List (P₀.AdrsKey × P₀.Y)) {β : Type}
    (X : OracleComp (unifSpec + GP P₀) β) (n : ℕ)
    (h : IsQueryBoundP X (fun t => isPortI t = true) n) (s : List ℕ) :
    IsQueryBoundP ((simulateQ (outerC tg) X).run s) (fun i => i.isRight = true) n := by
  refine IsQueryBoundP.simulateQ_run_of_step h (fun t ht s => ?_) (fun t ht s => ?_) s
  · rcases t with n | i | q
    · simp [isPortI] at ht
    · simp [isPortI] at ht
    · show IsQueryBoundP ((liftM (cq q) : StateT (List ℕ) (OracleComp CSpec) St).run s) _ 1
      rw [StateT.run_monadLift]
      exact isQueryBoundP_bind (m := 0) (cq_bound q) fun x _ => isQueryBoundP_pure _ (x, s) _
  · rcases t with n | i | q
    · show IsQueryBoundP ((liftM (liftM (CSpec.query (.inl n)) : OracleComp CSpec _) :
        StateT (List ℕ) (OracleComp CSpec) _).run s) _ 0
      rw [StateT.run_monadLift]
      exact isQueryBoundP_bind_zero _ _ ((isQueryBoundP_query_iff _ _ _).2 fun h => by simp at h)
        fun x => isQueryBoundP_pure _ (x, s) _
    · exact isQueryBoundP_liftM_isRight _
    · simp [isPortI] at ht

/-- Hash queries of the FORS open program (`Reduction.Open.forsFindOpen_hashes`). -/
def forsHashes (qs : ℕ) : ℕ :=
  Lazy.keygenHashes Link.vp + qs * forsSignHashes Link.vp + (1 + qs + Link.vp.params.k)

/-- **Compression queries of the ideal-model second phase**: the forger's own `qf`, then
`thashCost len` per hash query and `hmsgCost ℓ` per `H_msg` query. -/
def q2Fors (qf qs ℓ : ℕ) : ℕ :=
  qf * 1 + forsHashes qs * thashCost Link.vp.params.len + (qs + (1 + qs)) * hmsgCost ℓ

theorem okLen_le (xs : List P₀.Y) (h : OkLen Link.vp xs) : xs.length ≤ Link.vp.params.len := by
  have hk : Link.vp.params.k ≤ Link.vp.params.len := by decide
  have h2 : 2 ≤ Link.vp.params.len := by decide
  rcases h with h | h | h | h <;> omega

/-- **The second phase makes at most `q2Fors qf qs ℓ` compression queries.** -/
theorem phase2C_bound {β : Type} (post : List (P₀.AdrsKey × P₀.Y) → (ℕ × P₀.Y) × List ℕ → β)
    (optRand : PublicKeyCore P₀.core → ProbComp P₀.Y) (mainP : PortForgerProg Link.vp P₀)
    (qf qs ℓ : ℕ)
    (hqf : ∀ pk, IsQueryBoundP (mainP pk)
      (fun i => isPortQ (S := GeneralScheme.SignatureCore Link.vp P₀.core) i = true) qf)
    (hqs : ∀ pk, IsQueryBoundP (mainP pk)
      (fun i => isSignQ (S := GeneralScheme.SignatureCore Link.vp P₀.core) i = true) qs)
    (hlong : ∀ pk, IsQueryBoundP (mainP pk)
      (fun i => isLongQ (S := GeneralScheme.SignatureCore Link.vp P₀.core) ℓ i = true) 0)
    (hout : ∀ pk, ∀ z ∈ support (mainP pk), z.1.length ≤ ℓ)
    (tbl : SecIdx → P₀.Y) (tg : List (P₀.AdrsKey × P₀.Y)) (ys : List P₀.Y) (pk : P₀.PkSeed) :
    IsQueryBoundP (phase2C post optRand mainP tbl tg ys pk) (fun i => i.isRight = true)
      (q2Fors qf qs ℓ) := by
  unfold phase2C
  refine (isQueryBoundP_bind (m := 0) (outerC_bound tg _ _ (chainImplP_bound tbl
    Link.vp.params.len ℓ _
    (forsFindOpenP_bad optRand mainP pk ys _ ℓ okLen_le hlong hout)
    (forsFindOpenP_port optRand mainP pk ys qf hqf)
    (forsFindOpenP_hashes optRand mainP pk ys qs hqs)
    (forsFindOpenP_hmsg optRand mainP pk ys qs hqs)) []) fun z _ =>
      isQueryBoundP_pure _ _ _).mono ?_
  unfold q2Fors forsHashes
  omega

/-! ## The first phase -/

section Phase1

variable {PkSeed Tweak M Y : Type}

/-- A challenge query of the selection-phase interface. -/
def isChal0 {κ : Type} : ℕ ⊕ ((Tweak × M) ⊕ κ) → Bool
  | .inr (.inl _) => true
  | _ => false

theorem initHF_chal (gen : ProbComp M) :
    ∀ l : List Tweak, IsQueryBoundP (initHF (PkSeed := PkSeed) (Y := Y) gen l)
      (fun t => isChal0 t = true) l.length
  | [] => isQueryBoundP_pure _ _ _
  | t :: ts => by
      unfold initHF
      refine (isQueryBoundP_bind (n := 0) (IsQueryBoundP.of_imp (fun t ht => by
          rcases t with n | t
          · simp [isChal0] at ht
          · rfl) (isQueryBoundP_liftM_isRight _)) fun x _ =>
        isQueryBoundP_bind (n := 1) ((isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos)
          fun y _ => isQueryBoundP_bind (m := 0) (initHF_chal gen ts) fun r _ =>
            isQueryBoundP_pure _ _ _).mono ?_
      simp only [List.length_cons]
      omega

end Phase1

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]

/-- **The first phase makes at most `openPreTargets` challenge queries.** -/
theorem forsPhase1_chal :
    IsQueryBoundP (forsPhase1 vp prims) (fun t => isChal0 t = true) (openPreTargets vp) := by
  have h0 : ∀ (Q : OracleComp (PickSpec prims.PkSeed prims.AdrsKey prims.Y)
      (SecretTable vp prims × List prims.AdrsKey)),
      IsQueryBoundP Q (fun t => t.isRight = true) 0 →
      IsQueryBoundP (simulateQ (liftPickHF : QueryImpl (PickSpec prims.PkSeed prims.AdrsKey prims.Y)
        (OracleComp (ForsP1Spec prims))) Q) (fun t => isChal0 t = true) 0 := by
    intro Q hQ
    refine qb_simulateQ_zero (fun t ht => ?_) hQ
    rcases t with n | q
    · exact (isQueryBoundP_query_iff _ _ _).2 fun h => by simp [isChal0] at h
    · simp at ht
  unfold forsPhase1
  refine (isQueryBoundP_bind (n := 0) (m := openPreTargets vp) (h0 _ ?_) fun w _ =>
    isQueryBoundP_bind (m := 0) ((initHF_chal _ _).mono (List.length_take_le _ _)) fun r _ =>
      isQueryBoundP_pure _ _ _).mono (by omega)
  exact isQueryBoundP_bind_zero _ _ (isQueryBoundP_liftM_isRight _) fun _ =>
    isQueryBoundP_pure _ _ _

/-- `forsPhase1_chal` for any program equal to the first phase (used with an irreducible
constant, so that the closed program is never exposed to the elaborator). -/
theorem chal_of_eq (X : OracleComp (ForsP1Spec prims) (ForsP1State vp prims))
    (hX : X = forsPhase1 vp prims) (p : (ForsP1Spec prims).Domain → Prop) [DecidablePred p]
    (hp : ∀ t, p t → isChal0 t = true) :
    IsQueryBoundP X p (openPreTargets vp) := by
  subst hX
  exact forsPhase1_chal.of_imp hp

end Ideal.Realize.Fors

#print axioms Ideal.Realize.Fors.chainImplP_bound
#print axioms Ideal.Realize.Fors.outerC_bound
#print axioms Ideal.Realize.Fors.phase2C_bound
#print axioms Ideal.Realize.Fors.forsPhase1_chal
