
import MIdeal.Wots128fBound
import MIdeal.Fors
import Ideal.Realize.ForsRealize
/-! The ported FORS opening experiment and its query bounds at SHA2-128f. -/
namespace MIdeal.Fors128f
open Ideal Ideal.Realize MLink SLHDSA SLHDSA.Security OracleComp OracleSpec Reduction Reduction.Open
open Ideal.Realize.Fors Reduction.Lazy Ideal.Transport ENNReal TweakableHash Reduction.Resources2
open TweakableHash.SM_DT_OpenPRE_SourceFinalValidity (findOracles openOracle)

set_option linter.unusedSectionVars false
section
variable {v : ValidatedParams} (base : Primitives v.params)
variable (hash : QueryImpl (publicHashSpec base.core) (OracleComp CSpec))
variable (ans : QueryImpl (publicHashSpec base.core) Id)
variable [SampleableType base.SkSeed] [SampleableType base.SkPrf] [SampleableType base.Y]
  [DecidableEq base.Y] [DecidableEq base.PkSeed] [DecidableEq base.AdrsKey] [Inhabited base.Y]
/-- A compression program read over `unifSpec + GP base`. -/
def liftCS : QueryImpl CSpec (OracleComp (unifSpec + GP base))
  | .inl n => (liftM ((unifSpec + GP base).query (.inl n)) : OracleComp (unifSpec + GP base) _)
  | .inr q => (liftM ((unifSpec + GP base).query (.inr (.inr q))) : OracleComp (unifSpec + GP base) _)

/-- Table interpretation with hash queries issued as compression chains. -/
def chainImplP (tbl : SecIdx → base.Y) :
    QueryImpl (OSpec base (GP base)) (OracleComp (unifSpec + GP base))
  | .inl n => (liftM ((unifSpec + GP base).query (.inl n)) : OracleComp (unifSpec + GP base) _)
  | .inr (.inl t) => (liftM ((unifSpec + GP base).query (.inr t)) : OracleComp (unifSpec + GP base) _)
  | .inr (.inr (.inl d)) => pure (tbl d)
  | .inr (.inr (.inr q)) => simulateQ (liftCS base) (hash q)

/-- The opening oracle inside the adversary; port queries become compression queries. -/
noncomputable def outerC (tg : List (base.AdrsKey × base.Y)) :
    QueryImpl (unifSpec + GP base) (StateT (List ℕ) (OracleComp CSpec))
  | .inl n => (liftM (liftM (CSpec.query (.inl n)) : OracleComp CSpec _) :
      StateT (List ℕ) (OracleComp CSpec) _)
  | .inr (.inl i) => StateT.mk fun s =>
      (liftM ((openOracle tg i).run s) : OracleComp CSpec ((forsG base).Range i × List ℕ))
  | .inr (.inr q) => (liftM (cq q) : StateT (List ℕ) (OracleComp CSpec) St)

/-- **The ideal-model second phase**, for a post-processing `post`. -/
noncomputable def phase2C {β : Type}
    (post : List (base.AdrsKey × base.Y) → (ℕ × base.Y) × List ℕ → β)
    (optRand : PublicKeyCore base.core → ProbComp base.Y) (mainP : PortForgerProg v base)
    (tbl : SecIdx → base.Y) (tg : List (base.AdrsKey × base.Y)) (ys : List base.Y) (pk : base.PkSeed) :
    OracleComp CSpec β :=
  (simulateQ (outerC base tg) (simulateQ (chainImplP base hash tbl) (forsFindOpenP optRand mainP pk ys))).run [] >>=
    fun z => pure (post tg z)

section Correct

variable (g : CF St Blk)

theorem portAns_liftC {β : Type} (X : OracleComp CSpec β) :
    simulateQ (portAns (prims := base) g) (simulateQ (liftCS base) X) =
      (liftM (simulateQ (instImpl₀ g) X) : OracleComp (unifSpec + forsG base) β) := by
  induction X using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, ih, liftM_bind]
    rcases t with n | q
    · simp [liftCS, portAns]
      rfl
    · simp [liftCS, portAns]

/-- **The chain interpretation is the table interpretation at `g`** (once the port is answered
by `g`). -/
theorem chainImplP_inst (he : ∀ t, simulateQ (instImpl₀ g) (hash t) = pure (f := ProbComp) (α := (publicHashSpec base.core).Range t) (ans t)) (tbl : SecIdx → base.Y) {β : Type} (P : OracleComp (OSpec base (GP base)) β) :
    simulateQ (portAns (prims := base) g) (simulateQ (chainImplP base hash tbl) P) =
      simulateQ (portAns (prims := base) g) (simulateQ (Lazy.tblImpl ans tbl) P) := by
  rw [← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose]
  congr 1
  funext t
  rcases t with n | t | d | q
  · rfl
  · rfl
  · rfl
  · simp only [QueryImpl.apply_compose, chainImplP, Lazy.tblImpl, portAns_liftC]
    rw [he]
    simp

theorem outerC_inst (tg : List (base.AdrsKey × base.Y)) {β : Type}
    (X : OracleComp (unifSpec + GP base) β) (s : List ℕ) :
    simulateQ (instImpl₀ g) ((simulateQ (outerC base tg) X).run s) =
      (simulateQ (findOracles tg) (simulateQ (portAns (prims := base) g) X)).run s := by
  rw [← QueryImpl.simulateQ_compose]
  refine simulateQ_StateT_compose _ _ _ (fun t s => ?_) X s
  rcases t with n | i | q
  · simp [outerC, portAns, findOracles]
  · simp [outerC, portAns, findOracles, instImpl₀_liftM]
  · simp [outerC, portAns, cq]

/-- **Correctness of the ideal-model second phase.** -/
theorem phase2C_inst (he : ∀ t, simulateQ (instImpl₀ g) (hash t) = pure (f := ProbComp) (α := (publicHashSpec base.core).Range t) (ans t)) {β : Type} (post : List (base.AdrsKey × base.Y) → (ℕ × base.Y) × List ℕ → β)
    (optRand : PublicKeyCore base.core → ProbComp base.Y) (mainP : PortForgerProg v base)
    (tbl : SecIdx → base.Y) (tg : List (base.AdrsKey × base.Y)) (ys : List base.Y) (pk : base.PkSeed) :
    simulateQ (instImpl₀ g) (phase2C base hash post optRand mainP tbl tg ys pk) =
      forsRun (prims := base) ans tbl tg
          (forsFindOpen optRand (fun pk => simulateQ (instImpl g) (mainP pk)) pk ys) >>=
        fun z => pure (post tg z) := by
  unfold phase2C forsRun
  rw [simulateQ_bind, outerC_inst, chainImplP_inst base hash ans g he, forsFindOpenP_fusion]
  simp

end Correct

variable (T : base.PkSeed → base.AdrsKey → List base.Y → base.Y)
  (H : base.Y → base.PkSeed → base.Y → List Byte → Bytes v.params.m)
  (r : base.PkSeed → base.Y → ProbComp base.Y) (seeds : ProbComp base.PkSeed)
  (codec : CoreWireCodec v.params base.core)
  (mb : List Byte → OracleComp (FSpecP (List Byte)) (List Byte × List Byte))
  (g : CF St Blk) (prf : base.PkSeed → base.SkSeed → Adrs → base.Y)
  (pm : base.SkPrf → base.Y → List Byte → base.Y)
  (tbl : SecretTable v base) (tg : List (base.AdrsKey × base.Y)) (ys : List base.Y) (pk : base.PkSeed)
  (he : ∀ t, simulateQ (instImpl₀ g) (hash t) =
    pure (f := ProbComp) (α := (publicHashSpec base.core).Range t) (PublicHash.impl (withTH base T H) t))
set_option quotPrecheck false in
local notation "B" => bytesToTyped (vp := v) (prims := setPrf (withTH base T H) prf pm)
    (codec := trCodec _ prf pm codec) (optRand := fun k => r k.pkSeed k.pkRoot)
    (pkSeedDist := seeds) ⟨fun pk => simulateQ (instImpl g) (mb pk)⟩

include he in
theorem tcr_run :
    (toTcr (Lazy.bOpenPreS B)).forge (tbl,tg,ys) pk =
      simulateQ (instImpl₀ g) (phase2C base hash (fun _ z => forsTcrPost z)
        (fun k => r k.pkSeed k.pkRoot) (typedP codec mb) tbl tg ys pk) := by
  let W := withTH base T H
  let rb := fun (k : PublicKeyCore base.core) => r k.pkSeed k.pkRoot
  let rs := fun (k : PublicKeyCore (setPrfC base.core prf pm)) => r k.pkSeed k.pkRoot
  let S := fun pk => simulateQ (instImpl g) (mb pk)
  let C := bytesToTyped (vp := v) (prims := W) (codec := codec) (optRand := rb)
    (pkSeedDist := seeds) ⟨S⟩
  refine (toTcr_forge_setPrf W prf pm codec rb rs (fun _ => rfl) seeds S (tbl,tg,ys) pk).trans ?_
  refine (forsTcr_phase2_open_eq C tbl tg ys pk).trans ?_
  refine Eq.trans ?_ (phase2C_inst base hash _ g he (fun _ z => forsTcrPost z) rb (typedP codec mb) tbl tg ys pk).symm
  have main : (fun k => simulateQ (instImpl g) (typedP (prims := base) codec mb k)) = C.main :=
    funext (typedP_inst (prims := base) codec rb seeds g mb)
  rw [main]
  exact congrArg (fun o => forsRun (prims := base) (PublicHash.impl W) tbl tg o >>= fun z => pure ((fun _ z => forsTcrPost z) tg z))
    (forsFindOpen_withTH (prims := base) (optRand := rb) T H C.main pk ys)

theorem tcr_choose :
    (toTcr (Lazy.bOpenPreS B)).choose = forsPhase1 v base := by
  let W := withTH base T H
  let rb := fun (k : PublicKeyCore base.core) => r k.pkSeed k.pkRoot
  let rs := fun (k : PublicKeyCore (setPrfC base.core prf pm)) => r k.pkSeed k.pkRoot
  rw [toTcr_choose_setPrf W prf pm codec rb rs seeds _, toTcr_choose_eq, forsPhase1_withTH]

include he in
theorem dspr_run :
    (toDspr (Lazy.bOpenPreS B)).guess (tbl,tg,ys) pk =
      simulateQ (instImpl₀ g) (phase2C base hash (fun tg z => forsDsprPost tg z)
        (fun k => r k.pkSeed k.pkRoot) (typedP codec mb) tbl tg ys pk) := by
  let W := withTH base T H
  let rb := fun (k : PublicKeyCore base.core) => r k.pkSeed k.pkRoot
  let rs := fun (k : PublicKeyCore (setPrfC base.core prf pm)) => r k.pkSeed k.pkRoot
  let S := fun pk => simulateQ (instImpl g) (mb pk)
  let C := bytesToTyped (vp := v) (prims := W) (codec := codec) (optRand := rb)
    (pkSeedDist := seeds) ⟨S⟩
  refine (toDspr_guess_setPrf W prf pm codec rb rs (fun _ => rfl) seeds S (tbl,tg,ys) pk).trans ?_
  refine (forsDspr_phase2_open_eq C tbl tg ys pk).trans ?_
  refine Eq.trans ?_ (phase2C_inst base hash _ g he (fun tg z => forsDsprPost tg z) rb (typedP codec mb) tbl tg ys pk).symm
  have main : (fun k => simulateQ (instImpl g) (typedP (prims := base) codec mb k)) = C.main :=
    funext (typedP_inst (prims := base) codec rb seeds g mb)
  rw [main]
  exact congrArg (fun o => forsRun (prims := base) (PublicHash.impl W) tbl tg o >>= fun z => pure ((fun tg z => forsDsprPost tg z) tg z))
    (forsFindOpen_withTH (prims := base) (optRand := rb) T H C.main pk ys)

theorem dspr_choose :
    (toDspr (Lazy.bOpenPreS B)).choose = forsPhase1 v base := by
  let W := withTH base T H
  let rb := fun (k : PublicKeyCore base.core) => r k.pkSeed k.pkRoot
  let rs := fun (k : PublicKeyCore (setPrfC base.core prf pm)) => r k.pkSeed k.pkRoot
  rw [toDspr_choose_setPrf W prf pm codec rb rs seeds _, toDspr_choose_eq, forsPhase1_withTH]
theorem liftCS_bound {β : Type} (X : OracleComp CSpec β) (n : ℕ)
    (h : IsQueryBoundP X (fun i => i.isRight = true) n) :
    IsQueryBoundP (simulateQ (liftCS base) X) (fun t => isPortI t = true) n := by
  refine IsQueryBoundP.simulateQ_of_step h (fun t ht => ?_) (fun t ht => ?_)
  · rcases t with n | q
    · exact (isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos
    · exact (isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos
  · rcases t with n | q
    · exact (isQueryBoundP_query_iff _ _ _).2 fun h' => by simp [isPortI] at h'
    · simp at ht

theorem outerC_bound (tg : List (base.AdrsKey × base.Y)) {β : Type}
    (X : OracleComp (unifSpec + GP base) β) (n : ℕ)
    (h : IsQueryBoundP X (fun t => isPortI t = true) n) (s : List ℕ) :
    IsQueryBoundP ((simulateQ (outerC base tg) X).run s) (fun i => i.isRight = true) n := by
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

end
open Class128f (vp P)
attribute [local irreducible] wotsChainTargets wotsStepTargets wotsStepTargetsT Lazy.structSecIdx Lazy.sparseTable wotsInsts
noncomputable local instance modelY (g : CompressionTables) : SampleableType (P g).Y := sampY128
local instance modelSk (g : CompressionTables) : SampleableType (P g).SkSeed := inferInstanceAs (SampleableType (Bytes 16))
local instance modelPrf (g : CompressionTables) : SampleableType (P g).SkPrf := inferInstanceAs (SampleableType (Bytes 16))
local instance modelInh (g : CompressionTables) : Inhabited (P g).Y := inferInstanceAs (Inhabited (Bytes 16))
local instance modelEqY (g : CompressionTables) : DecidableEq (P g).Y := inferInstanceAs (DecidableEq (Bytes 16))
local instance modelEqPk (g : CompressionTables) : DecidableEq (P g).PkSeed := inferInstanceAs (DecidableEq (Bytes 16))
local instance modelEqAd (g : CompressionTables) : DecidableEq (P g).AdrsKey := inferInstanceAs (DecidableEq (Bytes 22))
local instance modelFinite (g : CompressionTables) : Fintype (P g).Y := inferInstanceAs (Fintype (Bytes 16))

theorem chain_count (m : CompressionTables) (tbl : SecIdx → (P m).Y) (B ℓ : ℕ) {β : Type}
    (o : OracleComp (OSpec (P m) (GP (P m))) β) {n₁ n₂ n₃ : ℕ}
    (h0 : IsQueryBoundP o (fun t => isBadIdx B ℓ t = true) 0)
    (h1 : IsQueryBoundP o (fun t => isPortIdx t = true) n₁)
    (h2 : IsQueryBoundP o (fun t => Lazy.kind t = .hash) n₂)
    (h3 : IsQueryBoundP o (fun t => isHmsgIdx t = true) n₃) :
    IsQueryBoundP (simulateQ (chainImplP (P m) (Class128f.hashImpl m) tbl) o) (fun t => isPortI t = true)
      (n₁ * 1 + n₂ * thashCost B + n₃ * ((ℓ+56)/64+4)) := by
  refine qb_simulateQ_classes 1 (thashCost B) (((ℓ+56)/64+4)) (fun t ht => ?_) h0 h1 h2 h3
  rcases t with n | (i | q) | d | (⟨pk, a, xs⟩ | ⟨R, pk, root, M⟩)
  · exact ((isQueryBoundP_query_iff _ _ _).2 fun h => by simp [isPortI] at h).mono (Nat.zero_le _)
  · exact ((isQueryBoundP_query_iff _ _ _).2 fun h => by simp [isPortI] at h).mono (Nat.zero_le _)
  · refine ((isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos).mono ?_
    simp only [isPortIdx, ↓reduceIte]
    exact le_trans (Nat.le_add_right 1 _) (Nat.le_add_right _ _)
  · exact (isQueryBoundP_pure _ _ _).mono (Nat.zero_le _)
  · have hxs : xs.length ≤ B := by simpa [isBadIdx] using ht
    refine (liftCS_bound (P m) _ _ (thashC_bound pk a xs)).mono (le_trans (thashCost_mono hxs) ?_)
    simp [isPortIdx, Lazy.kind, isHmsgIdx]
  · have hM : M.length ≤ ℓ := by simpa [isBadIdx] using ht
    refine (liftCS_bound (P m) _ _ (Class128f.hmsg_count R pk root M)).mono ?_
    simp only [isPortIdx, Lazy.kind, isHmsgIdx]
    simp
    omega

def hashCount (qs : ℕ) : ℕ :=
  Lazy.keygenHashes vp + qs * forsSignHashes vp + (1 + qs + vp.params.k)

/-- **Compression queries of the ideal-model second phase**: the forger's own `qf`, then
`thashCost len` per hash query and `((ℓ+56)/64+4)` per `H_msg` query. -/
def phaseBudget (qf qs ℓ : ℕ) : ℕ :=
  qf * 1 + hashCount qs * thashCost vp.params.len + (qs + (1 + qs)) * ((ℓ+56)/64+4)

theorem len_bound (m : CompressionTables) (xs : List (P m).Y) (h : OkLen vp xs) : xs.length ≤ vp.params.len := by
  have hk : vp.params.k ≤ vp.params.len := by decide
  have h2 : 2 ≤ vp.params.len := by decide
  rcases h with h | h | h | h <;> omega

/-- **The second phase makes at most `phaseBudget qf qs ℓ` compression queries.** -/
theorem phase_count (m : CompressionTables) {β : Type} (post : List ((P m).AdrsKey × (P m).Y) → (ℕ × (P m).Y) × List ℕ → β)
    (optRand : PublicKeyCore (P m).core → ProbComp (P m).Y) (mainP : PortForgerProg vp (P m))
    (qf qs ℓ : ℕ)
    (hqf : ∀ pk, IsQueryBoundP (mainP pk)
      (fun i => isPortQ (S := GeneralScheme.SignatureCore vp (P m).core) i = true) qf)
    (hqs : ∀ pk, IsQueryBoundP (mainP pk)
      (fun i => isSignQ (S := GeneralScheme.SignatureCore vp (P m).core) i = true) qs)
    (hlong : ∀ pk, IsQueryBoundP (mainP pk)
      (fun i => isLongQ (S := GeneralScheme.SignatureCore vp (P m).core) ℓ i = true) 0)
    (hout : ∀ pk, ∀ z ∈ support (mainP pk), z.1.length ≤ ℓ)
    (tbl : SecIdx → (P m).Y) (tg : List ((P m).AdrsKey × (P m).Y)) (ys : List (P m).Y) (pk : (P m).PkSeed) :
    IsQueryBoundP (phase2C (P m) (Class128f.hashImpl m) post optRand mainP tbl tg ys pk) (fun i => i.isRight = true)
      (phaseBudget qf qs ℓ) := by
  unfold phase2C
  refine (isQueryBoundP_bind (m := 0) (outerC_bound (P m) tg _ _ (chain_count m tbl
    vp.params.len ℓ _
    (forsFindOpenP_bad optRand mainP pk ys _ ℓ (len_bound m) hlong hout)
    (forsFindOpenP_port optRand mainP pk ys qf hqf)
    (forsFindOpenP_hashes optRand mainP pk ys qs hqs)
    (forsFindOpenP_hmsg optRand mainP pk ys qs hqs)) []) fun z _ =>
      isQueryBoundP_pure _ _ _).mono ?_
  unfold phaseBudget hashCount
  omega

end MIdeal.Fors128f
#print axioms MIdeal.Fors128f.phase_count

#print axioms MIdeal.Fors128f.dspr_run
#print axioms MIdeal.Fors128f.tcr_run
