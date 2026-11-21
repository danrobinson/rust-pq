import Reduction.Lazy.MsgLazy
import Reduction.SufHopMsg

/-!
# The lazy `PRF_msg` distinguisher of the SUF-CMA proof

`bPrfMsgW w A` (`Reduction.SufHopMsg`) samples the eager `2 ^ 256`-cell table `sampleTable`.
`bPrfMsgWL w A` is the same distinguisher with the secret values drawn lazily (association-list
cache), exactly as `Reduction.Lazy.bPrfMsgL` is for `bPrfMsg`: the only differences are the
harness (`runForgerSig`, which records the returned `(message, signature)` pairs) and the output
bit (`w` instead of the EUF-CMA check).  Same advantage (`prfAdvantage_bPrfMsgWL`), same
resource lemmas.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal

namespace Reduction
namespace Lazy

set_option linter.unusedSectionVars false

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]
variable {optRand : PublicKeyCore prims.core → ProbComp prims.Y}
  {pkSeedDist : ProbComp prims.PkSeed}

/-- The open program of the `PRF_msg` distinguisher with final check `w`. -/
def msgOpenW (w : WinCheck vp prims) (A : Forger vp prims optRand pkSeedDist) :
    OracleComp (OSpec prims (msgG prims)) Bool := do
  let pkSeed ← (liftM pkSeedDist : OracleComp (OSpec prims (msgG prims)) prims.PkSeed)
  let root ← openKeygen prims (msgG prims) pkSeed
  let z ← runForgerSig A ⟨pkSeed, root⟩ (msgSignO optRand ⟨pkSeed, root⟩)
  return w ⟨pkSeed, root⟩ z.1 z.2

/-- **The lazy `PRF_msg` distinguisher of the SUF-CMA proof**: `msgOpenW w A` with the secret oracle answered from an
association-list cache, a fresh uniform value being drawn on each miss. -/
noncomputable def bPrfMsgWL (w : WinCheck vp prims) (A : Forger vp prims optRand pkSeedDist) : MsgPrfAdv prims :=
  lazyRun (PublicHash.impl prims) (msgOpenW w A)

/-- What `bPrfMsgW w A` does after sampling the seed and the table. -/
noncomputable def msgBodyW (w : WinCheck vp prims) (A : Forger vp prims optRand pkSeedDist) (tbl : SecretTable vp prims)
    (pkSeed : prims.PkSeed) :
    OracleComp (PRFScheme.PRFOracleSpec (prims.Y × List Byte) prims.Y) Bool := do
  let z ← runForgerSig A (idealPk vp prims tbl pkSeed) fun m => do
    let addrnd ← (monadLift (optRand (idealPk vp prims tbl pkSeed)) :
      OracleComp (PRFScheme.PRFOracleSpec (prims.Y × List Byte) prims.Y) prims.Y)
    let R ← (PRFScheme.functionQuery (addrnd, m) :
      OracleComp (PRFScheme.PRFOracleSpec (prims.Y × List Byte) prims.Y) prims.Y)
    return idealSign vp prims tbl m (idealPk vp prims tbl pkSeed) R
  return w (idealPk vp prims tbl pkSeed) z.1 z.2

theorem bPrfMsgW_eq (w : WinCheck vp prims) (A : Forger vp prims optRand pkSeedDist) :
    bPrfMsgW w A = (liftM pkSeedDist :
      OracleComp (PRFScheme.PRFOracleSpec (prims.Y × List Byte) prims.Y) prims.PkSeed) >>=
        fun pkSeed => (liftM (sampleTable vp prims) :
          OracleComp (PRFScheme.PRFOracleSpec (prims.Y × List Byte) prims.Y) _) >>=
        fun tbl => msgBodyW w A tbl pkSeed := rfl

/-- Interpreting the secret oracle of the open harness run by a table. -/
theorem runForgerSig_tbl (A : Forger vp prims optRand pkSeedDist) (g : SecretTable vp prims)
    (pk : PublicKeyCore prims.core)
    (signO : List Byte → OracleComp (OSpec prims (msgG prims))
      (GeneralScheme.SignatureCore vp prims.core))
    (signC : List Byte → OracleComp (unifSpec + msgG prims)
      (GeneralScheme.SignatureCore vp prims.core))
    (hsign : ∀ m, simulateQ (tblImpl (PublicHash.impl prims) g) (signO m) = signC m) :
    simulateQ (tblImpl (PublicHash.impl prims) g) (runForgerSig A pk signO) =
      runForgerSig A pk signC := by
  unfold runForgerSig
  rw [QueryImpl.simulateQ_mapStateTBase_run]
  congr 2
  funext t
  cases t with
  | inl n =>
    refine StateT.ext fun s => ?_
    simp [QueryImpl.mapStateTBase]
    exact simulateQ_tblImpl_liftM (PublicHash.impl prims) g (liftM (unifSpec.query n))
  | inr m =>
    refine StateT.ext fun s => ?_
    simp [QueryImpl.mapStateTBase, sigSignOracle, appendLog, hsign]

theorem msgOpenW_tbl (w : WinCheck vp prims) (A : Forger vp prims optRand pkSeedDist) (g : SecretTable vp prims) :
    simulateQ (tblImpl (PublicHash.impl prims) g) (msgOpenW w A) =
      (liftM pkSeedDist :
        OracleComp (PRFScheme.PRFOracleSpec (prims.Y × List Byte) prims.Y) prims.PkSeed) >>=
        fun pkSeed => msgBodyW w A g pkSeed := by
  unfold msgOpenW
  simp only [simulateQ_bind, simulateQ_pure]
  rw [simulateQ_tblImpl_liftM]
  refine bind_congr fun pkSeed => ?_
  rw [openKeygen_tbl, pure_bind]
  rw [runForgerSig_tbl A g ⟨pkSeed, idealRoot vp prims g pkSeed⟩ _ _ (fun m => ?_)]
  · rfl
  · unfold msgSignO
    simp only [simulateQ_bind]
    rw [simulateQ_tblImpl_liftM]
    refine bind_congr fun addrnd => ?_
    rw [simulateQ_tblImpl_gameQ]
    refine bind_congr fun R => ?_
    exact openSign_tbl g m ⟨pkSeed, idealRoot vp prims g pkSeed⟩ R

/-! ## Same advantage -/

/-- Real world: the lazy and the eager distinguisher have the same output law. -/
theorem evalDist_prfReal_bPrfMsgWL (w : WinCheck vp prims) (A : Forger vp prims optRand pkSeedDist) :
    𝒟[(msgPrf vp prims).prfRealExperiment (bPrfMsgWL w A)] =
      𝒟[(msgPrf vp prims).prfRealExperiment (bPrfMsgW w A)] := by
  unfold PRFScheme.prfRealExperiment
  refine evalDist_bind_congr_of_support _ _ _ fun k _ => ?_
  have hlift : ∀ {β : Type} (ob : ProbComp β),
      simulateQ ((msgPrf vp prims).prfRealQueryImpl k)
        (liftM ob :
          OracleComp (PRFScheme.PRFOracleSpec (prims.Y × List Byte) prims.Y) β) = ob :=
    fun ob => PRFScheme.simulateQ_prfRealQueryImpl_liftComp _ k ob
  unfold bPrfMsgWL
  rw [evalDist_lazyRun_eq_table' (PublicHash.impl prims) ((msgPrf vp prims).prfRealQueryImpl k)
    (hlift _) (msgOpenW w A)]
  simp only [msgOpenW_tbl, bPrfMsgW_eq, simulateQ_bind, hlift]
  exact OracleComp.evalDist_bind_bind_swap _ _ _

/-- Ideal world: the lazy and the eager distinguisher have the same output law. -/
theorem evalDist_prfIdeal_bPrfMsgWL (w : WinCheck vp prims) (A : Forger vp prims optRand pkSeedDist) :
    𝒟[PRFScheme.prfIdealExperiment (bPrfMsgWL w A)] =
      𝒟[PRFScheme.prfIdealExperiment (bPrfMsgW w A)] := by
  unfold PRFScheme.prfIdealExperiment
  have hl : ∀ {β : Type} (ob : ProbComp β)
      (c : ((prims.Y × List Byte) →ₒ prims.Y).QueryCache),
      (simulateQ (PRFScheme.prfIdealQueryImpl (D := prims.Y × List Byte) (R := prims.Y))
        (liftM ob :
          OracleComp (PRFScheme.PRFOracleSpec (prims.Y × List Byte) prims.Y) β)).run c =
        (·, c) <$> ob :=
    fun ob c => OracleSpec.simulateQ_romImpl_liftM_run ob c
  unfold bPrfMsgWL
  rw [evalDist_lazyRun_eq_table_run' (PublicHash.impl prims)
    (PRFScheme.prfIdealQueryImpl (D := prims.Y × List Byte) (R := prims.Y))
    (fun s => hl _ s) (msgOpenW w A)]
  simp only [msgOpenW_tbl, bPrfMsgW_eq, simulateQ_bind, StateT.run'_eq, StateT.run_bind, hl,
    bind_map_left, map_bind]
  exact OracleComp.evalDist_bind_bind_swap _ _ _

/-- **Same advantage.** -/
theorem prfAdvantage_bPrfMsgWL (w : WinCheck vp prims) (A : Forger vp prims optRand pkSeedDist) :
    (msgPrf vp prims).prfAdvantage (bPrfMsgWL w A) = (msgPrf vp prims).prfAdvantage (bPrfMsgW w A) := by
  unfold PRFScheme.prfAdvantage
  rw [evalDist_prfReal_bPrfMsgWL, evalDist_prfIdeal_bPrfMsgWL]

/-! ## Resources -/

/-- Queries of kind `K` (game / secret / hash) of the open program, for a forger with at most
`qs` signing queries. -/
theorem msgOpenW_kindBound (w : WinCheck vp prims) (A : Forger vp prims optRand pkSeedDist) (K : Kind) (hK : K ≠ .unif)
    (qs : ℕ) (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs) :
    IsQueryBoundP (msgOpenW w A) (fun t => kind t = K)
      (keygenB vp (ind K .sec) (ind K .hash) +
        qs * (ind K .game + signB vp (ind K .sec) (ind K .hash))) := by
  have hrun : ∀ pk : PublicKeyCore prims.core,
      IsQueryBoundP (runForgerSig A pk (msgSignO optRand pk)) (fun t => kind t = K)
        (qs * (ind K .game + signB vp (ind K .sec) (ind K .hash))) := by
    intro pk
    unfold runForgerSig
    refine IsQueryBoundP.simulateQ_run_of_step_le (hA _) (fun t ht s => ?_) (fun t ht s => ?_) []
    · cases t with
      | inl n => simp at ht
      | inr m =>
        have hstep := qb_bind (fun t => kind t = K)
          (liftM_kindBound (gspec := msgG prims) (D := SecIdx) (V := prims.Y)
            (hspec := publicHashSpec prims.core) K hK (optRand pk)) fun addrnd =>
          qb_bind (fun t => kind t = K) (gameQ_kindBound (prims := prims) (gspec := msgG prims) K
            (addrnd, m)) fun R =>
            qb_bind (fun t => kind t = K) (m := 0)
              (openSign_kindBound (gspec := msgG prims) K m pk.pkSeed pk.pkRoot R)
              fun sig => isQueryBoundP_pure _ (sig, s ++ [⟨m, sig⟩]) _
        simpa [sigSignOracle, appendLog, msgSignO] using hstep
    · cases t with
      | inl n =>
        simp only [QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply, StateT.run_monadLift]
        have h0 := qb_bind (fun t => kind t = K) (m := 0)
          (liftM_kindBound (gspec := msgG prims) (D := SecIdx) (V := prims.Y)
            (hspec := publicHashSpec prims.core) K hK
            (liftM (unifSpec.query n) : ProbComp _)) fun x => isQueryBoundP_pure _ (x, s) _
        exact h0
      | inr m => simp at ht
  unfold msgOpenW
  exact (qb_bind _ (liftM_kindBound K hK pkSeedDist) fun pkSeed =>
    qb_bind _ (openKeygen_kindBound K pkSeed) fun root =>
      qb_bind _ (m := 0) (hrun _) fun z => isQueryBoundP_pure _ _ _).mono (by omega)

/-- `bPrfMsgWL w A` is the interpretation of the resource-explicit program `lazyRes (msgOpenW w A)`
(fresh draw ↦ `$ᵗ prims.Y`, hash query ↦ evaluation). -/
theorem bPrfMsgWL_eq (w : WinCheck vp prims) (A : Forger vp prims optRand pkSeedDist) :
    bPrfMsgWL w A = simulateQ (interp (PublicHash.impl prims)) (lazyRes (msgOpenW w A)) := rfl

/-- (i) One `PRF_msg` query per signing query. -/
theorem bPrfMsgWL_queryBound (w : WinCheck vp prims) (A : Forger vp prims optRand pkSeedDist) (qs : ℕ)
    (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs) :
    IsQueryBoundP (bPrfMsgWL w A) (fun i => i.isRight = true) qs :=
  lazyRun_gameBound _ _ qs ((msgOpenW_kindBound w A .game (by decide) qs hA).mono
    (by simp [ind, keygenB_game, signB_game]))

/-- (ii) Fresh uniform draws (= cache entries): at most `2^h'·len + qs·signReads`. -/
theorem bPrfMsgWL_draws (w : WinCheck vp prims) (A : Forger vp prims optRand pkSeedDist) (qs : ℕ)
    (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs) :
    IsQueryBoundP (lazyRes (msgOpenW w A)) (fun t => kind t = .sec)
      (2 ^ vp.params.hp * vp.params.len + qs * signReads vp) :=
  lazyRes_bound_draws _ _ ((msgOpenW_kindBound w A .sec (by decide) qs hA).mono
    (Nat.add_le_add keygenB_sec (Nat.mul_le_mul_left _ (by
      simpa [ind] using signB_sec (vp := vp)))))

/-- (iii) Hash evaluations: at most `keygenHashes + qs·signHashes`. -/
theorem bPrfMsgWL_hashes (w : WinCheck vp prims) (A : Forger vp prims optRand pkSeedDist) (qs : ℕ)
    (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs) :
    IsQueryBoundP (lazyRes (msgOpenW w A)) (fun t => kind t = .hash)
      (keygenHashes vp + qs * signHashes vp) :=
  lazyRes_bound_hash _ _ ((msgOpenW_kindBound w A .hash (by decide) qs hA).mono
    (Nat.add_le_add keygenB_hash (Nat.mul_le_mul_left _ (by
      simpa [ind] using signB_hash (vp := vp)))))

/-- Game queries of the resource-explicit program. -/
theorem bPrfMsgWL_gameRes (w : WinCheck vp prims) (A : Forger vp prims optRand pkSeedDist) (qs : ℕ)
    (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs) :
    IsQueryBoundP (lazyRes (msgOpenW w A)) (fun t => kind t = .game) qs :=
  lazyRes_bound_game _ _ ((msgOpenW_kindBound w A .game (by decide) qs hA).mono
    (by simp [ind, keygenB_game, signB_game]))

end Lazy
end Reduction

#print axioms Reduction.Lazy.prfAdvantage_bPrfMsgWL
#print axioms Reduction.Lazy.bPrfMsgWL_queryBound
#print axioms Reduction.Lazy.bPrfMsgWL_draws
#print axioms Reduction.Lazy.bPrfMsgWL_hashes
