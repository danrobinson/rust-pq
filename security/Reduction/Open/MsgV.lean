/-
Work package OPEN, item R2: the `PRF_msg` distinguishers with the FINAL CHECK as oracle queries.

`Lazy.msgOpen A` / `Lazy.msgOpenW w A` end with `harnessValid` / `w`, which run `verifyInternal`
directly on `prims`.  Here:

* `embR Q` — a program `Q` over the hash oracle alone, read as an open program (every query of
  `Q` is ONE hash-kind query); `simulateQ_lazyImpl_emb`, `simulateQ_tblImpl_emb`, `emb_kindBound`.
* `msgOpenV A`, `msgOpenWV wO A` — as `msgOpen A`, `msgOpenW w A`, with the final check
  `embR (verification program)`; `wO : WinCheckO` is a final check given as a program over the hash
  oracle, `wO.eval` the `WinCheck` it computes; `sufCheckO.eval = sufCheck`, `eufCheckO`.
* `lazyRun_msgOpenV`, `lazyRun_msgOpenWV`, `lazyRun_msgOpenWV_sufCheck` — equality of programs
  with `Lazy.bPrfMsgL A`, `Lazy.bPrfMsgWL w A`.
* `msgOpenV_kindBound`, … — counts; hash kind `keygenHashes + qs·signHashes + (1 + verifyHashes)`
  (the `1` is the `H_msg` evaluation of verification, which `verifyHashes` does not include).
* `msgOpenV_castForger`, `msgOpenWV_castForger`, `itsrOpen_castForger` — the open programs do not
  depend on the `Thash`/`Hmsg` components of `prims` at all (`rfl`).
-/
import Reduction.Lazy.SufMsgLazy
import Reduction.Lazy.ItsrLazy
import Reduction.TcrMemo
import Reduction.Instance128sV2
import Reduction.Open.WithHash

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal

namespace Reduction
namespace Open

open Lazy

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! ## Programs over the hash oracle as open programs -/

section Generic

variable {ι κ : Type} {gspec : OracleSpec ι} {hspec : OracleSpec κ} {D V α : Type}

/-- A hash query, forwarded as the hash-kind query of the open interface. -/
def hashEmbR : QueryImpl hspec (OracleComp (RSpec gspec D V hspec)) :=
  fun q => (liftM ((RSpec gspec D V hspec).query (.inr (.inr (.inr q)))) :
    OracleComp (RSpec gspec D V hspec) _)

/-- A program over the hash oracle alone, as an open program: each of its queries is one
hash-kind query; nothing is evaluated. -/
def embR (Q : OracleComp hspec α) : OracleComp (RSpec gspec D V hspec) α :=
  simulateQ hashEmbR Q

/-- Under any handler that answers hash queries by `hI`, `embR Q` is the evaluation of `Q`. -/
theorem simulateQ_emb {m : Type → Type} [Monad m] [LawfulMonad m]
    (I : QueryImpl (RSpec gspec D V hspec) m) (hI : QueryImpl hspec Id)
    (h : ∀ q, I (.inr (.inr (.inr q))) = pure (hI q)) (Q : OracleComp hspec α) :
    simulateQ I (embR (gspec := gspec) (D := D) (V := V) Q) = pure (simulateQ hI Q) := by
  induction Q using OracleComp.inductionOn with
  | pure a => simp [embR]; rfl
  | query_bind t k ih =>
    have h1 : simulateQ I (embR (gspec := gspec) (D := D) (V := V) (liftM (hspec.query t) >>= k)) =
        I (.inr (.inr (.inr t))) >>= fun x => simulateQ I (embR (k x)) := by
      simp [embR, hashEmbR]
    rw [h1, h, pure_bind, ih]
    rfl

theorem simulateQ_lazyImpl_emb [DecidableEq D] [SampleableType V] (hI : QueryImpl hspec Id)
    (Q : OracleComp hspec α) :
    simulateQ (lazyImpl (gspec := gspec) (D := D) (V := V) hI) (embR Q) =
      pure (simulateQ hI Q) :=
  simulateQ_emb _ hI (fun _ => rfl) Q

theorem simulateQ_tblImpl_emb (hI : QueryImpl hspec Id) (g : D → V) (Q : OracleComp hspec α) :
    simulateQ (tblImpl (gspec := gspec) hI g) (embR Q) = pure (simulateQ hI Q) :=
  simulateQ_emb _ hI (fun _ => rfl) Q

/-- `embR Q` makes as many hash-kind queries as `Q` makes queries, and no other query. -/
theorem emb_kindBound (K : Kind) (Q : OracleComp hspec α) (n : ℕ)
    (hQ : IsTotalQueryBound Q n) :
    IsQueryBoundP (embR (gspec := gspec) (D := D) (V := V) Q) (fun t => kind t = K)
      (n * ind K .hash) := by
  by_cases hK : K = .hash
  · subst hK
    have h := IsQueryBoundP.simulateQ_of_step (impl := hashEmbR (gspec := gspec) (D := D) (V := V))
      (q := fun t => kind t = Kind.hash) (hQ.isQueryBoundP (p := fun _ => True))
      (fun t _ => (isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos)
      (fun t ht => absurd trivial ht)
    simpa [ind, embR] using h
  · have h := isQueryBoundP_simulateQ_zero (impl := hashEmbR (gspec := gspec) (D := D) (V := V))
      (q := fun t => kind t = K) Q
      (fun t => (isQueryBoundP_query_iff _ _ _).2 fun h => (hK (Eq.symm h)).elim)
    simpa [ind, hK, embR] using h

end Generic

/-! ## The open distinguishers with open final check -/

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]
variable {optRand : PublicKeyCore prims.core → ProbComp prims.Y}
  {pkSeedDist : ProbComp prims.PkSeed}

/-- A final check given as a PROGRAM over the public hash oracle (no evaluation by `prims`). -/
abbrev WinCheckO (vp : ValidatedParams) (prims : Primitives vp.params) : Type :=
  PublicKeyCore prims.core → List Byte × GeneralScheme.SignatureCore vp prims.core →
    SigLog vp prims → OracleComp (publicHashSpec prims.core) Bool

/-- The `WinCheck` computed by an open final check: its hash queries evaluated by `prims`. -/
def WinCheckO.eval (wO : WinCheckO vp prims) : WinCheck vp prims :=
  fun pk f log => simulateQ (PublicHash.impl prims) (wO pk f log)

/-- The EUF-CMA final check (`harnessValid`) as a program over the hash oracle: the freshness
test, and `verifyInternalM` (FIPS 205 Algorithm 20 with `H_msg`/`F`/`H`/`T_l` as queries). -/
def eufCheckO (pk : PublicKeyCore prims.core) (msgs : List (List Byte)) (msg : List Byte)
    (sig : GeneralScheme.SignatureCore vp prims.core) :
    OracleComp (publicHashSpec prims.core) Bool :=
  (fun b => decide (msg ∉ msgs) && b) <$>
    (GeneralScheme.verifyInternalM vp prims.core msg sig pk :
      OracleComp (publicHashSpec prims.core) Bool)

theorem eufCheckO_eval (pk : PublicKeyCore prims.core) (msgs : List (List Byte)) (msg : List Byte)
    (sig : GeneralScheme.SignatureCore vp prims.core) :
    simulateQ (PublicHash.impl prims) (eufCheckO pk msgs msg sig) =
      harnessValid pk msgs msg sig := by
  unfold eufCheckO harnessValid GeneralScheme.verifyInternal
  rw [simulateQ_map]
  rfl

/-- The SUF-CMA final check `sufCheck` as a program over the hash oracle. -/
def sufCheckO : WinCheckO vp prims := fun pk f log =>
  letI := sigDecEq (vp := vp) (prims := prims)
  (fun b => !SignatureAlg.signingLogContains log f.1 f.2 && b) <$>
    (GeneralScheme.verifyInternalM vp prims.core f.1 f.2 pk :
      OracleComp (publicHashSpec prims.core) Bool)

theorem sufCheckO_eval : (sufCheckO (vp := vp) (prims := prims)).eval = sufCheck := by
  funext pk f log
  unfold WinCheckO.eval sufCheckO sufCheck GeneralScheme.verifyInternal
  rw [simulateQ_map]
  rfl

/-- The common first part of `msgOpen A` and `msgOpenV A`: seed, open key generation, the
forger's run with open signing. -/
def msgPre (A : Forger vp prims optRand pkSeedDist) :
    OracleComp (OSpec prims (msgG prims))
      (PublicKeyCore prims.core ×
        ((List Byte × GeneralScheme.SignatureCore vp prims.core) × List (List Byte))) := do
  let pkSeed ← (liftM pkSeedDist : OracleComp (OSpec prims (msgG prims)) prims.PkSeed)
  let root ← openKeygen prims (msgG prims) pkSeed
  let z ← runForger A ⟨pkSeed, root⟩ (msgSignO optRand ⟨pkSeed, root⟩)
  return (⟨pkSeed, root⟩, z)

/-- The same for the SUF-CMA harness. -/
def msgPreW (A : Forger vp prims optRand pkSeedDist) :
    OracleComp (OSpec prims (msgG prims))
      (PublicKeyCore prims.core ×
        ((List Byte × GeneralScheme.SignatureCore vp prims.core) × SigLog vp prims)) := do
  let pkSeed ← (liftM pkSeedDist : OracleComp (OSpec prims (msgG prims)) prims.PkSeed)
  let root ← openKeygen prims (msgG prims) pkSeed
  let z ← runForgerSig A ⟨pkSeed, root⟩ (msgSignO optRand ⟨pkSeed, root⟩)
  return (⟨pkSeed, root⟩, z)

/-- **The open `PRF_msg` distinguisher with open final check**: as `Lazy.msgOpen A`, the final
verification being hash-kind queries. -/
def msgOpenV (A : Forger vp prims optRand pkSeedDist) :
    OracleComp (OSpec prims (msgG prims)) Bool :=
  msgPre A >>= fun x => embR (eufCheckO x.1 x.2.2 x.2.1.1 x.2.1.2)

/-- **The open `PRF_msg` distinguisher of the SUF-CMA proof with open final check `wO`.** -/
def msgOpenWV (wO : WinCheckO vp prims) (A : Forger vp prims optRand pkSeedDist) :
    OracleComp (OSpec prims (msgG prims)) Bool :=
  msgPreW A >>= fun x => embR (wO x.1 x.2.1 x.2.2)

theorem msgOpen_eq_pre (A : Forger vp prims optRand pkSeedDist) :
    msgOpen A = msgPre A >>= fun x => pure (harnessValid x.1 x.2.2 x.2.1.1 x.2.1.2) := by
  simp [msgOpen, msgPre]

theorem msgOpenW_eq_pre (w : WinCheck vp prims) (A : Forger vp prims optRand pkSeedDist) :
    msgOpenW w A = msgPreW A >>= fun x => pure (w x.1 x.2.1 x.2.2) := by
  simp [msgOpenW, msgPreW]

/-! ## Equations -/

/-- **`msgOpenV A` under the lazy handler is the program `bPrfMsgL A`** (equality of programs). -/
theorem lazyRun_msgOpenV (A : Forger vp prims optRand pkSeedDist) :
    lazyRun (PublicHash.impl prims) (msgOpenV A) = bPrfMsgL A := by
  unfold bPrfMsgL
  rw [lazyRun_eq, lazyRun_eq, msgOpen_eq_pre]
  unfold msgOpenV
  simp only [simulateQ_bind, simulateQ_pure, simulateQ_lazyImpl_emb, eufCheckO_eval]

/-- **`msgOpenWV wO A` under the lazy handler is the program `bPrfMsgWL wO.eval A`.** -/
theorem lazyRun_msgOpenWV (wO : WinCheckO vp prims) (A : Forger vp prims optRand pkSeedDist) :
    lazyRun (PublicHash.impl prims) (msgOpenWV wO A) = bPrfMsgWL wO.eval A := by
  unfold bPrfMsgWL
  rw [lazyRun_eq, lazyRun_eq, msgOpenW_eq_pre]
  unfold msgOpenWV
  simp only [simulateQ_bind, simulateQ_pure, simulateQ_lazyImpl_emb]
  rfl

/-- The same for a `WinCheck` `w` with an open form `wO` (equation hypothesis `hw`). -/
theorem lazyRun_msgOpenWV_of_eval (w : WinCheck vp prims) (wO : WinCheckO vp prims)
    (hw : wO.eval = w) (A : Forger vp prims optRand pkSeedDist) :
    lazyRun (PublicHash.impl prims) (msgOpenWV wO A) = bPrfMsgWL w A := by
  rw [lazyRun_msgOpenWV, hw]

/-- **The headline instance**: `msgOpenWV sufCheckO A` is `bPrfMsgWL sufCheck A`. -/
theorem lazyRun_msgOpenWV_sufCheck (A : Forger vp prims optRand pkSeedDist) :
    lazyRun (PublicHash.impl prims) (msgOpenWV sufCheckO A) = bPrfMsgWL sufCheck A :=
  lazyRun_msgOpenWV_of_eval _ _ sufCheckO_eval A

/-- Resource-explicit form: `bPrfMsgL A` is the interpretation (draw ↦ `$ᵗ`, hash query ↦
evaluation by `prims`) of `lazyRes (msgOpenV A)`. -/
theorem bPrfMsgL_eq_lazyRes_msgOpenV (A : Forger vp prims optRand pkSeedDist) :
    bPrfMsgL A = simulateQ (interp (PublicHash.impl prims)) (lazyRes (msgOpenV A)) :=
  (lazyRun_msgOpenV A).symm

theorem bPrfMsgWL_eq_lazyRes_msgOpenWV (A : Forger vp prims optRand pkSeedDist) :
    bPrfMsgWL sufCheck A =
      simulateQ (interp (PublicHash.impl prims)) (lazyRes (msgOpenWV sufCheckO A)) :=
  (lazyRun_msgOpenWV_sufCheck A).symm

/-- Table interpretation (as `msgOpen_tbl`). -/
theorem msgOpenV_tbl (A : Forger vp prims optRand pkSeedDist) (g : SecretTable vp prims) :
    simulateQ (tblImpl (PublicHash.impl prims) g) (msgOpenV A) =
      simulateQ (tblImpl (PublicHash.impl prims) g) (msgOpen A) := by
  rw [msgOpen_eq_pre]
  unfold msgOpenV
  simp only [simulateQ_bind, simulateQ_pure, simulateQ_tblImpl_emb, eufCheckO_eval]

theorem msgOpenWV_tbl (wO : WinCheckO vp prims) (A : Forger vp prims optRand pkSeedDist)
    (g : SecretTable vp prims) :
    simulateQ (tblImpl (PublicHash.impl prims) g) (msgOpenWV wO A) =
      simulateQ (tblImpl (PublicHash.impl prims) g) (msgOpenW wO.eval A) := by
  rw [msgOpenW_eq_pre]
  unfold msgOpenWV
  simp only [simulateQ_bind, simulateQ_pure, simulateQ_tblImpl_emb]
  rfl

/-! ## Counts -/

/-- Hash queries of one verification INCLUDING its `H_msg` query. -/
theorem verifyInternalQueryBound_eq :
    GeneralScheme.verifyInternalQueryBound vp.params = 1 + Resources2.verifyHashes vp := by
  unfold GeneralScheme.verifyInternalQueryBound GeneralHypertree.recoverQueryBound
    GeneralHypertree.xmssRecoverQueryBound Resources2.verifyHashes
  ring

theorem eufCheckO_total (pk : PublicKeyCore prims.core) (msgs : List (List Byte))
    (msg : List Byte) (sig : GeneralScheme.SignatureCore vp prims.core) :
    IsTotalQueryBound (eufCheckO pk msgs msg sig) (1 + Resources2.verifyHashes vp) := by
  rw [← verifyInternalQueryBound_eq]
  unfold eufCheckO
  have h := isTotalQueryBound_bind
    (GeneralScheme.verifyInternalM_isTotalQueryBound vp prims.core msg sig pk)
    (fun b => show IsTotalQueryBound
      (pure (decide (msg ∉ msgs) && b) : OracleComp (publicHashSpec prims.core) Bool) 0
      from trivial)
  simpa [map_eq_bind_pure_comp] using h

theorem sufCheckO_total (pk : PublicKeyCore prims.core)
    (f : List Byte × GeneralScheme.SignatureCore vp prims.core) (log : SigLog vp prims) :
    IsTotalQueryBound (sufCheckO pk f log) (1 + Resources2.verifyHashes vp) := by
  rw [← verifyInternalQueryBound_eq]
  unfold sufCheckO
  let _ := sigDecEq (vp := vp) (prims := prims)
  have h := isTotalQueryBound_bind
    (GeneralScheme.verifyInternalM_isTotalQueryBound vp prims.core f.1 f.2 pk)
    (fun b => show IsTotalQueryBound
      (pure (!SignatureAlg.signingLogContains log f.1 f.2 && b) :
        OracleComp (publicHashSpec prims.core) Bool) 0
      from trivial)
  simpa [map_eq_bind_pure_comp] using h

theorem msgPre_kindBound (A : Forger vp prims optRand pkSeedDist) (K : Kind) (hK : K ≠ .unif)
    (qs : ℕ) (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs) :
    IsQueryBoundP (msgPre A) (fun t => kind t = K)
      (keygenB vp (ind K .sec) (ind K .hash) +
        qs * (ind K .game + signB vp (ind K .sec) (ind K .hash))) := by
  have h := msgOpen_kindBound A K hK qs hA
  have he : msgOpen A = (fun x => harnessValid x.1 x.2.2 x.2.1.1 x.2.1.2) <$> msgPre A := by
    rw [msgOpen_eq_pre, map_eq_bind_pure_comp]; rfl
  rwa [he, isQueryBoundP_map_iff] at h

theorem msgPreW_kindBound (A : Forger vp prims optRand pkSeedDist) (K : Kind) (hK : K ≠ .unif)
    (qs : ℕ) (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs) :
    IsQueryBoundP (msgPreW A) (fun t => kind t = K)
      (keygenB vp (ind K .sec) (ind K .hash) +
        qs * (ind K .game + signB vp (ind K .sec) (ind K .hash))) := by
  have h := msgOpenW_kindBound (fun _ _ _ => true) A K hK qs hA
  have he : msgOpenW (fun _ _ _ => true) A = (fun _ => true) <$> msgPreW A := by
    rw [msgOpenW_eq_pre, map_eq_bind_pure_comp]; rfl
  rwa [he, isQueryBoundP_map_iff] at h

/-- Queries of kind `K` of `msgOpenV A`: those of `msgOpen A`, plus `1 + verifyHashes vp`
hash-kind queries for the final verification. -/
theorem msgOpenV_kindBound (A : Forger vp prims optRand pkSeedDist) (K : Kind) (hK : K ≠ .unif)
    (qs : ℕ) (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs) :
    IsQueryBoundP (msgOpenV A) (fun t => kind t = K)
      (keygenB vp (ind K .sec) (ind K .hash) +
        qs * (ind K .game + signB vp (ind K .sec) (ind K .hash)) +
        (1 + Resources2.verifyHashes vp) * ind K .hash) :=
  qb_bind _ (msgPre_kindBound A K hK qs hA) fun x =>
    emb_kindBound K _ _ (eufCheckO_total x.1 x.2.2 x.2.1.1 x.2.1.2)

/-- Queries of kind `K` of `msgOpenWV wO A`, for an open check making at most `n` queries. -/
theorem msgOpenWV_kindBound (wO : WinCheckO vp prims) (n : ℕ)
    (hw : ∀ pk f log, IsTotalQueryBound (wO pk f log) n)
    (A : Forger vp prims optRand pkSeedDist) (K : Kind) (hK : K ≠ .unif)
    (qs : ℕ) (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs) :
    IsQueryBoundP (msgOpenWV wO A) (fun t => kind t = K)
      (keygenB vp (ind K .sec) (ind K .hash) +
        qs * (ind K .game + signB vp (ind K .sec) (ind K .hash)) + n * ind K .hash) :=
  qb_bind _ (msgPreW_kindBound A K hK qs hA) fun x => emb_kindBound K _ _ (hw x.1 x.2.1 x.2.2)

section Closed

variable (A : Forger vp prims optRand pkSeedDist) (qs : ℕ)
  (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs)
include hA

/-- **Hash-kind queries of `msgOpenV A`**: `keygenHashes + qs·signHashes + (1 + verifyHashes)`. -/
theorem msgOpenV_hashes :
    IsQueryBoundP (msgOpenV A) (fun t => kind t = .hash)
      (keygenHashes vp + qs * signHashes vp + (1 + Resources2.verifyHashes vp)) :=
  (msgOpenV_kindBound A .hash (by decide) qs hA).mono (by
    have h1 := keygenB_hash (vp := vp)
    have h2 := Nat.mul_le_mul_left qs (signB_hash (vp := vp))
    simp only [ind, ite_true, reduceCtorEq, ite_false, Nat.zero_add, Nat.mul_one]
    omega)

/-- **Game-kind queries of `msgOpenV A`**: one per signing query. -/
theorem msgOpenV_game :
    IsQueryBoundP (msgOpenV A) (fun t => kind t = .game) qs :=
  (msgOpenV_kindBound A .game (by decide) qs hA).mono
    (by simp [ind, keygenB_game, signB_game])

/-- **Secret-kind queries of `msgOpenV A`**: as for `msgOpen A`. -/
theorem msgOpenV_sec :
    IsQueryBoundP (msgOpenV A) (fun t => kind t = .sec)
      (2 ^ vp.params.hp * vp.params.len + qs * signReads vp) :=
  (msgOpenV_kindBound A .sec (by decide) qs hA).mono (by
    have h1 := keygenB_sec (vp := vp)
    have h2 := Nat.mul_le_mul_left qs (signB_sec (vp := vp))
    simp only [ind, ite_true, reduceCtorEq, ite_false, Nat.zero_add, Nat.mul_zero, Nat.add_zero]
    omega)

/-- Hash queries of the resource-explicit program `lazyRes (msgOpenV A)`. -/
theorem lazyRes_msgOpenV_hashes :
    IsQueryBoundP (lazyRes (msgOpenV A)) (fun t => kind t = .hash)
      (keygenHashes vp + qs * signHashes vp + (1 + Resources2.verifyHashes vp)) :=
  lazyRes_bound_hash _ _ (msgOpenV_hashes A qs hA)

/-- Game queries of `lazyRes (msgOpenV A)`. -/
theorem lazyRes_msgOpenV_game :
    IsQueryBoundP (lazyRes (msgOpenV A)) (fun t => kind t = .game) qs :=
  lazyRes_bound_game _ _ (msgOpenV_game A qs hA)

/-- Fresh uniform draws of `lazyRes (msgOpenV A)`. -/
theorem lazyRes_msgOpenV_draws :
    IsQueryBoundP (lazyRes (msgOpenV A)) (fun t => kind t = .sec)
      (2 ^ vp.params.hp * vp.params.len + qs * signReads vp) :=
  lazyRes_bound_draws _ _ (msgOpenV_sec A qs hA)

/-- **Hash-kind queries of `msgOpenWV sufCheckO A`** (the SUF check costs exactly one
verification; the log comparison makes no query). -/
theorem msgOpenWV_suf_hashes :
    IsQueryBoundP (msgOpenWV sufCheckO A) (fun t => kind t = .hash)
      (keygenHashes vp + qs * signHashes vp + (1 + Resources2.verifyHashes vp)) :=
  (msgOpenWV_kindBound sufCheckO _ sufCheckO_total A .hash (by decide) qs hA).mono (by
    have h1 := keygenB_hash (vp := vp)
    have h2 := Nat.mul_le_mul_left qs (signB_hash (vp := vp))
    simp only [ind, ite_true, reduceCtorEq, ite_false, Nat.zero_add, Nat.mul_one]
    omega)

theorem msgOpenWV_suf_game :
    IsQueryBoundP (msgOpenWV sufCheckO A) (fun t => kind t = .game) qs :=
  (msgOpenWV_kindBound sufCheckO _ sufCheckO_total A .game (by decide) qs hA).mono
    (by simp [ind, keygenB_game, signB_game])

theorem msgOpenWV_suf_sec :
    IsQueryBoundP (msgOpenWV sufCheckO A) (fun t => kind t = .sec)
      (2 ^ vp.params.hp * vp.params.len + qs * signReads vp) :=
  (msgOpenWV_kindBound sufCheckO _ sufCheckO_total A .sec (by decide) qs hA).mono (by
    have h1 := keygenB_sec (vp := vp)
    have h2 := Nat.mul_le_mul_left qs (signB_sec (vp := vp))
    simp only [ind, ite_true, reduceCtorEq, ite_false, Nat.zero_add, Nat.mul_zero, Nat.add_zero]
    omega)

theorem lazyRes_msgOpenWV_suf_hashes :
    IsQueryBoundP (lazyRes (msgOpenWV sufCheckO A)) (fun t => kind t = .hash)
      (keygenHashes vp + qs * signHashes vp + (1 + Resources2.verifyHashes vp)) :=
  lazyRes_bound_hash _ _ (msgOpenWV_suf_hashes A qs hA)

theorem lazyRes_msgOpenWV_suf_game :
    IsQueryBoundP (lazyRes (msgOpenWV sufCheckO A)) (fun t => kind t = .game) qs :=
  lazyRes_bound_game _ _ (msgOpenWV_suf_game A qs hA)

theorem lazyRes_msgOpenWV_suf_draws :
    IsQueryBoundP (lazyRes (msgOpenWV sufCheckO A)) (fun t => kind t = .sec)
      (2 ^ vp.params.hp * vp.params.len + qs * signReads vp) :=
  lazyRes_bound_draws _ _ (msgOpenWV_suf_sec A qs hA)

end Closed

/-! ## Independence of `Thash` / `Hmsg`

The open programs are literally the same when the `Thash`/`Hmsg` components of `prims` are
replaced by arbitrary functions (the forger being the same program, `castForger`): no evaluation
of `prims.Thash` or `prims.Hmsg` occurs in them. (`Lazy.msgOpen` does not have this property.) -/

theorem msgOpenV_castForger (T : prims.PkSeed → prims.AdrsKey → List prims.Y → prims.Y)
    (H : prims.Y → prims.PkSeed → prims.Y → List Byte → Bytes vp.params.m)
    (A : Forger vp prims optRand pkSeedDist) :
    msgOpenV (prims := withTH prims T H) (castForger T H A) = msgOpenV A := rfl

theorem msgOpenWV_castForger (T : prims.PkSeed → prims.AdrsKey → List prims.Y → prims.Y)
    (H : prims.Y → prims.PkSeed → prims.Y → List Byte → Bytes vp.params.m)
    (A : Forger vp prims optRand pkSeedDist) :
    msgOpenWV (prims := withTH prims T H) sufCheckO (castForger T H A) =
      msgOpenWV sufCheckO A := rfl

theorem itsrRandomizerO_withTH (T : prims.PkSeed → prims.AdrsKey → List prims.Y → prims.Y)
    (H : prims.Y → prims.PkSeed → prims.Y → List Byte → Bytes vp.params.m)
    (pkSeed : prims.PkSeed) (root : prims.Y) :
    Lazy.itsrRandomizerO (prims := withTH prims T H) pkSeed root =
      Lazy.itsrRandomizerO (prims := prims) pkSeed root := by
  funext log m a
  unfold Lazy.itsrRandomizerO
  split <;> rename_i h <;> rw [h] <;> rfl

/-- **R2 item 4.** `Lazy.itsrOpen A` has no final check (it returns the forgery's randomizer and
`(PK.seed, PK.root, M)`); its hash evaluations are those of `openKeygen` and `openSign`, which are
hash-kind queries, and it is the same program for every `Thash`/`Hmsg`. -/
theorem itsrOpen_castForger (T : prims.PkSeed → prims.AdrsKey → List prims.Y → prims.Y)
    (H : prims.Y → prims.PkSeed → prims.Y → List Byte → Bytes vp.params.m)
    (A : Forger vp prims optRand pkSeedDist) :
    Lazy.itsrOpen (prims := withTH prims T H) (castForger T H A) = Lazy.itsrOpen A := by
  unfold Lazy.itsrOpen
  refine bind_congr fun pkSeed => bind_congr fun root => ?_
  rw [itsrRandomizerO_withTH T H pkSeed root]
  rfl

/-- Hence the lazy ITSR adversary over `withTH prims T H` is `itsrOpen A` (independent of `T`,
`H`) with hash queries answered by `T`, `H`. -/
theorem bItsrL_castForger_main (T : prims.PkSeed → prims.AdrsKey → List prims.Y → prims.Y)
    (H : prims.Y → prims.PkSeed → prims.Y → List Byte → Bytes vp.params.m)
    (A : Forger vp prims optRand pkSeedDist) :
    (Lazy.bItsrL (prims := withTH prims T H) (castForger T H A)).main =
      lazyRun (PublicHash.impl (withTH prims T H)) (Lazy.itsrOpen (prims := prims) A) :=
  congrArg (lazyRun (PublicHash.impl (withTH prims T H))) (itsrOpen_castForger T H A)

/-- The same for the two `PRF_msg` distinguishers. -/
theorem bPrfMsgL_castForger (T : prims.PkSeed → prims.AdrsKey → List prims.Y → prims.Y)
    (H : prims.Y → prims.PkSeed → prims.Y → List Byte → Bytes vp.params.m)
    (A : Forger vp prims optRand pkSeedDist) :
    Lazy.bPrfMsgL (prims := withTH prims T H) (castForger T H A) =
      lazyRun (PublicHash.impl (withTH prims T H)) (msgOpenV (prims := prims) A) :=
  (lazyRun_msgOpenV (prims := withTH prims T H) (castForger T H A)).symm

theorem bPrfMsgWL_castForger (T : prims.PkSeed → prims.AdrsKey → List prims.Y → prims.Y)
    (H : prims.Y → prims.PkSeed → prims.Y → List Byte → Bytes vp.params.m)
    (A : Forger vp prims optRand pkSeedDist) :
    Lazy.bPrfMsgWL (prims := withTH prims T H) sufCheck (castForger T H A) =
      lazyRun (PublicHash.impl (withTH prims T H)) (msgOpenWV (prims := prims) sufCheckO A) :=
  (lazyRun_msgOpenWV_sufCheck (prims := withTH prims T H) (castForger T H A)).symm

/-! ## SLH-DSA-SHA2-128s -/

theorem msgOpenV_hashes_128s
    {optRand : PublicKeyCore Link.prims.core → ProbComp Link.prims.Y}
    {pkSeedDist : ProbComp Link.prims.PkSeed}
    (A : Forger Link.vp Link.prims optRand pkSeedDist) (qs : ℕ)
    (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs) :
    IsQueryBoundP (msgOpenV A) (fun t => kind t = .hash) (269824 + qs * 2007385 + 3929) ∧
    IsQueryBoundP (lazyRes (msgOpenV A)) (fun t => kind t = .hash)
      (269824 + qs * 2007385 + 3929) ∧
    IsQueryBoundP (msgOpenWV sufCheckO A) (fun t => kind t = .hash)
      (269824 + qs * 2007385 + 3929) ∧
    IsQueryBoundP (lazyRes (msgOpenWV sufCheckO A)) (fun t => kind t = .hash)
      (269824 + qs * 2007385 + 3929) := by
  have h1 := msgOpenV_hashes A qs hA
  have h2 := lazyRes_msgOpenV_hashes A qs hA
  have h3 := msgOpenWV_suf_hashes A qs hA
  have h4 := lazyRes_msgOpenWV_suf_hashes A qs hA
  rw [keygenHashes_128s, signHashes_128s, Resources2.verifyHashes_128s] at h1 h2 h3 h4
  exact ⟨h1, h2, h3, h4⟩

end Open
end Reduction

#print axioms Reduction.Open.lazyRun_msgOpenV
#print axioms Reduction.Open.lazyRun_msgOpenWV_sufCheck
#print axioms Reduction.Open.msgOpenV_hashes
#print axioms Reduction.Open.msgOpenV_game
#print axioms Reduction.Open.msgOpenV_sec
#print axioms Reduction.Open.lazyRes_msgOpenV_hashes
#print axioms Reduction.Open.lazyRes_msgOpenWV_suf_hashes
#print axioms Reduction.Open.msgOpenV_castForger
#print axioms Reduction.Open.itsrOpen_castForger
#print axioms Reduction.Open.bItsrL_castForger_main
#print axioms Reduction.Open.bPrfMsgWL_castForger
#print axioms Reduction.Open.msgOpenV_hashes_128s
