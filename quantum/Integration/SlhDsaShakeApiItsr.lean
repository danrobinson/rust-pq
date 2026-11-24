import Integration.SlhDsaShakeApiForger
import Integration.SlhDsaCompressionItsrTransport
namespace Reduction.ShakeApi

open MLink OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal PQ.Interactive PQ.QROM Quantum
open scoped ComplexOrder Kronecker

variable (S : Sha2Set) {E : Type} [Fintype E] [DecidableEq E] (N : ℕ)
  (optRand₀ : S.Node → S.Node → ProbComp S.Node) (pkSeedDist₀ : ProbComp S.Node)
  (F : PortForger (Input N) (Bytes S.vp.params.m) E)
noncomputable def itsrMach (base : Xof S) (H : Input N → (Bytes S.vp.params.m)) :
    QOC (WS (Input N) (Bytes S.vp.params.m) E) (unifSpec + Lazy.itsrG (primitives S base))
      ((primitives S base).Y × ItsrIn (primitives S base)) :=
  qLazyRun (hashPort S N base H) (qmItsrOpen (signRand S optRand₀ base) pkSeedDist₀ (qmForger S N F base H))

theorem itsrMach_oracle (base : Xof S) (H : RawTable S N) :
    itsrMach S N optRand₀ pkSeedDist₀ F base H =
      qbItsrL (qPureBytesToInternal (rawForger S N optRand₀ pkSeedDist₀ F H)) := by
  let real := primitives S (extend H)
  let ref := {primitives S base with Thash := real.Thash, Hmsg := real.Hmsg}
  let rand : PublicKeyCore ref.core → ProbComp ref.Y := fun k => optRand₀ k.pkSeed k.pkRoot
  let B := F.at H (pureBytesAlg S.vp ref (codec S base) rand pkSeedDist₀)
  have tr := Compression.MessageHash.itsr_tr (prims := ref) real.PRF real.PRFmsg
    (codec S base) rand (fun k => optRand₀ k.pkSeed k.pkRoot) (fun _ => rfl) pkSeedDist₀ B
  have eq : itsrMach S N optRand₀ pkSeedDist₀ F base H = qbItsrL (qPureBytesToInternal B) := by
    unfold itsrMach
    have hp : hashPort S N base H = PublicHash.impl ref := by funext t; cases t <;> rfl
    rw [hp]
    have main : (qPureBytesToInternal B).main = qmForger S N F base H := by
      funext pk
      simp only [B,qPureBytesToInternal,qToInternal,qPureBytesToTyped,QForger.wrapForger,
        PortForger.at,qmCSign_eq,qmCRead_eq,pureBytesView]
      rfl
    kexact congrArg (fun k => qLazyRun (PublicHash.impl ref) (qmItsrOpen (prims := ref) rand pkSeedDist₀ k)) main.symm
  kexact eq.trans tr.symm

abbrev hashWI (base : Xof S) : (Lazy.OSpec (primitives S base) (Lazy.itsrG (primitives S base))).Domain → ℕ :=
  fun t ↦ if Lazy.kind t = .hash then 1 else 0

abbrev hashWU (base : Xof S) :
    (Lazy.RSpec (Lazy.itsrG (primitives S base)) Unit (primitives S base).Y
      (publicHashSpec (primitives S base).core)).Domain → ℕ :=
  fun t ↦ if Lazy.kind t = .hash then 1 else 0

theorem pue_qmItsrOpen (base : Xof S) (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hqs : ∀ pk, CountBound isSign (F.main pk) qs) :
    PUE (hashWI S base) (fun H ↦ qmItsrOpen (signRand S optRand₀ base) pkSeedDist₀
      (qmForger S N F base H)) (q + itsrHashes S.vp qs) := by
  unfold qmItsrOpen
  have h0 : WCount (hashWI S base) (liftM pkSeedDist₀ :
      OracleComp (Lazy.OSpec (primitives S base) (Lazy.itsrG (primitives S base))) _) 0 :=
    wCount_of_isQueryBoundP _ _ _ (Lazy.liftM_kindBound .hash (by decide) pkSeedDist₀)
  have hk : ∀ pkSeed, WCount (hashWI S base)
      (Lazy.openKeygen (primitives S base) (Lazy.itsrG (primitives S base)) pkSeed) (Lazy.keygenHashes S.vp) :=
    fun pkSeed ↦ wCount_of_isQueryBoundP _ _ _ (keygen_hashesG pkSeed)
  have hrun : ∀ pkSeed root, PUE (hashWI S base) (fun H ↦
      wrap ((QueryImpl.ofLift unifSpec (OracleComp (Lazy.OSpec (primitives S base)
          (Lazy.itsrG (primitives S base))))).liftTarget
          (StateT (G2Log (primitives S base)) (OracleComp (Lazy.OSpec (primitives S base)
            (Lazy.itsrG (primitives S base))))) +
        logSignOracle (signRand S optRand₀ base) ⟨pkSeed, root⟩
          (Lazy.itsrRandomizerO pkSeed root)
          (fun m R ↦ Lazy.openSign (primitives S base) (Lazy.itsrG (primitives S base)) m pkSeed root R))
        (qmForger S N F base H ⟨pkSeed, root⟩) [] >>= fun z ↦
      liftQ (pure (z.1.2.randomness, (pkSeed, root, z.1.1))))
      (q + qs * Lazy.signHashes S.vp + 0) := by
    intro pkSeed root
    refine PUE.bind (PUE.wrap _ (cnt := sgnW (Lazy.signHashes S.vp)) ?_
      (pue_qmForger S N F base q qs _ hq hqs ⟨pkSeed, root⟩) []) fun z ↦ ?_
    · exact fun t s ↦ wCount_of_isQueryBoundP _ _ _ (itsr_step_hashes _ pkSeed root t s)
    · simp only [liftQ_pure]
      exact PUE.pure _ 0
  have h := PUE.liftQ_bind _ h0 fun pkSeed ↦ PUE.liftQ_bind _ (hk pkSeed) fun root ↦
    hrun pkSeed root
  refine h.mono ?_
  unfold itsrHashes
  omega

theorem read_costQ {κ α : Type} {sp : OracleSpec κ} (cnt : sp.Domain → ℕ)
    (xs : List SLHDSA.Byte) (decode : Bytes S.vp.params.m → α) :
    EvalCostQ E cnt (fun H : RawTable S N => (pure (decode (extend H xs)) : OracleComp sp α)) 1 := by
  by_cases h : xs.length ≤ N
  · simpa only [extend,dite_eq_left h] using (EvalCostQ.eval (E := E) (cnt := cnt) (BList.ofList xs h) decode)
  · simpa only [extend,dite_eq_right h] using
      (EvalCostQ.const (X := Input N) (Y := Bytes S.vp.params.m) (E := E) (pure (decode default))
        (wCount_pure cnt _ 0)).mono (Nat.zero_le 1)

theorem evalCostQ_hashPort (base : Xof S) {ι' : Type} {sp : OracleSpec ι'}
    (cnt : (unifSpec + sp).Domain → ℕ) (t : (publicHashSpec (primitives S base).core).Domain) :
    EvalCostQ E cnt (fun H ↦ (pure (hashPort S N base H t) :
      OracleComp (unifSpec + sp) ((publicHashSpec (primitives S base).core).Range t))) 1 := by
  cases t with
  | thash pk a xs => exact read_costQ S N cnt _ (prefixBytes S.vp.params.n)
  | hmsg r pk root m => exact read_costQ S N cnt _ id

theorem pue_itsrMach (base : Xof S) (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hqs : ∀ pk, CountBound isSign (F.main pk) qs) :
    PUE (fun _ ↦ 0) (itsrMach S N optRand₀ pkSeedDist₀ F base) (q + itsrHashes S.vp qs) := by
  unfold itsrMach qLazyRun
  refine PUE.wrap0E (fun H ↦ Lazy.interp (hashPort S N base H)) (cnt := hashWU S base) ?_
    (PUE.map _ (PUE.wrap _ (cnt := hashWI S base) ?_ (pue_qmItsrOpen S N optRand₀ pkSeedDist₀ F base q qs
      hq hqs) []))
  · intro t
    rcases t with n | t | d | hq'
    · exact (EvalCostQ.const _ (wCount_zero _ _)).mono (Nat.zero_le _)
    · exact (EvalCostQ.const _ (wCount_zero _ _)).mono (Nat.zero_le _)
    · exact (EvalCostQ.const _ (wCount_zero _ _)).mono (Nat.zero_le _)
    · exact evalCostQ_hashPort S N base _ hq'
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

end Reduction.ShakeApi
#print axioms Reduction.ShakeApi.itsrMach_oracle
#print axioms Reduction.ShakeApi.pue_itsrMach
