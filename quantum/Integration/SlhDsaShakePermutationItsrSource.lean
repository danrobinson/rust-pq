import Integration.SlhDsaShakeApiItsr
import Integration.SlhDsaShakePermutationMsgCost
import Integration.SlhDsaCompressionItsrTransport
namespace Reduction.ShakePermutation.ItsrCost

open ShakeApi MLink OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal PQ.Interactive PQ.QROM Quantum
open scoped ComplexOrder Kronecker

set_option maxHeartbeats 2000000
set_option maxRecDepth 12000
variable (S : Sha2Set) {E : Type} [Fintype E] [DecidableEq E] (N : ℕ)
  (optRand₀ : S.Node → S.Node → ProbComp S.Node) (pkSeedDist₀ : ProbComp S.Node)
  (F : PortForger Port Words E)
noncomputable def itsrMach (base : Xof S) (H : Port → Words) :
    QOC (WS Port Words E) (unifSpec + Lazy.itsrG (ShakeApi.primitives S base))
      ((ShakeApi.primitives S base).Y × ItsrIn (ShakeApi.primitives S base)) :=
  qLazyRun (hashPort S N base (SkCost.table S N H)) (qmItsrOpen (signRand S optRand₀ base) pkSeedDist₀ (SkCost.qmForger S F base H))

theorem itsrMach_oracle (base : Xof S) (H : Port → Words) :
    itsrMach S N optRand₀ pkSeedDist₀ F base H =
      qbItsrL (qPureBytesToInternal (forgerAt S optRand₀ pkSeedDist₀ F (extend (SkCost.table S N H)) H)) := by
  let real := ShakeApi.primitives S (extend (SkCost.table S N H))
  let ref := {ShakeApi.primitives S base with Thash := real.Thash, Hmsg := real.Hmsg}
  let rand : PublicKeyCore ref.core → ProbComp ref.Y := fun k => optRand₀ k.pkSeed k.pkRoot
  let B := F.at H (pureBytesAlg S.vp ref (ShakeApi.codec S base) rand pkSeedDist₀)
  have tr := Compression.MessageHash.itsr_tr (prims := ref) real.PRF real.PRFmsg
    (ShakeApi.codec S base) rand (fun k => optRand₀ k.pkSeed k.pkRoot) (fun _ => rfl) pkSeedDist₀ B
  have eq : itsrMach S N optRand₀ pkSeedDist₀ F base H = qbItsrL (qPureBytesToInternal B) := by
    unfold itsrMach
    have hp : hashPort S N base (SkCost.table S N H) = PublicHash.impl ref := by funext t; cases t <;> rfl
    rw [hp]
    have main : (qPureBytesToInternal B).main = SkCost.qmForger S F base H := by
      funext pk
      simp only [B,qPureBytesToInternal,qToInternal,qPureBytesToTyped,QForger.wrapForger,
        PortForger.at,qmCSign_eq,qmCRead_eq,pureBytesView]
      rfl
    kexact congrArg (fun k => qLazyRun (PublicHash.impl ref) (qmItsrOpen (prims := ref) rand pkSeedDist₀ k)) main.symm
  kexact eq.trans tr.symm

theorem pue_qmItsrOpen (base : Xof S) (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hqs : ∀ pk, CountBound isSign (F.main pk) qs) :
    PUE (fun i => 483*ShakeApi.hashWI S base i) (fun H ↦ qmItsrOpen (signRand S optRand₀ base) pkSeedDist₀
      (SkCost.qmForger S F base H)) (q + 483*itsrHashes S.vp qs) := by
  unfold qmItsrOpen
  have h0 : WCount (ShakeApi.hashWI S base) (liftM pkSeedDist₀ :
      OracleComp (Lazy.OSpec (ShakeApi.primitives S base) (Lazy.itsrG (ShakeApi.primitives S base))) _) 0 :=
    wCount_of_isQueryBoundP _ _ _ (Lazy.liftM_kindBound .hash (by decide) pkSeedDist₀)
  have hk : ∀ pkSeed, WCount (ShakeApi.hashWI S base)
      (Lazy.openKeygen (ShakeApi.primitives S base) (Lazy.itsrG (ShakeApi.primitives S base)) pkSeed) (Lazy.keygenHashes S.vp) :=
    fun pkSeed ↦ wCount_of_isQueryBoundP _ _ _ (keygen_hashesG pkSeed)
  have hrun : ∀ pkSeed root, PUE (fun i => 483*ShakeApi.hashWI S base i) (fun H ↦
      wrap ((QueryImpl.ofLift unifSpec (OracleComp (Lazy.OSpec (ShakeApi.primitives S base)
          (Lazy.itsrG (ShakeApi.primitives S base))))).liftTarget
          (StateT (G2Log (ShakeApi.primitives S base)) (OracleComp (Lazy.OSpec (ShakeApi.primitives S base)
            (Lazy.itsrG (ShakeApi.primitives S base))))) +
        logSignOracle (signRand S optRand₀ base) ⟨pkSeed, root⟩
          (Lazy.itsrRandomizerO pkSeed root)
          (fun m R ↦ Lazy.openSign (ShakeApi.primitives S base) (Lazy.itsrG (ShakeApi.primitives S base)) m pkSeed root R))
        (SkCost.qmForger S F base H ⟨pkSeed, root⟩) [] >>= fun z ↦
      liftQ (pure (z.1.2.randomness, (pkSeed, root, z.1.1))))
      (q + qs * (483*Lazy.signHashes S.vp) + 0) := by
    intro pkSeed root
    refine PUE.bind (PUE.wrap _ (cnt := sgnW (483*Lazy.signHashes S.vp)) ?_
      (SkCost.pue_qmForger S F base q qs _ hq hqs ⟨pkSeed, root⟩) []) fun z ↦ ?_
    · intro t s
      have b := MsgCost.scale (ShakeApi.hashWI S base) _ _ (wCount_of_isQueryBoundP _ _ _ (itsr_step_hashes (signRand S optRand₀ base) pkSeed root t s))
      rcases t with n|m
      · simpa [sgnW] using b
      · exact b
    · simp only [liftQ_pure]
      exact PUE.pure _ 0
  have h := PUE.liftQ_bind _ (MsgCost.scale _ _ _ h0) fun pkSeed ↦ PUE.liftQ_bind _ (MsgCost.scale _ _ _ (hk pkSeed)) fun root ↦
    hrun pkSeed root
  refine h.mono ?_
  unfold itsrHashes
  simp only [Nat.mul_add,Nat.mul_left_comm 483 qs]
  omega

theorem pue_itsrMach (base : Xof S) (cap : N ≤ rawCap S 67 65536) (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hqs : ∀ pk, CountBound isSign (F.main pk) qs) :
    PUE (fun _ ↦ 0) (itsrMach S N optRand₀ pkSeedDist₀ F base) (q + 483*itsrHashes S.vp qs) := by
  unfold itsrMach qLazyRun
  refine PUE.wrap0E (fun H ↦ Lazy.interp (hashPort S N base (SkCost.table S N H))) (cnt := fun i => 483*ShakeApi.hashWU S base i) ?_
    (PUE.map _ (PUE.wrap _ (cnt := fun i => 483*ShakeApi.hashWI S base i) ?_ (pue_qmItsrOpen S optRand₀ pkSeedDist₀ F base q qs
      hq hqs) []))
  · intro t
    rcases t with n | t | d | hq'
    · exact (EvalCostQ.const _ (wCount_zero _ _)).mono (Nat.zero_le _)
    · exact (EvalCostQ.const _ (wCount_zero _ _)).mono (Nat.zero_le _)
    · exact (EvalCostQ.const _ (wCount_zero _ _)).mono (Nat.zero_le _)
    · exact MsgCost.liftDet _ (fun _ => rfl) _ (SkCost.hash_cost S N base cap hq')
  · intro t s
    apply MsgCost.scale (ShakeApi.hashWU S base)
    refine wCount_of_isQueryBoundP _ _ _ ?_
    rcases t with n | t | d | hq'
    · simp [Lazy.lazyImplR, Lazy.kind]
    · simp [Lazy.lazyImplR, Lazy.kind]
    · rcases hc : s.lookup d with _ | v
      · rw [Lazy.lazyImplR_sec_run_miss d s hc]
        simp [Lazy.kind]
      · rw [Lazy.lazyImplR_sec_run_hit d s v hc]
        simp
    · simp [Lazy.lazyImplR, Lazy.kind, ShakeApi.hashWI]

end Reduction.ShakePermutation.ItsrCost
#print axioms Reduction.ShakePermutation.ItsrCost.itsrMach_oracle
#print axioms Reduction.ShakePermutation.ItsrCost.pue_itsrMach
