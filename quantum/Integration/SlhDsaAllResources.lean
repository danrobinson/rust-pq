import Integration.SlhDsaAll
import Integration.SlhDsaResources

/-!
# Quantum resources of the machines of the final unconditional headlines (integration)

NOT part of the default target; checked by `scripts/check-integration.sh`.

For the machines on the right-hand sides of the `…_quantum_all` headlines of
`Integration/SlhDsaAll.lean` (final form: tight caps, memoising class adversaries, EUF and SUF
distinguishers, byte-level and context-string wrappers):

* `quantum_resources_final`: along every path, the instrument-index sequence of each machine is the
  instrument-index sequence of some path of `Q.main pk` (trace-set INCLUSION), with the forger's
  initial state `Q.ρ₀`.  The inclusion bounds number, identity and order of the instruments per
  path; it does not by itself exclude continuing as if a different outcome had occurred, nor
  classical simulation — the certificate for that is `reduction_certificate`
  (`Integration/SlhDsaAllCertificate.lean`).  For the two-phase machines this is the statement for the second phase;
  their first phase has type `OracleComp (unifSpec + …) State`: classical by typing.
* `QForger.traces_wrapForger`, `traces_qToInternal`, `traces_qBytesToTyped`,
  `traces_qPureBytesToInternal`: the interface translations add no instrument: one run of the
  translated forger is one run of the original forger.
* `slhdsa_*_final_quantum_all_resources`: the headline together with these facts.

Classical query counts of the new machines (the analogue of `qfinal_resources` for the SUF
distinguishers, `qbTcrArM n` and `qrTcrT`) are not ported here.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal PQ.Interactive
open scoped ComplexOrder

namespace PQ.Interactive

variable {W : Type} [Fintype W] {M PK SK S Mb PKb SKb Sb : Type}
variable {alg : SignatureAlg ProbComp M PK SK S} {balg : SignatureAlg ProbComp Mb PKb SKb Sb}

/-- The instrument sequences of one run of the forger on some public key. -/
def QForger.traces (Q : QForger W alg) : Set (List (InstrIdx W)) :=
  ⋃ pk, instrTraces (Q.main pk)

/-- A classical interface translation adds no instrument: every run of the translated forger
applies the instruments of one run of the original forger. -/
theorem QForger.traces_wrapForger
    (h : QueryImpl (unifSpec + (Mb →ₒ Sb)) (OracleComp (unifSpec + (M →ₒ S))))
    (encPk : PK → PKb) (rd : Mb × Sb → M × S) (Q : QForger W balg) :
    (Q.wrapForger (alg := alg) h encPk rd).traces ⊆ Q.traces := by
  intro l hl
  obtain ⟨pk, hpk⟩ := Set.mem_iUnion.1 hl
  exact Set.mem_iUnion.2 ⟨encPk pk,
    instrTraces_wrap0_subset _ _ (instrTraces_map_subset _ _ hpk)⟩

end PQ.Interactive

namespace Reduction

open TweakableHash

set_option linter.unusedSectionVars false

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]
  [Fintype prims.Y]
variable {codec : CoreWireCodec vp.params prims.core}
variable {optRand : PublicKeyCore prims.core → ProbComp prims.Y}
  {pkSeedDist : ProbComp prims.PkSeed}
variable {W : Type} [Fintype W]

attribute [local irreducible] arityTargets tcrTargets

/-! ## The new machines -/

theorem instrTraces_qbPrfW (w : WinCheck vp prims)
    (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) :
    instrTraces (qbPrfW w Q) ⊆ forgerTraces Q :=
  instrTraces_liftQ_bind_subset_of _ _ fun _ ↦ instrTraces_liftQ_bind_subset_of _ _ fun _ ↦
    instrTraces_liftQ_bind_subset_of _ _ fun _ ↦ instrTraces_bind_liftQ_subset_of _ _
      ((instrTraces_wrap_subset _ _ _).trans (instrTraces_main_subset Q _))

/-- `qbPrfWC w Q` instrument traces are included in those of `Q` (trace-set inclusion). -/
theorem instrTraces_qbPrfWC (w : WinCheck vp prims)
    (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) :
    instrTraces (qbPrfWC w Q) ⊆ forgerTraces Q :=
  (instrTraces_wrap0_subset _ _).trans (instrTraces_qbPrfW w Q)

/-- `qbPrfMsgWL w Q` instrument traces are included in those of `Q` (trace-set inclusion). -/
theorem instrTraces_qbPrfMsgWL (w : WinCheck vp prims)
    (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) :
    instrTraces (qbPrfMsgWL w Q) ⊆ forgerTraces Q :=
  (instrTraces_qLazyRun _ _).trans <|
    instrTraces_liftQ_bind_subset_of _ _ fun _ ↦ instrTraces_liftQ_bind_subset_of _ _ fun _ ↦
      instrTraces_bind_liftQ_subset_of _ _
        ((instrTraces_wrap_subset _ _ _).trans (instrTraces_main_subset Q _))

/-- Second phase of `qbTcrArM n Q`: instrument traces included in those of `Q` (trace-set inclusion). -/
theorem instrTraces_qMemoForge (n : ℕ) (Q : QForger W (internalAlg vp prims optRand pkSeedDist))
    (st : SecretTable vp prims × List (prims.AdrsKey × List prims.Y)) (pkSeed : prims.PkSeed) :
    instrTraces (qMemoForge n Q st pkSeed) ⊆ forgerTraces Q :=
  instrTraces_bind_liftU_subset_of _ _
    ((instrTraces_close_subset _ _ _).trans (instrTraces_main_subset Q _))

/-- Second phase of `qrTcrT Q`: instrument traces included in those of `Q` (trace-set inclusion). -/
theorem instrTraces_qrTcrT_forge (Q : QForger W (internalAlg vp prims optRand pkSeedDist))
    (st : (SecretTable vp prims × List (WotsGame.Entry prims) × prims.Y) ×
      List (WotsGame.Entry prims)) (pk : prims.PkSeed) :
    instrTraces ((qrTcrT Q).forge st pk) ⊆ forgerTraces Q :=
  instrTraces_bind_liftU_subset_of _ _ (instrTraces_qWotsForge Q st.1 pk)

/-- **Quantum resources of the machines of the final headlines** (`qBetaEufMemo`, `qBetaSufMemo`,
and the two sides of the linear forms).  The instrument-index sequence of every path of each machine
is that of some path of `Q.main pk` for one public key (trace-set inclusion; see
`reduction_certificate` for the syntactic certificate), and the two-phase machines start their
quantum phase from `Q.ρ₀`. -/
structure QuantumResourcesFinal (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) :
    Prop where
  prf : instrTraces (qbPrfC Q) ⊆ forgerTraces Q
  prfSuf : instrTraces (qbPrfWC sufCheck Q) ⊆ forgerTraces Q
  msg : instrTraces (qbPrfMsgL Q) ⊆ forgerTraces Q
  msgSuf : instrTraces (qbPrfMsgWL sufCheck Q) ⊆ forgerTraces Q
  itsr : instrTraces (qbItsrL Q) ⊆ forgerTraces Q
  dspr : ∀ st pk, instrTraces ((qToDspr Q).guess st pk) ⊆ forgerTraces Q
  tcrF : ∀ st pk, instrTraces ((qToTcr Q).forge st pk) ⊆ forgerTraces Q
  /-- the four arity classes `n = 1, 2, len, k` (stated for every `n`) -/
  tcrAr : ∀ n st pk, instrTraces (qMemoForge n Q st pk) ⊆ forgerTraces Q
  ud : ∀ st pk, instrTraces ((qrUd Q).distinguish st pk) ⊆ forgerTraces Q
  pre : ∀ st pk, instrTraces ((qrPre Q).invert st pk) ⊆ forgerTraces Q
  tcrW : ∀ st pk, instrTraces ((qrTcrT Q).forge st pk) ⊆ forgerTraces Q
  /-- The quantum phase of every two-phase machine starts from the initial state of `Q`. -/
  rho : (qToDspr Q).ρ₀ = Q.ρ₀ ∧ (qToTcr Q).ρ₀ = Q.ρ₀ ∧ (∀ n, (qbTcrArM n Q).ρ₀ = Q.ρ₀) ∧
    (qrUd Q).ρ₀ = Q.ρ₀ ∧ (qrPre Q).ρ₀ = Q.ρ₀ ∧ (qrTcrT Q).ρ₀ = Q.ρ₀

theorem quantum_resources_final (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) :
    QuantumResourcesFinal Q where
  prf := instrTraces_qbPrfC Q
  prfSuf := instrTraces_qbPrfWC sufCheck Q
  msg := instrTraces_qbPrfMsgL Q
  msgSuf := instrTraces_qbPrfMsgWL sufCheck Q
  itsr := instrTraces_qbItsrL Q
  dspr := instrTraces_qToDspr_guess Q
  tcrF := instrTraces_qToTcr_forge Q
  tcrAr := fun n ↦ instrTraces_qMemoForge n Q
  ud := instrTraces_qrUd_distinguish Q
  pre := instrTraces_qrPre_invert Q
  tcrW := instrTraces_qrTcrT_forge Q
  rho := ⟨rfl, rfl, fun _ ↦ rfl, rfl, rfl, rfl⟩

/-- The `forge` phase of `qbTcrArM n Q` is `qMemoForge n Q`. -/
theorem qbTcrArM_forge (n : ℕ) (Q : QForger W (internalAlg vp prims optRand pkSeedDist))
    (st : SecretTable vp prims × List (prims.AdrsKey × List prims.Y)) (pk : prims.PkSeed) :
    (qbTcrArM n Q).forge st pk = qMemoForge n Q st pk := rfl

/-! ## The interface translations -/

theorem traces_qToInternal (Q : QForger W (externalAlg vp prims optRand pkSeedDist)) :
    forgerTraces (qToInternal Q) ⊆ Q.traces := by
  intro l hl
  obtain ⟨pk, hpk⟩ := Set.mem_iUnion.1 hl
  exact Set.mem_iUnion.2 ⟨pk, instrTraces_wrap0_subset _ _ (instrTraces_map_subset _ _ hpk)⟩

theorem traces_qBytesToTyped (Q : QForger W (bytesAlg vp prims codec optRand pkSeedDist)) :
    forgerTraces (qBytesToTyped Q) ⊆ Q.traces :=
  QForger.traces_wrapForger _ _ _ Q

theorem traces_qPureBytesToInternal
    (Q : QForger W (pureBytesAlg vp prims codec optRand pkSeedDist)) :
    forgerTraces (qPureBytesToInternal Q) ⊆ Q.traces :=
  (traces_qToInternal _).trans (QForger.traces_wrapForger _ _ _ Q)

/-! ## The headlines with resources -/

/-- **SUF-CMA of SLH-DSA on byte strings against every quantum forger, with the quantum
resources of the reduction machines.**  The bound of
`slhdsa_bytes_suf_cma_final_quantum_all`; every machine of the bound applies, on every path,
the instrument sequence of one run of the typed forger `qBytesToTyped Q`, which is the instrument
sequence of one run of `Q`; all quantum phases start from `Q.ρ₀`. -/
theorem slhdsa_bytes_suf_cma_final_quantum_all_resources (hS : Structural vp prims)
    (Q : QForger W (bytesAlg vp prims codec optRand pkSeedDist)) :
    qStrongUnforgeableAdvantage Q ≤ qBetaSufMemo (qBytesToTyped Q) ∧
      QuantumResourcesFinal (qBytesToTyped Q) ∧
      forgerTraces (qBytesToTyped Q) ⊆ Q.traces ∧ (qBytesToTyped Q).ρ₀ = Q.ρ₀ :=
  ⟨slhdsa_bytes_suf_cma_final_quantum_all hS Q, quantum_resources_final _,
    traces_qBytesToTyped Q, rfl⟩

theorem slhdsa_bytes_euf_cma_final_quantum_all_resources (hS : Structural vp prims)
    (Q : QForger W (bytesAlg vp prims codec optRand pkSeedDist)) :
    qUnforgeableAdvantage Q ≤ qBetaEufMemo (qBytesToTyped Q) ∧
      QuantumResourcesFinal (qBytesToTyped Q) ∧
      forgerTraces (qBytesToTyped Q) ⊆ Q.traces ∧ (qBytesToTyped Q).ρ₀ = Q.ρ₀ :=
  ⟨slhdsa_bytes_euf_cma_final_quantum_all hS Q, quantum_resources_final _,
    traces_qBytesToTyped Q, rfl⟩

theorem slhdsa_pure_bytes_suf_cma_final_quantum_all_resources (hS : Structural vp prims)
    (Q : QForger W (pureBytesAlg vp prims codec optRand pkSeedDist)) :
    qStrongUnforgeableAdvantage Q ≤ qBetaSufMemo (qPureBytesToInternal Q) ∧
      QuantumResourcesFinal (qPureBytesToInternal Q) ∧
      forgerTraces (qPureBytesToInternal Q) ⊆ Q.traces ∧ (qPureBytesToInternal Q).ρ₀ = Q.ρ₀ :=
  ⟨slhdsa_pure_bytes_suf_cma_final_quantum_all hS Q, quantum_resources_final _,
    traces_qPureBytesToInternal Q, rfl⟩

theorem slhdsa_pure_bytes_euf_cma_final_quantum_all_resources (hS : Structural vp prims)
    (Q : QForger W (pureBytesAlg vp prims codec optRand pkSeedDist)) :
    qUnforgeableAdvantage Q ≤ qBetaEufMemo (qPureBytesToInternal Q) ∧
      QuantumResourcesFinal (qPureBytesToInternal Q) ∧
      forgerTraces (qPureBytesToInternal Q) ⊆ Q.traces ∧ (qPureBytesToInternal Q).ρ₀ = Q.ρ₀ :=
  ⟨slhdsa_pure_bytes_euf_cma_final_quantum_all hS Q, quantum_resources_final _,
    traces_qPureBytesToInternal Q, rfl⟩

theorem slhdsa_suf_cma_final_quantum_all_resources (hS : Structural vp prims)
    (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) :
    qStrongUnforgeableAdvantage Q ≤ qBetaSufMemo Q ∧ QuantumResourcesFinal Q :=
  ⟨slhdsa_suf_cma_final_quantum_all hS Q, quantum_resources_final Q⟩

theorem slhdsa_euf_cma_final_quantum_all_resources (hS : Structural vp prims)
    (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) :
    qUnforgeableAdvantage Q ≤ qBetaEufMemo Q ∧ QuantumResourcesFinal Q :=
  ⟨slhdsa_euf_cma_final_quantum_all hS Q, quantum_resources_final Q⟩

theorem slhdsa_pure_suf_cma_final_quantum_all_resources (hS : Structural vp prims)
    (Q : QForger W (externalAlg vp prims optRand pkSeedDist)) :
    qStrongUnforgeableAdvantage Q ≤ qBetaSufMemo (qToInternal Q) ∧
      QuantumResourcesFinal (qToInternal Q) ∧
      forgerTraces (qToInternal Q) ⊆ Q.traces ∧ (qToInternal Q).ρ₀ = Q.ρ₀ :=
  ⟨slhdsa_pure_suf_cma_final_quantum_all hS Q, quantum_resources_final _,
    traces_qToInternal Q, rfl⟩

theorem slhdsa_pure_euf_cma_final_quantum_all_resources (hS : Structural vp prims)
    (Q : QForger W (externalAlg vp prims optRand pkSeedDist)) :
    qUnforgeableAdvantage Q ≤ qBetaEufMemo (qToInternal Q) ∧
      QuantumResourcesFinal (qToInternal Q) ∧
      forgerTraces (qToInternal Q) ⊆ Q.traces ∧ (qToInternal Q).ρ₀ = Q.ρ₀ :=
  ⟨slhdsa_pure_euf_cma_final_quantum_all hS Q, quantum_resources_final _,
    traces_qToInternal Q, rfl⟩

end Reduction

#print axioms Reduction.quantum_resources_final
#print axioms Reduction.traces_qPureBytesToInternal
#print axioms Reduction.slhdsa_bytes_suf_cma_final_quantum_all_resources
#print axioms Reduction.slhdsa_bytes_euf_cma_final_quantum_all_resources
#print axioms Reduction.slhdsa_pure_bytes_suf_cma_final_quantum_all_resources
#print axioms Reduction.slhdsa_pure_bytes_euf_cma_final_quantum_all_resources
#print axioms Reduction.slhdsa_suf_cma_final_quantum_all_resources
#print axioms Reduction.slhdsa_euf_cma_final_quantum_all_resources
#print axioms Reduction.slhdsa_pure_suf_cma_final_quantum_all_resources
#print axioms Reduction.slhdsa_pure_euf_cma_final_quantum_all_resources
