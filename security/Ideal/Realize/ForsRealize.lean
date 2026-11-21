import Ideal.Realize.ForsEq
import Ideal.Realize.ForsBound

/-!
# The FORS-leaf realisers (`RealizesDspr`, `RealizesForsTcr`; SUF and EUF)

For every ideal-model forger `S`, table-independent `opt_rand` sampler `oR` and seed
distribution `pkSeedDist`, and query bounds on the forger (`qf` compression queries, `qs` signing
queries, signed and forged messages of at most `ℓ` bytes):

* `realizesDspr_S`, `realizesDspr_E` : `RealizesDspr pkSeedDist (fun g => toDspr (bOpenPreS
  (S.typedS / S.typedE (optRandU oR) pkSeedDist g))) (pFors qf qs ℓ)`;
* `realizesForsTcr_S`, `realizesForsTcr_E` : the same for `RealizesForsTcr` / `toTcr`;
* `pFors qf qs ℓ = ⟨0, openPreTargets Link.vp, q2Fors qf qs ℓ⟩` (first phase: no compression
  query; challenge queries: the FORS-leaf target cap; second phase: `q2Fors`);
* `q2Fors_eq`: `q2Fors qf qs ℓ = qf + 2968229 + 21450308·qs + (2·qs + 1)·((ℓ + 56)/64 + 3)`
  (from `keygenHashes = 269824`, `forsSignHashes = 1950027`, `k = 14`, `thashCost 35 = 11`);
  `openPreTargets_eq`: `openPreTargets Link.vp = 528905046081400263933952`;
* `pFors_le` : `(pFors qf qs ℓ).Le Qc N` for `Qc ≥ qf + 2968229 + 21450308·qs + (2qs+1)·((ℓ+56)/64+3)`
  and `N ≥ openPreTargets Link.vp`.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security TweakableHash

namespace Ideal.Realize.Fors

open Reduction Reduction.Open Reduction.Lazy Reduction.Resources2 Ideal.Realize

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxHeartbeats 400000

/-- The query parameters of the FORS-leaf realisers. -/
def pFors (qf qs ℓ : ℕ) : P3 := ⟨0, openPreTargets Link.vp, q2Fors qf qs ℓ⟩

/-! ## Closed forms -/

theorem openPreTargets_eq : openPreTargets Link.vp = 528905046081400263933952 := by decide

theorem forsHashes_eq (qs : ℕ) : forsHashes qs = 269839 + qs * 1950028 := by
  unfold forsHashes
  rw [forsSignHashes_128s, show Lazy.keygenHashes Link.vp = 269824 by decide,
    show Link.vp.params.k = 14 by decide]
  omega

theorem q2Fors_eq (qf qs ℓ : ℕ) :
    q2Fors qf qs ℓ = qf + 2968229 + 21450308 * qs + (2 * qs + 1) * ((ℓ + 56) / 64 + 3) := by
  unfold q2Fors
  rw [forsHashes_eq, show thashCost Link.vp.params.len = 11 by decide]
  unfold hmsgCost
  ring_nf

/-- **The bounds in the shape `P3.Le` needs.** -/
theorem pFors_le {qf qs ℓ Qc N : ℕ}
    (hQ : qf + 2968229 + 21450308 * qs + (2 * qs + 1) * ((ℓ + 56) / 64 + 3) ≤ Qc)
    (hN : 528905046081400263933952 ≤ N) : (pFors qf qs ℓ).Le Qc N := by
  refine ⟨Nat.zero_le _, ?_, ?_⟩
  · show openPreTargets Link.vp ≤ N
    rw [openPreTargets_eq]; exact hN
  · show q2Fors qf qs ℓ ≤ Qc
    rw [q2Fors_eq]; exact hQ

/-! ## The forger's bounds, transferred to the typed port forger -/

section Hyp

variable (S : ForgerI)

theorem mainP_port {qf : ℕ}
    (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List Byte) i = true) qf)
    (pk : PublicKeyCore P₀.core) :
    IsQueryBoundP (mainP S pk)
      (fun i => isPortQ (S := GeneralScheme.SignatureCore Link.vp P₀.core) i = true) qf :=
  typedP_bound (prims := P₀) codec₀ (fun i => isPortQ (S := List Byte) i)
    (fun i => isPortQ (S := GeneralScheme.SignatureCore Link.vp P₀.core) i)
    (fun _ _ _ => ⟨rfl, rfl, rfl⟩) S.main pk qf (hqf _)

theorem mainP_sign {qs : ℕ}
    (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List Byte) i = true) qs)
    (pk : PublicKeyCore P₀.core) :
    IsQueryBoundP (mainP S pk)
      (fun i => isSignQ (S := GeneralScheme.SignatureCore Link.vp P₀.core) i = true) qs :=
  typedP_bound (prims := P₀) codec₀ (fun i => isSignQ (S := List Byte) i)
    (fun i => isSignQ (S := GeneralScheme.SignatureCore Link.vp P₀.core) i)
    (fun _ _ _ => ⟨rfl, rfl, rfl⟩) S.main pk qs (hqs _)

theorem mainP_long {ℓ : ℕ}
    (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQ (S := List Byte) ℓ i = true) 0)
    (pk : PublicKeyCore P₀.core) :
    IsQueryBoundP (mainP S pk)
      (fun i => isLongQ (S := GeneralScheme.SignatureCore Link.vp P₀.core) ℓ i = true) 0 :=
  typedP_bound (prims := P₀) codec₀ (fun i => isLongQ (S := List Byte) ℓ i)
    (fun i => isLongQ (S := GeneralScheme.SignatureCore Link.vp P₀.core) ℓ i)
    (fun _ _ _ => ⟨rfl, rfl, rfl⟩) S.main pk 0 (hlong _)

theorem mainP_out {ℓ : ℕ} (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ)
    (pk : PublicKeyCore P₀.core) : ∀ z ∈ support (mainP S pk), z.1.length ≤ ℓ := by
  intro z hz
  obtain ⟨out, hout', h⟩ := typedP_out (prims := P₀) codec₀ S.main pk z hz
  rw [h]
  exact hout _ out hout'

end Hyp

/-! ## The bounds of the ideal-model adversaries -/

section Bounds

variable (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
  (pkSeedDist : ProbComp (Bytes 16))

theorem choose_noH :
    IsQueryBoundP (simulateQ embImpl phase1P :
        OracleComp (FFors128 pkSeedDist).fvAdvS (ForsP1State Link.vp P₀))
      (fun i => THFam.fvIsH (FFors128 pkSeedDist) i = true) 0 :=
  emb_noH _ (fun t => by rcases t with n | t <;> simp [embIdx, THFam.fvIsH]) _

theorem choose_chal :
    IsQueryBoundP (simulateQ embImpl phase1P :
        OracleComp (FFors128 pkSeedDist).fvAdvS (ForsP1State Link.vp P₀))
      (fun i => THFam.fvIsChal (FFors128 pkSeedDist) i = true) (openPreTargets Link.vp) := by
  refine emb_bound _ _ _ (chal_of_eq (vp := Link.vp) (prims := P₀) phase1P phase1P_def _
    fun t ht => ?_)
  rcases t with n | (x | q)
  · simp [embIdx, THFam.fvIsChal] at ht
  · rfl
  · simp [embIdx, THFam.fvIsChal] at ht

theorem dsprAdvI_choose : (dsprAdvI S oR pkSeedDist).ChooseBound 0 := by
  unfold DsprAdv.ChooseBound dsprAdvI
  exact choose_noH pkSeedDist

theorem dsprAdvI_chal : (dsprAdvI S oR pkSeedDist).ChalBound (openPreTargets Link.vp) := by
  unfold DsprAdv.ChalBound dsprAdvI
  exact choose_chal pkSeedDist

theorem tcrAdvI_choose : (tcrAdvI S oR pkSeedDist).ChooseBound 0 := by
  unfold FvAdv.ChooseBound tcrAdvI
  exact choose_noH pkSeedDist

theorem tcrAdvI_chal : (tcrAdvI S oR pkSeedDist).ChalBound (openPreTargets Link.vp) := by
  unfold FvAdv.ChalBound tcrAdvI
  exact choose_chal pkSeedDist

variable {qf qs ℓ : ℕ}
  (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List Byte) i = true) qf)
  (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List Byte) i = true) qs)
  (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQ (S := List Byte) ℓ i = true) 0)
  (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ)

include hqf hqs hlong hout

theorem dsprAdvI_guess : (dsprAdvI S oR pkSeedDist).GuessBound (q2Fors qf qs ℓ) := by
  unfold DsprAdv.GuessBound dsprAdvI
  intro st pk
  exact phase2C_bound _ _ _ qf qs ℓ (mainP_port S hqf) (mainP_sign S hqs)
    (mainP_long S hlong) (mainP_out S hout) _ _ _ pk

theorem tcrAdvI_forge : (tcrAdvI S oR pkSeedDist).ForgeBound (q2Fors qf qs ℓ) := by
  unfold FvAdv.ForgeBound tcrAdvI
  intro st pk
  exact phase2C_bound (β := ℕ × P₀.Y) (fun _ z => forsTcrPost z) (optRand₀ oR dT dH) (mainP S)
    qf qs ℓ (mainP_port S hqf) (mainP_sign S hqs)
    (mainP_long S hlong) (mainP_out S hout) st.1 st.2.1 st.2.2 pk

/-! ## The realisers -/

/-- **The FORS-leaf SM-DSPR realiser, SUF forger.** -/
noncomputable def realizesDspr_S :
    RealizesDspr pkSeedDist
      (fun g => Reduction.toDspr (Reduction.Lazy.bOpenPreS (S.typedS (optRandU oR) pkSeedDist g)))
      (pFors qf qs ℓ) where
  A := dsprAdvI S oR pkSeedDist
  success g := congrArg (fun X => 𝒟[SM_DT_DSPR_SourceFinalValidity.experiment X])
    (dspr_eq_S S oR pkSeedDist g)
  sp g := congrArg (fun X => 𝒟[SM_DT_DSPR_SourceFinalValidity.spExperiment X])
    (dspr_eq_S S oR pkSeedDist g)
  hq₁ := dsprAdvI_choose S oR pkSeedDist
  hch := dsprAdvI_chal S oR pkSeedDist
  hq₂ := dsprAdvI_guess S oR pkSeedDist hqf hqs hlong hout

/-- **The FORS-leaf SM-DSPR realiser, EUF forger.** -/
noncomputable def realizesDspr_E :
    RealizesDspr pkSeedDist
      (fun g => Reduction.toDspr (Reduction.Lazy.bOpenPreS (S.typedE (optRandU oR) pkSeedDist g)))
      (pFors qf qs ℓ) where
  A := dsprAdvI S oR pkSeedDist
  success g := congrArg (fun X => 𝒟[SM_DT_DSPR_SourceFinalValidity.experiment X])
    (dspr_eq_E S oR pkSeedDist g)
  sp g := congrArg (fun X => 𝒟[SM_DT_DSPR_SourceFinalValidity.spExperiment X])
    (dspr_eq_E S oR pkSeedDist g)
  hq₁ := dsprAdvI_choose S oR pkSeedDist
  hch := dsprAdvI_chal S oR pkSeedDist
  hq₂ := dsprAdvI_guess S oR pkSeedDist hqf hqs hlong hout

/-- **The FORS-leaf SM-TCR realiser, SUF forger.** -/
noncomputable def realizesForsTcr_S :
    RealizesForsTcr pkSeedDist
      (fun g => Reduction.toTcr (Reduction.Lazy.bOpenPreS (S.typedS (optRandU oR) pkSeedDist g)))
      (pFors qf qs ℓ) where
  A := tcrAdvI S oR pkSeedDist
  eq g := congrArg (fun X => 𝒟[SM_DT_TCR_SourceFinalValidity.experiment X])
    (tcr_eq_S S oR pkSeedDist g)
  hq₁ := tcrAdvI_choose S oR pkSeedDist
  hch := tcrAdvI_chal S oR pkSeedDist
  hq₂ := tcrAdvI_forge S oR pkSeedDist hqf hqs hlong hout

/-- **The FORS-leaf SM-TCR realiser, EUF forger.** -/
noncomputable def realizesForsTcr_E :
    RealizesForsTcr pkSeedDist
      (fun g => Reduction.toTcr (Reduction.Lazy.bOpenPreS (S.typedE (optRandU oR) pkSeedDist g)))
      (pFors qf qs ℓ) where
  A := tcrAdvI S oR pkSeedDist
  eq g := congrArg (fun X => 𝒟[SM_DT_TCR_SourceFinalValidity.experiment X])
    (tcr_eq_E S oR pkSeedDist g)
  hq₁ := tcrAdvI_choose S oR pkSeedDist
  hch := tcrAdvI_chal S oR pkSeedDist
  hq₂ := tcrAdvI_forge S oR pkSeedDist hqf hqs hlong hout

end Bounds

end Ideal.Realize.Fors

#print axioms Ideal.Realize.Fors.realizesDspr_S
#print axioms Ideal.Realize.Fors.realizesDspr_E
#print axioms Ideal.Realize.Fors.realizesForsTcr_S
#print axioms Ideal.Realize.Fors.realizesForsTcr_E
#print axioms Ideal.Realize.Fors.q2Fors_eq
#print axioms Ideal.Realize.Fors.openPreTargets_eq
#print axioms Ideal.Realize.Fors.pFors_le
