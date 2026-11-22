import Ideal.Realize.WotsUdFine
import Ideal.Realize.TcrCount3
import Ideal.Games.TcrFine

/-!
# The single-block SM-TCR realisers with their message blocks issued as free chain queries

As `WotsUdFine.lean`, for the two families bounded by `tcr_bound`:

* the WOTS-chain SM-TCR realiser (`tcrForge`, `Wots.realizesWotsTcrL`): `tcrForgeC`,
  `tcrForge_eq_expand`, `tcrForgeC_free`, `tcrForgeC_boundR` (at `pk ≠ 0`, at most
  `qMW = qf + 2·tcrH qs + 9·tcrLg qs` raw queries), `wotsTcrLeg_fine(E)`;
* the answer-storing class-TCR realiser at arities `1` (`F`) and `2` (`H`) (`forgeP3G`,
  `Tcr.realizesTcr3S`): `tcrMOpenPS_foreign` (every `H_msg` query of its second phase is at the
  public seed), `forgeP3GC`, `forgeP3G_eq_expand`, `forgeP3GC_free`, `forgeP3GC_boundR` (at most
  `qMT = qf + 2·verifyHashes·11` raw queries), `classTcrLeg_fine(E)`.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security TweakableHash ENNReal

namespace Ideal.Realize.Wots

open Reduction Reduction.Open Reduction.Lazy Reduction.Resources2 Ideal.Realize Ideal.Transport
open Ideal.Realize.Fors (isLongIdx)

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! ## WOTS-chain SM-TCR -/

section WotsTcr

variable (optRand : PublicKeyCore core₀ → ProbComp core₀.Y) (mainP : PortForgerProg Link.vp P0)
  (ℓ : ℕ)

theorem wTcrP_foreign (hist hist2 : List (WotsGame.Entry P0)) (root : P0.Y) (pk : P0.PkSeed)
    (hlong : IsQueryBoundP (mainP ⟨pk, root⟩)
      (fun i => isLongQ (S := GeneralScheme.SignatureCore Link.vp P0.core) ℓ i = true) 0) :
    IsQueryBoundP (wTcrP optRand mainP hist hist2 root pk) (fun t => isForeignIdx pk t = true) 0 :=
  wPhase2P_bound optRand mainP _ hist root pk _ 0 (0 + 0) 0
    (wForgeP_foreign optRand mainP ℓ hist root pk hlong)
    (fun r _ => pw_answer _ (foreign_hsec pk) (fun pk' key xs hx => foreign_hth pk pk' key xs hx)
      hist _ _ _ 0 (foreign_hm _ pk _ _))
    (fun x => pw_tcr _ (fun pk' key xs hx => foreign_hth pk pk' key xs hx) _ _ _ _ _)

end WotsTcr

section WotsTcrDist

variable (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))

/-- **Second phase of the ideal-model WOTS-chain SM-TCR adversary with chain queries.** -/
noncomputable def tcrForgeC (st : Open.RState Link.vp P0) (pk : Bytes 16) :
    OracleComp (pcS St Blk) (ℕ × Bytes 16) :=
  simulateQ (chainImplH st.1.1 pk) (wTcrP (optRand₀ oR) (mainP S) st.1.2.1 st.2 st.1.2.2 pk)

theorem tcrForge_eq_expand (st : Open.RState Link.vp P0) (pk : Bytes 16) :
    tcrForge S oR st pk = simulateQ (expandImpl IV128) (tcrForgeC S oR st pk) :=
  (expand_simulateQ_chainImplH _ _ _).symm

theorem tcrForgeC_free (st : Open.RState Link.vp P0) (pk : Bytes 16) :
    AllQueriesSatisfy (tcrForgeC S oR st pk) (freeC (sb128 pk)) :=
  allQueriesSatisfy_simulateQ _ _ (chainImplH_free _ _) _

/-- Raw compression queries of the WOTS-chain SM-TCR second phase with chain queries. -/
abbrev qMW (qf qs : ℕ) : ℕ := qf * 1 + tcrH qs * 2 + (qs + 2) * 0 + tcrLg qs * 9

variable {qf qs ℓ : ℕ}
  (hqf : ∀ pk, IsQueryBoundP (S.main pk)
    (fun i => Ideal.Realize.isPortQ (S := List Byte) i = true) qf)
  (hqs : ∀ pk, IsQueryBoundP (S.main pk)
    (fun i => Ideal.Realize.isSignQ (S := List Byte) i = true) qs)
  (hlong : ∀ pk, IsQueryBoundP (S.main pk)
    (fun i => Ideal.Realize.isLongQ (S := List Byte) ℓ i = true) 0)
  (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ)

include hqf hqs hlong hout in
theorem tcrForgeC_boundR (st : Open.RState Link.vp P0) (pk : Bytes 16) (hpk : pk ≠ zero16) :
    IsQueryBoundP (tcrForgeC S oR st pk) (fun t => isRawC t = true) (qMW qf qs) :=
  Prf.qb_simulateQ_classes4
    (p₀ := fun t => isBadIdx Link.vp.params.len ℓ t = true ∨ isForeignIdx pk t = true)
    (p₁ := fun t => Lazy.kind t = .game) (p₂ := fun t => Lazy.kind t = .hash)
    (p₃ := fun t => isHmsgIdx t = true) (p₄ := fun t => isLongIdx t = true) 1 2 0 9
    (fun t ht => chainImplH_stepR _ ℓ (by decide) _ pk hpk t ht)
    ((wTcrP_bad (prims := P0) _ _ _ _ _ _ Link.vp.params.len ℓ okLen_le (mainP_long S hlong _)
      (mainP_out S hout _)).or (wTcrP_foreign _ _ ℓ _ _ _ _ (mainP_long S hlong _)))
    (wTcrP_port (prims := P0) _ _ _ _ _ _ (mainP_port S hqf _))
    (wTcrP_hashes (prims := P0) _ _ _ _ _ _ (mainP_sign S hqs _))
    (wTcrP_hmsg (prims := P0) _ _ _ _ _ _ (mainP_sign S hqs _))
    (wTcrP_long (prims := P0) _ _ _ _ _ _ (mainP_sign S hqs _))

end WotsTcrDist

end Ideal.Realize.Wots

/-! ## Class TCR (answer-storing), arities `1` and `2` -/

namespace Ideal.Realize.Tcr

open Reduction Reduction.Open Ideal.Transport Ideal.Realize.Wots

attribute [local irreducible] Reduction.arityTargets Reduction.tcrTargets
attribute [local irreducible] Reduction.Lazy.sparseTable Reduction.Lazy.structSecIdx

set_option linter.unusedVariables false

section Foreign

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]
variable (optRand : PublicKeyCore prims.core → ProbComp prims.Y) (mainP : PortForgerProg vp prims)
  (L : List (prims.AdrsKey × List prims.Y)) (S : Store prims) (pkSeed : prims.PkSeed)

attribute [local instance] Lazy.openQ

/-- **Every `H_msg` query of the lookup program is at the public seed.** -/
theorem tcrMOpenPS_foreign (qs : ℕ)
    (hqs : ∀ pk, IsQueryBoundP (mainP pk)
      (fun i => isSignQ (S := GeneralScheme.SignatureCore vp prims.core) i = true) qs) :
    IsQueryBoundP (tcrMOpenPS optRand mainP L S pkSeed)
      (fun t => isForeignIdx pkSeed t = true) 0 := by
  have hu : ∀ n : ℕ, ¬ isForeignIdx (ι := St × Blk) (K := prims.AdrsKey) (Y := prims.Y) pkSeed
      (.inl n) = true := by
    intro n; simp [isForeignIdx]
  have hsec : ∀ d : SecIdx, ¬ isForeignIdx (ι := St × Blk) (K := prims.AdrsKey) (Y := prims.Y)
      pkSeed (.inr (.inr (.inl d))) = true := by
    intro d; simp [isForeignIdx]
  have hth : ∀ (pk : prims.PkSeed) (key : prims.AdrsKey) (xs : List prims.Y),
      ¬ isForeignIdx pkSeed (thIdx prims (St × Blk) pk key xs) = true := by
    intro pk key xs; simp [isForeignIdx]
  have hm : ∀ (R : prims.Y) (root : prims.Y) (m : List Byte),
      ¬ isForeignIdx pkSeed (hmIdx prims (St × Blk) R pkSeed root m) = true := by
    intro R root m; simp [isForeignIdx]
  have h := tcrMOpenRK_bound (gspec := hS St Blk) (fun t => isForeignIdx pkSeed t = true)
    (simulateQ (lkImpl (gspec := hS St Blk) pkSeed S) (Lazy.openKeygen prims (hS St Blk) pkSeed))
    (portRunS optRand mainP S pkSeed) L pkSeed 0 (qs * 0) 0 0
    (lk_bound pkSeed S _ _ 0 (np_openKeygen _ pkSeed hsec fun key xs _ => hth _ _ _))
    (fun root => portRunS_bound optRand mainP S pkSeed (fun t => isForeignIdx pkSeed t = true) hu
      (fun q => by simp [isForeignIdx]) 0
      (fun root msg R => lk_bound pkSeed S _ _ 0
        (np_openSign _ msg pkSeed root R hsec (fun key xs _ => hth _ _ _) (hm _ _ _))) qs hqs root)
    (fun root z _ => (isQueryBoundP_query_iff _ _ _).2 fun h => absurd h (hm _ _ _))
    (fun parts sig => np_collO_run _ pkSeed L (fun key xs _ => hth _ _ _)
      (fun q _ => hth _ _ _) parts sig none)
  exact h.mono (by omega)

end Foreign

theorem chainImplH_stepT (ℓ : ℕ) (tbl : SecretTable Link.vp P₀) (pk : Bytes 16)
    (hpk : pk ≠ zero16) (t : (Lazy.OSpec (vp := Link.vp) P₀ (hS St Blk)).Domain)
    (ht : ¬ (isBadIdx Bmax ℓ t = true ∨ isForeignIdx pk t = true)) :
    IsQueryBoundP (chainImplH tbl pk t) (fun t => isRawC t = true)
      ((if Lazy.kind t = .game then 1 else 0) + (if isThIdx t = true then thashCost Bmax else 0) +
        (if isHmsgIdx t = true then 0 else 0)) := by
  simp only [not_or] at ht
  rcases t with n | q | d | (⟨pk', a, xs⟩ | ⟨R, pk', root, M⟩)
  · exact rawE_bound _ _ ((chainImpl_step ℓ tbl _ ht.1).mono
      (by simp [Lazy.kind, isHmsgIdx, isThIdx]))
  · exact rawE_bound _ _ ((chainImpl_step ℓ tbl _ ht.1).mono
      (by simp [Lazy.kind, isHmsgIdx, isThIdx]))
  · exact rawE_bound _ _ ((chainImpl_step ℓ tbl _ ht.1).mono
      (by simp [Lazy.kind, isHmsgIdx, isThIdx]))
  · exact rawE_bound _ _ ((chainImpl_step ℓ tbl _ ht.1).mono
      (by simp [Lazy.kind, isHmsgIdx, isThIdx]))
  · have he : @Eq (Bytes 16) pk' pk := by
      have h2 := ht.2
      simp only [isForeignIdx, decide_eq_true_eq, not_not] at h2
      exact h2
    subst he
    show IsQueryBoundP (hmsgCh pk' R pk' root M) (fun t => isRawC t = true) _
    unfold hmsgCh
    refine (isQueryBoundP_bind (chainOrRaw_free_cost _ _ (iblocksH_head_ne R pk' root M hpk pk'))
      fun s _ => isQueryBoundP_bind (m := 0)
        (chainOrRaw_free_cost _ _ (oblocksH_head_ne R pk' s hpk pk')) fun _ _ =>
          isQueryBoundP_pure _ _ _).mono (by simp)

variable (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) {qf qs ℓ : ℕ}

/-- **Second phase of the answer-storing class-TCR adversary with chain queries.** -/
noncomputable def forgeP3GC (n : ℕ) (tbl : SecretTable Link.vp P₀) (L : List (P₀.AdrsKey × List P₀.Y))
    (Sto : Store P₀) (pk : Bytes 16) :
    OracleComp (pcS St Blk) (ℕ × {xs : List P₀.Y // xs.length = n}) :=
  simulateQ (chainImplH tbl pk)
      (tcrMOpenPS (vp := Link.vp) (prims := P₀) (optRand₀ oR) (typedP codec₀ S.main) L Sto pk) >>=
    fun jm => pure (classOut P₀ n L jm)

theorem forgeP3G_eq_expand (n : ℕ) (tbl : SecretTable Link.vp P₀)
    (L : List (P₀.AdrsKey × List P₀.Y)) (Sto : Store P₀) (pk : Bytes 16) :
    forgeP3G dT dH S oR n tbl L Sto pk =
      simulateQ (expandImpl IV128) (forgeP3GC S oR n tbl L Sto pk) := by
  unfold forgeP3G forgeP3GC
  rw [simulateQ_bind, expand_simulateQ_chainImplH]
  simp

theorem forgeP3GC_free (n : ℕ) (tbl : SecretTable Link.vp P₀)
    (L : List (P₀.AdrsKey × List P₀.Y)) (Sto : Store P₀) (pk : Bytes 16) :
    AllQueriesSatisfy (forgeP3GC S oR n tbl L Sto pk) (freeC (sb128 pk)) :=
  allQueriesSatisfy_bind (allQueriesSatisfy_simulateQ _ _ (chainImplH_free _ _) _)
    fun _ => allQueriesSatisfy_pure _ _

/-- Raw compression queries of the answer-storing class-TCR second phase with chain queries. -/
def qMT (qf : ℕ) : ℕ := qf * 1 + (Resources2.verifyHashes Link.vp * 2) * thashCost Bmax

theorem forgeP3GC_boundR (n : ℕ)
    (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List Byte) i = true) qf)
    (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List Byte) i = true) qs)
    (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQ (S := List Byte) ℓ i = true) 0)
    (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ)
    (tbl : SecretTable Link.vp P₀) (L : List (P₀.AdrsKey × List P₀.Y))
    (hL : ∀ q ∈ L, q.2.length ≤ Bmax) (Sto : Store P₀) (pk : Bytes 16) (hpk : pk ≠ zero16) :
    IsQueryBoundP (forgeP3GC S oR n tbl L Sto pk) (fun t => isRawC t = true) (qMT qf) := by
  have hX := qb_simulateQ_classes
    (p₀ := fun t => isBadIdx Bmax ℓ t = true ∨ isForeignIdx pk t = true)
    (p₁ := fun t => Lazy.kind t = .game) (p₂ := fun t => isThIdx t = true)
    (p₃ := fun t => isHmsgIdx t = true)
    (q := fun t : (pcS St Blk).Domain => isRawC t = true)
    (impl := chainImplH tbl pk) 1 (thashCost Bmax) 0
    (fun t ht => chainImplH_stepT ℓ tbl pk hpk t ht)
    ((tcrMOpenPS_bad (vp := Link.vp) (prims := P₀) (optRand₀ oR) (typedP codec₀ S.main) L Sto pk
      Bmax ℓ okLen_le hL (typedP_long S hlong) (typedP_outLen S hout)).or
      (tcrMOpenPS_foreign (vp := Link.vp) (prims := P₀) (optRand₀ oR) (typedP codec₀ S.main) L
        Sto pk qs (typedP_sign S hqs)))
    (tcrMOpenPS_port (vp := Link.vp) (prims := P₀) (optRand₀ oR) (typedP codec₀ S.main) L Sto pk
      qf (typedP_port S hqf))
    (tcrMOpenPS_th (vp := Link.vp) (prims := P₀) (optRand₀ oR) (typedP codec₀ S.main) L Sto pk
      qs (typedP_sign S hqs))
    (tcrMOpenPS_hmsg (vp := Link.vp) (prims := P₀) (optRand₀ oR) (typedP codec₀ S.main) L Sto pk
      qs (typedP_sign S hqs))
  unfold forgeP3GC
  exact (isQueryBoundP_bind (m := 0) hX fun _ _ => isQueryBoundP_pure _ _ _).mono (by
    unfold qMT; omega)

end Ideal.Realize.Tcr

#print axioms Ideal.Realize.Wots.tcrForge_eq_expand
#print axioms Ideal.Realize.Wots.tcrForgeC_boundR
#print axioms Ideal.Realize.Tcr.tcrMOpenPS_foreign
#print axioms Ideal.Realize.Tcr.forgeP3G_eq_expand
#print axioms Ideal.Realize.Tcr.forgeP3GC_boundR
