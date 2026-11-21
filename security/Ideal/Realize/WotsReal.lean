import Ideal.Realize.WotsPort
import Ideal.Realize.Phase1
import Ideal.Transport.AdvWots
import Ideal.ComposeFinal

/-!
# WOTS realisers: the second phases in the ideal model

Over the table-independent bundle `P0 = R₀ dT dH` (core `core₀`) and the port forger
`mainP S = typedP codec₀ S.main` built from the ideal-model forger `S`:

* `udDist`, `preInv`, `tcrForge` — the second phases of the ideal-model adversaries: the port
  programs `wUdP`, `wPreP`, `wTcrP` with every hash query replaced by its compression chain
  (`chainImpl`), secrets read from the state;
* `udDist_inst`, `preInv_inst`, `tcrForge_inst` — answering their compression queries by `g`
  gives the second phases of `rUd`, `rPre`, `rTcrT` at `Lazy.bWotsS (B₀ S oR pkSeedDist g)`,
  where `B₀ … g` is the Reduction's typed forger over `R₀ (thG g) (hmG g)`;
* `stepUd`, `stepPre`, `stepTcr` — the Reduction's adversaries at `S.typedS (optRandU oR) … g`
  (over `primsG (liftC g)`) ARE those at `B₀ … g` (transport `Ideal.Transport.r*_setPrf_S`);
* `chain_count` — compression queries of a chain-substituted open program:
  `port + hash·thashCost B + hmsg·hmsgCost ℓ`, if no `Thash` query has more than `B` values and
  no `H_msg` query more than `ℓ` bytes;
* `udDist_bound`, `preInv_bound`, `tcrForge_bound` — the resulting second-phase counts.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security TweakableHash

namespace Ideal.Realize.Wots

open Reduction Reduction.Open Reduction.Lazy Reduction.Resources2 Ideal.Realize Ideal.Transport

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! ## The reference bundle, codec, `opt_rand`, forger -/

/-- The wire codec over `core₀` (every carrier `Bytes 16`, encoded as itself). -/
def codec₀ : CoreWireCodec Link.vp.params core₀ where
  pkSeed := WireCodec.bytes Link.vp.params.n
  skSeed := WireCodec.bytes Link.vp.params.n
  skPrf := WireCodec.bytes Link.vp.params.n
  y := WireCodec.bytes Link.vp.params.n
  y_toBytes := fun _ => rfl

/-- The table-independent `opt_rand` over `core₀`. -/
def optRand₀ (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) (pk : PublicKeyCore core₀) :
    ProbComp core₀.Y := oR pk.pkSeed pk.pkRoot

/-- The table-independent reference bundle. -/
abbrev P0 : Primitives Link.vp.params := R₀ dT dH

/-- The typed forger over `R₀ (thG g) (hmG g)` built from the ideal-model forger at `g`. -/
noncomputable def B₀ (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    (pkSeedDist : ProbComp (Bytes 16)) (g : CF St Blk) :
    Forger Link.vp (R₀ (thG g) (hmG g)) (optRand₀ oR) pkSeedDist :=
  (bytesToTypedS (vp := Link.vp) (prims := R₀ (thG g) (hmG g)) (codec := codec₀)
    (optRand := optRand₀ oR) (pkSeedDist := pkSeedDist)
    ⟨fun pk => simulateQ (instImpl g) (S.main pk)⟩).toUnforgeableAdversary

/-- The port forger (table-independent) built from `S`. -/
def mainP (S : ForgerI) : PortForgerProg Link.vp P0 := typedP codec₀ S.main

/-! ## Transport: `primsG (liftC g)` to `R₀ (thG g) (hmG g)` -/

section Step

variable (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
  (pkSeedDist : ProbComp (Bytes 16)) (g : CF St Blk)

theorem stepUd :
    rUd pkSeedDist (Lazy.bWotsS (S.typedS (optRandU oR) pkSeedDist g)) =
      rUd pkSeedDist (Lazy.bWotsS (B₀ S oR pkSeedDist g)) :=
  rUd_setPrf_S (R₀ (thG g) (hmG g)) (prfG g) (pmG g) codec₀ (optRand₀ oR)
    (optRandU oR g) (fun _ => rfl) pkSeedDist (fun pk => simulateQ (instImpl g) (S.main pk))

theorem stepPre :
    rPre pkSeedDist (Lazy.bWotsS (S.typedS (optRandU oR) pkSeedDist g)) =
      rPre pkSeedDist (Lazy.bWotsS (B₀ S oR pkSeedDist g)) :=
  rPre_setPrf_S (R₀ (thG g) (hmG g)) (prfG g) (pmG g) codec₀ (optRand₀ oR)
    (optRandU oR g) (fun _ => rfl) pkSeedDist (fun pk => simulateQ (instImpl g) (S.main pk))

theorem stepTcr :
    rTcrT (vp := Link.vp) pkSeedDist (Lazy.bWotsS (S.typedS (optRandU oR) pkSeedDist g)) =
      rTcrT (vp := Link.vp) pkSeedDist (Lazy.bWotsS (B₀ S oR pkSeedDist g)) :=
  rTcrT_setPrf_S (R₀ (thG g) (hmG g)) (prfG g) (pmG g) codec₀ (optRand₀ oR)
    (optRandU oR g) (fun _ => rfl) pkSeedDist (fun pk => simulateQ (instImpl g) (S.main pk))

/-- The forger with its port answered by `g` is `B₀ … g`. -/
theorem instForger_eq :
    instForger (prims := R₀ (thG g) (hmG g)) (optRand₀ oR) pkSeedDist g (mainP S) =
      B₀ S oR pkSeedDist g := by
  unfold instForger
  have h : (fun pk => simulateQ (instImpl g) (mainP S pk)) = (B₀ S oR pkSeedDist g).main :=
    funext fun pk => typedP_inst (prims := R₀ (thG g) (hmG g)) codec₀ (optRand₀ oR) pkSeedDist g
      S.main pk
  rw [h]

end Step

/-! ## Composition of interpretations -/

theorem simulateQ_comp {ι₁ ι₂ ι₃ : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    {spec₃ : OracleSpec ι₃} (a : QueryImpl spec₂ (OracleComp spec₃))
    (b : QueryImpl spec₁ (OracleComp spec₂)) {α : Type} (x : OracleComp spec₁ α) :
    simulateQ a (simulateQ b x) = simulateQ (fun t => simulateQ a (b t)) x := by
  induction x using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t k ih => simp only [simulateQ_bind, simulateQ_spec_query, ih]

/-- The table interpretation followed by answering compression queries with `g`. -/
noncomputable def φg (g : CF St Blk) (hI : QueryImpl (publicHashSpec core₀) Id)
    (tbl : SecIdx → Bytes 16) : QueryImpl (Lazy.OSpec P0 (hS St Blk)) ProbComp :=
  fun t => simulateQ (instImpl₀ g) (Lazy.tblImpl (gspec := hS St Blk) hI tbl t)

theorem φg_port (g : CF St Blk) (hI : QueryImpl (publicHashSpec core₀) Id)
    (tbl : SecIdx → Bytes 16) (q : St × Blk) : φg g hI tbl (.inr (.inl q)) = pure (g q) := by
  have h : φg g hI tbl (.inr (.inl q)) = simulateQ (instImpl₀ g) (cq q) := by
    simp [φg, Lazy.tblImpl, cq]
  rw [h, cq_inst]

/-! ## The second phases in the ideal model -/

section Dist

variable (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))

/-- **Second phase of the ideal-model SM-UD adversary.** -/
noncomputable def udDist (st : Open.RState Link.vp P0) (pk : Bytes 16) :
    OracleComp (unifSpec + hS St Blk) Bool :=
  simulateQ (chainImpl st.1.1) (wUdP (optRand₀ oR) (mainP S) st.1.2.1 st.2 st.1.2.2 pk)

/-- **Second phase of the ideal-model SM-PRE adversary.** -/
noncomputable def preInv (st : Open.RState Link.vp P0) (pk : Bytes 16) :
    OracleComp (unifSpec + hS St Blk) (ℕ × Bytes 16) :=
  simulateQ (chainImpl st.1.1) (wPreP (optRand₀ oR) (mainP S) st.1.2.1 st.2 st.1.2.2 pk)

/-- **Second phase of the ideal-model SM-TCR adversary.** -/
noncomputable def tcrForge (st : Open.RState Link.vp P0) (pk : Bytes 16) :
    OracleComp (unifSpec + hS St Blk) (ℕ × Bytes 16) :=
  simulateQ (chainImpl st.1.1) (wTcrP (optRand₀ oR) (mainP S) st.1.2.1 st.2 st.1.2.2 pk)

variable (pkSeedDist : ProbComp (Bytes 16)) (g : CF St Blk)

/-- Generic second-phase identity: chain substitution, fusion, the open-program equation. -/
theorem phase2_inst {β : Type} (tbl : SecIdx → Bytes 16)
    (P : OracleComp (Lazy.OSpec P0 (hS St Blk)) β)
    (Q : OracleComp (Lazy.OSpec (R₀ (thG g) (hmG g)) (hS St Blk)) β) (X : ProbComp β)
    (hfus : simulateQ (φg g (implTH (thG g) (hmG g)) tbl) P =
      simulateQ (φg g (implTH (thG g) (hmG g)) tbl) Q)
    (hopen : (liftM X : OracleComp (unifSpec + hS St Blk) β) =
      simulateQ (Lazy.tblImpl (gspec := hS St Blk) (PublicHash.impl (R₀ (thG g) (hmG g))) tbl)
        Q) :
    simulateQ (instImpl₀ g) (simulateQ (chainImpl tbl) P) = X := by
  refine (chainImpl_inst g (implTH (thG g) (hmG g)) (hashC_inst g) tbl P).trans ?_
  refine (simulateQ_comp _ _ P).trans ?_
  refine hfus.trans ?_
  rw [← instImpl₀_liftM g X, hopen, impl_R₀]
  exact (simulateQ_comp (instImpl₀ g)
    (Lazy.tblImpl (gspec := hS St Blk) (implTH (thG g) (hmG g)) tbl) Q).symm

theorem udDist_inst (st : Open.RState Link.vp P0) (pk : Bytes 16) :
    simulateQ (instImpl₀ g) (udDist S oR st pk) =
      (rUd pkSeedDist (Lazy.bWotsS (B₀ S oR pkSeedDist g))).distinguish st pk := by
  obtain ⟨⟨tbl, hist, root⟩, hist2⟩ := st
  refine phase2_inst g tbl _ (wotsUdOpenAll (B₀ S oR pkSeedDist g) hist hist2 root pk) _ ?_
    (wotsUd_phase2_open_eq (B₀ S oR pkSeedDist g) tbl hist hist2 root pk)
  have h := wUdP_fusion (prims := R₀ (thG g) (hmG g)) (optRand₀ oR) pkSeedDist
    (φg g (implTH (thG g) (hmG g)) tbl) g (φg_port g _ tbl) (mainP S) hist hist2 root pk
  rw [instForger_eq] at h
  kexact h

theorem preInv_inst (st : Open.RState Link.vp P0) (pk : Bytes 16) :
    simulateQ (instImpl₀ g) (preInv S oR st pk) =
      (rPre pkSeedDist (Lazy.bWotsS (B₀ S oR pkSeedDist g))).invert st pk := by
  obtain ⟨⟨tbl, hist, root⟩, hist2⟩ := st
  refine phase2_inst g tbl _ (wotsPreOpenAll (B₀ S oR pkSeedDist g) hist hist2 root pk) _ ?_
    (wotsPre_phase2_open_eq (B₀ S oR pkSeedDist g) tbl hist hist2 root pk)
  have h := wPreP_fusion (prims := R₀ (thG g) (hmG g)) (optRand₀ oR) pkSeedDist
    (φg g (implTH (thG g) (hmG g)) tbl) g (φg_port g _ tbl) (mainP S) hist hist2 root pk
  rw [instForger_eq] at h
  kexact h

theorem tcrForge_inst (st : Open.RState Link.vp P0) (pk : Bytes 16) :
    simulateQ (instImpl₀ g) (tcrForge S oR st pk) =
      (rTcrT (vp := Link.vp) pkSeedDist (Lazy.bWotsS (B₀ S oR pkSeedDist g))).forge st pk := by
  obtain ⟨⟨tbl, hist, root⟩, hist2⟩ := st
  refine phase2_inst g tbl _ (wotsTcrOpenAll (B₀ S oR pkSeedDist g) hist hist2 root pk) _ ?_
    (wotsTcrT_phase2_open_eq (B₀ S oR pkSeedDist g) tbl hist hist2 root pk)
  have h := wTcrP_fusion (prims := R₀ (thG g) (hmG g)) (optRand₀ oR) pkSeedDist
    (φg g (implTH (thG g) (hmG g)) tbl) g (φg_port g _ tbl) (mainP S) hist hist2 root pk
  rw [instForger_eq] at h
  kexact h

end Dist

/-! ## Compression queries of a chain-substituted open program -/

section ChainCount

/-- A `Thash` query of an open program. -/
def isThIdx {ι P K Y : Type} : ℕ ⊕ (ι ⊕ (SecIdx ⊕ PublicHashQuery P K Y)) → Bool
  | .inr (.inr (.inr (.thash _ _ _))) => true
  | _ => false

variable (B ℓ : ℕ)

theorem chainImpl_step (tbl : SecIdx → Bytes 16) (t : (PSpecC SecIdx (Bytes 16)).Domain)
    (ht : ¬ isBadIdx B ℓ t = true) :
    IsQueryBoundP (chainImpl tbl t) (fun i => i.isRight = true)
      ((if Lazy.kind t = .game then 1 else 0) + (if isThIdx t = true then thashCost B else 0) +
        (if isHmsgIdx t = true then hmsgCost ℓ else 0)) := by
  rcases t with n | q | d | (⟨pk, a, xs⟩ | ⟨R, pk, root, M⟩)
  · exact (isQueryBoundP_query_iff _ _ _).2 fun h => by simp at h
  · show IsQueryBoundP (cq q) (fun i => i.isRight = true) _
    exact (cq_bound q).mono (by simp [Lazy.kind, isThIdx, isHmsgIdx])
  · exact (isQueryBoundP_pure _ _ _).mono (Nat.zero_le _)
  · have hx : xs.length ≤ B := by simpa [isBadIdx] using ht
    show IsQueryBoundP (thashC pk a xs) (fun i => i.isRight = true) _
    exact (thashC_bound pk a xs).mono ((thashCost_mono hx).trans
      (by simp [Lazy.kind, isThIdx, isHmsgIdx]))
  · have hx : M.length ≤ ℓ := by simpa [isBadIdx] using ht
    show IsQueryBoundP (hmsgC R pk root M) (fun i => i.isRight = true) _
    exact (hmsgC_bound R pk root M).mono ((hmsgCost_mono hx).trans
      (by simp [Lazy.kind, isThIdx, isHmsgIdx]))

/-- **Hash query → compression chain, with the count**: compression queries
`≤ port·1 + hash·thashCost B + hmsg·hmsgCost ℓ`. -/
theorem chain_count (tbl : SecIdx → Bytes 16) {α : Type}
    (oa : OracleComp (PSpecC SecIdx (Bytes 16)) α) (a H M : ℕ)
    (h0 : IsQueryBoundP oa (fun t => isBadIdx B ℓ t = true) 0)
    (h1 : IsQueryBoundP oa (fun t => Lazy.kind t = .game) a)
    (h2 : IsQueryBoundP oa (fun t => Lazy.kind t = .hash) H)
    (h3 : IsQueryBoundP oa (fun t => isHmsgIdx t = true) M) :
    IsQueryBoundP (simulateQ (chainImpl tbl) oa) (fun i => i.isRight = true)
      (a * 1 + H * thashCost B + M * hmsgCost ℓ) := by
  have h2' : IsQueryBoundP oa (fun t => isThIdx t = true) H :=
    IsQueryBoundP.of_imp (fun t ht => by
      rcases t with n | q | d | (⟨pk, a, xs⟩ | ⟨R, pk, root, M⟩) <;>
        simp_all [isThIdx, Lazy.kind]) h2
  exact qb_simulateQ_classes (p₀ := fun t => isBadIdx B ℓ t = true)
    (p₁ := fun t => Lazy.kind t = .game) (p₂ := fun t => isThIdx t = true)
    (p₃ := fun t => isHmsgIdx t = true) 1 (thashCost B) (hmsgCost ℓ)
    (fun t ht => chainImpl_step B ℓ tbl t ht) h0 h1 h2' h3

end ChainCount

/-! ## Second-phase counts -/

section Bounds

/-- Every SLH-DSA hash call is on at most `len` values. -/
theorem okLen_le (xs : List core₀.Y) (h : OkLen Link.vp xs) : xs.length ≤ Link.vp.params.len := by
  have h1 : 2 ≤ Link.vp.params.len ∧ Link.vp.params.k ≤ Link.vp.params.len := by decide
  rcases h with h | h | h | h <;> omega

variable (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) {qf qs ℓ : ℕ}
  (hqf : ∀ pk, IsQueryBoundP (S.main pk)
    (fun i => Ideal.Realize.isPortQ (S := List Byte) i = true) qf)
  (hqs : ∀ pk, IsQueryBoundP (S.main pk)
    (fun i => Ideal.Realize.isSignQ (S := List Byte) i = true) qs)
  (hlong : ∀ pk, IsQueryBoundP (S.main pk)
    (fun i => Ideal.Realize.isLongQ (S := List Byte) ℓ i = true) 0)
  (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ)

include hqf in
theorem mainP_port (pk : PublicKeyCore core₀) :
    IsQueryBoundP (mainP S pk)
      (fun i => isPortQ (S := GeneralScheme.SignatureCore Link.vp core₀) i = true) qf :=
  typedP_bound (prims := P0) codec₀ (isPortQ (S := List Byte))
    (isPortQ (S := GeneralScheme.SignatureCore Link.vp core₀)) (fun _ _ _ => ⟨rfl, rfl, rfl⟩) S.main pk qf (hqf _)

include hqs in
theorem mainP_sign (pk : PublicKeyCore core₀) :
    IsQueryBoundP (mainP S pk)
      (fun i => isSignQ (S := GeneralScheme.SignatureCore Link.vp core₀) i = true) qs :=
  typedP_bound (prims := P0) codec₀ (isSignQ (S := List Byte))
    (isSignQ (S := GeneralScheme.SignatureCore Link.vp core₀)) (fun _ _ _ => ⟨rfl, rfl, rfl⟩) S.main pk qs (hqs _)

include hlong in
theorem mainP_long (pk : PublicKeyCore core₀) :
    IsQueryBoundP (mainP S pk)
      (fun i => isLongQ (S := GeneralScheme.SignatureCore Link.vp core₀) ℓ i = true) 0 :=
  typedP_bound (prims := P0) codec₀ (isLongQ (S := List Byte) ℓ)
    (isLongQ (S := GeneralScheme.SignatureCore Link.vp core₀) ℓ) (fun _ _ _ => ⟨rfl, rfl, rfl⟩) S.main pk 0 (hlong _)

include hout in
theorem mainP_out (pk : PublicKeyCore core₀) :
    ∀ z ∈ support (mainP S pk), z.1.length ≤ ℓ := by
  intro z hz
  obtain ⟨out, hout', he⟩ := typedP_out (prims := P0) codec₀ S.main pk z hz
  rw [he]
  exact hout _ out hout'

/-- Hash queries of the SM-UD second phase (`Reduction.Open.wotsUd_phase2_open_hashes`). -/
abbrev udH (qs : ℕ) : ℕ :=
  qs * wotsSignHistHashes Link.vp + (wotsAnswerHashes Link.vp + wotsWinHashes Link.vp)
/-- Hash queries of the SM-PRE second phase. -/
abbrev preH (qs : ℕ) : ℕ :=
  qs * wotsSignHistHashes Link.vp + (wotsAnswerHashes Link.vp + wotsPreHashes Link.vp)
/-- Hash queries of the SM-TCR second phase. -/
abbrev tcrH (qs : ℕ) : ℕ :=
  qs * wotsSignHistHashes Link.vp + (wotsAnswerHashes Link.vp + wotsTcrHashes Link.vp)

/-- Compression queries of a second phase with `H` hash queries. -/
abbrev q2 (qf qs ℓ H : ℕ) : ℕ :=
  qf * 1 + H * thashCost Link.vp.params.len + (qs + 2) * hmsgCost ℓ

include hqf hqs hlong hout in
theorem udDist_bound (st : Open.RState Link.vp P0) (pk : Bytes 16) :
    IsQueryBoundP (udDist S oR st pk) (fun i => i.isRight = true) (q2 qf qs ℓ (udH qs)) :=
  chain_count _ ℓ _ _ _ _ _
    (wUdP_bad (prims := P0) _ _ _ _ _ _ Link.vp.params.len ℓ okLen_le (mainP_long S hlong _)
      (mainP_out S hout _))
    (wUdP_port (prims := P0) _ _ _ _ _ _ (mainP_port S hqf _))
    (wUdP_hashes (prims := P0) _ _ _ _ _ _ (mainP_sign S hqs _))
    (wUdP_hmsg (prims := P0) _ _ _ _ _ _ (mainP_sign S hqs _))

include hqf hqs hlong hout in
theorem preInv_bound (st : Open.RState Link.vp P0) (pk : Bytes 16) :
    IsQueryBoundP (preInv S oR st pk) (fun i => i.isRight = true) (q2 qf qs ℓ (preH qs)) :=
  chain_count _ ℓ _ _ _ _ _
    (wPreP_bad (prims := P0) _ _ _ _ _ _ Link.vp.params.len ℓ okLen_le (mainP_long S hlong _)
      (mainP_out S hout _))
    (wPreP_port (prims := P0) _ _ _ _ _ _ (mainP_port S hqf _))
    (wPreP_hashes (prims := P0) _ _ _ _ _ _ (mainP_sign S hqs _))
    (wPreP_hmsg (prims := P0) _ _ _ _ _ _ (mainP_sign S hqs _))

include hqf hqs hlong hout in
theorem tcrForge_bound (st : Open.RState Link.vp P0) (pk : Bytes 16) :
    IsQueryBoundP (tcrForge S oR st pk) (fun i => i.isRight = true) (q2 qf qs ℓ (tcrH qs)) :=
  chain_count _ ℓ _ _ _ _ _
    (wTcrP_bad (prims := P0) _ _ _ _ _ _ Link.vp.params.len ℓ okLen_le (mainP_long S hlong _)
      (mainP_out S hout _))
    (wTcrP_port (prims := P0) _ _ _ _ _ _ (mainP_port S hqf _))
    (wTcrP_hashes (prims := P0) _ _ _ _ _ _ (mainP_sign S hqs _))
    (wTcrP_hmsg (prims := P0) _ _ _ _ _ _ (mainP_sign S hqs _))

end Bounds

end Ideal.Realize.Wots

#print axioms Ideal.Realize.Wots.stepUd
#print axioms Ideal.Realize.Wots.udDist_inst
#print axioms Ideal.Realize.Wots.preInv_inst
#print axioms Ideal.Realize.Wots.tcrForge_inst
#print axioms Ideal.Realize.Wots.chain_count
#print axioms Ideal.Realize.Wots.udDist_bound
#print axioms Ideal.Realize.Wots.preInv_bound
#print axioms Ideal.Realize.Wots.tcrForge_bound
