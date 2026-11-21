import Ideal.Realize.WotsRealize

/-!
# The six WOTS-chain realisers and their parameter bounds

* `realizesUd`, `realizesPre`, `realizesWotsTcr` (SUF: the families at `S.typedS (optRandU oR)`)
  and `realizesUdE`, `realizesPreE`, `realizesWotsTcrE` (EUF: at `S.typedE (optRandU oR)`), with
  parameters `pU qf qs ℓ`, `pP qf qs ℓ`, `pW qf qs ℓ`, under the four forger hypotheses
  (`qf` compression queries, `qs` signing queries, signed and forged messages of at most `ℓ`
  bytes).
* `pU_le`, `pP_le`, `pW_le`: `P5.Le` at `QcW qf qs ℓ = qf + 11·(121857·qs + 146514) +
  (qs + 2)·((ℓ + 56)/64 + 3)` and `NW = 1062560399506556770327551 (≈ 2^79.81)`.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security TweakableHash

namespace Ideal.Realize.Wots

open Reduction Reduction.Open Reduction.Lazy Reduction.Resources2 Ideal.Realize Ideal.Transport

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.constructorNameAsVariable false

/-! ## Embedded first phases: generic counts -/

section GenF

variable {PkSeed Tweak M Y ι : Type} {α : Type}

theorem genP_q1 (F : THFam St Blk PkSeed Tweak M Y ι)
    (oa : OracleComp (unifSpec + (SM_DT_PRE_challengeSpec Tweak Y + F.collS)) α) :
    IsQueryBoundP (simulateQ (embImpl (X := SM_DT_PRE_challengeSpec Tweak Y + F.collS)) oa)
      (fun i => F.pIsH i = true) 0 :=
  emb_noH _ (fun t => by rcases t with n | t <;> simp [embIdx, THFam.pIsH]) oa

theorem genP_chal (F : THFam St Blk PkSeed Tweak M Y ι)
    (oa : OracleComp (unifSpec + (SM_DT_PRE_challengeSpec Tweak Y + F.collS)) α) (n : ℕ)
    (h : IsQueryBoundP oa isChalI n) :
    IsQueryBoundP (simulateQ (embImpl (X := SM_DT_PRE_challengeSpec Tweak Y + F.collS)) oa)
      (fun i => F.pIsChal i = true) n :=
  emb_bound _ oa n (IsQueryBoundP.of_imp (fun t ht => by
    rcases t with n | t | t <;> simp_all [embIdx, isChalI, THFam.pIsChal]) h)

theorem genP_coll (F : THFam St Blk PkSeed Tweak M Y ι)
    (oa : OracleComp (unifSpec + (SM_DT_PRE_challengeSpec Tweak Y + F.collS)) α) (n : ℕ)
    (h : IsQueryBoundP oa isColl n) :
    IsQueryBoundP (simulateQ (embImpl (X := SM_DT_PRE_challengeSpec Tweak Y + F.collS)) oa)
      (fun i => F.pIsColl i = true) n :=
  emb_bound _ oa n (IsQueryBoundP.of_imp (fun t ht => by
    rcases t with n | t | t <;> simp_all [embIdx, isColl, THFam.pIsColl]) h)

theorem genT_q1 (F : THFam St Blk PkSeed Tweak M Y ι)
    (oa : OracleComp (unifSpec + (SM_DT_TCR_challengeSpec Tweak M Y + F.collS)) α) :
    IsQueryBoundP (simulateQ (embImpl (X := SM_DT_TCR_challengeSpec Tweak M Y + F.collS)) oa)
      (fun i => F.isH i = true) 0 :=
  emb_noH _ (fun t => by rcases t with n | t <;> simp [embIdx, THFam.isH]) oa

theorem genT_chal (F : THFam St Blk PkSeed Tweak M Y ι)
    (oa : OracleComp (unifSpec + (SM_DT_TCR_challengeSpec Tweak M Y + F.collS)) α) (n : ℕ)
    (h : IsQueryBoundP oa isChalI n) :
    IsQueryBoundP (simulateQ (embImpl (X := SM_DT_TCR_challengeSpec Tweak M Y + F.collS)) oa)
      (fun i => F.isChal i = true) n :=
  emb_bound _ oa n (IsQueryBoundP.of_imp (fun t ht => by
    rcases t with n | t | t <;> simp_all [embIdx, isChalI, THFam.isChal]) h)

theorem genT_coll (F : THFam St Blk PkSeed Tweak M Y ι)
    (oa : OracleComp (unifSpec + (SM_DT_TCR_challengeSpec Tweak M Y + F.collS)) α) (n : ℕ)
    (h : IsQueryBoundP oa isColl n) :
    IsQueryBoundP (simulateQ (embImpl (X := SM_DT_TCR_challengeSpec Tweak M Y + F.collS)) oa)
      (fun i => F.isColl i = true) n :=
  emb_bound _ oa n (IsQueryBoundP.of_imp (fun t ht => by
    rcases t with n | t | t <;> simp_all [embIdx, isColl, THFam.isColl]) h)

end GenF

/-- A collection query with at most `Lw` blocks after the first (or no collection query). -/
def lenOk {T : Type} : ℕ ⊕ ((St × Blk) ⊕ (T ⊕ ((_ : Unit) × Bytes 22 × List (Bytes 16)))) → Prop
  | .inr (.inr (.inr q)) => (tblocks q.2.1 q.2.2).2.length ≤ Lw
  | _ => True

noncomputable instance {T : Type} : DecidablePred (lenOk (T := T)) :=
  fun _ => Classical.propDecidable _

/-- Collection lengths of an embedded first phase whose collection queries are SLH-DSA hash
calls. -/
theorem emb_okLen {T : Type} {X : OracleSpec (T ⊕ ((_ : Unit) × Bytes 22 × List (Bytes 16)))}
    {α : Type} (oa : OracleComp (unifSpec + X) α)
    (h : @IsQueryBoundP _ (unifSpec + X) _ oa (badG (vp := Link.vp) (prims := P0) (T := T))
      instDecidablePredSumNatSigmaUnitProdAdrsKeyListYBadG 0) :
    AllQueriesSatisfy (simulateQ (embImpl (X := X)) oa) (lenOk (T := T)) := by
  refine (isQueryBoundP_zero_iff _ _).1 (emb_bound _ oa 0 ?_)
  refine @IsQueryBoundP.of_imp _ _ _ _ (fun t => ¬ lenOk (embIdx t))
    (badG (vp := Link.vp) (prims := P0) (T := T)) _
    instDecidablePredSumNatSigmaUnitProdAdrsKeyListYBadG 0 (fun t ht => ?_) h
  rcases t with n | t | q
  · exact (ht trivial).elim
  · exact (ht trivial).elim
  · intro hb
    exact ht (tblocks_okLen _ _ hb)

/-! ## The challenge / collection counts, as numerals

(The realisers' parameters are numerals: the kernel would otherwise try to evaluate
`wotsQc Link.vp` or `(wotsInsts Link.vp).length` when comparing them.) -/

/-- Challenge queries of the SM-UD and SM-PRE first phases: `#inst · len`. -/
theorem chU_eq : (wotsInsts Link.vp).length * (Link.vp.params.len * 1) = 323449759100660631040 := by
  rw [Resources.wotsInsts_length_128s]
  have : Link.vp.params.len = 35 := by decide
  rw [this]

/-- Collection queries of the SM-UD and SM-PRE first phases: `wotsQc + #inst · len · (w-1)`. -/
theorem collU_eq :
    wotsQc Link.vp + (wotsInsts Link.vp).length * (Link.vp.params.len * (Link.vp.params.w - 1)) =
      1062560399506556770327551 := udCollB_128s

/-- Challenge queries of the SM-TCR first phase: `#inst · len · (w-1)`. -/
theorem chW_eq :
    (wotsInsts Link.vp).length * (Link.vp.params.len * (Link.vp.params.w - 1)) =
      4851746386509909465600 := by
  rw [Resources.wotsInsts_length_128s]
  have h1 : Link.vp.params.len = 35 := by decide
  have h2 : Link.vp.params.w = 16 := by decide
  rw [h1, h2]

/-- Collection queries of the SM-TCR first phase: `wotsQc + #inst · len`. -/
theorem collW_eq :
    wotsQc Link.vp + (wotsInsts Link.vp).length * (Link.vp.params.len * 1) =
      1058032102879147521492991 := by
  rw [Nat.mul_one]; exact tcrCollB_128s

/-! ## SM-UD -/

section Ud

variable (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
  (pkSeedDist : ProbComp (Bytes 16))

theorem udAdv_q1 : (udAdv S oR pkSeedDist).PickBound 0 :=
  genP_q1 (FWotsPre128 pkSeedDist) _

theorem udAdv_chal : (udAdv S oR pkSeedDist).ChalBound 323449759100660631040 :=
  (genP_chal (FWotsPre128 pkSeedDist) _ _ (rUd_pick_chal pkSeedDist (dF oR pkSeedDist))).mono
    (le_of_eq chU_eq)

theorem udAdv_coll : (udAdv S oR pkSeedDist).CollBound 1062560399506556770327551 :=
  (genP_coll (FWotsPre128 pkSeedDist) _ _ (rUd_pick_coll pkSeedDist (dF oR pkSeedDist))).mono
    (le_of_eq collU_eq)

set_option maxHeartbeats 2000000 in
theorem udAdv_len : (udAdv S oR pkSeedDist).CollLen Lw := by
  kexact emb_okLen (X := SM_DT_UD_challengeSpec (Bytes 22) (Bytes 16) + collSpecC (Bytes 22) (Bytes 16))
    _ (rUd_pick_len (vp := Link.vp) (prims := P0) pkSeedDist (dF oR pkSeedDist))

/-- **Parameters of the SM-UD realiser**: no first-phase compression query; challenge and
collection counts of `rUd_pick_chal`, `rUd_pick_coll`; continuation length `Lw`; second phase
`q2 qf qs ℓ (udH qs)` (forger's queries + hash queries × chain cost). -/
def pU (qf qs ℓ : ℕ) : P5 :=
  ⟨0, 323449759100660631040, 1062560399506556770327551, Lw, q2 qf qs ℓ (udH qs)⟩

variable {S oR pkSeedDist} {qf qs ℓ : ℕ}
  (hqf : ∀ pk, IsQueryBoundP (S.main pk)
    (fun i => Ideal.Realize.isPortQ (S := List Byte) i = true) qf)
  (hqs : ∀ pk, IsQueryBoundP (S.main pk)
    (fun i => Ideal.Realize.isSignQ (S := List Byte) i = true) qs)
  (hlong : ∀ pk, IsQueryBoundP (S.main pk)
    (fun i => Ideal.Realize.isLongQ (S := List Byte) ℓ i = true) 0)
  (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ)

include hqf hqs hlong hout in
theorem udAdv_q2 : (udAdv S oR pkSeedDist).DistBound (q2 qf qs ℓ (udH qs)) :=
  fun st pk => udDist_bound S oR hqf hqs hlong hout st pk

include hqf hqs hlong hout in
/-- **The SM-UD realiser (SUF).** -/
noncomputable def realizesUd :
    RealizesUd pkSeedDist
      (fun g => Reduction.rUd pkSeedDist
        (Reduction.Lazy.bWotsS (S.typedS (optRandU oR) pkSeedDist g))) (pU qf qs ℓ) :=
  RealizesUd.ofEq (udAdv S oR pkSeedDist) (udAdv_inst S oR pkSeedDist)
    (udAdv_q1 S oR pkSeedDist) (udAdv_chal S oR pkSeedDist) (udAdv_coll S oR pkSeedDist)
    (udAdv_len S oR pkSeedDist) (udAdv_q2 hqf hqs hlong hout)

include hqf hqs hlong hout in
/-- **The SM-UD realiser (EUF).** -/
noncomputable def realizesUdE :
    RealizesUd pkSeedDist
      (fun g => Reduction.rUd pkSeedDist
        (Reduction.Lazy.bWotsS (S.typedE (optRandU oR) pkSeedDist g))) (pU qf qs ℓ) :=
  realizesUd hqf hqs hlong hout

end Ud

/-! ## The irreducible first phases: counts -/

section P1

variable (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) (pkSeedDist : ProbComp (Bytes 16))

theorem preP1_chal : IsQueryBoundP (preP1 oR pkSeedDist) isChalI
    ((wotsInsts Link.vp).length * (Link.vp.params.len * 1)) := by
  unfold preP1; exact preChooseI_chal _ _

theorem preP1_coll : IsQueryBoundP (preP1 oR pkSeedDist) isColl
    (wotsQc Link.vp + (wotsInsts Link.vp).length * (Link.vp.params.len * (Link.vp.params.w - 1))) := by
  unfold preP1; exact preChooseI_coll _ _

theorem preP1_len : @IsQueryBoundP _ (unifSpec + (SM_DT_PRE_challengeSpec (Bytes 22) (Bytes 16) +
      collSpecC (Bytes 22) (Bytes 16))) _ (preP1 oR pkSeedDist)
    (badG (vp := Link.vp) (prims := P0) (T := P0.AdrsKey))
    instDecidablePredSumNatSigmaUnitProdAdrsKeyListYBadG 0 := by
  unfold preP1; exact preChooseI_len _ _

theorem tcrP1_chal : IsQueryBoundP (tcrP1 oR pkSeedDist) isChalI
    ((wotsInsts Link.vp).length * (Link.vp.params.len * (Link.vp.params.w - 1))) := by
  unfold tcrP1; exact tcrChooseI_chal _ _

theorem tcrP1_coll : IsQueryBoundP (tcrP1 oR pkSeedDist) isColl
    (wotsQc Link.vp + (wotsInsts Link.vp).length * (Link.vp.params.len * 1)) := by
  unfold tcrP1; exact tcrChooseI_coll _ _

theorem tcrP1_len : @IsQueryBoundP _ (unifSpec + (SM_DT_TCR_challengeSpec (Bytes 22) (Bytes 16) (Bytes 16) +
      collSpecC (Bytes 22) (Bytes 16))) _ (tcrP1 oR pkSeedDist)
    (badG (vp := Link.vp) (prims := P0) (T := P0.AdrsKey × P0.Y))
    instDecidablePredSumNatSigmaUnitProdAdrsKeyListYBadG 0 := by
  unfold tcrP1; exact tcrChooseI_len _ _

end P1

/-! ## SM-PRE -/

section Pre

variable (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
  (pkSeedDist : ProbComp (Bytes 16))

theorem preAdv_q1 : (preAdv S oR pkSeedDist).ChooseBound 0 :=
  genP_q1 (FWotsPre128 pkSeedDist) _

theorem preAdv_chal : (preAdv S oR pkSeedDist).ChalBound 323449759100660631040 :=
  (genP_chal (FWotsPre128 pkSeedDist) _ _ (preP1_chal oR pkSeedDist)).mono
    (le_of_eq chU_eq)

theorem preAdv_coll : (preAdv S oR pkSeedDist).CollBound 1062560399506556770327551 :=
  (genP_coll (FWotsPre128 pkSeedDist) _ _ (preP1_coll oR pkSeedDist)).mono
    (le_of_eq collU_eq)

set_option maxHeartbeats 2000000 in
theorem preAdv_len : (preAdv S oR pkSeedDist).CollLen Lw := by
  kexact emb_okLen (X := SM_DT_PRE_challengeSpec (Bytes 22) (Bytes 16) +
      collSpecC (Bytes 22) (Bytes 16))
    _ (preP1_len oR pkSeedDist)

/-- **Parameters of the SM-PRE realiser.** -/
def pP (qf qs ℓ : ℕ) : P5 :=
  ⟨0, 323449759100660631040, 1062560399506556770327551, Lw, q2 qf qs ℓ (preH qs)⟩

variable {S oR pkSeedDist} {qf qs ℓ : ℕ}
  (hqf : ∀ pk, IsQueryBoundP (S.main pk)
    (fun i => Ideal.Realize.isPortQ (S := List Byte) i = true) qf)
  (hqs : ∀ pk, IsQueryBoundP (S.main pk)
    (fun i => Ideal.Realize.isSignQ (S := List Byte) i = true) qs)
  (hlong : ∀ pk, IsQueryBoundP (S.main pk)
    (fun i => Ideal.Realize.isLongQ (S := List Byte) ℓ i = true) 0)
  (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ)

include hqf hqs hlong hout in
theorem preAdv_q2 : (preAdv S oR pkSeedDist).InvertBound (q2 qf qs ℓ (preH qs)) :=
  fun st pk => preInv_bound S oR hqf hqs hlong hout st pk

include hqf hqs hlong hout in
/-- **The SM-PRE realiser (SUF).** -/
noncomputable def realizesPre :
    RealizesPre pkSeedDist
      (fun g => Reduction.rPre pkSeedDist
        (Reduction.Lazy.bWotsS (S.typedS (optRandU oR) pkSeedDist g))) (pP qf qs ℓ) :=
  ⟨preAdv S oR pkSeedDist,
    fun g => by kexact congrArg (fun x => 𝒟[SM_DT_PRE_Experiment x]) (preAdv_inst S oR pkSeedDist g),
    preAdv_q1 S oR pkSeedDist, preAdv_chal S oR pkSeedDist, preAdv_coll S oR pkSeedDist,
    preAdv_len S oR pkSeedDist, preAdv_q2 hqf hqs hlong hout⟩

include hqf hqs hlong hout in
/-- **The SM-PRE realiser (EUF).** -/
noncomputable def realizesPreE :
    RealizesPre pkSeedDist
      (fun g => Reduction.rPre pkSeedDist
        (Reduction.Lazy.bWotsS (S.typedE (optRandU oR) pkSeedDist g))) (pP qf qs ℓ) :=
  realizesPre hqf hqs hlong hout

end Pre

/-! ## SM-TCR on `F` (tight cap) -/

section Tcr

variable (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
  (pkSeedDist : ProbComp (Bytes 16))

theorem tcrAdv_q1 : (tcrAdv S oR pkSeedDist).ChooseBound 0 :=
  genT_q1 (FWots128T pkSeedDist) _

theorem tcrAdv_chal : (tcrAdv S oR pkSeedDist).ChalBound 4851746386509909465600 :=
  (genT_chal (FWots128T pkSeedDist) _ _ (tcrP1_chal oR pkSeedDist)).mono
    (le_of_eq chW_eq)

theorem tcrAdv_coll : (tcrAdv S oR pkSeedDist).CollBound 1058032102879147521492991 :=
  (genT_coll (FWots128T pkSeedDist) _ _ (tcrP1_coll oR pkSeedDist)).mono
    (le_of_eq collW_eq)

set_option maxHeartbeats 2000000 in
theorem tcrAdv_len : (tcrAdv S oR pkSeedDist).CollLen Lw := by
  kexact emb_okLen (X := SM_DT_TCR_challengeSpec (Bytes 22) (Bytes 16) (Bytes 16) +
      collSpecC (Bytes 22) (Bytes 16))
    _ (tcrP1_len oR pkSeedDist)

/-- **Parameters of the SM-TCR realiser.** -/
def pW (qf qs ℓ : ℕ) : P5 :=
  ⟨0, 4851746386509909465600, 1058032102879147521492991, Lw, q2 qf qs ℓ (tcrH qs)⟩

variable {S oR pkSeedDist} {qf qs ℓ : ℕ}
  (hqf : ∀ pk, IsQueryBoundP (S.main pk)
    (fun i => Ideal.Realize.isPortQ (S := List Byte) i = true) qf)
  (hqs : ∀ pk, IsQueryBoundP (S.main pk)
    (fun i => Ideal.Realize.isSignQ (S := List Byte) i = true) qs)
  (hlong : ∀ pk, IsQueryBoundP (S.main pk)
    (fun i => Ideal.Realize.isLongQ (S := List Byte) ℓ i = true) 0)
  (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ)

include hqf hqs hlong hout in
theorem tcrAdv_q2 : (tcrAdv S oR pkSeedDist).ForgeBound (q2 qf qs ℓ (tcrH qs)) :=
  fun st pk => tcrForge_bound S oR hqf hqs hlong hout st pk

include hqf hqs hlong hout in
/-- **The SM-TCR realiser on `F` (SUF).** -/
noncomputable def realizesWotsTcr :
    RealizesWotsTcr pkSeedDist
      (fun g => Reduction.rTcrT pkSeedDist
        (Reduction.Lazy.bWotsS (S.typedS (optRandU oR) pkSeedDist g))) (pW qf qs ℓ) :=
  ⟨tcrAdv S oR pkSeedDist,
    fun g => by kexact congrArg (fun x => 𝒟[SM_DT_TCR_Experiment x]) (tcrAdv_inst S oR pkSeedDist g),
    tcrAdv_q1 S oR pkSeedDist, tcrAdv_chal S oR pkSeedDist, tcrAdv_coll S oR pkSeedDist,
    tcrAdv_len S oR pkSeedDist, tcrAdv_q2 hqf hqs hlong hout⟩

include hqf hqs hlong hout in
/-- **The SM-TCR realiser on `F` (EUF).** -/
noncomputable def realizesWotsTcrE :
    RealizesWotsTcr pkSeedDist
      (fun g => Reduction.rTcrT pkSeedDist
        (Reduction.Lazy.bWotsS (S.typedE (optRandU oR) pkSeedDist g))) (pW qf qs ℓ) :=
  realizesWotsTcr hqf hqs hlong hout

end Tcr

/-! ## Bounds in the shape of `P5.Le` -/

/-- Compression-query cap of the three realisers: the forger's `qf` queries; `11` compressions
(`thashCost len`) for each of the `≤ 121857·qs + 146514` hash queries of the SM-TCR second phase
(the largest of the three counts `udH`, `preH`, `tcrH`); `(ℓ + 56)/64 + 3` compressions
(`hmsgCost ℓ`) for each of the `≤ qs + 2` `H_msg` queries. -/
def QcW (qf qs ℓ : ℕ) : ℕ := qf + 11 * (121857 * qs + 146514) + (qs + 2) * ((ℓ + 56) / 64 + 3)

/-- Challenge / collection cap of the three realisers (`≈ 2^79.81`). -/
def NW : ℕ := 1062560399506556770327551

theorem q2_le (qf qs ℓ H : ℕ) (hH : H ≤ 121857 * qs + 146514) : q2 qf qs ℓ H ≤ QcW qf qs ℓ := by
  have h11 : thashCost Link.vp.params.len = 11 := by decide
  unfold q2 QcW hmsgCost
  rw [h11]
  omega

theorem udH_le (qs : ℕ) : udH qs ≤ 121857 * qs + 146514 := by
  unfold udH
  rw [wotsSignHistHashes_128s, wotsAnswerHashes_128s, wotsWinHashes_128s]; omega

theorem preH_le (qs : ℕ) : preH qs ≤ 121857 * qs + 146514 := by
  unfold preH
  rw [wotsSignHistHashes_128s, wotsAnswerHashes_128s, wotsPreHashes_128s]; omega

theorem tcrH_le (qs : ℕ) : tcrH qs ≤ 121857 * qs + 146514 := by
  unfold tcrH
  rw [wotsSignHistHashes_128s, wotsAnswerHashes_128s, wotsTcrHashes_128s]; omega

theorem Lw_le : Lw ≤ 10 := by rw [Lw_eq]; omega

/-- **SM-UD realiser parameters meet the caps** `QcW qf qs ℓ`, `NW`. -/
theorem pU_le (qf qs ℓ : ℕ) : (pU qf qs ℓ).Le (QcW qf qs ℓ) NW :=
  ⟨Nat.zero_le _, by simp [pU, NW], by simp [pU, NW], Lw_le,
    q2_le _ _ _ _ (udH_le qs)⟩

/-- **SM-PRE realiser parameters meet the caps.** -/
theorem pP_le (qf qs ℓ : ℕ) : (pP qf qs ℓ).Le (QcW qf qs ℓ) NW :=
  ⟨Nat.zero_le _, by simp [pP, NW], by simp [pP, NW], Lw_le,
    q2_le _ _ _ _ (preH_le qs)⟩

/-- **SM-TCR realiser parameters meet the caps.** -/
theorem pW_le (qf qs ℓ : ℕ) : (pW qf qs ℓ).Le (QcW qf qs ℓ) NW :=
  ⟨Nat.zero_le _, by simp [pW, NW], by simp [pW, NW], Lw_le,
    q2_le _ _ _ _ (tcrH_le qs)⟩

end Ideal.Realize.Wots
#print axioms Ideal.Realize.Wots.realizesUd
#print axioms Ideal.Realize.Wots.realizesPre
#print axioms Ideal.Realize.Wots.realizesWotsTcr
#print axioms Ideal.Realize.Wots.realizesUdE
#print axioms Ideal.Realize.Wots.realizesPreE
#print axioms Ideal.Realize.Wots.realizesWotsTcrE
#print axioms Ideal.Realize.Wots.pU_le
#print axioms Ideal.Realize.Wots.pP_le
#print axioms Ideal.Realize.Wots.pW_le
