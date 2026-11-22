import Ideal.Realize.WotsRealizers
import Ideal.Realize.ForsL5

/-!
# Per-arity compression counts for the WOTS-chain realisers (`status/TIGHT.md` §4.1, L5)

`QcW` charges each of the `≤ 121857·qs + 146514` hash queries of the three WOTS second phases
`thashCost len = 11` compression queries.  Here every hash query is charged `2` and every long
`Thash` query (more than two values: `T_len`, `T_k`) `9` more:

* `wotsSignFromHistO_long`: one history-based signature makes at most `wotsSignLong Link.vp`
  long `Thash` queries (per hypertree layer the `T_len` leaves of one authentication path);
* `wPhase2P_long` (and the three instances): at most `qs·wotsSignLong + (answer + tail hash
  count)` long `Thash` queries (the one-off answer extraction is bounded by its hash count);
* `chain_countL`: the chain interpretation with `2` per hash query, `9` per long `Thash` query;
* `q2L`, `udAdv_q2L`, …: the second phases make at most
  `q2L qf qs ℓ H Lg = qf + 2·H + (qs+2)·hmsgCost ℓ + 9·Lg` compression queries;
* `realizesUdL`, `realizesPreL`, `realizesWotsTcrL` (and `…E`): the realisers of
  `WotsRealizers.lean` (same adversaries, same experiments) with the parameters `pUL`, `pPL`,
  `pWL`; all at most `QcWL qf qs ℓ = qf + 2·(121857·qs + 146514) + 9·(3577·qs + 146514) +
  (qs+2)·((ℓ+56)/64+3)` (`pUL_le`, …), against `QcW = qf + 11·(121857·qs + 146514) + …`.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security TweakableHash

namespace Ideal.Realize.Wots

open Reduction Reduction.Open Reduction.Lazy Reduction.Resources2 Ideal.Realize Ideal.Transport
open Ideal.Realize.Fors (isLongIdx)

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.constructorNameAsVariable false

section Generic

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]

attribute [local instance] Lazy.openQ

/-- Long `Thash` queries of one history-based signature. -/
def wotsSignLong (vp : ValidatedParams) : ℕ :=
  0 + vp.params.k * (0 + Lazy.authB (0 + 0) 0 vp.params.a) + vp.params.d * Lazy.authB 1 0 vp.params.hp

theorem wotsSignFromHistO_long {ι : Type} {gspec : OracleSpec ι}
    (hist : List (WotsGame.Entry prims)) (pk : PublicKeyCore prims.core) (msg : List Byte)
    (R : prims.Y) :
    IsQueryBoundP (wotsSignFromHistO (gspec := gspec) hist pk msg R)
      (fun t => isLongIdx t = true) (wotsSignLong vp) := by
  have hf : ∀ (a : Adrs) (y : prims.core.Y), IsQueryBoundP (PublicHash.f prims.core pk.pkSeed a y :
      OracleComp (Lazy.OSpec prims gspec) prims.Y) (fun t => isLongIdx t = true) 0 :=
    fun _ _ => (isQueryBoundP_query_iff _ _ _).2 fun h => by simp [isLongIdx] at h
  have htl : ∀ (a : Adrs) (ys : List prims.core.Y),
      IsQueryBoundP (PublicHash.tl prims.core pk.pkSeed a ys :
      OracleComp (Lazy.OSpec prims gspec) prims.Y) (fun t => isLongIdx t = true) 1 :=
    fun _ _ => (isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos
  have hh : ∀ (a : Adrs) (l r : prims.core.Y),
      IsQueryBoundP (PublicHash.h prims.core pk.pkSeed a l r :
      OracleComp (Lazy.OSpec prims gspec) prims.Y) (fun t => isLongIdx t = true) 0 :=
    fun _ _ _ => (isQueryBoundP_query_iff _ _ _).2 fun h => by simp [isLongIdx] at h
  have hs : ∀ a : Adrs, IsQueryBoundP (Lazy.secQ prims gspec a) (fun t => isLongIdx t = true) 0 :=
    fun _ => (isQueryBoundP_query_iff _ _ _).2 fun h => by simp [isLongIdx] at h
  have hm : IsQueryBoundP (PublicHash.hmsg prims.core R pk.pkSeed pk.pkRoot msg :
      OracleComp (Lazy.OSpec prims gspec) _) (fun t => isLongIdx t = true) 0 :=
    (isQueryBoundP_query_iff _ _ _).2 fun h => by simp [isLongIdx] at h
  unfold wotsSignFromHistO
  refine (Lazy.qb_bind _ hm fun digest =>
    Lazy.qb_bind _ (Lazy.qb_forsSign _ prims.core _ _ _ hf hh hs _ _) fun forsSig =>
      Lazy.qb_bind _ (m := 0) (Lazy.qb_ofFnM _ _ _ fun j =>
        Lazy.qb_bind _ (m := 0) (Lazy.qb_authPath _ _ _ _ _ _ _ (fun t => htl _ _)
          (fun z t l r => hh _ l r)) fun path => isQueryBoundP_pure _ _ _)
        fun ht => isQueryBoundP_pure _ _ _).mono ?_
  unfold wotsSignLong
  simp only [Nat.add_zero]
  omega

variable (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
  (mainP : PortForgerProg vp prims)

theorem wForgeP_long (qs : ℕ) (hist : List (WotsGame.Entry prims)) (root : prims.Y)
    (pk : prims.PkSeed)
    (hqs : IsQueryBoundP (mainP ⟨pk, root⟩)
      (fun i => isSignQ (S := GeneralScheme.SignatureCore vp prims.core) i = true) qs) :
    IsQueryBoundP (wForgeP optRand mainP hist root pk) (fun t => isLongIdx t = true)
      (qs * wotsSignLong vp) := by
  have hu : ∀ n : ℕ, ¬ isLongIdx (ι := St × Blk) (P := prims.PkSeed) (K := prims.AdrsKey)
      (Y := prims.Y) (.inl n) = true := by intro n; simp [isLongIdx]
  refine IsQueryBoundP.simulateQ_run_of_step_le hqs (fun t ht s => ?_) (fun t ht s => ?_) []
  · rcases t with n | q | msg
    · simp [isSignQ] at ht
    · simp [isSignQ] at ht
    · exact wSign_step optRand _ hu hist pk root msg _
        (fun R => wotsSignFromHistO_long hist _ msg R) s
  · rcases t with n | q | msg
    · exact wUnif_step optRand _ hu hist pk root n s
    · exact wGame_step optRand _ hist pk root q s 0
        ((isQueryBoundP_query_iff _ _ _).2 fun h => by simp [isLongIdx] at h)
    · exact absurd rfl ht

theorem long_hash {ι : Type} (t : ℕ ⊕ (ι ⊕ (SecIdx ⊕ PublicHashQuery prims.PkSeed prims.AdrsKey prims.Y)))
    (h : isLongIdx t = true) : Lazy.kind t = .hash := by
  rcases t with n | q | d | q
  · simp [isLongIdx] at h
  · simp [isLongIdx] at h
  · simp [isLongIdx] at h
  · rfl

theorem wPhase2P_long (qs c : ℕ) (hist : List (WotsGame.Entry prims)) (root : prims.Y)
    (pk : prims.PkSeed) {β : Type} (tail : ℕ × prims.Y × WotsSig vp.params prims.core →
      OracleComp (Lazy.OSpec prims (hS St Blk)) β)
    (ht : ∀ x, IsQueryBoundP (tail x) (fun t => Lazy.kind t = .hash) c)
    (hqs : IsQueryBoundP (mainP ⟨pk, root⟩)
      (fun i => isSignQ (S := GeneralScheme.SignatureCore vp prims.core) i = true) qs) :
    IsQueryBoundP (wPhase2P optRand mainP hist root pk tail) (fun t => isLongIdx t = true)
      (qs * wotsSignLong vp + (wotsAnswerHashes vp + c)) :=
  wPhase2P_bound optRand mainP _ hist root pk tail _ _ _
    (wForgeP_long optRand mainP qs hist root pk hqs)
    (fun r _ => IsQueryBoundP.of_imp (fun t h => long_hash t h)
      (wotsAnswerOpen_hashes hist _ _ _))
    (fun x => IsQueryBoundP.of_imp (fun t h => long_hash t h) (ht x))

variable {qs : ℕ} (hist hist2 : List (WotsGame.Entry prims)) (root : prims.Y) (pk : prims.PkSeed)
  (hqs : IsQueryBoundP (mainP ⟨pk, root⟩)
    (fun i => isSignQ (S := GeneralScheme.SignatureCore vp prims.core) i = true) qs)

include hqs in
theorem wUdP_long : IsQueryBoundP (wUdP optRand mainP hist hist2 root pk)
    (fun t => isLongIdx t = true)
    (qs * wotsSignLong vp + (wotsAnswerHashes vp + wotsWinHashes vp)) :=
  wPhase2P_long optRand mainP qs _ hist root pk _
    (fun x => (wotsWinO_kindBound .hash pk hist2 x.1 x.2.1 x.2.2).mono
      (by simp [Lazy.ind, wotsWinHashes])) hqs

include hqs in
theorem wPreP_long : IsQueryBoundP (wPreP optRand mainP hist hist2 root pk)
    (fun t => isLongIdx t = true)
    (qs * wotsSignLong vp + (wotsAnswerHashes vp + wotsPreHashes vp)) :=
  wPhase2P_long optRand mainP qs _ hist root pk _
    (fun x => (wotsPreAnswerO_kindBound .hash pk hist2 x.1 x.2.1 x.2.2).mono
      (by simp [Lazy.ind, wotsPreHashes])) hqs

include hqs in
theorem wTcrP_long : IsQueryBoundP (wTcrP optRand mainP hist hist2 root pk)
    (fun t => isLongIdx t = true)
    (qs * wotsSignLong vp + (wotsAnswerHashes vp + wotsTcrHashes vp)) :=
  wPhase2P_long optRand mainP qs _ hist root pk _
    (fun x => (wotsTcrAnswerO_kindBound .hash pk hist2 x.1 x.2.1 x.2.2).mono (by
      have h1 : Lazy.ind Lazy.Kind.hash Lazy.Kind.hash = 1 := rfl
      rw [h1, wotsTcrHashes]
      exact le_of_eq (by ring))) hqs

end Generic

theorem wotsSignLong_128s : wotsSignLong Link.vp = 3577 := by decide

/-! ## Compression queries -/

section ChainCountL

variable (B ℓ : ℕ)

theorem chainImpl_stepL (hB : B ≤ 35) (tbl : SecIdx → Bytes 16)
    (t : (PSpecC SecIdx (Bytes 16)).Domain) (ht : ¬ isBadIdx B ℓ t = true) :
    IsQueryBoundP (chainImpl tbl t) (fun i => i.isRight = true)
      ((if Lazy.kind t = .game then 1 else 0) + (if Lazy.kind t = .hash then 2 else 0) +
        (if isHmsgIdx t = true then hmsgCost ℓ else 0) +
        (if isLongIdx t = true then 9 else 0)) := by
  rcases t with n | q | d | (⟨pk, a, xs⟩ | ⟨R, pk, root, M⟩)
  · exact (isQueryBoundP_query_iff _ _ _).2 fun h => by simp at h
  · show IsQueryBoundP (cq q) (fun i => i.isRight = true) _
    exact (cq_bound q).mono (by simp [Lazy.kind, isHmsgIdx, isLongIdx])
  · exact (isQueryBoundP_pure _ _ _).mono (Nat.zero_le _)
  · have hx : xs.length ≤ B := by simpa [isBadIdx] using ht
    show IsQueryBoundP (thashC pk a xs) (fun i => i.isRight = true) _
    refine (thashC_bound pk a xs).mono ((Fors.thashCost_le_L xs.length (hx.trans hB)).trans ?_)
    by_cases hl : 2 < xs.length
    · simp [Lazy.kind, isHmsgIdx, isLongIdx, hl]
    · simp [Lazy.kind, isHmsgIdx, isLongIdx, hl]
  · have hx : M.length ≤ ℓ := by simpa [isBadIdx] using ht
    show IsQueryBoundP (hmsgC R pk root M) (fun i => i.isRight = true) _
    refine (hmsgC_bound R pk root M).mono ((hmsgCost_mono hx).trans ?_)
    simp [Lazy.kind, isHmsgIdx, isLongIdx]

/-- **Hash query → compression chain, per-arity count.** -/
theorem chain_countL (hB : B ≤ 35) (tbl : SecIdx → Bytes 16) {α : Type}
    (oa : OracleComp (PSpecC SecIdx (Bytes 16)) α) (a H M Lg : ℕ)
    (h0 : IsQueryBoundP oa (fun t => isBadIdx B ℓ t = true) 0)
    (h1 : IsQueryBoundP oa (fun t => Lazy.kind t = .game) a)
    (h2 : IsQueryBoundP oa (fun t => Lazy.kind t = .hash) H)
    (h3 : IsQueryBoundP oa (fun t => isHmsgIdx t = true) M)
    (h4 : IsQueryBoundP oa (fun t => isLongIdx t = true) Lg) :
    IsQueryBoundP (simulateQ (chainImpl tbl) oa) (fun i => i.isRight = true)
      (a * 1 + H * 2 + M * hmsgCost ℓ + Lg * 9) :=
  Prf.qb_simulateQ_classes4 (p₀ := fun t => isBadIdx B ℓ t = true)
    (p₁ := fun t => Lazy.kind t = .game) (p₂ := fun t => Lazy.kind t = .hash)
    (p₃ := fun t => isHmsgIdx t = true) (p₄ := fun t => isLongIdx t = true) 1 2 (hmsgCost ℓ) 9
    (fun t ht => chainImpl_stepL B ℓ hB tbl t ht) h0 h1 h2 h3 h4

end ChainCountL

section Bounds

/-- Compression queries of a second phase with `H` hash queries and `Lg` long `Thash` queries. -/
abbrev q2L (qf qs ℓ H Lg : ℕ) : ℕ :=
  qf * 1 + H * 2 + (qs + 2) * hmsgCost ℓ + Lg * 9

/-- Long `Thash` queries of the three second phases. -/
abbrev udLg (qs : ℕ) : ℕ := qs * wotsSignLong Link.vp + (wotsAnswerHashes Link.vp + wotsWinHashes Link.vp)
abbrev preLg (qs : ℕ) : ℕ := qs * wotsSignLong Link.vp + (wotsAnswerHashes Link.vp + wotsPreHashes Link.vp)
abbrev tcrLg (qs : ℕ) : ℕ := qs * wotsSignLong Link.vp + (wotsAnswerHashes Link.vp + wotsTcrHashes Link.vp)

variable (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) {qf qs ℓ : ℕ}
  (hqf : ∀ pk, IsQueryBoundP (S.main pk)
    (fun i => Ideal.Realize.isPortQ (S := List Byte) i = true) qf)
  (hqs : ∀ pk, IsQueryBoundP (S.main pk)
    (fun i => Ideal.Realize.isSignQ (S := List Byte) i = true) qs)
  (hlong : ∀ pk, IsQueryBoundP (S.main pk)
    (fun i => Ideal.Realize.isLongQ (S := List Byte) ℓ i = true) 0)
  (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ)

include hqf hqs hlong hout in
theorem udDist_boundL (st : Open.RState Link.vp P0) (pk : Bytes 16) :
    IsQueryBoundP (udDist S oR st pk) (fun i => i.isRight = true)
      (q2L qf qs ℓ (udH qs) (udLg qs)) :=
  chain_countL _ ℓ (by decide) _ _ _ _ _ _
    (wUdP_bad (prims := P0) _ _ _ _ _ _ Link.vp.params.len ℓ okLen_le (mainP_long S hlong _)
      (mainP_out S hout _))
    (wUdP_port (prims := P0) _ _ _ _ _ _ (mainP_port S hqf _))
    (wUdP_hashes (prims := P0) _ _ _ _ _ _ (mainP_sign S hqs _))
    (wUdP_hmsg (prims := P0) _ _ _ _ _ _ (mainP_sign S hqs _))
    (wUdP_long (prims := P0) _ _ _ _ _ _ (mainP_sign S hqs _))

include hqf hqs hlong hout in
theorem preInv_boundL (st : Open.RState Link.vp P0) (pk : Bytes 16) :
    IsQueryBoundP (preInv S oR st pk) (fun i => i.isRight = true)
      (q2L qf qs ℓ (preH qs) (preLg qs)) :=
  chain_countL _ ℓ (by decide) _ _ _ _ _ _
    (wPreP_bad (prims := P0) _ _ _ _ _ _ Link.vp.params.len ℓ okLen_le (mainP_long S hlong _)
      (mainP_out S hout _))
    (wPreP_port (prims := P0) _ _ _ _ _ _ (mainP_port S hqf _))
    (wPreP_hashes (prims := P0) _ _ _ _ _ _ (mainP_sign S hqs _))
    (wPreP_hmsg (prims := P0) _ _ _ _ _ _ (mainP_sign S hqs _))
    (wPreP_long (prims := P0) _ _ _ _ _ _ (mainP_sign S hqs _))

include hqf hqs hlong hout in
theorem tcrForge_boundL (st : Open.RState Link.vp P0) (pk : Bytes 16) :
    IsQueryBoundP (tcrForge S oR st pk) (fun i => i.isRight = true)
      (q2L qf qs ℓ (tcrH qs) (tcrLg qs)) :=
  chain_countL _ ℓ (by decide) _ _ _ _ _ _
    (wTcrP_bad (prims := P0) _ _ _ _ _ _ Link.vp.params.len ℓ okLen_le (mainP_long S hlong _)
      (mainP_out S hout _))
    (wTcrP_port (prims := P0) _ _ _ _ _ _ (mainP_port S hqf _))
    (wTcrP_hashes (prims := P0) _ _ _ _ _ _ (mainP_sign S hqs _))
    (wTcrP_hmsg (prims := P0) _ _ _ _ _ _ (mainP_sign S hqs _))
    (wTcrP_long (prims := P0) _ _ _ _ _ _ (mainP_sign S hqs _))

end Bounds

/-! ## The realisers -/

def pUL (qf qs ℓ : ℕ) : P5 :=
  ⟨0, 323449759100660631040, 1062560399506556770327551, Lw, q2L qf qs ℓ (udH qs) (udLg qs)⟩
def pPL (qf qs ℓ : ℕ) : P5 :=
  ⟨0, 323449759100660631040, 1062560399506556770327551, Lw, q2L qf qs ℓ (preH qs) (preLg qs)⟩
def pWL (qf qs ℓ : ℕ) : P5 :=
  ⟨0, 4851746386509909465600, 1058032102879147521492991, Lw, q2L qf qs ℓ (tcrH qs) (tcrLg qs)⟩

section Realizers

variable {S : ForgerI} {oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)}
  {pkSeedDist : ProbComp (Bytes 16)} {qf qs ℓ : ℕ}
  (hqf : ∀ pk, IsQueryBoundP (S.main pk)
    (fun i => Ideal.Realize.isPortQ (S := List Byte) i = true) qf)
  (hqs : ∀ pk, IsQueryBoundP (S.main pk)
    (fun i => Ideal.Realize.isSignQ (S := List Byte) i = true) qs)
  (hlong : ∀ pk, IsQueryBoundP (S.main pk)
    (fun i => Ideal.Realize.isLongQ (S := List Byte) ℓ i = true) 0)
  (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ)

include hqf hqs hlong hout

/-- **SM-UD realiser (SUF), per-arity costs.** -/
noncomputable def realizesUdL :
    RealizesUd pkSeedDist
      (fun g => Reduction.rUd pkSeedDist
        (Reduction.Lazy.bWotsS (S.typedS (optRandU oR) pkSeedDist g))) (pUL qf qs ℓ) :=
  { realizesUd (S := S) (oR := oR) (pkSeedDist := pkSeedDist) hqf hqs hlong hout with
    hq₂ := fun st pk => udDist_boundL S oR hqf hqs hlong hout st pk }

/-- **SM-UD realiser (EUF), per-arity costs.** -/
noncomputable def realizesUdLE :
    RealizesUd pkSeedDist
      (fun g => Reduction.rUd pkSeedDist
        (Reduction.Lazy.bWotsS (S.typedE (optRandU oR) pkSeedDist g))) (pUL qf qs ℓ) :=
  realizesUdL hqf hqs hlong hout

/-- **SM-PRE realiser (SUF), per-arity costs.** -/
noncomputable def realizesPreL :
    RealizesPre pkSeedDist
      (fun g => Reduction.rPre pkSeedDist
        (Reduction.Lazy.bWotsS (S.typedS (optRandU oR) pkSeedDist g))) (pPL qf qs ℓ) :=
  { realizesPre (S := S) (oR := oR) (pkSeedDist := pkSeedDist) hqf hqs hlong hout with
    hq₂ := fun st pk => preInv_boundL S oR hqf hqs hlong hout st pk }

/-- **SM-PRE realiser (EUF), per-arity costs.** -/
noncomputable def realizesPreLE :
    RealizesPre pkSeedDist
      (fun g => Reduction.rPre pkSeedDist
        (Reduction.Lazy.bWotsS (S.typedE (optRandU oR) pkSeedDist g))) (pPL qf qs ℓ) :=
  realizesPreL hqf hqs hlong hout

/-- **SM-TCR realiser on `F` (SUF), per-arity costs.** -/
noncomputable def realizesWotsTcrL :
    RealizesWotsTcr pkSeedDist
      (fun g => Reduction.rTcrT pkSeedDist
        (Reduction.Lazy.bWotsS (S.typedS (optRandU oR) pkSeedDist g))) (pWL qf qs ℓ) :=
  { realizesWotsTcr (S := S) (oR := oR) (pkSeedDist := pkSeedDist) hqf hqs hlong hout with
    hq₂ := fun st pk => tcrForge_boundL S oR hqf hqs hlong hout st pk }

/-- **SM-TCR realiser on `F` (EUF), per-arity costs.** -/
noncomputable def realizesWotsTcrLE :
    RealizesWotsTcr pkSeedDist
      (fun g => Reduction.rTcrT pkSeedDist
        (Reduction.Lazy.bWotsS (S.typedE (optRandU oR) pkSeedDist g))) (pWL qf qs ℓ) :=
  realizesWotsTcrL hqf hqs hlong hout

end Realizers

/-! ## Bounds in the shape of `P5.Le` -/

/-- Compression-query cap of the three realisers with per-arity costs. -/
def QcWL (qf qs ℓ : ℕ) : ℕ :=
  qf + 2 * (121857 * qs + 146514) + 9 * (3577 * qs + 146514) + (qs + 2) * ((ℓ + 56) / 64 + 3)

theorem q2L_le (qf qs ℓ H Lg : ℕ) (hH : H ≤ 121857 * qs + 146514) (hL : Lg ≤ 3577 * qs + 146514) :
    q2L qf qs ℓ H Lg ≤ QcWL qf qs ℓ := by
  unfold q2L QcWL hmsgCost
  omega

theorem udLg_le (qs : ℕ) : udLg qs ≤ 3577 * qs + 146514 := by
  unfold udLg
  rw [wotsSignLong_128s, wotsAnswerHashes_128s, wotsWinHashes_128s]; omega
theorem preLg_le (qs : ℕ) : preLg qs ≤ 3577 * qs + 146514 := by
  unfold preLg
  rw [wotsSignLong_128s, wotsAnswerHashes_128s, wotsPreHashes_128s]; omega
theorem tcrLg_le (qs : ℕ) : tcrLg qs ≤ 3577 * qs + 146514 := by
  unfold tcrLg
  rw [wotsSignLong_128s, wotsAnswerHashes_128s, wotsTcrHashes_128s]; omega

theorem QcWL_le_QcW (qf qs ℓ : ℕ) : QcWL qf qs ℓ ≤ QcW qf qs ℓ := by
  unfold QcWL QcW
  omega

theorem pUL_le (qf qs ℓ : ℕ) : (pUL qf qs ℓ).Le (QcWL qf qs ℓ) NW :=
  ⟨Nat.zero_le _, by simp [pUL, NW], by simp [pUL, NW], Lw_le,
    q2L_le _ _ _ _ _ (udH_le qs) (udLg_le qs)⟩
theorem pPL_le (qf qs ℓ : ℕ) : (pPL qf qs ℓ).Le (QcWL qf qs ℓ) NW :=
  ⟨Nat.zero_le _, by simp [pPL, NW], by simp [pPL, NW], Lw_le,
    q2L_le _ _ _ _ _ (preH_le qs) (preLg_le qs)⟩
theorem pWL_le (qf qs ℓ : ℕ) : (pWL qf qs ℓ).Le (QcWL qf qs ℓ) NW :=
  ⟨Nat.zero_le _, by simp [pWL, NW], by simp [pWL, NW], Lw_le,
    q2L_le _ _ _ _ _ (tcrH_le qs) (tcrLg_le qs)⟩

end Ideal.Realize.Wots

#print axioms Ideal.Realize.Wots.wotsSignFromHistO_long
#print axioms Ideal.Realize.Wots.wPhase2P_long
#print axioms Ideal.Realize.Wots.chain_countL
#print axioms Ideal.Realize.Wots.udDist_boundL
#print axioms Ideal.Realize.Wots.preInv_boundL
#print axioms Ideal.Realize.Wots.tcrForge_boundL
#print axioms Ideal.Realize.Wots.realizesUdL
#print axioms Ideal.Realize.Wots.realizesPreL
#print axioms Ideal.Realize.Wots.realizesWotsTcrL
#print axioms Ideal.Realize.Wots.realizesUdLE
#print axioms Ideal.Realize.Wots.realizesPreLE
#print axioms Ideal.Realize.Wots.realizesWotsTcrLE
#print axioms Ideal.Realize.Wots.QcWL_le_QcW
#print axioms Ideal.Realize.Wots.pUL_le
#print axioms Ideal.Realize.Wots.pPL_le
#print axioms Ideal.Realize.Wots.pWL_le
