import Ideal.Realize.WotsL5
import Ideal.Games.UdFine

/-!
# The SM-UD realiser with its message blocks issued as free chain queries

The second phase `udDist` of the SM-UD realiser (`WotsReal.lean`) issues every hash query as
compression queries (`chainImpl`).  `udDistC tbl pk` is the same program with each of the two
SHA-256 chains of an `H_msg` query issued as ONE chain query (`pcS`) whenever its first block is
not the seed block `sb128 pk`, and as raw compression queries otherwise (`chainOrRaw`):

* `udDist_eq_expand`: `udDist` is the expansion (`expandImpl IV128`) of `udDistC` — the same
  program, query for query;
* `udDistC_free`: every chain query of `udDistC … pk` is free (`freeC (sb128 pk)`), by
  construction;
* `udDistC_boundR`: for `pk ≠ 0`, `udDistC … pk` makes at most
  `qf + 2·udH qs + 9·udLg qs` raw compression queries — the `H_msg` chains cost none.  Why:
  every `H_msg` query of the second phase is at the public seed `pk` (`wUdP_foreign`), and the
  first block of either chain of `H_msg(R, pk, root, M)` carries `pk` in bytes `16..31`, where the
  seed block has zeros (`iblocksH_head_ne`, `oblocksH_head_ne`).  This is a property of the
  blocks the program forms, whatever the forger's messages are.
* `udLeg_fine`: the averaged SM-UD gap of the Reduction's adversary with the fine error
  `epsUdF` (`wotsUd_bound_128s_fine`).
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security TweakableHash ENNReal

namespace Ideal.Realize.Wots

open Reduction Reduction.Open Reduction.Lazy Reduction.Resources2 Ideal.Realize Ideal.Transport
open Ideal.Realize.Fors (isLongIdx)

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! ## First blocks of the `H_msg` chains -/

theorem blocksOf_head? (l : List UInt8) (h : 64 ≤ l.length) :
    (blocksOf l).head? = some (Vector.ofFn fun j : Fin 64 => l.getD j 0) := by
  unfold blocksOf
  obtain ⟨n, hn⟩ : ∃ n, l.length / 64 = n + 1 := ⟨l.length / 64 - 1, by omega⟩
  rw [hn, List.range_succ_eq_map]
  simp

theorem padBlocks_head_byte (x : ByteArray) {b : Blk} (h : (padBlocks x).head? = some b)
    (j : ℕ) (hj : j < 64) (hjx : j < x.data.toList.length) :
    b.toList[j]'(by simp; omega) = x.data.toList[j] := by
  unfold padBlocks at h
  rw [blocksOf_head? _ (by rw [padL_length]; omega)] at h
  obtain rfl := (Option.some.inj h).symm
  have hj' : j < x.data.size := by simpa using hjx
  simp [padL, List.getD_eq_getElem?_getD, List.getElem?_append_left hjx,
    Array.getElem?_eq_getElem hj']

/-- The all-zero public seed. -/
def zero16 : Bytes 16 := Vector.replicate 16 0

theorem sb128_byte (pk₀ : Bytes 16) (i : ℕ) (hi : i < 16) :
    (sb128 pk₀).toList[16 + i]'(by simp; omega) = 0 := by
  simp only [sb128_toList]
  rw [List.getElem_append_right (by simp)]
  exact List.getElem_replicate _

/-- A block whose bytes `16..31` are `pk` is not a seed block, unless `pk = 0`. -/
theorem head_ne_sb_of_bytes (x : ByteArray) (pk : Bytes 16) (hpk : pk ≠ zero16) (pk₀ : Bytes 16)
    (hlen : 32 ≤ x.data.toList.length)
    (hx : ∀ i (hi : i < 16), x.data.toList[16 + i]'(by omega) = pk.toList[i]'(by simp; omega)) :
    (padBlocks x).head? ≠ some (sb128 pk₀) := by
  intro h
  apply hpk
  apply Vector.toList_inj.mp
  apply List.ext_getElem (by simp [zero16])
  intro i hi _
  have hi' : i < 16 := by simpa using hi
  have h1 := padBlocks_head_byte x h (16 + i) (by omega) (by omega)
  rw [sb128_byte pk₀ i hi', hx i hi'] at h1
  rw [← h1]
  show (0 : UInt8) = (Vector.replicate 16 (0 : UInt8)).toList[i]'(by simp; omega)
  simp only [Vector.toList_replicate]
  exact (List.getElem_replicate _).symm

theorem iblocksH_head_ne (R pk root : Bytes 16) (M : List UInt8) (hpk : pk ≠ zero16)
    (pk₀ : Bytes 16) : (iblocksH R pk root M).head? ≠ some (sb128 pk₀) := by
  unfold iblocksH
  refine head_ne_sb_of_bytes _ pk hpk pk₀ (by rw [hInner_toList]; simp <;> omega) fun i hi => ?_
  simp only [hInner_toList]
  rw [List.getElem_append_right (by simp), List.getElem_append_left (by simp; omega)]
  simp

theorem oblocksH_head_ne (R pk : Bytes 16) (s : St) (hpk : pk ≠ zero16) (pk₀ : Bytes 16) :
    (oblocksH R pk s).head? ≠ some (sb128 pk₀) := by
  unfold oblocksH
  refine head_ne_sb_of_bytes _ pk hpk pk₀ (by rw [hOuter_toList]; simp <;> omega) fun i hi => ?_
  simp only [hOuter_toList]
  rw [List.getElem_append_right (by simp), List.getElem_append_left (by simp; omega)]
  simp

/-! ## Raw programs inside the chain interface -/

/-- A raw compression program, read in the chain interface. -/
def rawE : QueryImpl CSpec (OracleComp (pcS St Blk))
  | .inl n => (liftM ((pcS St Blk).query (.inl n)) : OracleComp (pcS St Blk) _)
  | .inr q => (liftM ((pcS St Blk).query (.inr (.inl q))) : OracleComp (pcS St Blk) _)

theorem expand_rawE {α : Type} (oa : OracleComp CSpec α) :
    simulateQ (expandImpl IV128) (simulateQ rawE oa) = oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, ih]
    rcases t with n | q
    · simp [rawE, expandImpl]
    · simp [rawE, expandImpl, rawQ]

theorem rawE_bound {α : Type} (oa : OracleComp CSpec α) (n : ℕ)
    (h : IsQueryBoundP oa (fun i => i.isRight = true) n) :
    IsQueryBoundP (simulateQ rawE oa) (fun t => isRawC t = true) n := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure x => exact isQueryBoundP_pure _ _ _
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at h
    simp only [simulateQ_bind, simulateQ_spec_query]
    rcases t with m | q
    · refine (isQueryBoundP_bind (m := n) (n := 0)
        ((isQueryBoundP_query_iff _ _ _).2 fun h => by simp [isRawC] at h) fun u _ => ?_).mono
        (by omega)
      exact ih u n (by simpa using h.2 u)
    · have hn : 0 < n := h.1.resolve_left (by simp)
      refine (isQueryBoundP_bind (m := n - 1) (n := 1)
        ((isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos) fun u _ => ?_).mono (by omega)
      exact ih u (n - 1) (by simpa using h.2 u)

theorem rawE_free {α : Type} (oa : OracleComp CSpec α) (sbS : Blk) :
    AllQueriesSatisfy (simulateQ rawE oa) (freeC sbS) := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query]
    rcases t with m | q
    · exact allQueriesSatisfy_bind ((allQueriesSatisfy_query_iff _ _).2 trivial) fun u => ih u
    · exact allQueriesSatisfy_bind ((allQueriesSatisfy_query_iff _ _).2 trivial) fun u => ih u

/-! ## The handler with chain queries for `H_msg` -/

/-- One SHA-256 chain from `IV`: a chain query unless its first block is the seed block. -/
def chainOrRaw (pk : Bytes 16) (bs : List Blk) : OracleComp (pcS St Blk) St :=
  if bs.head? = some (sb128 pk) then simulateQ rawE (foldQ IV128 bs)
  else (liftM ((pcS St Blk).query (.inr (.inr bs))) : OracleComp (pcS St Blk) St)

/-- `H_msg(R, pk', root, M)` with its two chains through `chainOrRaw pk`. -/
def hmsgCh (pk R pk' root : Bytes 16) (M : List UInt8) : OracleComp (pcS St Blk) (Bytes 30) := do
  let s ← chainOrRaw pk (iblocksH R pk' root M)
  let s' ← chainOrRaw pk (oblocksH R pk' s)
  return dig30 s'

/-- The handler of `chainImpl` with `H_msg` through `hmsgCh pk`. -/
def chainImplH {D V : Type} (tbl : D → V) (pk : Bytes 16) :
    QueryImpl (PSpecC D V) (OracleComp (pcS St Blk))
  | .inl n => simulateQ rawE (chainImpl tbl (.inl n))
  | .inr (.inl q) => simulateQ rawE (chainImpl tbl (.inr (.inl q)))
  | .inr (.inr (.inl d)) => simulateQ rawE (chainImpl tbl (.inr (.inr (.inl d))))
  | .inr (.inr (.inr (.thash pk' a xs))) =>
      simulateQ rawE (chainImpl tbl (.inr (.inr (.inr (.thash pk' a xs)))))
  | .inr (.inr (.inr (.hmsg R pk' root M))) => hmsgCh pk R pk' root M

theorem expand_chainOrRaw (pk : Bytes 16) (bs : List Blk) :
    simulateQ (expandImpl IV128) (chainOrRaw pk bs) = foldQ IV128 bs := by
  unfold chainOrRaw
  split_ifs
  · exact expand_rawE _
  · simp [expandImpl, foldR, foldQ, rawQ, cq]

theorem expand_chainImplH {D V : Type} (tbl : D → V) (pk : Bytes 16) (t : (PSpecC D V).Domain) :
    simulateQ (expandImpl IV128) (chainImplH tbl pk t) = chainImpl tbl t := by
  rcases t with n | q | d | (⟨pk', a, xs⟩ | ⟨R, pk', root, M⟩)
  · exact expand_rawE _
  · exact expand_rawE _
  · exact expand_rawE _
  · exact expand_rawE _
  · show simulateQ (expandImpl IV128) (hmsgCh pk R pk' root M) = hmsgC R pk' root M
    simp only [hmsgCh, hmsgC, simulateQ_bind, expand_chainOrRaw, simulateQ_pure]

/-- **Expansion**: a program through `chainImplH` and then `expandImpl` is the program through
`chainImpl`. -/
theorem expand_simulateQ_chainImplH {D V : Type} (tbl : D → V) (pk : Bytes 16) {α : Type}
    (oa : OracleComp (PSpecC D V) α) :
    simulateQ (expandImpl IV128) (simulateQ (chainImplH tbl pk) oa) =
      simulateQ (chainImpl tbl) oa := by
  rw [simulateQ_comp]
  congr 1
  funext t
  exact expand_chainImplH tbl pk t

theorem chainOrRaw_free (pk : Bytes 16) (bs : List Blk) :
    AllQueriesSatisfy (chainOrRaw pk bs) (freeC (sb128 pk)) := by
  unfold chainOrRaw
  split_ifs with h
  · exact rawE_free _ _
  · exact (allQueriesSatisfy_query_iff _ _).2 h

theorem chainImplH_free {D V : Type} (tbl : D → V) (pk : Bytes 16) (t : (PSpecC D V).Domain) :
    AllQueriesSatisfy (chainImplH tbl pk t) (freeC (sb128 pk)) := by
  rcases t with n | q | d | (⟨pk', a, xs⟩ | ⟨R, pk', root, M⟩)
  · exact rawE_free _ _
  · exact rawE_free _ _
  · exact rawE_free _ _
  · exact rawE_free _ _
  · show AllQueriesSatisfy (hmsgCh pk R pk' root M) (freeC (sb128 pk))
    unfold hmsgCh
    exact allQueriesSatisfy_bind (chainOrRaw_free _ _) fun s =>
      allQueriesSatisfy_bind (chainOrRaw_free _ _) fun _ => allQueriesSatisfy_pure _ _

theorem allQueriesSatisfy_simulateQ {ι₁ ι₂ : Type} {spec₁ : OracleSpec ι₁}
    {spec₂ : OracleSpec ι₂} (impl : QueryImpl spec₁ (OracleComp spec₂)) (p : ι₂ → Prop)
    (h : ∀ t, AllQueriesSatisfy (impl t) p) {α : Type} (oa : OracleComp spec₁ α) :
    AllQueriesSatisfy (simulateQ impl oa) p := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query]
    exact allQueriesSatisfy_bind (h t) fun u => ih u

/-! ## Counts -/

/-- An `H_msg` query at a public seed other than `pk`. -/
def isForeignIdx {ι P K Y : Type} [DecidableEq P] (pk : P) :
    ℕ ⊕ (ι ⊕ (SecIdx ⊕ PublicHashQuery P K Y)) → Bool
  | .inr (.inr (.inr (.hmsg _ pk' _ _))) => decide (pk' ≠ pk)
  | _ => false

theorem chainOrRaw_free_cost (pk : Bytes 16) (bs : List Blk)
    (h : bs.head? ≠ some (sb128 pk)) :
    IsQueryBoundP (chainOrRaw pk bs) (fun t => isRawC t = true) 0 := by
  unfold chainOrRaw
  rw [if_neg h]
  exact (isQueryBoundP_query_iff _ _ _).2 fun h => by simp [isRawC] at h

theorem chainImplH_stepR (B ℓ : ℕ) (hB : B ≤ 35) (tbl : SecIdx → Bytes 16) (pk : Bytes 16)
    (hpk : pk ≠ zero16) (t : (PSpecC SecIdx (Bytes 16)).Domain)
    (ht : ¬ (isBadIdx B ℓ t = true ∨ isForeignIdx pk t = true)) :
    IsQueryBoundP (chainImplH tbl pk t) (fun t => isRawC t = true)
      ((if Lazy.kind t = .game then 1 else 0) + (if Lazy.kind t = .hash then 2 else 0) +
        (if isHmsgIdx t = true then 0 else 0) +
        (if isLongIdx t = true then 9 else 0)) := by
  simp only [not_or] at ht
  rcases t with n | q | d | (⟨pk', a, xs⟩ | ⟨R, pk', root, M⟩)
  · exact rawE_bound _ _ ((chainImpl_stepL B ℓ hB tbl _ ht.1).mono
      (by simp [Lazy.kind, isHmsgIdx, isLongIdx]))
  · exact rawE_bound _ _ ((chainImpl_stepL B ℓ hB tbl _ ht.1).mono
      (by simp [Lazy.kind, isHmsgIdx, isLongIdx]))
  · exact rawE_bound _ _ ((chainImpl_stepL B ℓ hB tbl _ ht.1).mono
      (by simp [Lazy.kind, isHmsgIdx, isLongIdx]))
  · exact rawE_bound _ _ ((chainImpl_stepL B ℓ hB tbl _ ht.1).mono
      (by simp [Lazy.kind, isHmsgIdx]))
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


/-! ## Every `H_msg` query of the SM-UD second phase is at the public seed -/

section Foreign

variable (optRand : PublicKeyCore core₀ → ProbComp core₀.Y) (mainP : PortForgerProg Link.vp P0)
  (ℓ : ℕ)

theorem foreign_hth (pk : P0.PkSeed) (pk' : P0.PkSeed) (key : P0.AdrsKey) (xs : List P0.Y)
    (hx : OkLen Link.vp xs) :
    ¬ isForeignIdx pk (thIdx P0 (St × Blk) pk' key xs) = true := by
  simp [isForeignIdx, thIdx]

theorem foreign_hsec (pk : P0.PkSeed) (d : SecIdx) :
    ¬ isForeignIdx (ι := St × Blk) (K := P0.AdrsKey) (Y := P0.Y) pk (.inr (.inr (.inl d))) = true := by
  simp [isForeignIdx]

theorem foreign_hm (R : P0.Y) (pk : P0.PkSeed) (root : P0.Y) (msg : List Byte) :
    IsQueryBoundP (PublicHash.hmsg P0.core R pk root msg :
      OracleComp (OSpec P0 (hS St Blk)) _) (fun t => isForeignIdx pk t = true) 0 :=
  (isQueryBoundP_query_iff _ _ _).2 fun h => by simp [isForeignIdx] at h

theorem wForgeP_foreign (hist : List (WotsGame.Entry P0)) (root : P0.Y) (pk : P0.PkSeed)
    (hlong : IsQueryBoundP (mainP ⟨pk, root⟩)
      (fun i => isLongQ (S := GeneralScheme.SignatureCore Link.vp P0.core) ℓ i = true) 0) :
    IsQueryBoundP (wForgeP optRand mainP hist root pk) (fun t => isForeignIdx pk t = true) 0 := by
  have hu : ∀ n : ℕ, ¬ isForeignIdx (ι := St × Blk) (K := P0.AdrsKey) (Y := P0.Y) pk
      (.inl n) = true := by
    intro n; simp [isForeignIdx]
  refine qb_simulateQ_run_zero
    (p := fun i => isLongQ (S := GeneralScheme.SignatureCore Link.vp P0.core) ℓ i = true)
    (fun t ht s => ?_) hlong []
  rcases t with n | q | msg
  · exact wUnif_step optRand _ hu hist pk root n s
  · exact wGame_step optRand _ hist pk root q s 0
      ((isQueryBoundP_query_iff _ _ _).2 fun h => by simp [isForeignIdx] at h)
  · exact wSign_step optRand _ hu hist pk root msg 0
      (fun R => pw_signFromHist _ (foreign_hsec pk) (fun pk' key xs hx => foreign_hth pk pk' key xs hx)
        hist _ msg R 0 (foreign_hm _ pk _ _)) s

theorem wUdP_foreign (hist hist2 : List (WotsGame.Entry P0)) (root : P0.Y) (pk : P0.PkSeed)
    (hlong : IsQueryBoundP (mainP ⟨pk, root⟩)
      (fun i => isLongQ (S := GeneralScheme.SignatureCore Link.vp P0.core) ℓ i = true) 0) :
    IsQueryBoundP (wUdP optRand mainP hist hist2 root pk) (fun t => isForeignIdx pk t = true) 0 :=
  wPhase2P_bound optRand mainP _ hist root pk _ 0 (0 + 0) 0
    (wForgeP_foreign optRand mainP ℓ hist root pk hlong)
    (fun r _ => pw_answer _ (foreign_hsec pk) (fun pk' key xs hx => foreign_hth pk pk' key xs hx)
      hist _ _ _ 0 (foreign_hm _ pk _ _))
    (fun x => pw_win _ (fun pk' key xs hx => foreign_hth pk pk' key xs hx) _ _ _ _ _)

end Foreign

/-! ## The SM-UD second phase with chain queries -/

section Dist

variable (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))

/-- **Second phase of the ideal-model SM-UD adversary with chain queries** for the `H_msg`
chains (`udDist` is its expansion, `udDist_eq_expand`). -/
noncomputable def udDistC (st : Open.RState Link.vp P0) (pk : Bytes 16) :
    OracleComp (pcS St Blk) Bool :=
  simulateQ (chainImplH st.1.1 pk) (wUdP (optRand₀ oR) (mainP S) st.1.2.1 st.2 st.1.2.2 pk)

theorem udDist_eq_expand (st : Open.RState Link.vp P0) (pk : Bytes 16) :
    udDist S oR st pk = simulateQ (expandImpl IV128) (udDistC S oR st pk) :=
  (expand_simulateQ_chainImplH _ _ _).symm

theorem udDistC_free (st : Open.RState Link.vp P0) (pk : Bytes 16) :
    AllQueriesSatisfy (udDistC S oR st pk) (freeC (sb128 pk)) :=
  allQueriesSatisfy_simulateQ _ _ (chainImplH_free _ _) _

/-- Raw compression queries of the SM-UD second phase with chain queries: the forger's, two per
hash query, nine more per long `Thash` query; none for `H_msg`. -/
abbrev qMU (qf qs : ℕ) : ℕ := qf * 1 + udH qs * 2 + (qs + 2) * 0 + udLg qs * 9

variable {qf qs ℓ : ℕ}
  (hqf : ∀ pk, IsQueryBoundP (S.main pk)
    (fun i => Ideal.Realize.isPortQ (S := List Byte) i = true) qf)
  (hqs : ∀ pk, IsQueryBoundP (S.main pk)
    (fun i => Ideal.Realize.isSignQ (S := List Byte) i = true) qs)
  (hlong : ∀ pk, IsQueryBoundP (S.main pk)
    (fun i => Ideal.Realize.isLongQ (S := List Byte) ℓ i = true) 0)
  (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ)

include hqf hqs hlong hout in
/-- **The raw count**, at a public seed `pk ≠ 0`. -/
theorem udDistC_boundR (st : Open.RState Link.vp P0) (pk : Bytes 16) (hpk : pk ≠ zero16) :
    IsQueryBoundP (udDistC S oR st pk) (fun t => isRawC t = true) (qMU qf qs) :=
  Prf.qb_simulateQ_classes4
    (p₀ := fun t => isBadIdx Link.vp.params.len ℓ t = true ∨ isForeignIdx pk t = true)
    (p₁ := fun t => Lazy.kind t = .game) (p₂ := fun t => Lazy.kind t = .hash)
    (p₃ := fun t => isHmsgIdx t = true) (p₄ := fun t => isLongIdx t = true) 1 2 0 9
    (fun t ht => chainImplH_stepR _ ℓ (by decide) _ pk hpk t ht)
    ((wUdP_bad (prims := P0) _ _ _ _ _ _ Link.vp.params.len ℓ okLen_le (mainP_long S hlong _)
      (mainP_out S hout _)).or (wUdP_foreign _ _ ℓ _ _ _ _ (mainP_long S hlong _)))
    (wUdP_port (prims := P0) _ _ _ _ _ _ (mainP_port S hqf _))
    (wUdP_hashes (prims := P0) _ _ _ _ _ _ (mainP_sign S hqs _))
    (wUdP_hmsg (prims := P0) _ _ _ _ _ _ (mainP_sign S hqs _))
    (wUdP_long (prims := P0) _ _ _ _ _ _ (mainP_sign S hqs _))

end Dist

end Ideal.Realize.Wots

#print axioms Ideal.Realize.Wots.udDist_eq_expand
#print axioms Ideal.Realize.Wots.udDistC_free
#print axioms Ideal.Realize.Wots.udDistC_boundR

namespace Ideal

open Ideal.Realize

private theorem card_bytes16_inv_udF :
    (Fintype.card (Bytes 16) : ℝ≥0∞)⁻¹ = ((2 : ℝ≥0∞) ^ 128)⁻¹ := by
  rw [card_bytes]
  norm_num

private theorem card_St_inv_udF : (Fintype.card St : ℝ≥0∞)⁻¹ = ((2 : ℝ≥0∞) ^ 256)⁻¹ := by
  rw [card_St, Nat.cast_pow, Nat.cast_ofNat]

/-- **SM-UD of the 128s `F`, fine accounting of the second phase** (`ud_bound_fine` at
`FWotsPre128`).  The distinguisher is the expansion of `dC` (chain queries from `IV128`); outside
a set `bad` of public seeds of probability `≤ β`, `dC` makes at most `qM` raw compression queries
and only chain queries whose first block is not the seed block. -/
theorem wotsUd_bound_128s_fine (pkSeedDist : ProbComp (Bytes 16))
    (γ : ℝ≥0∞) (hγ : ∀ s, Pr{let s' ← pkSeedDist}[s' = s] ≤ γ)
    (A : WotsUdAdv128 pkSeedDist) (q₁ qch qc L q₂ : ℕ)
    (hq₁ : A.PickBound q₁) (hch : A.ChalBound qch) (hc : A.CollBound qc)
    (hL : A.CollLen L) (hq₂ : A.DistBound q₂)
    (dC : A.State → Bytes 16 → OracleComp (pcS St Blk) Bool)
    (hdC : ∀ st pk, A.distinguish st pk = simulateQ (expandImpl IV128) (dC st pk))
    (bad : Bytes 16 → Prop) (β : ℝ≥0∞) (hβ : Pr{let s ← pkSeedDist}[bad s] ≤ β) (qM : ℕ)
    (hqM : ∀ st pk, ¬ bad pk → IsQueryBoundP (dC st pk) (fun t => isRawC t = true) qM)
    (hfree : ∀ st pk, ¬ bad pk → AllQueriesSatisfy (dC st pk) (freeC (sb128 pk))) :
    wotsUdRealI pkSeedDist A ≤
      wotsUdIdealI pkSeedDist A + (qM + q₂ * β) * ((2 : ℝ≥0∞) ^ 128)⁻¹ + 2 * q₁ * γ +
        (2 * (2 * q₁ + (qch + qc) * (1 + 2 * L) + 1) + (1 + 2 * ((q₁ + qc) * max 1 L)) +
          2 * q₂ : ℕ) * ((2 : ℝ≥0∞) ^ 256)⁻¹ := by
  have hs : ∀ (t : Bytes 22) (x : Bytes 16), (tblocks t [x]).2 = [] :=
    fun t x => tblocks_snd_of_length_one t [x] rfl
  rw [wotsUdRealI_eq, wotsUdIdealI_eq, ← card_St_inv_udF, ← card_bytes16_inv_udF]
  exact @ud_bound_fine St Blk (Bytes 16) (Bytes 22) (Bytes 16) (Bytes 16) (Bytes 16) Unit
    (FWotsPre128 pkSeedDist) _ _ _ _ _ _ _ sampY128 _ sampY128 _
    id Function.injective_id sb128_injective γ hγ hs btw128
    (fun t x => btw128_tblocks t [x]) (fun _ t m => btw128_tblocks t m)
    (fun t x x' h => List.singleton_injective
      (tblocks_injective (Prod.ext h ((hs t x).trans (hs t x').symm))).2)
    prEvent_out16 A q₁ qch qc L q₂ hq₁ hch hc hL hq₂ dC hdC bad β hβ qM hqM hfree

/-- The fine SM-UD error (`wotsUd_bound_128s_fine` with `β = γ`). -/
noncomputable def epsUdF (γ : ℝ≥0∞) (p : P5) (qM : ℕ) : ℝ≥0∞ :=
  (qM + p.q₂ * γ) * ((2 : ℝ≥0∞) ^ 128)⁻¹ + 2 * p.q₁ * γ +
    (2 * (2 * p.q₁ + (p.qch + p.qc) * (1 + 2 * p.L) + 1) + (1 + 2 * ((p.q₁ + p.qc) * max 1 p.L)) +
      2 * p.q₂ : ℕ) * ((2 : ℝ≥0∞) ^ 256)⁻¹

section Leg

variable {S : ForgerI} {oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)}
  {pkSeedDist : ProbComp (Bytes 16)} {γ : ℝ≥0∞} {qf qs ℓ : ℕ}
  (hγ : ∀ s, Pr{let s' ← pkSeedDist}[s' = s] ≤ γ)
  (hqf : ∀ pk, IsQueryBoundP (S.main pk)
    (fun i => Ideal.Realize.isPortQ (S := List Byte) i = true) qf)
  (hqs : ∀ pk, IsQueryBoundP (S.main pk)
    (fun i => Ideal.Realize.isSignQ (S := List Byte) i = true) qs)
  (hlong : ∀ pk, IsQueryBoundP (S.main pk)
    (fun i => Ideal.Realize.isLongQ (S := List Byte) ℓ i = true) 0)
  (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ)

include hγ hqf hqs hlong hout

/-- **The SM-UD leg with the message blocks uncharged (SUF).**  The averaged real-minus-ideal gap
of the Reduction's SM-UD adversary is at most `epsUdF γ (pUL qf qs ℓ) (qMU qf qs)`: the
realiser's second phase charged `qMU qf qs = qf + 2·udH qs + 9·udLg qs` raw compression queries,
its `H_msg` chains free (the seed `0` is the `bad` set, of probability `≤ γ`). -/
theorem udLeg_fine :
    (cfAvg fun g => SM_DT_UD_RealSuccess (Reduction.rUd pkSeedDist
        (Reduction.Lazy.bWotsS (S.typedS (optRandU oR) pkSeedDist g)))) ≤
      (cfAvg fun g => SM_DT_UD_IdealSuccess (Reduction.rUd pkSeedDist
        (Reduction.Lazy.bWotsS (S.typedS (optRandU oR) pkSeedDist g)))) +
        epsUdF γ (Wots.pUL qf qs ℓ) (Wots.qMU qf qs) := by
  let R := Wots.realizesUdL (oR := oR) (pkSeedDist := pkSeedDist) hqf hqs hlong hout
  have h1 : (cfAvg fun g => SM_DT_UD_RealSuccess (Reduction.rUd pkSeedDist
      (Reduction.Lazy.bWotsS (S.typedS (optRandU oR) pkSeedDist g)))) =
      wotsUdRealI pkSeedDist R.A := cfAvg_of_evalDist_eq R.real
  have h2 : (cfAvg fun g => SM_DT_UD_IdealSuccess (Reduction.rUd pkSeedDist
      (Reduction.Lazy.bWotsS (S.typedS (optRandU oR) pkSeedDist g)))) =
      wotsUdIdealI pkSeedDist R.A := cfAvg_of_evalDist_eq R.ideal
  rw [h1, h2]
  refine (wotsUd_bound_128s_fine pkSeedDist γ hγ R.A _ _ _ _ _ R.hq₁ R.hch R.hc R.hL R.hq₂
    (Wots.udDistC S oR) (fun st pk => Wots.udDist_eq_expand S oR st pk) (· = Wots.zero16) γ
    (hγ _) (Wots.qMU qf qs) (fun st pk h => Wots.udDistC_boundR S oR hqf hqs hlong hout st pk h)
    (fun st pk _ => Wots.udDistC_free S oR st pk)).trans (le_of_eq ?_)
  rw [epsUdF]
  ring

/-- **The SM-UD leg with the message blocks uncharged (EUF).** -/
theorem udLeg_fineE :
    (cfAvg fun g => SM_DT_UD_RealSuccess (Reduction.rUd pkSeedDist
        (Reduction.Lazy.bWotsS (S.typedE (optRandU oR) pkSeedDist g)))) ≤
      (cfAvg fun g => SM_DT_UD_IdealSuccess (Reduction.rUd pkSeedDist
        (Reduction.Lazy.bWotsS (S.typedE (optRandU oR) pkSeedDist g)))) +
        epsUdF γ (Wots.pUL qf qs ℓ) (Wots.qMU qf qs) := by
  let R := Wots.realizesUdLE (oR := oR) (pkSeedDist := pkSeedDist) hqf hqs hlong hout
  have h1 : (cfAvg fun g => SM_DT_UD_RealSuccess (Reduction.rUd pkSeedDist
      (Reduction.Lazy.bWotsS (S.typedE (optRandU oR) pkSeedDist g)))) =
      wotsUdRealI pkSeedDist R.A := cfAvg_of_evalDist_eq R.real
  have h2 : (cfAvg fun g => SM_DT_UD_IdealSuccess (Reduction.rUd pkSeedDist
      (Reduction.Lazy.bWotsS (S.typedE (optRandU oR) pkSeedDist g)))) =
      wotsUdIdealI pkSeedDist R.A := cfAvg_of_evalDist_eq R.ideal
  rw [h1, h2]
  refine (wotsUd_bound_128s_fine pkSeedDist γ hγ R.A _ _ _ _ _ R.hq₁ R.hch R.hc R.hL R.hq₂
    (Wots.udDistC S oR) (fun st pk => Wots.udDist_eq_expand S oR st pk) (· = Wots.zero16) γ
    (hγ _) (Wots.qMU qf qs) (fun st pk h => Wots.udDistC_boundR S oR hqf hqs hlong hout st pk h)
    (fun st pk _ => Wots.udDistC_free S oR st pk)).trans (le_of_eq ?_)
  rw [epsUdF]
  ring

end Leg

end Ideal

#print axioms Ideal.wotsUd_bound_128s_fine
#print axioms Ideal.udLeg_fine
#print axioms Ideal.udLeg_fineE
