import Ideal.Realize.Tcr

/-!
# The class-TCR realisers: query counts and the realiser definitions

Headline: `realizesTcrS` / `realizesTcrE` (every arity `n`; SUF / EUF families of
`Ideal/Compose128.lean`'s `SufRealizers` / `EufRealizers`, at `optRandU oR`), with the eight
named instances `realizesTcr{F,H,Len,K}_{S,E}`, parameters `tcrP qf qs ℓ`, and the bound
lemmas `tcrP_le`, `tcrP_le_of`, `tcrP_le_2_81` (shape of `P5.Le`), `q₂T_128s`, `q₂T_le`.
Hypotheses: only the four forger bounds `hqf`, `hqs`, `hlong`, `hout`.

Counts of the ideal-model adversary `advT S oR pkSeedDist n` (`Ideal/Realize/Tcr.lean`) in the
form of `TcrAdv`'s bound predicates, for a forger with at most `qf` compression queries, at most
`qs` signing queries, signed messages and forged message of at most `ℓ` bytes:

* first phase: no compression query; challenge and collection queries each at most
  `tcrTargets Link.vp` (the router stops at that many recorded calls, `routeHF_cap`); every
  collection query has `(22 + 16·len + 8)/64 = 9` blocks after the first, at most;
* second phase: at most
  `qf + H·thashCost len + (qs + 1)·hmsgCost ℓ` compression queries, where
  `H = keygenHashes + qs·signHashes + (1 + 2·verifyHashes)` is the hash-query count of the open
  program (`tcrMOpenP_hashes`, the count of `Reduction.Open.tcrM_phase2_open_hashes`), every hash
  query is charged as a `Thash` chain on `len` values (`thashCost len = 11`), and the `qs + 1`
  `H_msg` queries (`tcrMOpenP_hmsg`) are charged in addition at `hmsgCost ℓ` each.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security TweakableHash

namespace Ideal.Realize.Tcr
open Reduction Reduction.Open Ideal.Transport

attribute [local irreducible] Reduction.arityTargets Reduction.tcrTargets
-- Never let the elaborator evaluate the (closed, huge) secret-index list of the 128s key
-- structure: statements about closed programs such as `tcrChooseHF Link.vp P₀` otherwise make
-- `whnf` unfold `structSecIdx Link.vp` and exhaust the recursion depth.
attribute [local irreducible] Reduction.Lazy.sparseTable Reduction.Lazy.structSecIdx

set_option linter.unusedVariables false

/-! ## Second phase -/

/-- A `Thash` query of an open program. -/
def isThIdx {ι P K Y : Type} : ℕ ⊕ (ι ⊕ (SecIdx ⊕ PublicHashQuery P K Y)) → Bool
  | .inr (.inr (.inr (.thash _ _ _))) => true
  | _ => false

theorem isThIdx_kind {ι P K Y : Type} (t : ℕ ⊕ (ι ⊕ (SecIdx ⊕ PublicHashQuery P K Y)))
    (h : isThIdx t = true) : Lazy.kind t = .hash := by
  rcases t with n | q | d | q
  · simp [isThIdx] at h
  · simp [isThIdx] at h
  · simp [isThIdx] at h
  · rfl

/-- The hash-query count of the open second-phase program. -/
def hashBudget (qs : ℕ) : ℕ :=
  Lazy.keygenHashes Link.vp + qs * Lazy.signHashes Link.vp + (1 + Resources2.verifyHashes Link.vp * 2)

/-- Compression queries of the second phase. -/
def q₂T (qf qs ℓ : ℕ) : ℕ :=
  qf * 1 + hashBudget qs * thashCost Bmax + (qs + 1) * hmsgCost ℓ

/-- One step of `chainImpl`: a port query costs one compression query, a `Thash` query on at most
`Bmax` values `thashCost Bmax`, an `H_msg` query on at most `ℓ` bytes `hmsgCost ℓ`. -/
theorem chainImpl_step (ℓ : ℕ) (tbl : SecretTable Link.vp P₀)
    (t : (Lazy.OSpec (vp := Link.vp) P₀ (hS St Blk)).Domain)
    (ht : ¬ isBadIdx Bmax ℓ t = true) :
    IsQueryBoundP (chainImpl tbl t) (fun i => i.isRight = true)
      ((if Lazy.kind t = .game then 1 else 0) + (if isThIdx t = true then thashCost Bmax else 0) +
        (if isHmsgIdx t = true then hmsgCost ℓ else 0)) := by
  rcases t with n | q | d | q
  · exact ((isQueryBoundP_query_iff _ _ _).2 fun h => absurd h (by simp)).mono (Nat.zero_le _)
  · simp only [Lazy.kind, isThIdx, isHmsgIdx, ite_true, Bool.false_eq_true, ite_false]
    exact cq_bound q
  · exact (isQueryBoundP_pure _ _ _).mono (Nat.zero_le _)
  · rcases q with ⟨pk, a, xs⟩ | ⟨R, pk, root, M⟩
    · have hx : xs.length ≤ Bmax := by
        simp only [isBadIdx, decide_eq_true_eq, not_lt] at ht; exact ht
      simp only [Lazy.kind, isThIdx, isHmsgIdx, ite_true, Bool.false_eq_true, ite_false,
        reduceCtorEq]
      exact ((thashC_bound pk a xs).mono (thashCost_mono hx)).mono (by omega)
    · have hM : M.length ≤ ℓ := by
        simp only [isBadIdx, decide_eq_true_eq, not_lt] at ht; exact ht
      simp only [Lazy.kind, isThIdx, isHmsgIdx, ite_true, Bool.false_eq_true, ite_false,
        reduceCtorEq]
      exact ((hmsgC_bound R pk root M).mono (hmsgCost_mono hM)).mono (by omega)

variable (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) {qf qs ℓ : ℕ}

/-- The forger hypotheses, transferred to the typed port forger `typedP codec₀ S.main`. -/
theorem typedP_port (hqf : ∀ pk, IsQueryBoundP (S.main pk)
      (fun i => isPortQ (S := List Byte) i = true) qf) (pk : PublicKeyCore P₀.core) :
    IsQueryBoundP (typedP (vp := Link.vp) (prims := P₀) codec₀ S.main pk)
      (fun i => isPortQ (S := GeneralScheme.SignatureCore Link.vp P₀.core) i = true) qf :=
  typedP_bound (vp := Link.vp) (prims := P₀) codec₀ (isPortQ (S := List Byte))
    (isPortQ (S := GeneralScheme.SignatureCore Link.vp P₀.core)) (fun _ _ _ => ⟨rfl, rfl, rfl⟩)
    S.main pk qf (hqf _)

theorem typedP_sign (hqs : ∀ pk, IsQueryBoundP (S.main pk)
      (fun i => isSignQ (S := List Byte) i = true) qs) (pk : PublicKeyCore P₀.core) :
    IsQueryBoundP (typedP (vp := Link.vp) (prims := P₀) codec₀ S.main pk)
      (fun i => isSignQ (S := GeneralScheme.SignatureCore Link.vp P₀.core) i = true) qs :=
  typedP_bound (vp := Link.vp) (prims := P₀) codec₀ (isSignQ (S := List Byte))
    (isSignQ (S := GeneralScheme.SignatureCore Link.vp P₀.core)) (fun _ _ _ => ⟨rfl, rfl, rfl⟩)
    S.main pk qs (hqs _)

theorem typedP_long (hlong : ∀ pk, IsQueryBoundP (S.main pk)
      (fun i => isLongQ (S := List Byte) ℓ i = true) 0) (pk : PublicKeyCore P₀.core) :
    IsQueryBoundP (typedP (vp := Link.vp) (prims := P₀) codec₀ S.main pk)
      (fun i => isLongQ (S := GeneralScheme.SignatureCore Link.vp P₀.core) ℓ i = true) 0 :=
  typedP_bound (vp := Link.vp) (prims := P₀) codec₀ (isLongQ (S := List Byte) ℓ)
    (isLongQ (S := GeneralScheme.SignatureCore Link.vp P₀.core) ℓ) (fun _ _ _ => ⟨rfl, rfl, rfl⟩)
    S.main pk 0 (hlong _)

theorem typedP_outLen (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ)
    (pk : PublicKeyCore P₀.core) :
    ∀ z ∈ support (typedP (vp := Link.vp) (prims := P₀) codec₀ S.main pk), z.1.length ≤ ℓ := by
  intro z hz
  obtain ⟨out, hout', he⟩ := typedP_out (vp := Link.vp) (prims := P₀) codec₀ S.main pk z hz
  rw [he]; exact hout _ out hout'

theorem okLen_le (xs : List P₀.Y) (h : OkLen Link.vp xs) : xs.length ≤ Bmax := by
  rcases h with h | h | h | h <;> rw [h] <;> decide

/-- **Compression queries of the second phase**, for every secret table, every stored list of
entries of at most `len` values, every public seed. -/
theorem forgeP_bound (n : ℕ)
    (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List Byte) i = true) qf)
    (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List Byte) i = true) qs)
    (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQ (S := List Byte) ℓ i = true) 0)
    (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ)
    (tbl : SecretTable Link.vp P₀) (L : List (P₀.AdrsKey × List P₀.Y))
    (hL : ∀ q ∈ L, q.2.length ≤ Bmax) (pk : P₀.PkSeed) :
    IsQueryBoundP (forgeP S oR n tbl L pk) (fun i => i.isRight = true) (q₂T qf qs ℓ) := by
  have hX := qb_simulateQ_classes (p₀ := fun t => isBadIdx Bmax ℓ t = true)
    (p₁ := fun t => Lazy.kind t = .game) (p₂ := fun t => isThIdx t = true)
    (p₃ := fun t => isHmsgIdx t = true) (q := fun i : (unifSpec + hS St Blk).Domain => i.isRight = true)
    (impl := chainImpl tbl) 1 (thashCost Bmax) (hmsgCost ℓ)
    (fun t ht => chainImpl_step ℓ tbl t ht)
    (tcrMOpenP_bad (vp := Link.vp) (prims := P₀) (optRand₀ oR) (typedP codec₀ S.main) L pk Bmax ℓ
      okLen_le hL (typedP_long S hlong) (typedP_outLen S hout))
    (tcrMOpenP_port (vp := Link.vp) (prims := P₀) (optRand₀ oR) (typedP codec₀ S.main) L pk qf
      (typedP_port S hqf))
    (IsQueryBoundP.of_imp (fun t ht => isThIdx_kind t ht)
      (tcrMOpenP_hashes (vp := Link.vp) (prims := P₀) (optRand₀ oR) (typedP codec₀ S.main) L pk qs
        (typedP_sign S hqs)))
    (tcrMOpenP_hmsg (vp := Link.vp) (prims := P₀) (optRand₀ oR) (typedP codec₀ S.main) L pk qs
      (typedP_sign S hqs))
  unfold forgeP
  exact (isQueryBoundP_bind (m := 0) hX fun _ _ => isQueryBoundP_pure _ _ _).mono (by
    unfold q₂T hashBudget; omega)

/-! ## First phase -/

/-- Continuation blocks of a collection query on at most `len` values. -/
def tcrL : ℕ := (22 + 16 * Bmax + 8) / 64

variable (pkSeedDist : ProbComp (Bytes 16)) (n : ℕ)

/-- `IsQueryBoundP.of_imp` with the decidability instances unified rather than synthesized. -/
theorem of_imp' {ι α : Type} {spec : OracleSpec ι} {oa : OracleComp spec α} {p p' : ι → Prop}
    {_ : DecidablePred p} {_ : DecidablePred p'} {k : ℕ} (himp : ∀ t, p t → p' t)
    (h : IsQueryBoundP oa p' k) : IsQueryBoundP oa p k :=
  IsQueryBoundP.of_imp himp h

/-- The first phase, as a program over the selection interface of the class game. -/
abbrev Ph1 (n : ℕ) : Type := OracleComp (TcrP1Spec P₀ n) (TcrP1State Link.vp P₀)

/-- `choose` of the ideal-model adversary is the embedded first phase (kernel check). -/
theorem advT_choose : (advT S oR pkSeedDist n).choose =
    simulateQ embImpl (tcrPhase1 Link.vp P₀ n : Ph1 n) := by krfl

/-- Game queries (challenge and collection) of the first phase: at most `tcrTargets`. -/
theorem tcrPhase1_cap (oa : Ph1 n) (hoa : oa = tcrPhase1 Link.vp P₀ n) :
    IsQueryBoundP oa (fun t => t.isRight = true) (tcrTargets Link.vp) := by
  delta tcrPhase1 at hoa
  generalize tcrChooseHF Link.vp P₀ = c at hoa
  subst hoa
  have h := routeHF_cap (PkSeed := P₀.PkSeed) (fun xs : List P₀.Y => xs.length = n)
    (tcrTargets Link.vp) c []
  rw [List.length_nil, Nat.sub_zero] at h
  exact h

/-- No challenge or collection query of the first phase is on more than `len` values. -/
theorem tcrPhase1_len (oa : Ph1 n) (hoa : oa = tcrPhase1 Link.vp P₀ n) :
    IsQueryBoundP oa (fun t => bad1 (fun xs : List P₀.Y => xs.length = n) Bmax t = true) 0 := by
  delta tcrPhase1 at hoa
  generalize hc : tcrChooseHF Link.vp P₀ = c at hoa
  subst hoa
  exact routeHF_len (PkSeed := P₀.PkSeed) _ _ Bmax c
    (hc ▸ tcrChooseHF_len (vp := Link.vp) (prims := P₀) Bmax okLen_le) []

/-- The first phase makes no compression query. -/
theorem advT_chooseBound : (advT S oR pkSeedDist n).ChooseBound 0 := by
  unfold TcrAdv.ChooseBound
  rw [advT_choose]
  generalize (tcrPhase1 Link.vp P₀ n : Ph1 n) = oa
  exact emb_noH (fun i => (F128T pkSeedDist n).isH i = true) (fun t => by
    rcases t with m | t <;> simp only [embIdx, THFam.isH] <;> decide) oa

/-- The first phase makes at most `tcrTargets` challenge queries. -/
theorem advT_chalBound : (advT S oR pkSeedDist n).ChalBound (tcrTargets Link.vp) := by
  unfold TcrAdv.ChalBound
  rw [advT_choose]
  generalize hoa : (tcrPhase1 Link.vp P₀ n : Ph1 n) = oa
  have h1 := tcrPhase1_cap n oa hoa.symm
  refine emb_bound (fun i => (F128T pkSeedDist n).isChal i = true) oa _
    (of_imp' (fun t ht => ?_) h1)
  rcases t with m | t
  · simp only [embIdx, THFam.isChal] at ht
    exact absurd ht (by decide)
  · rfl

/-- The first phase makes at most `tcrTargets` collection queries. -/
theorem advT_collBound : (advT S oR pkSeedDist n).CollBound (tcrTargets Link.vp) := by
  unfold TcrAdv.CollBound
  rw [advT_choose]
  generalize hoa : (tcrPhase1 Link.vp P₀ n : Ph1 n) = oa
  have h1 := tcrPhase1_cap n oa hoa.symm
  refine emb_bound (fun i => (F128T pkSeedDist n).isColl i = true) oa _
    (of_imp' (fun t ht => ?_) h1)
  rcases t with m | t
  · simp only [embIdx, THFam.isColl] at ht
    exact absurd ht (by decide)
  · rfl

/-- Every collection query of the first phase has at most `tcrL = 9` blocks after the first. -/
theorem advT_collLen : (advT S oR pkSeedDist n).CollLen tcrL := by
  classical
  unfold TcrAdv.CollLen
  rw [← isQueryBoundP_zero_iff, advT_choose]
  generalize hoa : (tcrPhase1 Link.vp P₀ n : Ph1 n) = oa
  have h1 := tcrPhase1_len n oa hoa.symm
  refine emb_bound _ oa 0 (of_imp' (fun t ht => ?_) h1)
  rcases t with m | ⟨tw, xs⟩ | ⟨u, tw, xs⟩
  · simp [embIdx] at ht
  · simp [embIdx] at ht
  · simp only [embIdx, F128T, not_le] at ht
    have hl : (tblocks tw xs).2.length = (22 + 16 * xs.length + 8) / 64 := tblocks_snd_length _ _
    simp only [bad1, decide_eq_true_eq]
    unfold tcrL at ht
    omega

/-- The second phase makes at most `q₂T qf qs ℓ` compression queries, at every state. -/
theorem advT_forgeBound
    (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List Byte) i = true) qf)
    (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List Byte) i = true) qs)
    (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQ (S := List Byte) ℓ i = true) 0)
    (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ) :
    (advT S oR pkSeedDist n).ForgeBound (q₂T qf qs ℓ) := fun st pk =>
  forgeP_bound S oR n hqf hqs hlong hout st.1 (clampL Bmax st.2) (clampL_mem _ _) pk

/-! ## The realisers -/

/-- **The query parameters of the class-TCR realisers**: no first-phase compression query,
`tcrTargets` challenge and collection queries, `tcrL` continuation blocks, `q₂T qf qs ℓ`
second-phase compression queries. -/
def tcrP (qf qs ℓ : ℕ) : P5 where
  q₁ := 0
  qch := tcrTargets Link.vp
  qc := tcrTargets Link.vp
  L := tcrL
  q₂ := q₂T qf qs ℓ

/-- **Class-TCR realiser, SUF family, every arity `n`.** -/
noncomputable def realizesTcrS
    (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List Byte) i = true) qf)
    (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List Byte) i = true) qs)
    (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQ (S := List Byte) ℓ i = true) 0)
    (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ) :
    RealizesTcr pkSeedDist n (fun g => Reduction.bTcrArM n (S.typedS (optRandU oR) pkSeedDist g))
      (tcrP qf qs ℓ) where
  A := advT S oR pkSeedDist n
  eq := advT_eq S oR pkSeedDist n
  hq₁ := advT_chooseBound S oR pkSeedDist n
  hch := advT_chalBound S oR pkSeedDist n
  hc := advT_collBound S oR pkSeedDist n
  hL := advT_collLen S oR pkSeedDist n
  hq₂ := advT_forgeBound S oR pkSeedDist n hqf hqs hlong hout

/-- The EUF typed forger is the SUF one. -/
theorem typedE_eq_typedS (g : CF St Blk) :
    S.typedE (optRandU oR) pkSeedDist g = S.typedS (optRandU oR) pkSeedDist g := rfl

/-- **Class-TCR realiser, EUF family, every arity `n`.** -/
noncomputable def realizesTcrE
    (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List Byte) i = true) qf)
    (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List Byte) i = true) qs)
    (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQ (S := List Byte) ℓ i = true) 0)
    (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ) :
    RealizesTcr pkSeedDist n (fun g => Reduction.bTcrArM n (S.typedE (optRandU oR) pkSeedDist g))
      (tcrP qf qs ℓ) :=
  realizesTcrS S oR pkSeedDist n hqf hqs hlong hout

/-! ## Parameter bounds -/

/-- The cap on the realisers' compression queries: the second-phase count. -/
def QcT (qf qs ℓ : ℕ) : ℕ := q₂T qf qs ℓ

/-- **`P5.Le` for the class-TCR parameters**, at `Qc = q₂T qf qs ℓ` and `N = tcrTargets`. -/
theorem tcrP_le (qf qs ℓ : ℕ) : (tcrP qf qs ℓ).Le (QcT qf qs ℓ) (tcrTargets Link.vp) := by
  refine ⟨Nat.zero_le _, le_rfl, le_rfl, ?_, le_rfl⟩
  show tcrL ≤ 10
  decide

/-- `P5.Le` at any larger caps. -/
theorem tcrP_le_of (qf qs ℓ Qc N : ℕ) (hQ : QcT qf qs ℓ ≤ Qc) (hN : tcrTargets Link.vp ≤ N) :
    (tcrP qf qs ℓ).Le Qc N := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := tcrP_le qf qs ℓ
  exact ⟨h1.trans hQ, h2.trans hN, h3.trans hN, h4, h5.trans hQ⟩

/-- At SLH-DSA-SHA2-128s: `q₂T qf qs ℓ = qf + (277681 + qs·2007385)·11 + (qs+1)·((ℓ+56)/64+3)`. -/
theorem q₂T_128s (qf qs ℓ : ℕ) :
    q₂T qf qs ℓ = qf + (269824 + qs * 2007385 + 7857) * 11 + (qs + 1) * ((ℓ + 56) / 64 + 3) := by
  have h1 := Reduction.keygenHashes_128s
  have h2 := Reduction.signHashes_128s
  have h3 := Reduction.Resources2.verifyHashes_128s
  have h4 : thashCost Bmax = 11 := by decide
  unfold q₂T hashBudget hmsgCost
  rw [h1, h2, h3, h4]
  ring

/-- `tcrTargets` at 128s is below `2^80`, and `tcrL = 9`. -/
theorem tcrP_128s_consts : tcrTargets Link.vp < 2 ^ 80 ∧ tcrL = 9 :=
  ⟨Reduction.Resources.tcrTargets_128s_bounds.2, by decide⟩

/-- A simple closed upper bound on the second-phase count at 128s. -/
theorem q₂T_le (qf qs ℓ : ℕ) : q₂T qf qs ℓ ≤ qf + (qs + 1) * (25135729 + (ℓ + 56) / 64) := by
  rw [q₂T_128s]
  nlinarith [Nat.zero_le qs, Nat.zero_le ((ℓ + 56) / 64)]

/-- `P5.Le` at `Qc ≥ qf + (qs+1)·(25135729 + (ℓ+56)/64)` and `N = 2^81` (the `N` of the closed
`suf_final_2_60_2_20` / `_2_80_2_40`; any `N ≥ 2^80` works). -/
theorem tcrP_le_2_81 (qf qs ℓ Qc : ℕ) (hQ : qf + (qs + 1) * (25135729 + (ℓ + 56) / 64) ≤ Qc) :
    (tcrP qf qs ℓ).Le Qc (2 ^ 81) :=
  tcrP_le_of qf qs ℓ Qc _ ((q₂T_le qf qs ℓ).trans hQ)
    (tcrP_128s_consts.1.le.trans (Nat.pow_le_pow_right (by norm_num) (by norm_num)))

/-! ## The eight headline realisers (four arities, SUF and EUF) -/

section Headline

variable {qf qs ℓ : ℕ}
  (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List Byte) i = true) qf)
  (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List Byte) i = true) qs)
  (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQ (S := List Byte) ℓ i = true) 0)
  (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ)

/-- `F` (arity 1), SUF. -/
noncomputable def realizesTcrF_S : RealizesTcr pkSeedDist 1
    (fun g => Reduction.bTcrArM 1 (S.typedS (optRandU oR) pkSeedDist g)) (tcrP qf qs ℓ) :=
  realizesTcrS S oR pkSeedDist 1 hqf hqs hlong hout
/-- `H` (arity 2), SUF. -/
noncomputable def realizesTcrH_S : RealizesTcr pkSeedDist 2
    (fun g => Reduction.bTcrArM 2 (S.typedS (optRandU oR) pkSeedDist g)) (tcrP qf qs ℓ) :=
  realizesTcrS S oR pkSeedDist 2 hqf hqs hlong hout
/-- `T_len`, SUF. -/
noncomputable def realizesTcrLen_S : RealizesTcr pkSeedDist Link.vp.params.len
    (fun g => Reduction.bTcrArM Link.vp.params.len (S.typedS (optRandU oR) pkSeedDist g))
    (tcrP qf qs ℓ) :=
  realizesTcrS S oR pkSeedDist Link.vp.params.len hqf hqs hlong hout
/-- `T_k`, SUF. -/
noncomputable def realizesTcrK_S : RealizesTcr pkSeedDist Link.vp.params.k
    (fun g => Reduction.bTcrArM Link.vp.params.k (S.typedS (optRandU oR) pkSeedDist g))
    (tcrP qf qs ℓ) :=
  realizesTcrS S oR pkSeedDist Link.vp.params.k hqf hqs hlong hout
/-- `F` (arity 1), EUF. -/
noncomputable def realizesTcrF_E : RealizesTcr pkSeedDist 1
    (fun g => Reduction.bTcrArM 1 (S.typedE (optRandU oR) pkSeedDist g)) (tcrP qf qs ℓ) :=
  realizesTcrE S oR pkSeedDist 1 hqf hqs hlong hout
/-- `H` (arity 2), EUF. -/
noncomputable def realizesTcrH_E : RealizesTcr pkSeedDist 2
    (fun g => Reduction.bTcrArM 2 (S.typedE (optRandU oR) pkSeedDist g)) (tcrP qf qs ℓ) :=
  realizesTcrE S oR pkSeedDist 2 hqf hqs hlong hout
/-- `T_len`, EUF. -/
noncomputable def realizesTcrLen_E : RealizesTcr pkSeedDist Link.vp.params.len
    (fun g => Reduction.bTcrArM Link.vp.params.len (S.typedE (optRandU oR) pkSeedDist g))
    (tcrP qf qs ℓ) :=
  realizesTcrE S oR pkSeedDist Link.vp.params.len hqf hqs hlong hout
/-- `T_k`, EUF. -/
noncomputable def realizesTcrK_E : RealizesTcr pkSeedDist Link.vp.params.k
    (fun g => Reduction.bTcrArM Link.vp.params.k (S.typedE (optRandU oR) pkSeedDist g))
    (tcrP qf qs ℓ) :=
  realizesTcrE S oR pkSeedDist Link.vp.params.k hqf hqs hlong hout

end Headline

end Ideal.Realize.Tcr


#print axioms Ideal.Realize.Tcr.chainImpl_step
#print axioms Ideal.Realize.Tcr.forgeP_bound
#print axioms Ideal.Realize.Tcr.advT_chooseBound
#print axioms Ideal.Realize.Tcr.advT_chalBound
#print axioms Ideal.Realize.Tcr.advT_collBound
#print axioms Ideal.Realize.Tcr.advT_collLen
#print axioms Ideal.Realize.Tcr.advT_forgeBound
#print axioms Ideal.Realize.Tcr.realizesTcrS
#print axioms Ideal.Realize.Tcr.realizesTcrE
#print axioms Ideal.Realize.Tcr.tcrP_le
#print axioms Ideal.Realize.Tcr.tcrP_le_of
#print axioms Ideal.Realize.Tcr.q₂T_128s
#print axioms Ideal.Realize.Tcr.tcrP_128s_consts
#print axioms Ideal.Realize.Tcr.q₂T_le
#print axioms Ideal.Realize.Tcr.tcrP_le_2_81
#print axioms Ideal.Realize.Tcr.realizesTcrF_S
#print axioms Ideal.Realize.Tcr.realizesTcrH_S
#print axioms Ideal.Realize.Tcr.realizesTcrLen_S
#print axioms Ideal.Realize.Tcr.realizesTcrK_S
#print axioms Ideal.Realize.Tcr.realizesTcrF_E
#print axioms Ideal.Realize.Tcr.realizesTcrH_E
#print axioms Ideal.Realize.Tcr.realizesTcrLen_E
#print axioms Ideal.Realize.Tcr.realizesTcrK_E
