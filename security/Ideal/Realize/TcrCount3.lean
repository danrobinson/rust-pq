import Ideal.Realize.Tcr3

/-!
# The answer-storing class-TCR realisers: query counts and realiser definitions

Counts of `advT3 S oR pkSeedDist n` (`Ideal/Realize/Tcr3.lean`):

* first phase: no compression query; at most `tcrTargets` challenge and collection queries
  (`routeHFA_cap`); every collection query has at most `tcrL = 9` blocks after the first
  (`routeHFA_len`) — as for `advT`;
* second phase, for EVERY state: at most
  `q₂T3 qf qs ℓ = qf + 2·verifyHashes·thashCost len + (qs + 1)·hmsgCost ℓ`
  compression queries (`= qf + 86416 + (qs+1)·(⌊(ℓ+56)/64⌋ + 3)` at 128s, `q₂T3_128s`): the
  forger's own queries, the `Thash` evaluations of verifying the forgery (with the comparison
  value of the collision search) and the `H_msg` chains; key regeneration and signing make none
  (`tcrMOpenPS_th`).  The realisers of `TcrCount.lean` make `q₂T qf qs ℓ =
  qf + (277681 + qs·2007385)·11 + (qs+1)·hmsgCost ℓ`.

Realisers: `realizesTcr3S` / `realizesTcr3E` (every arity), the same adversary families as
`realizesTcrS` / `realizesTcrE`.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security TweakableHash

namespace Ideal.Realize.Tcr
open Reduction Reduction.Open Ideal.Transport

attribute [local irreducible] Reduction.arityTargets Reduction.tcrTargets
attribute [local irreducible] Reduction.Lazy.sparseTable Reduction.Lazy.structSecIdx

set_option linter.unusedVariables false

/-- Compression queries of the second phase of the answer-storing realiser. -/
def q₂T3 (qf qs ℓ : ℕ) : ℕ :=
  qf * 1 + (Resources2.verifyHashes Link.vp * 2) * thashCost Bmax + (qs + 1) * hmsgCost ℓ

variable (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) {qf qs ℓ : ℕ}

/-- **Compression queries of the second phase**, for every secret table, every stored list of
entries of at most `len` values, every store, every public seed. -/
theorem forgeP3_bound (n : ℕ)
    (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List Byte) i = true) qf)
    (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List Byte) i = true) qs)
    (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQ (S := List Byte) ℓ i = true) 0)
    (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ)
    (tbl : SecretTable Link.vp P₀) (L : List (P₀.AdrsKey × List P₀.Y))
    (hL : ∀ q ∈ L, q.2.length ≤ Bmax) (Sto : Store P₀) (pk : P₀.PkSeed) :
    IsQueryBoundP (forgeP3G dT dH S oR n tbl L Sto pk) (fun i => i.isRight = true)
      (q₂T3 qf qs ℓ) := by
  have hX := qb_simulateQ_classes (p₀ := fun t => isBadIdx Bmax ℓ t = true)
    (p₁ := fun t => Lazy.kind t = .game) (p₂ := fun t => isThIdx t = true)
    (p₃ := fun t => isHmsgIdx t = true)
    (q := fun i : (unifSpec + hS St Blk).Domain => i.isRight = true)
    (impl := chainImpl tbl) 1 (thashCost Bmax) (hmsgCost ℓ)
    (fun t ht => chainImpl_step ℓ tbl t ht)
    (tcrMOpenPS_bad (vp := Link.vp) (prims := P₀) (optRand₀ oR) (typedP codec₀ S.main) L Sto pk
      Bmax ℓ okLen_le hL (typedP_long S hlong) (typedP_outLen S hout))
    (tcrMOpenPS_port (vp := Link.vp) (prims := P₀) (optRand₀ oR) (typedP codec₀ S.main) L Sto pk
      qf (typedP_port S hqf))
    (tcrMOpenPS_th (vp := Link.vp) (prims := P₀) (optRand₀ oR) (typedP codec₀ S.main) L Sto pk
      qs (typedP_sign S hqs))
    (tcrMOpenPS_hmsg (vp := Link.vp) (prims := P₀) (optRand₀ oR) (typedP codec₀ S.main) L Sto pk
      qs (typedP_sign S hqs))
  unfold forgeP3G
  exact (isQueryBoundP_bind (m := 0) hX fun _ _ => isQueryBoundP_pure _ _ _).mono (by
    unfold q₂T3; omega)

variable (pkSeedDist : ProbComp (Bytes 16)) (n : ℕ)

/-- The recording first phase, as a program over the selection interface of the class game. -/
abbrev Ph1A (n : ℕ) : Type := OracleComp (TcrP1Spec P₀ n) (TcrP1StateA Link.vp P₀)

theorem advT3_choose : (advT3 S oR pkSeedDist n).choose =
    simulateQ embImpl (tcrPhase1A Link.vp P₀ n : Ph1A n) := by krfl

theorem tcrPhase1A_cap (oa : Ph1A n) (hoa : oa = tcrPhase1A Link.vp P₀ n) :
    IsQueryBoundP oa (fun t => t.isRight = true) (tcrTargets Link.vp) := by
  delta tcrPhase1A at hoa
  generalize tcrChooseHF Link.vp P₀ = c at hoa
  subst hoa
  have h := routeHFA_cap (PkSeed := P₀.PkSeed) (fun xs : List P₀.Y => xs.length = n)
    (tcrTargets Link.vp) c [] []
  rw [List.length_nil, Nat.sub_zero] at h
  exact h

theorem tcrPhase1A_len (oa : Ph1A n) (hoa : oa = tcrPhase1A Link.vp P₀ n) :
    IsQueryBoundP oa (fun t => bad1 (fun xs : List P₀.Y => xs.length = n) Bmax t = true) 0 := by
  delta tcrPhase1A at hoa
  generalize hc : tcrChooseHF Link.vp P₀ = c at hoa
  subst hoa
  exact routeHFA_len (PkSeed := P₀.PkSeed) _ _ Bmax c
    (hc ▸ tcrChooseHF_len (vp := Link.vp) (prims := P₀) Bmax okLen_le) ([], [])

theorem advT3_chooseBound : (advT3 S oR pkSeedDist n).ChooseBound 0 := by
  unfold TcrAdv.ChooseBound
  rw [advT3_choose]
  generalize (tcrPhase1A Link.vp P₀ n : Ph1A n) = oa
  exact emb_noH (fun i => (F128T pkSeedDist n).isH i = true) (fun t => by
    rcases t with m | t <;> simp only [embIdx, THFam.isH] <;> decide) oa

theorem advT3_chalBound : (advT3 S oR pkSeedDist n).ChalBound (tcrTargets Link.vp) := by
  unfold TcrAdv.ChalBound
  rw [advT3_choose]
  generalize hoa : (tcrPhase1A Link.vp P₀ n : Ph1A n) = oa
  have h1 := tcrPhase1A_cap n oa hoa.symm
  refine emb_bound (fun i => (F128T pkSeedDist n).isChal i = true) oa _
    (of_imp' (fun t ht => ?_) h1)
  rcases t with m | t
  · simp only [embIdx, THFam.isChal] at ht
    exact absurd ht (by decide)
  · rfl

theorem advT3_collBound : (advT3 S oR pkSeedDist n).CollBound (tcrTargets Link.vp) := by
  unfold TcrAdv.CollBound
  rw [advT3_choose]
  generalize hoa : (tcrPhase1A Link.vp P₀ n : Ph1A n) = oa
  have h1 := tcrPhase1A_cap n oa hoa.symm
  refine emb_bound (fun i => (F128T pkSeedDist n).isColl i = true) oa _
    (of_imp' (fun t ht => ?_) h1)
  rcases t with m | t
  · simp only [embIdx, THFam.isColl] at ht
    exact absurd ht (by decide)
  · rfl

theorem advT3_collLen : (advT3 S oR pkSeedDist n).CollLen tcrL := by
  classical
  unfold TcrAdv.CollLen
  rw [← isQueryBoundP_zero_iff, advT3_choose]
  generalize hoa : (tcrPhase1A Link.vp P₀ n : Ph1A n) = oa
  have h1 := tcrPhase1A_len n oa hoa.symm
  refine emb_bound _ oa 0 (of_imp' (fun t ht => ?_) h1)
  rcases t with m | ⟨tw, xs⟩ | ⟨u, tw, xs⟩
  · simp [embIdx] at ht
  · simp [embIdx] at ht
  · simp only [embIdx, F128T, not_le] at ht
    have hl : (tblocks tw xs).2.length = (22 + 16 * xs.length + 8) / 64 := tblocks_snd_length _ _
    simp only [bad1, decide_eq_true_eq]
    unfold tcrL at ht
    omega

theorem advT3_forgeBound
    (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List Byte) i = true) qf)
    (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List Byte) i = true) qs)
    (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQ (S := List Byte) ℓ i = true) 0)
    (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ) :
    (advT3 S oR pkSeedDist n).ForgeBound (q₂T3 qf qs ℓ) := fun st pk =>
  forgeP3_bound S oR n hqf hqs hlong hout st.1 (clampL Bmax st.2.1) (clampL_mem _ _) st.2.2 pk

/-! ## The realisers -/

/-- **Query parameters of the answer-storing class-TCR realisers.** -/
def tcrP3 (qf qs ℓ : ℕ) : P5 where
  q₁ := 0
  qch := tcrTargets Link.vp
  qc := tcrTargets Link.vp
  L := tcrL
  q₂ := q₂T3 qf qs ℓ

/-- **Answer-storing class-TCR realiser, SUF family, every arity `n`.** -/
noncomputable def realizesTcr3S
    (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List Byte) i = true) qf)
    (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List Byte) i = true) qs)
    (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQ (S := List Byte) ℓ i = true) 0)
    (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ) :
    RealizesTcr pkSeedDist n (fun g => Reduction.bTcrArM n (S.typedS (optRandU oR) pkSeedDist g))
      (tcrP3 qf qs ℓ) where
  A := advT3 S oR pkSeedDist n
  eq := advT3_eq S oR pkSeedDist n
  hq₁ := advT3_chooseBound S oR pkSeedDist n
  hch := advT3_chalBound S oR pkSeedDist n
  hc := advT3_collBound S oR pkSeedDist n
  hL := advT3_collLen S oR pkSeedDist n
  hq₂ := advT3_forgeBound S oR pkSeedDist n hqf hqs hlong hout

/-- **Answer-storing class-TCR realiser, EUF family, every arity `n`.** -/
noncomputable def realizesTcr3E
    (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List Byte) i = true) qf)
    (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List Byte) i = true) qs)
    (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQ (S := List Byte) ℓ i = true) 0)
    (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ) :
    RealizesTcr pkSeedDist n (fun g => Reduction.bTcrArM n (S.typedE (optRandU oR) pkSeedDist g))
      (tcrP3 qf qs ℓ) :=
  realizesTcr3S S oR pkSeedDist n hqf hqs hlong hout

/-! ## Parameter bounds -/

/-- At SLH-DSA-SHA2-128s: `q₂T3 qf qs ℓ = qf + 86416 + (qs+1)·((ℓ+56)/64+3)`. -/
theorem q₂T3_128s (qf qs ℓ : ℕ) :
    q₂T3 qf qs ℓ = qf + 86416 + (qs + 1) * ((ℓ + 56) / 64 + 3) := by
  have h3 := Reduction.Resources2.verifyHashes_128s
  have h4 : thashCost Bmax = 11 := by decide
  unfold q₂T3 hmsgCost
  rw [h3, h4]
  ring

/-- A closed upper bound on the second-phase count at 128s. -/
theorem q₂T3_le (qf qs ℓ : ℕ) : q₂T3 qf qs ℓ ≤ qf + (qs + 1) * (86419 + (ℓ + 56) / 64) := by
  rw [q₂T3_128s]
  nlinarith [Nat.zero_le qs, Nat.zero_le ((ℓ + 56) / 64)]

/-- Never above the count of the recomputing realisers. -/
theorem q₂T3_le_q₂T (qf qs ℓ : ℕ) : q₂T3 qf qs ℓ ≤ q₂T qf qs ℓ := by
  rw [q₂T3_128s, q₂T_128s]
  nlinarith [Nat.zero_le qs, Nat.zero_le ((ℓ + 56) / 64)]

/-- `P5.Le` of the answer-storing parameters at any caps above the recomputing ones'. -/
theorem tcrP3_le_of (qf qs ℓ Qc N : ℕ) (hQ : QcT qf qs ℓ ≤ Qc) (hN : tcrTargets Link.vp ≤ N) :
    (tcrP3 qf qs ℓ).Le Qc N := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := tcrP_le_of qf qs ℓ Qc N hQ hN
  exact ⟨h1, h2, h3, h4, (q₂T3_le_q₂T qf qs ℓ).trans h5⟩

end Ideal.Realize.Tcr

#print axioms Ideal.Realize.Tcr.forgeP3_bound
#print axioms Ideal.Realize.Tcr.advT3_chooseBound
#print axioms Ideal.Realize.Tcr.advT3_chalBound
#print axioms Ideal.Realize.Tcr.advT3_collBound
#print axioms Ideal.Realize.Tcr.advT3_collLen
#print axioms Ideal.Realize.Tcr.advT3_forgeBound
#print axioms Ideal.Realize.Tcr.realizesTcr3S
#print axioms Ideal.Realize.Tcr.realizesTcr3E
#print axioms Ideal.Realize.Tcr.q₂T3_128s
#print axioms Ideal.Realize.Tcr.q₂T3_le
#print axioms Ideal.Realize.Tcr.q₂T3_le_q₂T
#print axioms Ideal.Realize.Tcr.tcrP3_le_of
