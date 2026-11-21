import Ideal.Realize.WotsReal
import Ideal.Realize.WotsLen

/-!
# The three WOTS-chain realisers (SM-UD, SM-PRE, SM-TCR on `F`), SUF and EUF

For an ideal-model forger `S : ForgerI`, a table-independent `opt_rand` family `optRandU oR` and
any public-seed distribution, the Reduction's adversaries
`rUd / rPre / rTcrT pkSeedDist (Lazy.bWotsS (S.typedS (optRandU oR) pkSeedDist g))` (and the
same at `S.typedE`) are, for every table `g`, the instantiations at `g` of ONE ideal-model
adversary (`udAdv`, `preAdv`, `tcrAdv`):

* first phase: the Reduction's (forger-free, hash-free) first phase over the reference bundle
  `P0`, embedded (`embImpl`): no compression query;
* second phase: `udDist` / `preInv` / `tcrForge` (`WotsReal.lean`): the forger's own compression
  queries passed through, every hash evaluation of the reduction replaced by its compression
  chain.

Headline definitions: `realizesUd`, `realizesPre`, `realizesWotsTcr` (SUF) and `realizesUdE`,
`realizesPreE`, `realizesWotsTcrE` (EUF), with parameters `pU`, `pP`, `pW`; bounds in the shape of
`P5.Le`: `pU_le`, `pP_le`, `pW_le` (`Qc qf qs ℓ`, `Nw`).
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security TweakableHash

namespace Ideal.Realize.Wots

open Reduction Reduction.Open Reduction.Lazy Reduction.Resources2 Ideal.Realize Ideal.Transport

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! ## A forger over the reference bundle (only its first phases are used, which do not depend
on the forger) -/

/-- A fixed forger over `P0` (outputs a constant forgery). -/
noncomputable def dF (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    (pkSeedDist : ProbComp (Bytes 16)) : Forger Link.vp P0 (optRand₀ oR) pkSeedDist :=
  ⟨fun _ => pure ([], constSig default)⟩

/-! ## Continuation length of the collection queries -/

/-- Blocks after the first of a `Thash` evaluation on `len` values: `9` at 128s. -/
abbrev Lw : ℕ := (22 + 16 * Link.vp.params.len + 8) / 64

theorem Lw_eq : Lw = 9 := by decide

theorem tblocks_okLen (a : Bytes 22) (xs : List (Bytes 16)) (h : OkLen Link.vp xs) :
    (tblocks a xs).2.length ≤ Lw := by
  rw [tblocks_snd_length]
  rcases h with h | h | h | h <;> rw [h] <;> decide

/-! ## The first phases, embedded -/

section Phase1

section Gen

variable {A B : Type} {X : OracleSpec (A ⊕ B)} {α : Type}

theorem emb_chal (oa : OracleComp (unifSpec + X) α) (n : ℕ)
    (h : IsQueryBoundP oa isChalI n) :
    IsQueryBoundP (simulateQ (embImpl (X := X)) oa)
      (fun i => (match i with | .inr (.inr (.inl _)) => true | _ => false) = true) n :=
  emb_bound _ oa n (IsQueryBoundP.of_imp (fun t ht => by
    rcases t with n | t | t <;> simp_all [embIdx, isChalI]) h)

theorem emb_coll (oa : OracleComp (unifSpec + X) α) (n : ℕ)
    (h : IsQueryBoundP oa isColl n) :
    IsQueryBoundP (simulateQ (embImpl (X := X)) oa)
      (fun i => (match i with | .inr (.inr (.inr _)) => true | _ => false) = true) n :=
  emb_bound _ oa n (IsQueryBoundP.of_imp (fun t ht => by
    rcases t with n | t | t <;> simp_all [embIdx, isColl]) h)

theorem emb_noComp (oa : OracleComp (unifSpec + X) α) :
    IsQueryBoundP (simulateQ (embImpl (X := X)) oa)
      (fun i => (match i with | .inr (.inl _) => true | _ => false) = true) 0 :=
  emb_noH _ (fun t => by rcases t with n | t <;> simp [embIdx]) oa

end Gen

variable {T : Type} {X : OracleSpec (T ⊕ ((_ : Unit) × P0.AdrsKey × List P0.Y))} {α : Type}

theorem emb_len (oa : OracleComp (unifSpec + X) α)
    (h : IsQueryBoundP oa (badG (vp := Link.vp) (prims := P0) (T := T)) 0) :
    AllQueriesSatisfy (simulateQ (embImpl (X := X)) oa) fun i => match i with
      | .inr (.inr (.inr q)) => (tblocks q.2.1 q.2.2).2.length ≤ Lw
      | _ => True := by
  classical
  refine (isQueryBoundP_zero_iff _ _).1 (emb_bound _ oa 0 (IsQueryBoundP.of_imp (fun t ht => ?_) h))
  rcases t with n | t | q
  · simp [embIdx] at ht
  · simp [embIdx] at ht
  · intro hb
    exact ht (tblocks_okLen _ _ hb)

end Phase1

section GenF

variable {St' Blk' PkSeed Tweak M Y ι : Type} {α : Type}

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

end GenF


/-! ## SM-UD -/

section Ud

variable (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
  (pkSeedDist : ProbComp (Bytes 16))

/-- **The ideal-model SM-UD adversary.** -/
noncomputable def udAdv : WotsUdAdv128 pkSeedDist where
  State := Open.RState Link.vp P0
  pick := simulateQ (embImpl (X := SM_DT_UD_challengeSpec (Bytes 22) (Bytes 16) +
      collSpecC (Bytes 22) (Bytes 16)))
    (rUd (prims := P0) pkSeedDist (Lazy.bWotsS (dF oR pkSeedDist))).pick
  distinguish := udDist S oR

theorem udAdv_inst (g : CF St Blk) :
    rUd pkSeedDist (Lazy.bWotsS (S.typedS (optRandU oR) pkSeedDist g)) =
      instWU (udAdv S oR pkSeedDist) g := by
  rw [stepUd]
  have hc : @Eq (OracleComp (udSpecC (Bytes 22) (Bytes 16)) (Open.RState Link.vp P0))
      (rUd pkSeedDist (Lazy.bWotsS (B₀ S oR pkSeedDist g))).pick
      (simulateQ (instImpl (spec := SM_DT_UD_challengeSpec (Bytes 22) (Bytes 16) +
        collSpecC (Bytes 22) (Bytes 16)) g) (udAdv S oR pkSeedDist).pick) := by
    refine Eq.trans ?_ (instImpl_emb g _).symm
    exact wotsUd_phase1_hashfree_all (prims := P0) ⟨thG g, hmG g, core₀.PRF, core₀.PRFmsg⟩
      (B₀ S oR pkSeedDist g) (dF oR pkSeedDist)
  have hf : ∀ st pk, (rUd pkSeedDist (Lazy.bWotsS (B₀ S oR pkSeedDist g))).distinguish st pk =
      simulateQ (instImpl₀ g) (udDist S oR st pk) := fun st pk =>
    (udDist_inst S oR pkSeedDist g st pk).symm
  kexact udAdv_mk_congr (wotsUdProblem Link.vp (R₀ (thG g) (hmG g)) pkSeedDist)
    (Open.RState Link.vp P0) _ _ _ _ hc hf

theorem udAdv_q1 : (udAdv S oR pkSeedDist).PickBound 0 :=
  genP_q1 (FWotsPre128 pkSeedDist) _

theorem udAdv_chal : (udAdv S oR pkSeedDist).ChalBound
    ((wotsInsts Link.vp).length * (Link.vp.params.len * 1)) :=
  genP_chal (FWotsPre128 pkSeedDist) _ _ (rUd_pick_chal pkSeedDist (dF oR pkSeedDist))

theorem udAdv_coll : (udAdv S oR pkSeedDist).CollBound
    (wotsQc Link.vp + (wotsInsts Link.vp).length * (Link.vp.params.len * (Link.vp.params.w - 1))) :=
  genP_coll (FWotsPre128 pkSeedDist) _ _ (rUd_pick_coll pkSeedDist (dF oR pkSeedDist))

theorem udAdv_len : (udAdv S oR pkSeedDist).CollLen Lw := by
  unfold UdAdv.CollLen udAdv
  exact emb_len _ (rUd_pick_len (vp := Link.vp) (prims := P0) pkSeedDist (dF oR pkSeedDist))

/-- **Parameters of the SM-UD realiser**: no first-phase compression query; challenge and
collection counts of `rUd_pick_chal`, `rUd_pick_coll`; continuation length `Lw`; second phase
`q2 qf qs ℓ (udH qs)` (forger's queries + hash queries × chain cost). -/
abbrev pU (qf qs ℓ : ℕ) : P5 :=
  ⟨0, (wotsInsts Link.vp).length * (Link.vp.params.len * 1),
    wotsQc Link.vp + (wotsInsts Link.vp).length * (Link.vp.params.len * (Link.vp.params.w - 1)),
    Lw, q2 qf qs ℓ (udH qs)⟩

variable {S oR pkSeedDist} {qf qs ℓ : ℕ}
  (hqf : ∀ pk, IsQueryBoundP (S.main pk)
    (fun i => Ideal.Realize.isPortQ (S := List Byte) i = true) qf)
  (hqs : ∀ pk, IsQueryBoundP (S.main pk)
    (fun i => Ideal.Realize.isSignQ (S := List Byte) i = true) qs)
  (hlong : ∀ pk, IsQueryBoundP (S.main pk)
    (fun i => Ideal.Realize.isLongQ (S := List Byte) ℓ i = true) 0)
  (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ)

include hqf hqs hlong hout in
/-- **The SM-UD realiser (SUF).** -/
noncomputable def realizesUd :
    RealizesUd pkSeedDist
      (fun g => Reduction.rUd pkSeedDist
        (Reduction.Lazy.bWotsS (S.typedS (optRandU oR) pkSeedDist g))) (pU qf qs ℓ) :=
  RealizesUd.ofEq (udAdv S oR pkSeedDist) (udAdv_inst S oR pkSeedDist)
    (udAdv_q1 S oR pkSeedDist) (udAdv_chal S oR pkSeedDist) (udAdv_coll S oR pkSeedDist)
    (udAdv_len S oR pkSeedDist) (fun st pk => udDist_bound S oR hqf hqs hlong hout st pk)

include hqf hqs hlong hout in
/-- **The SM-UD realiser (EUF).** -/
noncomputable def realizesUdE :
    RealizesUd pkSeedDist
      (fun g => Reduction.rUd pkSeedDist
        (Reduction.Lazy.bWotsS (S.typedE (optRandU oR) pkSeedDist g))) (pU qf qs ℓ) :=
  realizesUd hqf hqs hlong hout

end Ud

end Ideal.Realize.Wots
