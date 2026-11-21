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

/-! ## SM-UD -/

section Ud

variable (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
  (pkSeedDist : ProbComp (Bytes 16))

/-- **The ideal-model SM-UD adversary.** -/
noncomputable def udAdv : WotsUdAdv128 pkSeedDist where
  State := Open.RState Link.vp P0
  pick := simulateQ (embImpl (X := SM_DT_UD_challengeSpec (Bytes 22) (Bytes 16) +
      collSpecC (Bytes 22) (Bytes 16)))
    (rUd (vp := Link.vp) (prims := P0) pkSeedDist (Lazy.bWotsS (dF oR pkSeedDist))).pick
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

end Ud

/-! ## SM-PRE -/

/-- The SM-PRE first phase over `P0` (irreducible for the elaborator: its whnf would start
evaluating the key-structure walk). -/
@[irreducible] noncomputable def preP1 (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    (pkSeedDist : ProbComp (Bytes 16)) :
    OracleComp (unifSpec + (SM_DT_PRE_challengeSpec (Bytes 22) (Bytes 16) +
      collSpecC (Bytes 22) (Bytes 16))) (Open.RState Link.vp P0) :=
  preChooseI (vp := Link.vp) (prims := P0) pkSeedDist (dF oR pkSeedDist)

theorem preP1_eq (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    (pkSeedDist : ProbComp (Bytes 16)) :
    preP1 oR pkSeedDist =
      (rPre (vp := Link.vp) (prims := P0) pkSeedDist (Lazy.bWotsS (dF oR pkSeedDist))).choose := by
  unfold preP1; exact preChooseI_eq _ _

/-- The SM-TCR first phase over `P0` (irreducible, as `preP1`). -/
@[irreducible] noncomputable def tcrP1 (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    (pkSeedDist : ProbComp (Bytes 16)) :
    OracleComp (unifSpec + (SM_DT_TCR_challengeSpec (Bytes 22) (Bytes 16) (Bytes 16) +
      collSpecC (Bytes 22) (Bytes 16))) (Open.RState Link.vp P0) :=
  tcrChooseI (vp := Link.vp) (prims := P0) pkSeedDist (dF oR pkSeedDist)

theorem tcrP1_eq (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    (pkSeedDist : ProbComp (Bytes 16)) :
    tcrP1 oR pkSeedDist =
      (rTcrT (vp := Link.vp) (prims := P0) pkSeedDist (Lazy.bWotsS (dF oR pkSeedDist))).choose := by
  unfold tcrP1; exact tcrChooseI_eq _ _

section Pre

variable (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
  (pkSeedDist : ProbComp (Bytes 16))

/-- **The ideal-model SM-PRE adversary.** -/
noncomputable def preAdv : WotsPreAdv128 pkSeedDist where
  State := Open.RState Link.vp P0
  choose := simulateQ (embImpl (X := SM_DT_PRE_challengeSpec (Bytes 22) (Bytes 16) +
      collSpecC (Bytes 22) (Bytes 16)))
    (preP1 oR pkSeedDist)
  invert := preInv S oR

theorem preAdv_inst (g : CF St Blk) :
    rPre pkSeedDist (Lazy.bWotsS (S.typedS (optRandU oR) pkSeedDist g)) =
      instWP (preAdv S oR pkSeedDist) g := by
  rw [stepPre]
  have hc : @Eq (OracleComp (preSpecC (Bytes 22) (Bytes 16)) (Open.RState Link.vp P0))
      (rPre pkSeedDist (Lazy.bWotsS (B₀ S oR pkSeedDist g))).choose
      (simulateQ (instImpl (spec := SM_DT_PRE_challengeSpec (Bytes 22) (Bytes 16) +
        collSpecC (Bytes 22) (Bytes 16)) g) (preAdv S oR pkSeedDist).choose) := by
    have e1 := instImpl_emb (X := SM_DT_PRE_challengeSpec (Bytes 22) (Bytes 16) +
        collSpecC (Bytes 22) (Bytes 16)) g (preP1 oR pkSeedDist)
    rw [preP1_eq] at e1
    kexact (wotsPre_phase1_hashfree_all (prims := P0) ⟨thG g, hmG g, core₀.PRF, core₀.PRFmsg⟩
      (B₀ S oR pkSeedDist g) (dF oR pkSeedDist)).trans e1.symm
  have hf : ∀ st pk, (rPre pkSeedDist (Lazy.bWotsS (B₀ S oR pkSeedDist g))).invert st pk =
      simulateQ (instImpl₀ g) (preInv S oR st pk) := fun st pk =>
    (preInv_inst S oR pkSeedDist g st pk).symm
  kexact preAdv_mk_congr (wotsPreProblem Link.vp (R₀ (thG g) (hmG g)) pkSeedDist)
    (Open.RState Link.vp P0) _ _ _ _ hc hf

end Pre

/-! ## SM-TCR on `F` (tight cap) -/

section Tcr

variable (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
  (pkSeedDist : ProbComp (Bytes 16))

/-- **The ideal-model SM-TCR adversary on `F`.** -/
noncomputable def tcrAdv : WotsTcrAdv128T pkSeedDist where
  State := Open.RState Link.vp P0
  choose := simulateQ (embImpl (X := SM_DT_TCR_challengeSpec (Bytes 22) (Bytes 16) (Bytes 16) +
      collSpecC (Bytes 22) (Bytes 16)))
    (tcrP1 oR pkSeedDist)
  forge := tcrForge S oR

theorem tcrAdv_inst (g : CF St Blk) :
    rTcrT (vp := Link.vp) pkSeedDist (Lazy.bWotsS (S.typedS (optRandU oR) pkSeedDist g)) =
      instWT (tcrAdv S oR pkSeedDist) g := by
  rw [stepTcr]
  have hc : @Eq (OracleComp (tcrSpecC (Bytes 22) (Bytes 16)) (Open.RState Link.vp P0))
      (rTcrT (vp := Link.vp) pkSeedDist (Lazy.bWotsS (B₀ S oR pkSeedDist g))).choose
      (simulateQ (instImpl (spec := SM_DT_TCR_challengeSpec (Bytes 22) (Bytes 16) (Bytes 16) +
        collSpecC (Bytes 22) (Bytes 16)) g) (tcrAdv S oR pkSeedDist).choose) := by
    have e1 := instImpl_emb (X := SM_DT_TCR_challengeSpec (Bytes 22) (Bytes 16) (Bytes 16) +
        collSpecC (Bytes 22) (Bytes 16)) g (tcrP1 oR pkSeedDist)
    rw [tcrP1_eq] at e1
    kexact (wotsTcrT_phase1_hashfree_all (prims := P0) ⟨thG g, hmG g, core₀.PRF, core₀.PRFmsg⟩
      (B₀ S oR pkSeedDist g) (dF oR pkSeedDist)).trans e1.symm
  have hf : ∀ st pk,
      (rTcrT (vp := Link.vp) pkSeedDist (Lazy.bWotsS (B₀ S oR pkSeedDist g))).forge st pk =
        simulateQ (instImpl₀ g) (tcrForge S oR st pk) := fun st pk =>
    (tcrForge_inst S oR pkSeedDist g st pk).symm
  kexact wtcrAdv_mk_congr (wotsTcrProblemT Link.vp (R₀ (thG g) (hmG g)) pkSeedDist)
    (Open.RState Link.vp P0) _ _ _ _ hc hf

end Tcr

end Ideal.Realize.Wots

#print axioms Ideal.Realize.Wots.udAdv_inst
#print axioms Ideal.Realize.Wots.preAdv_inst
#print axioms Ideal.Realize.Wots.tcrAdv_inst
