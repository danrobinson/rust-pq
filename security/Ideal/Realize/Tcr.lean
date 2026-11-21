import Ideal.Realize.Port
import Ideal.Realize.Phase1
import Ideal.Transport.AdvTcr
import Ideal.ComposeFinal

/-!
# The class-TCR realisers: the ideal-model adversary and the equality of experiments

For an ideal-model forger `S : ForgerI`, a table-independent `opt_rand` family `optRandU oR` and
an arity `n`, this file builds ONE ideal-model SM-TCR adversary `advT S oR pkSeedDist n`
(`TcrAdv128T pkSeedDist n`, i.e. an oracle program with compression queries) and proves

  `advT_eq : 𝒟[SM_DT_TCR_Experiment (bTcrArM n (S.typedS (optRandU oR) pkSeedDist g))] =
             𝒟[SM_DT_TCR_Experiment (instRT (advT S oR pkSeedDist n) g)]`   for every table `g`.

Construction (all over the table-independent bundle `P₀ = R₀ dT dH`, core `core₀`):
* state `TcrP1State Link.vp P₀` (sparse secret table, stored list of the phase-1 hash calls);
* first phase: the forger-free program `Reduction.Open.tcrPhase1 Link.vp P₀ n`, embedded
  (`embImpl`, no compression query);
* second phase `forgeP`: the open program `tcrMOpenP` (the forger `typedP codec₀ S.main` with its
  compression port) interpreted by `chainImpl tbl` (secrets from the table, every `Thash` /
  `H_msg` query issued as its chain of compression queries), followed by `classOut`; the stored
  list is first clamped to entries of at most `len` values (`clampL`), which changes nothing on
  the lists the first phase produces (`routeHF_clamp`) and makes the second phase's query count
  hold for EVERY state.

Proof steps: `step1` (Transport: the adversary at `primsG (liftC g) = setPrf (R₀ (thG g) (hmG g))
(prfG g) (pmG g)` is the one at `R₀ (thG g) (hmG g)`, `bTcrArM_bytesToTypedS_setPrf`);
`forgeP_inst` (second phase: `chainImpl_inst`, `tcrMOpenP_fusion`, `typedP_inst`,
`bytesToTypedS_open_main`, `tcrMOpen_withTH`, `tcrM_phase2_open_eq`, `instImpl₀_liftM`);
`advT_choose_inst` (`instImpl_emb`); `hC_lem` (`routeHF_clamp`, `tcrChooseHF_len`);
`experiment_map_choose`.

Pitfall (recorded in `status/R-tcr.md`): the elaborator must never be asked to compare a term
over `P₀` with one over `R₀ (thG g) (hmG g)` or `primsG (liftC g)` *as programs* (it unfolds
`simulateQ`/`tcrPhase1` and runs out of recursion depth); such glue steps are closed by
`kexact` (kernel check) or go through generic lemmas (`tcrPhase1_withTH`, `tcrMOpen_withTH`,
`bytesToTypedS_open_main`) whose instantiation needs no comparison.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security TweakableHash

namespace Ideal.Realize.Tcr
open Reduction Reduction.Open Ideal.Transport

attribute [local irreducible] Reduction.arityTargets Reduction.tcrTargets

/-- `primsG (liftC g)` is the reference bundle `R₀ (thG g) (hmG g)` with `PRF`, `PRF_msg`
replaced (cited in `Ideal/Realize/Chain.lean`). -/
theorem primsG_eq (g : CF St Blk) :
    primsG (liftC g) = setPrf (R₀ (thG g) (hmG g)) (prfG g) (pmG g) := rfl

/-- The wire codec over `core₀` (that of `codecC`). -/
def codec₀ : CoreWireCodec Link.vp.params core₀ where
  pkSeed := WireCodec.bytes Link.vp.params.n
  skSeed := WireCodec.bytes Link.vp.params.n
  skPrf := WireCodec.bytes Link.vp.params.n
  y := WireCodec.bytes Link.vp.params.n
  y_toBytes := fun _ => rfl

/-- `optRandU oR` over `core₀`. -/
def optRand₀ (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) (pk : PublicKeyCore core₀) :
    ProbComp core₀.Y := oR pk.pkSeed pk.pkRoot

/-- The table-independent bundle over which the ideal-model adversary is written. -/
abbrev P₀ : Primitives Link.vp.params := R₀ dT dH

/-- The typed forger over `R₀ (thG g) (hmG g)` built from `S` with its port answered by `g`. -/
noncomputable def B₀ (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    (pkSeedDist : ProbComp (Bytes 16)) (g : CF St Blk) :
    Forger Link.vp (R₀ (thG g) (hmG g)) (optRand₀ oR) pkSeedDist :=
  (bytesToTypedS (vp := Link.vp) (prims := R₀ (thG g) (hmG g)) (codec := codec₀)
    (optRand := optRand₀ oR) (pkSeedDist := pkSeedDist)
    ⟨fun pk => simulateQ (instImpl g) (S.main pk)⟩).toUnforgeableAdversary

/-- **Second phase of the ideal-model adversary**: the open program with port, hash queries
issued as compression chains, then `classOut`. -/
noncomputable def forgeP (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) (n : ℕ)
    (tbl : SecretTable Link.vp P₀) (L : List (P₀.AdrsKey × List P₀.Y)) (pk : P₀.PkSeed) :
    OracleComp (unifSpec + hS St Blk) (ℕ × {xs : List P₀.Y // xs.length = n}) :=
  simulateQ (chainImpl tbl)
      (tcrMOpenP (vp := Link.vp) (prims := P₀) (optRand₀ oR) (typedP codec₀ S.main) L pk) >>=
    fun jm => pure (classOut P₀ n L jm)

theorem forgeP_inst (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    (pkSeedDist : ProbComp (Bytes 16)) (n : ℕ) (g : CF St Blk)
    (tbl : SecretTable Link.vp P₀) (L : List (P₀.AdrsKey × List P₀.Y)) (pk : P₀.PkSeed) :
    simulateQ (instImpl₀ g) (forgeP S oR n tbl L pk) =
      (bTcrArM n (B₀ S oR pkSeedDist g)).forge (tbl, L) pk := by
  have h1 := tcrM_phase2_open_eq (prims := R₀ (thG g) (hmG g)) (hS St Blk) n
    (B₀ S oR pkSeedDist g) tbl L pk
  have h2 := congrArg (simulateQ (instImpl₀ g)) h1
  rw [instImpl₀_liftM] at h2
  rw [h2]
  unfold forgeP
  rw [simulateQ_bind, simulateQ_bind,
    chainImpl_inst g (implTH (thG g) (hmG g)) (hashC_inst g) tbl,
    ← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose]
  have hF := tcrMOpenP_fusion (optRand₀ oR)
    (instImpl₀ g ∘ₛ Lazy.tblImpl (gspec := hS St Blk) (implTH (thG g) (hmG g)) tbl) g
    (fun q => rfl) (typedP codec₀ S.main) L pk
  have hT : (fun pk => simulateQ (instImpl g) (typedP codec₀ S.main pk)) =
      fun pk => (bytesToTypedS (vp := Link.vp) (prims := P₀) (codec := codec₀)
        (optRand := optRand₀ oR) (pkSeedDist := pkSeedDist)
        ⟨fun pkb => simulateQ (instImpl g) (S.main pkb)⟩).toUnforgeableAdversary.main pk :=
    funext fun pk => typedP_inst (vp := Link.vp) (prims := P₀) codec₀ (optRand₀ oR) pkSeedDist g S.main pk
  have hM : (B₀ S oR pkSeedDist g).main =
      (bytesToTypedS (vp := Link.vp) (prims := P₀) (codec := codec₀)
        (optRand := optRand₀ oR) (pkSeedDist := pkSeedDist)
        ⟨fun pkb => simulateQ (instImpl g) (S.main pkb)⟩).toUnforgeableAdversary.main :=
    bytesToTypedS_open_main (prims := P₀) (thG g) (hmG g)
      ⟨fun pkb => simulateQ (instImpl g) (S.main pkb)⟩
  rw [hF, hT, ← impl_R₀ (thG g) (hmG g), hM,
    tcrMOpen_withTH (prims := P₀) (thG g) (hmG g)]
  simp only [classOut_withTH (prims := P₀) (thG g) (hmG g)]

/-- The bound on the input length of the scheme's hash calls (`len`). -/
abbrev Bmax : ℕ := Link.vp.params.len

/-- **The ideal-model class-TCR adversary.** -/
noncomputable def advT (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    (pkSeedDist : ProbComp (Bytes 16)) (n : ℕ) : TcrAdv128T pkSeedDist n where
  State := TcrP1State Link.vp P₀
  choose := simulateQ embImpl (tcrPhase1 Link.vp P₀ n : OracleComp (TcrP1Spec P₀ n) (TcrP1State Link.vp P₀))
  forge := fun st pk => forgeP S oR n st.1 (clampL Bmax st.2) pk

theorem step1 (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    (pkSeedDist : ProbComp (Bytes 16)) (g : CF St Blk) (n : ℕ) :
    bTcrArM n (S.typedS (optRandU oR) pkSeedDist g) = bTcrArM n (B₀ S oR pkSeedDist g) :=
  bTcrArM_bytesToTypedS_setPrf (prims := R₀ (thG g) (hmG g)) (prfG g) (pmG g) codec₀ (optRand₀ oR)
    (optRandU oR g) (fun _ => rfl) pkSeedDist n (fun pk => simulateQ (instImpl g) (S.main pk))

theorem advT_choose_inst (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    (pkSeedDist : ProbComp (Bytes 16)) (n : ℕ) (g : CF St Blk) :
    simulateQ (instImpl g) (advT S oR pkSeedDist n).choose = tcrPhase1 Link.vp P₀ n := by
  kexact instImpl_emb g (tcrPhase1 Link.vp P₀ n : OracleComp (TcrP1Spec P₀ n) (TcrP1State Link.vp P₀))

theorem exp_choose_congr {ι PkSeed Tweak M Y : Type} [DecidableEq Tweak] [DecidableEq M]
    [DecidableEq Y] {prob : SM_DT_TCR_Problem ι PkSeed Tweak M Y} (a : SM_DT_TCR_Adversary prob)
    {c : OracleComp (unifSpec + (SM_DT_TCR_challengeSpec Tweak M Y + collectionSpec prob.thColl))
      a.State} (hc : a.choose = c) :
    SM_DT_TCR_Experiment a = SM_DT_TCR_Experiment (⟨a.State, c, a.forge⟩ : SM_DT_TCR_Adversary prob) := by
  subst hc; rfl

theorem hch_lem (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    (pkSeedDist : ProbComp (Bytes 16)) (n : ℕ) (g : CF St Blk) :
    ((bTcrArM n (B₀ S oR pkSeedDist g)).choose :
      OracleComp (TcrP1Spec (R₀ (thG g) (hmG g)) n) (TcrP1State Link.vp (R₀ (thG g) (hmG g)))) =
      tcrPhase1 Link.vp P₀ n :=
    (bTcrArM_choose_eq n (B₀ S oR pkSeedDist g)).trans
      (tcrPhase1_withTH (prims := P₀) (thG g) (hmG g) n)

theorem hB_lem (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    (pkSeedDist : ProbComp (Bytes 16)) (n : ℕ) (g : CF St Blk) :
    SM_DT_TCR_Experiment (bTcrArM n (B₀ S oR pkSeedDist g)) =
      SM_DT_TCR_Experiment (⟨TcrP1State Link.vp P₀, tcrPhase1 Link.vp P₀ n,
        (bTcrArM n (B₀ S oR pkSeedDist g)).forge⟩ :
        SM_DT_TCR_Adversary (thashArityProblemT Link.vp (R₀ (thG g) (hmG g)) pkSeedDist n)) :=
  exp_choose_congr _ (hch_lem S oR pkSeedDist n g)

theorem hC_lem (n : ℕ) :
    (fun z : TcrP1State Link.vp P₀ => (z.1, clampL Bmax z.2)) <$> tcrPhase1 Link.vp P₀ n =
      tcrPhase1 Link.vp P₀ n :=
  routeHF_clamp _ _ Bmax _ (tcrChooseHF_len Bmax fun xs h => by
    rcases h with h | h | h | h <;> rw [h] <;> decide) [] (by simp)

theorem hE_lem (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    (pkSeedDist : ProbComp (Bytes 16)) (n : ℕ) (g : CF St Blk) :
    SM_DT_TCR_Experiment (⟨TcrP1State Link.vp P₀, tcrPhase1 Link.vp P₀ n,
        (bTcrArM n (B₀ S oR pkSeedDist g)).forge⟩ :
        SM_DT_TCR_Adversary (thashArityProblemT Link.vp (R₀ (thG g) (hmG g)) pkSeedDist n)) =
      SM_DT_TCR_Experiment (⟨TcrP1State Link.vp P₀, tcrPhase1 Link.vp P₀ n,
        fun st pk => (bTcrArM n (B₀ S oR pkSeedDist g)).forge (st.1, clampL Bmax st.2) pk⟩ :
        SM_DT_TCR_Adversary (thashArityProblemT Link.vp (R₀ (thG g) (hmG g)) pkSeedDist n)) := by
  have hE := experiment_map_choose
    (prob := thashArityProblemT Link.vp (R₀ (thG g) (hmG g)) pkSeedDist n)
    (fun z : TcrP1State Link.vp P₀ => (z.1, clampL Bmax z.2)) (tcrPhase1 Link.vp P₀ n)
    (bTcrArM n (B₀ S oR pkSeedDist g)).forge
  refine Eq.trans ?_ hE
  exact congrArg (fun c : OracleComp (TcrP1Spec P₀ n) (TcrP1State Link.vp P₀) =>
    SM_DT_TCR_Experiment (⟨TcrP1State Link.vp P₀, c, (bTcrArM n (B₀ S oR pkSeedDist g)).forge⟩ :
        SM_DT_TCR_Adversary (thashArityProblemT Link.vp (R₀ (thG g) (hmG g)) pkSeedDist n)))
    (hC_lem n).symm

theorem hI_lem (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    (pkSeedDist : ProbComp (Bytes 16)) (n : ℕ) (g : CF St Blk) :
    instRT (advT S oR pkSeedDist n) g =
      (⟨TcrP1State Link.vp P₀, tcrPhase1 Link.vp P₀ n,
        fun st pk => (bTcrArM n (B₀ S oR pkSeedDist g)).forge (st.1, clampL Bmax st.2) pk⟩ :
        SM_DT_TCR_Adversary (thashArityProblemT Link.vp (primsG (liftC g)) pkSeedDist n)) := by
  kexact (adv_ext (prob := thashArityProblemT Link.vp (primsG (liftC g)) pkSeedDist n)
      (advT_choose_inst S oR pkSeedDist n g)
      (funext fun st => funext fun pk => forgeP_inst S oR pkSeedDist n g st.1 (clampL Bmax st.2) pk))

/-- **The experiments agree at every table.** -/
theorem advT_eq (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    (pkSeedDist : ProbComp (Bytes 16)) (n : ℕ) (g : CF St Blk) :
    𝒟[SM_DT_TCR_Experiment (bTcrArM n (S.typedS (optRandU oR) pkSeedDist g))] =
      𝒟[SM_DT_TCR_Experiment (instRT (advT S oR pkSeedDist n) g)] := by
  rw [step1, hI_lem]
  kexact (congrArg (fun x => 𝒟[x]) ((hB_lem S oR pkSeedDist n g).trans (hE_lem S oR pkSeedDist n g)))

end Ideal.Realize.Tcr

#print axioms Ideal.Realize.Tcr.primsG_eq
#print axioms Ideal.Realize.Tcr.forgeP_inst
#print axioms Ideal.Realize.Tcr.step1
#print axioms Ideal.Realize.Tcr.advT_choose_inst
#print axioms Ideal.Realize.Tcr.hC_lem
#print axioms Ideal.Realize.Tcr.advT_eq
