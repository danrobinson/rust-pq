import Ideal.Realize.TcrStore3

/-!
# The answer-storing class-TCR realisers: adversary and equality of experiments

For an ideal-model forger `S`, the table-independent `opt_rand` family `optRandU oR` and an arity
`n`, `advT3 S oR pkSeedDist n` is ONE ideal-model SM-TCR adversary with

* first phase: the recording program `tcrPhase1A Link.vp P₀ n` (the walk of the key structure
  routed to the class game, as in `advT`, but keeping every answer of the challenge and
  collection oracles: state `(tbl, (L, S))`), embedded without compression query;
* second phase `forgeP3`: the lookup program `tcrMOpenPS` (`Ideal/Realize/TcrStore3.lean`) —
  key regeneration and every signature computed from the stored answers, no compression query;
  the forger's compression queries, the `H_msg` evaluations and the verification of the forgery
  issued as compression chains — then `classOut`.

`advT3_eq`: for every table `g`,
`𝒟[SM_DT_TCR_Experiment (bTcrArM n (S.typedS (optRandU oR) pkSeedDist g))] =
 𝒟[SM_DT_TCR_Experiment (instRT (advT3 S oR pkSeedDist n) g)]`, the same family as the realisers
of `Ideal/Realize/TcrCount.lean`.

Proof: on the support of the first phase the store is `ann pk (honestCalls tbl pk)`
(`bTcrArA_choose_run`, via `bTcrArA_choose_eq_A`), at which `tcrMOpenPS` is interpreted as
`tcrMOpenP` (`tcrMOpenPS_tbl`), hence the second phase is that of `advT` (`forgeP3_eq`) and the
experiments are those of `Ideal/Realize/Tcr.lean` (`hB_lem`, `hE_lem`).
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security TweakableHash

namespace Ideal.Realize.Tcr
open Reduction Reduction.Open Ideal.Transport

attribute [local irreducible] Reduction.arityTargets Reduction.tcrTargets
attribute [local irreducible] Reduction.Lazy.sparseTable Reduction.Lazy.structSecIdx

/-- The structural side conditions hold for every reference bundle `R₀ T H`. -/
theorem structural₀ (T : Bytes 16 → Bytes 22 → List (Bytes 16) → Bytes 16)
    (H : Bytes 16 → Bytes 16 → Bytes 16 → List Byte → Bytes 30) :
    Reduction.Structural Link.vp (R₀ T H) := by
  have hb : ApprovedAddressBounds Link.vp.params := fipsApprovedAddressBounds Link.S128
  refine ⟨⟨fun _ _ h => h⟩, ?_, hb.toCanonicalAddressBounds⟩
  intro a ha b hb' hkey
  obtain ⟨hac, hal, hat⟩ := sha2Domain_of_addressFacts hb ha
  obtain ⟨hbc, hbl, hbt⟩ := sha2Domain_of_addressFacts hb hb'
  exact Concrete.sha2AdrsKey_injective_of_domain hac hal hat hbc hbl hbt hkey

/-- **Second phase of the answer-storing ideal-model adversary**, over the reference bundle
`R₀ T H` (the adversary uses `T, H = dT, dH`; at a table `g` it is compared at `thG g, hmG g`,
`forgeP3G_TH`). -/
noncomputable def forgeP3G (T : Bytes 16 → Bytes 22 → List (Bytes 16) → Bytes 16)
    (H : Bytes 16 → Bytes 16 → Bytes 16 → List Byte → Bytes 30)
    (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) (n : ℕ)
    (tbl : SecretTable Link.vp (R₀ T H)) (L : List ((R₀ T H).AdrsKey × List (R₀ T H).Y))
    (Sto : Store (R₀ T H)) (pk : Bytes 16) :
    OracleComp (unifSpec + hS St Blk) (ℕ × {xs : List (R₀ T H).Y // xs.length = n}) :=
  simulateQ (chainImpl tbl)
      (tcrMOpenPS (vp := Link.vp) (prims := R₀ T H) (optRand₀ oR) (typedP codec₀ S.main) L Sto pk) >>=
    fun jm => pure (classOut (R₀ T H) n L jm)

/-- **The answer-storing ideal-model class-TCR adversary.** -/
noncomputable def advT3 (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    (pkSeedDist : ProbComp (Bytes 16)) (n : ℕ) : TcrAdv128T pkSeedDist n where
  State := TcrP1StateA Link.vp P₀
  choose := simulateQ embImpl
    (tcrPhase1A Link.vp P₀ n : OracleComp (TcrP1Spec P₀ n) (TcrP1StateA Link.vp P₀))
  forge := fun st pk => forgeP3G dT dH S oR n st.1 (clampL Bmax st.2.1) st.2.2 pk

/-- **At the phase-one store of the table `g`, the second phase is that of `bTcrArM n B₀`.** -/
theorem forgeP3G_inst (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    (pkSeedDist : ProbComp (Bytes 16)) (n : ℕ) (g : CF St Blk)
    (tbl : SecretTable Link.vp (R₀ (thG g) (hmG g)))
    (L : List ((R₀ (thG g) (hmG g)).AdrsKey × List (R₀ (thG g) (hmG g)).Y)) (pk : Bytes 16) :
    simulateQ (instImpl₀ g) (forgeP3G (thG g) (hmG g) S oR n tbl L
        (ann (thashList Link.vp (R₀ (thG g) (hmG g)) pkSeedDist) pk (honestCalls tbl pk)) pk) =
      (bTcrArM n (B₀ S oR pkSeedDist g)).forge (tbl, L) pk := by
  have h1 := tcrM_phase2_open_eq (prims := R₀ (thG g) (hmG g)) (hS St Blk) n
    (B₀ S oR pkSeedDist g) tbl L pk
  have h2 := congrArg (simulateQ (instImpl₀ g)) h1
  rw [instImpl₀_liftM] at h2
  rw [h2]
  unfold forgeP3G
  have hP := tcrMOpenPS_tbl (vp := Link.vp) (prims := R₀ (thG g) (hmG g))
    (pkSeedDist := pkSeedDist) tbl pk L (typedP codec₀ S.main) (optRand₀ oR)
  rw [simulateQ_bind, simulateQ_bind,
    chainImpl_inst g (implTH (thG g) (hmG g)) (hashC_inst g) tbl, ← impl_R₀]
  erw [hP]
  rw [← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose]
  have hF := tcrMOpenP_fusion (optRand₀ oR)
    (instImpl₀ g ∘ₛ Lazy.tblImpl (gspec := hS St Blk) (PublicHash.impl (R₀ (thG g) (hmG g))) tbl) g
    (fun q => rfl) (typedP codec₀ S.main) L pk
  have hT : (fun pk => simulateQ (instImpl g)
      (typedP (vp := Link.vp) (prims := R₀ (thG g) (hmG g)) codec₀ S.main pk)) =
      (B₀ S oR pkSeedDist g).main :=
    funext fun pk => typedP_inst (vp := Link.vp) (prims := R₀ (thG g) (hmG g)) codec₀
      (optRand₀ oR) pkSeedDist g S.main pk
  rw [hF, hT]

/-- The honest calls are on at most `len` values. -/
theorem clampL_honest {T : Bytes 16 → Bytes 22 → List (Bytes 16) → Bytes 16}
    {H : Bytes 16 → Bytes 16 → Bytes 16 → List Byte → Bytes 30}
    (tbl : SecretTable Link.vp (R₀ T H)) (pk : Bytes 16) :
    clampL Bmax (honestCalls tbl pk) = honestCalls tbl pk := by
  refine clampL_eq_self _ _ fun q hq => ?_
  obtain ⟨a, -, -, h2⟩ := honestCalls_arity tbl pk q hq
  rw [h2]
  unfold arityOf
  split_ifs <;> decide

/-- Two adversaries whose first-phase runs are images of one computation, with the same game
state and second phases agreeing at the images, have the same experiment. -/
theorem exp_eq_of_run {ι PkSeed Tweak M Y : Type} [DecidableEq Tweak] [DecidableEq M]
    [DecidableEq Y] {prob : SM_DT_TCR_Problem ι PkSeed Tweak M Y}
    (a b : SM_DT_TCR_Adversary prob) {τ : Type} (X : ProbComp τ)
    (fa : PkSeed → τ → a.State × SM_DT_TCR_State Tweak M)
    (fb : PkSeed → τ → b.State × SM_DT_TCR_State Tweak M)
    (ha : ∀ pk, (simulateQ (SM_DT_TCR_oracles prob pk) a.choose).run ([], []) = fa pk <$> X)
    (hb : ∀ pk, (simulateQ (SM_DT_TCR_oracles prob pk) b.choose).run ([], []) = fb pk <$> X)
    (hs : ∀ pk x, (fa pk x).2 = (fb pk x).2)
    (hf : ∀ pk x, a.forge (fa pk x).1 pk = b.forge (fb pk x).1 pk) :
    SM_DT_TCR_Experiment a = SM_DT_TCR_Experiment b := by
  unfold SM_DT_TCR_Experiment
  refine bind_congr fun pk => ?_
  rw [ha, hb, bind_map_left, bind_map_left]
  refine bind_congr fun x => ?_
  have h1 := hs pk x
  have h2 := hf pk x
  rcases hfa : fa pk x with ⟨sa, ga⟩
  rcases hfb : fb pk x with ⟨sb, gb⟩
  rw [hfa, hfb] at h1 h2
  simp only at h1 h2
  subst h1
  rcases ga with ⟨q, c⟩
  simp only
  rw [h2]

/-- The answer-storing adversary instantiated at a table, written over `R₀ T H`, against the
class game over `R₀ T₀ H₀`. -/
noncomputable def adv3G (T₀ : Bytes 16 → Bytes 22 → List (Bytes 16) → Bytes 16)
    (H₀ : Bytes 16 → Bytes 16 → Bytes 16 → List Byte → Bytes 30)
    (T : Bytes 16 → Bytes 22 → List (Bytes 16) → Bytes 16)
    (H : Bytes 16 → Bytes 16 → Bytes 16 → List Byte → Bytes 30)
    (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    (pkSeedDist : ProbComp (Bytes 16)) (n : ℕ) (g : CF St Blk) :
    SM_DT_TCR_Adversary (thashArityProblemT Link.vp (R₀ T₀ H₀) pkSeedDist n) :=
  ⟨TcrP1StateA Link.vp (R₀ T H), tcrPhase1A Link.vp (R₀ T H) n,
    fun st pk => simulateQ (instImpl₀ g) (forgeP3G T H S oR n st.1 (clampL Bmax st.2.1) st.2.2 pk)⟩

/-- `adv3G` does not depend on the bundle it is written over (kernel check, abstract `T`, `H`). -/
theorem adv3G_TH (T₀ : Bytes 16 → Bytes 22 → List (Bytes 16) → Bytes 16)
    (H₀ : Bytes 16 → Bytes 16 → Bytes 16 → List Byte → Bytes 30)
    (T T' : Bytes 16 → Bytes 22 → List (Bytes 16) → Bytes 16)
    (H H' : Bytes 16 → Bytes 16 → Bytes 16 → List Byte → Bytes 30)
    (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    (pkSeedDist : ProbComp (Bytes 16)) (n : ℕ) (g : CF St Blk) :
    adv3G T₀ H₀ T H S oR pkSeedDist n g = adv3G T₀ H₀ T' H' S oR pkSeedDist n g := by
  o9_kernel_rfl

/-- The second phases of `adv3G` at the store of phase one. -/
theorem forge3_at (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    (pkSeedDist : ProbComp (Bytes 16)) (n : ℕ) (g : CF St Blk) (pk : Bytes 16)
    (tbl : SecretTable Link.vp (R₀ (thG g) (hmG g))) :
    (adv3G (thG g) (hmG g) (thG g) (hmG g) S oR pkSeedDist n g).forge (tbl, (honestCalls tbl pk,
        ann (thashList Link.vp (R₀ (thG g) (hmG g)) pkSeedDist) pk (honestCalls tbl pk))) pk =
      (bTcrArM n (B₀ S oR pkSeedDist g)).forge (tbl, honestCalls tbl pk) pk := by
  have e := forgeP3G_inst S oR pkSeedDist n g tbl (clampL Bmax (honestCalls tbl pk)) pk
  have e2 := congrArg (fun L => (bTcrArM n (B₀ S oR pkSeedDist g)).forge (tbl, L) pk)
    (clampL_honest tbl pk)
  kexact e.trans e2

/-- **The experiment of the answer-storing adversary is that of `bTcrArM n B₀`.** -/
theorem exp3_eq (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    (pkSeedDist : ProbComp (Bytes 16)) (n : ℕ) (g : CF St Blk) :
    SM_DT_TCR_Experiment (adv3G (thG g) (hmG g) (thG g) (hmG g) S oR pkSeedDist n g) =
      SM_DT_TCR_Experiment (bTcrArM n (B₀ S oR pkSeedDist g)) := by
  refine exp_eq_of_run _ _ (Lazy.sparseTable Link.vp (R₀ (thG g) (hmG g)))
    (fun pk tbl => ((tbl, (honestCalls tbl pk,
        ann (thashList Link.vp (R₀ (thG g) (hmG g)) pkSeedDist) pk (honestCalls tbl pk))),
      TcrSplit.gState (fun xs => xs.length = n) (honestCalls tbl pk)))
    (fun pk tbl => ((tbl, honestCalls tbl pk),
      TcrSplit.gState (fun xs => xs.length = n) (honestCalls tbl pk)))
    (fun pk => ?_) (fun pk => bTcrArM_choose_run (structural₀ (thG g) (hmG g)) n
      (B₀ S oR pkSeedDist g) pk) (fun _ _ => rfl) (forge3_at S oR pkSeedDist n g)
  have h := bTcrArA_choose_run (structural₀ (thG g) (hmG g)) n (B₀ S oR pkSeedDist g) pk
  show (simulateQ (SM_DT_TCR_oracles
      (thashArityProblemT Link.vp (R₀ (thG g) (hmG g)) pkSeedDist n) pk)
      (tcrPhase1A Link.vp (R₀ (thG g) (hmG g)) n)).run ([], []) = _
  rw [← bTcrArA_choose_eq_A n (B₀ S oR pkSeedDist g)]
  exact h

theorem advT3_choose_inst (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    (pkSeedDist : ProbComp (Bytes 16)) (n : ℕ) (g : CF St Blk) :
    simulateQ (instImpl g) (advT3 S oR pkSeedDist n).choose = tcrPhase1A Link.vp P₀ n := by
  kexact instImpl_emb g
    (tcrPhase1A Link.vp P₀ n : OracleComp (TcrP1Spec P₀ n) (TcrP1StateA Link.vp P₀))

theorem hI3_lem (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    (pkSeedDist : ProbComp (Bytes 16)) (n : ℕ) (g : CF St Blk) :
    instRT (advT3 S oR pkSeedDist n) g =
      (⟨TcrP1StateA Link.vp P₀, tcrPhase1A Link.vp P₀ n,
        fun st pk => simulateQ (instImpl₀ g)
          (forgeP3G dT dH S oR n st.1 (clampL Bmax st.2.1) st.2.2 pk)⟩ :
        SM_DT_TCR_Adversary (thashArityProblemT Link.vp (primsG (liftC g)) pkSeedDist n)) := by
  kexact (adv_ext (prob := thashArityProblemT Link.vp (primsG (liftC g)) pkSeedDist n)
      (f' := fun st pk => simulateQ (instImpl₀ g)
        (forgeP3G dT dH S oR n st.1 (clampL Bmax st.2.1) st.2.2 pk))
      (advT3_choose_inst S oR pkSeedDist n g) (funext fun st => funext fun pk => rfl))

/-- **The experiments agree at every table**: the answer-storing adversary realises the same
family `bTcrArM n (S.typedS (optRandU oR) pkSeedDist g)` as `advT`. -/
theorem advT3_eq (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    (pkSeedDist : ProbComp (Bytes 16)) (n : ℕ) (g : CF St Blk) :
    𝒟[SM_DT_TCR_Experiment (bTcrArM n (S.typedS (optRandU oR) pkSeedDist g))] =
      𝒟[SM_DT_TCR_Experiment (instRT (advT3 S oR pkSeedDist n) g)] := by
  rw [step1, hI3_lem]
  have h := (exp3_eq S oR pkSeedDist n g).symm.trans
    (congrArg SM_DT_TCR_Experiment (adv3G_TH (thG g) (hmG g) (thG g) dT (hmG g) dH S oR
      pkSeedDist n g))
  kexact (congrArg (fun x => 𝒟[x]) h)

end Ideal.Realize.Tcr

#print axioms Ideal.Realize.Tcr.forgeP3G_inst
#print axioms Ideal.Realize.Tcr.exp3_eq
#print axioms Ideal.Realize.Tcr.advT3_eq
