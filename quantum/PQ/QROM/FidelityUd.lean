import PQ.QROM.FidelityPre
import PQ.QROM.ExactUdClosed
import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTUD

/-!
# Fidelity of the exact SM-DT-UD games to VCVio's `SM_DT_UD_Experiment`

`udReal` / `udIdeal` (`PQ/QROM/ExactUd.lean`), restricted to classical adversaries with one
uniform coin, are VCVio's `SM_DT_UD_RealSuccess` / `SM_DT_UD_IdealSuccess` at a uniformly random
tweakable hash, for the problem `fidUdProblem cap Th`: `M' = Msg`, `emb = id`, uniform inputs
and uniform outputs, collection: the same function.

Both worlds are handled at once: the challenge response is a uniform draw `z ← $ᵗ Z` mapped by
`ans row t z` (`Z = Msg`, `ans a t x = a (t, x)` in the real world; `Z = Y`, `ans a t y = y` in
the ideal world).

* `fid_ud_presample`: pre-sampling of the challenge responses (`fidLazy_eq_eager`).
* `fid_ud_eag_run`: the table-run is the classical run against the exact challenger.
* `fid_ud_real_eq`, `fid_ud_ideal_eq`: the fidelity equalities.
* `fid_ud_classical_le`: `ud_exact_real_le_ideal_add` / `ud_exact_ideal_le_real_add` for
  VCVio's success probabilities.
-/

open OracleComp OracleSpec TweakableHash ENNReal Quantum Matrix

set_option linter.unusedSectionVars false

namespace PQ.QROM

variable {Y : Type} [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
  {Sd Tw Msg Ω Z : Type} [Fintype Sd] [DecidableEq Sd] [Fintype Tw] [DecidableEq Tw]
  [Fintype Msg] [DecidableEq Msg] [Nonempty Msg]
  [SampleableType Sd] [SampleableType Msg] [SampleableType Y]
  [Fintype Ω] [Nonempty Ω] [SampleableType Ω]
  [Fintype Z] [Nonempty Z] [SampleableType Z]

/-- VCVio's SM-DT-UD problem for the hash `Th`: `M' = Msg`, uniform inputs and outputs. -/
noncomputable def fidUdProblem (cap : ℕ) (Th : Dom Sd Tw Msg → Y) :
    SM_DT_UD_Problem Unit Sd Tw Msg Msg Y where
  th := ⟨$ᵗ Sd, fun P t m ↦ Th (P, (t, m))⟩
  emb := id
  emb_injective := Function.injective_id
  inputGen := $ᵗ Msg
  outputGen := $ᵗ Y
  thColl := ⟨fun _ ↦ Msg, fun _ P t m ↦ Th (P, (t, m))⟩
  numTargets := cap

/-- A classical SM-DT-UD adversary with a uniform coin drawn at the start. -/
structure FidUdAdv (Ω Sd Tw Msg Y : Type) where
  /-- Private state carried from `pick` to `distinguish`. -/
  State : Type
  /-- The first phase, for the coin `ω`. -/
  pick : Ω → OracleComp ((Dom Sd Tw Msg →ₒ Y) + fidPreReqSpec Tw Msg Y) State
  /-- The second phase. -/
  distinguish : State → Sd → OracleComp (Dom Sd Tw Msg →ₒ Y) Bool

/-- Answer hash queries with `Th`; pass challenge and collection queries on. -/
def fidUdInst (cap : ℕ) (Th : Dom Sd Tw Msg → Y) :
    QueryImpl ((Dom Sd Tw Msg →ₒ Y) + fidPreReqSpec Tw Msg Y) (OracleComp (unifSpec +
      (SM_DT_UD_challengeSpec Tw Y + collectionSpec (fidUdProblem cap Th).thColl))) :=
  fun t ↦ match t with
    | .inl q => pure (Th q)
    | .inr r => liftM (OracleSpec.query (spec := unifSpec +
      (SM_DT_UD_challengeSpec Tw Y + collectionSpec (fidUdProblem cap Th).thColl)) (.inr r))

/-- VCVio's adversary at the hash `Th`. -/
noncomputable def FidUdAdv.honest (cap : ℕ) (A : FidUdAdv Ω Sd Tw Msg Y)
    (Th : Dom Sd Tw Msg → Y) : SM_DT_UD_Adversary (fidUdProblem cap Th) where
  State := A.State
  pick := do
    let ω ← (liftM ($ᵗ Ω : ProbComp Ω) : OracleComp (unifSpec +
      (SM_DT_UD_challengeSpec Tw Y + collectionSpec (fidUdProblem cap Th).thColl)) Ω)
    simulateQ (fidUdInst cap Th) (A.pick ω)
  distinguish st P := simulateQ (fun q ↦ (pure (Th q) : ProbComp Y)) (A.distinguish st P)

/-- VCVio's oracles with hash queries answered by `Th`, as one implementation. -/
noncomputable def fidUdImpl (w : SM_DT_UD_World) (cap : ℕ) (Th : Dom Sd Tw Msg → Y) (P : Sd) :
    QueryImpl ((Dom Sd Tw Msg →ₒ Y) + fidPreReqSpec Tw Msg Y)
      (StateT (SM_DT_UD_State Tw) ProbComp) :=
  fun t ↦ match t with
    | .inl q => pure (Th q)
    | .inr r => SM_DT_UD_oracles w (fidUdProblem cap Th) P (.inr r)

theorem fid_ud_compose (w : SM_DT_UD_World) (cap : ℕ) (Th : Dom Sd Tw Msg → Y) (P : Sd)
    {State : Type} (oa : OracleComp ((Dom Sd Tw Msg →ₒ Y) + fidPreReqSpec Tw Msg Y) State) :
    simulateQ (SM_DT_UD_oracles w (fidUdProblem cap Th) P)
        (simulateQ (fidUdInst cap Th) oa) =
      simulateQ (fidUdImpl w cap Th P) oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind t k ih =>
    rw [simulateQ_bind (fidUdInst cap Th), simulateQ_spec_query,
      simulateQ_bind (fidUdImpl w cap Th P), simulateQ_spec_query, simulateQ_bind]
    rcases t with q | r
    · simp only [fidUdInst, fidUdImpl]
      rw [simulateQ_pure, pure_bind, pure_bind]
      exact ih (Th q)
    · simp only [fidUdInst, fidUdImpl]
      refine Eq.trans (congrArg (· >>= _) (simulateQ_spec_query
        (SM_DT_UD_oracles w (fidUdProblem cap Th) P) (.inr r))) ?_
      exact bind_congr fun u ↦ ih u

/-- VCVio's two oracles with the challenge response read from the table `zs` through `ans`,
as deterministic steps on VCVio's state. -/
def fidUdEag (cap : ℕ) (Th : Dom Sd Tw Msg → Y) (P : Sd) (ans : Tw → Z → Y) (zs : Tw → Z) :
    (t : ((Dom Sd Tw Msg →ₒ Y) + fidPreReqSpec Tw Msg Y).Domain) → SM_DT_UD_State Tw →
      ((Dom Sd Tw Msg →ₒ Y) + fidPreReqSpec Tw Msg Y).Range t × SM_DT_UD_State Tw
  | .inl q, s => (Th q, s)
  | .inr (.inl t), s =>
    if cap ≤ s.1.length ∨ ¬ TweakFresh id s.1 s.2 t then ((none : Option Y), s)
    else (some (ans t (zs t)), (s.1 ++ [t], s.2))
  | .inr (.inr q), s =>
    if TweakReserved id s.1 q.2.1 then ((none : Option Y), s)
    else (some (Th (P, (q.2.1, q.2.2))), (s.1, s.2 ++ [q.2.1]))

/-- **Pre-sampling of the challenge responses**, in the world `w` whose response is a uniform
draw from `Z` mapped by `ans`. -/
theorem fid_ud_presample (w : SM_DT_UD_World) (cap : ℕ) (Th : Dom Sd Tw Msg → Y) (P : Sd)
    (ans : Tw → Z → Y)
    (hresp : ∀ t, SM_DT_UD_response w (fidUdProblem cap Th) P t =
      (($ᵗ Z : ProbComp Z) >>= fun z ↦ pure (ans t z)))
    {State : Type} (oa : OracleComp ((Dom Sd Tw Msg →ₒ Y) + fidPreReqSpec Tw Msg Y) State)
    (s : SM_DT_UD_State Tw) (cont : State × SM_DT_UD_State Tw → ProbComp Bool) :
    fidPr ((simulateQ (SM_DT_UD_oracles w (fidUdProblem cap Th) P)
        (simulateQ (fidUdInst cap Th) oa)).run s >>= cont) =
      avg fun zs : Tw → Z ↦ fidPr (cont (fidEagRun (fidUdEag cap Th P ans zs) oa s)) := by
  rw [fid_ud_compose]
  refine fidLazy_eq_eager (dead := fun s i ↦ TweakReserved id s.1 i) ?_ ?_ ?_ oa s cont
  · intro t s
    rcases t with q | t | q
    · exact Or.inl fun zs ↦ rfl
    · by_cases h : cap ≤ s.1.length ∨ ¬ TweakFresh id s.1 s.2 t
      · left
        intro zs
        change (SM_DT_UD_challengeOracle w (fidUdProblem cap Th) P t).run s = _
        simp [fidUdEag, SM_DT_UD_challengeOracle, fidUdProblem, h]
      · right
        refine ⟨t, fun z ↦ (some (ans t z), (s.1 ++ [t], s.2)), ?_, ?_, ?_⟩
        · change (SM_DT_UD_challengeOracle w (fidUdProblem cap Th) P t).run s = _
          have h' : ¬ ((fidUdProblem cap Th).numTargets ≤ s.1.length ∨
              ¬ TweakFresh id s.1 s.2 t) := h
          simp [SM_DT_UD_challengeOracle, h', hresp, map_eq_bind_pure_comp]
        · intro zs
          simp [fidUdEag, h]
        · intro z
          exact ⟨t, by simp, rfl⟩
    · left
      intro zs
      change (collectionOracle (Q := Tw) id (fidUdProblem cap Th).thColl P q).run s = _
      by_cases h : TweakReserved id s.1 q.2.1
      · simp [fidUdEag, collectionOracle, fidUdProblem, h]
      · simp [fidUdEag, collectionOracle, fidUdProblem, h]
  · intro zs t s i hi
    rcases t with q | t | q
    · exact hi
    · simp only [fidUdEag]
      split_ifs
      · exact hi
      · obtain ⟨e, he, heq⟩ := hi
        exact ⟨e, List.mem_append_left _ he, heq⟩
    · simp only [fidUdEag]
      split_ifs
      · exact hi
      · exact hi
  · intro zs t s i z hi
    rcases t with q | t | q
    · rfl
    · by_cases hti : t = i
      · subst hti
        have h : cap ≤ s.1.length ∨ ¬ TweakFresh id s.1 s.2 t := Or.inr fun hf ↦ hf.1 hi
        simp [fidUdEag, h]
      · simp [fidUdEag, Function.update_of_ne hti]
    · rfl

/-- The challenger of the exact game whose challenge answers are `ans row t (zs t)`. -/
abbrev fidUdCh (cap : ℕ) (ans : (Tw × Msg → Y) → Tw → Z → Y) (zs : Tw → Z) (a : Tw × Msg → Y) :
    Tw ⊕ (Tw × Msg) → PreState Tw Msg → Option Y × PreState Tw Msg :=
  preChT cap (fun t ↦ ans a t (zs t)) a

/-- VCVio's game state for the histories of the exact game. -/
def fidUdSt (s : PreState Tw Msg) : SM_DT_UD_State Tw := (s.chal, s.coll.map Prod.fst)

theorem fid_ud_reserved_iff (s : PreState Tw Msg) (t : Tw) :
    TweakReserved id (fidUdSt s).1 t ↔ t ∈ s.chal := by
  simp [TweakReserved, fidUdSt]

theorem fid_ud_step_chal (cap : ℕ) (Th : Dom Sd Tw Msg → Y) (P : Sd)
    (ans : (Tw × Msg → Y) → Tw → Z → Y) (zs : Tw → Z) (t : Tw) (s : PreState Tw Msg) :
    fidUdEag cap Th P (ans (rowOf Th P)) zs (.inr (.inl t)) (fidUdSt s) =
      ((preChT cap (fun t ↦ ans (rowOf Th P) t (zs t)) (rowOf Th P) (.inl t) s).1,
        fidUdSt (preChT cap (fun t ↦ ans (rowOf Th P) t (zs t)) (rowOf Th P) (.inl t) s).2) := by
  have hc : (cap ≤ (fidUdSt s).1.length ∨
      ¬ TweakFresh id (fidUdSt s).1 (fidUdSt s).2 t) ↔
      (cap ≤ s.chal.length ∨ t ∈ s.chal ∨ t ∈ s.coll.map Prod.fst) := by
    unfold TweakFresh
    rw [fid_ud_reserved_iff]
    simp only [fidUdSt]
    tauto
  simp only [fidUdEag, preChT]
  by_cases h : cap ≤ s.chal.length ∨ t ∈ s.chal ∨ t ∈ s.coll.map Prod.fst
  · rw [if_pos (hc.2 h), dif_pos h]
  · rw [if_neg (fun h' ↦ h (hc.1 h')), dif_neg h]
    simp [fidUdSt]

theorem fid_ud_step_coll (cap : ℕ) (Th : Dom Sd Tw Msg → Y) (P : Sd)
    (ans : (Tw × Msg → Y) → Tw → Z → Y) (zs : Tw → Z) (q : (_ : Unit) × Tw × Msg)
    (s : PreState Tw Msg) :
    fidUdEag cap Th P (ans (rowOf Th P)) zs (.inr (.inr q)) (fidUdSt s) =
      ((preChT cap (fun t ↦ ans (rowOf Th P) t (zs t)) (rowOf Th P) (.inr q.2) s).1,
        fidUdSt (preChT cap (fun t ↦ ans (rowOf Th P) t (zs t)) (rowOf Th P) (.inr q.2) s).2) := by
  simp only [fidUdEag, preChT]
  by_cases h : q.2.1 ∈ s.chal
  · rw [if_pos ((fid_ud_reserved_iff s _).2 h), dif_pos h]
  · rw [if_neg (fun h' ↦ h ((fid_ud_reserved_iff s _).1 h')), dif_neg h]
    simp [fidUdSt, rowOf]

/-- The table-run of VCVio's first phase is the classical run against the challenger of the
exact game. -/
theorem fid_ud_eag_run (cap : ℕ) (Th : Dom Sd Tw Msg → Y) (P : Sd)
    (ans : (Tw × Msg → Y) → Tw → Z → Y) (zs : Tw → Z) {State : Type}
    (oa : OracleComp ((Dom Sd Tw Msg →ₒ Y) + fidPreReqSpec Tw Msg Y) State)
    (s : PreState Tw Msg) :
    fidEagRun (fidUdEag cap Th P (ans (rowOf Th P)) zs) oa (fidUdSt s) =
      ((fidGRun (fidPreCodec Tw Msg Y) Th
          (preChT cap (fun t ↦ ans (rowOf Th P) t (zs t)) (rowOf Th P)) oa s).1,
        fidUdSt (fidGRun (fidPreCodec Tw Msg Y) Th
          (preChT cap (fun t ↦ ans (rowOf Th P) t (zs t)) (rowOf Th P)) oa s).2) := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure a => rfl
  | query_bind t k ih =>
    rcases t with q | t | q
    · exact ih (Th q) s
    · change fidEagRun _ (k (fidUdEag cap Th P (ans (rowOf Th P)) zs (.inr (.inl t))
        (fidUdSt s)).1) (fidUdEag cap Th P (ans (rowOf Th P)) zs (.inr (.inl t)) (fidUdSt s)).2 = _
      rw [fid_ud_step_chal]
      exact ih _ _
    · change fidEagRun _ (k (fidUdEag cap Th P (ans (rowOf Th P)) zs (.inr (.inr q))
        (fidUdSt s)).1) (fidUdEag cap Th P (ans (rowOf Th P)) zs (.inr (.inr q)) (fidUdSt s)).2 = _
      rw [fid_ud_step_coll]
      exact ih _ _

theorem fid_ud_run_lift {α : Type} (w : SM_DT_UD_World) (cap : ℕ) (Th : Dom Sd Tw Msg → Y)
    (P : Sd) (oa : ProbComp α) (s : SM_DT_UD_State Tw) :
    (simulateQ (SM_DT_UD_oracles w (fidUdProblem cap Th) P)
      (liftM oa : OracleComp (unifSpec +
      (SM_DT_UD_challengeSpec Tw Y + collectionSpec (fidUdProblem cap Th).thColl)) α)).run s =
      oa >>= fun a ↦ pure (a, s) := by
  unfold SM_DT_UD_oracles
  rw [QueryImpl.simulateQ_add_liftM_left]
  simp

theorem fid_ud_experiment (w : SM_DT_UD_World) (cap : ℕ) (Th : Dom Sd Tw Msg → Y)
    (A : FidUdAdv Ω Sd Tw Msg Y) :
    SM_DT_UD_Experiment w (A.honest cap Th) =
      (do
        let P ← $ᵗ Sd
        let ω ← $ᵗ Ω
        (simulateQ (SM_DT_UD_oracles w (fidUdProblem cap Th) P)
          (simulateQ (fidUdInst cap Th) (A.pick ω))).run ([], []) >>= fun z ↦
            simulateQ (fun q ↦ (pure (Th q) : ProbComp Y)) (A.distinguish z.1 P) :
              ProbComp Bool) := by
  unfold SM_DT_UD_Experiment
  refine bind_congr (m := ProbComp) fun P ↦ ?_
  simp only [FidUdAdv.honest]
  rw [simulateQ_bind, StateT.run_bind, fid_ud_run_lift]
  simp only [bind_assoc, pure_bind]

/-- **Fidelity of the exact SM-DT-UD game**, in the world `w` whose challenge response is a
uniform draw from `Z` mapped by `ans row t`. -/
theorem fid_ud_world_eq (w : SM_DT_UD_World) (cap : ℕ) (ans : (Tw × Msg → Y) → Tw → Z → Y)
    (hresp : ∀ (Th : Dom Sd Tw Msg → Y) (P : Sd) (t : Tw),
      SM_DT_UD_response w (fidUdProblem cap Th) P t =
        (($ᵗ Z : ProbComp Z) >>= fun z ↦ pure (ans (rowOf Th P) t z)))
    (A : FidUdAdv Ω Sd Tw Msg Y) (n : ℕ) (hb : ∀ ω, IsQueryBoundP (A.pick ω) fidIsReq n) :
    (avg fun zs : Tw → Z ↦ twoPhaseExp .instruments (A := QReg.of Unit) (SubState.basis ())
        (fidUdCh cap ans zs) preInit n
        (fidGCoinEmb (fidPreCodec Tw Msg Y) A.pick n) (fidGPh2 A.distinguish) udWin) =
      avg fun Th : Dom Sd Tw Msg → Y ↦ fidPr (SM_DT_UD_Experiment w (A.honest cap Th)) := by
  rw [avg_congr fun zs ↦ fidGCoin_twoPhaseExp (fidPreCodec Tw Msg Y)
    (fidUdCh cap ans zs) preInit udWin n A.pick (fidGPh2 A.distinguish)]
  unfold twoPhaseExp
  rw [avg_reverse4]
  refine avg_congr fun Th ↦ ?_
  rw [fid_ud_experiment]
  refine Eq.trans ?_ (fidPr_uniform_bind _).symm
  refine avg_congr fun P ↦ ?_
  refine Eq.trans ?_ (fidPr_uniform_bind _).symm
  refine avg_congr fun ω ↦ ?_
  rw [fid_ud_presample w cap Th P (ans (rowOf Th P)) (hresp Th P)]
  refine avg_congr fun zs ↦ ?_
  rw [fidG_realProb _ _ _ _ _ _ _ (hb ω)]
  have h := fid_ud_eag_run cap Th P ans zs (A.pick ω) preInit
  rw [show (([], []) : SM_DT_UD_State Tw) = fidUdSt preInit from rfl, h]
  simp only
  rw [fid_simulateQ_pure, fidPr_pure]
  rfl

/-- **Fidelity of the exact SM-DT-UD game, real world.** -/
theorem fid_ud_real_eq (cap : ℕ) (A : FidUdAdv Ω Sd Tw Msg Y) (n : ℕ)
    (hb : ∀ ω, IsQueryBoundP (A.pick ω) fidIsReq n) :
    udReal .instruments (A := QReg.of Unit) (SubState.basis ()) cap n
        (fidGCoinEmb (fidPreCodec Tw Msg Y) A.pick n) (fidGPh2 A.distinguish) =
      avg fun Th : Dom Sd Tw Msg → Y ↦ SM_DT_UD_RealSuccess (A.honest cap Th) :=
  fid_ud_world_eq .real cap (fun a t x ↦ a (t, x)) (fun _ _ _ ↦ rfl) A n hb

/-- **Fidelity of the exact SM-DT-UD game, ideal world.** -/
theorem fid_ud_ideal_eq (cap : ℕ) (A : FidUdAdv Ω Sd Tw Msg Y) (n : ℕ)
    (hb : ∀ ω, IsQueryBoundP (A.pick ω) fidIsReq n) :
    udIdeal .instruments (A := QReg.of Unit) (SubState.basis ()) cap n
        (fidGCoinEmb (fidPreCodec Tw Msg Y) A.pick n) (fidGPh2 A.distinguish) =
      avg fun Th : Dom Sd Tw Msg → Y ↦ SM_DT_UD_IdealSuccess (A.honest cap Th) :=
  fid_ud_world_eq .ideal cap (fun _ _ y ↦ y) (fun _ _ _ ↦ (bind_pure _).symm) A n hb

/-- **The exact SM-DT-UD bound for VCVio's success probabilities**, averaged over the uniformly
random tweakable hash. -/
theorem fid_ud_classical_le [Nonempty Tw] (cap : ℕ) (A : FidUdAdv Ω Sd Tw Msg Y) (n q₁ q₂ : ℕ)
    (hb : ∀ ω, IsQueryBoundP (A.pick ω) fidIsReq n)
    (h1 : ∀ ω, IsQueryBoundP (A.pick ω) fidIsHash q₁)
    (h2 : ∀ st P, IsTotalQueryBound (A.distinguish st P) q₂) :
    (avg fun Th : Dom Sd Tw Msg → Y ↦ SM_DT_UD_RealSuccess (A.honest cap Th)) ≤
        (avg fun Th : Dom Sd Tw Msg → Y ↦ SM_DT_UD_IdealSuccess (A.honest cap Th)) +
          (4 * q₂ * ((Fintype.card Msg : ℝ≥0∞)⁻¹) ^ (2⁻¹ : ℝ) + 2 * seedLoss Sd q₁) ∧
      (avg fun Th : Dom Sd Tw Msg → Y ↦ SM_DT_UD_IdealSuccess (A.honest cap Th)) ≤
        (avg fun Th : Dom Sd Tw Msg → Y ↦ SM_DT_UD_RealSuccess (A.honest cap Th)) +
          (4 * q₂ * ((Fintype.card Msg : ℝ≥0∞)⁻¹) ^ (2⁻¹ : ℝ) + 2 * seedLoss Sd q₁) := by
  rw [← fid_ud_real_eq cap A n hb, ← fid_ud_ideal_eq cap A n hb]
  exact ⟨ud_exact_real_le_ideal_add (fidGCoin_emb_isQueryBound _ A.pick n q₁ h1)
      (fidG_ph2_isQueryBound A.distinguish q₂ h2),
    ud_exact_ideal_le_real_add (fidGCoin_emb_isQueryBound _ A.pick n q₁ h1)
      (fidG_ph2_isQueryBound A.distinguish q₂ h2)⟩

end PQ.QROM

#print axioms PQ.QROM.fid_ud_presample
#print axioms PQ.QROM.fid_ud_real_eq
#print axioms PQ.QROM.fid_ud_ideal_eq
#print axioms PQ.QROM.fid_ud_classical_le
