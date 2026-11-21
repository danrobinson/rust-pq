import Ideal.Realize.WotsUniv
import Reduction.Open.Phase1Wots

/-!
# Challenge and collection queries of the WOTS first phases, as syntactic bounds

For every forger `A`, the first phases of `rUd`, `rPre`, `rTcrT pkSeedDist (Lazy.bWotsS A)`
make at most

| | collection queries | challenge queries |
|---|---|---|
| `rUd` | `wotsQc + #inst·len·(w-1)` (`rUd_pick_coll`) | `#inst·len` (`rUd_pick_chal`) |
| `rPre` | `wotsQc + #inst·len·(w-1)` (`rPre_choose_coll`) | `#inst·len` (`rPre_choose_chal`) |
| `rTcrT` | `wotsQc + #inst·len` (`rTcrT_choose_coll`) | `#inst·len·(w-1)` (`rTcrT_choose_chal`) |

as `IsQueryBoundP` statements.  The collection counts are those of
`Reduction.Open.rUd/rPre/rTcrT_collection_le` (the potential argument
`simChoose_bWotsWith_count`), read in the universal counting oracle of `WotsUniv.lean`.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security TweakableHash

namespace Ideal.Realize.Wots

open Reduction Reduction.Open WotsFinal

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- A challenge query of an SM game interface `unifSpec + (challengeSpec + collectionSpec)`. -/
def isChalI {A B : Type} : ℕ ⊕ (A ⊕ B) → Prop
  | Sum.inr (Sum.inl _) => True
  | _ => False

instance {A B : Type} : DecidablePred (isChalI (A := A) (B := B)) := fun t =>
  match t with
  | Sum.inr (Sum.inl _) => isTrue trivial
  | Sum.inr (Sum.inr _) => isFalse id
  | Sum.inl _ => isFalse id

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]
variable {optRand : PublicKeyCore prims.core → ProbComp prims.Y}
  (pkSeedDist : ProbComp prims.PkSeed)

/-! ## The universal oracle of the three game interfaces -/

section UnivGame

variable {T : Type}

/-- Full-support answers for `T →ₒ Option Y` + collection. -/
noncomputable def sampG (Y : Type) [SampleableType Y] (K : Type) :
    (t : T ⊕ ((_ : Unit) × K × List Y)) →
      ProbComp (((T →ₒ Option Y) + collSpecC K Y).Range t)
  | .inl _ => optU Y
  | .inr _ => optU Y

theorem sampG_support (Y : Type) [SampleableType Y] (K : Type)
    (t : T ⊕ ((_ : Unit) × K × List Y)) : support (sampG (T := T) Y K t) = Set.univ := by
  rcases t with t | t <;> exact support_optU Y

/-- The counter of the universal oracle for a predicate `pc`. -/
def cG {Y K : Type} (pc : ℕ ⊕ (T ⊕ ((_ : Unit) × K × List Y)) → Prop) [DecidablePred pc] :
    T ⊕ ((_ : Unit) × K × List Y) → ℕ :=
  fun t => if pc (.inr t) then 1 else 0

theorem univG_hO {Y K : Type} [SampleableType Y]
    (pc : ℕ ⊕ (T ⊕ ((_ : Unit) × K × List Y)) → Prop) [DecidablePred pc]
    (hu : ∀ n, ¬ pc (.inl n)) (t : ℕ ⊕ (T ⊕ ((_ : Unit) × K × List Y))) (σ : ℕ) :
    ∀ z ∈ support ((outer (univO (spec := (T →ₒ Option Y) + collSpecC K Y)
        (sampG Y K) (cG pc) ) t).run σ), id z.2 ≤ id σ + (if pc t then 1 else 0) := by
  intro z hz
  rcases t with n | t
  · rw [univ_outer_inl, support_map] at hz
    obtain ⟨u, -, rfl⟩ := hz
    simp
  · rw [univ_outer_inr, support_map] at hz
    obtain ⟨u, -, rfl⟩ := hz
    simp [cG]

/-- **Semantic → syntactic for the WOTS simulators**: the counter bound of
`simChoose_bWotsWith_count` in the universal oracle gives a query bound. -/
theorem qb_simChoose {Y K : Type} [SampleableType Y]
    (pc : ℕ ⊕ (T ⊕ ((_ : Unit) × K × List Y)) → Prop) [DecidablePred pc]
    (hu : ∀ n, ¬ pc (.inl n)) {α : Type}
    (oa : OracleComp (unifSpec + ((T →ₒ Option Y) + collSpecC K Y)) α) (N : ℕ)
    (h : ∀ z ∈ support ((simulateQ (outer (univO (spec := (T →ₒ Option Y) + collSpecC K Y)
        (sampG Y K) (cG pc))) oa).run 0), id z.2 ≤ id 0 + N) :
    IsQueryBoundP oa pc N :=
  qb_of_univ _ _ (sampG_support Y K) pc (fun t => rfl) hu oa N fun z hz => by
    simpa using h z hz

end UnivGame

theorem isColl_inl {A B : Type} (n : ℕ) : ¬ isColl (A := A) (B := B) (.inl n) := id
theorem isChalI_inl {A B : Type} (n : ℕ) : ¬ isChalI (A := A) (B := B) (.inl n) := id

end Ideal.Realize.Wots

namespace Ideal.Realize.Wots

open Reduction Reduction.Open WotsFinal

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]
variable {optRand : PublicKeyCore prims.core → ProbComp prims.Y}
  (pkSeedDist : ProbComp prims.PkSeed)

/-! ## SM-UD -/

section Ud

theorem udColl_chal (key : prims.AdrsKey) (xs : List prims.Y) :
    IsQueryBoundP (udColl (vp := vp) pkSeedDist key xs) isChalI 0 := by
  unfold udColl
  exact Lazy.qb_bind _ (n := 0) (m := 0) (by simp [isChalI]) fun _ => isQueryBoundP_pure _ _ _

theorem udChal_chal (key : prims.AdrsKey) :
    IsQueryBoundP (udChal (vp := vp) pkSeedDist key) isChalI 1 := by
  unfold udChal
  exact Lazy.qb_bind _ (n := 1) (m := 0) (by simp) fun _ => isQueryBoundP_pure _ _ _

theorem udChain_chal (ca : Adrs) (x : prims.Y) (i s : ℕ) :
    IsQueryBoundP (chainWith (udChainHash (vp := vp) pkSeedDist) ca x i s) isChalI 0 :=
  (Lazy.qb_chain isChalI prims.core 0 (hash := udChainHash (vp := vp) pkSeedDist)
    (fun a y => udColl_chal pkSeedDist _ _) ca x i s).mono (by simp)

theorem udStart_chal (k : ℕ) (ca : Adrs) (b : ℕ) :
    IsQueryBoundP (udStart (vp := vp) pkSeedDist k ca b) isChalI 1 := by
  unfold udStart
  split_ifs with h
  · exact (Lazy.qb_bind _ (udChal_chal pkSeedDist _) fun y =>
      udChain_chal pkSeedDist ca y _ _).mono (by omega)
  · exact (Lazy.qb_bind _ (n := 0)
      (qb_lift_isColl _ isChalI (by rintro (_ | _ | _) h <;> simp_all [isChalI]))
      fun y => udChain_chal pkSeedDist ca y _ _).mono (by omega)

theorem udSim_coll (my : ProbComp (SecretTable vp prims)) (A : Forger vp prims optRand pkSeedDist)
    (kf : ℕ) :
    IsQueryBoundP (WotsGame.simChoose (Lazy.bWotsWith my A) (wotsInsts vp) (udStart pkSeedDist kf)
      (udChainHash pkSeedDist) (udColl pkSeedDist) : OracleComp (udSpecC prims.AdrsKey prims.Y) _)
      isColl (wotsQc vp + (wotsInsts vp).length * (vp.params.len * (vp.params.w - 1))) := by
  apply qb_simChoose (T := prims.AdrsKey) (Y := prims.Y) (K := prims.AdrsKey) isColl isColl_inl
  intro z hz
  have h := simChoose_bWotsWith_count (univO (sampG prims.Y prims.AdrsKey) (cG isColl)) id
    isColl (univG_hO isColl isColl_inl) (udStart pkSeedDist kf) (udChainHash pkSeedDist)
    (udColl pkSeedDist) 1 (vp.params.len * (vp.params.w - 1)) (udColl_qb pkSeedDist)
    (signProg_qb isColl _ _ (fun b => b) 1 (vp.params.w - 1)
      (fun ca b => udStart_qb pkSeedDist kf ca b) (fun a y => udColl_qb pkSeedDist _ _)
      (fun b hb => by omega)) my A 0 z hz
  simpa using h

theorem udSim_chal (my : ProbComp (SecretTable vp prims)) (A : Forger vp prims optRand pkSeedDist)
    (kf : ℕ) :
    IsQueryBoundP (WotsGame.simChoose (Lazy.bWotsWith my A) (wotsInsts vp) (udStart pkSeedDist kf)
      (udChainHash pkSeedDist) (udColl pkSeedDist) : OracleComp (udSpecC prims.AdrsKey prims.Y) _)
      isChalI ((wotsInsts vp).length * (vp.params.len * 1)) := by
  apply qb_simChoose (T := prims.AdrsKey) (Y := prims.Y) (K := prims.AdrsKey) isChalI isChalI_inl
  intro z hz
  have h := simChoose_bWotsWith_count (univO (sampG prims.Y prims.AdrsKey) (cG isChalI)) id
    isChalI (univG_hO isChalI isChalI_inl) (udStart pkSeedDist kf) (udChainHash pkSeedDist)
    (udColl pkSeedDist) 0 (vp.params.len * 1) (udColl_chal pkSeedDist)
    (signProg_qb isChalI _ _ (fun _ => 1) 0 1
      (fun ca b => udStart_chal pkSeedDist kf ca b) (fun a y => udColl_chal pkSeedDist _ _)
      (fun b hb => by omega)) my A 0 z hz
  simpa using h

theorem rUd_pick_eq (A : Forger vp prims optRand pkSeedDist) :
    (rUd pkSeedDist (Lazy.bWotsS A)).pick =
    ((monadLift ($ᵗ (Fin (vp.params.w - 3 + 1)) : ProbComp (Fin (vp.params.w - 3 + 1))) :
      OracleComp (udSpecC prims.AdrsKey prims.Y) (Fin (vp.params.w - 3 + 1))) >>= fun k =>
        WotsGame.simChoose (Lazy.bWotsWith (Lazy.sparseOn vp prims (forsSkIdx vp)) A)
          (wotsInsts vp) (udStart pkSeedDist k.val) (udChainHash pkSeedDist) (udColl pkSeedDist)) :=
  rfl

/-- **Collection queries of the SM-UD first phase** (syntactic form of `rUd_collection_le`):
`≤ wotsQc + #inst·len·(w-1)`. -/
theorem rUd_pick_coll (A : Forger vp prims optRand pkSeedDist) :
    IsQueryBoundP (rUd pkSeedDist (Lazy.bWotsS A)).pick isColl
      (wotsQc vp + (wotsInsts vp).length * (vp.params.len * (vp.params.w - 1))) := by
  rw [rUd_pick_eq]
  exact (isQueryBoundP_bind (n := 0)
    (qb_lift_isColl _ isColl (by rintro (_ | _ | _) h <;> simp_all [isColl])) fun kf _ =>
      udSim_coll pkSeedDist _ A kf.val).mono (by omega)

/-- **Challenge queries of the SM-UD first phase**: `≤ #inst·len`. -/
theorem rUd_pick_chal (A : Forger vp prims optRand pkSeedDist) :
    IsQueryBoundP (rUd pkSeedDist (Lazy.bWotsS A)).pick isChalI
      ((wotsInsts vp).length * (vp.params.len * 1)) := by
  rw [rUd_pick_eq]
  exact (isQueryBoundP_bind (n := 0)
    (qb_lift_isColl _ isChalI (by rintro (_ | _ | _) h <;> simp_all [isChalI])) fun kf _ =>
      udSim_chal pkSeedDist _ A kf.val).mono (by omega)

end Ud

/-! ## SM-PRE -/

section Pre

theorem preColl_chal (key : prims.AdrsKey) (xs : List prims.Y) :
    IsQueryBoundP (preColl (vp := vp) pkSeedDist key xs) isChalI 0 := by
  unfold preColl
  exact Lazy.qb_bind _ (n := 0) (m := 0) (by simp [isChalI]) fun _ => isQueryBoundP_pure _ _ _

theorem preStart_chal (ca : Adrs) (b : ℕ) :
    IsQueryBoundP (preStart (vp := vp) pkSeedDist ca b) isChalI 1 := by
  unfold preStart
  split_ifs with h
  · exact (qb_lift_isColl _ isChalI (by rintro (_ | _ | _) h <;> simp_all [isChalI])).mono
      (by omega)
  · unfold preChal
    exact Lazy.qb_bind _ (n := 1) (m := 0) (by simp) fun _ => isQueryBoundP_pure _ _ _

theorem rPre_choose_eq (A : Forger vp prims optRand pkSeedDist) :
    (rPre pkSeedDist (Lazy.bWotsS A)).choose =
      (WotsGame.simChoose (Lazy.bWotsWith (Lazy.sparseOn vp prims (forsSkIdx vp)) A)
        (wotsInsts vp) (preStart pkSeedDist) (preChainHash pkSeedDist) (preColl pkSeedDist) :
          OracleComp (preSpecC prims.AdrsKey prims.Y) _) := rfl

theorem preSim_coll (my : ProbComp (SecretTable vp prims))
    (A : Forger vp prims optRand pkSeedDist) :
    IsQueryBoundP (WotsGame.simChoose (Lazy.bWotsWith my A) (wotsInsts vp) (preStart pkSeedDist)
      (preChainHash pkSeedDist) (preColl pkSeedDist) : OracleComp (preSpecC prims.AdrsKey prims.Y) _)
      isColl (wotsQc vp + (wotsInsts vp).length * (vp.params.len * (vp.params.w - 1))) := by
  apply qb_simChoose (T := prims.AdrsKey) (Y := prims.Y) (K := prims.AdrsKey) isColl isColl_inl
  intro z hz
  have h := simChoose_bWotsWith_count (univO (sampG prims.Y prims.AdrsKey) (cG isColl)) id
    isColl (univG_hO isColl isColl_inl) (preStart pkSeedDist) (preChainHash pkSeedDist)
    (preColl pkSeedDist) 1 (vp.params.len * (vp.params.w - 1)) (preColl_qb pkSeedDist)
    (signProg_qb isColl _ _ (fun _ => 0) 1 (vp.params.w - 1)
      (fun ca b => preStart_qb pkSeedDist ca b) (fun a y => preColl_qb pkSeedDist _ _)
      (fun b hb => by omega)) my A 0 z hz
  simpa using h

theorem preSim_chal (my : ProbComp (SecretTable vp prims))
    (A : Forger vp prims optRand pkSeedDist) :
    IsQueryBoundP (WotsGame.simChoose (Lazy.bWotsWith my A) (wotsInsts vp) (preStart pkSeedDist)
      (preChainHash pkSeedDist) (preColl pkSeedDist) : OracleComp (preSpecC prims.AdrsKey prims.Y) _)
      isChalI ((wotsInsts vp).length * (vp.params.len * 1)) := by
  apply qb_simChoose (T := prims.AdrsKey) (Y := prims.Y) (K := prims.AdrsKey) isChalI isChalI_inl
  intro z hz
  have h := simChoose_bWotsWith_count (univO (sampG prims.Y prims.AdrsKey) (cG isChalI)) id
    isChalI (univG_hO isChalI isChalI_inl) (preStart pkSeedDist) (preChainHash pkSeedDist)
    (preColl pkSeedDist) 0 (vp.params.len * 1) (preColl_chal pkSeedDist)
    (signProg_qb isChalI _ _ (fun _ => 1) 0 1
      (fun ca b => preStart_chal pkSeedDist ca b) (fun a y => preColl_chal pkSeedDist _ _)
      (fun b hb => by omega)) my A 0 z hz
  simpa using h

/-- **Collection queries of the SM-PRE first phase**: `≤ wotsQc + #inst·len·(w-1)`. -/
theorem rPre_choose_coll (A : Forger vp prims optRand pkSeedDist) :
    IsQueryBoundP (rPre pkSeedDist (Lazy.bWotsS A)).choose isColl
      (wotsQc vp + (wotsInsts vp).length * (vp.params.len * (vp.params.w - 1))) := by
  rw [rPre_choose_eq]
  exact preSim_coll pkSeedDist _ A

/-- **Challenge queries of the SM-PRE first phase**: `≤ #inst·len`. -/
theorem rPre_choose_chal (A : Forger vp prims optRand pkSeedDist) :
    IsQueryBoundP (rPre pkSeedDist (Lazy.bWotsS A)).choose isChalI
      ((wotsInsts vp).length * (vp.params.len * 1)) := by
  rw [rPre_choose_eq]
  exact preSim_chal pkSeedDist _ A

end Pre

/-! ## SM-TCR (tight cap) -/

section Tcr

theorem wtcrColl_chal (key : prims.AdrsKey) (xs : List prims.Y) :
    IsQueryBoundP (wtcrColl (vp := vp) pkSeedDist key xs) isChalI 0 := by
  unfold wtcrColl
  exact Lazy.qb_bind _ (n := 0) (m := 0) (by simp [isChalI]) fun _ => isQueryBoundP_pure _ _ _

theorem wtcrChal_chal (key : prims.AdrsKey) (x : prims.Y) :
    IsQueryBoundP (wtcrChal (vp := vp) pkSeedDist key x) isChalI 1 := by
  unfold wtcrChal
  exact Lazy.qb_bind _ (n := 1) (m := 0) (by simp) fun _ => isQueryBoundP_pure _ _ _

theorem tcrStart_chal (ca : Adrs) (b : ℕ) :
    IsQueryBoundP (tcrStart (vp := vp) pkSeedDist ca b) isChalI 0 := by
  unfold tcrStart
  refine Lazy.qb_bind _ (n := 0) (m := 0)
    (qb_lift_isColl _ isChalI (by rintro (_ | _ | _) h <;> simp_all [isChalI])) fun s => ?_
  split_ifs with h
  · exact isQueryBoundP_pure _ _ _
  · exact wtcrColl_chal pkSeedDist _ _

theorem rTcrT_choose_eq (A : Forger vp prims optRand pkSeedDist) :
    (rTcrT (vp := vp) pkSeedDist (Lazy.bWotsS A)).choose =
      (WotsGame.simChoose (Lazy.bWotsWith (Lazy.sparseOn vp prims (forsSkIdx vp)) A)
        (wotsInsts vp) (tcrStart pkSeedDist) (tcrChainHash pkSeedDist) (wtcrColl pkSeedDist) :
          OracleComp (tcrSpecC prims.AdrsKey prims.Y) _) := by
  rw [rTcrT_choose]
  rfl

theorem tcrSim_coll (my : ProbComp (SecretTable vp prims))
    (A : Forger vp prims optRand pkSeedDist) :
    IsQueryBoundP (WotsGame.simChoose (Lazy.bWotsWith my A) (wotsInsts vp) (tcrStart pkSeedDist)
      (tcrChainHash pkSeedDist) (wtcrColl pkSeedDist) : OracleComp (tcrSpecC prims.AdrsKey prims.Y) _)
      isColl (wotsQc vp + (wotsInsts vp).length * (vp.params.len * 1)) := by
  apply qb_simChoose (T := prims.AdrsKey × prims.Y) (Y := prims.Y) (K := prims.AdrsKey) isColl
    isColl_inl
  intro z hz
  have h := simChoose_bWotsWith_count
    (univO (sampG (T := prims.AdrsKey × prims.Y) prims.Y prims.AdrsKey) (cG isColl)) id
    isColl (univG_hO isColl isColl_inl) (tcrStart pkSeedDist) (tcrChainHash pkSeedDist)
    (wtcrColl pkSeedDist) 1 (vp.params.len * 1) (wtcrColl_qb pkSeedDist)
    (tcr_signProg_qb pkSeedDist) my A 0 z hz
  simpa using h

theorem tcrSim_chal (my : ProbComp (SecretTable vp prims))
    (A : Forger vp prims optRand pkSeedDist) :
    IsQueryBoundP (WotsGame.simChoose (Lazy.bWotsWith my A) (wotsInsts vp) (tcrStart pkSeedDist)
      (tcrChainHash pkSeedDist) (wtcrColl pkSeedDist) : OracleComp (tcrSpecC prims.AdrsKey prims.Y) _)
      isChalI ((wotsInsts vp).length * (vp.params.len * (vp.params.w - 1))) := by
  apply qb_simChoose (T := prims.AdrsKey × prims.Y) (Y := prims.Y) (K := prims.AdrsKey) isChalI
    isChalI_inl
  intro z hz
  have h := simChoose_bWotsWith_count
    (univO (sampG (T := prims.AdrsKey × prims.Y) prims.Y prims.AdrsKey) (cG isChalI)) id
    isChalI (univG_hO isChalI isChalI_inl) (tcrStart pkSeedDist) (tcrChainHash pkSeedDist)
    (wtcrColl pkSeedDist) 0 (vp.params.len * (vp.params.w - 1)) (wtcrColl_chal pkSeedDist)
    (signProg_qb isChalI _ _ (fun _ => 0) 1 (vp.params.w - 1)
      (fun ca b => tcrStart_chal pkSeedDist ca b) (fun a y => wtcrChal_chal pkSeedDist _ _)
      (fun b hb => by omega)) my A 0 z hz
  simpa using h

/-- **Collection queries of the SM-TCR first phase**: `≤ wotsQc + #inst·len`. -/
theorem rTcrT_choose_coll (A : Forger vp prims optRand pkSeedDist) :
    IsQueryBoundP (rTcrT (vp := vp) pkSeedDist (Lazy.bWotsS A)).choose isColl
      (wotsQc vp + (wotsInsts vp).length * (vp.params.len * 1)) := by
  rw [rTcrT_choose_eq]
  exact tcrSim_coll pkSeedDist _ A

/-- **Challenge queries of the SM-TCR first phase**: `≤ #inst·len·(w-1)`. -/
theorem rTcrT_choose_chal (A : Forger vp prims optRand pkSeedDist) :
    IsQueryBoundP (rTcrT (vp := vp) pkSeedDist (Lazy.bWotsS A)).choose isChalI
      ((wotsInsts vp).length * (vp.params.len * (vp.params.w - 1))) := by
  rw [rTcrT_choose_eq]
  exact tcrSim_chal pkSeedDist _ A

end Tcr

/-! ## Irreducible wrappers of the SM-PRE / SM-TCR first phases

(Their weak-head normal form would start evaluating the key-structure walk — the first step
samples `#forsSkIdx` table cells — so statements about them are kept behind an irreducible
name.) -/

section Irred

/-- The SM-PRE first phase, behind an irreducible name. -/
@[irreducible] noncomputable def preChooseI (A : Forger vp prims optRand pkSeedDist) :
    OracleComp (preSpecC prims.AdrsKey prims.Y) (RState vp prims) :=
  (rPre pkSeedDist (Lazy.bWotsS A)).choose

theorem preChooseI_eq (A : Forger vp prims optRand pkSeedDist) :
    preChooseI pkSeedDist A = (rPre pkSeedDist (Lazy.bWotsS A)).choose := by
  unfold preChooseI; rfl

theorem preChooseI_chal (A : Forger vp prims optRand pkSeedDist) :
    IsQueryBoundP (preChooseI pkSeedDist A) isChalI
      ((wotsInsts vp).length * (vp.params.len * 1)) := by
  rw [preChooseI_eq]; exact rPre_choose_chal pkSeedDist A

theorem preChooseI_coll (A : Forger vp prims optRand pkSeedDist) :
    IsQueryBoundP (preChooseI pkSeedDist A) isColl
      (wotsQc vp + (wotsInsts vp).length * (vp.params.len * (vp.params.w - 1))) := by
  rw [preChooseI_eq]; exact rPre_choose_coll pkSeedDist A

/-- The SM-TCR (tight cap) first phase, behind an irreducible name. -/
@[irreducible] noncomputable def tcrChooseI (A : Forger vp prims optRand pkSeedDist) :
    OracleComp (tcrSpecC prims.AdrsKey prims.Y) (RState vp prims) :=
  (rTcrT (vp := vp) pkSeedDist (Lazy.bWotsS A)).choose

theorem tcrChooseI_eq (A : Forger vp prims optRand pkSeedDist) :
    tcrChooseI pkSeedDist A = (rTcrT (vp := vp) pkSeedDist (Lazy.bWotsS A)).choose := by
  unfold tcrChooseI; rfl

theorem tcrChooseI_chal (A : Forger vp prims optRand pkSeedDist) :
    IsQueryBoundP (tcrChooseI pkSeedDist A) isChalI
      ((wotsInsts vp).length * (vp.params.len * (vp.params.w - 1))) := by
  rw [tcrChooseI_eq]; exact rTcrT_choose_chal pkSeedDist A

theorem tcrChooseI_coll (A : Forger vp prims optRand pkSeedDist) :
    IsQueryBoundP (tcrChooseI pkSeedDist A) isColl
      (wotsQc vp + (wotsInsts vp).length * (vp.params.len * 1)) := by
  rw [tcrChooseI_eq]; exact rTcrT_choose_coll pkSeedDist A

end Irred

end Ideal.Realize.Wots

#print axioms Ideal.Realize.Wots.rUd_pick_coll
#print axioms Ideal.Realize.Wots.rUd_pick_chal
#print axioms Ideal.Realize.Wots.rPre_choose_coll
#print axioms Ideal.Realize.Wots.rPre_choose_chal
#print axioms Ideal.Realize.Wots.rTcrT_choose_coll
#print axioms Ideal.Realize.Wots.rTcrT_choose_chal
