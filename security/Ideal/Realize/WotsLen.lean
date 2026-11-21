import Ideal.Realize.Walk
import Reduction.Open.WotsCountsSM
import Ideal.Realize.WotsCount1

/-!
# Collection queries of the WOTS first phases are SLH-DSA hash calls

Every collection query of the first phases of `rUd`, `rPre`, `rTcrT pkSeedDist (Lazy.bWotsS A)`
is on `1`, `2`, `len` or `k` values (`OkLen`):

* `npw_*`: the WOTS-game first phase `chooseBody` (a program in the state monad `WM`) submits
  only `OkLen` collection queries (`npw_chooseBody`, `bWotsWith_choose_np`);
* `simChoose_np`: the simulator `WotsGame.simChoose` turns `OkLen` collection queries of the WOTS
  game into `OkLen` collection queries of the SM game, and its signing simulation submits only
  `OkLen` ones, if `startVal`, `chainHash`, `coll` do;
* `rUd_pick_len`, `rPre_choose_len`, `rTcrT_choose_len`.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security TweakableHash

namespace Ideal.Realize.Wots

open Reduction Reduction.Open WotsFinal

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.constructorNameAsVariable false

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]

/-! ## The WOTS-game first phase -/

/-- A collection query of the WOTS game that is not an SLH-DSA hash call. -/
def badW : (WSpec prims).Domain → Prop
  | .inr (.inr q) => ¬ OkLen vp q.2
  | _ => False

instance : DecidablePred (badW (vp := vp) (prims := prims)) := fun t =>
  match t with
  | .inr (.inr q) => inferInstanceAs (Decidable (¬ OkLen vp q.2))
  | .inr (.inl _) => isFalse id
  | .inl _ => isFalse id

/-- A program of the WOTS-game first phase that makes no `badW` query from any state. -/
def NPW {α : Type} (c : WM prims α) : Prop := ∀ h, IsQueryBoundP (c.run h) (badW (vp := vp)) 0

theorem npw_pure {α : Type} (x : α) : NPW (vp := vp) (pure x : WM prims α) := fun h => by
  rw [StateT.run_pure]; exact isQueryBoundP_pure _ _ _

theorem npw_bind {α β : Type} {c : WM prims α} {f : α → WM prims β} (hc : NPW (vp := vp) c)
    (hf : ∀ a, NPW (vp := vp) (f a)) : NPW (vp := vp) (c >>= f) := fun h => by
  rw [StateT.run_bind]
  exact isQueryBoundP_bind_zero _ _ (hc h) fun p => hf p.1 p.2

theorem npw_lift {α : Type} (x : OracleComp (WSpec prims) α)
    (hx : IsQueryBoundP x (badW (vp := vp)) 0) :
    NPW (vp := vp) (monadLift x : WM prims α) := fun h => by
  rw [StateT.run_monadLift]
  exact isQueryBoundP_bind_zero _ _ hx fun a => isQueryBoundP_pure _ _ _

theorem npw_wColl (key : prims.AdrsKey) (xs : List prims.Y) (hx : OkLen vp xs) :
    NPW (vp := vp) (wColl key xs) := by
  unfold wColl
  exact npw_bind (npw_lift _ ((isQueryBoundP_query_iff _ _ _).2 fun h => absurd hx h)) fun r =>
    npw_pure _

theorem npw_topsAt (a : Adrs) (msg : WM prims prims.Y) (hmsg : NPW (vp := vp) msg) :
    NPW (vp := vp) (topsAt a msg) := by
  intro h
  unfold topsAt
  rw [StateT.run_bind, StateT.run_get, pure_bind]
  split
  · rw [StateT.run_pure]; exact isQueryBoundP_pure _ _ _
  · refine npw_bind hmsg (fun m => npw_bind (npw_lift _ ?_) fun r => ?_) h
    · exact (isQueryBoundP_query_iff _ _ _).2 fun h => (show False from h).elim
    intro h'
    split
    · rw [StateT.run_bind]
      refine isQueryBoundP_bind_zero _ _ ?_ fun p => by
        rw [StateT.run_pure]; exact isQueryBoundP_pure _ _ _
      simp only [modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, StateT.run]
      exact isQueryBoundP_pure _ _ _
    · rw [StateT.run_pure]; exact isQueryBoundP_pure _ _ _

theorem npw_merkle (leaf : ℕ → WM prims prims.Y)
    (node : ℕ → ℕ → prims.Y → prims.Y → WM prims prims.Y)
    (hl : ∀ i, NPW (vp := vp) (leaf i)) (hn : ∀ z t l r, NPW (vp := vp) (node z t l r)) :
    ∀ z t, NPW (vp := vp) (PerfectMerkleTree.merkleRootM leaf node z t)
  | 0, t => hl t
  | z + 1, t => by
    rw [PerfectMerkleTree.merkleRootM]
    exact npw_bind (npw_merkle leaf node hl hn z _) fun l =>
      npw_bind (npw_merkle leaf node hl hn z _) fun r => hn _ _ _ _

theorem npw_forM {β : Type} (f : β → WM prims PUnit) (hf : ∀ b, NPW (vp := vp) (f b)) :
    ∀ ps : List β, NPW (vp := vp) (ps.forM f)
  | [] => npw_pure _
  | p :: ps => npw_bind (hf p) fun _ => npw_forM f hf ps

theorem npw_x1 {α : Type} (x : OracleComp (x1_spec prims) α)
    (hx : IsQueryBoundP x (fun q => ¬ OkLen vp q.2) 0) :
    NPW (vp := vp) (simulateQ x1_implW x) := by
  induction x using OracleComp.inductionOn with
  | pure x => rw [simulateQ_pure]; exact npw_pure x
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hx
    have ht : OkLen vp t.2 := not_not.mp (hx.1.resolve_right (Nat.lt_irrefl 0))
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map]
    exact npw_bind (npw_wColl _ _ ht) fun u => ih u (by simpa [ht] using hx.2 u)

theorem x1_free_np (tbl : SecretTable vp prims) (adrs : Adrs) :
    IsQueryBoundP (x1_free (prims := prims) tbl adrs) (fun q => ¬ OkLen vp q.2) 0 :=
  np_forsPkGen (fun q : Adrs × List prims.Y => ¬ OkLen vp q.2) prims.core
    (fun a y => by rw [isQueryBoundP_query_iff]; exact fun h => absurd (Or.inl rfl) h)
    (fun a ys hys => by rw [isQueryBoundP_query_iff]; exact fun h => absurd (Or.inr (Or.inr hys)) h)
    (fun a l r => by rw [isQueryBoundP_query_iff]; exact fun h => absurd (Or.inr (Or.inl rfl)) h)
    (fun a => isQueryBoundP_pure _ _ _) adrs

theorem npw_msgAt (tbl : SecretTable vp prims) :
    ∀ l tree leaf, NPW (vp := vp) (msgAt tbl l tree leaf)
  | 0, tree, leaf => by
    rw [x1_msgAt_eq]
    exact npw_x1 _ (x1_free_np tbl _)
  | l + 1, tree, leaf => by
    rw [msgAt]
    refine npw_merkle _ _ (fun t => npw_bind (npw_topsAt _ _ (npw_msgAt tbl l _ t)) fun tops =>
      npw_wColl _ _ (Or.inr (Or.inr (Or.inl (by simp))))) (fun z t l r => ?_) _ _
    exact npw_wColl _ _ (Or.inr (Or.inl rfl))

theorem npw_chooseBody (tbl : SecretTable vp prims) : NPW (vp := vp) (chooseBody tbl) := by
  unfold chooseBody
  exact npw_bind (npw_forM _ (fun pos => npw_bind (npw_topsAt _ _ (npw_msgAt tbl _ _ _))
    fun _ => npw_pure _) _) fun _ => npw_msgAt tbl _ _ _

variable {optRand : PublicKeyCore prims.core → ProbComp prims.Y}
  {pkSeedDist : ProbComp prims.PkSeed}

/-- **The WOTS-game first phase of `bWotsWith my A` submits only SLH-DSA hash calls.** -/
theorem bWotsWith_choose_np (my : ProbComp (SecretTable vp prims))
    (A : Forger vp prims optRand pkSeedDist) :
    IsQueryBoundP (Lazy.bWotsWith my A).choose (badW (vp := vp)) 0 := by
  rw [Lazy.bWotsWith_choose_eq]
  refine isQueryBoundP_bind_zero _ _ (IsQueryBoundP.of_imp (fun t ht => ?_)
    (isQueryBoundP_liftM_isRight my)) fun tbl =>
      isQueryBoundP_bind_zero _ _ (npw_chooseBody tbl []) fun x => isQueryBoundP_pure _ _ _
  rcases t with n | t
  · exact ht.elim
  · rfl

/-! ## The simulator -/

section Sim

variable {T : Type}

/-- A collection query of an SM game that is not an SLH-DSA hash call. -/
def badG : ℕ ⊕ (T ⊕ ((_ : Unit) × prims.AdrsKey × List prims.Y)) → Prop
  | .inr (.inr q) => ¬ OkLen vp q.2.2
  | _ => False

instance : DecidablePred (badG (vp := vp) (prims := prims) (T := T)) := fun t =>
  match t with
  | .inr (.inr q) => inferInstanceAs (Decidable (¬ OkLen vp q.2.2))
  | .inr (.inl _) => isFalse id
  | .inl _ => isFalse id

variable {spec : OracleSpec (T ⊕ ((_ : Unit) × prims.AdrsKey × List prims.Y))}

/-- **The simulator submits only SLH-DSA hash calls**, if its three callbacks do. -/
theorem simChoose_np (my : ProbComp (SecretTable vp prims))
    (A : Forger vp prims optRand pkSeedDist)
    (startVal : Adrs → ℕ → OracleComp (unifSpec + spec) prims.Y)
    (chainHash : Adrs → prims.Y → OracleComp (unifSpec + spec) prims.Y)
    (coll : prims.AdrsKey → List prims.Y → OracleComp (unifSpec + spec) prims.Y)
    (hstart : ∀ ca b, IsQueryBoundP (startVal ca b) (badG (vp := vp) (prims := prims)) 0)
    (hchain : ∀ a y, IsQueryBoundP (chainHash a y) (badG (vp := vp) (prims := prims)) 0)
    (hcoll : ∀ key xs, OkLen vp xs → IsQueryBoundP (coll key xs) (badG (vp := vp) (prims := prims)) 0) :
    IsQueryBoundP (WotsGame.simChoose (Lazy.bWotsWith my A) (wotsInsts vp) startVal chainHash coll)
      (badG (vp := vp) (prims := prims)) 0 := by
  refine qb_simulateQ_run_zero (p := badW (vp := vp)) (fun t ht s => ?_)
    (bWotsWith_choose_np my A) []
  rcases t with k | q | q
  · show IsQueryBoundP ((WotsFinal.simImpl (wotsInsts vp) startVal chainHash coll
      (Sum.inl k)).run s) _ 0
    rw [simImpl_run_unif]
    exact isQueryBoundP_bind_zero _ _ ((isQueryBoundP_query_iff _ _ _).2
      fun h => (show False from h).elim) fun u => isQueryBoundP_pure _ _ _
  · show IsQueryBoundP ((WotsFinal.simImpl (wotsInsts vp) startVal chainHash coll
      (Sum.inr (Sum.inl q))).run s) _ 0
    rw [simImpl_run_sign]
    split_ifs
    · exact isQueryBoundP_pure _ _ _
    · refine isQueryBoundP_bind_zero _ _ ((signProg_qb (badG (vp := vp) (prims := prims)) startVal chainHash
        (fun _ => 0) 0 0 hstart hchain (fun b hb => by simp) q.1 q.2).mono (by simp)) fun r =>
          isQueryBoundP_pure _ _ _
  · show IsQueryBoundP ((WotsFinal.simImpl (wotsInsts vp) startVal chainHash coll
      (Sum.inr (Sum.inr q))).run s) _ 0
    rw [simImpl_run_coll]
    split_ifs
    · exact isQueryBoundP_pure _ _ _
    · exact isQueryBoundP_bind_zero _ _ (hcoll _ _ (not_not.mp ht)) fun y =>
        isQueryBoundP_pure _ _ _

end Sim

/-! ## The three families -/

section Families

variable (pkSeedDist)

theorem lift_np {T : Type} {X : OracleSpec (T ⊕ ((_ : Unit) × prims.AdrsKey × List prims.Y))}
    {β : Type} (ob : ProbComp β) :
    IsQueryBoundP (liftM ob : OracleComp (unifSpec + X) β) (badG (vp := vp) (prims := prims) (T := T)) 0 :=
  IsQueryBoundP.of_imp (fun t ht => by
    rcases t with n | t
    · exact ht.elim
    · rfl) (isQueryBoundP_liftM_isRight ob)

theorem udColl_np (key : prims.AdrsKey) (xs : List prims.Y) (hx : OkLen vp xs) :
    @IsQueryBoundP _ (udSpecC prims.AdrsKey prims.Y) _ (udColl (vp := vp) pkSeedDist key xs)
      (badG (vp := vp) (prims := prims) (T := prims.AdrsKey)) _ 0 := by
  unfold udColl
  exact isQueryBoundP_bind_zero _ _ ((isQueryBoundP_query_iff _ _ _).2 fun h => absurd hx h) fun _ =>
    isQueryBoundP_pure _ _ _

theorem udChain_np (ca : Adrs) (x : prims.Y) (i s : ℕ) :
    @IsQueryBoundP _ (udSpecC prims.AdrsKey prims.Y) _
      (chainWith (udChainHash (vp := vp) pkSeedDist) ca x i s)
      (badG (vp := vp) (prims := prims) (T := prims.AdrsKey)) _ 0 :=
  (Lazy.qb_chain (badG (vp := vp) (prims := prims) (T := prims.AdrsKey)) prims.core 0
    (hash := udChainHash (vp := vp) pkSeedDist)
    (fun a y => udColl_np pkSeedDist _ _ (Or.inl rfl)) ca x i s).mono (by simp)

theorem udStart_np (k : ℕ) (ca : Adrs) (b : ℕ) :
    @IsQueryBoundP _ (udSpecC prims.AdrsKey prims.Y) _ (udStart (vp := vp) pkSeedDist k ca b)
      (badG (vp := vp) (prims := prims) (T := prims.AdrsKey)) _ 0 := by
  unfold udStart
  split_ifs with h
  · refine isQueryBoundP_bind_zero _ _ ?_ fun y => udChain_np pkSeedDist ca y _ _
    unfold udChal
    exact isQueryBoundP_bind_zero _ _ ((isQueryBoundP_query_iff _ _ _).2 fun h => (show False from h).elim)
      fun _ => isQueryBoundP_pure _ _ _
  · exact isQueryBoundP_bind_zero _ _ (lift_np _) fun y => udChain_np pkSeedDist ca y _ _

/-- **SM-UD first phase: every collection query is an SLH-DSA hash call.** -/
theorem rUd_pick_len (A : Forger vp prims optRand pkSeedDist) :
    @IsQueryBoundP _ (udSpecC prims.AdrsKey prims.Y) _ (rUd pkSeedDist (Lazy.bWotsS A)).pick
      (badG (vp := vp) (prims := prims) (T := prims.AdrsKey)) _ 0 := by
  rw [rUd_pick_eq]
  exact isQueryBoundP_bind_zero _ _ (lift_np _) fun kf =>
    simChoose_np _ A _ _ _ (udStart_np pkSeedDist kf.val)
      (fun a y => udColl_np pkSeedDist _ _ (Or.inl rfl)) (udColl_np pkSeedDist)

theorem preColl_np (key : prims.AdrsKey) (xs : List prims.Y) (hx : OkLen vp xs) :
    @IsQueryBoundP _ (preSpecC prims.AdrsKey prims.Y) _ (preColl (vp := vp) pkSeedDist key xs)
      (badG (vp := vp) (prims := prims) (T := prims.AdrsKey)) _ 0 := by
  unfold preColl
  exact isQueryBoundP_bind_zero _ _ ((isQueryBoundP_query_iff _ _ _).2 fun h => absurd hx h) fun _ =>
    isQueryBoundP_pure _ _ _

theorem preStart_np (ca : Adrs) (b : ℕ) :
    @IsQueryBoundP _ (preSpecC prims.AdrsKey prims.Y) _ (preStart (vp := vp) pkSeedDist ca b)
      (badG (vp := vp) (prims := prims) (T := prims.AdrsKey)) _ 0 := by
  unfold preStart
  split_ifs with h
  · exact lift_np _
  · unfold preChal
    exact isQueryBoundP_bind_zero _ _ ((isQueryBoundP_query_iff _ _ _).2 fun h => (show False from h).elim)
      fun _ => isQueryBoundP_pure _ _ _

/-- **SM-PRE first phase: every collection query is an SLH-DSA hash call.** -/
theorem rPre_choose_len (A : Forger vp prims optRand pkSeedDist) :
    @IsQueryBoundP _ (preSpecC prims.AdrsKey prims.Y) _ (rPre pkSeedDist (Lazy.bWotsS A)).choose
      (badG (vp := vp) (prims := prims) (T := prims.AdrsKey)) _ 0 := by
  rw [rPre_choose_eq]
  exact simChoose_np _ A _ _ _ (preStart_np pkSeedDist)
    (fun a y => preColl_np pkSeedDist _ _ (Or.inl rfl)) (preColl_np pkSeedDist)

theorem wtcrColl_np (key : prims.AdrsKey) (xs : List prims.Y) (hx : OkLen vp xs) :
    @IsQueryBoundP _ (tcrSpecC prims.AdrsKey prims.Y) _ (wtcrColl (vp := vp) pkSeedDist key xs)
      (badG (vp := vp) (prims := prims) (T := prims.AdrsKey × prims.Y)) _ 0 := by
  unfold wtcrColl
  exact isQueryBoundP_bind_zero _ _ ((isQueryBoundP_query_iff _ _ _).2 fun h => absurd hx h) fun _ =>
    isQueryBoundP_pure _ _ _

theorem tcrStart_np (ca : Adrs) (b : ℕ) :
    @IsQueryBoundP _ (tcrSpecC prims.AdrsKey prims.Y) _ (tcrStart (vp := vp) pkSeedDist ca b)
      (badG (vp := vp) (prims := prims) (T := prims.AdrsKey × prims.Y)) _ 0 := by
  unfold tcrStart
  refine isQueryBoundP_bind_zero _ _ (lift_np _) fun s => ?_
  split_ifs with h
  · exact isQueryBoundP_pure _ _ _
  · exact wtcrColl_np pkSeedDist _ _ (Or.inl rfl)

theorem tcrChain_np (a : Adrs) (y : prims.Y) :
    @IsQueryBoundP _ (tcrSpecC prims.AdrsKey prims.Y) _ (tcrChainHash (vp := vp) pkSeedDist a y)
      (badG (vp := vp) (prims := prims) (T := prims.AdrsKey × prims.Y)) _ 0 := by
  unfold tcrChainHash wtcrChal
  exact isQueryBoundP_bind_zero _ _ ((isQueryBoundP_query_iff _ _ _).2 fun h => (show False from h).elim)
    fun _ => isQueryBoundP_pure _ _ _

/-- **SM-TCR first phase: every collection query is an SLH-DSA hash call.** -/
theorem rTcrT_choose_len (A : Forger vp prims optRand pkSeedDist) :
    @IsQueryBoundP _ (tcrSpecC prims.AdrsKey prims.Y) _
      (rTcrT (vp := vp) pkSeedDist (Lazy.bWotsS A)).choose
      (badG (vp := vp) (prims := prims) (T := prims.AdrsKey × prims.Y)) _ 0 := by
  rw [rTcrT_choose_eq]
  exact simChoose_np _ A _ _ _ (tcrStart_np pkSeedDist) (tcrChain_np pkSeedDist)
    (wtcrColl_np pkSeedDist)

/-- An SM-game query that is an SLH-DSA hash call (or not a collection query). -/
def okG {T : Type} : ℕ ⊕ (T ⊕ ((_ : Unit) × prims.AdrsKey × List prims.Y)) → Prop
  | .inr (.inr q) => OkLen vp q.2.2
  | _ => True

theorem okG_of_np {T : Type} {X : OracleSpec (T ⊕ ((_ : Unit) × prims.AdrsKey × List prims.Y))}
    {α : Type} (oa : OracleComp (unifSpec + X) α)
    (h : IsQueryBoundP oa (badG (vp := vp) (prims := prims) (T := T)) 0) :
    AllQueriesSatisfy oa (okG (vp := vp) (prims := prims) (T := T)) := by
  classical
  refine (isQueryBoundP_zero_iff _ _).1 (IsQueryBoundP.of_imp (fun t ht => ?_) h)
  rcases t with n | t | q
  · exact ht trivial
  · exact ht trivial
  · exact ht

theorem rUd_pick_ok (A : Forger vp prims optRand pkSeedDist) :
    @AllQueriesSatisfy _ (udSpecC prims.AdrsKey prims.Y) _ (rUd pkSeedDist (Lazy.bWotsS A)).pick
      (okG (vp := vp) (prims := prims) (T := prims.AdrsKey)) :=
  okG_of_np _ (rUd_pick_len pkSeedDist A)

set_option maxHeartbeats 2000000 in
theorem rPre_choose_ok (A : Forger vp prims optRand pkSeedDist) :
    @AllQueriesSatisfy _ (preSpecC prims.AdrsKey prims.Y) _ (rPre pkSeedDist (Lazy.bWotsS A)).choose
      (okG (vp := vp) (prims := prims) (T := prims.AdrsKey)) :=
by
  rw [rPre_choose_eq]
  exact okG_of_np (X := SM_DT_PRE_challengeSpec prims.AdrsKey prims.Y + collSpecC prims.AdrsKey prims.Y)
    _ (simChoose_np (spec := SM_DT_PRE_challengeSpec prims.AdrsKey prims.Y +
      collSpecC prims.AdrsKey prims.Y) _ A _ _ _ (preStart_np pkSeedDist)
    (fun a y => preColl_np pkSeedDist _ _ (Or.inl rfl)) (preColl_np pkSeedDist))

set_option maxHeartbeats 2000000 in
theorem rTcrT_choose_ok (A : Forger vp prims optRand pkSeedDist) :
    @AllQueriesSatisfy _ (tcrSpecC prims.AdrsKey prims.Y) _
      (rTcrT (vp := vp) pkSeedDist (Lazy.bWotsS A)).choose
      (okG (vp := vp) (prims := prims) (T := prims.AdrsKey × prims.Y)) :=
by
  rw [rTcrT_choose_eq]
  exact okG_of_np (X := SM_DT_TCR_challengeSpec prims.AdrsKey prims.Y prims.Y +
      collSpecC prims.AdrsKey prims.Y)
    _ (simChoose_np (spec := SM_DT_TCR_challengeSpec prims.AdrsKey prims.Y prims.Y +
      collSpecC prims.AdrsKey prims.Y) _ A _ _ _ (tcrStart_np pkSeedDist) (tcrChain_np pkSeedDist)
    (wtcrColl_np pkSeedDist))

theorem preChooseI_len (A : Forger vp prims optRand pkSeedDist) :
    @IsQueryBoundP _ (preSpecC prims.AdrsKey prims.Y) _ (preChooseI pkSeedDist A)
      (badG (vp := vp) (prims := prims) (T := prims.AdrsKey)) _ 0 := by
  rw [preChooseI_eq]; exact rPre_choose_len pkSeedDist A

theorem tcrChooseI_len (A : Forger vp prims optRand pkSeedDist) :
    @IsQueryBoundP _ (tcrSpecC prims.AdrsKey prims.Y) _ (tcrChooseI pkSeedDist A)
      (badG (vp := vp) (prims := prims) (T := prims.AdrsKey × prims.Y)) _ 0 := by
  rw [tcrChooseI_eq]; exact rTcrT_choose_len pkSeedDist A

end Families

end Ideal.Realize.Wots

#print axioms Ideal.Realize.Wots.bWotsWith_choose_np
#print axioms Ideal.Realize.Wots.rUd_pick_len
#print axioms Ideal.Realize.Wots.rPre_choose_len
#print axioms Ideal.Realize.Wots.rTcrT_choose_len
