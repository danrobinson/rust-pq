import Reduction.Resources2Wots
import Reduction.HeadlineSplit

/-!
# Phase 2 of the arity-class SM-TCR adversaries `bTcrArS n A`: own hash evaluations

Package W3.  `bTcrArS n A = TcrSplit.restrict (·.length = n) _ (Lazy.bTcrS A)`; its second phase
(`forge`, after `PK.seed` is revealed, no oracle) is `(Lazy.bTcrS A).forge` followed by a
hash-free index translation (`tcr_restrict_forge_eq`, `rfl`).  `(Lazy.bTcrS A).forge tbl pkSeed`

1. recomputes `PK.root` (`idealPk`: one top XMSS tree),
2. runs the forger once, simulating every signature from the table (`g2Run`),
3. evaluates `honestCalls tbl pkSeed`: **the whole key structure is recomputed at the revealed
   seed**, because the state carried across the reveal is the table only (the answers of the
   phase-1 target queries are not stored),
4. computes `verifyCalls` of the forgery and searches a collision (`findCollision`).

## What is formal

`tcrForgeOpen A tbl pkSeed` is the open program (`Lazy.OSpec`: every evaluation of `Thash`/`Hmsg`
of items 1–3 is a query to the hash oracle `publicHashSpec`, every secret read a query to the
secret oracle).

* `tcrForgeOpen_tbl` — interpreting the secret oracle by the table and the hash oracle by `prims`
  gives back the adversary's phase-2 program: `= liftM ((Lazy.bTcrWith my A).forge tbl pkSeed)`
  (`tcrForgeOpen_tbl_bTcrS` at `Lazy.bTcrS A`; `bTcrArS_forge_open` at `bTcrArS n A`).
* `tcrForgeOpen_hashes` — at most
  `Lazy.keygenHashes vp + qs * Lazy.signHashes vp + tcrTargets vp` hash queries;
  at SHA2-128s `269824 + qs·2007385 + 1062560399506556770327551` (`tcrForgeOpen_hashes_128s`).
* `tcr_structure_exact` — item 3 is not an artefact of the bound: `honestCalls tbl pk` is the log
  of the run of `structureFree tbl` under `prims.Thash pk`, one entry per evaluation, and has
  EXACTLY `tcrTargets vp` entries (pairwise distinct tweaks).  So phase 2 of each of the four
  adversaries `bTcrArS n A` performs a structure-size local computation: `tcrTargets vp ≈ 2^79.81`
  evaluations of `Thash` at 128s, independently of `qs`.

## What is only argued

Item 4 stays a pure tail of `tcrForgeOpen`.  Count: `verifyCalls` evaluates one verification,
`≤ k·(1+a) + 1 + d·(len·(w-1) + 1 + h')` calls (`3928` at 128s); `findCollision` evaluates
`Thash` twice for each pair (call, target) with equal tweak and different input, and the target
tweaks are pairwise distinct, so `≤ 2` per call.  Together `≤ 3·(k·(1+a) + 1 + d·(len·(w-1)+1+h'))`
(`11784` at 128s).  (`digestParts` inside `verifyCalls`: one `Hmsg`.)  Not counted: list work
(`findIdx` over the `tcrTargets` targets), the forger.

Phase 1 (`choose`): every hash value is obtained from the game (target or collection query,
`bTcrArS_choose_run`); the term contains no evaluation of `prims.Thash` (by inspection of
`Lazy.bTcrWith`, `structureVia`, `TcrSplit.route`; not a theorem, there is no cost model).
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal

namespace Reduction
namespace Resources2

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]
variable {optRand : PublicKeyCore prims.core → ProbComp prims.Y}
  {pkSeedDist : ProbComp prims.PkSeed}
variable {ι : Type} {gspec : OracleSpec ι}

attribute [local instance] Lazy.openQ Lazy.closedQ

/-! ## The structure walk as hash queries -/

/-- One `Thash` evaluation at seed `pk`, as a hash query of an open program, with the call
appended to a log (the open counterpart of `logTh`). -/
def tcrThLog (pk : prims.PkSeed) :
    QueryImpl (thSpec prims)
      (StateT (List (prims.AdrsKey × List prims.Y)) (OracleComp (Lazy.OSpec prims gspec))) :=
  fun t => StateT.mk fun L =>
    (fun y => (y, L ++ [t])) <$>
      (liftM ((Lazy.OSpec prims gspec).query
        (.inr (.inr (.inr (PublicHashQuery.thash pk t.1 t.2))))) :
        OracleComp (Lazy.OSpec prims gspec) prims.Y)

/-- Interpreting the hash oracle by `prims` turns the logged open run into the logged pure run. -/
theorem tcrThLog_tbl {α : Type} (tbl : SecretTable vp prims) (pk : prims.PkSeed)
    (P : OracleComp (thSpec prims) α) (L : List (prims.AdrsKey × List prims.Y)) :
    simulateQ (Lazy.tblImpl (gspec := gspec) (PublicHash.impl prims) tbl)
        ((simulateQ (tcrThLog (gspec := gspec) pk) P).run L) =
      pure ((simulateQ (logImpl pk) P).run L) := by
  induction P using OracleComp.inductionOn generalizing L with
  | pure a => simp; rfl
  | query_bind t k ih =>
    have h1 : (simulateQ (logImpl pk) (liftM ((thSpec prims).query t) >>= k)).run L =
        (simulateQ (logImpl pk) (k (prims.Thash pk t.1 t.2))).run (L ++ [t]) := by
      rw [simulateQ_bind, simulateQ_spec_query]; rfl
    rw [h1, ← ih]
    simp [tcrThLog, Lazy.tblImpl, StateT.run_bind, PublicHash.impl]

/-- The logged open run makes at most as many hash queries as the program makes queries. -/
theorem tcrThLog_bound {α : Type} (pk : prims.PkSeed) (K : Lazy.Kind)
    (P : OracleComp (thSpec prims) α) (n : ℕ) (h : IsQueryBoundP P (fun _ => True) n)
    (L : List (prims.AdrsKey × List prims.Y)) :
    IsQueryBoundP ((simulateQ (tcrThLog (gspec := gspec) pk) P).run L)
      (fun t => Lazy.kind t = K) n := by
  refine (IsQueryBoundP.simulateQ_run_of_step_le (cost := 1)
    (q := fun t => Lazy.kind t = K) h (fun t ht s => ?_) (fun t ht s => ?_) L).mono (by simp)
  · simp only [tcrThLog, StateT.run_mk, isQueryBoundP_map_iff]
    exact (isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos
  · exact absurd trivial ht

/-! ## Query count of the structure walk -/

theorem tcr_qb_forM {κ' : Type} {spec : OracleSpec κ'} (p : κ' → Prop) [DecidablePred p]
    {β : Type} (l : List β) (f : β → OracleComp spec PUnit) (c : ℕ)
    (h : ∀ a, IsQueryBoundP (f a) p c) : IsQueryBoundP (l.forM f) p (l.length * c) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.length_cons, Nat.succ_mul, Nat.add_comm]
    change IsQueryBoundP (f a >>= fun _ => l.forM f) p _
    exact Lazy.qb_bind p (h a) fun _ => ih

/-- Query budget of the structure walk before simplification. -/
def tcrStructB (vp : ValidatedParams) : ℕ :=
  (allBottomPositions vp).length * (vp.params.k * Lazy.merkleB 1 1 vp.params.a + 1 + 0) +
    (allXmssTrees vp).length * (Lazy.merkleB (Lazy.wotsB vp 1 0 + 1) 1 vp.params.hp + 0)

theorem tcrStructB_eq : tcrStructB vp = tcrTargets vp := by
  have h1 := Lazy.merkleB_add 1 1 vp.params.a
  have h2 := Lazy.merkleB_add (Lazy.wotsB vp 1 0 + 1) 1 vp.params.hp
  have hw : Lazy.wotsB vp 1 0 = vp.params.len * (vp.params.w - 1) := by simp [Lazy.wotsB]
  have hP := Nat.one_le_two_pow (n := vp.params.hp)
  have hA := Nat.one_le_two_pow (n := vp.params.a)
  have e1 : Lazy.merkleB 1 1 vp.params.a = 2 ^ (vp.params.a + 1) - 1 := by
    rw [pow_succ]; omega
  have e2 : Lazy.merkleB (Lazy.wotsB vp 1 0 + 1) 1 vp.params.hp =
      2 ^ vp.params.hp * (vp.params.len * (vp.params.w - 1) + 1) + (2 ^ vp.params.hp - 1) := by
    have : 2 ^ vp.params.hp * (Lazy.wotsB vp 1 0 + 1 + 1) =
        2 ^ vp.params.hp * (vp.params.len * (vp.params.w - 1) + 1) + 2 ^ vp.params.hp := by
      rw [hw]; ring
    omega
  unfold tcrStructB
  simp only [Nat.add_zero]
  rw [Resources.tcrTargets_eq', e1, e2, Resources.allBottomPositions_length_eq,
    Nat.mul_add (allXmssTrees vp).length, ← Nat.mul_assoc, ← Resources.wotsInsts_length_eq_trees,
    Resources.allXmssTrees_length_mul_pred, Nat.add_assoc]

/-- The structure walk makes at most `tcrTargets vp` hash-oracle queries, whatever the answers. -/
theorem tcr_structureFree_bound (tbl : SecretTable vp prims) :
    IsQueryBoundP (structureFree tbl) (fun _ => True) (tcrTargets vp) := by
  rw [← tcrStructB_eq]
  have hq : ∀ (key : prims.AdrsKey) (xs : List prims.Y),
      IsQueryBoundP (liftM ((thSpec prims).query (key, xs)) : OracleComp (thSpec prims) prims.Y)
        (fun _ => True) 1 := fun _ _ => (isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos
  have hs : ∀ a : Adrs, IsQueryBoundP (pure (secretOf vp prims tbl a) :
      OracleComp (thSpec prims) prims.Y) (fun _ => True) 0 := fun _ => isQueryBoundP_pure _ _ _
  unfold structureFree structureVia tcrStructB
  refine Lazy.qb_bind _ (tcr_qb_forM _ _ _ _ fun bp => ?_) fun _ =>
    tcr_qb_forM _ _ _ _ fun c => ?_
  · refine Lazy.qb_bind _ (Lazy.qb_bind _ (Lazy.qb_ofFnM _ _ _ fun i => ?_) fun roots => hq _ _)
      fun _ => isQueryBoundP_pure _ _ _
    exact Lazy.qb_merkleRoot _ _ _ 1 1 _ _
      (fun j => (Lazy.qb_bind _ (hs _) fun x => hq _ _).mono (by omega))
      (fun h i l r => hq _ _)
  · exact Lazy.qb_bind _ (Lazy.qb_xmssNode (fun _ => True) prims.core 1 1 1 0
      (fun a y => hq _ _) (fun a ys => hq _ _) (fun a l r => hq _ _) hs _ _ _)
      fun _ => isQueryBoundP_pure _ _ _

/-- **The structure recomputation of phase 2 is exact.**  `honestCalls tbl pk` — the argument of
`findCollision` in `(Lazy.bTcrS A).forge` — is the log of the run of the hash-oracle program
`structureFree tbl` under `prims.Thash pk` (`logImpl pk` appends one entry per evaluation), and
it has exactly `tcrTargets vp` entries, with pairwise distinct tweaks. -/
theorem tcr_structure_exact (hS : Structural vp prims) (tbl : SecretTable vp prims)
    (pk : prims.PkSeed) :
    honestCalls tbl pk = ((simulateQ (logImpl pk) (structureFree tbl)).run []).2 ∧
      (honestCalls tbl pk).length = tcrTargets vp ∧ ((honestCalls tbl pk).map (·.1)).Nodup :=
  ⟨honestCalls_eq_free tbl pk, (honestCalls_nodup_length hS tbl pk).2,
    (honestCalls_nodup_length hS tbl pk).1⟩

/-! ## The open phase-2 program -/

/-- Phase 2 of `Lazy.bTcrWith my A` as an open program: key generation, the forger's run with
open signing, the structure walk at the revealed seed (hash queries), then the pure collision
search. -/
noncomputable def tcrForgeOpen (A : Forger vp prims optRand pkSeedDist)
    (tbl : SecretTable vp prims) (pkSeed : prims.PkSeed) :
    OracleComp (Lazy.OSpec prims gspec) (ℕ × List prims.Y) := do
  let root ← Lazy.openKeygen prims gspec pkSeed
  let z ← runForgerLog A ⟨pkSeed, root⟩ lazyRandomizerLift
    (fun m R => Lazy.openSign prims gspec m pkSeed root R)
  let c ← (simulateQ (tcrThLog (gspec := gspec) pkSeed) (structureFree tbl)).run []
  return (findCollision pkSeed c.2 (verifyCalls ⟨pkSeed, root⟩ z.1.1 z.1.2)).getD (0, [])

/-- **Interpretation.**  With the secret oracle read from the table and the hash oracle
evaluated by `prims`, `tcrForgeOpen` is the phase-2 program of `Lazy.bTcrWith my A`. -/
theorem tcrForgeOpen_tbl (my : ProbComp (SecretTable vp prims))
    (A : Forger vp prims optRand pkSeedDist) (tbl : SecretTable vp prims)
    (pkSeed : prims.PkSeed) :
    simulateQ (Lazy.tblImpl (gspec := gspec) (PublicHash.impl prims) tbl)
        (tcrForgeOpen A tbl pkSeed) =
      (liftM ((Lazy.bTcrWith my A).forge tbl pkSeed) : OracleComp (unifSpec + gspec) _) := by
  have hrun : simulateQ (Lazy.tblImpl (gspec := gspec) (PublicHash.impl prims) tbl)
      (runForgerLog A ⟨pkSeed, idealRoot vp prims tbl pkSeed⟩ lazyRandomizerLift
        (fun m R => Lazy.openSign prims gspec m pkSeed (idealRoot vp prims tbl pkSeed) R)) =
      (liftM (g2Run A tbl (idealPk vp prims tbl pkSeed)) : OracleComp (unifSpec + gspec) _) :=
    (wots_runForgerLog_tbl A tbl ⟨pkSeed, idealRoot vp prims tbl pkSeed⟩ _ _ lazyRandomizerLift
      (fun m R => pure (idealSign vp prims tbl m ⟨pkSeed, idealRoot vp prims tbl pkSeed⟩ R))
      (fun log m a => Lazy.simulateQ_tblImpl_liftM (PublicHash.impl prims) tbl _)
      (fun m R => Lazy.openSign_tbl tbl m ⟨pkSeed, idealRoot vp prims tbl pkSeed⟩ R)).trans
    (wots_runForgerLog_pure_eq_liftM_g2RunWith A ⟨pkSeed, idealRoot vp prims tbl pkSeed⟩ _)
  have hforge : (Lazy.bTcrWith my A).forge tbl pkSeed =
      g2Run A tbl (idealPk vp prims tbl pkSeed) >>= fun z =>
        pure ((findCollision pkSeed (honestCalls tbl pkSeed)
          (verifyCalls (idealPk vp prims tbl pkSeed) z.1.1 z.1.2)).getD (0, [])) := rfl
  unfold tcrForgeOpen
  simp only [simulateQ_bind, simulateQ_pure]
  rw [Lazy.openKeygen_tbl, pure_bind, hrun, hforge, liftM_bind]
  refine bind_congr fun z => ?_
  rw [tcrThLog_tbl, pure_bind, ← honestCalls_eq_free]
  rfl

theorem tcrForgeOpen_tbl_bTcrS (A : Forger vp prims optRand pkSeedDist)
    (tbl : SecretTable vp prims) (pkSeed : prims.PkSeed) :
    simulateQ (Lazy.tblImpl (gspec := gspec) (PublicHash.impl prims) tbl)
        (tcrForgeOpen A tbl pkSeed) =
      (liftM ((Lazy.bTcrS A).forge tbl pkSeed) : OracleComp (unifSpec + gspec) _) :=
  tcrForgeOpen_tbl (Lazy.sparseTable vp prims) A tbl pkSeed

/-- Queries of kind `K` of the open phase-2 program. -/
theorem tcrForgeOpen_kindBound (A : Forger vp prims optRand pkSeedDist) (K : Lazy.Kind)
    (hK : K ≠ .unif) (qs : ℕ)
    (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs)
    (tbl : SecretTable vp prims) (pkSeed : prims.PkSeed) :
    IsQueryBoundP (tcrForgeOpen (gspec := gspec) A tbl pkSeed) (fun t => Lazy.kind t = K)
      (Lazy.keygenB vp (Lazy.ind K .sec) (Lazy.ind K .hash) +
        qs * Lazy.signB vp (Lazy.ind K .sec) (Lazy.ind K .hash) + tcrTargets vp) := by
  have hrun : ∀ root : prims.Y,
      IsQueryBoundP (runForgerLog (spec := gspec + ((SecIdx →ₒ prims.Y) + publicHashSpec prims.core))
        A ⟨pkSeed, root⟩ lazyRandomizerLift
        (fun m R => Lazy.openSign prims gspec m pkSeed root R)) (fun t => Lazy.kind t = K)
        (qs * Lazy.signB vp (Lazy.ind K .sec) (Lazy.ind K .hash)) := by
    intro root
    unfold runForgerLog
    refine IsQueryBoundP.simulateQ_run_of_step_le (hA _) (fun t ht s => ?_) (fun t ht s => ?_) []
    · cases t with
      | inl n => simp at ht
      | inr m =>
        have hstep := Lazy.qb_bind (fun t => Lazy.kind t = K)
          (Lazy.liftM_kindBound (gspec := gspec) (D := SecIdx) (V := prims.Y)
            (hspec := publicHashSpec prims.core) K hK (optRand ⟨pkSeed, root⟩)) fun addrnd =>
          Lazy.qb_bind (fun t => Lazy.kind t = K)
            (Lazy.liftM_kindBound (gspec := gspec) (D := SecIdx) (V := prims.Y)
              (hspec := publicHashSpec prims.core) K hK (lazyRandomizer s m addrnd)) fun R =>
            Lazy.qb_bind (fun t => Lazy.kind t = K) (m := 0)
              (Lazy.openSign_kindBound (gspec := gspec) K m pkSeed root R)
              fun sig => isQueryBoundP_pure _ (sig, s ++ [(m, addrnd, R)]) _
        simpa [logSignOracle, lazyRandomizerLift] using hstep
    · cases t with
      | inl n =>
        simp only [QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply, StateT.run_monadLift]
        have h0 := Lazy.qb_bind (fun t => Lazy.kind t = K) (m := 0)
          (Lazy.liftM_kindBound (gspec := gspec) (D := SecIdx) (V := prims.Y)
            (hspec := publicHashSpec prims.core) K hK
            (liftM (unifSpec.query n) : ProbComp _)) fun x => isQueryBoundP_pure _ (x, s) _
        exact h0
      | inr m => simp at ht
  unfold tcrForgeOpen
  exact (Lazy.qb_bind _ (Lazy.openKeygen_kindBound K pkSeed) fun root =>
    Lazy.qb_bind _ (hrun root) fun z =>
      Lazy.qb_bind _ (m := 0)
        (tcrThLog_bound pkSeed K _ _ (tcr_structureFree_bound tbl) []) fun c =>
          isQueryBoundP_pure _ _ _).mono (by omega)

/-- **Own hash evaluations of phase 2** (key generation, signing simulation, structure walk):
at most `keygenHashes + qs·signHashes + tcrTargets`. -/
theorem tcrForgeOpen_hashes (A : Forger vp prims optRand pkSeedDist) (qs : ℕ)
    (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs)
    (tbl : SecretTable vp prims) (pkSeed : prims.PkSeed) :
    IsQueryBoundP (tcrForgeOpen (gspec := gspec) A tbl pkSeed) (fun t => Lazy.kind t = .hash)
      (Lazy.keygenHashes vp + qs * Lazy.signHashes vp + tcrTargets vp) :=
  (tcrForgeOpen_kindBound A .hash (by decide) qs hA tbl pkSeed).mono
    (Nat.add_le_add_right (Nat.add_le_add Lazy.keygenB_hash (Nat.mul_le_mul_left _ (by
      simpa [Lazy.ind] using Lazy.signB_hash (vp := vp)))) _)

/-! ## The restricted adversaries -/

/-- Phase 2 of a restricted adversary: `B.forge`, then a hash-free index translation. -/
theorem tcr_restrict_forge_eq {PkSeed Tweak Y : Type} [DecidableEq Tweak]
    {th : TweakableHash PkSeed Tweak (List Y) Y} {N : ℕ} (P : List Y → Prop) [DecidablePred P]
    (d : {xs : List Y // P xs})
    (B : TweakableHash.SM_DT_TCR_Adversary (TweakableHash.SM_DT_TCR_Problem.standalone th N))
    (s : B.State × List (Tweak × List Y)) (pk : PkSeed) :
    (TcrSplit.restrict P d B).forge s pk = B.forge s.1 pk >>= fun jm =>
      pure (match s.2[jm.1]? with
        | some q => if h : P q.2 ∧ P jm.2 then (TcrSplit.classIdx P s.2 jm.1, ⟨jm.2, h.2⟩)
            else (s.2.length, d)
        | none => (s.2.length, d)) := rfl

/-- **Phase 2 of `bTcrArS n A`** is the interpretation of `tcrForgeOpen A tbl pk` followed by the
index translation of `TcrSplit.restrict`. -/
theorem bTcrArS_forge_open (n : ℕ) (A : Forger vp prims optRand pkSeedDist)
    (tbl : SecretTable vp prims) (L : List (prims.AdrsKey × List prims.Y)) (pk : prims.PkSeed) :
    (liftM ((bTcrArS n A).forge (tbl, L) pk) : OracleComp (unifSpec + gspec) _) =
      simulateQ (Lazy.tblImpl (gspec := gspec) (PublicHash.impl prims) tbl)
        (tcrForgeOpen A tbl pk) >>= fun jm =>
        pure (match L[jm.1]? with
          | some q => if h : q.2.length = n ∧ jm.2.length = n then
              (TcrSplit.classIdx (fun xs : List prims.Y => xs.length = n) L jm.1, ⟨jm.2, h.2⟩)
              else (L.length, arityDefault prims n)
          | none => (L.length, arityDefault prims n)) := by
  rw [tcrForgeOpen_tbl_bTcrS]
  have h : (bTcrArS n A).forge (tbl, L) pk = _ :=
    tcr_restrict_forge_eq (fun xs : List prims.Y => xs.length = n) (arityDefault prims n)
      (Lazy.bTcrS A) (tbl, L) pk
  rw [h, liftM_bind]
  simp only [liftM_pure]
  refine bind_congr fun jm => congrArg pure ?_
  rcases L[jm.1]? with _ | q
  · rfl
  · rfl

end Resources2
end Reduction

/-! ## SLH-DSA-SHA2-128s -/

namespace Reduction
namespace Resources2

/-- Own hash evaluations of phase 2 of `bTcrArS n A` at SHA2-128s (items 1–3):
`≤ 269824 + qs·2007385 + 1062560399506556770327551`. -/
theorem tcrForgeOpen_hashes_128s {ι : Type} {gspec : OracleSpec ι}
    (optRand : PublicKeyCore Link.prims.core → ProbComp Link.prims.Y)
    (pkSeedDist : ProbComp Link.prims.PkSeed)
    (A : Forger Link.vp Link.prims optRand pkSeedDist) (qs : ℕ)
    (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs)
    (tbl : SecretTable Link.vp Link.prims) (pkSeed : Link.prims.PkSeed) :
    IsQueryBoundP (tcrForgeOpen (gspec := gspec) A tbl pkSeed) (fun t => Lazy.kind t = .hash)
      (269824 + qs * 2007385 + 1062560399506556770327551) := by
  have h := tcrForgeOpen_hashes (gspec := gspec) A qs hA tbl pkSeed
  rwa [keygenHashes_128s, signHashes_128s, Resources.tcrTargets_128s_val] at h

#print axioms tcrThLog_tbl
#print axioms tcr_structureFree_bound
#print axioms tcr_structure_exact
#print axioms tcrForgeOpen_tbl
#print axioms tcrForgeOpen_tbl_bTcrS
#print axioms tcrForgeOpen_hashes
#print axioms bTcrArS_forge_open
#print axioms tcrForgeOpen_hashes_128s

end Resources2
end Reduction
