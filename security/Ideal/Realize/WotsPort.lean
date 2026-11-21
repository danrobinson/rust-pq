import Ideal.Realize.Port
import Reduction.Open.Wots

/-!
# The WOTS second phases with a compression port (realisers of `rUd`, `rPre`, `rTcrT`)

The open second phases `Reduction.Open.wotsUdOpenAll` / `wotsPreOpenAll` / `wotsTcrOpenAll` run a
forger WITHOUT compression queries.  Here the forger is a port program
(`Ideal.Realize.PortForgerProg`) whose compression queries become game queries of the open
program (the game slot `hS St Blk` of `Lazy.OSpec prims (hS St Blk)`):

* `wStd`, `wPort`, `wForgeP`, `wPhase2P` and the three programs `wUdP`, `wPreP`, `wTcrP`;
* **fusion** (`wUdP_fusion`, …): under any interpretation that answers port queries by a table
  `g`, the port program is the open program of `Reduction/Open/Wots.lean` at the forger with its
  port answered by `g`;
* counts, for a port forger with at most `qf` compression and `qs` signing queries, signed
  messages and forged message of at most `ℓ` bytes:
  - port (game-kind) queries `≤ qf` (`wUdP_port`, …);
  - hash-kind queries `≤ qs·wotsSignHistHashes + (wotsAnswerHashes + tail)` (`wUdP_hashes`, …;
    the counts of `Reduction.Open.wots*_phase2_open_hashes`);
  - `H_msg` queries `≤ qs + 2` (`wUdP_hmsg`, …): one per signing query, two in the extraction
    (the forgery's digest and the reference signature);
  - no `Thash` query on more than `B` values and no `H_msg` query on more than `ℓ` bytes, if
    every SLH-DSA hash call (`OkLen`) has at most `B` values (`wUdP_bad`, …).

The walks are generic in the counted predicate (`pw_*` lemmas): a predicate that holds of no
secret read and of no `Thash` query on `1`, `2`, `len` or `k` values counts only `H_msg` queries.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security

namespace Ideal.Realize.Wots

open Reduction Reduction.Open Reduction.Lazy Reduction.Resources2 Ideal.Realize

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]

attribute [local instance] Lazy.openQ

/-! ## Walks, generic in the counted predicate -/

section Walks

variable {ι : Type} {gspec : OracleSpec ι}
variable (p : ℕ ⊕ (ι ⊕ (SecIdx ⊕ PublicHashQuery prims.PkSeed prims.AdrsKey prims.Y)) → Prop)
  [DecidablePred p]
variable (hsec : ∀ d, ¬ p (.inr (.inr (.inl d))))
  (hth : ∀ pk key xs, OkLen vp xs → ¬ p (thIdx prims ι pk key xs))

include hth in
theorem pw_f (pk : prims.PkSeed) (a : Adrs) (y : prims.Y) :
    IsQueryBoundP (PublicHash.f prims.core pk a y : OracleComp (OSpec prims gspec) prims.Y) p 0 :=
  (isQueryBoundP_query_iff _ _ _).2 fun h => absurd h (hth _ _ _ (Or.inl rfl))

include hth in
theorem pw_h (pk : prims.PkSeed) (a : Adrs) (l r : prims.Y) :
    IsQueryBoundP (PublicHash.h prims.core pk a l r : OracleComp (OSpec prims gspec) prims.Y)
      p 0 :=
  (isQueryBoundP_query_iff _ _ _).2 fun h => absurd h (hth _ _ _ (Or.inr (Or.inl rfl)))

include hth in
theorem pw_tl (pk : prims.PkSeed) (a : Adrs) (ys : List prims.Y)
    (hys : ys.length = vp.params.len ∨ ys.length = vp.params.k) :
    IsQueryBoundP (PublicHash.tl prims.core pk a ys : OracleComp (OSpec prims gspec) prims.Y)
      p 0 :=
  (isQueryBoundP_query_iff _ _ _).2 fun h => absurd h (hth _ _ _ (Or.inr (Or.inr hys)))

include hsec in
theorem pw_sec (a : Adrs) : IsQueryBoundP (Lazy.secQ prims gspec a) p 0 :=
  (isQueryBoundP_query_iff _ _ _).2 fun h => absurd h (hsec _)

include hsec hth in
/-- The history-based signer makes as many `p`-queries as its `H_msg` query. -/
theorem pw_signFromHist (hist : List (WotsGame.Entry prims)) (pk : PublicKeyCore prims.core)
    (msg : List Byte) (R : prims.Y) (c : ℕ)
    (hm : IsQueryBoundP (PublicHash.hmsg prims.core R pk.pkSeed pk.pkRoot msg :
      OracleComp (OSpec prims gspec) _) p c) :
    IsQueryBoundP (wotsSignFromHistO (gspec := gspec) hist pk msg R) p c := by
  unfold wotsSignFromHistO
  refine (Lazy.qb_bind _ hm fun digest =>
    Lazy.qb_bind _ (m := 0) (np_forsSign p prims.core (pw_f p hth pk.pkSeed)
      (pw_h p hth pk.pkSeed) (pw_sec p hsec) _ _) fun forsSig =>
      Lazy.qb_bind _ (m := 0) (Lazy.qb_ofFnM _ _ 0 fun j =>
        Lazy.qb_bind _ (m := 0) ((Lazy.qb_authPath _ _ _ 0 0 _ _
          (fun t => pw_tl p hth _ _ _ (Or.inl (by simp)))
          (fun z t l r => pw_h p hth _ _ l r)).mono (by rw [Lazy.authB_zero]))
          fun path => isQueryBoundP_pure _ _ _)
        fun ht => isQueryBoundP_pure _ _ _).mono (by simp)

include hth in
theorem pw_tops (pk : prims.PkSeed) (sig : WotsSig vp.params prims.core) (msg : prims.Y)
    (a : Adrs) :
    IsQueryBoundP (wotsPkFromSigTopsM prims.core sig msg pk a :
      OracleComp (OSpec prims gspec) (Vector prims.Y vp.params.len)) p 0 :=
  (Lazy.qb_ofFnM _ _ 0 fun i =>
    (Lazy.qb_chain _ prims.core 0 (pw_f p hth pk) _ _ _ _).mono (by simp)).mono (by simp)

include hth in
theorem pw_layerStep (pk : prims.PkSeed) (adrs : Adrs) (idx : ℕ)
    (sig : XmssSig vp.params prims.core) (msg : prims.Y) :
    IsQueryBoundP (layerStepM prims.core pk adrs idx sig msg :
      OracleComp (OSpec prims gspec) (Vector prims.Y vp.params.len × prims.Y)) p 0 := by
  unfold layerStepM
  refine Lazy.qb_bind _ (m := 0) (pw_tops p hth pk _ _ _) fun tops =>
    Lazy.qb_bind _ (m := 0) (pw_tl p hth _ _ _ (Or.inl (by simp))) fun leaf =>
      Lazy.qb_bind _ (m := 0) ((Lazy.qb_climb _ _ 0 (fun h i l r => pw_h p hth pk _ l r) _ _ _).mono
        (by simp)) fun root => isQueryBoundP_pure _ _ _

include hth in
theorem pw_layerTrace (pkSeed : prims.PkSeed) (parts : DigestParts vp.params)
    (s : HtSigCore vp.params prims.core) (m0 : prims.Y) (n : ℕ) :
    IsQueryBoundP (layerTraceO (gspec := gspec) pkSeed parts s m0 n) p 0 := by
  induction n with
  | zero => exact isQueryBoundP_pure _ _ _
  | succ n ih =>
    unfold layerTraceO at ih ⊢
    rw [layerTraceM]
    refine Lazy.qb_bind _ (n := 0) (m := 0) ih fun r => ?_
    split_ifs with h
    · exact Lazy.qb_bind _ (m := 0) (pw_layerStep p hth _ _ _ _ _) fun x =>
        isQueryBoundP_pure _ _ _
    · exact isQueryBoundP_pure _ _ _

include hth in
theorem pw_forsPk (pk : prims.PkSeed) (sig : ForsSigCore vp.params prims.core) (md : List Byte)
    (adrs : Adrs) :
    IsQueryBoundP (forsPkFromSigM prims.core sig md pk adrs :
      OracleComp (OSpec prims gspec) prims.Y) p 0 :=
  np_forsPk p prims.core (pw_f p hth pk) (fun a ys hys => pw_tl p hth pk a ys hys)
    (pw_h p hth pk) sig md adrs

include hsec hth in
/-- The extraction tail makes the `p`-queries of its two `H_msg` queries (the forgery's digest
and the reference signature's). -/
theorem pw_answer (hist : List (WotsGame.Entry prims)) (pk : PublicKeyCore prims.core)
    (msg : List Byte) (sig : GeneralScheme.SignatureCore vp prims.core) (c : ℕ)
    (hm : IsQueryBoundP (PublicHash.hmsg prims.core sig.randomness pk.pkSeed pk.pkRoot msg :
      OracleComp (OSpec prims gspec) _) p c) :
    IsQueryBoundP (wotsAnswerOpen (gspec := gspec) hist pk msg sig) p (c + c) := by
  unfold wotsAnswerOpen
  refine (Lazy.qb_bind _ hm fun digest =>
    Lazy.qb_bind _ (pw_signFromHist p hsec hth hist pk msg sig.randomness c hm) fun ref =>
    Lazy.qb_bind _ (m := 0) (pw_forsPk p hth _ _ _ _) fun fm0 =>
    Lazy.qb_bind _ (m := 0) (pw_forsPk p hth _ _ _ _) fun hm0 =>
    Lazy.qb_bind _ (m := 0) (pw_layerTrace p hth _ _ _ _ _) fun fl =>
    Lazy.qb_bind _ (m := 0) (pw_layerTrace p hth _ _ _ _ _) fun rl =>
      isQueryBoundP_pure _ _ _).mono (by omega)

include hth in
theorem pw_win (pk : prims.PkSeed) (hist : List (WotsGame.Entry prims)) (j : ℕ) (m' : prims.Y)
    (sig' : WotsSig vp.params prims.core) :
    IsQueryBoundP (wotsWinO (gspec := gspec) pk hist j m' sig') p 0 := by
  unfold wotsWinO
  rcases hist[j]? with _ | ⟨a, m, sig, tops⟩
  · exact isQueryBoundP_pure _ _ _
  · exact Lazy.qb_bind _ (m := 0) (pw_tops p hth pk _ _ _) fun t => isQueryBoundP_pure _ _ _

include hth in
theorem pw_chainO (pk : prims.PkSeed) (a : Adrs) (x : prims.Y) (i s : ℕ) :
    IsQueryBoundP (wotsChainO (gspec := gspec) pk a x i s) p 0 :=
  (Lazy.qb_chain _ prims.core 0 (pw_f p hth pk) a x i s).mono (by simp)

include hth in
theorem pw_pre (pk : prims.PkSeed) (hist : List (WotsGame.Entry prims)) (j : ℕ) (m' : prims.Y)
    (sig' : WotsSig vp.params prims.core) :
    IsQueryBoundP (wotsPreAnswerO (gspec := gspec) pk hist j m' sig') p 0 := by
  unfold wotsPreAnswerO
  rcases hist[j]? with _ | ⟨a, m, sig, tops⟩
  · exact isQueryBoundP_pure _ _ _
  · exact (Lazy.qb_bind _ (m := 0) (wots_qb_mapM _ _ _ 0 fun i _ =>
      Lazy.qb_bind _ (m := 0) (pw_chainO p hth _ _ _ _ _) fun x =>
        Lazy.qb_bind _ (m := 0) (pw_f p hth _ _ _) fun y => isQueryBoundP_pure _ _ _)
      fun ys => isQueryBoundP_pure _ _ _).mono (by simp)

include hth in
theorem pw_tcr (pk : prims.PkSeed) (hist : List (WotsGame.Entry prims)) (j : ℕ) (m' : prims.Y)
    (sig' : WotsSig vp.params prims.core) :
    IsQueryBoundP (wotsTcrAnswerO (gspec := gspec) pk hist j m' sig') p 0 := by
  unfold wotsTcrAnswerO
  rcases hist[j]? with _ | ⟨a, m, sig, tops⟩
  · exact isQueryBoundP_pure _ _ _
  · exact (Lazy.qb_bind _ (m := 0) (wots_qb_mapM _ _ _ 0 fun i _ =>
      Lazy.qb_bind _ (m := 0) ((wots_qb_mapM _ _ _ 0 fun t ht =>
        Lazy.qb_bind _ (m := 0) (pw_chainO p hth _ _ _ _ _) fun fv =>
        Lazy.qb_bind _ (m := 0) (pw_chainO p hth _ _ _ _ _) fun hv =>
        Lazy.qb_bind _ (m := 0) (pw_f p hth _ _ _) fun y1 =>
        Lazy.qb_bind _ (m := 0) (pw_f p hth _ _ _) fun y2 =>
          isQueryBoundP_pure _ _ _).mono (by simp)) fun zs => isQueryBoundP_pure _ _ _)
      fun ys => isQueryBoundP_pure _ _ _).mono (by simp)

end Walks

/-! ## The port programs -/

section Programs

variable (optRand : PublicKeyCore prims.core → ProbComp prims.Y)

/-- The handler by which `Reduction.Open.wotsForgeOpen` runs a forger without port. -/
noncomputable def wStd (hist : List (WotsGame.Entry prims)) (pk : prims.PkSeed) (root : prims.Y) :
    QueryImpl (unifSpec + (List Byte →ₒ GeneralScheme.SignatureCore vp prims.core))
      (StateT (G2Log prims) (OracleComp (Lazy.OSpec prims (hS St Blk)))) :=
  (QueryImpl.ofLift unifSpec (OracleComp (Lazy.OSpec prims (hS St Blk)))).liftTarget
      (StateT (G2Log prims) (OracleComp (Lazy.OSpec prims (hS St Blk)))) +
    logSignOracle (spec := hS St Blk + ((SecIdx →ₒ prims.Y) + publicHashSpec prims.core))
      optRand ⟨pk, root⟩ lazyRandomizerLift (wotsSignFromHistO hist ⟨pk, root⟩)

/-- The handler by which the port program runs a port forger: sampling and signing as `wStd`, a
compression query becomes a game query. -/
noncomputable def wPort (hist : List (WotsGame.Entry prims)) (pk : prims.PkSeed) (root : prims.Y) :
    QueryImpl (FSpecP (GeneralScheme.SignatureCore vp prims.core))
      (StateT (G2Log prims) (OracleComp (Lazy.OSpec prims (hS St Blk))))
  | .inl n => wStd optRand hist pk root (.inl n)
  | .inr (.inl q) => (liftM (Lazy.gameQ prims (hS St Blk) q) :
      StateT (G2Log prims) (OracleComp (Lazy.OSpec prims (hS St Blk))) St)
  | .inr (.inr m) => wStd optRand hist pk root (.inr m)

variable (mainP : PortForgerProg vp prims)

/-- The forger run of the port program. -/
noncomputable def wForgeP (hist : List (WotsGame.Entry prims)) (root : prims.Y)
    (pk : prims.PkSeed) :
    OracleComp (Lazy.OSpec prims (hS St Blk))
      ((List Byte × GeneralScheme.SignatureCore vp prims.core) × G2Log prims) :=
  (simulateQ (wPort optRand hist pk root) (mainP ⟨pk, root⟩)).run []

/-- The complete port second phase with tail `tail`. -/
noncomputable def wPhase2P (hist : List (WotsGame.Entry prims)) (root : prims.Y)
    (pk : prims.PkSeed) {β : Type}
    (tail : ℕ × prims.Y × WotsSig vp.params prims.core →
      OracleComp (Lazy.OSpec prims (hS St Blk)) β) :
    OracleComp (Lazy.OSpec prims (hS St Blk)) β :=
  wForgeP optRand mainP hist root pk >>= fun r =>
    wotsAnswerOpen hist ⟨pk, root⟩ r.1.1 r.1.2 >>= tail

/-- **SM-UD second phase with compression port.** -/
noncomputable def wUdP (hist hist2 : List (WotsGame.Entry prims)) (root : prims.Y)
    (pk : prims.PkSeed) : OracleComp (Lazy.OSpec prims (hS St Blk)) Bool :=
  wPhase2P optRand mainP hist root pk fun x => wotsWinO pk hist2 x.1 x.2.1 x.2.2

/-- **SM-PRE second phase with compression port.** -/
noncomputable def wPreP (hist hist2 : List (WotsGame.Entry prims)) (root : prims.Y)
    (pk : prims.PkSeed) : OracleComp (Lazy.OSpec prims (hS St Blk)) (ℕ × prims.Y) :=
  wPhase2P optRand mainP hist root pk fun x => wotsPreAnswerO pk hist2 x.1 x.2.1 x.2.2

/-- **SM-TCR second phase with compression port.** -/
noncomputable def wTcrP (hist hist2 : List (WotsGame.Entry prims)) (root : prims.Y)
    (pk : prims.PkSeed) : OracleComp (Lazy.OSpec prims (hS St Blk)) (ℕ × prims.Y) :=
  wPhase2P optRand mainP hist root pk fun x => wotsTcrAnswerO pk hist2 x.1 x.2.1 x.2.2

end Programs

/-! ## Fusion -/

section Fusion

variable (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
  (pkSeedDist : ProbComp prims.PkSeed)
variable {m : Type → Type} [Monad m] [LawfulMonad m]
  (φ : QueryImpl (Lazy.OSpec prims (hS St Blk)) m) (g : CF St Blk)
  (hφ : ∀ q, φ (.inr (.inl q)) = pure (g q))
  (mainP : PortForgerProg vp prims)

/-- The forger with its port answered by `g`. -/
noncomputable def instForger : Forger vp prims optRand pkSeedDist :=
  ⟨fun pk => simulateQ (instImpl g) (mainP pk)⟩

include hφ in
theorem wForgeP_fusion (hist : List (WotsGame.Entry prims)) (root : prims.Y)
    (pk : prims.PkSeed) :
    simulateQ φ (wForgeP optRand mainP hist root pk) =
      simulateQ φ (wotsForgeOpen (gspec := hS St Blk)
        (instForger optRand pkSeedDist g mainP) hist root pk) := by
  rw [wotsForgeOpen_eq_main]
  refine port_fusion φ (instImpl g) (wStd optRand hist pk root) (wPort optRand hist pk root)
    (fun t s => ?_) _ _
  rcases t with n | q | msg
  · simp [wPort, instImpl]
  · simp [wPort, instImpl, Lazy.gameQ, hφ]
  · simp [wPort, instImpl]

include hφ in
theorem wPhase2P_fusion (hist : List (WotsGame.Entry prims)) (root : prims.Y)
    (pk : prims.PkSeed) {β : Type}
    (tail : ℕ × prims.Y × WotsSig vp.params prims.core →
      OracleComp (Lazy.OSpec prims (hS St Blk)) β) :
    simulateQ φ (wPhase2P optRand mainP hist root pk tail) =
      simulateQ φ (wotsPhase2All (instForger optRand pkSeedDist g mainP) hist root pk tail) := by
  unfold wPhase2P wotsPhase2All
  rw [simulateQ_bind, simulateQ_bind, wForgeP_fusion optRand pkSeedDist φ g hφ]

include hφ in
theorem wUdP_fusion (hist hist2 : List (WotsGame.Entry prims)) (root : prims.Y)
    (pk : prims.PkSeed) :
    simulateQ φ (wUdP optRand mainP hist hist2 root pk) =
      simulateQ φ (wotsUdOpenAll (instForger optRand pkSeedDist g mainP) hist hist2 root pk) :=
  wPhase2P_fusion optRand pkSeedDist φ g hφ mainP hist root pk _

include hφ in
theorem wPreP_fusion (hist hist2 : List (WotsGame.Entry prims)) (root : prims.Y)
    (pk : prims.PkSeed) :
    simulateQ φ (wPreP optRand mainP hist hist2 root pk) =
      simulateQ φ (wotsPreOpenAll (instForger optRand pkSeedDist g mainP) hist hist2 root pk) :=
  wPhase2P_fusion optRand pkSeedDist φ g hφ mainP hist root pk _

include hφ in
theorem wTcrP_fusion (hist hist2 : List (WotsGame.Entry prims)) (root : prims.Y)
    (pk : prims.PkSeed) :
    simulateQ φ (wTcrP optRand mainP hist hist2 root pk) =
      simulateQ φ (wotsTcrOpenAll (instForger optRand pkSeedDist g mainP) hist hist2 root pk) :=
  wPhase2P_fusion optRand pkSeedDist φ g hφ mainP hist root pk _

end Fusion

/-! ## Counts of the port programs -/

section Counts

variable (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
  (mainP : PortForgerProg vp prims)

abbrev PIdx (prims : Primitives vp.params) : Type :=
  ℕ ⊕ ((St × Blk) ⊕ (SecIdx ⊕ PublicHashQuery prims.PkSeed prims.AdrsKey prims.Y))

variable (p : PIdx prims → Prop) [DecidablePred p]

theorem wUnif_step (hu : ∀ n, ¬ p (.inl n)) (hist : List (WotsGame.Entry prims))
    (pk : prims.PkSeed) (root : prims.Y) (n : ℕ) (s : G2Log prims) :
    IsQueryBoundP ((wPort optRand hist pk root (.inl n)).run s) p 0 := by
  show IsQueryBoundP ((wStd optRand hist pk root (.inl n)).run s) p 0
  unfold wStd
  simp only [QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply, StateT.run_monadLift]
  exact isQueryBoundP_bind_zero _ _
    (liftM_np (gspec := hS St Blk) p hu (liftM (unifSpec.query n) : ProbComp _)) fun x =>
      isQueryBoundP_pure _ (x, s) _

theorem wGame_step (hist : List (WotsGame.Entry prims)) (pk : prims.PkSeed) (root : prims.Y)
    (q : St × Blk) (s : G2Log prims) (c : ℕ)
    (hq : IsQueryBoundP (Lazy.gameQ prims (hS St Blk) q) p c) :
    IsQueryBoundP ((wPort optRand hist pk root (.inr (.inl q))).run s) p c := by
  show IsQueryBoundP ((liftM (Lazy.gameQ prims (hS St Blk) q) :
    StateT (G2Log prims) (OracleComp (Lazy.OSpec prims (hS St Blk))) St).run s) p c
  rw [StateT.run_monadLift]
  exact isQueryBoundP_bind (m := 0) hq fun x _ => isQueryBoundP_pure _ (x, s) _

theorem wSign_step (hu : ∀ n, ¬ p (.inl n)) (hist : List (WotsGame.Entry prims))
    (pk : prims.PkSeed) (root : prims.Y) (msg : List Byte) (c : ℕ)
    (hsign : ∀ R, IsQueryBoundP (wotsSignFromHistO (gspec := hS St Blk) hist ⟨pk, root⟩ msg R)
      p c)
    (s : G2Log prims) :
    IsQueryBoundP ((wPort optRand hist pk root (.inr (.inr msg))).run s) p c := by
  have hstep := isQueryBoundP_bind (liftM_np (gspec := hS St Blk) p hu (optRand ⟨pk, root⟩))
    fun addrnd _ => isQueryBoundP_bind
      (liftM_np (gspec := hS St Blk) p hu (lazyRandomizer s msg addrnd)) fun R _ =>
        isQueryBoundP_bind (m := 0) (hsign R)
          fun sig _ => isQueryBoundP_pure _ (sig, s ++ [(msg, addrnd, R)]) _
  simpa [wPort, wStd, logSignOracle, lazyRandomizerLift] using hstep

/-- Queries of the complete port phase from those of its three parts. -/
theorem wPhase2P_bound (hist : List (WotsGame.Entry prims)) (root : prims.Y) (pk : prims.PkSeed)
    {β : Type} (tail : ℕ × prims.Y × WotsSig vp.params prims.core →
      OracleComp (Lazy.OSpec prims (hS St Blk)) β) (a b c : ℕ)
    (hf : IsQueryBoundP (wForgeP optRand mainP hist root pk) p a)
    (ha : ∀ r ∈ support (wForgeP optRand mainP hist root pk),
      IsQueryBoundP (wotsAnswerOpen (gspec := hS St Blk) hist ⟨pk, root⟩ r.1.1 r.1.2) p b)
    (ht : ∀ x, IsQueryBoundP (tail x) p c) :
    IsQueryBoundP (wPhase2P optRand mainP hist root pk tail) p (a + (b + c)) :=
  isQueryBoundP_bind hf fun r hr => isQueryBoundP_bind (ha r hr) fun x _ => ht x

/-- The forged message of the port run is a forged message of the port forger. -/
theorem wForgeP_out (hist : List (WotsGame.Entry prims)) (root : prims.Y) (pk : prims.PkSeed)
    (r : (List Byte × GeneralScheme.SignatureCore vp prims.core) × G2Log prims)
    (hr : r ∈ support (wForgeP optRand mainP hist root pk)) :
    r.1 ∈ support (mainP ⟨pk, root⟩) := by
  have hz : r.1 ∈ support ((simulateQ (wPort optRand hist pk root)
      (mainP ⟨pk, root⟩)).run' []) := by
    rw [StateT.run'_eq, support_map]
    exact ⟨r, hr, rfl⟩
  exact support_simulateQ_run'_subset _ _ _ hz

/-- Kinds `≠ unif` are not sampling queries. -/
theorem kind_ne_unif {K : Lazy.Kind} (hK : K ≠ .unif) (n : ℕ) :
    ¬ Lazy.kind (ι := St × Blk) (D := SecIdx)
      (κ := PublicHashQuery prims.PkSeed prims.AdrsKey prims.Y) (.inl n) = K := by
  intro h; exact hK (by simpa [Lazy.kind] using h.symm)

/-! ### Port queries -/

theorem wForgeP_port (qf : ℕ) (hist : List (WotsGame.Entry prims)) (root : prims.Y)
    (pk : prims.PkSeed)
    (hqf : IsQueryBoundP (mainP ⟨pk, root⟩)
      (fun i => isPortQ (S := GeneralScheme.SignatureCore vp prims.core) i = true) qf) :
    IsQueryBoundP (wForgeP optRand mainP hist root pk) (fun t => Lazy.kind t = .game) qf := by
  refine IsQueryBoundP.simulateQ_run_of_step hqf (fun t ht s => ?_) (fun t ht s => ?_) []
  · rcases t with n | q | msg
    · simp [isPortQ] at ht
    · exact wGame_step optRand _ hist pk root q s 1
        ((isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos)
    · simp [isPortQ] at ht
  · rcases t with n | q | msg
    · exact wUnif_step optRand _ (kind_ne_unif (by decide)) hist pk root n s
    · exact absurd rfl ht
    · exact wSign_step optRand _ (kind_ne_unif (by decide)) hist pk root msg 0
        (fun R => (wotsSignFromHistO_kindBound .game hist _ msg R).mono
          (by simp [Lazy.ind, wotsSignHistB_game])) s

theorem wPhase2P_port (qf : ℕ) (hist : List (WotsGame.Entry prims)) (root : prims.Y)
    (pk : prims.PkSeed) {β : Type} (tail : ℕ × prims.Y × WotsSig vp.params prims.core →
      OracleComp (Lazy.OSpec prims (hS St Blk)) β)
    (ht : ∀ x, IsQueryBoundP (tail x) (fun t => Lazy.kind t = .game) 0)
    (hqf : IsQueryBoundP (mainP ⟨pk, root⟩)
      (fun i => isPortQ (S := GeneralScheme.SignatureCore vp prims.core) i = true) qf) :
    IsQueryBoundP (wPhase2P optRand mainP hist root pk tail) (fun t => Lazy.kind t = .game) qf :=
  (wPhase2P_bound optRand mainP _ hist root pk tail qf 0 0
    (wForgeP_port optRand mainP qf hist root pk hqf)
    (fun r _ => (wotsAnswerOpen_kindBound .game hist _ _ _).mono
      (by simp [Lazy.ind, wotsAnswerB_game])) ht).mono (by omega)

/-! ### Hash queries -/

theorem wForgeP_hashes (qs : ℕ) (hist : List (WotsGame.Entry prims)) (root : prims.Y)
    (pk : prims.PkSeed)
    (hqs : IsQueryBoundP (mainP ⟨pk, root⟩)
      (fun i => isSignQ (S := GeneralScheme.SignatureCore vp prims.core) i = true) qs) :
    IsQueryBoundP (wForgeP optRand mainP hist root pk) (fun t => Lazy.kind t = .hash)
      (qs * wotsSignHistHashes vp) := by
  refine IsQueryBoundP.simulateQ_run_of_step_le hqs (fun t ht s => ?_) (fun t ht s => ?_) []
  · rcases t with n | q | msg
    · simp [isSignQ] at ht
    · simp [isSignQ] at ht
    · exact wSign_step optRand _ (kind_ne_unif (by decide)) hist pk root msg _
        (fun R => (wotsSignFromHistO_kindBound .hash hist _ msg R).mono
          wotsSignHistB_ind_hash) s
  · rcases t with n | q | msg
    · exact wUnif_step optRand _ (kind_ne_unif (by decide)) hist pk root n s
    · exact wGame_step optRand _ hist pk root q s 0
        ((isQueryBoundP_query_iff _ _ _).2 fun h => by simp [Lazy.kind] at h)
    · exact absurd rfl ht

theorem wPhase2P_hashes (qs c : ℕ) (hist : List (WotsGame.Entry prims)) (root : prims.Y)
    (pk : prims.PkSeed) {β : Type} (tail : ℕ × prims.Y × WotsSig vp.params prims.core →
      OracleComp (Lazy.OSpec prims (hS St Blk)) β)
    (ht : ∀ x, IsQueryBoundP (tail x) (fun t => Lazy.kind t = .hash) c)
    (hqs : IsQueryBoundP (mainP ⟨pk, root⟩)
      (fun i => isSignQ (S := GeneralScheme.SignatureCore vp prims.core) i = true) qs) :
    IsQueryBoundP (wPhase2P optRand mainP hist root pk tail) (fun t => Lazy.kind t = .hash)
      (qs * wotsSignHistHashes vp + (wotsAnswerHashes vp + c)) :=
  wPhase2P_bound optRand mainP _ hist root pk tail _ _ _
    (wForgeP_hashes optRand mainP qs hist root pk hqs)
    (fun r _ => wotsAnswerOpen_hashes hist _ _ _) ht

/-! ### `H_msg` queries -/

theorem hmsg_hth (pk : prims.PkSeed) (key : prims.AdrsKey) (xs : List prims.Y)
    (_hx : OkLen vp xs) : ¬ isHmsgIdx (thIdx prims (St × Blk) pk key xs) = true := by
  simp [isHmsgIdx]

theorem hmsg_hsec (d : SecIdx) :
    ¬ isHmsgIdx (ι := St × Blk) (P := prims.PkSeed) (K := prims.AdrsKey) (Y := prims.Y)
      (.inr (.inr (.inl d))) = true := by
  simp [isHmsgIdx]

theorem hmsg_one (R : prims.Y) (pk : prims.PkSeed) (root : prims.Y) (msg : List Byte) :
    IsQueryBoundP (PublicHash.hmsg prims.core R pk root msg :
      OracleComp (OSpec prims (hS St Blk)) _) (fun t => isHmsgIdx t = true) 1 :=
  (isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos

theorem wForgeP_hmsg (qs : ℕ) (hist : List (WotsGame.Entry prims)) (root : prims.Y)
    (pk : prims.PkSeed)
    (hqs : IsQueryBoundP (mainP ⟨pk, root⟩)
      (fun i => isSignQ (S := GeneralScheme.SignatureCore vp prims.core) i = true) qs) :
    IsQueryBoundP (wForgeP optRand mainP hist root pk) (fun t => isHmsgIdx t = true) qs := by
  have hu : ∀ n : ℕ, ¬ isHmsgIdx (ι := St × Blk) (P := prims.PkSeed) (K := prims.AdrsKey)
      (Y := prims.Y) (.inl n) = true := by
    intro n; simp [isHmsgIdx]
  refine IsQueryBoundP.simulateQ_run_of_step hqs (fun t ht s => ?_) (fun t ht s => ?_) []
  · rcases t with n | q | msg
    · simp [isSignQ] at ht
    · simp [isSignQ] at ht
    · exact wSign_step optRand _ hu hist pk root msg 1
        (fun R => pw_signFromHist _ hmsg_hsec hmsg_hth hist _ msg R 1 (hmsg_one _ _ _ _)) s
  · rcases t with n | q | msg
    · exact wUnif_step optRand _ hu hist pk root n s
    · exact wGame_step optRand _ hist pk root q s 0
        ((isQueryBoundP_query_iff _ _ _).2 fun h => by simp [isHmsgIdx] at h)
    · exact absurd rfl ht

theorem wPhase2P_hmsg (qs : ℕ) (hist : List (WotsGame.Entry prims)) (root : prims.Y)
    (pk : prims.PkSeed) {β : Type} (tail : ℕ × prims.Y × WotsSig vp.params prims.core →
      OracleComp (Lazy.OSpec prims (hS St Blk)) β)
    (ht : ∀ x, IsQueryBoundP (tail x) (fun t => isHmsgIdx t = true) 0)
    (hqs : IsQueryBoundP (mainP ⟨pk, root⟩)
      (fun i => isSignQ (S := GeneralScheme.SignatureCore vp prims.core) i = true) qs) :
    IsQueryBoundP (wPhase2P optRand mainP hist root pk tail) (fun t => isHmsgIdx t = true)
      (qs + 2) :=
  (wPhase2P_bound optRand mainP _ hist root pk tail qs (1 + 1) 0
    (wForgeP_hmsg optRand mainP qs hist root pk hqs)
    (fun r _ => pw_answer _ hmsg_hsec hmsg_hth hist _ _ _ 1 (hmsg_one _ _ _ _)) ht).mono
    (by omega)

/-! ### No long hash query -/

variable (B ℓ : ℕ)

theorem bad_hth (hB : ∀ xs : List prims.Y, OkLen vp xs → xs.length ≤ B)
    (pk : prims.PkSeed) (key : prims.AdrsKey) (xs : List prims.Y) (hx : OkLen vp xs) :
    ¬ isBadIdx B ℓ (thIdx prims (St × Blk) pk key xs) = true := by
  have := hB xs hx
  simp [isBadIdx]; omega

theorem bad_hsec (d : SecIdx) :
    ¬ isBadIdx (ι := St × Blk) (P := prims.PkSeed) (K := prims.AdrsKey) (Y := prims.Y) B ℓ
      (.inr (.inr (.inl d))) = true := by
  simp [isBadIdx]

theorem bad_hm (R : prims.Y) (pk : prims.PkSeed) (root : prims.Y) (msg : List Byte)
    (hm : msg.length ≤ ℓ) :
    IsQueryBoundP (PublicHash.hmsg prims.core R pk root msg :
      OracleComp (OSpec prims (hS St Blk)) _) (fun t => isBadIdx B ℓ t = true) 0 :=
  (isQueryBoundP_query_iff _ _ _).2 fun h => by simp [isBadIdx] at h; omega

theorem wForgeP_bad (hB : ∀ xs : List prims.Y, OkLen vp xs → xs.length ≤ B)
    (hist : List (WotsGame.Entry prims)) (root : prims.Y) (pk : prims.PkSeed)
    (hlong : IsQueryBoundP (mainP ⟨pk, root⟩)
      (fun i => isLongQ (S := GeneralScheme.SignatureCore vp prims.core) ℓ i = true) 0) :
    IsQueryBoundP (wForgeP optRand mainP hist root pk) (fun t => isBadIdx B ℓ t = true) 0 := by
  have hu : ∀ n : ℕ, ¬ isBadIdx (ι := St × Blk) (P := prims.PkSeed) (K := prims.AdrsKey)
      (Y := prims.Y) B ℓ (.inl n) = true := by
    intro n; simp [isBadIdx]
  refine qb_simulateQ_run_zero
    (p := fun i => isLongQ (S := GeneralScheme.SignatureCore vp prims.core) ℓ i = true)
    (fun t ht s => ?_) hlong []
  rcases t with n | q | msg
  · exact wUnif_step optRand _ hu hist pk root n s
  · exact wGame_step optRand _ hist pk root q s 0
      ((isQueryBoundP_query_iff _ _ _).2 fun h => by simp [isBadIdx] at h)
  · have hm : msg.length ≤ ℓ := by
      simp only [isLongQ, decide_eq_true_eq, not_lt] at ht
      exact ht
    exact wSign_step optRand _ hu hist pk root msg 0
      (fun R => pw_signFromHist _ (bad_hsec B ℓ) (bad_hth B ℓ hB) hist _ msg R 0
        (bad_hm B ℓ _ _ _ _ hm)) s

theorem wPhase2P_bad (hB : ∀ xs : List prims.Y, OkLen vp xs → xs.length ≤ B)
    (hist : List (WotsGame.Entry prims)) (root : prims.Y) (pk : prims.PkSeed) {β : Type}
    (tail : ℕ × prims.Y × WotsSig vp.params prims.core →
      OracleComp (Lazy.OSpec prims (hS St Blk)) β)
    (ht : ∀ x, IsQueryBoundP (tail x) (fun t => isBadIdx B ℓ t = true) 0)
    (hlong : IsQueryBoundP (mainP ⟨pk, root⟩)
      (fun i => isLongQ (S := GeneralScheme.SignatureCore vp prims.core) ℓ i = true) 0)
    (hout : ∀ z ∈ support (mainP ⟨pk, root⟩), z.1.length ≤ ℓ) :
    IsQueryBoundP (wPhase2P optRand mainP hist root pk tail) (fun t => isBadIdx B ℓ t = true) 0 :=
  wPhase2P_bound optRand mainP _ hist root pk tail 0 (0 + 0) 0
    (wForgeP_bad optRand mainP B ℓ hB hist root pk hlong)
    (fun r hr => pw_answer _ (bad_hsec B ℓ) (bad_hth B ℓ hB) hist _ _ _ 0
      (bad_hm B ℓ _ _ _ _ (hout _ (wForgeP_out optRand mainP hist root pk r hr)))) ht

end Counts

/-! ## The three families -/

section Families

variable (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
  (mainP : PortForgerProg vp prims) (hist hist2 : List (WotsGame.Entry prims)) (root : prims.Y)
  (pk : prims.PkSeed) {qf qs : ℕ}
  (hqf : IsQueryBoundP (mainP ⟨pk, root⟩)
    (fun i => isPortQ (S := GeneralScheme.SignatureCore vp prims.core) i = true) qf)
  (hqs : IsQueryBoundP (mainP ⟨pk, root⟩)
    (fun i => isSignQ (S := GeneralScheme.SignatureCore vp prims.core) i = true) qs)

include hqf in
theorem wUdP_port : IsQueryBoundP (wUdP optRand mainP hist hist2 root pk)
    (fun t => Lazy.kind t = .game) qf :=
  wPhase2P_port optRand mainP qf hist root pk _
    (fun x => (wotsWinO_kindBound .game pk hist2 x.1 x.2.1 x.2.2).mono (by simp [Lazy.ind])) hqf

include hqf in
theorem wPreP_port : IsQueryBoundP (wPreP optRand mainP hist hist2 root pk)
    (fun t => Lazy.kind t = .game) qf :=
  wPhase2P_port optRand mainP qf hist root pk _
    (fun x => (wotsPreAnswerO_kindBound .game pk hist2 x.1 x.2.1 x.2.2).mono
      (by simp [Lazy.ind])) hqf

include hqf in
theorem wTcrP_port : IsQueryBoundP (wTcrP optRand mainP hist hist2 root pk)
    (fun t => Lazy.kind t = .game) qf :=
  wPhase2P_port optRand mainP qf hist root pk _
    (fun x => (wotsTcrAnswerO_kindBound .game pk hist2 x.1 x.2.1 x.2.2).mono
      (by simp [Lazy.ind])) hqf

include hqs in
theorem wUdP_hashes : IsQueryBoundP (wUdP optRand mainP hist hist2 root pk)
    (fun t => Lazy.kind t = .hash)
    (qs * wotsSignHistHashes vp + (wotsAnswerHashes vp + wotsWinHashes vp)) :=
  wPhase2P_hashes optRand mainP qs _ hist root pk _
    (fun x => (wotsWinO_kindBound .hash pk hist2 x.1 x.2.1 x.2.2).mono
      (by simp [Lazy.ind, wotsWinHashes])) hqs

include hqs in
theorem wPreP_hashes : IsQueryBoundP (wPreP optRand mainP hist hist2 root pk)
    (fun t => Lazy.kind t = .hash)
    (qs * wotsSignHistHashes vp + (wotsAnswerHashes vp + wotsPreHashes vp)) :=
  wPhase2P_hashes optRand mainP qs _ hist root pk _
    (fun x => (wotsPreAnswerO_kindBound .hash pk hist2 x.1 x.2.1 x.2.2).mono
      (by simp [Lazy.ind, wotsPreHashes])) hqs

include hqs in
theorem wTcrP_hashes : IsQueryBoundP (wTcrP optRand mainP hist hist2 root pk)
    (fun t => Lazy.kind t = .hash)
    (qs * wotsSignHistHashes vp + (wotsAnswerHashes vp + wotsTcrHashes vp)) :=
  wPhase2P_hashes optRand mainP qs _ hist root pk _
    (fun x => (wotsTcrAnswerO_kindBound .hash pk hist2 x.1 x.2.1 x.2.2).mono (by
      have h1 : Lazy.ind Lazy.Kind.hash Lazy.Kind.hash = 1 := rfl
      rw [h1, wotsTcrHashes]
      exact le_of_eq (by ring))) hqs

include hqs in
theorem wUdP_hmsg : IsQueryBoundP (wUdP optRand mainP hist hist2 root pk)
    (fun t => isHmsgIdx t = true) (qs + 2) :=
  wPhase2P_hmsg optRand mainP qs hist root pk _
    (fun x => pw_win _ hmsg_hth _ _ _ _ _) hqs

include hqs in
theorem wPreP_hmsg : IsQueryBoundP (wPreP optRand mainP hist hist2 root pk)
    (fun t => isHmsgIdx t = true) (qs + 2) :=
  wPhase2P_hmsg optRand mainP qs hist root pk _
    (fun x => pw_pre _ hmsg_hth _ _ _ _ _) hqs

include hqs in
theorem wTcrP_hmsg : IsQueryBoundP (wTcrP optRand mainP hist hist2 root pk)
    (fun t => isHmsgIdx t = true) (qs + 2) :=
  wPhase2P_hmsg optRand mainP qs hist root pk _
    (fun x => pw_tcr _ hmsg_hth _ _ _ _ _) hqs

variable (B ℓ : ℕ) (hB : ∀ xs : List prims.Y, OkLen vp xs → xs.length ≤ B)
  (hlong : IsQueryBoundP (mainP ⟨pk, root⟩)
    (fun i => isLongQ (S := GeneralScheme.SignatureCore vp prims.core) ℓ i = true) 0)
  (hout : ∀ z ∈ support (mainP ⟨pk, root⟩), z.1.length ≤ ℓ)

include hB hlong hout in
theorem wUdP_bad : IsQueryBoundP (wUdP optRand mainP hist hist2 root pk)
    (fun t => isBadIdx B ℓ t = true) 0 :=
  wPhase2P_bad optRand mainP B ℓ hB hist root pk _
    (fun x => pw_win _ (bad_hth B ℓ hB) _ _ _ _ _) hlong hout

include hB hlong hout in
theorem wPreP_bad : IsQueryBoundP (wPreP optRand mainP hist hist2 root pk)
    (fun t => isBadIdx B ℓ t = true) 0 :=
  wPhase2P_bad optRand mainP B ℓ hB hist root pk _
    (fun x => pw_pre _ (bad_hth B ℓ hB) _ _ _ _ _) hlong hout

include hB hlong hout in
theorem wTcrP_bad : IsQueryBoundP (wTcrP optRand mainP hist hist2 root pk)
    (fun t => isBadIdx B ℓ t = true) 0 :=
  wPhase2P_bad optRand mainP B ℓ hB hist root pk _
    (fun x => pw_tcr _ (bad_hth B ℓ hB) _ _ _ _ _) hlong hout

end Families

end Ideal.Realize.Wots

#print axioms Ideal.Realize.Wots.wUdP_fusion
#print axioms Ideal.Realize.Wots.wPreP_fusion
#print axioms Ideal.Realize.Wots.wTcrP_fusion
#print axioms Ideal.Realize.Wots.wUdP_port
#print axioms Ideal.Realize.Wots.wUdP_hashes
#print axioms Ideal.Realize.Wots.wUdP_hmsg
#print axioms Ideal.Realize.Wots.wUdP_bad
#print axioms Ideal.Realize.Wots.wTcrP_hashes
#print axioms Ideal.Realize.Wots.wTcrP_bad
