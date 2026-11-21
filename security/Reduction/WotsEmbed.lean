import Reduction.Tables
import Reduction.WotsSim

/-!
# Step 7: embedding class `wots` into the WOTS game

`bWots A` (EC: `R_MEUFGCMAWOTSTWESNPRF_EUFNAGCMA ∘ R_FLSLXMSSMTTWESNPRFEUFNAGCMA_EUFCMA`).

* `choose` (seed hidden): sample the table (only its FORS entries are used) and evaluate the whole
  hypertree.  `msgAt ℓ tree leaf` is the message WOTS+-signed by the instance at layer `ℓ`, tree
  `tree`, leaf `leaf`: the FORS public key of that bottom position for `ℓ = 0`, and the root of
  the child XMSS tree `(ℓ - 1, tree · 2^h' + leaf)` otherwise; `msgAt d 0 0` is `PK.root`.
  An XMSS root is the Merkle root over the leaves `T_len(chain ends)`, every `Thash` call going to
  the collection oracle; the chain ends of a WOTS+ instance are obtained from the game's signing
  oracle on that instance's message (`topsAt`, memoised in the mirrored signing history).  Every
  WOTS+ instance of the hypertree is signed exactly once (`chooseBody` visits all of them).
  The table is the eager `2^256`-cell `sampleTable` as written.
  `#inst = Σ_{j<d} 2^(h−j·h') = 9241421688590303744 ≈ 2^63.003` signing queries at 128s
  (`Resources.wotsInsts_length_128s`); the `2^h` FORS public keys are computed locally.  Not
  feasible in any variant.
* `forge` (seed revealed): answer signing queries from the recorded WOTS+ signatures
  (`signFromHist`: FORS part from the table; at each layer the recorded WOTS+ signature of the
  instance on the path and the authentication path over the recorded chain ends), run `A` once
  as in `G2`, and output the layer found by `wotsLayer?` with the forged message and WOTS+
  signature there.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal

namespace Reduction

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]
variable {optRand : PublicKeyCore prims.core → ProbComp prims.Y}
  {pkSeedDist : ProbComp prims.PkSeed}

/-! ## The adversary -/

/-- Phase-1 oracle interface of a WOTS-game adversary. -/
abbrev WSpec (prims : Primitives vp.params) :=
  unifSpec + (WotsGame.signSpec prims + WotsGame.collSpec prims)

/-- Phase-1 monad of `bWots`: the oracle interface plus the mirrored signing history. -/
abbrev WM (prims : Primitives vp.params) :=
  StateT (List (WotsGame.Entry prims)) (OracleComp (WSpec prims))

/-- Collection query (a refused query is read as `default`). -/
def wColl (key : prims.AdrsKey) (xs : List prims.Y) : WM prims prims.Y := do
  let r ← (monadLift ((WSpec prims).query (Sum.inr (Sum.inr (key, xs))) :
    OracleComp (WSpec prims) (Option prims.Y)) : WM prims (Option prims.Y))
  pure (r.getD default)

/-- The chain ends of instance `a`: recorded ones if the instance was already signed, otherwise
compute its message by `msg`, query the signing oracle and record the answer. -/
def topsAt (a : Adrs) (msg : WM prims prims.Y) : WM prims (Vector prims.Y vp.params.len) := do
  let hist ← get
  match hist.find? (fun e => decide (e.1 = a)) with
  | some e => pure e.2.2.2
  | none => do
    let m ← msg
    let r ← (monadLift ((WSpec prims).query (Sum.inr (Sum.inl (a, m))) :
      OracleComp (WSpec prims)
        (Option (WotsSig vp.params prims.core × Vector prims.Y vp.params.len))) :
      WM prims (Option (WotsSig vp.params prims.core × Vector prims.Y vp.params.len)))
    match r with
    | some (sig, tops) => do
      modify (· ++ [(a, m, sig, tops)])
      pure tops
    | none => pure (Vector.replicate vp.params.len default)

/-- The FORS address of bottom position `(tree, leaf)`. -/
def bottomForsAdrs (tree leaf : ℕ) : Adrs :=
  ((Adrs.zero.setTreeAddress tree).setTypeAndClear .forsTree).setKeyPairAddress leaf

/-- The message signed by the WOTS+ instance at `(layer, tree, leaf)`; see the module docstring. -/
def msgAt (tbl : SecretTable vp prims) : ℕ → ℕ → ℕ → WM prims prims.Y
  | 0, tree, leaf =>
    forsPkGenWithSecret prims.core (fun a x => wColl (prims.adrsToKey a) [x])
      (fun a l r => wColl (prims.adrsToKey a) [l, r]) (fun a xs => wColl (prims.adrsToKey a) xs)
      (fun a => pure (secretOf vp prims tbl a)) (bottomForsAdrs tree leaf)
  | l + 1, tree, leaf =>
    PerfectMerkleTree.merkleRootM
      (fun t => do
        let tops ← topsAt
          (wotsLeafAdrs (GeneralHypertree.layerAdrs l (tree * 2 ^ vp.params.hp + leaf)) t)
          (msgAt tbl l (tree * 2 ^ vp.params.hp + leaf) t)
        wColl (prims.adrsToKey (wotsPkAdrs
          (wotsLeafAdrs (GeneralHypertree.layerAdrs l (tree * 2 ^ vp.params.hp + leaf)) t)))
          tops.toList)
      (xmssNodeHashWith (fun a l r => wColl (prims.adrsToKey a) [l, r])
        (GeneralHypertree.layerAdrs l (tree * 2 ^ vp.params.hp + leaf)))
      vp.params.hp 0

/-- Phase 1 of `bWots` after the table is drawn: sign every WOTS+ instance of the hypertree
(memoised, so each exactly once), then return `PK.root`. -/
def chooseBody (tbl : SecretTable vp prims) : WM prims prims.Y := do
  (allWotsInstances vp).forM fun pos => do
    let _ ← topsAt (wotsInstanceAdrs pos) (msgAt tbl pos.layer.val pos.tree.val pos.leaf.val)
    pure ()
  msgAt tbl vp.params.d 0 0

/-- The recorded entry of instance `a` (a dummy if there is none). -/
def histEntry (hist : List (WotsGame.Entry prims)) (a : Adrs) : WotsGame.Entry prims :=
  (hist.find? (fun e => decide (e.1 = a))).getD
    (a, default, Vector.replicate vp.params.len default, Vector.replicate vp.params.len default)

/-- Phase-2 signer of `bWots`: honest FORS part from the table; at each hypertree layer the
recorded WOTS+ signature of the instance on the path, and the authentication path of the Merkle
tree over the leaves `T_len(recorded chain ends)`. -/
def signFromHist (tbl : SecretTable vp prims) (hist : List (WotsGame.Entry prims))
    (pk : PublicKeyCore prims.core) (msg : List Byte) (R : prims.Y) :
    GeneralScheme.SignatureCore vp prims.core :=
  let parts : DigestParts vp.params := digestParts pk R msg
  let forsSig : ForsSigCore vp.params prims.core :=
    (forsSignWithSecret prims.core (fun a x => prims.F pk.pkSeed a x)
      (fun a l r => prims.H pk.pkSeed a l r) (fun a => secretOf vp prims tbl a)
      parts.md.toList parts.forsAdrs : Id (ForsSigCore vp.params prims.core))
  let ht : GeneralHypertree.Signature vp prims.core :=
    Vector.ofFn fun j : Fin vp.params.d =>
      let pos := LayerPosition.atLayer vp parts j
      ⟨(histEntry hist (wotsInstanceAdrs pos)).2.2.1,
        Id.run (PerfectMerkleTree.intrinsicAuthPathM
          (fun t => (pure (prims.Tl pk.pkSeed (wotsPkAdrs (wotsLeafAdrs pos.toAdrs t))
            (histEntry hist (wotsLeafAdrs pos.toAdrs t)).2.2.2.toList) : Id prims.Y))
          (xmssNodeHashWith (fun a l r => (pure (prims.H pk.pkSeed a l r) : Id prims.Y))
            pos.toAdrs)
          pos.leaf.val vp.params.hp)⟩
  ⟨R, forsSig, ht⟩

/-- The WOTS-game answer extracted from a forgery. -/
def wotsAnswer (tbl : SecretTable vp prims) (hist : List (WotsGame.Entry prims))
    (pk : PublicKeyCore prims.core) (msg : List Byte)
    (sig : GeneralScheme.SignatureCore vp prims.core) :
    ℕ × prims.Y × WotsSig vp.params prims.core :=
  let parts : DigestParts vp.params := digestParts pk sig.randomness msg
  let ref := signFromHist tbl hist pk msg sig.randomness
  match wotsLayer? pk parts sig ref with
  | none => (0, default, Vector.replicate vp.params.len default)
  | some j =>
    (hist.findIdx (fun e => decide (e.1 = layerWotsAdrs parts j)),
      layerMsg pk.pkSeed parts sig.hypertree
        (forsPkFromSig prims sig.fors parts.md.toList pk.pkSeed parts.forsAdrs) j.val,
      (sig.hypertree[j.val]).wots)

/-- The WOTS-game adversary built from a forger. -/
noncomputable def bWots (A : Forger vp prims optRand pkSeedDist) : WotsGame.Adversary prims where
  State := SecretTable vp prims × List (WotsGame.Entry prims) × prims.Y
  choose := do
    let tbl ← (monadLift (sampleTable vp prims) :
      OracleComp (WSpec prims) (SecretTable vp prims))
    let (root, hist) ← (chooseBody tbl).run []
    return (tbl, hist, root)
  forge := fun st pkSeed => do
    let pk : PublicKeyCore prims.core := ⟨pkSeed, st.2.2⟩
    let ((msg, sig), _) ← g2RunWith A pk (signFromHist st.1 st.2.1 pk)
    return wotsAnswer st.1 st.2.1 pk msg sig

/-! ## Honest objects as pure functions of the table (specification side) -/

/-- The honest message of the WOTS+ instance at `(layer, tree, leaf)`: the FORS public key of the
bottom position for layer `0`, the root of the child XMSS tree otherwise. -/
def hMsg (tbl : SecretTable vp prims) (pk : prims.PkSeed) : ℕ → ℕ → ℕ → prims.Y
  | 0, tree, leaf =>
    Id.run (forsPkGenWithSecret prims.core (fun a x => pure (prims.F pk a x))
      (fun a l r => pure (prims.H pk a l r)) (fun a xs => pure (prims.Tl pk a xs))
      (fun a => pure (secretOf vp prims tbl a)) (bottomForsAdrs tree leaf))
  | l + 1, tree, leaf =>
    Id.run (xmssRootWithSecret prims.core (fun a x => pure (prims.F pk a x))
      (fun a xs => pure (prims.Tl pk a xs)) (fun a l r => pure (prims.H pk a l r))
      (fun a => pure (secretOf vp prims tbl a))
      (GeneralHypertree.layerAdrs l (tree * 2 ^ vp.params.hp + leaf)))

/-- The honest message of the instance with base address `a`. -/
def hMsgA (tbl : SecretTable vp prims) (pk : prims.PkSeed) (a : Adrs) : prims.Y :=
  hMsg tbl pk a.layer a.tree a.word1

/-- The table's start values of the instance with base address `a`. -/
def startsOf (tbl : SecretTable vp prims) (a : Adrs) : Vector prims.Y vp.params.len :=
  Vector.ofFn fun i : Fin vp.params.len => secretOf vp prims tbl (wotsSkAdrs a i.val)

/-- The honest history entry of the instance with base address `a`. -/
def entryOf (tbl : SecretTable vp prims) (pk : prims.PkSeed) (a : Adrs) : WotsGame.Entry prims :=
  (a, hMsgA tbl pk a, WotsGame.hybSig 0 pk a (hMsgA tbl pk a) (startsOf tbl a),
    wotsPkFromSigTops prims (WotsGame.hybSig 0 pk a (hMsgA tbl pk a) (startsOf tbl a))
      (hMsgA tbl pk a) pk a)

/-- A history is *good*: every entry is the honest entry of its instance, and every instance of
the hypertree has an entry. -/
def HistGood (tbl : SecretTable vp prims) (pk : prims.PkSeed)
    (hist : List (WotsGame.Entry prims)) : Prop :=
  (∀ e ∈ hist, e = entryOf tbl pk e.1) ∧ ∀ a ∈ wotsInsts vp, a ∈ hist.map (·.1)

/-! ## The WOTS game's phase-1 oracles over an arbitrary base monad -/

/-- `WotsGame.signOracle 0` with the start values drawn by `samp` in a base monad `m`. -/
def signOracleIn {m : Type → Type} [Monad m]
    (samp : Adrs → m (Vector prims.Y vp.params.len)) (insts : List Adrs) (pk : prims.PkSeed) :
    QueryImpl (WotsGame.signSpec prims) (StateT (List (WotsGame.Entry prims)) m) :=
  fun q => do
    let hist ← get
    if q.1 ∉ insts ∨ q.1 ∈ hist.map (·.1) then
      return none
    else
      let ss ← (monadLift (samp q.1) :
        StateT (List (WotsGame.Entry prims)) m (Vector prims.Y vp.params.len))
      let sig := WotsGame.hybSig 0 pk q.1 q.2 ss
      let tops := wotsPkFromSigTops prims sig q.2 pk q.1
      set (hist ++ [(q.1, q.2, sig, tops)])
      return some (sig, tops)

/-- `WotsGame.collOracle` over a base monad `m`. -/
def collOracleIn {m : Type → Type} [Monad m] (insts : List Adrs) (pk : prims.PkSeed) :
    QueryImpl (WotsGame.collSpec prims) (StateT (List (WotsGame.Entry prims)) m) :=
  fun q => pure (if WotsGame.reservedKey insts q.1 then none else some (prims.Thash pk q.1 q.2))

/-- `WotsGame.oracles 0` over a base monad `m`: uniform sampling by `u`, start values by `samp`. -/
def oraclesIn {m : Type → Type} [Monad m] (u : QueryImpl unifSpec m)
    (samp : Adrs → m (Vector prims.Y vp.params.len)) (insts : List Adrs) (pk : prims.PkSeed) :
    QueryImpl (WSpec prims) (StateT (List (WotsGame.Entry prims)) m) :=
  u.liftTarget (StateT (List (WotsGame.Entry prims)) m) +
    (signOracleIn samp insts pk + collOracleIn (m := m) insts pk)

/-- The game's oracles with every instance's start values read from the table. -/
noncomputable abbrev tblOracles (tbl : SecretTable vp prims) (pk : prims.PkSeed) :
    QueryImpl (WSpec prims) (StateT (List (WotsGame.Entry prims)) ProbComp) :=
  oraclesIn (m := ProbComp) (QueryImpl.ofLift unifSpec ProbComp)
    (fun a => (pure (startsOf tbl a) : ProbComp (Vector prims.Y vp.params.len)))
    (wotsInsts vp) pk

/-- Table cell `i` is a WOTS+ start-value cell of the hypertree. -/
def IsWotsCell (vp : ValidatedParams) (i : SecIdx) : Prop :=
  ∃ a ∈ wotsInsts vp, ∃ j : Fin vp.params.len, secIdx (wotsSkAdrs a j.val) = i

set_option linter.unusedSectionVars false

/-! ## Lemmas

Helper blocks `x1_*` (layer 0 of phase 1), `x2_*` (phase 1 against the table-reading oracles),
`y_*` (the phase-2 signer and the extracted answer), `z_*` (independence of the WOTS+ cells),
then the simulation coupling (`section Glue`) and `stepWotsEmbed`. -/

/-! ### X1 helpers -/

/-- One oracle per hash callback: address and input list. -/
abbrev x1_spec (prims : Primitives vp.params) : OracleSpec (Adrs × List prims.Y) :=
  (Adrs × List prims.Y) →ₒ prims.Y

/-- The FORS public key as a free program over the hash callbacks. -/
def x1_free (tbl : SecretTable vp prims) (adrs : Adrs) : OracleComp (x1_spec prims) prims.Y :=
  forsPkGenWithSecret prims.core
    (fun a x => (liftM ((x1_spec prims).query (a, [x])) : OracleComp (x1_spec prims) prims.Y))
    (fun a l r => (liftM ((x1_spec prims).query (a, [l, r])) : OracleComp (x1_spec prims) prims.Y))
    (fun a xs => (liftM ((x1_spec prims).query (a, xs)) : OracleComp (x1_spec prims) prims.Y))
    (fun a => pure (secretOf vp prims tbl a)) adrs

/-- Handler in the adversary monad. -/
def x1_implW : QueryImpl (x1_spec prims) (WM prims) :=
  fun q => wColl (prims.adrsToKey q.1) q.2

/-- Pure handler. -/
def x1_implId (pk : prims.PkSeed) : QueryImpl (x1_spec prims) Id :=
  fun q => prims.Thash pk (prims.adrsToKey q.1) q.2

/-- Addresses whose key is never reserved. -/
def x1_Good (vp : ValidatedParams) (a : Adrs) : Prop :=
  AddressFacts vp a ∧ a.type ≠ AddrType.wotsHash.toCode

theorem x1_not_reserved (hS : Structural vp prims) {a : Adrs} (ha : x1_Good vp a) :
    WotsGame.reservedKey (wotsInsts vp) (prims.adrsToKey a) = false := by
  by_contra hne
  have hres : WotsGame.reservedKey (wotsInsts vp) (prims.adrsToKey a) = true := by
    simpa using hne
  simp only [WotsGame.reservedKey, List.any_eq_true, List.mem_range, decide_eq_true_eq] at hres
  obtain ⟨b, hb, i, hi, t, ht, hk⟩ := hres
  simp only [wotsInsts, List.mem_map] at hb
  obtain ⟨pos, -, rfl⟩ := hb
  have h1 : a = wotsStepAdrs (pos, ⟨i, hi⟩) ⟨t, ht⟩ :=
    hS.keyInj ha.1 (addressFacts_wotsStepAdrs hS.bounds _ _) hk
  exact ha.2 (by rw [h1]; rfl)

theorem x1_coll_run (hS : Structural vp prims) (tbl : SecretTable vp prims) (pk : prims.PkSeed)
    {a : Adrs} (ha : x1_Good vp a) (xs : List prims.Y) (h g : List (WotsGame.Entry prims)) :
    (simulateQ (tblOracles tbl pk) ((wColl (prims.adrsToKey a) xs).run h)).run g =
      pure ((prims.Thash pk (prims.adrsToKey a) xs, h), g) := by
  simp [wColl, oraclesIn, collOracleIn, x1_not_reserved hS ha]

/-- The relational predicate on free programs. -/
def x1_Q (tbl : SecretTable vp prims) (pk : prims.PkSeed) {α : Type}
    (x : OracleComp (x1_spec prims) α) : Prop :=
  ∀ h g : List (WotsGame.Entry prims),
    (simulateQ (tblOracles tbl pk) ((simulateQ x1_implW x).run h)).run g =
      pure ((Id.run (simulateQ (x1_implId pk) x), h), g)

theorem x1_Q_pure (tbl : SecretTable vp prims) (pk : prims.PkSeed) {α : Type} (x : α) :
    x1_Q tbl pk (pure x : OracleComp (x1_spec prims) α) := by
  intro h g
  simp

theorem x1_Q_bind (tbl : SecretTable vp prims) (pk : prims.PkSeed) {α β : Type}
    (oa : OracleComp (x1_spec prims) α) (ob : α → OracleComp (x1_spec prims) β)
    (ha : x1_Q tbl pk oa) (hb : ∀ x, x1_Q tbl pk (ob x)) : x1_Q tbl pk (oa >>= ob) := by
  intro h g
  simp only [simulateQ_bind, StateT.run_bind, ha h g, pure_bind, hb _ h g]
  rfl

theorem x1_Q_query (hS : Structural vp prims) (tbl : SecretTable vp prims) (pk : prims.PkSeed)
    {a : Adrs} (ha : x1_Good vp a) (xs : List prims.Y) :
    x1_Q tbl pk (liftM ((x1_spec prims).query (a, xs)) : OracleComp (x1_spec prims) prims.Y) := by
  intro h g
  simp only [simulateQ_spec_query]
  exact x1_coll_run hS tbl pk ha xs h g

theorem x1_bottom_eq (tree leaf : ℕ) (htree : tree < 2 ^ layerTreeHeight vp 0)
    (hleaf : leaf < 2 ^ vp.params.hp) :
    bottomForsAdrs tree leaf = (⟨⟨tree, htree⟩, ⟨leaf, hleaf⟩⟩ : BottomPosition vp).forsAdrs :=
  rfl

theorem x1_good_node (hS : Structural vp prims) (pos : BottomPosition vp) {z t : ℕ}
    (hz : z ≤ vp.params.a) (ht : t < vp.params.k * 2 ^ vp.params.a) :
    x1_Good vp (forsNodeAdrs pos.forsAdrs z t) :=
  ⟨addressFacts_forsNodeAdrs hS.bounds pos
    (lt_of_le_of_lt (hz.trans hS.bounds.a_le) (by norm_num))
    (lt_of_lt_of_le ht hS.bounds.forsIndex_le),
    by show AddrType.forsTree.toCode ≠ AddrType.wotsHash.toCode; decide⟩

theorem x1_good_pk (hS : Structural vp prims) (pos : BottomPosition vp) :
    x1_Good vp (forsPkAdrs pos.forsAdrs) :=
  ⟨addressFacts_forsPkAdrs hS.bounds pos,
    by show AddrType.forsRoots.toCode ≠ AddrType.wotsHash.toCode; decide⟩

theorem x1_free_Q (hS : Structural vp prims) (tbl : SecretTable vp prims) (pk : prims.PkSeed)
    (pos : BottomPosition vp) : x1_Q tbl pk (x1_free (prims := prims) tbl pos.forsAdrs) := by
  unfold x1_free forsPkGenWithSecret
  refine x1_Q_bind tbl pk _ _ ?_ fun roots => x1_Q_query hS tbl pk (x1_good_pk hS pos) _
  refine Vector.ofFnM_pred (fun {α} x => x1_Q tbl pk x) (x1_Q_pure tbl pk) (x1_Q_bind tbl pk) _
    fun i => ?_
  refine PerfectMerkleTree.merkleRootM_pred_of_subtree (fun {α} x => x1_Q tbl pk x)
    (x1_Q_bind tbl pk) _ _ _ _ ?_ ?_
  · intro j hj
    refine x1_Q_bind tbl pk _ _ (x1_Q_pure tbl pk _) fun x =>
      x1_Q_query hS tbl pk (x1_good_node hS pos (Nat.zero_le _) ?_) _
    have : j < (i.val + 1) * 2 ^ vp.params.a := by
      have := Nat.lt_succ_iff.mpr (le_of_eq hj)
      exact (Nat.div_lt_iff_lt_mul (by positivity)).mp this
    exact lt_of_lt_of_le this (Nat.mul_le_mul_right _ i.isLt)
  · intro z j hz hza hj l r
    refine x1_Q_query hS tbl pk (x1_good_node hS pos hza ?_) _
    have h1 : j < (i.val + 1) * 2 ^ (vp.params.a - z) :=
      (Nat.div_lt_iff_lt_mul (by positivity)).mp (Nat.lt_succ_iff.mpr (le_of_eq hj))
    have h2 : (i.val + 1) * 2 ^ (vp.params.a - z) ≤ vp.params.k * 2 ^ vp.params.a :=
      Nat.mul_le_mul i.isLt (Nat.pow_le_pow_right (by norm_num) (Nat.sub_le _ _))
    exact lt_of_lt_of_le h1 h2

theorem x1_msgAt_eq (tbl : SecretTable vp prims) (tree leaf : ℕ) :
    msgAt tbl 0 tree leaf =
      simulateQ x1_implW (x1_free (prims := prims) tbl (bottomForsAdrs tree leaf)) := by
  have := forsPkGenWithSecret_natural prims.core (simulateQ' (x1_implW (prims := prims)))
    (fun a x => (liftM ((x1_spec prims).query (a, [x])) : OracleComp (x1_spec prims) prims.Y))
    (fun a x => wColl (prims.adrsToKey a) [x])
    (fun a l r => (liftM ((x1_spec prims).query (a, [l, r])) : OracleComp (x1_spec prims) prims.Y))
    (fun a l r => wColl (prims.adrsToKey a) [l, r])
    (fun a xs => (liftM ((x1_spec prims).query (a, xs)) : OracleComp (x1_spec prims) prims.Y))
    (fun a xs => wColl (prims.adrsToKey a) xs)
    (fun a => pure (secretOf vp prims tbl a)) (fun a => pure (secretOf vp prims tbl a))
    (fun _ _ => by simp [x1_implW]) (fun _ _ _ => by simp [x1_implW])
    (fun _ _ => by simp [x1_implW]) (fun _ _ => by simp) (bottomForsAdrs tree leaf)
  exact this.symm

theorem x1_hMsg_eq (tbl : SecretTable vp prims) (pk : prims.PkSeed) (tree leaf : ℕ) :
    hMsg tbl pk 0 tree leaf =
      Id.run (simulateQ (x1_implId pk)
        (x1_free (prims := prims) tbl (bottomForsAdrs tree leaf))) := by
  have := forsPkGenWithSecret_natural prims.core (simulateQ' (x1_implId (prims := prims) pk))
    (fun a x => (liftM ((x1_spec prims).query (a, [x])) : OracleComp (x1_spec prims) prims.Y))
    (fun a x => pure (prims.F pk a x))
    (fun a l r => (liftM ((x1_spec prims).query (a, [l, r])) : OracleComp (x1_spec prims) prims.Y))
    (fun a l r => pure (prims.H pk a l r))
    (fun a xs => (liftM ((x1_spec prims).query (a, xs)) : OracleComp (x1_spec prims) prims.Y))
    (fun a xs => pure (prims.Tl pk a xs))
    (fun a => pure (secretOf vp prims tbl a)) (fun a => pure (secretOf vp prims tbl a))
    (fun _ _ => by simp [x1_implId]; rfl) (fun _ _ _ => by simp [x1_implId]; rfl)
    (fun _ _ => by simp [x1_implId]; rfl) (fun _ _ => by simp) (bottomForsAdrs tree leaf)
  exact congrArg Id.run this.symm



/-- Layer `0`: the FORS public key is computed without touching either history. -/
theorem msgAt_zero_run (hS : Structural vp prims) (tbl : SecretTable vp prims) (pk : prims.PkSeed)
    (tree leaf : ℕ) (htree : tree < 2 ^ layerTreeHeight vp 0) (hleaf : leaf < 2 ^ vp.params.hp)
    (h g : List (WotsGame.Entry prims)) :
    (simulateQ (tblOracles tbl pk) ((msgAt tbl 0 tree leaf).run h)).run g =
      pure ((hMsg tbl pk 0 tree leaf, h), g) := by
  rw [x1_msgAt_eq, x1_hMsg_eq, x1_bottom_eq tree leaf htree hleaf]
  exact x1_free_Q hS tbl pk _ h g



/-! ### X2 helpers: deterministic runs -/

/-- `c`, started with mirrored history `h` against the table oracles with game history `g`,
deterministically returns `x` and ends with histories `h'`, `g'`. -/
def x2_Runs {α : Type} (tbl : SecretTable vp prims) (pk : prims.PkSeed) (c : WM prims α)
    (h g : List (WotsGame.Entry prims)) (x : α) (h' g' : List (WotsGame.Entry prims)) : Prop :=
  (simulateQ (tblOracles tbl pk) (c.run h)).run g = pure ((x, h'), g')

theorem x2_runs_pure {α : Type} (tbl : SecretTable vp prims) (pk : prims.PkSeed) (x : α)
    (h g : List (WotsGame.Entry prims)) :
    x2_Runs tbl pk (pure x : WM prims α) h g x h g := by
  simp [x2_Runs]

theorem x2_runs_bind {α β : Type} {tbl : SecretTable vp prims} {pk : prims.PkSeed}
    {c : WM prims α} {f : α → WM prims β} {h g h' g' h'' g'' : List (WotsGame.Entry prims)}
    {x : α} {y : β} (hc : x2_Runs tbl pk c h g x h' g')
    (hf : x2_Runs tbl pk (f x) h' g' y h'' g'') :
    x2_Runs tbl pk (c >>= f) h g y h'' g'' := by
  unfold x2_Runs at *
  rw [StateT.run_bind, simulateQ_bind, StateT.run_bind, hc, pure_bind]
  exact hf

theorem x2_runs_get (tbl : SecretTable vp prims) (pk : prims.PkSeed)
    (h g : List (WotsGame.Entry prims)) :
    x2_Runs tbl pk (get : WM prims _) h g h h g := by
  simp [x2_Runs]

theorem x2_runs_modify (tbl : SecretTable vp prims) (pk : prims.PkSeed)
    (f : List (WotsGame.Entry prims) → List (WotsGame.Entry prims))
    (h g : List (WotsGame.Entry prims)) :
    x2_Runs tbl pk (modify f : WM prims _) h g PUnit.unit (f h) g := by
  simp [x2_Runs]

theorem x2_runs_coll (tbl : SecretTable vp prims) (pk : prims.PkSeed) (key : prims.AdrsKey)
    (xs : List prims.Y) (hkey : WotsGame.reservedKey (wotsInsts vp) key = false)
    (h g : List (WotsGame.Entry prims)) :
    x2_Runs tbl pk (wColl key xs) h g (prims.Thash pk key xs) h g := by
  simp [x2_Runs, wColl, tblOracles, oraclesIn, collOracleIn, hkey]

theorem x2_runs_sign (tbl : SecretTable vp prims) (pk : prims.PkSeed) (a : Adrs) (m : prims.Y)
    (h g : List (WotsGame.Entry prims)) (ha : a ∈ wotsInsts vp) (hg : a ∉ g.map (·.1)) :
    x2_Runs tbl pk
      (monadLift ((WSpec prims).query (Sum.inr (Sum.inl (a, m))) :
        OracleComp (WSpec prims)
          (Option (WotsSig vp.params prims.core × Vector prims.Y vp.params.len))) :
        WM prims (Option (WotsSig vp.params prims.core × Vector prims.Y vp.params.len)))
      h g
      (some (WotsGame.hybSig 0 pk a m (startsOf tbl a),
        wotsPkFromSigTops prims (WotsGame.hybSig 0 pk a m (startsOf tbl a)) m pk a))
      h (g ++ [(a, m, WotsGame.hybSig 0 pk a m (startsOf tbl a),
        wotsPkFromSigTops prims (WotsGame.hybSig 0 pk a m (startsOf tbl a)) m pk a)]) := by
  have hg' : ∀ (x : prims.Y) (y : WotsSig vp.params prims.core)
      (z : Vector prims.Y vp.params.len), (a, x, y, z) ∉ g := fun x y z hmem =>
    hg (List.mem_map.2 ⟨_, hmem, rfl⟩)
  simp [x2_Runs, tblOracles, oraclesIn, signOracleIn, ha, hg', -wotsPkFromSigTops_eq_ofFn]

/-! ### X2 helpers: invariant and Hoare triples -/

/-- Every entry is the honest entry of an allowed instance. -/
def x2_Inv (tbl : SecretTable vp prims) (pk : prims.PkSeed)
    (h : List (WotsGame.Entry prims)) : Prop :=
  ∀ e ∈ h, e.1 ∈ wotsInsts vp ∧ e = entryOf tbl pk e.1

/-- `h'` extends `h` by honest entries of layer `< L`. -/
def x2_Ext (tbl : SecretTable vp prims) (pk : prims.PkSeed) (L : ℕ)
    (h h' : List (WotsGame.Entry prims)) : Prop :=
  x2_Inv tbl pk h' ∧ (∀ e ∈ h, e ∈ h') ∧ ∀ e ∈ h', e ∈ h ∨ e.1.layer < L

/-- From equal good histories, `c` returns `x` and extends the histories (equally) by entries of
layer `< L`. -/
def x2_Spec {α : Type} (tbl : SecretTable vp prims) (pk : prims.PkSeed) (c : WM prims α) (x : α)
    (L : ℕ) : Prop :=
  ∀ h, x2_Inv tbl pk h → ∃ h', x2_Runs tbl pk c h h x h' h' ∧ x2_Ext tbl pk L h h'

theorem x2_ext_refl {tbl : SecretTable vp prims} {pk : prims.PkSeed} {L : ℕ}
    {h : List (WotsGame.Entry prims)} (hI : x2_Inv tbl pk h) : x2_Ext tbl pk L h h :=
  ⟨hI, fun _ he => he, fun _ he => Or.inl he⟩

theorem x2_ext_trans {tbl : SecretTable vp prims} {pk : prims.PkSeed} {L L' : ℕ}
    {h h' h'' : List (WotsGame.Entry prims)} (h1 : x2_Ext tbl pk L h h')
    (h2 : x2_Ext tbl pk L' h' h'') (hL : L ≤ L') : x2_Ext tbl pk L' h h'' := by
  refine ⟨h2.1, fun e he => h2.2.1 e (h1.2.1 e he), fun e he => ?_⟩
  rcases h2.2.2 e he with h0 | h0
  · rcases h1.2.2 e h0 with h3 | h3
    · exact Or.inl h3
    · exact Or.inr (lt_of_lt_of_le h3 hL)
  · exact Or.inr h0

theorem x2_spec_bind {α β : Type} {tbl : SecretTable vp prims} {pk : prims.PkSeed}
    {c : WM prims α} {f : α → WM prims β} {x : α} {y : β} {L : ℕ}
    (hc : x2_Spec tbl pk c x L) (hf : x2_Spec tbl pk (f x) y L) :
    x2_Spec tbl pk (c >>= f) y L := by
  intro h hI
  obtain ⟨h1, hr1, he1⟩ := hc h hI
  obtain ⟨h2, hr2, he2⟩ := hf h1 he1.1
  exact ⟨h2, x2_runs_bind hr1 hr2, x2_ext_trans he1 he2 le_rfl⟩

theorem x2_spec_of_runs {α : Type} {tbl : SecretTable vp prims} {pk : prims.PkSeed}
    {c : WM prims α} {x : α} (L : ℕ) (hc : ∀ h g, x2_Runs tbl pk c h g x h g) :
    x2_Spec tbl pk c x L :=
  fun h hI => ⟨h, hc h h, x2_ext_refl hI⟩

theorem x2_spec_topsAt {tbl : SecretTable vp prims} {pk : prims.PkSeed} {a : Adrs}
    {msg : WM prims prims.Y} {l : ℕ} (ha : a ∈ wotsInsts vp) (hl : a.layer = l)
    (hmsg : x2_Spec tbl pk msg (hMsgA tbl pk a) l) :
    ∀ h, x2_Inv tbl pk h → ∃ h', x2_Runs tbl pk (topsAt a msg) h h (entryOf tbl pk a).2.2.2 h' h' ∧
      x2_Ext tbl pk (l + 1) h h' ∧ a ∈ h'.map (·.1) := by
  intro h hI
  unfold topsAt
  cases hf : h.find? (fun e => decide (e.1 = a)) with
  | some e =>
    have he := List.mem_of_find?_eq_some hf
    have hea : e.1 = a := by simpa using List.find?_some hf
    refine ⟨h, ?_, x2_ext_refl hI, List.mem_map.2 ⟨e, he, hea⟩⟩
    refine x2_runs_bind (x2_runs_get tbl pk h h) ?_
    simp only [hf]
    have h2 := (hI e he).2
    rw [hea] at h2
    rw [← h2]
    exact x2_runs_pure tbl pk _ h h
  | none =>
    obtain ⟨h1, hr1, hE1⟩ := hmsg h hI
    have hnot : a ∉ h1.map (·.1) := by
      intro hm
      obtain ⟨e, he, hea⟩ := List.mem_map.1 hm
      rcases hE1.2.2 e he with h0 | h0
      · have := List.find?_eq_none.1 hf e h0
        simp at this
        exact this hea
      · rw [hea, hl] at h0
        exact lt_irrefl _ h0
    refine ⟨h1 ++ [entryOf tbl pk a], ?_, ?_, ?_⟩
    · refine x2_runs_bind (x2_runs_get tbl pk h h) ?_
      simp only [hf]
      refine x2_runs_bind hr1 ?_
      refine x2_runs_bind (x2_runs_sign tbl pk a _ h1 h1 ha hnot) ?_
      exact x2_runs_bind (x2_runs_modify tbl pk _ h1 _) (x2_runs_pure tbl pk _ _ _)
    · refine ⟨?_, ?_, ?_⟩
      · intro e he
        rcases List.mem_append.1 he with h0 | h0
        · exact hE1.1 e h0
        · rw [List.mem_singleton] at h0
          subst h0
          exact ⟨ha, rfl⟩
      · intro e he
        exact List.mem_append_left _ (hE1.2.1 e he)
      · intro e he
        rcases List.mem_append.1 he with h0 | h0
        · rcases hE1.2.2 e h0 with h3 | h3
          · exact Or.inl h3
          · exact Or.inr (Nat.lt_succ_of_lt h3)
        · rw [List.mem_singleton] at h0
          subst h0
          right
          show a.layer < l + 1
          omega
    · simp [entryOf]

open PerfectMerkleTree in
theorem x2_spec_merkle {tbl : SecretTable vp prims} {pk : prims.PkSeed} (P : ℕ → ℕ → Prop)
    (hP : ∀ z t, P (z + 1) t → P z (2 * t) ∧ P z (2 * t + 1))
    (leafW : ℕ → WM prims prims.Y) (nodeW : ℕ → ℕ → prims.Y → prims.Y → WM prims prims.Y)
    (leafI : ℕ → Id prims.Y) (nodeI : ℕ → ℕ → prims.Y → prims.Y → Id prims.Y) (L : ℕ)
    (hleaf : ∀ i, P 0 i → x2_Spec tbl pk (leafW i) (Id.run (leafI i)) L)
    (hnode : ∀ z t l r, P (z + 1) t → ∀ h g,
      x2_Runs tbl pk (nodeW (z + 1) t l r) h g (Id.run (nodeI (z + 1) t l r)) h g) :
    ∀ z t, P z t →
      x2_Spec tbl pk (merkleRootM leafW nodeW z t) (Id.run (merkleRootM leafI nodeI z t)) L
  | 0, t, h => hleaf t h
  | z + 1, t, h => by
    rw [merkleRootM]
    refine x2_spec_bind (x2_spec_merkle P hP leafW nodeW leafI nodeI L hleaf hnode z (2 * t)
      (hP z t h).1) ?_
    refine x2_spec_bind (x2_spec_merkle P hP leafW nodeW leafI nodeI L hleaf hnode z (2 * t + 1)
      (hP z t h).2) ?_
    exact x2_spec_of_runs L (hnode z t _ _ h)

/-! ### X2 helpers: tweaks that are not reserved -/

theorem x2_not_reserved (hS : Structural vp prims) {b : Adrs} (hb : AddressFacts vp b)
    (hty : b.type ≠ AddrType.wotsHash.toCode) :
    WotsGame.reservedKey (wotsInsts vp) (prims.adrsToKey b) = false := by
  by_contra hne
  have htrue : WotsGame.reservedKey (wotsInsts vp) (prims.adrsToKey b) = true := by
    simpa using hne
  simp only [WotsGame.reservedKey, List.any_eq_true, List.mem_range, decide_eq_true_eq] at htrue
  obtain ⟨a, ha, i, hi, t, ht, heq⟩ := htrue
  simp only [wotsInsts, List.mem_map] at ha
  obtain ⟨pos, -, rfl⟩ := ha
  have h1 : b = wotsStepAdrs (pos, ⟨i, hi⟩) ⟨t, ht⟩ :=
    hS.keyInj hb (addressFacts_wotsStepAdrs hS.bounds (pos, ⟨i, hi⟩) ⟨t, ht⟩) heq
  exact hty (by rw [h1]; rfl)

/-! ### X2 helpers: the pure side -/

theorem x2_chain_id (pk : prims.PkSeed) (adrs : Adrs) (x : prims.Y) (i : ℕ) : ∀ s : ℕ,
    chainWith (m := Id) (fun a y => pure (prims.F pk a y)) adrs x i s =
      pure (chain prims pk adrs x i s)
  | 0 => rfl
  | s + 1 => by
    rw [chainWith_succ, x2_chain_id pk adrs x i s, chain_succ]
    rfl

theorem x2_tops_val (tbl : SecretTable vp prims) (pk : prims.PkSeed) (a : Adrs) (m : prims.Y) :
    wotsPkFromSigTops prims (WotsGame.hybSig 0 pk a m (startsOf tbl a)) m pk a =
      Id.run (wotsPkGenTopsWithSecret prims.core (fun a y => pure (prims.F pk a y))
        (fun a => pure (secretOf vp prims tbl a)) a) := by
  unfold wotsPkGenTopsWithSecret
  simp only [pure_bind, x2_chain_id]
  refine Eq.trans ?_ (Vector.idRun_ofFnM (f := fun i : Fin vp.params.len =>
    (pure (chain prims pk (wotsChainAdrs a i.val) (secretOf vp prims tbl (wotsSkAdrs a i.val)) 0
      (vp.params.w - 1)) : Id prims.Y))).symm
  apply Vector.ext
  intro i hi
  simp only [wotsPkFromSigTops_eq_ofFn, Vector.getElem_ofFn, WotsGame.hybSig, startsOf]
  have hc := chain_compose prims pk (wotsChainAdrs a i)
    (secretOf vp prims tbl (wotsSkAdrs a i)) 0 (chainStepsCore prims.core m i)
    (vp.params.w - 1 - chainStepsCore prims.core m i)
  rw [Nat.zero_add] at hc
  simp only [Nat.zero_min, Nat.sub_zero]
  rw [hc, Nat.add_sub_cancel' (chainStepsCore_le prims.core m i)]
  rfl

theorem x2_leaf_val (tbl : SecretTable vp prims) (pk : prims.PkSeed) (adrs : Adrs) (t : ℕ) :
    prims.Thash pk (prims.adrsToKey (wotsPkAdrs (wotsLeafAdrs adrs t)))
        (entryOf tbl pk (wotsLeafAdrs adrs t)).2.2.2.toList =
      Id.run (xmssLeafWithSecret prims.core (fun a y => pure (prims.F pk a y))
        (fun a xs => pure (prims.Tl pk a xs)) (fun a => pure (secretOf vp prims tbl a)) adrs t) := by
  unfold xmssLeafWithSecret wotsPkGenWithSecret
  show prims.Thash pk (prims.adrsToKey (wotsPkAdrs (wotsLeafAdrs adrs t))) _ =
    prims.Thash pk (prims.adrsToKey (wotsPkAdrs (wotsLeafAdrs adrs t)))
      (Id.run (wotsPkGenTopsWithSecret prims.core (fun a y => pure (prims.F pk a y))
        (fun a => pure (secretOf vp prims tbl a)) (wotsLeafAdrs adrs t))).toList
  rw [← x2_tops_val tbl pk (wotsLeafAdrs adrs t) (hMsgA tbl pk (wotsLeafAdrs adrs t))]
  rfl

/-! ### X2 helpers: the hypertree -/

theorem x2_spec_topsAt' {tbl : SecretTable vp prims} {pk : prims.PkSeed} {a : Adrs}
    {msg : WM prims prims.Y} {l : ℕ} (ha : a ∈ wotsInsts vp) (hl : a.layer = l)
    (hmsg : x2_Spec tbl pk msg (hMsgA tbl pk a) l) :
    x2_Spec tbl pk (topsAt a msg) (entryOf tbl pk a).2.2.2 (l + 1) := fun h hI => by
  obtain ⟨h', h1, h2, -⟩ := x2_spec_topsAt ha hl hmsg h hI
  exact ⟨h', h1, h2⟩

theorem x2_child_lt {l tree leaf : ℕ} (hl : l + 1 ≤ vp.params.d)
    (h1 : l + 1 < vp.params.d → tree < 2 ^ layerTreeHeight vp (l + 1) ∧ leaf < 2 ^ vp.params.hp)
    (h2 : l + 1 = vp.params.d → tree = 0 ∧ leaf = 0) :
    tree * 2 ^ vp.params.hp + leaf < 2 ^ layerTreeHeight vp l := by
  rcases Nat.lt_or_ge (l + 1) vp.params.d with h | h
  · obtain ⟨ht, hf⟩ := h1 h
    have e : layerTreeHeight vp l = layerTreeHeight vp (l + 1) + vp.params.hp := by
      unfold layerTreeHeight
      have : vp.params.d - (l + 1) = (vp.params.d - (l + 1 + 1)) + 1 := by omega
      rw [this, Nat.add_mul, Nat.one_mul]
    rw [e, pow_add]
    calc tree * 2 ^ vp.params.hp + leaf < tree * 2 ^ vp.params.hp + 2 ^ vp.params.hp := by omega
      _ = (tree + 1) * 2 ^ vp.params.hp := by ring
      _ ≤ 2 ^ layerTreeHeight vp (l + 1) * 2 ^ vp.params.hp := Nat.mul_le_mul_right _ ht
  · obtain ⟨rfl, rfl⟩ := h2 (by omega)
    simp

theorem x2_spec_msgAt (hS : Structural vp prims) (tbl : SecretTable vp prims)
    (pk : prims.PkSeed)
    (hX1 : ∀ tree leaf : ℕ, tree < 2 ^ layerTreeHeight vp 0 → leaf < 2 ^ vp.params.hp →
      ∀ h g : List (WotsGame.Entry prims),
        (simulateQ (tblOracles tbl pk) ((msgAt tbl 0 tree leaf).run h)).run g =
          pure ((hMsg tbl pk 0 tree leaf, h), g)) :
    ∀ (l tree leaf : ℕ), l ≤ vp.params.d →
    (l < vp.params.d → tree < 2 ^ layerTreeHeight vp l ∧ leaf < 2 ^ vp.params.hp) →
    (l = vp.params.d → tree = 0 ∧ leaf = 0) →
    x2_Spec tbl pk (msgAt tbl l tree leaf) (hMsg tbl pk l tree leaf) l
  | 0, tree, leaf, _, h1, _ => fun h hI =>
    ⟨h, hX1 tree leaf (h1 vp.valid.d_pos).1 (h1 vp.valid.d_pos).2 h h,
      x2_ext_refl hI⟩
  | l + 1, tree, leaf, hl, h1, h2 => by
    have hT := x2_child_lt hl h1 h2
    have hld : l < vp.params.d := by omega
    have hhp : vp.params.hp ≤ 32 := hS.bounds.hp_le
    rw [msgAt, hMsg]
    unfold xmssRootWithSecret xmssNodeWithSecret
    refine x2_spec_merkle (fun z t => z ≤ vp.params.hp ∧ t < 2 ^ (vp.params.hp - z)) ?_ _ _ _ _
      (l + 1) ?_ ?_ vp.params.hp 0 ⟨le_rfl, by simp⟩
    · rintro z t ⟨hz, ht⟩
      have e : vp.params.hp - z = (vp.params.hp - (z + 1)) + 1 := by omega
      rw [e, pow_succ]
      exact ⟨⟨by omega, by omega⟩, by omega, by omega⟩
    · rintro i ⟨-, hi⟩
      rw [Nat.sub_zero] at hi
      have hmem : wotsLeafAdrs (GeneralHypertree.layerAdrs l (tree * 2 ^ vp.params.hp + leaf)) i ∈
          wotsInsts vp := by
        simp only [wotsInsts, List.mem_map]
        exact ⟨⟨⟨l, hld⟩, ⟨_, hT⟩, ⟨i, hi⟩⟩, mem_allWotsInstances vp _, rfl⟩
      refine x2_spec_bind (x2_spec_topsAt' hmem rfl
        (x2_spec_msgAt hS tbl pk hX1 l _ i hld.le (fun _ => ⟨hT, hi⟩) (fun h => absurd h hld.ne))) ?_
      rw [← x2_leaf_val]
      refine x2_spec_of_runs _ (x2_runs_coll tbl pk _ _ (x2_not_reserved hS
        (addressFacts_wotsPkAdrs hS.bounds ⟨⟨l, hld⟩, ⟨_, hT⟩, ⟨i, hi⟩⟩)
        (show AddrType.wotsPk.toCode ≠ AddrType.wotsHash.toCode by decide)))
    · rintro z t x y ⟨hz, ht⟩ h g
      have hz32 : z + 1 < 2 ^ 32 := by omega
      have ht32 : t < 2 ^ 32 :=
        lt_of_lt_of_le ht (Nat.pow_le_pow_right (by norm_num) (by omega))
      exact x2_runs_coll tbl pk _ _ (x2_not_reserved hS
        (addressFacts_xmssNodeAdrs hS.bounds ⟨⟨l, hld⟩, ⟨_, hT⟩⟩ hz32 ht32)
        (show AddrType.tree.toCode ≠ AddrType.wotsHash.toCode by decide)) h g

theorem x2_forM {tbl : SecretTable vp prims} {pk : prims.PkSeed}
    (f : LayerPosition vp → WM prims PUnit)
    (hf : ∀ pos h, x2_Inv tbl pk h → ∃ h', x2_Runs tbl pk (f pos) h h PUnit.unit h' h' ∧
      x2_Inv tbl pk h' ∧ (∀ e ∈ h, e ∈ h') ∧ wotsInstanceAdrs pos ∈ h'.map (·.1)) :
    ∀ (ps : List (LayerPosition vp)) h, x2_Inv tbl pk h →
      ∃ h', x2_Runs tbl pk (ps.forM f) h h PUnit.unit h' h' ∧ x2_Inv tbl pk h' ∧
        (∀ e ∈ h, e ∈ h') ∧ ∀ pos ∈ ps, wotsInstanceAdrs pos ∈ h'.map (·.1)
  | [], h, hI => ⟨h, x2_runs_pure tbl pk _ h h, hI,
      fun _ he => he, by simp⟩
  | p :: ps, h, hI => by
    obtain ⟨h1, hr1, hI1, hs1, hm1⟩ := hf p h hI
    obtain ⟨h2, hr2, hI2, hs2, hm2⟩ := x2_forM f hf ps h1 hI1
    refine ⟨h2, ?_, hI2, fun e he => hs2 e (hs1 e he), ?_⟩
    · exact x2_runs_bind (f := fun _ => ps.forM f) hr1 hr2
    · intro pos hpos
      rcases List.mem_cons.1 hpos with rfl | h0
      · obtain ⟨e, he, hea⟩ := List.mem_map.1 hm1
        exact List.mem_map.2 ⟨e, hs2 e he, hea⟩
      · exact hm2 pos h0

theorem x2_idealRoot (tbl : SecretTable vp prims) (pk : prims.PkSeed) :
    idealRoot vp prims tbl pk = hMsg tbl pk vp.params.d 0 0 := by
  obtain ⟨n, hn⟩ : ∃ n, vp.params.d = n + 1 := ⟨vp.params.d - 1, by have := vp.valid.d_pos; omega⟩
  have e : hMsg tbl pk vp.params.d 0 0 = hMsg tbl pk (n + 1) 0 0 :=
    congrArg (fun k => hMsg tbl pk k 0 0) hn
  rw [e, hMsg]
  unfold idealRoot GeneralScheme.keygenInternalWithSecretM GeneralHypertree.rootWithSecretM
    GeneralHypertree.rootWithSecret
  have e2 : vp.params.d - 1 = n := by omega
  have e3 : 0 * 2 ^ vp.params.hp + 0 = 0 := by simp
  rw [e2, e3]
  exact xmssRootWithSecret_natural prims.core (simulateQ' (PublicHash.impl prims))
    (m := OracleComp (publicHashSpec prims.core)) (n := Id)
    (PublicHash.f prims.core pk)
    (fun a y => (pure (prims.F pk a y) : Id prims.Y))
    (PublicHash.tl prims.core pk)
    (fun a xs => (pure (prims.Tl pk a xs) : Id prims.Y))
    (PublicHash.h prims.core pk)
    (fun a l r => (pure (prims.H pk a l r) : Id prims.Y))
    (fun a => (pure (secretOf vp prims tbl a) : OracleComp (publicHashSpec prims.core) prims.Y))
    (fun a => (pure (secretOf vp prims tbl a) : Id prims.Y))
    (fun a y => PublicHash.simulateQ_f prims pk a y)
    (fun a ys => PublicHash.simulateQ_tl prims pk a ys)
    (fun a l r => PublicHash.simulateQ_h prims pk a l r)
    (fun a _ => simulateQ_pure (PublicHash.impl prims) (secretOf vp prims tbl a))
    (GeneralHypertree.layerAdrs n 0)



/-- Phase 1 against the table-reading game oracles is deterministic: it returns `PK.root`,
and the mirrored history equals the game's history and is good. -/
theorem chooseBody_run (hS : Structural vp prims) (tbl : SecretTable vp prims)
    (pk : prims.PkSeed) :
    ∃ hist, (simulateQ (tblOracles tbl pk) ((chooseBody tbl).run [])).run [] =
        pure ((idealRoot vp prims tbl pk, hist), hist) ∧ HistGood tbl pk hist := by
  have hmsg := x2_spec_msgAt hS tbl pk (fun tree leaf ht hl h g =>
    msgAt_zero_run hS tbl pk tree leaf ht hl h g)
  obtain ⟨h1, hr1, hI1, -, hm1⟩ := x2_forM (tbl := tbl) (pk := pk)
    (fun pos => do
      let _ ← topsAt (wotsInstanceAdrs pos) (msgAt tbl pos.layer.val pos.tree.val pos.leaf.val)
      pure ())
    (fun pos h hI => by
      have hmem : wotsInstanceAdrs pos ∈ wotsInsts vp :=
        List.mem_map.2 ⟨pos, mem_allWotsInstances vp pos, rfl⟩
      obtain ⟨h', hr, hE, hm⟩ := x2_spec_topsAt hmem rfl
        (hmsg pos.layer.val pos.tree.val pos.leaf.val pos.layer.isLt.le
          (fun _ => ⟨pos.tree.isLt, pos.leaf.isLt⟩)
          (fun h => absurd h pos.layer.isLt.ne)) h hI
      exact ⟨h', x2_runs_bind hr (x2_runs_pure tbl pk _ _ _), hE.1, hE.2.1, hm⟩)
    (allWotsInstances vp) [] (fun e he => by simp at he)
  obtain ⟨h2, hr2, hE2⟩ := hmsg vp.params.d 0 0 le_rfl
    (fun h => absurd h (lt_irrefl _)) (fun _ => ⟨rfl, rfl⟩) h1 hI1
  refine ⟨h2, ?_, fun e he => (hE2.1 e he).2, fun a ha => ?_⟩
  · rw [x2_idealRoot]
    exact x2_runs_bind hr1 hr2
  · obtain ⟨pos, hpos, rfl⟩ := List.mem_map.1 ha
    obtain ⟨e, he, hea⟩ := List.mem_map.1 (hm1 pos hpos)
    exact List.mem_map.2 ⟨e, hE2.2.1 e he, hea⟩



/-! ## Y: helper lemmas for (Y1), (Y2) -/

section YHelpers

/-! ### Pure forms of the honest WOTS+/XMSS objects over a secret provider -/

/-- Honest chain ends of the instance `a`. -/
def y_tops (sec : Adrs → prims.Y) (pk : prims.PkSeed) (a : Adrs) :
    Vector prims.Y vp.params.len :=
  Vector.ofFn fun i : Fin vp.params.len =>
    chain prims pk (wotsChainAdrs a i.val) (sec (wotsSkAdrs a i.val)) 0 (vp.params.w - 1)

/-- Honest WOTS+ signature of the instance `a` on `msg`. -/
def y_wsig (sec : Adrs → prims.Y) (pk : prims.PkSeed) (msg : prims.Y) (a : Adrs) :
    WotsSig vp.params prims.core :=
  Vector.ofFn fun i : Fin vp.params.len =>
    chain prims pk (wotsChainAdrs a i.val) (sec (wotsSkAdrs a i.val)) 0
      (chainStepsCore prims.core msg i.val)

/-- Honest XMSS leaf. -/
def y_leaf (sec : Adrs → prims.Y) (pk : prims.PkSeed) (adrs : Adrs) (t : ℕ) : prims.Y :=
  prims.Tl pk (wotsPkAdrs (wotsLeafAdrs adrs t)) (y_tops sec pk (wotsLeafAdrs adrs t)).toList

/-- Honest XMSS root. -/
def y_root (sec : Adrs → prims.Y) (pk : prims.PkSeed) (adrs : Adrs) : prims.Y :=
  PerfectMerkleTree.merkleRoot (y_leaf sec pk adrs) (xmssNodeHash prims pk adrs) vp.params.hp 0

/-- Honest XMSS signature. -/
def y_xsig (sec : Adrs → prims.Y) (pk : prims.PkSeed) (msg : prims.Y) (adrs : Adrs) (idx : ℕ) :
    XmssSig vp.params prims.core :=
  ⟨y_wsig sec pk msg (wotsLeafAdrs adrs idx),
    PerfectMerkleTree.intrinsicAuthPath (y_leaf sec pk adrs) (xmssNodeHash prims pk adrs) idx
      vp.params.hp⟩

theorem y_sim_bind {α β : Type} (oa : OracleComp (publicHashSpec prims.core) α)
    (ob : α → OracleComp (publicHashSpec prims.core) β) :
    simulateQ (PublicHash.impl prims) (oa >>= ob) =
      simulateQ (PublicHash.impl prims) (ob (simulateQ (PublicHash.impl prims) oa)) := by
  rw [simulateQ_bind]
  rfl

theorem y_S_wsig (sec : Adrs → prims.Y) (pk : prims.PkSeed) (msg : prims.Y) (adrs : Adrs) :
    simulateQ (PublicHash.impl prims)
        (wotsSignWithSecret prims.core (PublicHash.f prims.core pk) (fun a => pure (sec a)) msg adrs :
          OracleComp (publicHashSpec prims.core) (WotsSig vp.params prims.core)) =
      y_wsig sec pk msg adrs := by
  unfold wotsSignWithSecret
  rw [simulateQ_ofFnM]
  simp only [pure_bind]
  exact Vector.idRun_ofFnM

theorem y_S_tops (sec : Adrs → prims.Y) (pk : prims.PkSeed) (adrs : Adrs) :
    simulateQ (PublicHash.impl prims)
        (wotsPkGenTopsWithSecret prims.core (PublicHash.f prims.core pk) (fun a => pure (sec a)) adrs :
          OracleComp (publicHashSpec prims.core) (Vector prims.Y vp.params.len)) =
      y_tops sec pk adrs := by
  unfold wotsPkGenTopsWithSecret
  rw [simulateQ_ofFnM]
  simp only [pure_bind]
  exact Vector.idRun_ofFnM

theorem y_S_leaf (sec : Adrs → prims.Y) (pk : prims.PkSeed) (adrs : Adrs) (t : ℕ) :
    simulateQ (PublicHash.impl prims)
        (xmssLeafWithSecret prims.core (PublicHash.f prims.core pk) (PublicHash.tl prims.core pk)
          (fun a => pure (sec a)) adrs t : OracleComp (publicHashSpec prims.core) prims.Y) =
      y_leaf sec pk adrs t := by
  unfold xmssLeafWithSecret wotsPkGenWithSecret
  rw [y_sim_bind, PublicHash.simulateQ_tl, y_S_tops]
  rfl

theorem y_S_root (sec : Adrs → prims.Y) (pk : prims.PkSeed) (adrs : Adrs) :
    simulateQ (PublicHash.impl prims)
        (xmssRootWithSecret prims.core (PublicHash.f prims.core pk) (PublicHash.tl prims.core pk)
          (PublicHash.h prims.core pk) (fun a => pure (sec a)) adrs :
            OracleComp (publicHashSpec prims.core) prims.Y) =
      y_root sec pk adrs := by
  unfold xmssRootWithSecret xmssNodeWithSecret
  rw [PerfectMerkleTree.simulateQ_merkleRootM]
  unfold y_root
  congr 1
  funext t
  exact y_S_leaf sec pk adrs t

theorem y_S_xsig (sec : Adrs → prims.Y) (pk : prims.PkSeed) (msg : prims.Y) (adrs : Adrs)
    (idx : ℕ) :
    simulateQ (PublicHash.impl prims)
        (xmssSignWithSecret prims.core (PublicHash.f prims.core pk) (PublicHash.tl prims.core pk)
          (PublicHash.h prims.core pk) (fun a => pure (sec a)) msg adrs idx :
            OracleComp (publicHashSpec prims.core) (XmssSig vp.params prims.core)) =
      y_xsig sec pk msg adrs idx := by
  unfold xmssSignWithSecret
  simp only [simulateQ_bind, simulateQ_pure]
  rw [PerfectMerkleTree.simulateQ_intrinsicAuthPathM]
  have hl : (fun t => simulateQ (PublicHash.impl prims)
      (xmssLeafWithSecret prims.core (PublicHash.f prims.core pk) (PublicHash.tl prims.core pk)
        (fun a => pure (sec a)) adrs t : OracleComp (publicHashSpec prims.core) prims.Y)) =
      y_leaf sec pk adrs := funext fun t => y_S_leaf sec pk adrs t
  rw [hl]
  have hw := y_S_wsig sec pk msg (wotsLeafAdrs adrs idx)
  unfold y_xsig
  rw [← hw]
  rfl

/-- WOTS+ correctness at the level of chain ends. -/
theorem y_tops_wsig (sec : Adrs → prims.Y) (pk : prims.PkSeed) (msg : prims.Y) (adrs : Adrs) :
    wotsPkFromSigTops prims (y_wsig sec pk msg adrs) msg pk adrs = y_tops sec pk adrs := by
  apply Vector.ext
  intro i hi
  simp only [wotsPkFromSigTops_eq_ofFn, Vector.getElem_ofFn, y_wsig, y_tops]
  have hc := chain_compose prims pk (wotsChainAdrs adrs i)
    (sec (wotsSkAdrs adrs i)) 0 (chainStepsCore prims.core msg i)
    (vp.params.w - 1 - chainStepsCore prims.core msg i)
  rw [Nat.zero_add] at hc
  rw [hc, Nat.add_sub_cancel' (chainStepsCore_le prims.core msg i)]

/-- XMSS correctness. -/
theorem y_xmss_correct (sec : Adrs → prims.Y) (pk : prims.PkSeed) (msg : prims.Y)
    (adrs : Adrs) (idx : ℕ) (hidx : idx < 2 ^ vp.params.hp) :
    xmssPkFromSig prims idx (y_xsig sec pk msg adrs idx) msg pk adrs = y_root sec pk adrs := by
  rw [xmssPkFromSig_eq_climb]
  unfold y_xsig
  dsimp only
  rw [wotsPkFromSig_eq_tl, y_tops_wsig]
  have key := PerfectMerkleTree.climb_authPath (y_leaf sec pk adrs)
    (xmssNodeHash prims pk adrs) idx vp.params.hp
  rw [Nat.div_eq_of_lt hidx] at key
  rw [PerfectMerkleTree.intrinsicAuthPath_toList]
  exact key

/-! ### FORS -/

/-- Honest FORS leaf. -/
def y_fleaf (sec : Adrs → prims.Y) (pk : prims.PkSeed) (adrs : Adrs) (t : ℕ) : prims.Y :=
  prims.F pk (forsNodeAdrs adrs 0 t) (sec (forsSkAdrs adrs t))

/-- Honest FORS public key. -/
def y_fpk (sec : Adrs → prims.Y) (pk : prims.PkSeed) (adrs : Adrs) : prims.Y :=
  prims.Tl pk (forsPkAdrs adrs)
    (Vector.ofFn (fun i : Fin vp.params.k =>
      PerfectMerkleTree.merkleRoot (y_fleaf sec pk adrs) (forsNodeHash prims pk adrs)
        vp.params.a i.val)).toList

/-- Honest FORS signature. -/
def y_fsig (sec : Adrs → prims.Y) (pk : prims.PkSeed) (md : List Byte) (adrs : Adrs) :
    ForsSigCore vp.params prims.core :=
  Vector.ofFn fun i : Fin vp.params.k =>
    ForsTreeSigCore.mk (sec (forsSkAdrs adrs (i.val * 2 ^ vp.params.a + forsIdx vp.params md i.val)))
      (PerfectMerkleTree.intrinsicAuthPath (y_fleaf sec pk adrs) (forsNodeHash prims pk adrs)
        (i.val * 2 ^ vp.params.a + forsIdx vp.params md i.val) vp.params.a)

theorem y_S_fleaf (sec : Adrs → prims.Y) (pk : prims.PkSeed) (adrs : Adrs) :
    (fun t => simulateQ (PublicHash.impl prims)
        (forsLeafWithSecret prims.core (PublicHash.f prims.core pk) (fun a => pure (sec a)) adrs t :
          OracleComp (publicHashSpec prims.core) prims.Y)) = y_fleaf sec pk adrs := by
  funext t
  unfold forsLeafWithSecret
  simp only [pure_bind]
  exact PublicHash.simulateQ_f prims pk _ _

theorem y_S_fsig (sec : Adrs → prims.Y) (pk : prims.PkSeed) (md : List Byte) (adrs : Adrs) :
    simulateQ (PublicHash.impl prims)
        (forsSignWithSecretM prims.core (fun a => pure (sec a)) md pk adrs :
          OracleComp (publicHashSpec prims.core) (ForsSigCore vp.params prims.core)) =
      y_fsig sec pk md adrs := by
  unfold forsSignWithSecretM forsSignWithSecret
  rw [simulateQ_ofFnM]
  refine Vector.idRun_ofFnM.trans ?_
  apply Vector.ext
  intro i hi
  simp only [y_fsig, Vector.getElem_ofFn, pure_bind, simulateQ_bind, simulateQ_pure,
    PerfectMerkleTree.simulateQ_intrinsicAuthPathM, y_S_fleaf]
  rfl

theorem y_S_fpk (sec : Adrs → prims.Y) (pk : prims.PkSeed) (adrs : Adrs) :
    simulateQ (PublicHash.impl prims)
        (forsPkGenWithSecret prims.core (PublicHash.f prims.core pk) (PublicHash.h prims.core pk)
          (PublicHash.tl prims.core pk) (fun a => pure (sec a)) adrs :
            OracleComp (publicHashSpec prims.core) prims.Y) =
      y_fpk sec pk adrs := by
  unfold forsPkGenWithSecret
  rw [y_sim_bind, PublicHash.simulateQ_tl, simulateQ_ofFnM]
  unfold y_fpk
  congr 2
  refine Vector.idRun_ofFnM.trans ?_
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_ofFn]
  unfold forsRootWithSecret
  rw [PerfectMerkleTree.simulateQ_merkleRootM, y_S_fleaf]
  rfl

/-- FORS correctness. -/
theorem y_fors_correct (sec : Adrs → prims.Y) (pk : prims.PkSeed) (md : List Byte) (adrs : Adrs) :
    forsPkFromSig prims (y_fsig sec pk md adrs) md pk adrs = y_fpk sec pk adrs := by
  rw [forsPkFromSig_eq_tl]
  unfold y_fpk
  apply congrArg (prims.Tl pk (forsPkAdrs adrs))
  congr 1
  apply Vector.ext
  intro i hi
  simp only [y_fsig, Vector.getElem_ofFn]
  have ht : (i * 2 ^ vp.params.a + forsIdx vp.params md i) / 2 ^ vp.params.a = i := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity : 0 < 2 ^ vp.params.a),
      Nat.div_eq_of_lt (forsIdx_lt vp.params md i), Nat.zero_add]
  have key := PerfectMerkleTree.climb_authPath (y_fleaf sec pk adrs)
    (forsNodeHash prims pk adrs) (i * 2 ^ vp.params.a + forsIdx vp.params md i) vp.params.a
  rw [ht] at key
  rw [PerfectMerkleTree.intrinsicAuthPath_toList]
  exact key

/-! ### Hypertree -/

/-- The honest message at layer `k` on the path of `parts`, from layer-zero message `m0`. -/
def y_L (sec : Adrs → prims.Y) (pk : prims.PkSeed) (parts : DigestParts vp.params)
    (m0 : prims.Y) : ℕ → prims.Y
  | 0 => m0
  | k + 1 =>
    if h : k < vp.params.d then y_root sec pk (LayerPosition.atLayer vp parts ⟨k, h⟩).toAdrs
    else m0

theorem y_head_insertIdx_zero {X : Type} {n : ℕ} (rest : Vector X n) (x : X) :
    (rest.insertIdx 0 x)[0] = x := by
  simp [Vector.insertIdx_zero]

theorem y_succ_insertIdx_zero {X : Type} {n : ℕ} (rest : Vector X n) (x : X) (i : ℕ)
    (hi : i < n) : (rest.insertIdx 0 x)[i + 1] = rest[i] := by
  simp [Vector.insertIdx_zero]

theorem y_sign_getElem (sec : Adrs → prims.Y) (pk : prims.PkSeed) (parts : DigestParts vp.params)
    (m0 : prims.Y) :
    ∀ (layers : ℕ) (rf : Bool) (j : Fin vp.params.d) (pos : LayerPosition vp)
      (_hpos : pos = LayerPosition.atLayer vp parts j)
      (hrem : pos.layer.val + layers = vp.params.d) (msg : prims.Y)
      (_hmsg : msg = y_L sec pk parts m0 j.val)
      (i : ℕ) (hi : i < layers) (k : Fin vp.params.d) (_hk : k.val = j.val + i),
      (Id.run (simulateQ (PublicHash.impl prims)
        (GeneralHypertree.signFromPositionWithSecret prims.core (PublicHash.f prims.core pk)
          (PublicHash.tl prims.core pk) (PublicHash.h prims.core pk) (fun a => pure (sec a))
          rf pos layers hrem msg :
            OracleComp (publicHashSpec prims.core)
              (Vector (XmssSig vp.params prims.core) layers))))[i] =
        y_xsig sec pk (y_L sec pk parts m0 k.val) (LayerPosition.atLayer vp parts k).toAdrs
          (LayerPosition.atLayer vp parts k).leaf.val := by
  intro layers
  induction layers using Nat.twoStepInduction with
  | zero =>
    intro rf j pos hpos hrem msg hmsg i hi
    omega
  | one =>
    intro rf j pos hpos hrem msg hmsg i hi k hk
    have hsig : simulateQ (PublicHash.impl prims)
        (GeneralHypertree.signFromPositionWithSecret prims.core (PublicHash.f prims.core pk)
          (PublicHash.tl prims.core pk) (PublicHash.h prims.core pk) (fun a => pure (sec a))
          rf pos 1 hrem msg :
            OracleComp (publicHashSpec prims.core) (Vector (XmssSig vp.params prims.core) 1)) =
        #v[y_xsig sec pk msg pos.toAdrs pos.leaf.val] := by
      rw [← y_S_xsig, GeneralHypertree.signFromPositionWithSecret]
      cases rf <;> simp only [simulateQ_bind, simulateQ_pure, Bool.false_eq_true, ite_false,
        ite_true] <;> rfl
    have hi0 : i = 0 := by omega
    subst hi0
    have hkj : k = j := Fin.ext (by simpa using hk)
    subst hkj
    subst hpos
    subst hmsg
    simp only [hsig]
    rfl
  | more layers _ ih =>
    intro rf j pos hpos hrem msg hmsg i hi k hk
    have hnext : pos.layer.val + 1 < vp.params.d := by omega
    have hsig : simulateQ (PublicHash.impl prims)
        (GeneralHypertree.signFromPositionWithSecret prims.core (PublicHash.f prims.core pk)
          (PublicHash.tl prims.core pk) (PublicHash.h prims.core pk) (fun a => pure (sec a))
          rf pos (layers + 2) hrem msg :
            OracleComp (publicHashSpec prims.core)
              (Vector (XmssSig vp.params prims.core) (layers + 2))) =
        (simulateQ (PublicHash.impl prims)
          (GeneralHypertree.signFromPositionWithSecret prims.core (PublicHash.f prims.core pk)
            (PublicHash.tl prims.core pk) (PublicHash.h prims.core pk) (fun a => pure (sec a))
            false (pos.next hnext) (layers + 1) (by simp; omega)
            (xmssPkFromSig prims pos.leaf.val
              (y_xsig sec pk msg pos.toAdrs pos.leaf.val) msg pk pos.toAdrs) :
            OracleComp (publicHashSpec prims.core)
              (Vector (XmssSig vp.params prims.core) (layers + 1)))).insertIdx 0
          (y_xsig sec pk msg pos.toAdrs pos.leaf.val) := by
      rw [← y_S_xsig, GeneralHypertree.signFromPositionWithSecret]
      simp only [simulateQ_bind, simulateQ_pure]
      rfl
    subst hpos
    subst hmsg
    have hjd : j.val + 1 < vp.params.d := by simpa using hnext
    simp only [hsig]
    rcases i with _ | i
    · have hkj : k = j := Fin.ext (by simpa using hk)
      subst hkj
      exact y_head_insertIdx_zero _ _
    · refine (y_succ_insertIdx_zero _ _ i (by omega)).trans ?_
      refine ih false ⟨j.val + 1, hjd⟩ _
        (LayerPosition.atLayer_succ_eq_next vp parts j hjd).symm _ _ ?_ i (by omega) k
        (by simp only []; omega)
      rw [y_xmss_correct sec pk _ _ _ (LayerPosition.atLayer vp parts j).leaf.isLt]
      simp only [y_L, j.isLt, ↓reduceDIte]

/-! ### The reference signature, layer by layer -/

theorem y_idealSign_eq (tbl : SecretTable vp prims) (msg : List Byte)
    (pk : PublicKeyCore prims.core) (R : prims.Y) :
    idealSign vp prims tbl msg pk R =
      ⟨R, y_fsig (secretOf vp prims tbl) pk.pkSeed (digestParts pk R msg).md.toList
          (digestParts pk R msg).forsAdrs,
        simulateQ (PublicHash.impl prims)
          (GeneralHypertree.signWithSecretM prims.core (fun a => pure (secretOf vp prims tbl a))
            (y_fpk (secretOf vp prims tbl) pk.pkSeed (digestParts pk R msg).forsAdrs)
            pk.pkSeed (digestParts pk R msg) :
              OracleComp (publicHashSpec prims.core)
                (GeneralHypertree.Signature vp prims.core))⟩ := by
  rw [← y_fors_correct _ _ (digestParts pk R msg).md.toList, ← y_S_fsig]
  unfold idealSign GeneralScheme.signInternalWithSecretRandomizerM
  simp only [simulateQ_bind, simulateQ_pure]
  rfl

theorem y_ht_getElem (sec : Adrs → prims.Y) (pk : prims.PkSeed) (parts : DigestParts vp.params)
    (m0 : prims.Y) (k : Fin vp.params.d) :
    (Id.run (simulateQ (PublicHash.impl prims)
      (GeneralHypertree.signWithSecretM prims.core (fun a => pure (sec a)) m0 pk parts :
        OracleComp (publicHashSpec prims.core)
          (GeneralHypertree.Signature vp prims.core))))[k.val] =
      y_xsig sec pk (y_L sec pk parts m0 k.val) (LayerPosition.atLayer vp parts k).toAdrs
        (LayerPosition.atLayer vp parts k).leaf.val :=
  y_sign_getElem sec pk parts m0 vp.params.d _ ⟨0, vp.valid.d_pos⟩ (LayerPosition.initial vp parts)
    rfl _ m0 rfl k.val k.isLt k (by simp)

theorem y_layerMsg (sec : Adrs → prims.Y) (pk : prims.PkSeed) (parts : DigestParts vp.params)
    (m0 : prims.Y) (s : HtSigCore vp.params prims.core)
    (hs : ∀ k : Fin vp.params.d, s[k.val] =
      y_xsig sec pk (y_L sec pk parts m0 k.val) (LayerPosition.atLayer vp parts k).toAdrs
        (LayerPosition.atLayer vp parts k).leaf.val) :
    ∀ k : ℕ, k ≤ vp.params.d → layerMsg pk parts s m0 k = y_L sec pk parts m0 k
  | 0, _ => rfl
  | k + 1, hk => by
    have hk' : k < vp.params.d := hk
    rw [layerMsg, dite_eq_left_of_eq_true (eq_true hk'), y_layerMsg sec pk parts m0 s hs k
      (le_of_lt hk'), hs ⟨k, hk'⟩,
      y_xmss_correct sec pk _ _ _ (LayerPosition.atLayer vp parts ⟨k, hk'⟩).leaf.isLt]
    simp only [y_L, hk', ↓reduceDIte]

theorem y_hMsg_zero (tbl : SecretTable vp prims) (pk : prims.PkSeed) (tree leaf : ℕ) :
    hMsg tbl pk 0 tree leaf = y_fpk (secretOf vp prims tbl) pk (bottomForsAdrs tree leaf) :=
  (forsPkGenWithSecret_natural prims.core (simulateQ' (PublicHash.impl prims))
    (PublicHash.f prims.core pk) (fun a x => (pure (prims.F pk a x) : Id prims.Y))
    (PublicHash.h prims.core pk) (fun a l r => (pure (prims.H pk a l r) : Id prims.Y))
    (PublicHash.tl prims.core pk) (fun a xs => (pure (prims.Tl pk a xs) : Id prims.Y))
    (fun a => pure (secretOf vp prims tbl a)) (fun a => pure (secretOf vp prims tbl a))
    (fun a y => PublicHash.simulateQ_f prims pk a y)
    (fun a l r => PublicHash.simulateQ_h prims pk a l r)
    (fun a xs => PublicHash.simulateQ_tl prims pk a xs)
    (fun _ _ => simulateQ_pure (PublicHash.impl prims) _) (bottomForsAdrs tree leaf)).symm.trans
    (y_S_fpk (secretOf vp prims tbl) pk (bottomForsAdrs tree leaf))

theorem y_hMsg_succ (tbl : SecretTable vp prims) (pk : prims.PkSeed) (l tree leaf : ℕ) :
    hMsg tbl pk (l + 1) tree leaf = y_root (secretOf vp prims tbl) pk
      (GeneralHypertree.layerAdrs l (tree * 2 ^ vp.params.hp + leaf)) :=
  (xmssRootWithSecret_natural prims.core (simulateQ' (PublicHash.impl prims))
    (PublicHash.f prims.core pk) (fun a x => (pure (prims.F pk a x) : Id prims.Y))
    (PublicHash.tl prims.core pk) (fun a xs => (pure (prims.Tl pk a xs) : Id prims.Y))
    (PublicHash.h prims.core pk) (fun a l r => (pure (prims.H pk a l r) : Id prims.Y))
    (fun a => pure (secretOf vp prims tbl a)) (fun a => pure (secretOf vp prims tbl a))
    (fun a y => PublicHash.simulateQ_f prims pk a y)
    (fun a xs => PublicHash.simulateQ_tl prims pk a xs)
    (fun a l r => PublicHash.simulateQ_h prims pk a l r)
    (fun _ _ => simulateQ_pure (PublicHash.impl prims) _)
    (GeneralHypertree.layerAdrs l (tree * 2 ^ vp.params.hp + leaf))).symm.trans
    (y_S_root (secretOf vp prims tbl) pk _)

theorem y_L_eq_hMsgA (tbl : SecretTable vp prims) (pk : prims.PkSeed)
    (parts : DigestParts vp.params) (j : Fin vp.params.d) :
    y_L (secretOf vp prims tbl) pk parts (y_fpk (secretOf vp prims tbl) pk parts.forsAdrs) j.val =
      hMsgA tbl pk (layerWotsAdrs parts j) := by
  obtain ⟨j, hj⟩ := j
  cases j with
  | zero => exact (y_hMsg_zero tbl pk _ _).symm
  | succ k =>
    have hk : k < vp.params.d := by omega
    have hn := LayerPosition.atLayer_succ_eq_next vp parts ⟨k, hk⟩ hj
    have h1 : (layerWotsAdrs parts ⟨k + 1, hj⟩).layer = k + 1 :=
      LayerPosition.atLayer_layer_val vp parts ⟨k + 1, hj⟩
    have h2 : (layerWotsAdrs parts ⟨k + 1, hj⟩).tree =
        (LayerPosition.atLayer vp parts ⟨k + 1, hj⟩).tree.val := rfl
    have h3 : (layerWotsAdrs parts ⟨k + 1, hj⟩).word1 =
        (LayerPosition.atLayer vp parts ⟨k + 1, hj⟩).leaf.val := rfl
    have h4 : (LayerPosition.atLayer vp parts ⟨k, hk⟩).toAdrs =
        GeneralHypertree.layerAdrs k (LayerPosition.atLayer vp parts ⟨k, hk⟩).tree.val :=
      congrArg (fun l => GeneralHypertree.layerAdrs l _)
        (LayerPosition.atLayer_layer_val vp parts ⟨k, hk⟩)
    unfold hMsgA
    rw [h1, h2, h3, y_hMsg_succ, hn]
    simp only [y_L, hk, ↓reduceDIte, LayerPosition.next_tree_val, LayerPosition.next_leaf_val]
    rw [h4, Nat.div_add_mod']

theorem y_layerWotsAdrs_mem (parts : DigestParts vp.params) (j : Fin vp.params.d) :
    layerWotsAdrs parts j ∈ wotsInsts vp :=
  List.mem_map.mpr ⟨LayerPosition.atLayer vp parts j, mem_allWotsInstances vp _, rfl⟩

/-- Core lemma: the reference signature layer by layer. -/
theorem y_idealSign_layer (tbl : SecretTable vp prims) (msg : List Byte)
    (pk : PublicKeyCore prims.core) (R : prims.Y) (j : Fin vp.params.d) :
    (idealSign vp prims tbl msg pk R).hypertree[j.val] =
        y_xsig (secretOf vp prims tbl) pk.pkSeed
          (hMsgA tbl pk.pkSeed (layerWotsAdrs (digestParts pk R msg) j))
          (LayerPosition.atLayer vp (digestParts pk R msg) j).toAdrs
          (LayerPosition.atLayer vp (digestParts pk R msg) j).leaf.val ∧
      layerMsg pk.pkSeed (digestParts pk R msg) (idealSign vp prims tbl msg pk R).hypertree
          (forsPkFromSig prims (idealSign vp prims tbl msg pk R).fors
            (digestParts pk R msg).md.toList pk.pkSeed (digestParts pk R msg).forsAdrs) j.val =
        hMsgA tbl pk.pkSeed (layerWotsAdrs (digestParts pk R msg) j) := by
  have hs : ∀ k : Fin vp.params.d, (idealSign vp prims tbl msg pk R).hypertree[k.val] =
      y_xsig (secretOf vp prims tbl) pk.pkSeed
        (y_L (secretOf vp prims tbl) pk.pkSeed (digestParts pk R msg)
          (y_fpk (secretOf vp prims tbl) pk.pkSeed (digestParts pk R msg).forsAdrs) k.val)
        (LayerPosition.atLayer vp (digestParts pk R msg) k).toAdrs
        (LayerPosition.atLayer vp (digestParts pk R msg) k).leaf.val := by
    intro k
    rw [y_idealSign_eq]
    exact y_ht_getElem _ _ _ _ k
  have hf : forsPkFromSig prims (idealSign vp prims tbl msg pk R).fors
      (digestParts pk R msg).md.toList pk.pkSeed (digestParts pk R msg).forsAdrs =
      y_fpk (secretOf vp prims tbl) pk.pkSeed (digestParts pk R msg).forsAdrs := by
    rw [y_idealSign_eq]
    exact y_fors_correct _ _ _ _
  refine ⟨?_, ?_⟩
  · rw [hs j, y_L_eq_hMsgA]
  · rw [hf, y_layerMsg _ _ _ _ _ hs j.val (le_of_lt j.isLt), y_L_eq_hMsgA]

/-! ### The history side -/

theorem y_histEntry (tbl : SecretTable vp prims) (pk : prims.PkSeed)
    (hist : List (WotsGame.Entry prims)) (hg : HistGood tbl pk hist) (a : Adrs)
    (ha : a ∈ wotsInsts vp) : histEntry hist a = entryOf tbl pk a := by
  obtain ⟨e, he, hea⟩ := List.mem_map.mp (hg.2 a ha)
  have hsome : (hist.find? (fun e => decide (e.1 = a))).isSome = true :=
    List.find?_isSome.mpr ⟨e, he, decide_eq_true hea⟩
  obtain ⟨e', he'⟩ := Option.isSome_iff_exists.mp hsome
  have h1 : e'.1 = a := by simpa using List.find?_some he'
  have h2 := hg.1 e' (List.mem_of_find?_eq_some he')
  unfold histEntry
  rw [he', Option.getD_some, h2, h1]

theorem y_entry_sig (tbl : SecretTable vp prims) (pk : prims.PkSeed) (a : Adrs) :
    (entryOf tbl pk a).2.2.1 = y_wsig (secretOf vp prims tbl) pk (hMsgA tbl pk a) a := by
  apply Vector.ext
  intro i hi
  simp [entryOf, WotsGame.hybSig, startsOf, y_wsig]

theorem y_entry_tops (tbl : SecretTable vp prims) (pk : prims.PkSeed) (a : Adrs) :
    (entryOf tbl pk a).2.2.2 = y_tops (secretOf vp prims tbl) pk a := by
  have h : (entryOf tbl pk a).2.2.2 =
      wotsPkFromSigTops prims (entryOf tbl pk a).2.2.1 (hMsgA tbl pk a) pk a := rfl
  rw [h, y_entry_sig, y_tops_wsig]

theorem y_idRun_intrinsicAuthPathM {Y : Type} (leaf : ℕ → Id Y)
    (nodeHash : ℕ → ℕ → Y → Y → Id Y) (idx : ℕ) : ∀ z : ℕ,
    Id.run (PerfectMerkleTree.intrinsicAuthPathM leaf nodeHash idx z) =
      PerfectMerkleTree.intrinsicAuthPath (fun i => Id.run (leaf i))
        (fun h i l r => Id.run (nodeHash h i l r)) idx z
  | 0 => rfl
  | z + 1 => by
    rw [PerfectMerkleTree.intrinsicAuthPathM, PerfectMerkleTree.intrinsicAuthPath,
      ← y_idRun_intrinsicAuthPathM leaf nodeHash idx z, ← PerfectMerkleTree.idRun_merkleRootM]
    rfl

theorem y_root_congr {Y : Type} (leaf₁ leaf₂ : ℕ → Y) (node : ℕ → ℕ → Y → Y → Y) (h : ℕ)
    (hl : ∀ i < 2 ^ h, leaf₁ i = leaf₂ i) : ∀ (z t : ℕ), (t + 1) * 2 ^ z ≤ 2 ^ h →
    PerfectMerkleTree.merkleRoot leaf₁ node z t = PerfectMerkleTree.merkleRoot leaf₂ node z t
  | 0, t, ht => by
    simp only [pow_zero, Nat.mul_one] at ht
    exact hl t (by omega)
  | z + 1, t, ht => by
    have hp : 0 < 2 ^ z := by positivity
    have hpow : 2 ^ (z + 1) = 2 ^ z * 2 := pow_succ 2 z
    have hleft : (2 * t + 1) * 2 ^ z ≤ 2 ^ h := by
      rw [hpow] at ht
      nlinarith
    have hright : (2 * t + 1 + 1) * 2 ^ z ≤ 2 ^ h := by
      rw [hpow] at ht
      nlinarith
    rw [PerfectMerkleTree.merkleRoot_succ, PerfectMerkleTree.merkleRoot_succ,
      y_root_congr leaf₁ leaf₂ node h hl z (2 * t) hleft,
      y_root_congr leaf₁ leaf₂ node h hl z (2 * t + 1) hright]

theorem y_auth_congr {Y : Type} (leaf₁ leaf₂ : ℕ → Y) (node : ℕ → ℕ → Y → Y → Y) (h : ℕ)
    (hl : ∀ i < 2 ^ h, leaf₁ i = leaf₂ i) (idx : ℕ) (hidx : idx < 2 ^ h) : ∀ z : ℕ, z ≤ h →
    PerfectMerkleTree.intrinsicAuthPath leaf₁ node idx z =
      PerfectMerkleTree.intrinsicAuthPath leaf₂ node idx z
  | 0, _ => rfl
  | z + 1, hz => by
    have hpz : 0 < 2 ^ z := by positivity
    have hp : 2 ^ h = 2 * 2 ^ (h - z - 1) * 2 ^ z := by
      rw [← pow_succ', ← pow_add]
      congr 1
      omega
    have hq : idx / 2 ^ z < 2 * 2 ^ (h - z - 1) := by
      rw [Nat.div_lt_iff_lt_mul hpz, ← hp]
      exact hidx
    have hs : PerfectMerkleTree.sibling (idx / 2 ^ z) + 1 ≤ 2 * 2 ^ (h - z - 1) := by
      unfold PerfectMerkleTree.sibling
      generalize 2 ^ (h - z - 1) = M at hq ⊢
      generalize idx / 2 ^ z = q at hq ⊢
      split_ifs <;> omega
    rw [PerfectMerkleTree.intrinsicAuthPath, PerfectMerkleTree.intrinsicAuthPath,
      y_auth_congr leaf₁ leaf₂ node h hl idx hidx z (by omega),
      y_root_congr leaf₁ leaf₂ node h hl z _ (by rw [hp]; exact Nat.mul_le_mul_right _ hs)]

theorem y_leafAdrs_mem (pos : LayerPosition vp) (t : ℕ) (ht : t < 2 ^ vp.params.hp) :
    wotsLeafAdrs pos.toAdrs t ∈ wotsInsts vp :=
  List.mem_map.mpr ⟨⟨pos.layer, pos.tree, ⟨t, ht⟩⟩, mem_allWotsInstances vp _, rfl⟩

/-- Layer `pos` of `signFromHist` on a good history is the honest XMSS signature. -/
theorem y_hist_layer (tbl : SecretTable vp prims) (pk : prims.PkSeed)
    (hist : List (WotsGame.Entry prims)) (hg : HistGood tbl pk hist) (pos : LayerPosition vp) :
    (⟨(histEntry hist (wotsInstanceAdrs pos)).2.2.1,
        Id.run (PerfectMerkleTree.intrinsicAuthPathM
          (fun t => (pure (prims.Tl pk (wotsPkAdrs (wotsLeafAdrs pos.toAdrs t))
            (histEntry hist (wotsLeafAdrs pos.toAdrs t)).2.2.2.toList) : Id prims.Y))
          (xmssNodeHashWith (fun a l r => (pure (prims.H pk a l r) : Id prims.Y))
            pos.toAdrs)
          pos.leaf.val vp.params.hp)⟩ : XmssSig vp.params prims.core) =
      y_xsig (secretOf vp prims tbl) pk (hMsgA tbl pk (wotsInstanceAdrs pos)) pos.toAdrs
        pos.leaf.val := by
  have h1 : (histEntry hist (wotsInstanceAdrs pos)).2.2.1 =
      y_wsig (secretOf vp prims tbl) pk (hMsgA tbl pk (wotsInstanceAdrs pos))
        (wotsLeafAdrs pos.toAdrs pos.leaf.val) := by
    show (histEntry hist (wotsLeafAdrs pos.toAdrs pos.leaf.val)).2.2.1 = _
    rw [y_histEntry tbl pk hist hg _ (y_leafAdrs_mem pos pos.leaf.val pos.leaf.isLt), y_entry_sig]
    rfl
  have h2 : Id.run (PerfectMerkleTree.intrinsicAuthPathM
          (fun t => (pure (prims.Tl pk (wotsPkAdrs (wotsLeafAdrs pos.toAdrs t))
            (histEntry hist (wotsLeafAdrs pos.toAdrs t)).2.2.2.toList) : Id prims.Y))
          (xmssNodeHashWith (fun a l r => (pure (prims.H pk a l r) : Id prims.Y))
            pos.toAdrs)
          pos.leaf.val vp.params.hp) =
      PerfectMerkleTree.intrinsicAuthPath (y_leaf (secretOf vp prims tbl) pk pos.toAdrs)
        (xmssNodeHash prims pk pos.toAdrs) pos.leaf.val vp.params.hp := by
    rw [y_idRun_intrinsicAuthPathM]
    refine (y_auth_congr _ _ _ vp.params.hp ?_ _ pos.leaf.isLt _ le_rfl).trans rfl
    intro t ht
    show prims.Tl pk _ _ = y_leaf _ _ _ _
    rw [y_histEntry tbl pk hist hg _ (y_leafAdrs_mem pos t ht), y_entry_tops]
    rfl
  rw [h1, h2]
  rfl

theorem y_id_fsig (sec : Adrs → prims.Y) (pk : prims.PkSeed) (md : List Byte) (adrs : Adrs) :
    (forsSignWithSecret prims.core (fun a x => (pure (prims.F pk a x) : Id prims.Y))
      (fun a l r => (pure (prims.H pk a l r) : Id prims.Y)) (fun a => (pure (sec a) : Id prims.Y))
      md adrs : Id (ForsSigCore vp.params prims.core)) = y_fsig sec pk md adrs :=
  (forsSignWithSecret_natural prims.core (simulateQ' (PublicHash.impl prims))
    (PublicHash.f prims.core pk) (fun a x => (pure (prims.F pk a x) : Id prims.Y))
    (PublicHash.h prims.core pk) (fun a l r => (pure (prims.H pk a l r) : Id prims.Y))
    (fun a => pure (sec a)) (fun a => pure (sec a))
    (fun a y => PublicHash.simulateQ_f prims pk a y)
    (fun a l r => PublicHash.simulateQ_h prims pk a l r)
    (fun _ _ => simulateQ_pure (PublicHash.impl prims) _) md adrs).symm.trans
    (y_S_fsig sec pk md adrs)

/-- The honest XMSS signature as the `Id` program of the interface. -/
theorem y_id_xsig (sec : Adrs → prims.Y) (pk : prims.PkSeed) (msg : prims.Y) (adrs : Adrs)
    (idx : ℕ) :
    (xmssSignWithSecret prims.core (fun a x => (pure (prims.F pk a x) : Id prims.Y))
      (fun a xs => (pure (prims.Tl pk a xs) : Id prims.Y))
      (fun a l r => (pure (prims.H pk a l r) : Id prims.Y)) (fun a => (pure (sec a) : Id prims.Y))
      msg adrs idx : Id (XmssSig vp.params prims.core)) = y_xsig sec pk msg adrs idx :=
  (xmssSignWithSecret_natural prims.core (simulateQ' (PublicHash.impl prims))
    (PublicHash.f prims.core pk) (fun a x => (pure (prims.F pk a x) : Id prims.Y))
    (PublicHash.tl prims.core pk) (fun a xs => (pure (prims.Tl pk a xs) : Id prims.Y))
    (PublicHash.h prims.core pk) (fun a l r => (pure (prims.H pk a l r) : Id prims.Y))
    (fun a => pure (sec a)) (fun a => pure (sec a))
    (fun a y => PublicHash.simulateQ_f prims pk a y)
    (fun a xs => PublicHash.simulateQ_tl prims pk a xs)
    (fun a l r => PublicHash.simulateQ_h prims pk a l r)
    (fun _ _ => simulateQ_pure (PublicHash.impl prims) _) msg adrs idx).symm.trans
    (y_S_xsig sec pk msg adrs idx)

end YHelpers



/-- On a good history the phase-2 signer is the honest signer of the table. -/
theorem signFromHist_eq_idealSign (hS : Structural vp prims) (tbl : SecretTable vp prims)
    (hist : List (WotsGame.Entry prims)) (pk : PublicKeyCore prims.core)
    (hg : HistGood tbl pk.pkSeed hist) (msg : List Byte) (R : prims.Y) :
    signFromHist tbl hist pk msg R = idealSign vp prims tbl msg pk R := by
  have hR : (idealSign vp prims tbl msg pk R).randomness = R := by rw [y_idealSign_eq]
  have hF : (idealSign vp prims tbl msg pk R).fors = (signFromHist tbl hist pk msg R).fors := by
    rw [y_idealSign_eq]
    exact (y_id_fsig (secretOf vp prims tbl) pk.pkSeed _ _).symm
  have hH : (signFromHist tbl hist pk msg R).hypertree =
      (idealSign vp prims tbl msg pk R).hypertree := by
    apply Vector.ext
    intro i hi
    rw [(y_idealSign_layer tbl msg pk R ⟨i, hi⟩).1]
    show (Vector.ofFn (fun j : Fin vp.params.d => _))[i] = _
    rw [Vector.getElem_ofFn]
    exact y_hist_layer tbl pk.pkSeed hist hg _
  revert hR hF hH
  generalize idealSign vp prims tbl msg pk R = ref
  intro hR hF hH
  obtain ⟨r, f, h⟩ := ref
  dsimp only at hR hF hH
  subst hR hF hH
  rfl

/-- Deterministic: a fresh valid forgery of class `wots` wins the WOTS game through
`wotsAnswer`, on a good history. -/
theorem wotsAnswer_wins (hS : Structural vp prims) (tbl : SecretTable vp prims)
    (hist : List (WotsGame.Entry prims)) (pk : PublicKeyCore prims.core) (log : G2Log prims)
    (msg : List Byte) (sig : GeneralScheme.SignatureCore vp prims.core)
    (hg : HistGood tbl pk.pkSeed hist)
    (hvalid : g2Valid pk log msg sig = true)
    (hclass : g2ClassOf tbl pk log msg sig = .wots) :
    WotsGame.win pk.pkSeed hist (wotsAnswer tbl hist pk msg sig).1
      (wotsAnswer tbl hist pk msg sig).2.1 (wotsAnswer tbl hist pk msg sig).2.2 = true := by
  have href := signFromHist_eq_idealSign hS tbl hist pk hg msg sig.randomness
  have hw : (wotsLayer? pk (digestParts pk sig.randomness msg) sig
      (idealSign vp prims tbl msg pk sig.randomness)).isSome = true := by
    unfold g2ClassOf classify at hclass
    dsimp only at hclass
    split_ifs at hclass with h1 h2 h3
    exact h2
  obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp hw
  have hp : layerMsg pk.pkSeed (digestParts pk sig.randomness msg) sig.hypertree
        (forsPkFromSig prims sig.fors (digestParts pk sig.randomness msg).md.toList pk.pkSeed
          (digestParts pk sig.randomness msg).forsAdrs) j.val ≠
      layerMsg pk.pkSeed (digestParts pk sig.randomness msg)
        (idealSign vp prims tbl msg pk sig.randomness).hypertree
        (forsPkFromSig prims (idealSign vp prims tbl msg pk sig.randomness).fors
          (digestParts pk sig.randomness msg).md.toList pk.pkSeed
          (digestParts pk sig.randomness msg).forsAdrs) j.val ∧
      layerTops pk.pkSeed (digestParts pk sig.randomness msg) sig.hypertree
        (forsPkFromSig prims sig.fors (digestParts pk sig.randomness msg).md.toList pk.pkSeed
          (digestParts pk sig.randomness msg).forsAdrs) j =
      layerTops pk.pkSeed (digestParts pk sig.randomness msg)
        (idealSign vp prims tbl msg pk sig.randomness).hypertree
        (forsPkFromSig prims (idealSign vp prims tbl msg pk sig.randomness).fors
          (digestParts pk sig.randomness msg).md.toList pk.pkSeed
          (digestParts pk sig.randomness msg).forsAdrs) j := by
    unfold wotsLayer? at hj
    have h := List.find?_some hj
    exact of_decide_eq_true h
  have hans : wotsAnswer tbl hist pk msg sig =
      (hist.findIdx (fun e => decide (e.1 = layerWotsAdrs (digestParts pk sig.randomness msg) j)),
        layerMsg pk.pkSeed (digestParts pk sig.randomness msg) sig.hypertree
          (forsPkFromSig prims sig.fors (digestParts pk sig.randomness msg).md.toList pk.pkSeed
            (digestParts pk sig.randomness msg).forsAdrs) j.val,
        (sig.hypertree[j.val]).wots) := by
    unfold wotsAnswer
    simp only [href, hj]
  rw [hans]
  obtain ⟨hl1, hl2⟩ := y_idealSign_layer tbl msg pk sig.randomness j
  obtain ⟨e, he, hea⟩ := List.mem_map.mp
    (hg.2 _ (y_layerWotsAdrs_mem (digestParts pk sig.randomness msg) j))
  have hlt : hist.findIdx
      (fun e => decide (e.1 = layerWotsAdrs (digestParts pk sig.randomness msg) j)) <
        hist.length :=
    List.findIdx_lt_length_of_exists ⟨e, he, decide_eq_true hea⟩
  have hp1 : (hist[hist.findIdx
      (fun e => decide (e.1 = layerWotsAdrs (digestParts pk sig.randomness msg) j))]).1 =
      layerWotsAdrs (digestParts pk sig.randomness msg) j := by
    have h := List.findIdx_getElem (w := hlt)
    exact of_decide_eq_true h
  have hent : hist[hist.findIdx
      (fun e => decide (e.1 = layerWotsAdrs (digestParts pk sig.randomness msg) j))] =
      entryOf tbl pk.pkSeed (layerWotsAdrs (digestParts pk sig.randomness msg) j) := by
    have h := hg.1 _ (List.getElem_mem hlt)
    rw [hp1] at h
    exact h
  have hrt : layerTops pk.pkSeed (digestParts pk sig.randomness msg)
        (idealSign vp prims tbl msg pk sig.randomness).hypertree
        (forsPkFromSig prims (idealSign vp prims tbl msg pk sig.randomness).fors
          (digestParts pk sig.randomness msg).md.toList pk.pkSeed
          (digestParts pk sig.randomness msg).forsAdrs) j =
      (entryOf tbl pk.pkSeed (layerWotsAdrs (digestParts pk sig.randomness msg) j)).2.2.2 := by
    unfold layerTops
    rw [hl2, hl1, y_entry_tops]
    exact y_tops_wsig _ _ _ _
  unfold WotsGame.win
  rw [List.getElem?_eq_getElem hlt, hent]
  show decide (_ ≠ hMsgA tbl pk.pkSeed (layerWotsAdrs (digestParts pk sig.randomness msg) j) ∧
    wotsPkFromSigTops prims _ _ pk.pkSeed (layerWotsAdrs (digestParts pk sig.randomness msg) j) =
      (entryOf tbl pk.pkSeed (layerWotsAdrs (digestParts pk sig.randomness msg) j)).2.2.2) = true
  refine decide_eq_true ⟨?_, ?_⟩
  · rw [← hl2]
    exact hp.1
  · rw [← hrt]
    exact hp.2


/-! ### Z helpers -/

theorem z_secIdx_val (a : Adrs) :
    (secIdx a).val = (a.layer + 2 ^ 32 * (a.tree + 2 ^ 96 * (a.type + 2 ^ 32 *
      (a.word1 + 2 ^ 32 * (a.word2 + 2 ^ 32 * a.word3))))) % 2 ^ 256 := rfl

/-- `secIdx` is injective on FIPS-canonical addresses. -/
theorem z_secIdx_injOn_canonical : Set.InjOn secIdx {a : Adrs | a.isCanonical = true} := by
  intro a ha b hb h
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := Adrs.fits_of_isCanonical a ha
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := Adrs.fits_of_isCanonical b hb
  rw [Adrs.fits_iff] at a1 a2 a3 a4 a5 a6 b1 b2 b3 b4 b5 b6
  have h1 := congrArg Fin.val h
  rw [z_secIdx_val, z_secIdx_val] at h1
  norm_num at a1 a2 a3 a4 a5 a6 b1 b2 b3 b4 b5 b6
  apply Adrs.ext <;> omega

theorem z_mem_wotsInsts {a : Adrs} (ha : a ∈ wotsInsts vp) :
    ∃ pos : LayerPosition vp, a = wotsInstanceAdrs pos := by
  obtain ⟨pos, -, rfl⟩ := List.mem_map.1 ha
  exact ⟨pos, rfl⟩

/-- A FORS secret cell of a reachable bottom position is not a WOTS+ cell. -/
theorem z_fors_not_wotsCell (hb : CanonicalAddressBounds vp.params) (pos : BottomPosition vp)
    {t : ℕ} (ht : t < vp.params.k * 2 ^ vp.params.a) :
    ¬ IsWotsCell vp (secIdx (forsSkAdrs pos.forsAdrs t)) := by
  rintro ⟨a, ha, j, hj⟩
  obtain ⟨p, rfl⟩ := z_mem_wotsInsts ha
  have e := z_secIdx_injOn_canonical (addressFacts_wotsSkAdrs hb p j).canonical
    (addressFacts_forsSkAdrs hb pos ht).canonical hj
  have e' := congrArg Adrs.type e
  revert e'
  show AddrType.wotsPrf.toCode = AddrType.forsPrf.toCode → False
  decide

theorem z_fors_agree (hb : CanonicalAddressBounds vp.params) {tbl tbl' : SecretTable vp prims}
    (h : ∀ i, ¬ IsWotsCell vp i → tbl i = tbl' i) (pos : BottomPosition vp)
    {t : ℕ} (ht : t < vp.params.k * 2 ^ vp.params.a) :
    secretOf vp prims tbl (forsSkAdrs pos.forsAdrs t) =
      secretOf vp prims tbl' (forsSkAdrs pos.forsAdrs t) :=
  h _ (z_fors_not_wotsCell hb pos ht)

open PerfectMerkleTree in
theorem z_merkleRootM_congr {Y : Type} {m : Type → Type} [Monad m] (leaf1 leaf2 : ℕ → m Y)
    (node : ℕ → ℕ → Y → Y → m Y) : ∀ (z t : ℕ),
    (∀ i, i / 2 ^ z = t → leaf1 i = leaf2 i) →
      merkleRootM leaf1 node z t = merkleRootM leaf2 node z t
  | 0, t, h => by
      rw [merkleRootM, merkleRootM]
      exact h t (by simp)
  | z + 1, t, h => by
      rw [merkleRootM, merkleRootM,
        z_merkleRootM_congr leaf1 leaf2 node z (2 * t) (fun i hi => h i (by
          rw [pow_succ, ← Nat.div_div_eq_div_mul, hi]; omega)),
        z_merkleRootM_congr leaf1 leaf2 node z (2 * t + 1) (fun i hi => h i (by
          rw [pow_succ, ← Nat.div_div_eq_div_mul, hi]; omega))]

open PerfectMerkleTree in
theorem z_authPathM_congr {Y : Type} {m : Type → Type} [Monad m] (leaf1 leaf2 : ℕ → m Y)
    (node : ℕ → ℕ → Y → Y → m Y) (idx hgt : ℕ)
    (h : ∀ i, i / 2 ^ hgt = idx / 2 ^ hgt → leaf1 i = leaf2 i) : ∀ z, z ≤ hgt →
      intrinsicAuthPathM leaf1 node idx z = intrinsicAuthPathM leaf2 node idx z
  | 0, _ => by rw [intrinsicAuthPathM, intrinsicAuthPathM]
  | z + 1, hz => by
      rw [intrinsicAuthPathM, intrinsicAuthPathM, z_authPathM_congr leaf1 leaf2 node idx hgt h z
        (by omega),
        z_merkleRootM_congr leaf1 leaf2 node z (sibling (idx / 2 ^ z)) (fun i hi => h i (by
          obtain ⟨c, rfl⟩ : ∃ c, hgt = z + (c + 1) := ⟨hgt - z - 1, by omega⟩
          rw [pow_add, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, hi, pow_succ,
            Nat.mul_comm, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul (idx / 2 ^ z),
            sibling_div_two]))]

theorem z_lt_of_div {a k t i : ℕ} (hi : i < k) (h : t / 2 ^ a = i) : t < k * 2 ^ a := by
  have h1 : t / 2 ^ a < k := h ▸ hi
  exact (Nat.div_lt_iff_lt_mul (by positivity)).1 h1

/-- FORS leaves agree on the leaves of the `k` trees. -/
theorem z_forsLeaf_congr {m : Type → Type} [Monad m] (hb : CanonicalAddressBounds vp.params)
    {tbl tbl' : SecretTable vp prims} (h : ∀ i, ¬ IsWotsCell vp i → tbl i = tbl' i)
    (hash : Adrs → prims.core.Y → m prims.core.Y) (pos : BottomPosition vp)
    {t : ℕ} (ht : t < vp.params.k * 2 ^ vp.params.a) :
    forsLeafWithSecret prims.core hash (fun a => pure (secretOf vp prims tbl a)) pos.forsAdrs t =
      forsLeafWithSecret prims.core hash (fun a => pure (secretOf vp prims tbl' a))
        pos.forsAdrs t := by
  unfold forsLeafWithSecret
  dsimp only
  rw [z_fors_agree hb h pos ht]

theorem z_forsSign_congr (hb : CanonicalAddressBounds vp.params)
    {tbl tbl' : SecretTable vp prims} (h : ∀ i, ¬ IsWotsCell vp i → tbl i = tbl' i)
    (hash : Adrs → prims.core.Y → Id prims.core.Y)
    (nodeHash : Adrs → prims.core.Y → prims.core.Y → Id prims.core.Y) (md : List Byte)
    (pos : BottomPosition vp) :
    forsSignWithSecret prims.core hash nodeHash (fun a => pure (secretOf vp prims tbl a)) md
        pos.forsAdrs =
      forsSignWithSecret prims.core hash nodeHash (fun a => pure (secretOf vp prims tbl' a)) md
        pos.forsAdrs := by
  unfold forsSignWithSecret
  congr 1
  funext i
  have hidx : (i.val * 2 ^ vp.params.a + forsIdx vp.params md i.val) / 2 ^ vp.params.a = i.val := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity),
      Nat.div_eq_of_lt (forsIdx_lt vp.params md i.val), Nat.zero_add]
  have hlt := z_lt_of_div i.isLt hidx
  simp only []
  rw [z_fors_agree hb h pos hlt,
    z_authPathM_congr _ _ _ _ vp.params.a (fun t ht => z_forsLeaf_congr hb h hash pos
      (z_lt_of_div i.isLt (ht.trans hidx))) vp.params.a le_rfl]

theorem z_forsPkGen_congr {m : Type → Type} [Monad m] (hb : CanonicalAddressBounds vp.params)
    {tbl tbl' : SecretTable vp prims} (h : ∀ i, ¬ IsWotsCell vp i → tbl i = tbl' i)
    (hash : Adrs → prims.core.Y → m prims.core.Y)
    (nodeHash : Adrs → prims.core.Y → prims.core.Y → m prims.core.Y)
    (compress : Adrs → List prims.core.Y → m prims.core.Y) (pos : BottomPosition vp) :
    forsPkGenWithSecret prims.core hash nodeHash compress
        (fun a => pure (secretOf vp prims tbl a)) pos.forsAdrs =
      forsPkGenWithSecret prims.core hash nodeHash compress
        (fun a => pure (secretOf vp prims tbl' a)) pos.forsAdrs := by
  unfold forsPkGenWithSecret forsRootWithSecret
  congr 2
  funext i
  exact z_merkleRootM_congr _ _ _ _ _ fun t ht =>
    z_forsLeaf_congr hb h hash pos (z_lt_of_div i.isLt ht)

theorem z_msgAt_zero_congr (hb : CanonicalAddressBounds vp.params)
    {tbl tbl' : SecretTable vp prims} (h : ∀ i, ¬ IsWotsCell vp i → tbl i = tbl' i)
    (tree leaf : ℕ) (htree : tree < 2 ^ layerTreeHeight vp 0) (hleaf : leaf < 2 ^ vp.params.hp) :
    msgAt (prims := prims) tbl 0 tree leaf = msgAt tbl' 0 tree leaf := by
  rw [msgAt, msgAt]
  exact z_forsPkGen_congr hb h _ _ _ (⟨⟨tree, htree⟩, ⟨leaf, hleaf⟩⟩ : BottomPosition vp)

theorem z_msgAt_succ_of (tbl tbl' : SecretTable vp prims) (l tree leaf : ℕ)
    (ih : ∀ t, t < 2 ^ vp.params.hp →
      msgAt (prims := prims) tbl l (tree * 2 ^ vp.params.hp + leaf) t =
        msgAt tbl' l (tree * 2 ^ vp.params.hp + leaf) t) :
    msgAt (prims := prims) tbl (l + 1) tree leaf = msgAt tbl' (l + 1) tree leaf := by
  rw [msgAt, msgAt]
  refine z_merkleRootM_congr _ _ _ _ _ fun t ht => ?_
  have ht' : t < 2 ^ vp.params.hp := by
    rcases Nat.lt_or_ge t (2 ^ vp.params.hp) with h | h
    · exact h
    · have := Nat.div_pos h (by positivity); omega
  rw [ih t ht']

theorem z_msgAt_congr (hb : CanonicalAddressBounds vp.params)
    {tbl tbl' : SecretTable vp prims} (h : ∀ i, ¬ IsWotsCell vp i → tbl i = tbl' i) :
    ∀ (l tree leaf : ℕ), l < vp.params.d → tree < 2 ^ layerTreeHeight vp l →
      leaf < 2 ^ vp.params.hp →
      msgAt (prims := prims) tbl l tree leaf = msgAt tbl' l tree leaf
  | 0, tree, leaf, _, htree, hleaf => z_msgAt_zero_congr hb h tree leaf htree hleaf
  | l + 1, tree, leaf, hl, htree, hleaf =>
    z_msgAt_succ_of tbl tbl' l tree leaf fun t ht =>
      z_msgAt_congr hb h l _ t (by omega) (by
        have e : layerTreeHeight vp l = layerTreeHeight vp (l + 1) + vp.params.hp := by
          unfold layerTreeHeight
          obtain ⟨c, hc⟩ : ∃ c, vp.params.d = l + 2 + c := ⟨vp.params.d - (l + 2), by omega⟩
          rw [hc, show l + 2 + c - (l + 1) = c + 1 by omega,
            show l + 2 + c - (l + 1 + 1) = c by omega, Nat.add_mul, Nat.one_mul]
        rw [e, pow_add]
        calc tree * 2 ^ vp.params.hp + leaf < tree * 2 ^ vp.params.hp + 2 ^ vp.params.hp := by
              omega
          _ = (tree + 1) * 2 ^ vp.params.hp := by rw [Nat.add_mul, Nat.one_mul]
          _ ≤ _ := Nat.mul_le_mul_right _ htree) ht

theorem z_msgAt_top_congr (hb : CanonicalAddressBounds vp.params)
    {tbl tbl' : SecretTable vp prims} (h : ∀ i, ¬ IsWotsCell vp i → tbl i = tbl' i) :
    msgAt (prims := prims) tbl vp.params.d 0 0 = msgAt tbl' vp.params.d 0 0 := by
  obtain ⟨c, hc⟩ : ∃ c, vp.params.d = c + 1 := ⟨vp.params.d - 1, by have := vp.valid.d_pos; omega⟩
  rw [hc]
  refine z_msgAt_succ_of tbl tbl' c 0 0 fun t ht => ?_
  exact z_msgAt_congr hb h c _ t (by omega) (by simp) ht



/-- Distinct WOTS+ start-value cells. -/
theorem wotsCell_inj (hS : Structural vp prims) :
    ∀ a ∈ wotsInsts vp, ∀ a' ∈ wotsInsts vp, ∀ j j' : Fin vp.params.len,
      secIdx (wotsSkAdrs a j.val) = secIdx (wotsSkAdrs a' j'.val) → a = a' ∧ j = j' := by
  intro a ha a' ha' j j' hj
  obtain ⟨p, rfl⟩ := z_mem_wotsInsts ha
  obtain ⟨p', rfl⟩ := z_mem_wotsInsts ha'
  have e := z_secIdx_injOn_canonical (addressFacts_wotsSkAdrs hS.bounds p j).canonical
    (addressFacts_wotsSkAdrs hS.bounds p' j').canonical hj
  have e1 : p.layer.val = p'.layer.val := congrArg Adrs.layer e
  have e2 : p.tree.val = p'.tree.val := congrArg Adrs.tree e
  have e3 : p.leaf.val = p'.leaf.val := congrArg Adrs.word1 e
  have e4 : j.val = j'.val := congrArg Adrs.word2 e
  refine ⟨?_, Fin.ext e4⟩
  exact Adrs.ext e1 e2 rfl e3 rfl rfl

/-- Phase 1 reads the table only outside the WOTS+ cells. -/
theorem chooseBody_congr (hS : Structural vp prims) {tbl tbl' : SecretTable vp prims}
    (h : ∀ i, ¬ IsWotsCell vp i → tbl i = tbl' i) :
    chooseBody (prims := prims) tbl = chooseBody tbl' := by
  unfold chooseBody
  rw [z_msgAt_top_congr hS.bounds h]
  congr 2
  funext pos
  rw [z_msgAt_congr hS.bounds h _ _ _ pos.layer.isLt pos.tree.isLt pos.leaf.isLt]

/-- The phase-2 signer reads the table only outside the WOTS+ cells. -/
theorem signFromHist_congr (hS : Structural vp prims) {tbl tbl' : SecretTable vp prims}
    (h : ∀ i, ¬ IsWotsCell vp i → tbl i = tbl' i) (hist : List (WotsGame.Entry prims))
    (pk : PublicKeyCore prims.core) (msg : List Byte) (R : prims.Y) :
    signFromHist tbl hist pk msg R = signFromHist tbl' hist pk msg R := by
  unfold signFromHist
  have e := z_forsSign_congr hS.bounds h (fun a x => prims.F pk.pkSeed a x)
    (fun a l r => prims.H pk.pkSeed a l r) (digestParts pk R msg).md.toList
    (BottomPosition.ofDigestParts vp (digestParts pk R msg))
  rw [BottomPosition.forsAdrs_ofDigestParts] at e
  simp only []
  exact congrArg (fun f => (⟨R, f, _⟩ : GeneralScheme.SignatureCore vp prims.core)) e


/-! ## Glue -/

section Glue

/-- Block oracle delivering the start values of an instance. -/
abbrev BSpec (prims : Primitives vp.params) : OracleSpec Adrs :=
  Adrs →ₒ Vector prims.Y vp.params.len

abbrev QSpec (prims : Primitives vp.params) := unifSpec + BSpec prims

/-- The game's phase-1 oracles with the start values requested from the block oracle. -/
def qOracles (pk : prims.PkSeed) :
    QueryImpl (WSpec prims) (StateT (List (WotsGame.Entry prims)) (OracleComp (QSpec prims))) :=
  oraclesIn (m := OracleComp (QSpec prims)) (QueryImpl.ofLift unifSpec (OracleComp (QSpec prims)))
    (fun a => (liftM ((QSpec prims).query (Sum.inr a)) :
      OracleComp (QSpec prims) (Vector prims.Y vp.params.len))) (wotsInsts vp) pk

theorem q_step_unif (pk : prims.PkSeed) (n : ℕ) (s : List (WotsGame.Entry prims)) :
    (qOracles (vp := vp) pk (Sum.inl n)).run s =
      (liftM ((QSpec prims).query (Sum.inl n)) : OracleComp (QSpec prims) _) >>=
        fun x => pure (x, s) := by
  simp [qOracles, oraclesIn]
  rfl

theorem q_step_coll (pk : prims.PkSeed) (q : prims.AdrsKey × List prims.Y)
    (s : List (WotsGame.Entry prims)) :
    (qOracles (vp := vp) pk (Sum.inr (Sum.inr q))).run s =
      pure (if WotsGame.reservedKey (wotsInsts vp) q.1 then none
        else some (prims.Thash pk q.1 q.2), s) := by
  simp [qOracles, oraclesIn, collOracleIn]

theorem q_step_sign (pk : prims.PkSeed) (q : Adrs × prims.Y)
    (s : List (WotsGame.Entry prims)) :
    (qOracles (vp := vp) pk (Sum.inr (Sum.inl q))).run s =
      if q.1 ∉ wotsInsts vp ∨ q.1 ∈ s.map (·.1) then pure (none, s)
      else (liftM ((QSpec prims).query (Sum.inr q.1)) : OracleComp (QSpec prims) _) >>=
        fun ss => pure (some (WotsGame.hybSig 0 pk q.1 q.2 ss,
            wotsPkFromSigTops prims (WotsGame.hybSig 0 pk q.1 q.2 ss) q.2 pk q.1),
          s ++ [(q.1, q.2, WotsGame.hybSig 0 pk q.1 q.2 ss,
            wotsPkFromSigTops prims (WotsGame.hybSig 0 pk q.1 q.2 ss) q.2 pk q.1)]) := by
  split_ifs with h
  · simp [qOracles, oraclesIn, signOracleIn, -wotsPkFromSigTops_eq_ofFn]
    rw [if_pos h]; simp
  · simp [qOracles, oraclesIn, signOracleIn, -wotsPkFromSigTops_eq_ofFn]
    rw [if_neg h]; simp [-wotsPkFromSigTops_eq_ofFn]

theorem q_run_bind {α : Type} (pk : prims.PkSeed) (t : (WSpec prims).Domain)
    (k : (WSpec prims).Range t → OracleComp (WSpec prims) α) (s : List (WotsGame.Entry prims)) :
    (simulateQ (qOracles (vp := vp) pk) (liftM ((WSpec prims).query t) >>= k)).run s =
      (qOracles (vp := vp) pk t).run s >>= fun p => (simulateQ (qOracles pk) (k p.1)).run p.2 := by
  rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]

/-- Phase 1 against `qOracles` (followed by any oracle-free continuation) requests start values
only for allowed instances. -/
theorem q_queriesIn {α β : Type} (pk : prims.PkSeed) (c : OracleComp (WSpec prims) α)
    (f : α × List (WotsGame.Entry prims) → ProbComp β) (s : List (WotsGame.Entry prims)) :
    Tables.QueriesIn {a : Adrs | a ∈ wotsInsts vp}
      ((simulateQ (qOracles (vp := vp) pk) c).run s >>= fun r =>
        (liftM (f r) : OracleComp (QSpec prims) β)) := by
  induction c using OracleComp.inductionOn generalizing s with
  | pure x =>
    simp only [simulateQ_pure, StateT.run_pure, pure_bind]
    exact Tables.queriesIn_liftM _ _
  | query_bind t k ih =>
    rw [q_run_bind]
    rcases t with n | q | q
    · rw [q_step_unif]
      simp only [bind_assoc, pure_bind]
      exact allQueriesSatisfy_bind ((allQueriesSatisfy_query_iff _ _).2 trivial) fun u => ih u s
    · rw [q_step_sign]
      split_ifs with h
      · simp only [pure_bind]
        exact ih _ s
      · simp only [bind_assoc, pure_bind]
        refine allQueriesSatisfy_bind ((allQueriesSatisfy_query_iff _ _).2 ?_) fun u => ih _ _
        simp only [not_or, not_not] at h
        exact h.1
    · rw [q_step_coll]
      simp only [pure_bind]
      exact ih _ s

/-- Phase 1 against `qOracles` never requests the start values of an instance twice. -/
theorem q_noRepeat {α β : Type} [MeasurableSpace β] (pk : prims.PkSeed) (c : OracleComp (WSpec prims) α)
    (f : α × List (WotsGame.Entry prims) → ProbComp β) (s : List (WotsGame.Entry prims)) :
    Tables.NoRepeat {a : Adrs | a ∈ s.map (·.1)}
      ((simulateQ (qOracles (vp := vp) pk) c).run s >>= fun r =>
        (liftM (f r) : OracleComp (QSpec prims) β)) := by
  induction c using OracleComp.inductionOn generalizing s with
  | pure x =>
    simp only [simulateQ_pure, StateT.run_pure, pure_bind]
    exact Tables.noRepeat_liftM _ _
  | query_bind t k ih =>
    rw [q_run_bind]
    rcases t with n | q | q
    · rw [q_step_unif]
      simp only [bind_assoc, pure_bind]
      exact (isQueryBound_query_bind_iff _ _ _ _ _).2 ⟨trivial, fun u => ih u s⟩
    · rw [q_step_sign]
      split_ifs with h
      · simp only [pure_bind]
        exact ih _ s
      · simp only [bind_assoc, pure_bind]
        simp only [not_or, not_not] at h
        refine (isQueryBound_query_bind_iff _ _ _ _ _).2 ⟨h.2, fun u => ?_⟩
        have key := ih (some (WotsGame.hybSig 0 pk q.1 q.2 u,
            wotsPkFromSigTops prims (WotsGame.hybSig 0 pk q.1 q.2 u) q.2 pk q.1))
          (s ++ [(q.1, q.2, WotsGame.hybSig 0 pk q.1 q.2 u,
            wotsPkFromSigTops prims (WotsGame.hybSig 0 pk q.1 q.2 u) q.2 pk q.1)])
        have hset : {a : Adrs | a ∈ (s ++ [(q.1, q.2, WotsGame.hybSig 0 pk q.1 q.2 u,
            wotsPkFromSigTops prims (WotsGame.hybSig 0 pk q.1 q.2 u) q.2 pk q.1)]).map (·.1)} =
            insert q.1 {a : Adrs | a ∈ s.map (·.1)} := by
          ext a
          simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append,
            List.mem_singleton, Set.mem_setOf_eq, Set.mem_insert_iff]
          tauto
        rw [hset] at key
        exact key
    · rw [q_step_coll]
      simp only [pure_bind]
      exact ih _ s

/-- Interpreting the block oracle by `I` turns `qOracles` into the game's oracles whose start
values are drawn by `I`. -/
theorem q_push {α : Type} (I : QueryImpl (QSpec prims) ProbComp)
    (hI : ∀ n, I (Sum.inl n) = (liftM (unifSpec.query n) : ProbComp _)) (pk : prims.PkSeed)
    (c : OracleComp (WSpec prims) α) (s : List (WotsGame.Entry prims)) :
    simulateQ I ((simulateQ (qOracles (vp := vp) pk) c).run s) =
      (simulateQ (oraclesIn (m := ProbComp) (QueryImpl.ofLift unifSpec ProbComp)
        (fun a => I (Sum.inr a)) (wotsInsts vp) pk) c).run s := by
  induction c using OracleComp.inductionOn generalizing s with
  | pure x => simp
  | query_bind t k ih =>
    rw [q_run_bind, simulateQ_bind, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    simp only [ih]
    rcases t with n | q | q
    · rw [q_step_unif]
      simp [oraclesIn, hI]
    · rw [q_step_sign]
      split_ifs with h
      · simp [oraclesIn, signOracleIn, -wotsPkFromSigTops_eq_ofFn]
        rw [if_pos h]; simp
      · simp [oraclesIn, signOracleIn, -wotsPkFromSigTops_eq_ofFn]
        rw [if_neg h]; simp [-wotsPkFromSigTops_eq_ofFn]
    · rw [q_step_coll]
      simp [oraclesIn, collOracleIn]

theorem oracles_eq_oraclesIn (insts : List Adrs) (pk : prims.PkSeed) :
    WotsGame.oracles 0 insts pk =
      oraclesIn (m := ProbComp) (QueryImpl.ofLift unifSpec ProbComp)
        (fun _ => ($ᵗ (Vector prims.Y vp.params.len) : ProbComp _)) insts pk := rfl

/-- The end of the WOTS game at `bWots A`, given the outcome of phase 1. -/
noncomputable def finish (A : Forger vp prims optRand pkSeedDist) (pk : prims.PkSeed)
    (tbl : SecretTable vp prims)
    (r : (prims.Y × List (WotsGame.Entry prims)) × List (WotsGame.Entry prims)) :
    ProbComp Bool :=
  g2RunWith A ⟨pk, r.1.1⟩ (signFromHist tbl r.1.2 ⟨pk, r.1.1⟩) >>= fun z =>
    pure (WotsGame.win pk r.2 (wotsAnswer tbl r.1.2 ⟨pk, r.1.1⟩ z.1.1 z.1.2).1
      (wotsAnswer tbl r.1.2 ⟨pk, r.1.1⟩ z.1.1 z.1.2).2.1
      (wotsAnswer tbl r.1.2 ⟨pk, r.1.1⟩ z.1.1 z.1.2).2.2)

theorem finish_congr (hS : Structural vp prims) (A : Forger vp prims optRand pkSeedDist)
    (pk : prims.PkSeed) {tbl tbl' : SecretTable vp prims}
    (h : ∀ i, ¬ IsWotsCell vp i → tbl i = tbl' i) :
    finish A pk tbl = finish A pk tbl' := by
  have hs : ∀ hist pk', signFromHist tbl hist pk' = signFromHist tbl' hist pk' :=
    fun hist pk' => funext fun m => funext fun R => signFromHist_congr hS h hist pk' m R
  funext r
  simp only [finish, wotsAnswer, hs]

/-- The game's phase 1 and end, with the start values requested from the block oracle. -/
noncomputable def qGame (A : Forger vp prims optRand pkSeedDist) (pk : prims.PkSeed)
    (tbl : SecretTable vp prims) : OracleComp (QSpec prims) Bool :=
  (simulateQ (qOracles (vp := vp) pk) ((chooseBody tbl).run [])).run [] >>= fun r =>
    (liftM (finish A pk tbl r) : OracleComp (QSpec prims) Bool)

theorem simulateQ_qGame (A : Forger vp prims optRand pkSeedDist) (pk : prims.PkSeed)
    (tbl : SecretTable vp prims) (I : QueryImpl (QSpec prims) ProbComp)
    (hI : ∀ n, I (Sum.inl n) = (liftM (unifSpec.query n) : ProbComp _))
    (hlift : ∀ ob : ProbComp Bool, simulateQ I (liftM ob : OracleComp (QSpec prims) Bool) = ob) :
    simulateQ I (qGame A pk tbl) =
      (simulateQ (oraclesIn (m := ProbComp) (QueryImpl.ofLift unifSpec ProbComp)
        (fun a => I (Sum.inr a)) (wotsInsts vp) pk) ((chooseBody tbl).run [])).run [] >>=
        finish A pk tbl := by
  rw [qGame, simulateQ_bind, q_push I hI]
  exact bind_congr fun r => hlift _

theorem oraclesIn_run_lift {T γ : Type} (samp : Adrs → ProbComp (Vector prims.Y vp.params.len))
    (insts : List Adrs) (pk : prims.PkSeed) (my : ProbComp T)
    (f : T → OracleComp (WSpec prims) γ) (s : List (WotsGame.Entry prims)) :
    (simulateQ (oraclesIn (m := ProbComp) (QueryImpl.ofLift unifSpec ProbComp) samp insts pk)
        ((monadLift my : OracleComp (WSpec prims) T) >>= f)).run s =
      my >>= fun t => (simulateQ (oraclesIn (m := ProbComp) (QueryImpl.ofLift unifSpec ProbComp)
        samp insts pk) (f t)).run s := by
  have : (monadLift my : OracleComp (WSpec prims) T) = my.liftComp (WSpec prims) := rfl
  rw [simulateQ_bind, StateT.run_bind, this, oraclesIn, QueryImpl.simulateQ_add_liftComp_left,
    simulateQ_liftTarget]
  simp

/-- `WotsGame.hyb 0` at `bWots A`, with the start values requested from a fresh-sampling block
oracle. -/
theorem hyb_bWots_eq (A : Forger vp prims optRand pkSeedDist) :
    WotsGame.hyb pkSeedDist (wotsInsts vp) 0 (bWots A) =
      pkSeedDist >>= fun pk => sampleTable vp prims >>= fun tbl =>
        simulateQ (Tables.freshImpl Adrs (Vector prims.Y vp.params.len)) (qGame A pk tbl) := by
  unfold WotsGame.hyb
  refine bind_congr fun pk => ?_
  rw [oracles_eq_oraclesIn]
  have h1 := oraclesIn_run_lift (vp := vp) (prims := prims)
    (fun _ => ($ᵗ (Vector prims.Y vp.params.len) : ProbComp _)) (wotsInsts vp) pk
    (sampleTable vp prims)
    (fun tbl => (chooseBody tbl).run [] >>= fun x =>
      (pure (tbl, x.2, x.1) : OracleComp (WSpec prims) (bWots A).State)) []
  have h2 : (bWots A).choose = (monadLift (sampleTable vp prims) :
      OracleComp (WSpec prims) (SecretTable vp prims)) >>= fun tbl =>
        (chooseBody tbl).run [] >>= fun x =>
          (pure (tbl, x.2, x.1) : OracleComp (WSpec prims) (bWots A).State) := rfl
  rw [h2, h1, bind_assoc]
  refine bind_congr fun tbl => ?_
  rw [simulateQ_qGame A pk tbl _ (fun _ => rfl) (fun ob => Tables.simulateQ_freshImpl_liftM ob)]
  rw [simulateQ_bind, StateT.run_bind, bind_assoc]
  refine bind_congr fun r => ?_
  change ((g2RunWith A ⟨pk, r.1.1⟩ (signFromHist tbl r.1.2 ⟨pk, r.1.1⟩) >>= fun z =>
      (pure (wotsAnswer tbl r.1.2 ⟨pk, r.1.1⟩ z.1.1 z.1.2) : ProbComp _)) >>= fun x =>
      match r.2[x.1]? with
      | none => pure false
      | some (a, m, _, tops) =>
        pure (decide (x.2.1 ≠ m ∧ wotsPkFromSigTops prims x.2.2 x.2.1 pk a = tops))) = _
  rw [finish, bind_assoc]
  refine bind_congr fun z => ?_
  rw [pure_bind]
  simp only [WotsGame.win]
  split <;> rename_i heq <;> simp only [heq]

theorem prTrue_bind_bind_mono {P T : Type} (mp : ProbComp P) (my : ProbComp T)
    (f g : P → T → ProbComp Bool) (h : ∀ p t, prTrue (f p t) ≤ prTrue (g p t)) :
    prTrue (mp >>= fun p => my >>= fun t => f p t) ≤
      prTrue (mp >>= fun p => my >>= fun t => g p t) :=
  prTrue_bind_mono _ _ _ fun p _ => prTrue_bind_mono _ _ _ fun t _ => h p t

/-- The start-value cells of instance `a`. -/
def wotsCells (vp : ValidatedParams) (a : Adrs) (j : Fin vp.params.len) : SecIdx :=
  secIdx (wotsSkAdrs a j.val)

/-- **Simulation coupling, deterministic half.**  For a fixed seed and table, when the WOTS game
draws the start values of every instance from the table, the forger's view in `bWots A` is its
view in `G2` (same public key, same signing oracle), and the extracted answer wins whenever the
forgery is fresh, valid and of class `wots`. -/
theorem table_step (hS : Structural vp prims) (A : Forger vp prims optRand pkSeedDist)
    (pk : prims.PkSeed) (tbl : SecretTable vp prims) :
    prTrue (g2Run A tbl (idealPk vp prims tbl pk) >>= fun z =>
        pure (g2Valid (idealPk vp prims tbl pk) z.2 z.1.1 z.1.2 &&
          decide (g2ClassOf tbl (idealPk vp prims tbl pk) z.2 z.1.1 z.1.2 = .wots))) ≤
      prTrue (simulateQ (Tables.fnImpl fun a => Tables.readBlock tbl (wotsCells vp a))
        (qGame A pk tbl)) := by
  rw [simulateQ_qGame A pk tbl _ (fun _ => rfl) (fun ob => Tables.simulateQ_fnImpl_liftM _ ob)]
  obtain ⟨hist, hrun, hg⟩ := chooseBody_run hS tbl pk
  change _ ≤ prTrue ((simulateQ (tblOracles tbl pk) ((chooseBody tbl).run [])).run [] >>=
    finish A pk tbl)
  rw [hrun, pure_bind, finish]
  have hsign : signFromHist tbl hist (idealPk vp prims tbl pk) =
      fun m R => idealSign vp prims tbl m (idealPk vp prims tbl pk) R :=
    funext fun m => funext fun R => signFromHist_eq_idealSign hS tbl hist _ hg m R
  change _ ≤ prTrue (g2RunWith A (idealPk vp prims tbl pk)
    (signFromHist tbl hist (idealPk vp prims tbl pk)) >>= fun z => pure (WotsGame.win pk hist
      (wotsAnswer tbl hist (idealPk vp prims tbl pk) z.1.1 z.1.2).1
      (wotsAnswer tbl hist (idealPk vp prims tbl pk) z.1.1 z.1.2).2.1
      (wotsAnswer tbl hist (idealPk vp prims tbl pk) z.1.1 z.1.2).2.2))
  rw [hsign]
  refine prTrue_bind_pure_mono _ _ _ fun z _ hz => ?_
  rw [Bool.and_eq_true, decide_eq_true_eq] at hz
  exact wotsAnswer_wins hS tbl hist (idealPk vp prims tbl pk) z.2 z.1.1 z.1.2 hg hz.1 hz.2

/-- **Simulation coupling, probabilistic half.**  The start values the WOTS game draws afresh at
each (never repeated) instance and the table `bWots A` draws for the FORS secrets are jointly
distributed as one uniform table. -/
theorem fresh_eq_table (hS : Structural vp prims) (A : Forger vp prims optRand pkSeedDist)
    (pk : prims.PkSeed) :
    𝒟[sampleTable vp prims >>= fun tbl =>
        simulateQ (Tables.freshImpl Adrs (Vector prims.Y vp.params.len)) (qGame A pk tbl)] =
      𝒟[sampleTable vp prims >>= fun tbl =>
        simulateQ (Tables.fnImpl fun a => Tables.readBlock tbl (wotsCells vp a))
          (qGame A pk tbl)] := by
  have hempty : ({a : Adrs | a ∈ ([] : List (WotsGame.Entry prims)).map (·.1)} : Set Adrs) = ∅ := by
    ext a; simp
  refine evalDist_sampleTable_bind_freshImpl_block (wotsCells vp) (S := {a | a ∈ wotsInsts vp})
    (fun a ha a' ha' j j' h => wotsCell_inj hS a ha a' ha' j j' h) (qGame A pk)
    (fun tbl => q_queriesIn pk _ _ _) (fun tbl => hempty ▸ q_noRepeat pk _ _ _) ?_
  intro tbl tbl' h
  have h' : ∀ i, ¬ IsWotsCell vp i → tbl i = tbl' i :=
    fun i hi => h i fun d hd j hji => hi ⟨d, hd, j, hji⟩
  rw [qGame, qGame, chooseBody_congr hS h', finish_congr hS A pk h']

/-- **Step 7.** -/
theorem stepWotsEmbed (hS : Structural vp prims) (A : Forger vp prims optRand pkSeedDist) :
    StepWotsEmbed A (bWots A) := by
  unfold StepWotsEmbed
  rw [hyb_bWots_eq]
  calc prTrue (g2Class A .wots)
      ≤ prTrue (pkSeedDist >>= fun pk => sampleTable vp prims >>= fun tbl =>
          simulateQ (Tables.fnImpl fun a => Tables.readBlock tbl (wotsCells vp a))
            (qGame A pk tbl)) :=
        prTrue_bind_bind_mono pkSeedDist (sampleTable vp prims) _ _ (table_step hS A)
    _ = _ := prTrue_bind_congr _ _ _ fun pk _ => prTrue_congr (fresh_eq_table hS A pk).symm

end Glue


end Reduction

#print axioms Reduction.wotsAnswer_wins
#print axioms Reduction.stepWotsEmbed
