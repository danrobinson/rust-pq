/-
The proofs in this file follow `HashSig/SLHDSA/AddressDiscipline.lean` (Copyright (c) 2026
Alexander Hicks) and `HashSig/SLHDSA/Security/ComponentTraces.lean` (Copyright (c) 2026 Alexander
Hicks) of VCVio, released under the Apache 2.0 license (see `../.tools/VCVio-upstream/LICENSE`);
they are adapted here to a role-refined hypothesis.
-/
import HashSig.SLHDSA.AddressDiscipline
import HashSig.SLHDSA.Security.ComponentTraces
import HashSig.SLHDSA.Security.EncodedTargets

/-!
# S1, part 1: the role-refined address discipline of the SLH-DSA programs (`status/DIRECT.md` §14)

VCVio's `AddressDiscipline` shows that the honest programs evaluate the tweakable hash only at
addresses of type at most `4`; its hypotheses quantify over every list at every such address,
which is too coarse for the coupling of §13.1 (S1 needs the **arity** of each `Thash` call).
VCVio's `ComponentTraces` places every call at a reachable address in the six role ledgers, but
records only membership in their union.  Here the two are combined: for every predicate `Q` on
programs closed under `pure`/`bind`, `Q` holds of a provider-parametric program
(key generation, signing at a randomizer, verification) as soon as it holds of

* the `F` callback (`hash`) at every address of the WOTS+ step or FORS leaf ledger (`FAd`),
* the `H` callback (`nodeHash`) at every address of the XMSS node or FORS node ledger (`HAd`),
* the `T_l` callback (`compress`) at every WOTS+ public-key address with a list of length `len`
  and every FORS roots address with a list of length `k` (`TAd`),
* the secret provider everywhere.

The programs are those of `HashSig.SLHDSA.SecretProvider` (keygen, signing) and
`GeneralScheme.verifyInternalM`, at the reachable positions they use.
-/

open OracleComp OracleSpec

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Ideal.Direct.Rom.S1

open SLHDSA SLHDSA.Security

variable {vp : ValidatedParams}

/-- The `F` addresses (arity 1): the WOTS+ step and FORS leaf ledgers. -/
def FAd (vp : ValidatedParams) (a : Adrs) : Prop :=
  a ∈ wotsStepAddresses vp ∨ a ∈ forsLeafAddresses vp

/-- The `H` addresses (arity 2): the XMSS node and FORS internal-node ledgers. -/
def HAd (vp : ValidatedParams) (a : Adrs) : Prop :=
  a ∈ xmssNodeAddresses vp ∨ a ∈ forsTreeAddresses vp

/-- The `T_l` addresses with their arity: WOTS+ public keys (`len`), FORS roots (`k`). -/
def TAd (vp : ValidatedParams) (a : Adrs) (n : ℕ) : Prop :=
  (a ∈ wotsPkAddresses vp ∧ n = vp.params.len) ∨ (a ∈ forsRootAddresses vp ∧ n = vp.params.k)

section Generic

variable {m : Type → Type*} [Monad m] [LawfulMonad m] (Q : ∀ {α : Type}, m α → Prop)
  (hpure : ∀ {α : Type} (x : α), Q (pure x))
  (hbind : ∀ {α β : Type} (oa : m α) (ob : α → m β), Q oa → (∀ x, Q (ob x)) → Q (oa >>= ob))
  (core : CorePrimitives vp.params)
  {hash : Adrs → core.Y → m core.Y} {compress : Adrs → List core.Y → m core.Y}
  {nodeHash : Adrs → core.Y → core.Y → m core.Y} {secret : Adrs → m core.Y}
  (hF : ∀ a, FAd vp a → ∀ y, Q (hash a y))
  (hT : ∀ a ys, TAd vp a ys.length → Q (compress a ys))
  (hH : ∀ a, HAd vp a → ∀ l r, Q (nodeHash a l r))
  (hS : ∀ a, Q (secret a))

/-! ### WOTS+ -/

include hpure hbind hF in
theorem chain_ok (pos : LayerPosition vp) (chain : Fin vp.params.len) (x : core.Y) (i s : ℕ)
    (hint : i + s ≤ vp.params.w - 1) :
    Q (chainWith hash (wotsChainAdrs (wotsInstanceAdrs pos) chain.val) x i s) :=
  SLHDSA.chainWith_pred Q hpure hbind x i s fun j hj y => by
    have hstep : i + j < vp.params.w - 1 := by omega
    refine hF _ (.inl ?_) y
    simpa [wotsStepAdrs] using mem_wotsStepAddresses vp (pos, chain) ⟨i + j, hstep⟩

include hpure hbind hF hT hS in
theorem wotsPkGen_ok (pos : LayerPosition vp) :
    Q (wotsPkGenWithSecret core hash compress secret (wotsInstanceAdrs pos)) :=
  hbind _ _ (Vector.ofFnM_pred Q hpure hbind _ fun i =>
    hbind _ _ (hS _) fun x => chain_ok Q hpure hbind core hF pos i x 0 _ (by omega))
    fun tops => hT _ _ (.inl ⟨mem_wotsPkAddresses vp pos, by simp⟩)

include hpure hbind hF hS in
theorem wotsSign_ok (msg : core.Y) (pos : LayerPosition vp) :
    Q (wotsSignWithSecret core hash secret msg (wotsInstanceAdrs pos)) :=
  Vector.ofFnM_pred Q hpure hbind _ fun i =>
    hbind _ _ (hS _) fun x => chain_ok Q hpure hbind core hF pos i x 0 _ (by
      simpa using chainStepsCore_le core msg i.val)

include hpure hbind hF hT in
theorem wotsPkFromSig_ok (sig : WotsSig vp.params core) (msg : core.Y) (pos : LayerPosition vp) :
    Q (wotsPkFromSigWith core hash compress sig msg (wotsInstanceAdrs pos)) :=
  hbind _ _ (Vector.ofFnM_pred Q hpure hbind _ fun i =>
    chain_ok Q hpure hbind core hF pos i _ _ _ (by
      rw [Nat.add_sub_of_le]
      exact chainStepsCore_le core msg i.val))
    fun tops => hT _ _ (.inl ⟨mem_wotsPkAddresses vp pos, by simp⟩)

/-! ### XMSS -/

include hpure hbind hF hT hH hS in
theorem xmssNode_ok (coord : LayerTreeCoord vp) {z t : ℕ} (hz : z ≤ vp.params.hp)
    (ht : t < 2 ^ (vp.params.hp - z)) :
    Q (xmssNodeWithSecret core hash compress nodeHash secret coord.toAdrs z t) :=
  PerfectMerkleTree.merkleRootM_pred_of_subtree Q hbind _ _ z t
    (fun i hi => wotsPkGen_ok Q hpure hbind core hF hT hS
      ⟨coord.layer, coord.tree, ⟨i, lt_pow_of_div_pow_lt hz hi ht⟩⟩)
    fun h i hh hhz hi l r => by
      refine hH _ (.inl (mem_xmssNodeAddresses vp coord hh (hhz.trans hz) ?_)) l r
      have hlt : i / 2 ^ (z - h) < 2 ^ (vp.params.hp - z) := by rw [hi]; exact ht
      rwa [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add,
        show vp.params.hp - z + (z - h) = vp.params.hp - h by omega] at hlt

include hpure hbind hF hT hH hS in
theorem xmssSign_ok (msg : core.Y) (pos : LayerPosition vp) :
    Q (xmssSignWithSecret core hash compress nodeHash secret msg pos.toAdrs pos.leaf.val) := by
  have hleaf : pos.leaf.val / 2 ^ vp.params.hp = 0 := Nat.div_eq_of_lt pos.leaf.isLt
  refine hbind _ _ ?_ fun path => hbind _ _ (wotsSign_ok Q hpure hbind core hF hS msg pos)
    fun _ => hpure _
  refine PerfectMerkleTree.intrinsicAuthPathM_pred_of_tree Q hpure hbind _ _ _ _
    (fun i hi => ?_) fun h i hh hhp hi l r => ?_
  · rw [hleaf] at hi
    exact wotsPkGen_ok Q hpure hbind core hF hT hS
      ⟨pos.layer, pos.tree, ⟨i, lt_pow_of_div_pow_lt le_rfl hi (by positivity)⟩⟩
  · rw [hleaf] at hi
    refine hH _ (.inl (mem_xmssNodeAddresses_of_position vp pos hh hhp ?_)) l r
    have hlt : i / 2 ^ (vp.params.hp - h) < 1 := by rw [hi]; exact Nat.one_pos
    rwa [Nat.div_lt_iff_lt_mul (by positivity), Nat.one_mul] at hlt

include hpure hbind hF hT hH in
theorem xmssPkFromSig_ok (sig : XmssSig vp.params core) (msg : core.Y) (pos : LayerPosition vp) :
    Q (xmssPkFromSigWith core hash compress nodeHash pos.leaf.val sig msg pos.toAdrs) :=
  hbind _ _ (wotsPkFromSig_ok Q hpure hbind core hF hT sig.wots msg pos) fun leaf =>
    PerfectMerkleTree.climbM_pred_of_ancestors Q hpure hbind _ _ _ _ fun h hh hhp l r => by
      simp only [Vector.length_toList] at hhp
      refine hH _ (.inl (mem_xmssNodeAddresses_of_position vp pos hh hhp ?_)) l r
      rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, Nat.sub_add_cancel hhp]
      exact pos.leaf.isLt

/-! ### FORS -/

theorem forsLeaf_mem (pos : BottomPosition vp) (tree : Fin vp.params.k) {i : ℕ}
    (hi : i / 2 ^ vp.params.a = tree.val) :
    forsNodeAdrs pos.forsAdrs 0 i ∈ forsLeafAddresses vp := by
  have hidx : tree.val * vp.params.t + i % 2 ^ vp.params.a = i := by
    rw [← hi]
    exact Nat.div_add_mod' i _
  simpa [hidx] using mem_forsLeafAddresses vp pos tree
    ⟨i % 2 ^ vp.params.a, Nat.mod_lt i (by positivity)⟩

theorem forsTree_mem (pos : BottomPosition vp) (tree : Fin vp.params.k) {h i : ℕ}
    (hh : 0 < h) (hha : h ≤ vp.params.a) (hi : i / 2 ^ (vp.params.a - h) = tree.val) :
    forsNodeAdrs pos.forsAdrs h i ∈ forsTreeAddresses vp := by
  have hidx : tree.val * 2 ^ (vp.params.a - h) + i % 2 ^ (vp.params.a - h) = i := by
    rw [← hi]
    exact Nat.div_add_mod' i _
  simpa [hidx] using mem_forsTreeAddresses vp pos tree hh hha
    (Nat.mod_lt i (by positivity) : i % 2 ^ (vp.params.a - h) < 2 ^ (vp.params.a - h))

include hpure hbind hF hH hS in
theorem forsSign_ok (md : List Byte) (pos : BottomPosition vp) :
    Q (forsSignWithSecret core hash nodeHash secret md pos.forsAdrs) := by
  refine Vector.ofFnM_pred Q hpure hbind _ fun tree => ?_
  refine hbind _ _ (hS _) fun _ => hbind _ _ ?_ fun _ => hpure _
  refine PerfectMerkleTree.intrinsicAuthPathM_pred_of_tree Q hpure hbind _ _ _ _
    (fun i hi => ?_) fun h i hh hha hi l r => ?_
  · rw [forsLeafIndex_div] at hi
    exact hbind _ _ (hS _) fun x => hF _ (.inr (forsLeaf_mem pos tree hi)) x
  · rw [forsLeafIndex_div] at hi
    exact hH _ (.inr (forsTree_mem pos tree hh hha hi)) l r

include hpure hbind hF hT hH in
theorem forsPkFromSig_ok (sig : ForsSigCore vp.params core) (md : List Byte)
    (pos : BottomPosition vp) :
    Q (forsPkFromSigWith core hash nodeHash compress sig md pos.forsAdrs) := by
  refine hbind _ _ (Vector.ofFnM_pred Q hpure hbind _ fun tree => ?_) fun roots =>
    hT _ _ (.inr ⟨mem_forsRootAddresses vp pos, by simp⟩)
  refine hbind _ _ (hF _ (.inr (forsLeaf_mem pos tree (forsLeafIndex_div _ md _))) _)
    fun leaf => ?_
  refine PerfectMerkleTree.climbM_pred_of_ancestors Q hpure hbind _ _ _ _
    fun h hh hha l r => ?_
  simp only [Vector.length_toList] at hha
  refine hH _ (.inr (forsTree_mem pos tree hh hha ?_)) l r
  rw [Nat.div_div_eq_div_mul, ← pow_add, Nat.add_sub_cancel' hha, forsLeafIndex_div]

/-! ### The hypertree -/

include hpure hbind hF hT hH hS in
theorem signFromPosition_ok (recoverFinal : Bool) (pos : LayerPosition vp) (layers : ℕ)
    (hrem : pos.layer.val + layers = vp.params.d) (msg : core.Y) :
    Q (GeneralHypertree.signFromPositionWithSecret core hash compress nodeHash secret recoverFinal
      pos layers hrem msg) := by
  induction layers using Nat.twoStepInduction generalizing recoverFinal pos msg with
  | zero => rw [GeneralHypertree.signFromPositionWithSecret]; exact hpure _
  | one =>
      rw [GeneralHypertree.signFromPositionWithSecret]
      refine hbind _ _ (xmssSign_ok Q hpure hbind core hF hT hH hS msg pos) fun sig => ?_
      cases recoverFinal
      · exact hpure _
      · exact hbind _ _ (xmssPkFromSig_ok Q hpure hbind core hF hT hH sig msg pos)
          fun _ => hpure _
  | more layers _ ih =>
      rw [GeneralHypertree.signFromPositionWithSecret]
      exact hbind _ _ (xmssSign_ok Q hpure hbind core hF hT hH hS msg pos) fun sig =>
        hbind _ _ (xmssPkFromSig_ok Q hpure hbind core hF hT hH sig msg pos) fun root =>
          hbind _ _ (ih _ _ _ _) fun _ => hpure _

include hpure hbind hF hT hH in
theorem recoverFromPosition_ok (pkSeed : core.PkSeed) (pos : LayerPosition vp) (layers : ℕ)
    (hrem : pos.layer.val + layers = vp.params.d) (msg : core.Y)
    (sigs : Vector (XmssSig vp.params core) layers) :
    Q (GeneralHypertree.recoverFromPositionWith vp core hash compress nodeHash pkSeed pos layers
      hrem msg sigs) := by
  induction layers using Nat.twoStepInduction generalizing pos msg with
  | zero => rw [GeneralHypertree.recoverFromPositionWith]; exact hpure _
  | one =>
      rw [GeneralHypertree.recoverFromPositionWith]
      exact xmssPkFromSig_ok Q hpure hbind core hF hT hH _ msg pos
  | more layers _ ih =>
      rw [GeneralHypertree.recoverFromPositionWith]
      exact hbind _ _ (xmssPkFromSig_ok Q hpure hbind core hF hT hH _ msg pos) fun root =>
        ih _ _ _ _

end Generic

/-! ### The internal scheme, through the explicit public hash -/

/-- **A role-correct `Thash` query at the public seed `ps`**: the seed is `ps`, and the address
key is the key of a ledger address of a role whose arity is the length of the input list. -/
def RQ (vp : ValidatedParams) (core : CorePrimitives vp.params) (ps : core.PkSeed) :
    (publicHashSpec core).Domain → Prop
  | .thash ps' key xs => ps' = ps ∧ ∃ a, key = core.adrsToKey a ∧
      ((FAd vp a ∧ xs.length = 1) ∨ (HAd vp a ∧ xs.length = 2) ∨ TAd vp a xs.length)
  | .hmsg _ _ _ _ => False

section Scheme

variable {m : Type → Type*} [Monad m] [LawfulMonad m] (Q : ∀ {α : Type}, m α → Prop)
  (hpure : ∀ {α : Type} (x : α), Q (pure x))
  (hbind : ∀ {α β : Type} (oa : m α) (ob : α → m β), Q oa → (∀ x, Q (ob x)) → Q (oa >>= ob))
  (core : CorePrimitives vp.params) [HasQuery (publicHashSpec core) m] (ps : core.PkSeed)
  (hq : ∀ q, RQ vp core ps q → Q (HasQuery.query (spec := publicHashSpec core) q))
  {secret : Adrs → m core.Y} (hS : ∀ a, Q (secret a))

include hq in
theorem f_ok : ∀ a, FAd vp a → ∀ y, Q (PublicHash.f core ps a y : m core.Y) :=
  fun a ha y => hq _ ⟨rfl, a, rfl, .inl ⟨ha, rfl⟩⟩

include hq in
theorem h_ok : ∀ a, HAd vp a → ∀ l r, Q (PublicHash.h core ps a l r : m core.Y) :=
  fun a ha l r => hq _ ⟨rfl, a, rfl, .inr (.inl ⟨ha, rfl⟩)⟩

include hq in
theorem tl_ok : ∀ a ys, TAd vp a ys.length → Q (PublicHash.tl core ps a ys : m core.Y) :=
  fun a ys ha => hq _ ⟨rfl, a, rfl, .inr (.inr ha)⟩

include hpure hbind hq hS in
/-- **Key generation issues only role-correct `Thash` queries at its public seed.** -/
theorem keygen_ok : Q (GeneralScheme.keygenInternalWithSecretM core secret ps) := by
  unfold GeneralScheme.keygenInternalWithSecretM GeneralHypertree.rootWithSecretM
    GeneralHypertree.rootWithSecret xmssRootWithSecret
  rw [← LayerTreeCoord.top_toAdrs_layerAdrs]
  have hF := f_ok Q core ps hq
  have hT := tl_ok Q core ps hq
  have hH := h_ok Q core ps hq
  exact xmssNode_ok Q hpure hbind core hF hT hH hS _ le_rfl (by simp)

include hpure hbind hq hS in
/-- **Signing issues only role-correct `Thash` queries at its public seed**, and one `H_msg`
query (`hm`). -/
theorem sign_ok (msg : List Byte) (root R : core.Y)
    (hm : Q (PublicHash.hmsg core R ps root msg : m _)) :
    Q (GeneralScheme.signInternalWithSecretRandomizerM core secret msg ps root R) := by
  unfold GeneralScheme.signInternalWithSecretRandomizerM
  refine hbind _ _ hm fun digest => ?_
  have hF := f_ok Q core ps hq
  have hT := tl_ok Q core ps hq
  have hH := h_ok Q core ps hq
  refine hbind _ _ ?_ fun forsSig => hbind _ _ ?_ fun forsPk => hbind _ _ ?_ fun _ => hpure _
  · unfold forsSignWithSecretM
    rw [← BottomPosition.forsAdrs_ofDigestParts vp]
    exact forsSign_ok Q hpure hbind core hF hH hS _ _
  · unfold forsPkFromSigM
    rw [← BottomPosition.forsAdrs_ofDigestParts vp]
    exact forsPkFromSig_ok Q hpure hbind core hF hT hH _ _ _
  · unfold GeneralHypertree.signWithSecretM GeneralHypertree.signWithSecret
    exact signFromPosition_ok Q hpure hbind core hF hT hH hS _ _ _ _ _

end Scheme

section Verify

variable {m : Type → Type*} [Monad m] [LawfulMonad m] (Q : ∀ {α : Type}, m α → Prop)
  (hpure : ∀ {α : Type} (x : α), Q (pure x))
  (hbind : ∀ {α β : Type} (oa : m α) (ob : α → m β), Q oa → (∀ x, Q (ob x)) → Q (oa >>= ob))
  (core : CorePrimitives vp.params) [HasQuery (publicHashSpec core) m] [DecidableEq core.Y]
  (pk : PublicKeyCore core)
  (hq : ∀ q, RQ vp core pk.pkSeed q → Q (HasQuery.query (spec := publicHashSpec core) q))

include hpure hbind hq in
/-- **Verification issues only role-correct `Thash` queries at the public seed of its key**, and
one `H_msg` query (`hm`), for every signature. -/
theorem verify_ok (msg : List Byte) (sig : GeneralScheme.SignatureCore vp core)
    (hm : Q (PublicHash.hmsg core sig.randomness pk.pkSeed pk.pkRoot msg : m _)) :
    Q (GeneralScheme.verifyInternalM vp core msg sig pk) := by
  unfold GeneralScheme.verifyInternalM
  refine hbind _ _ hm fun digest => ?_
  have hF := f_ok Q core pk.pkSeed hq
  have hT := tl_ok Q core pk.pkSeed hq
  have hH := h_ok Q core pk.pkSeed hq
  refine hbind _ _ ?_ fun forsPk => ?_
  · unfold forsPkFromSigM
    rw [← BottomPosition.forsAdrs_ofDigestParts vp]
    exact forsPkFromSig_ok Q hpure hbind core hF hT hH _ _ _
  · unfold GeneralHypertree.verifyM GeneralHypertree.pkFromSigM GeneralHypertree.recoverFromPositionM
    exact hbind _ _ (recoverFromPosition_ok Q hpure hbind core hF hT hH _ _ _ _ _ _)
      fun _ => hpure _

end Verify

end Ideal.Direct.Rom.S1

#print axioms Ideal.Direct.Rom.S1.keygen_ok
#print axioms Ideal.Direct.Rom.S1.sign_ok
#print axioms Ideal.Direct.Rom.S1.verify_ok
