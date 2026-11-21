import Ideal.Realize.Port
import Ideal.ComposeFinal

/-!
# The second block of every `Thash` chain of the signing walks is not `cB` (ITSR realiser)

The ITSR bound with fine accounting (`Ideal.itsr_bound_128s_fine`) counts every chain query whose
SECOND block is the constant block `cB` (the second outer block of `H_msg`).  A `Thash`
evaluation `Thash(pk, a, xs)` is the chain `sb128 pk, (tblocks a xs).1, (tblocks a xs).2…`: its
second block is the first block of `ADRSc ‖ xs ‖ pad`.  It is never `cB`:

* `F` (`|xs| = 1`): byte 38 is the padding byte `0x80`, byte 38 of `cB` is `0`
  (`tblocks_one_ne_cB'`, the statement of `Ideal.tblocks_one_ne_cB`);
* `H` (`|xs| = 2`): byte 54 is the padding byte `0x80`, byte 54 of `cB` is `0`
  (`tblocks_two_ne_cB`);
* `T_len`, `T_k`: byte 9 is the address-type byte of `ADRSc` (`btw128_tblocks`), which is `1`
  (`WOTS_PK`) resp. `4` (`FORS_ROOTS`) at the addresses `wotsPkAdrs b`, `forsPkAdrs b` where the
  walks call `T_len`, `T_k` (and `7` on the fallback key), while byte 9 of `cB` is `0`
  (`tblocks_ne_cB_of_key9`, `key9_wotsPk`, `key9_forsPk`).

For the last case the address matters, so the walk lemmas of `Ideal/Realize/Walk.lean` (whose
`T_ℓ` hypothesis quantifies over every address) are re-proved here with the hypothesis on the
`T_ℓ` callback restricted to the addresses `wotsPkAdrs b` (on `len` values) and `forsPkAdrs b`
(on `k` values): `npA_*`, and for the open programs `npA_openKeygen`, `npA_openSign`.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security

namespace Ideal.Realize.Itsr

open Reduction Reduction.Lazy Ideal.Realize

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! ## Bytes of the second block -/

theorem cB_get9 : cB[9] = 0 := by decide
theorem cB_get38' : cB[38] = 0 := by decide
theorem cB_get54 : cB[54] = 0 := by decide

/-- Byte 54 of the first block of `tblocks a [l, r]` is the padding byte `0x80`. -/
theorem tblocks_two_get54 (a : Bytes 22) (l r : Bytes 16) : (tblocks a [l, r]).1[54] = 0x80 := by
  rw [tblocks_fst_eq]
  simp only [Vector.getElem_ofFn, tbytes]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp [flat])]
  simp [tailL, flat]
  rfl

/-- `F`: the second block of the chain is not `cB`. -/
theorem tblocks_one_ne_cB' (a : Bytes 22) (k : Bytes 16) : (tblocks a [k]).1 ≠ cB := by
  intro h
  have h1 := congrArg (fun v : Blk => v[38]) h
  simp only [tblocks_one_get38, cB_get38'] at h1
  exact absurd h1 (by decide)

/-- `H`: the second block of the chain is not `cB`. -/
theorem tblocks_two_ne_cB (a : Bytes 22) (l r : Bytes 16) : (tblocks a [l, r]).1 ≠ cB := by
  intro h
  have h1 := congrArg (fun v : Blk => v[54]) h
  simp only [tblocks_two_get54, cB_get54] at h1
  exact absurd h1 (by decide)

/-- Any arity: if byte 9 of the address key is not zero, the second block is not `cB`. -/
theorem tblocks_ne_cB_of_key9 (a : Bytes 22) (xs : List (Bytes 16)) (h : a[9] ≠ 0) :
    (tblocks a xs).1 ≠ cB := by
  intro he
  have h1 := btw128_tblocks a xs
  rw [he] at h1
  have h2 := congrArg (fun v : Bytes 22 => v[9]) h1
  simp only [btw128, Vector.getElem_ofFn] at h2
  rw [cB_get9] at h2
  exact h h2.symm

/-- Byte 9 of the SHA-2 address key of an address of type `WOTS_PK` or `FORS_ROOTS` is not
zero (it is the type byte, or `7` on the fallback key). -/
theorem key9_of_type (a : Adrs) (h1 : a.type = 1 ∨ a.type = 4) :
    (SLHDSA.Concrete.sha2AdrsKey a)[9] ≠ 0 := by
  unfold SLHDSA.Concrete.sha2AdrsKey
  split
  · rename_i v hv
    unfold Adrs.compressSha2Checked at hv
    split_ifs at hv
    cases hv
    simp only [Vector.getElem_mk, List.getElem_toArray]
    rcases h1 with h | h <;>
    · simp only [Adrs.compressSha2, h]
      rw [List.getElem_append_left (by simp), List.getElem_append_left (by simp),
        List.getElem_append_left (by simp), List.getElem_append_right (by simp)]
      simp
      simp [Adrs.toBytesBE, toByte, VCVio.Algorithms.Encoding.natToBytesBE]
  · simp [SLHDSA.Concrete.sha2FallbackKey]
    rcases h1 with h | h <;> simp [h]

theorem key9_wotsPk (b : Adrs) : (SLHDSA.Concrete.sha2AdrsKey (wotsPkAdrs b))[9] ≠ 0 :=
  key9_of_type _ (Or.inl rfl)

theorem key9_forsPk (b : Adrs) : (SLHDSA.Concrete.sha2AdrsKey (forsPkAdrs b))[9] ≠ 0 :=
  key9_of_type _ (Or.inr rfl)

/-! ## The walks, with the `T_ℓ` hypothesis restricted to the `WOTS_PK` / `FORS_ROOTS`
addresses -/

section Walk

variable {vp : ValidatedParams} {κ' : Type} {spec : OracleSpec κ'} (p : κ' → Prop) [DecidablePred p]
variable (core : CorePrimitives vp.params)
  {hash : Adrs → core.Y → OracleComp spec core.Y}
  {compress : Adrs → List core.Y → OracleComp spec core.Y}
  {nodeHash : Adrs → core.Y → core.Y → OracleComp spec core.Y}
  {secret : Adrs → OracleComp spec core.Y}

variable (hhash : ∀ a y, IsQueryBoundP (hash a y) p 0)
  (hcw : ∀ b ys, ys.length = vp.params.len → IsQueryBoundP (compress (wotsPkAdrs b) ys) p 0)
  (hcf : ∀ b ys, ys.length = vp.params.k → IsQueryBoundP (compress (forsPkAdrs b) ys) p 0)
  (hnode : ∀ a l r, IsQueryBoundP (nodeHash a l r) p 0)
  (hsecret : ∀ a, IsQueryBoundP (secret a) p 0)

include hhash hcw hsecret in
theorem npA_wotsPkGen (adrs : Adrs) :
    IsQueryBoundP (wotsPkGenWithSecret core hash compress secret adrs) p 0 :=
  isQueryBoundP_bind_zero _ _ (np_wotsTops p core hhash hsecret adrs) fun tops =>
    hcw _ _ (by simp)

include hhash hcw hnode hsecret in
theorem npA_xmssNode (adrs : Adrs) (z t : ℕ) :
    IsQueryBoundP (xmssNodeWithSecret core hash compress nodeHash secret adrs z t) p 0 :=
  (qb_merkleRoot p (xmssLeafWithSecret core hash compress secret adrs)
    (xmssNodeHashWith nodeHash adrs) 0 0 z t
    (fun i => npA_wotsPkGen p core hhash hcw hsecret _)
    (fun h i l r => hnode _ l r)).mono (Nat.le_of_eq (merkleB_zero z))

include hhash hcw hnode hsecret in
theorem npA_xmssSign (msg : core.Y) (adrs : Adrs) (idx : ℕ) :
    IsQueryBoundP (xmssSignWithSecret core hash compress nodeHash secret msg adrs idx) p 0 := by
  have h := (qb_authPath p (xmssLeafWithSecret core hash compress secret adrs)
    (xmssNodeHashWith nodeHash adrs) 0 0 idx vp.params.hp
    (fun i => npA_wotsPkGen p core hhash hcw hsecret _)
    (fun h i l r => hnode _ l r)).mono (Nat.le_of_eq (authB_zero _))
  exact isQueryBoundP_bind_zero _ _ h fun path =>
    isQueryBoundP_bind_zero _ _ (np_wotsSign p core hhash hsecret msg _) fun sig =>
      isQueryBoundP_pure _ _ _

include hhash hcw in
theorem npA_wotsPkFromSig (sig : WotsSig vp.params core) (msg : core.Y) (adrs : Adrs) :
    IsQueryBoundP (wotsPkFromSigWith core hash compress sig msg adrs) p 0 :=
  isQueryBoundP_bind_zero _ _
    ((qb_ofFnM p (fun i : Fin vp.params.len =>
      chainWith hash (wotsChainAdrs adrs i.val) sig[i.val] (chainStepsCore core msg i.val)
        (vp.params.w - 1 - chainStepsCore core msg i.val)) 0
      (fun i => (qb_chain p core 0 hhash _ _ _ _).mono (Nat.le_of_eq (by simp)))).mono
        (Nat.le_of_eq (by simp)))
    fun tops => hcw _ _ (by simp)

include hhash hcw hnode in
theorem npA_xmssPk (idx : ℕ) (sig : XmssSig vp.params core) (msg : core.Y) (adrs : Adrs) :
    IsQueryBoundP (xmssPkFromSigWith core hash compress nodeHash idx sig msg adrs) p 0 :=
  isQueryBoundP_bind_zero _ _ (npA_wotsPkFromSig p core hhash hcw sig.wots msg _) fun leaf =>
    (qb_climb p (xmssNodeHashWith nodeHash adrs) 0 (fun h i l r => hnode _ l r) idx leaf
      sig.auth.toList).mono (Nat.le_of_eq (by simp))

include hhash hcw hnode hsecret in
theorem npA_signFromPos (recoverFinal : Bool) (pos : LayerPosition vp) :
    ∀ (layers : ℕ) (h : pos.layer.val + layers = vp.params.d) (msg : core.Y),
      IsQueryBoundP (GeneralHypertree.signFromPositionWithSecret core hash compress nodeHash
        secret recoverFinal pos layers h msg) p 0
  | 0, _, _ => by
      rw [GeneralHypertree.signFromPositionWithSecret]
      exact isQueryBoundP_pure _ _ _
  | 1, _, msg => by
      rw [GeneralHypertree.signFromPositionWithSecret]
      refine isQueryBoundP_bind_zero _ _
        (npA_xmssSign p core hhash hcw hnode hsecret msg _ _) fun sig => ?_
      cases recoverFinal
      · exact isQueryBoundP_pure _ _ _
      · exact isQueryBoundP_bind_zero _ _ (npA_xmssPk p core hhash hcw hnode _ sig msg _)
          fun _ => isQueryBoundP_pure _ _ _
  | layers + 2, _, msg => by
      rw [GeneralHypertree.signFromPositionWithSecret]
      exact isQueryBoundP_bind_zero _ _ (npA_xmssSign p core hhash hcw hnode hsecret msg _ _)
        fun sig => isQueryBoundP_bind_zero _ _ (npA_xmssPk p core hhash hcw hnode _ sig msg _)
          fun root => isQueryBoundP_bind_zero _ _
            (npA_signFromPos false _ (layers + 1) _ root) fun _ => isQueryBoundP_pure _ _ _

include hhash hcf hnode in
theorem npA_forsPk (sig : ForsSigCore vp.params core) (md : List Byte) (adrs : Adrs) :
    IsQueryBoundP (forsPkFromSigWith core hash nodeHash compress sig md adrs) p 0 := by
  refine isQueryBoundP_bind_zero _ _ ((qb_ofFnM p _ 0 fun i => ?_).mono (Nat.le_of_eq (by simp)))
    fun roots => hcf _ _ (by simp)
  refine isQueryBoundP_bind_zero _ _ (hhash _ _) fun leaf => ?_
  exact (qb_climb p (forsNodeHashWith nodeHash adrs) 0 (fun h i l r => hnode _ l r)
    (i.val * 2 ^ vp.params.a + forsIdx vp.params md i.val) leaf (sig[i.val]).auth.toList).mono
      (Nat.le_of_eq (by simp))

end Walk

/-! ## The open programs -/

section Open

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable {ι : Type} {gspec : OracleSpec ι}

attribute [local instance] Lazy.openQ

variable (p : ℕ ⊕ (ι ⊕ (SecIdx ⊕ PublicHashQuery prims.PkSeed prims.AdrsKey prims.Y)) → Prop)
  [DecidablePred p] (pkSeed : prims.PkSeed)
  (hsec : ∀ d, ¬ p (.inr (.inr (.inl d))))
  (hF : ∀ key x, ¬ p (thIdx prims ι pkSeed key [x]))
  (hH : ∀ key l r, ¬ p (thIdx prims ι pkSeed key [l, r]))
  (hW : ∀ b xs, xs.length = vp.params.len →
    ¬ p (thIdx prims ι pkSeed (prims.adrsToKey (wotsPkAdrs b)) xs))
  (hR : ∀ b xs, xs.length = vp.params.k →
    ¬ p (thIdx prims ι pkSeed (prims.adrsToKey (forsPkAdrs b)) xs))

include hsec hF hH hW in
/-- Open key generation makes no `p`-query, if `p` holds of no secret read, of no `F`/`H` query,
and of no `T_len` query at a `WOTS_PK` address. -/
theorem npA_openKeygen : IsQueryBoundP (openKeygen prims gspec pkSeed) p 0 :=
  npA_xmssNode p prims.core
    (hash := PublicHash.f prims.core pkSeed) (compress := PublicHash.tl prims.core pkSeed)
    (nodeHash := PublicHash.h prims.core pkSeed) (secret := secQ prims gspec)
    (fun _ _ => (isQueryBoundP_query_iff _ _ _).2 fun h => absurd h (hF _ _))
    (fun _ ys hys => (isQueryBoundP_query_iff _ _ _).2 fun h => absurd h (hW _ _ hys))
    (fun _ _ _ => (isQueryBoundP_query_iff _ _ _).2 fun h => absurd h (hH _ _ _))
    (fun _ => (isQueryBoundP_query_iff _ _ _).2 fun h => absurd h (hsec _)) _ _ _

include hsec hF hH hW hR in
/-- Open signing makes at most `c` `p`-queries, if its `H_msg` query makes at most `c` and `p`
holds of no secret read, no `F`/`H` query and no `T_len`/`T_k` query at a `WOTS_PK`/`FORS_ROOTS`
address. -/
theorem npA_openSign (msg : List Byte) (pkRoot R : prims.Y) (c : ℕ)
    (hm : IsQueryBoundP (PublicHash.hmsg prims.core R pkSeed pkRoot msg :
      OracleComp (OSpec prims gspec) _) p c) :
    IsQueryBoundP (Lazy.openSign prims gspec msg pkSeed pkRoot R) p c := by
  have hf : ∀ (a : Adrs) (y : prims.core.Y), IsQueryBoundP (PublicHash.f prims.core pkSeed a y :
      OracleComp (OSpec prims gspec) prims.Y) p 0 :=
    fun _ _ => (isQueryBoundP_query_iff _ _ _).2 fun h => absurd h (hF _ _)
  have hw : ∀ (b : Adrs) (ys : List prims.core.Y), ys.length = vp.params.len →
      IsQueryBoundP (PublicHash.tl prims.core pkSeed (wotsPkAdrs b) ys :
      OracleComp (OSpec prims gspec) prims.Y) p 0 :=
    fun _ ys hys => (isQueryBoundP_query_iff _ _ _).2 fun h => absurd h (hW _ _ hys)
  have hr : ∀ (b : Adrs) (ys : List prims.core.Y), ys.length = vp.params.k →
      IsQueryBoundP (PublicHash.tl prims.core pkSeed (forsPkAdrs b) ys :
      OracleComp (OSpec prims gspec) prims.Y) p 0 :=
    fun _ ys hys => (isQueryBoundP_query_iff _ _ _).2 fun h => absurd h (hR _ _ hys)
  have hh : ∀ (a : Adrs) (l r : prims.core.Y),
      IsQueryBoundP (PublicHash.h prims.core pkSeed a l r :
      OracleComp (OSpec prims gspec) prims.Y) p 0 :=
    fun _ _ _ => (isQueryBoundP_query_iff _ _ _).2 fun h => absurd h (hH _ _ _)
  have hs : ∀ a : Adrs, IsQueryBoundP (secQ prims gspec a) p 0 :=
    fun _ => (isQueryBoundP_query_iff _ _ _).2 fun h => absurd h (hsec _)
  unfold Lazy.openSign GeneralScheme.signInternalWithSecretRandomizerM
  exact (isQueryBoundP_bind (m := 0) hm fun digest _ =>
    isQueryBoundP_bind_zero _ _ (np_forsSign p prims.core hf hh hs _ _) fun forsSig =>
      isQueryBoundP_bind_zero _ _ (npA_forsPk p prims.core hf hr hh forsSig _ _) fun forsPk =>
        isQueryBoundP_bind_zero _ _ (npA_signFromPos p prims.core hf hw hh hs _ _ _ _ _)
          fun htSig => isQueryBoundP_pure _ _ _).mono (by omega)

end Open

end Ideal.Realize.Itsr

#print axioms Ideal.Realize.Itsr.tblocks_two_ne_cB
#print axioms Ideal.Realize.Itsr.tblocks_ne_cB_of_key9
#print axioms Ideal.Realize.Itsr.key9_wotsPk
#print axioms Ideal.Realize.Itsr.key9_forsPk
#print axioms Ideal.Realize.Itsr.npA_openKeygen
#print axioms Ideal.Realize.Itsr.npA_openSign
