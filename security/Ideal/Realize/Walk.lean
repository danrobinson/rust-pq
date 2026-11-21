import Reduction.TcrMemo
import Ideal.Realize.Chain

/-!
# Which hash calls the SLH-DSA structure walks make (generic part of the realisers)

The counting lemmas of `Reduction/Lazy/Open.lean` (`qb_xmssNode`, `qb_forsPk`, …) bound the
number of queries of the callback-parametric programs for callbacks bounded at EVERY input.
Here the same programs are shown to make NO query satisfying a predicate `p`, under the weaker
hypothesis that the `T_ℓ` callback makes no `p`-query on inputs of `len` or `k` values (the only
lengths at which the programs call it: a WOTS+ public key compresses `len` chain ends, a FORS
public key `k` roots).  Consequences, for the open programs of the reductions:

* `np_openKeygen`, `np_openSign`: open key generation / signing make no `p`-query if `p` holds
  of no secret read and of no `Thash` query on `1`, `2`, `len` or `k` values (`OkLen`) (and, for
  signing, not of the `H_msg` query of the signed message);
* `np_verifyFree`: every hash call of verification is on `1`, `2`, `len` or `k` values;
* `np_collO_run`: the memoised verification `collO` against a stored list `L`;
* `np_structureVia`: the key-structure walk of the first phase.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security

namespace Ideal.Realize

open Reduction Reduction.Lazy

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- The input lengths of the tweakable-hash calls of SLH-DSA: `F` (1), `H` (2), `T_len`, `T_k`. -/
def OkLen (vp : ValidatedParams) {α : Type} (xs : List α) : Prop :=
  xs.length = 1 ∨ xs.length = 2 ∨ xs.length = vp.params.len ∨ xs.length = vp.params.k

instance (vp : ValidatedParams) {α : Type} (xs : List α) : Decidable (OkLen vp xs) := by
  unfold OkLen; infer_instance

section Walk

variable {vp : ValidatedParams} {κ' : Type} {spec : OracleSpec κ'} (p : κ' → Prop) [DecidablePred p]
variable (core : CorePrimitives vp.params)
  {hash : Adrs → core.Y → OracleComp spec core.Y}
  {compress : Adrs → List core.Y → OracleComp spec core.Y}
  {nodeHash : Adrs → core.Y → core.Y → OracleComp spec core.Y}
  {secret : Adrs → OracleComp spec core.Y}

variable (hhash : ∀ a y, IsQueryBoundP (hash a y) p 0)
  (hcompress : ∀ a ys, (ys.length = vp.params.len ∨ ys.length = vp.params.k) →
    IsQueryBoundP (compress a ys) p 0)
  (hnode : ∀ a l r, IsQueryBoundP (nodeHash a l r) p 0)
  (hsecret : ∀ a, IsQueryBoundP (secret a) p 0)

theorem np_forM {α : Type} (l : List α) (f : α → OracleComp spec PUnit)
    (h : ∀ a, IsQueryBoundP (f a) p 0) : IsQueryBoundP (l.forM f) p 0 := by
  induction l with
  | nil => exact isQueryBoundP_pure _ _ _
  | cons a l ih =>
    show IsQueryBoundP (f a >>= fun _ => l.forM f) p 0
    exact isQueryBoundP_bind_zero _ _ (h a) fun _ => ih

include hhash hsecret in
theorem np_wotsTops (adrs : Adrs) :
    IsQueryBoundP (wotsPkGenTopsWithSecret core hash secret adrs) p 0 :=
  (qb_wotsTops p core 0 0 hhash hsecret adrs).mono (Nat.le_of_eq (by simp [wotsB]))

include hhash hsecret in
theorem np_wotsSign (msg : core.Y) (adrs : Adrs) :
    IsQueryBoundP (wotsSignWithSecret core hash secret msg adrs) p 0 :=
  (qb_wotsSign p core 0 0 hhash hsecret msg adrs).mono (Nat.le_of_eq (by simp [wotsB]))

include hhash hcompress hsecret in
theorem np_wotsPkGen (adrs : Adrs) :
    IsQueryBoundP (wotsPkGenWithSecret core hash compress secret adrs) p 0 :=
  isQueryBoundP_bind_zero _ _ (np_wotsTops p core hhash hsecret adrs) fun tops =>
    hcompress _ _ (Or.inl (by simp))

include hhash hcompress hnode hsecret in
theorem np_xmssNode (adrs : Adrs) (z t : ℕ) :
    IsQueryBoundP (xmssNodeWithSecret core hash compress nodeHash secret adrs z t) p 0 :=
  (qb_merkleRoot p (xmssLeafWithSecret core hash compress secret adrs)
    (xmssNodeHashWith nodeHash adrs) 0 0 z t
    (fun i => np_wotsPkGen p core hhash hcompress hsecret _)
    (fun h i l r => hnode _ l r)).mono (Nat.le_of_eq (merkleB_zero z))

include hhash hcompress hnode hsecret in
theorem np_xmssSign (msg : core.Y) (adrs : Adrs) (idx : ℕ) :
    IsQueryBoundP (xmssSignWithSecret core hash compress nodeHash secret msg adrs idx) p 0 := by
  have h := (qb_authPath p (xmssLeafWithSecret core hash compress secret adrs)
    (xmssNodeHashWith nodeHash adrs) 0 0 idx vp.params.hp
    (fun i => np_wotsPkGen p core hhash hcompress hsecret _)
    (fun h i l r => hnode _ l r)).mono (Nat.le_of_eq (authB_zero _))
  exact isQueryBoundP_bind_zero _ _ h fun path =>
    isQueryBoundP_bind_zero _ _ (np_wotsSign p core hhash hsecret msg _) fun sig =>
      isQueryBoundP_pure _ _ _

include hhash hcompress in
theorem np_wotsPkFromSig (sig : WotsSig vp.params core) (msg : core.Y) (adrs : Adrs) :
    IsQueryBoundP (wotsPkFromSigWith core hash compress sig msg adrs) p 0 :=
  isQueryBoundP_bind_zero _ _
    ((qb_ofFnM p (fun i : Fin vp.params.len =>
      chainWith hash (wotsChainAdrs adrs i.val) sig[i.val] (chainStepsCore core msg i.val)
        (vp.params.w - 1 - chainStepsCore core msg i.val)) 0
      (fun i => (qb_chain p core 0 hhash _ _ _ _).mono (Nat.le_of_eq (by simp)))).mono
        (Nat.le_of_eq (by simp)))
    fun tops => hcompress _ _ (Or.inl (by simp))

include hhash hcompress hnode in
theorem np_xmssPk (idx : ℕ) (sig : XmssSig vp.params core) (msg : core.Y) (adrs : Adrs) :
    IsQueryBoundP (xmssPkFromSigWith core hash compress nodeHash idx sig msg adrs) p 0 :=
  isQueryBoundP_bind_zero _ _ (np_wotsPkFromSig p core hhash hcompress sig.wots msg _) fun leaf =>
    (qb_climb p (xmssNodeHashWith nodeHash adrs) 0 (fun h i l r => hnode _ l r) idx leaf
      sig.auth.toList).mono (Nat.le_of_eq (by simp))

include hhash hcompress hnode hsecret in
theorem np_signFromPos (recoverFinal : Bool) (pos : LayerPosition vp) :
    ∀ (layers : ℕ) (h : pos.layer.val + layers = vp.params.d) (msg : core.Y),
      IsQueryBoundP (GeneralHypertree.signFromPositionWithSecret core hash compress nodeHash
        secret recoverFinal pos layers h msg) p 0
  | 0, _, _ => by
      rw [GeneralHypertree.signFromPositionWithSecret]
      exact isQueryBoundP_pure _ _ _
  | 1, _, msg => by
      rw [GeneralHypertree.signFromPositionWithSecret]
      refine isQueryBoundP_bind_zero _ _
        (np_xmssSign p core hhash hcompress hnode hsecret msg _ _) fun sig => ?_
      cases recoverFinal
      · exact isQueryBoundP_pure _ _ _
      · exact isQueryBoundP_bind_zero _ _ (np_xmssPk p core hhash hcompress hnode _ sig msg _)
          fun _ => isQueryBoundP_pure _ _ _
  | layers + 2, _, msg => by
      rw [GeneralHypertree.signFromPositionWithSecret]
      exact isQueryBoundP_bind_zero _ _ (np_xmssSign p core hhash hcompress hnode hsecret msg _ _)
        fun sig => isQueryBoundP_bind_zero _ _ (np_xmssPk p core hhash hcompress hnode _ sig msg _)
          fun root => isQueryBoundP_bind_zero _ _
            (np_signFromPos false _ (layers + 1) _ root) fun _ => isQueryBoundP_pure _ _ _

include hhash hnode hsecret in
theorem np_forsSign (md : List Byte) (adrs : Adrs) :
    IsQueryBoundP (forsSignWithSecret core hash nodeHash secret md adrs) p 0 :=
  (qb_forsSign p core 0 0 0 hhash hnode hsecret md adrs).mono
    (Nat.le_of_eq (by simp [authB_zero]))

include hhash hcompress hnode in
theorem np_forsPk (sig : ForsSigCore vp.params core) (md : List Byte) (adrs : Adrs) :
    IsQueryBoundP (forsPkFromSigWith core hash nodeHash compress sig md adrs) p 0 := by
  refine isQueryBoundP_bind_zero _ _ ((qb_ofFnM p _ 0 fun i => ?_).mono (Nat.le_of_eq (by simp)))
    fun roots => hcompress _ _ (Or.inr (by simp))
  refine isQueryBoundP_bind_zero _ _ (hhash _ _) fun leaf => ?_
  exact (qb_climb p (forsNodeHashWith nodeHash adrs) 0 (fun h i l r => hnode _ l r)
    (i.val * 2 ^ vp.params.a + forsIdx vp.params md i.val) leaf (sig[i.val]).auth.toList).mono
      (Nat.le_of_eq (by simp))

include hhash hcompress hnode hsecret in
theorem np_forsPkGen (adrs : Adrs) :
    IsQueryBoundP (forsPkGenWithSecret core hash nodeHash compress secret adrs) p 0 := by
  refine isQueryBoundP_bind_zero _ _ ((qb_ofFnM p _ 0 fun i => ?_).mono (Nat.le_of_eq (by simp)))
    fun roots => hcompress _ _ (Or.inr (by simp))
  exact (qb_merkleRoot p (forsLeafWithSecret core hash secret adrs)
    (forsNodeHashWith nodeHash adrs) 0 0 vp.params.a i.val
    (fun j => isQueryBoundP_bind_zero _ _ (hsecret _) fun x => hhash _ x)
    (fun h i l r => hnode _ l r)).mono (Nat.le_of_eq (merkleB_zero _))

include hhash hcompress hnode in
theorem np_recover (pk : core.PkSeed) :
    ∀ (layers : ℕ) (pos : LayerPosition vp) (h : pos.layer.val + layers = vp.params.d)
      (msg : core.Y) (sigs : Vector (XmssSig vp.params core) layers),
      IsQueryBoundP (GeneralHypertree.recoverFromPositionWith vp core hash compress nodeHash pk
        pos layers h msg sigs) p 0
  | 0, pos, h, msg, sigs => by
      rw [GeneralHypertree.recoverFromPositionWith]
      exact isQueryBoundP_pure _ _ _
  | 1, pos, h, msg, sigs => by
      rw [GeneralHypertree.recoverFromPositionWith]
      exact np_xmssPk p core hhash hcompress hnode _ _ _ _
  | layers + 2, pos, h, msg, sigs => by
      rw [GeneralHypertree.recoverFromPositionWith]
      exact isQueryBoundP_bind_zero _ _ (np_xmssPk p core hhash hcompress hnode _ _ _ _)
        fun root => np_recover pk (layers + 1) _ _ _ _

end Walk

/-! ## The open programs -/

section Open

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable {ι : Type} {gspec : OracleSpec ι}

attribute [local instance] Lazy.openQ

/-- The index of a `Thash` query of an open program. -/
abbrev thIdx (prims : Primitives vp.params) (ι : Type) (pk : prims.PkSeed) (key : prims.AdrsKey)
    (xs : List prims.Y) :
    ℕ ⊕ (ι ⊕ (SecIdx ⊕ PublicHashQuery prims.PkSeed prims.AdrsKey prims.Y)) :=
  .inr (.inr (.inr (PublicHashQuery.thash pk key xs)))

/-- The index of an `H_msg` query of an open program. -/
abbrev hmIdx (prims : Primitives vp.params) (ι : Type) (R : prims.Y) (pk : prims.PkSeed)
    (root : prims.Y) (m : List Byte) :
    ℕ ⊕ (ι ⊕ (SecIdx ⊕ PublicHashQuery prims.PkSeed prims.AdrsKey prims.Y)) :=
  .inr (.inr (.inr (PublicHashQuery.hmsg R pk root m)))

variable (p : ℕ ⊕ (ι ⊕ (SecIdx ⊕ PublicHashQuery prims.PkSeed prims.AdrsKey prims.Y)) → Prop)
  [DecidablePred p]

/-- Open key generation makes no `p`-query, if `p` holds of no secret read and of no `Thash`
query on `1`, `2`, `len` or `k` values. -/
theorem np_openKeygen (pkSeed : prims.PkSeed) (hsec : ∀ d, ¬ p (.inr (.inr (.inl d))))
    (hth : ∀ key xs, OkLen vp xs → ¬ p (thIdx prims ι pkSeed key xs)) :
    IsQueryBoundP (openKeygen prims gspec pkSeed) p 0 :=
  np_xmssNode p prims.core
    (hash := PublicHash.f prims.core pkSeed) (compress := PublicHash.tl prims.core pkSeed)
    (nodeHash := PublicHash.h prims.core pkSeed) (secret := secQ prims gspec)
    (fun _ _ => (isQueryBoundP_query_iff _ _ _).2 fun h =>
      absurd h (hth _ _ (Or.inl rfl)))
    (fun _ ys hys => (isQueryBoundP_query_iff _ _ _).2 fun h =>
      absurd h (hth _ _ (Or.inr (Or.inr hys))))
    (fun _ _ _ => (isQueryBoundP_query_iff _ _ _).2 fun h =>
      absurd h (hth _ _ (Or.inr (Or.inl rfl))))
    (fun _ => (isQueryBoundP_query_iff _ _ _).2 fun h => absurd h (hsec _)) _ _ _

/-- Open signing of `msg` makes no `p`-query, if `p` holds of no secret read, of no `Thash`
query on `1`, `2`, `len` or `k` values, and not of the `H_msg` query of `msg`. -/
theorem np_openSign (msg : List Byte) (pkSeed : prims.PkSeed) (pkRoot R : prims.Y)
    (hsec : ∀ d, ¬ p (.inr (.inr (.inl d))))
    (hth : ∀ key xs, OkLen vp xs → ¬ p (thIdx prims ι pkSeed key xs))
    (hm : ¬ p (hmIdx prims ι R pkSeed pkRoot msg)) :
    IsQueryBoundP (Lazy.openSign prims gspec msg pkSeed pkRoot R) p 0 := by
  have hf : ∀ (a : Adrs) (y : prims.core.Y), IsQueryBoundP (PublicHash.f prims.core pkSeed a y :
      OracleComp (OSpec prims gspec) prims.Y) p 0 :=
    fun _ _ => (isQueryBoundP_query_iff _ _ _).2 fun h => absurd h (hth _ _ (Or.inl rfl))
  have htl : ∀ (a : Adrs) (ys : List prims.core.Y),
      (ys.length = vp.params.len ∨ ys.length = vp.params.k) →
      IsQueryBoundP (PublicHash.tl prims.core pkSeed a ys :
      OracleComp (OSpec prims gspec) prims.Y) p 0 :=
    fun _ ys hys => (isQueryBoundP_query_iff _ _ _).2 fun h =>
      absurd h (hth _ _ (Or.inr (Or.inr hys)))
  have hh : ∀ (a : Adrs) (l r : prims.core.Y),
      IsQueryBoundP (PublicHash.h prims.core pkSeed a l r :
      OracleComp (OSpec prims gspec) prims.Y) p 0 :=
    fun _ _ _ => (isQueryBoundP_query_iff _ _ _).2 fun h =>
      absurd h (hth _ _ (Or.inr (Or.inl rfl)))
  have hs : ∀ a : Adrs, IsQueryBoundP (secQ prims gspec a) p 0 :=
    fun _ => (isQueryBoundP_query_iff _ _ _).2 fun h => absurd h (hsec _)
  have hmq : IsQueryBoundP (PublicHash.hmsg prims.core R pkSeed pkRoot msg :
      OracleComp (OSpec prims gspec) _) p 0 :=
    (isQueryBoundP_query_iff _ _ _).2 fun h => absurd h hm
  unfold Lazy.openSign GeneralScheme.signInternalWithSecretRandomizerM
  exact isQueryBoundP_bind_zero _ _ hmq fun digest =>
    isQueryBoundP_bind_zero _ _ (np_forsSign p prims.core hf hh hs _ _) fun forsSig =>
      isQueryBoundP_bind_zero _ _ (np_forsPk p prims.core hf htl hh forsSig _ _) fun forsPk =>
        isQueryBoundP_bind_zero _ _ (np_signFromPos p prims.core hf htl hh hs _ _ _ _ _)
          fun htSig => isQueryBoundP_pure _ _ _

end Open

/-! ## Verification -/

section Verify

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [DecidableEq prims.Y] [DecidableEq prims.AdrsKey]
variable {ι : Type} {gspec : OracleSpec ι}

/-- **Every hash call of the free verification program is on `1`, `2`, `len` or `k` values**:
it makes no query satisfying a predicate that fails on such calls. -/
theorem np_verifyFree (p : prims.AdrsKey × List prims.Y → Prop) [DecidablePred p]
    (hp : ∀ key xs, OkLen vp xs → ¬ p (key, xs))
    (pkSeed : prims.PkSeed) (parts : DigestParts vp.params)
    (sig : GeneralScheme.SignatureCore vp prims.core) :
    IsQueryBoundP (Resources2.verifyFree pkSeed parts sig) p 0 := by
  have hq : ∀ (key : prims.AdrsKey) (xs : List prims.Y), OkLen vp xs →
      IsQueryBoundP (Resources2.thQ prims key xs) p 0 :=
    fun key xs h => (isQueryBoundP_query_iff _ _ _).2 fun h' => absurd h' (hp key xs h)
  unfold Resources2.verifyFree
  exact isQueryBoundP_bind_zero _ _
    (np_forsPk p prims.core (fun a y => hq _ _ (Or.inl rfl))
      (fun a ys hys => hq _ _ (Or.inr (Or.inr hys)))
      (fun a l r => hq _ _ (Or.inr (Or.inl rfl))) _ _ _) fun forsPk =>
    np_recover p prims.core (fun a y => hq _ _ (Or.inl rfl))
      (fun a ys hys => hq _ _ (Or.inr (Or.inr hys)))
      (fun a l r => hq _ _ (Or.inr (Or.inl rfl))) pkSeed vp.params.d _ _ _ _

variable (p : ℕ ⊕ (ι ⊕ (SecIdx ⊕ PublicHashQuery prims.PkSeed prims.AdrsKey prims.Y)) → Prop)
  [DecidablePred p]

/-- One step of the memoised verification makes no `p`-query, if `p` holds neither of the `Thash`
query of the call nor of the `Thash` query of any stored entry. -/
theorem np_collO_step (pk : prims.PkSeed) (L : List (prims.AdrsKey × List prims.Y))
    (t : prims.AdrsKey × List prims.Y) (r : Option (ℕ × List prims.Y))
    (ht : ¬ p (thIdx prims ι pk t.1 t.2))
    (hL : ∀ q ∈ L, ¬ p (thIdx prims ι pk q.1 q.2)) :
    IsQueryBoundP ((Resources2.collO (gspec := gspec) pk L t).run r) p 0 := by
  have hq : ∀ (key : prims.AdrsKey) (xs : List prims.Y), ¬ p (thIdx prims ι pk key xs) →
      IsQueryBoundP (Resources2.hashQ (gspec := gspec) pk key xs) p 0 :=
    fun _ _ h => (isQueryBoundP_query_iff _ _ _).2 fun h' => absurd h' h
  unfold Resources2.collO
  simp only [StateT.run_mk]
  refine isQueryBoundP_bind_zero _ _ (hq _ _ ht) fun y => ?_
  have hmem : ∀ q, L[L.findIdx fun q => decide (q.1 = t.1)]? = some q → q ∈ L :=
    fun q h => List.mem_of_getElem? h
  generalize L[L.findIdx fun q => decide (q.1 = t.1)]? = o at hmem ⊢
  rcases o with _ | q
  · exact isQueryBoundP_pure _ _ _
  · have hqL : q ∈ L := hmem q rfl
    show IsQueryBoundP (if t.2 ≠ q.2 then _ else _) _ _
    by_cases hne : t.2 ≠ q.2
    · rw [ite_eq_left hne]
      exact isQueryBoundP_bind_zero _ _ (hq _ _ (hL q hqL)) fun y' => isQueryBoundP_pure _ _ _
    · rw [ite_eq_right hne]
      exact isQueryBoundP_pure _ _ _

/-- **The memoised verification makes no `p`-query**, if `p` holds of no `Thash` query on `1`,
`2`, `len` or `k` values and of no `Thash` query of a stored entry. -/
theorem np_collO_run (pk : prims.PkSeed) (L : List (prims.AdrsKey × List prims.Y))
    (hth : ∀ key xs, OkLen vp xs → ¬ p (thIdx prims ι pk key xs))
    (hL : ∀ q ∈ L, ¬ p (thIdx prims ι pk q.1 q.2))
    (parts : DigestParts vp.params) (sig : GeneralScheme.SignatureCore vp prims.core)
    (r : Option (ℕ × List prims.Y)) :
    IsQueryBoundP ((simulateQ (Resources2.collO (gspec := gspec) pk L)
      (Resources2.verifyFree pk parts sig)).run r) p 0 := by
  exact qb_simulateQ_run_zero (p := fun t : prims.AdrsKey × List prims.Y => ¬ OkLen vp t.2)
    (fun t ht s => np_collO_step p pk L t s (hth _ _ (not_not.mp ht)) hL)
    (np_verifyFree _ (fun key xs h => not_not.mpr h) pk parts sig) r

end Verify

/-! ## The key-structure walk of the first phase -/

section Structure

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable {κ' : Type} {spec : OracleSpec κ'} (p : κ' → Prop) [DecidablePred p]

/-- The key-structure walk makes no `p`-query, if its hash callback makes none on `1`, `2`, `len`
or `k` values and the secret callback makes none. -/
theorem np_structureVia {th : prims.AdrsKey → List prims.Y → OracleComp spec prims.Y}
    {secret : Adrs → OracleComp spec prims.Y}
    (hth : ∀ key xs, OkLen vp xs → IsQueryBoundP (th key xs) p 0)
    (hsec : ∀ a, IsQueryBoundP (secret a) p 0) :
    IsQueryBoundP (structureVia (vp := vp) (prims := prims) th secret) p 0 := by
  unfold structureVia
  refine isQueryBoundP_bind_zero _ _ (np_forM p _ _ fun bp => ?_) fun _ =>
    np_forM p _ _ fun c => ?_
  · exact isQueryBoundP_bind_zero _ _
      (np_forsPkGen p prims.core (fun a y => hth _ _ (Or.inl rfl))
        (fun a ys hys => hth _ _ (Or.inr (Or.inr hys)))
        (fun a l r => hth _ _ (Or.inr (Or.inl rfl))) hsec _) fun _ => isQueryBoundP_pure _ _ _
  · exact isQueryBoundP_bind_zero _ _
      (np_xmssNode p prims.core (fun a y => hth _ _ (Or.inl rfl))
        (fun a ys hys => hth _ _ (Or.inr (Or.inr hys)))
        (fun a l r => hth _ _ (Or.inr (Or.inl rfl))) hsec _ _ _) fun _ => isQueryBoundP_pure _ _ _

end Structure

end Ideal.Realize

#print axioms Ideal.Realize.np_openKeygen
#print axioms Ideal.Realize.np_openSign
#print axioms Ideal.Realize.np_verifyFree
#print axioms Ideal.Realize.np_collO_run
#print axioms Ideal.Realize.np_structureVia
