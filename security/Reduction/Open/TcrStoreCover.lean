/-
Work package OPEN, O9: coverage — every `Thash` evaluation of the signing simulation and of the
recomputation of `PK.root` is a call of the key structure (`honestCalls tbl pk`), hence stored by
phase 1 of `bTcrArA n A`; and the resulting unconditional hash count of its second phase.

* writer-monad lemmas (`calls_*`, in the style of the `sub_*` lemmas of `Reduction/TCR.lean`,
  which cover only the verification of the reference signature): the calls of an authentication
  path are calls of the tree root; the calls of a WOTS+ signature are calls of the WOTS+ public
  key; hence XMSS signing ⊆ XMSS root, FORS signing ⊆ FORS public key, hypertree signing ⊆ the
  XMSS roots;
* `emb`: the writer monad as open programs (a call is a hash query, the value is the real one);
  the PINNED open key generation / signature is the image of the writer program
  (`pin_openKeygen_eq`, `pin_openSign_eq`);
* `cover_keygen`, `cover_sign`: the two coverage hypotheses of
  `storeForgeOpen_hashes_of_cover`, for the store produced by phase 1;
* `storeForgeOpen_hashes`: the pinned second phase of `bTcrArA n A` makes at most
  `qs + (1 + verifyHashes vp)` hash queries; `qs + 3929` at SHA2-128s.
-/
import Reduction.Open.TcrStoreCount

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal

namespace Reduction
namespace Open

open TweakableHash

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! ## Writer-monad lemmas: signing stays inside the key structure -/

section Writer

open sub_W PerfectMerkleTree

variable {C : Type}

/-- The calls of an authentication path are calls of the root of the subtree that contains it. -/
theorem calls_authPathM {Y : Type} (leaf : ℕ → sub_W C Y) (node : ℕ → ℕ → Y → Y → sub_W C Y)
    (idx : ℕ) : ∀ z, ∀ c ∈ calls (authPathM leaf node idx z),
      c ∈ calls (merkleRootM leaf node z (idx / 2 ^ z))
  | 0 => fun c hc => absurd hc List.not_mem_nil
  | z + 1 => by
    intro c hc
    have ih := calls_authPathM leaf node idx z
    have hpath : authPathM leaf node idx (z + 1) =
        authPathM leaf node idx z >>= fun path =>
          merkleRootM leaf node z (sibling (idx / 2 ^ z)) >>= fun sr => pure (path ++ [sr]) := rfl
    have hroot : merkleRootM leaf node (z + 1) (idx / 2 ^ (z + 1)) =
        merkleRootM leaf node z (2 * (idx / 2 ^ (z + 1))) >>= fun l =>
          merkleRootM leaf node z (2 * (idx / 2 ^ (z + 1)) + 1) >>= fun r =>
            node (z + 1) (idx / 2 ^ (z + 1)) l r := rfl
    have hdiv : idx / 2 ^ (z + 1) = idx / 2 ^ z / 2 := by
      rw [Nat.pow_succ, Nat.div_div_eq_div_mul]
    rw [hpath] at hc
    rw [hroot]
    by_cases hpar : idx / 2 ^ z % 2 = 0
    · have h2 : 2 * (idx / 2 ^ (z + 1)) = idx / 2 ^ z := by omega
      have hs : sibling (idx / 2 ^ z) = idx / 2 ^ z + 1 := by
        simp only [sibling, hpar, ↓reduceIte]
      rw [hs] at hc
      rw [h2]
      simp only [calls_bind, calls_pure, List.append_nil, List.mem_append] at hc ⊢
      rcases hc with hc | hc
      · exact Or.inl (ih c hc)
      · exact Or.inr (Or.inl hc)
    · have h2 : 2 * (idx / 2 ^ (z + 1)) + 1 = idx / 2 ^ z := by omega
      have hs : sibling (idx / 2 ^ z) = 2 * (idx / 2 ^ (z + 1)) := by
        simp only [sibling, hpar, ↓reduceIte]; omega
      rw [hs] at hc
      rw [h2]
      simp only [calls_bind, calls_pure, List.append_nil, List.mem_append] at hc ⊢
      rcases hc with hc | hc
      · exact Or.inr (Or.inl (ih c hc))
      · exact Or.inl hc

theorem calls_intrinsicAuthPathM {Y : Type} (leaf : ℕ → sub_W C Y)
    (node : ℕ → ℕ → Y → Y → sub_W C Y) (idx z : ℕ) :
    calls (intrinsicAuthPathM leaf node idx z) = calls (authPathM leaf node idx z) := by
  rw [← intrinsicAuthPathM_toList]
  exact (calls_map _ _).symm

variable {p : Params} (core : CorePrimitives p)
  (hash : Adrs → core.Y → sub_W C core.Y) (compress : Adrs → List core.Y → sub_W C core.Y)
  (nodeHash : Adrs → core.Y → core.Y → sub_W C core.Y) (s : Adrs → core.Y)

/-- The calls of a chain prefix are calls of the longer chain. -/
theorem calls_chain_prefix {Y : Type} (hash : Adrs → Y → sub_W C Y) (adrs : Adrs) (x : Y)
    (a n : ℕ) (ha : a ≤ n) :
    ∀ c ∈ calls (chainWith hash adrs x 0 a), c ∈ calls (chainWith hash adrs x 0 n) := by
  have h := chainWith_add hash adrs x 0 a (n - a)
  rw [Nat.add_sub_of_le ha] at h
  rw [h]
  simp only [calls_bind, List.mem_append]
  exact fun c hc => Or.inl hc

/-- The calls of a WOTS+ signature are calls of the WOTS+ public key. -/
theorem calls_wotsSign (msg : core.Y) (adrs : Adrs) :
    ∀ c ∈ calls (wotsSignWithSecret core hash (fun a => pure (s a)) msg adrs),
      c ∈ calls (wotsPkGenWithSecret core hash compress (fun a => pure (s a)) adrs) := by
  intro c hc
  unfold wotsSignWithSecret at hc
  unfold wotsPkGenWithSecret wotsPkGenTopsWithSecret
  simp only [calls_bind, List.mem_append]
  left
  rw [mem_calls_ofFnM] at hc ⊢
  obtain ⟨i, hi⟩ := hc
  refine ⟨i, ?_⟩
  simp only [pure_bind] at hi ⊢
  exact calls_chain_prefix hash _ _ _ _ (chainStepsCore_le core msg i.val) c hi

/-- The calls of an XMSS signature are calls of the XMSS root. -/
theorem calls_xmssSign (msg : core.Y) (adrs : Adrs) (idx : ℕ) (hidx : idx < 2 ^ p.hp) :
    ∀ c ∈ calls (xmssSignWithSecret core hash compress nodeHash (fun a => pure (s a)) msg adrs
        idx),
      c ∈ calls (xmssRootWithSecret core hash compress nodeHash (fun a => pure (s a)) adrs) := by
  intro c hc
  obtain ⟨-, -, ml⟩ := merkle_spec
    (xmssLeafWithSecret core hash compress (fun a => pure (s a)) adrs)
    (xmssNodeHashWith nodeHash adrs) idx p.hp
  have ha := calls_authPathM
    (xmssLeafWithSecret core hash compress (fun a => pure (s a)) adrs)
    (xmssNodeHashWith nodeHash adrs) idx p.hp
  rw [Nat.div_eq_of_lt hidx] at ml ha
  unfold xmssSignWithSecret at hc
  simp only [calls_bind, calls_pure, List.append_nil, List.mem_append] at hc
  rcases hc with hc | hc
  · rw [calls_intrinsicAuthPathM] at hc
    exact ha c hc
  · exact ml c (calls_wotsSign core hash compress s msg _ c hc)

/-- The calls of a FORS signature are calls of the FORS public key. -/
theorem calls_forsSign (md : List Byte) (adrs : Adrs) :
    ∀ c ∈ calls (forsSignWithSecret core hash nodeHash (fun a => pure (s a)) md adrs),
      c ∈ calls (forsPkGenWithSecret core hash nodeHash compress (fun a => pure (s a)) adrs) := by
  intro c hc
  unfold forsSignWithSecret at hc
  unfold forsPkGenWithSecret
  simp only [calls_bind, List.mem_append]
  left
  rw [mem_calls_ofFnM] at hc ⊢
  obtain ⟨i, hi⟩ := hc
  refine ⟨i, ?_⟩
  have ha := calls_authPathM (forsLeafWithSecret core hash (fun a => pure (s a)) adrs)
    (forsNodeHashWith nodeHash adrs) (i.val * 2 ^ p.a + forsIdx p md i.val) p.a
  rw [sub_fors_idx_div] at ha
  simp only [pure_bind, calls_bind, calls_pure, List.append_nil] at hi
  rw [calls_intrinsicAuthPathM] at hi
  exact ha c hi

end Writer

section Hypertree

open sub_W GeneralHypertree

variable {C : Type} {vp : ValidatedParams} (core : CorePrimitives vp.params)
  (hash : Adrs → core.Y → sub_W C core.Y) (compress : Adrs → List core.Y → sub_W C core.Y)
  (nodeHash : Adrs → core.Y → core.Y → sub_W C core.Y) (s : Adrs → core.Y)

/-- Every call of hypertree signing is a call of the root computation of some XMSS tree. -/
theorem calls_signFromPos :
    ∀ (layers : ℕ) (rf : Bool) (pos : LayerPosition vp)
      (h : pos.layer.val + layers = vp.params.d) (msg : core.Y),
      ∀ c ∈ calls (signFromPositionWithSecret core hash compress nodeHash (fun a => pure (s a)) rf
          pos layers h msg),
        ∃ coord : LayerTreeCoord vp, c ∈ calls (xmssRootWithSecret core hash compress nodeHash
          (fun a => pure (s a)) coord.toAdrs)
  | 0, rf, pos, h, msg => fun c hc => absurd hc List.not_mem_nil
  | 1, rf, pos, h, msg => by
    intro c hc
    rw [signFromPositionWithSecret] at hc
    cases rf
    · simp only [Bool.false_eq_true, ↓reduceIte, calls_bind, calls_pure, List.append_nil] at hc
      exact ⟨LayerTreeCoord.ofPosition pos,
        calls_xmssSign core hash compress nodeHash s msg pos.toAdrs pos.leaf.val pos.leaf.isLt c hc⟩
    · simp only [↓reduceIte, calls_bind, calls_pure, List.append_nil, List.mem_append] at hc
      rcases hc with hc | hc
      · exact ⟨LayerTreeCoord.ofPosition pos,
          calls_xmssSign core hash compress nodeHash s msg pos.toAdrs pos.leaf.val pos.leaf.isLt c
            hc⟩
      · exact ⟨LayerTreeCoord.ofPosition pos,
          (sub_xmss_spec core hash compress nodeHash s msg pos.toAdrs pos.leaf.val
            pos.leaf.isLt).2 c hc⟩
  | layers + 2, rf, pos, h, msg => by
    intro c hc
    rw [signFromPositionWithSecret] at hc
    simp only [calls_bind, calls_pure, List.append_nil, List.mem_append] at hc
    rcases hc with hc | hc | hc
    · exact ⟨LayerTreeCoord.ofPosition pos,
        calls_xmssSign core hash compress nodeHash s msg pos.toAdrs pos.leaf.val pos.leaf.isLt c hc⟩
    · exact ⟨LayerTreeCoord.ofPosition pos,
        (sub_xmss_spec core hash compress nodeHash s msg pos.toAdrs pos.leaf.val
          pos.leaf.isLt).2 c hc⟩
    · exact calls_signFromPos (layers + 1) false (pos.next (by omega)) (by simp; omega) _ c hc

end Hypertree

/-! ## Transfer to the pinned open programs -/

section Transfer

open sub_W GeneralHypertree

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]
variable {optRand : PublicKeyCore prims.core → ProbComp prims.Y}
  {pkSeedDist : ProbComp prims.PkSeed}
variable {ι : Type} {gspec : OracleSpec ι}

attribute [local irreducible] arityTargets tcrTargets
attribute [local instance] Lazy.openQ Lazy.closedQ

/-- Issue the hash queries of a call list, in order, ignoring the answers. -/
def issue (pk : prims.PkSeed) :
    List (prims.AdrsKey × List prims.Y) → OracleComp (Lazy.OSpec prims gspec) Unit
  | [] => pure ()
  | c :: l => Resources2.hashQ (gspec := gspec) pk c.1 c.2 >>= fun _ => issue pk l

theorem issue_append (pk : prims.PkSeed) (l l' : List (prims.AdrsKey × List prims.Y)) :
    issue (gspec := gspec) pk (l ++ l') = issue (gspec := gspec) pk l >>= fun _ => issue pk l' := by
  induction l with
  | nil => simp [issue]
  | cons c l ih => simp [issue, ih, bind_assoc]

/-- **The writer monad as open programs**: a writer computation `(value, calls)` becomes the
program that issues the hash queries `calls` (at the seed `pk`) and returns `value`. -/
def emb (pk : prims.PkSeed) :
    sub_W (prims.AdrsKey × List prims.Y) →ᵐ OracleComp (Lazy.OSpec prims gspec) where
  toFun _ x := issue (gspec := gspec) pk x.2 >>= fun _ => pure x.1
  toFun_pure' a := by
    show issue (gspec := gspec) pk [] >>= (fun _ => pure a) = pure a
    simp [issue]
  toFun_bind' x f := by
    show issue (gspec := gspec) pk (x.2 ++ (f x.1).2) >>= (fun _ => pure (f x.1).1) =
      (issue (gspec := gspec) pk x.2 >>= fun _ => pure x.1) >>= fun a =>
        issue (gspec := gspec) pk (f a).2 >>= fun _ => pure (f a).1
    rw [issue_append]
    simp

theorem emb_apply {α : Type} (pk : prims.PkSeed) (x : sub_W (prims.AdrsKey × List prims.Y) α) :
    emb (gspec := gspec) pk x = issue (gspec := gspec) pk (calls x) >>= fun _ => pure (val x) :=
  rfl

/-- A pinned hash query is the image of the writer-monad hash callback. -/
theorem pin_hashQ (tbl : SecretTable vp prims) (pk : prims.PkSeed) (key : prims.AdrsKey)
    (xs : List prims.Y) :
    simulateQ (pinImpl (gspec := gspec) tbl) (Resources2.hashQ (gspec := gspec) pk key xs) =
      emb (gspec := gspec) pk (sub_wTh pk key xs) := by
  rw [emb_apply]
  unfold Resources2.hashQ
  rw [simulateQ_spec_query]
  show (liftM ((Lazy.OSpec prims gspec).query
      (.inr (.inr (.inr (PublicHashQuery.thash pk key xs))))) >>= fun _ =>
        pure (prims.Thash pk key xs)) =
    (Resources2.hashQ (gspec := gspec) pk key xs >>= fun _ => pure ()) >>= fun _ =>
      pure (prims.Thash pk key xs)
  rw [bind_assoc]
  simp only [pure_bind]
  rfl

theorem pin_secQ (tbl : SecretTable vp prims) (a : Adrs) :
    simulateQ (pinImpl (gspec := gspec) tbl) (Lazy.secQ prims gspec a) =
      pure (secretOf vp prims tbl a) := by
  unfold Lazy.secQ
  rw [simulateQ_spec_query]
  rfl

/-- **The pinned open key generation is the image of the writer-monad top-tree root.** -/
theorem pin_openKeygen_eq (tbl : SecretTable vp prims) (pk : prims.PkSeed) :
    simulateQ (pinImpl (gspec := gspec) tbl) (Lazy.openKeygen prims gspec pk) =
      emb (gspec := gspec) pk (rootWithSecret prims.core
        (fun a x => sub_wTh pk (prims.adrsToKey a) [x])
        (fun a xs => sub_wTh pk (prims.adrsToKey a) xs)
        (fun a l r => sub_wTh pk (prims.adrsToKey a) [l, r])
        (fun a => pure (secretOf vp prims tbl a))) := by
  have h1 := rootWithSecret_natural prims.core (simulateQ' (pinImpl (gspec := gspec) tbl))
    (PublicHash.f prims.core pk) (fun a x => emb (gspec := gspec) pk (sub_wTh pk (prims.adrsToKey a) [x]))
    (PublicHash.tl prims.core pk) (fun a xs => emb (gspec := gspec) pk (sub_wTh pk (prims.adrsToKey a) xs))
    (PublicHash.h prims.core pk) (fun a l r => emb (gspec := gspec) pk (sub_wTh pk (prims.adrsToKey a) [l, r]))
    (Lazy.secQ prims gspec) (fun a => pure (secretOf vp prims tbl a))
    (fun a y => pin_hashQ tbl pk _ _) (fun a ys => pin_hashQ tbl pk _ _)
    (fun a l r => pin_hashQ tbl pk _ _) (fun a _ => pin_secQ tbl a)
  have h2 := rootWithSecret_natural prims.core (emb (gspec := gspec) pk)
    (fun a x => sub_wTh pk (prims.adrsToKey a) [x])
    (fun a x => emb (gspec := gspec) pk (sub_wTh pk (prims.adrsToKey a) [x]))
    (fun a xs => sub_wTh pk (prims.adrsToKey a) xs)
    (fun a xs => emb (gspec := gspec) pk (sub_wTh pk (prims.adrsToKey a) xs))
    (fun a l r => sub_wTh pk (prims.adrsToKey a) [l, r])
    (fun a l r => emb (gspec := gspec) pk (sub_wTh pk (prims.adrsToKey a) [l, r]))
    (fun a => pure (secretOf vp prims tbl a)) (fun a => pure (secretOf vp prims tbl a))
    (fun a y => rfl) (fun a ys => rfl) (fun a l r => rfl) (fun a _ => MonadHom.mmap_pure _ _)
  exact h1.trans h2.symm

/-- The writer-monad signing program after the digest: FORS signature, FORS public key from it,
hypertree signature. -/
def wSign (tbl : SecretTable vp prims) (pk : prims.PkSeed) (R : prims.Y)
    (parts : DigestParts vp.params) :
    sub_W (prims.AdrsKey × List prims.Y) (GeneralScheme.SignatureCore vp prims.core) :=
  forsSignWithSecret prims.core
      (fun a x => sub_wTh pk (prims.adrsToKey a) [x])
      (fun a l r => sub_wTh pk (prims.adrsToKey a) [l, r])
      (fun a => pure (secretOf vp prims tbl a)) parts.md.toList parts.forsAdrs >>= fun forsSig =>
    forsPkFromSigWith prims.core
        (fun a x => sub_wTh pk (prims.adrsToKey a) [x])
        (fun a l r => sub_wTh pk (prims.adrsToKey a) [l, r])
        (fun a xs => sub_wTh pk (prims.adrsToKey a) xs)
        forsSig parts.md.toList parts.forsAdrs >>= fun forsPk =>
      GeneralHypertree.signWithSecret prims.core
          (fun a x => sub_wTh pk (prims.adrsToKey a) [x])
          (fun a xs => sub_wTh pk (prims.adrsToKey a) xs)
          (fun a l r => sub_wTh pk (prims.adrsToKey a) [l, r])
          (fun a => pure (secretOf vp prims tbl a)) forsPk parts >>= fun htSig =>
        pure ⟨R, forsSig, htSig⟩

/-- **The pinned open signature is one `H_msg` query followed by the image of the writer-monad
signing program** at the digest `H_msg(R, PK.seed, PK.root, M)`. -/
theorem pin_openSign_eq (tbl : SecretTable vp prims) (m : List Byte) (pk : prims.PkSeed)
    (root R : prims.Y) :
    simulateQ (pinImpl (gspec := gspec) tbl) (Lazy.openSign prims gspec m pk root R) =
      simulateQ (pinImpl (gspec := gspec) tbl)
        (PublicHash.hmsg prims.core R pk root m :
          OracleComp (Lazy.OSpec prims gspec) (Bytes vp.params.m)) >>= fun dg =>
        emb (gspec := gspec) pk (wSign tbl pk R (splitDigest vp.params dg)) := by
  have k1 : ∀ (md : List Byte) (adrs : Adrs),
      simulateQ (pinImpl (gspec := gspec) tbl) (forsSignWithSecretM prims.core
        (Lazy.secQ prims gspec) md pk adrs) =
      emb (gspec := gspec) pk (forsSignWithSecret prims.core
          (fun a x => sub_wTh pk (prims.adrsToKey a) [x])
          (fun a l r => sub_wTh pk (prims.adrsToKey a) [l, r])
          (fun a => pure (secretOf vp prims tbl a)) md adrs) := by
    intro md adrs
    have h1 := forsSignWithSecret_natural prims.core (simulateQ' (pinImpl (gspec := gspec) tbl))
      (PublicHash.f prims.core pk)
      (fun a x => emb (gspec := gspec) pk (sub_wTh pk (prims.adrsToKey a) [x]))
      (PublicHash.h prims.core pk)
      (fun a l r => emb (gspec := gspec) pk (sub_wTh pk (prims.adrsToKey a) [l, r]))
      (Lazy.secQ prims gspec) (fun a => pure (secretOf vp prims tbl a))
      (fun a y => pin_hashQ tbl pk _ _) (fun a l r => pin_hashQ tbl pk _ _)
      (fun a _ => pin_secQ tbl a) md adrs
    have h2 := forsSignWithSecret_natural prims.core (emb (gspec := gspec) pk)
      (fun a x => sub_wTh pk (prims.adrsToKey a) [x])
      (fun a x => emb (gspec := gspec) pk (sub_wTh pk (prims.adrsToKey a) [x]))
      (fun a l r => sub_wTh pk (prims.adrsToKey a) [l, r])
      (fun a l r => emb (gspec := gspec) pk (sub_wTh pk (prims.adrsToKey a) [l, r]))
      (fun a => pure (secretOf vp prims tbl a)) (fun a => pure (secretOf vp prims tbl a))
      (fun a y => rfl) (fun a l r => rfl) (fun a _ => MonadHom.mmap_pure _ _) md adrs
    exact h1.trans h2.symm
  have k2 : ∀ (fs : ForsSigCore vp.params prims.core) (md : List Byte) (adrs : Adrs),
      simulateQ (pinImpl (gspec := gspec) tbl) (forsPkFromSigM prims.core fs md pk adrs) =
      emb (gspec := gspec) pk (forsPkFromSigWith prims.core
            (fun a x => sub_wTh pk (prims.adrsToKey a) [x])
            (fun a l r => sub_wTh pk (prims.adrsToKey a) [l, r])
            (fun a xs => sub_wTh pk (prims.adrsToKey a) xs) fs md adrs) := by
    intro fs md adrs
    have h1 := forsPkFromSigWith_natural (simulateQ' (pinImpl (gspec := gspec) tbl)) prims.core
      (PublicHash.f prims.core pk)
      (fun a x => emb (gspec := gspec) pk (sub_wTh pk (prims.adrsToKey a) [x]))
      (PublicHash.h prims.core pk)
      (fun a l r => emb (gspec := gspec) pk (sub_wTh pk (prims.adrsToKey a) [l, r]))
      (PublicHash.tl prims.core pk)
      (fun a xs => emb (gspec := gspec) pk (sub_wTh pk (prims.adrsToKey a) xs))
      (fun a y => pin_hashQ tbl pk _ _) (fun a l r => pin_hashQ tbl pk _ _)
      (fun a xs => pin_hashQ tbl pk _ _) fs md adrs
    have h2 := forsPkFromSigWith_natural (emb (gspec := gspec) pk) prims.core
      (fun a x => sub_wTh pk (prims.adrsToKey a) [x])
      (fun a x => emb (gspec := gspec) pk (sub_wTh pk (prims.adrsToKey a) [x]))
      (fun a l r => sub_wTh pk (prims.adrsToKey a) [l, r])
      (fun a l r => emb (gspec := gspec) pk (sub_wTh pk (prims.adrsToKey a) [l, r]))
      (fun a xs => sub_wTh pk (prims.adrsToKey a) xs)
      (fun a xs => emb (gspec := gspec) pk (sub_wTh pk (prims.adrsToKey a) xs))
      (fun a y => rfl) (fun a l r => rfl) (fun a xs => rfl) fs md adrs
    exact h1.trans h2.symm
  have k3 : ∀ (m0 : prims.Y) (parts : DigestParts vp.params),
      simulateQ (pinImpl (gspec := gspec) tbl) (GeneralHypertree.signWithSecretM prims.core
        (Lazy.secQ prims gspec) m0 pk parts) =
      emb (gspec := gspec) pk (GeneralHypertree.signWithSecret prims.core
          (fun a x => sub_wTh pk (prims.adrsToKey a) [x])
          (fun a xs => sub_wTh pk (prims.adrsToKey a) xs)
          (fun a l r => sub_wTh pk (prims.adrsToKey a) [l, r])
          (fun a => pure (secretOf vp prims tbl a)) m0 parts) := by
    intro m0 parts
    have h1 := GeneralHypertree.signWithSecret_natural prims.core
      (simulateQ' (pinImpl (gspec := gspec) tbl))
      (PublicHash.f prims.core pk)
      (fun a x => emb (gspec := gspec) pk (sub_wTh pk (prims.adrsToKey a) [x]))
      (PublicHash.tl prims.core pk)
      (fun a xs => emb (gspec := gspec) pk (sub_wTh pk (prims.adrsToKey a) xs))
      (PublicHash.h prims.core pk)
      (fun a l r => emb (gspec := gspec) pk (sub_wTh pk (prims.adrsToKey a) [l, r]))
      (Lazy.secQ prims gspec) (fun a => pure (secretOf vp prims tbl a))
      (fun a y => pin_hashQ tbl pk _ _) (fun a xs => pin_hashQ tbl pk _ _)
      (fun a l r => pin_hashQ tbl pk _ _) (fun a _ => pin_secQ tbl a) m0 parts
    have h2 := GeneralHypertree.signWithSecret_natural prims.core (emb (gspec := gspec) pk)
      (fun a x => sub_wTh pk (prims.adrsToKey a) [x])
      (fun a x => emb (gspec := gspec) pk (sub_wTh pk (prims.adrsToKey a) [x]))
      (fun a xs => sub_wTh pk (prims.adrsToKey a) xs)
      (fun a xs => emb (gspec := gspec) pk (sub_wTh pk (prims.adrsToKey a) xs))
      (fun a l r => sub_wTh pk (prims.adrsToKey a) [l, r])
      (fun a l r => emb (gspec := gspec) pk (sub_wTh pk (prims.adrsToKey a) [l, r]))
      (fun a => pure (secretOf vp prims tbl a)) (fun a => pure (secretOf vp prims tbl a))
      (fun a y => rfl) (fun a xs => rfl) (fun a l r => rfl)
      (fun a _ => MonadHom.mmap_pure _ _) m0 parts
    exact h1.trans h2.symm
  unfold Lazy.openSign GeneralScheme.signInternalWithSecretRandomizerM wSign
  simp only [simulateQ_bind, simulateQ_pure, MonadHom.mmap_bind, MonadHom.mmap_pure, k1, k2, k3]

/-! ## Coverage -/

omit [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey]
  [Inhabited prims.Y] in
/-- **Every `Thash` call of the signing simulation is a call of the key structure** (any digest,
any randomizer): FORS signing and the FORS public key lie in the FORS instance of the digest's
bottom position, hypertree signing in the XMSS trees. -/
theorem wSign_subset (tbl : SecretTable vp prims) (pk : prims.PkSeed) (R : prims.Y)
    (parts : DigestParts vp.params) :
    ∀ c ∈ calls (wSign tbl pk R parts), c ∈ honestCalls tbl pk := by
  intro c hc
  rw [sub_honestCalls_eq]
  unfold structureVia
  unfold wSign at hc
  simp only [sub_W.calls_bind, List.mem_append, sub_W.mem_calls_forM, List.append_nil,
    sub_W.calls_pure] at hc ⊢
  rcases hc with hc | hc | hc
  · left
    refine ⟨BottomPosition.ofDigestParts vp parts, mem_allBottomPositions vp _, ?_⟩
    rw [BottomPosition.forsAdrs_ofDigestParts]
    exact calls_forsSign prims.core _ _ _ _ _ _ c hc
  · left
    refine ⟨BottomPosition.ofDigestParts vp parts, mem_allBottomPositions vp _, ?_⟩
    rw [BottomPosition.forsAdrs_ofDigestParts]
    exact (sub_fors_spec prims.core _ _ _ _ _ _).2 c hc
  · right
    obtain ⟨coord, hcoord⟩ := calls_signFromPos prims.core _ _ _ _ _ _ _ _ _ c hc
    exact ⟨coord, mem_allXmssTrees vp coord, hcoord⟩

omit [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey]
  [Inhabited prims.Y] in
/-- **Every `Thash` call of the recomputation of `PK.root` is a call of the key structure** (the
top XMSS tree). -/
theorem wRoot_subset (tbl : SecretTable vp prims) (pk : prims.PkSeed) :
    ∀ c ∈ calls (rootWithSecret prims.core
        (fun a x => sub_wTh pk (prims.adrsToKey a) [x])
        (fun a xs => sub_wTh pk (prims.adrsToKey a) xs)
        (fun a l r => sub_wTh pk (prims.adrsToKey a) [l, r])
        (fun a => pure (secretOf vp prims tbl a))), c ∈ honestCalls tbl pk := by
  intro c hc
  rw [sub_honestCalls_eq]
  unfold structureVia
  simp only [sub_W.calls_bind, List.mem_append, sub_W.mem_calls_forM, List.append_nil,
    sub_W.calls_pure]
  right
  exact ⟨LayerTreeCoord.top vp, mem_allXmssTrees vp _, hc⟩

/-- A stored pair is found by the lookup. -/
theorem lookup_ann_isSome (pk : prims.PkSeed) (L : List (prims.AdrsKey × List prims.Y))
    (c : prims.AdrsKey × List prims.Y) (hc : c ∈ L) :
    ((ann (thashList vp prims pkSeedDist) pk L).lookup c).isSome = true := by
  induction L with
  | nil => exact absurd hc List.not_mem_nil
  | cons a L ih =>
    show (List.lookup c ((a, prims.Thash pk a.1 a.2) ::
      ann (thashList vp prims pkSeedDist) pk L)).isSome = true
    rw [List.lookup_cons]
    by_cases hca : c = a
    · subst hca
      simp
    · have hb : (c == a) = false := by simpa using hca
      rw [hb]
      exact ih ((List.mem_cons.1 hc).resolve_left hca)

/-- The image of a writer computation whose calls are all in the store makes no hash query
outside the store. -/
theorem emb_NH {α : Type} (pk : prims.PkSeed) (S : Store prims)
    (x : sub_W (prims.AdrsKey × List prims.Y) α)
    (h : ∀ c ∈ calls x, (S.lookup c).isSome = true) :
    IsQueryBoundP (emb (gspec := gspec) pk x) (NH pk S) 0 := by
  rw [emb_apply]
  refine Lazy.qb_bind (NH pk S) (m := 0) ?_ fun _ => isQueryBoundP_pure _ _ _
  generalize calls x = l at h
  induction l with
  | nil => exact isQueryBoundP_pure _ _ _
  | cons c l ih =>
    refine Lazy.qb_bind (NH pk S) (m := 0) ?_ fun _ => ih fun c' hc' =>
      h c' (List.mem_cons_of_mem _ hc')
    refine (isQueryBoundP_query_iff _ _ _).2 fun hnh => ?_
    have h1 := hnh.2
    have h2 := h c List.mem_cons_self
    simp [hitB, h2] at h1

/-- **Coverage, key generation**: with the store of phase 1, the pinned recomputation of
`PK.root` makes NO hash query outside the store. -/
theorem cover_keygen (tbl : SecretTable vp prims) (pk : prims.PkSeed) :
    IsQueryBoundP (simulateQ (pinImpl (gspec := gspec) tbl) (Lazy.openKeygen prims gspec pk))
      (NH pk (ann (thashList vp prims pkSeedDist) pk (honestCalls tbl pk))) 0 := by
  rw [pin_openKeygen_eq]
  exact emb_NH pk _ _ fun c hc => lookup_ann_isSome pk _ c (wRoot_subset tbl pk c hc)

/-- **Coverage, signing**: with the store of phase 1, a pinned simulated signature (any message,
any `PK.root` value, any randomizer) makes at most ONE hash query outside the store — its
`H_msg` query. -/
theorem cover_sign (tbl : SecretTable vp prims) (pk : prims.PkSeed) (m : List Byte)
    (root R : prims.Y) :
    IsQueryBoundP (simulateQ (pinImpl (gspec := gspec) tbl)
        (Lazy.openSign prims gspec m pk root R))
      (NH pk (ann (thashList vp prims pkSeedDist) pk (honestCalls tbl pk))) 1 := by
  rw [pin_openSign_eq]
  refine Lazy.qb_bind _ (m := 0) (pin_mono tbl _ _ _
    ((isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos)) fun dg => ?_
  exact emb_NH pk _ _ fun c hc => lookup_ann_isSome pk _ c (wSign_subset tbl pk R _ c hc)

/-! ## The unconditional count -/

/-- **Own hash evaluations of phase 2 of `bTcrArA n A`.**  At the state `(tbl, (L, S))` that
phase 1 hands over at the seed `pk` (`bTcrArA_choose_run`: `L = honestCalls tbl pk`, `S` = the
entries of `L` with their oracle answers), the open second phase `storeForgeOpen A L S pk`, run
with the secret reads answered from `tbl` and the hash queries answered by the real hash
functions (`pinImpl tbl`; this is the adversary's actual execution, `pinImpl_tbl`), makes at
most

`qs + (1 + verifyHashes vp)`,  `verifyHashes vp = k·(1+a) + 1 + d·(len·(w-1) + 1 + h')`

hash queries: one `H_msg` per signing query, one `H_msg` for the forgery and the `Thash`
evaluations of verifying the forgery.  Everything else — `PK.root`, all FORS / WOTS+ / XMSS
recomputations of the signing simulation, the comparison values of the collision test — is a
lookup in the stored phase-1 answers. -/
theorem storeForgeOpen_hashes (A : Forger vp prims optRand pkSeedDist) (qs : ℕ)
    (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs)
    (tbl : SecretTable vp prims) (pk : prims.PkSeed) :
    IsQueryBoundP (simulateQ (pinImpl (gspec := gspec) tbl)
        (storeForgeOpen (gspec := gspec) A (honestCalls tbl pk)
          (ann (thashList vp prims pkSeedDist) pk (honestCalls tbl pk)) pk))
      (fun t => Lazy.kind t = .hash) (qs + (1 + Resources2.verifyHashes vp)) :=
  storeForgeOpen_hashes_of_cover A qs hA tbl _ _ pk (sound_ann pk _)
    (fun c hc => lookup_ann_isSome pk _ c hc) (cover_keygen tbl pk)
    (fun m root R => cover_sign tbl pk m root R)

set_option linter.constructorNameAsVariable false in
/-- **The count holds at every state phase 1 can hand over**: every outcome of phase 1 in the
tight-cap class game at the seed `pk` is a state `(tbl, (L, S))` at which the pinned open second
phase makes at most `qs + (1 + verifyHashes vp)` hash queries (for every game spec). -/
theorem bTcrArA_phase2_hashes (hS : Structural vp prims) (n : ℕ)
    (A : Forger vp prims optRand pkSeedDist) (qs : ℕ)
    (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs) (pk : prims.PkSeed) :
    ∀ z ∈ support ((simulateQ (SM_DT_TCR_oracles (thashArityProblemT vp prims pkSeedDist n) pk)
        (bTcrArA n A).choose).run ([], [])),
      ∃ (tbl : SecretTable vp prims) (L : List (prims.AdrsKey × List prims.Y)) (S : Store prims),
        z.1 = (tbl, (L, S)) ∧ Sound pk S ∧
        ∀ {ι : Type} (gspec : OracleSpec ι),
          IsQueryBoundP (simulateQ (pinImpl (gspec := gspec) tbl)
            (storeForgeOpen (gspec := gspec) A L S pk))
            (fun t => Lazy.kind t = .hash) (qs + (1 + Resources2.verifyHashes vp)) := by
  intro z hz
  rw [bTcrArA_choose_run hS n A pk] at hz
  obtain ⟨tbl, rfl⟩ := exists_of_mem_support_map _ _ z hz
  exact ⟨tbl, _, _, rfl, sound_ann pk _, fun gspec => storeForgeOpen_hashes A qs hA tbl pk⟩

end Transfer

end Open
end Reduction

/-! ## SLH-DSA-SHA2-128s -/

namespace Reduction
namespace Open

/-- Phase 2 of `bTcrArA n A` at SHA2-128s: at most `qs + 3929` own hash evaluations
(`bTcrArM n A`: `269824 + qs·2007385 + 7857`). -/
theorem storeForgeOpen_hashes_128s {ι : Type} {gspec : OracleSpec ι}
    (optRand : PublicKeyCore Link.prims.core → ProbComp Link.prims.Y)
    (pkSeedDist : ProbComp Link.prims.PkSeed)
    (A : Forger Link.vp Link.prims optRand pkSeedDist) (qs : ℕ)
    (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs)
    (tbl : SecretTable Link.vp Link.prims) (pk : Link.prims.PkSeed) :
    IsQueryBoundP (simulateQ (pinImpl (gspec := gspec) tbl)
        (storeForgeOpen (gspec := gspec) A (honestCalls tbl pk)
          (ann (thashList Link.vp Link.prims pkSeedDist) pk (honestCalls tbl pk)) pk))
      (fun t => Lazy.kind t = .hash) (qs + 3929) := by
  have h := storeForgeOpen_hashes (gspec := gspec) A qs hA tbl pk
  rwa [Resources2.verifyHashes_128s] at h

end Open

#print axioms Open.calls_authPathM
#print axioms Open.calls_signFromPos
#print axioms Open.pin_openKeygen_eq
#print axioms Open.pin_openSign_eq
#print axioms Open.wSign_subset
#print axioms Open.wRoot_subset
#print axioms Open.cover_keygen
#print axioms Open.cover_sign
#print axioms Open.storeForgeOpen_hashes
#print axioms Open.bTcrArA_phase2_hashes
#print axioms Open.storeForgeOpen_hashes_128s

end Reduction
