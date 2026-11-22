import Ideal.Realize.PrfReal
import Ideal.Inst.SkPrf128Fine

/-!
# Key-block-shaped compression queries of the `PRF` realisers

`Ideal.skPrf_bound_128s_marked` charges `2^-128` only to compression queries whose block is a
key block `blk128 a k` (`a` a secret-key address).  Here the realisers `AprfS`, `AprfE` of
`PrfReal.lean` are shown to make at most

`qPrfM qf qs ℓ = qf + 9·nLong qs + (qs+1)·hmsgCost ℓ + qs·prfMsgCost ℓ`

such queries (`chainA_mark`, `AprfS_mark`, `AprfE_mark`): the forger's own queries, the blocks
after the first of the `T_len`/`T_k` evaluations (at most `9` each; `nLong qs` evaluations), and
every block of the `H_msg` and `PRF_msg` evaluations.  The other hash evaluations of the
reduction (`F`, `H`, `≈ 2·10^6` per signature) contribute none:

* the seed block `sb128 pk` is never a key block (`sb128_ne_blk128`);
* the first block of `Thash(pk, key, xs)` begins with `key` (`key_of_tblocks_eq_blk128`), and
  every tweakable-hash evaluation of the SLH-DSA programs is at an address of type `≤ 4`, whose
  key differs from the key of every secret-key address (VCVio's address discipline
  `GeneralScheme.*_pred` with `Concrete.keySeparated_sha2Primitives`): `openKeygenP_sk`,
  `openSignP_sk`, `verify_sk`;
* `F`, `H` have no block after the first (`(30 + 16·n)/64 = 0` for `n ≤ 2`).
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security

namespace Ideal.Realize.Prf

open Reduction Reduction.Open
open Ideal.Realize.Msg (codec₀ optRand₀ Rd mainC cEmb thB okLen_le hashN isTh isHm longH
  PortBounds harnP_bound)

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! ## Predicates -/

/-- The address key of a secret-key address. -/
def skKey (key : Bytes 22) : Prop := ∃ a : SkAd, key = SLHDSA.Concrete.sha2AdrsKey a.val

/-- A compression query (`CSpec` index) at a key block. -/
def markC : ℕ ⊕ (St × Blk) → Prop
  | .inr q => ∃ a k, q.2 = blk128 a k
  | .inl _ => False

noncomputable instance : DecidablePred markC := fun _ => Classical.propDecidable _

/-- A `Thash` query on more than two values. -/
def longTh {P K Y : Type} : PublicHashQuery P K Y → Bool
  | .thash _ _ xs => decide (2 < xs.length)
  | _ => false

/-- A `Thash` query (of the reference bundle) at the key of a secret-key address. -/
def skTh : PublicHashQuery Rd.PkSeed Rd.AdrsKey Rd.Y → Prop
  | .thash _ key _ => skKey key
  | _ => False

noncomputable instance : DecidablePred skTh := fun _ => Classical.propDecidable _

section Classes

variable {D P K Y M : Type}

/-- Long `Thash` queries. -/
abbrev qLong : ℕ ⊕ (((St × Blk) ⊕ D) ⊕ (PublicHashQuery P K Y ⊕ M)) → Prop :=
  liftQ False (fun _ => False) (fun q => longTh q = true) (fun _ => False)

/-- `Thash` queries at secret-key addresses. -/
abbrev qSk {M : Type} : ℕ ⊕ (((St × Blk) ⊕ D) ⊕ (PublicHashQuery Rd.PkSeed Rd.AdrsKey Rd.Y ⊕ M)) →
    Prop :=
  liftQ False (fun _ => False) skTh (fun _ => False)

end Classes

/-! ## One `Thash` evaluation -/

theorem cq_mark0 (q : St × Blk) (h : ¬ markC (.inr q)) : IsQueryBoundP (cq q) markC 0 :=
  (isQueryBoundP_query_iff _ _ _).2 fun h' => absurd h' h

theorem foldQ_mark (c : St) (bs : List Blk) : IsQueryBoundP (foldQ c bs) markC bs.length :=
  IsQueryBoundP.of_imp (fun t ht => by
    rcases t with n | q
    · exact ht.elim
    · rfl) (foldQ_bound c bs)

/-- **A `Thash` evaluation at a key that is not a secret-key key makes at most as many marked
compression queries as it has blocks after the first.** -/
theorem thashC_mark (pk : Bytes 16) (key : Bytes 22) (xs : List (Bytes 16)) (hk : ¬ skKey key) :
    IsQueryBoundP (thashC pk key xs) markC ((30 + 16 * xs.length) / 64) := by
  unfold thashC
  refine (isQueryBoundP_bind (n := 0) (cq_mark0 _ fun ⟨a, k, h⟩ => sb128_ne_blk128 pk a k h)
    fun cv _ => isQueryBoundP_bind (n := 0) (cq_mark0 _ fun ⟨a, k, h⟩ =>
      hk ⟨a, key_of_tblocks_eq_blk128 h⟩) fun c _ =>
      isQueryBoundP_bind (m := 0) (foldQ_mark c _) fun c' _ => isQueryBoundP_pure _ _ _).mono ?_
  rw [tblocks_snd_length]
  omega

/-- Embedded `CSpec` programs: marked queries are those of the program. -/
theorem cEmb_mark {α : Type} (oa : OracleComp CSpec α) (n : ℕ) (h : IsQueryBoundP oa markC n) :
    IsQueryBoundP (simulateQ (cEmb (X := Dsk →ₒ Bytes 16)) oa) (Prf.markQ blk128) n := by
  refine IsQueryBoundP.simulateQ_of_step h (fun t ht => ?_) (fun t ht => ?_)
  · rcases t with m | c
    · exact (isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos
    · exact (isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos
  · rcases t with m | c
    · exact (isQueryBoundP_query_iff _ _ _).2 fun h' => h'.elim
    · exact (isQueryBoundP_query_iff _ _ _).2 fun h' => absurd h' ht

theorem cEmb_markR {α : Type} (oa : OracleComp CSpec α) (n : ℕ)
    (h : IsQueryBoundP oa (fun i => i.isRight = true) n) :
    IsQueryBoundP (simulateQ (cEmb (X := Dsk →ₒ Bytes 16)) oa) (Prf.markQ blk128) n :=
  cEmb_mark oa n (IsQueryBoundP.of_imp (p := markC) (fun t ht => by
    rcases t with m | q
    · exact ht.elim
    · rfl) h)

/-! ## The chain interpretation -/

section Chain

variable (P : OracleComp (QSpec Rd Dsk) Bool) {qf qs ℓ nL : ℕ}

/-- **Marked compression queries of `chainA P`.** -/
theorem chainA_mark (hport : IsQueryBoundP P qPort qf) (hlong : IsQueryBoundP P qLong nL)
    (hhm : IsQueryBoundP P qHm (qs + 1)) (hpm : IsQueryBoundP P qPm qs)
    (hbad : IsQueryBoundP P (qBad thB ℓ) 0) (hsk : IsQueryBoundP P qSk 0) :
    IsQueryBoundP (chainA P) (Prf.markQ blk128)
      (qf * 1 + nL * 9 + (qs + 1) * hmsgCost ℓ + qs * prfMsgCost ℓ) := by
  unfold chainA
  have h0 : IsQueryBoundP P (fun t => qBad thB ℓ t ∨ qSk t) 0 := (hbad.or hsk).mono le_rfl
  refine qb_simulateQ_classes4 (p₀ := fun t => qBad thB ℓ t ∨ qSk t) (p₁ := qPort) (p₂ := qLong)
    (p₃ := qHm) (p₄ := qPm) 1 9 (hmsgCost ℓ) (prfMsgCost ℓ) (fun t ht => ?_)
    h0 hport hlong hhm hpm
  rcases t with n | (q | d) | (h | ⟨k, r, M⟩)
  · exact (isQueryBoundP_query_iff _ _ _).2 fun h => h.elim
  · exact (isQueryBoundP_query_iff _ _ _).2 fun _ => by simp [liftQ]
  · exact (isQueryBoundP_query_iff _ _ _).2 fun h => h.elim
  · rcases h with ⟨pk, a, xs⟩ | ⟨R, pk, root, M⟩
    · have hx : xs.length ≤ thB := by
        simp only [liftQ, longH, decide_eq_true_eq, not_lt, not_or] at ht
        exact ht.1
      have hk : ¬ skKey a := by
        simp only [liftQ, not_or] at ht
        exact ht.2
      have hx' : List.length (α := Bytes 16) xs ≤ 35 := hx
      refine (cEmb_mark _ _ (thashC_mark pk a xs hk)).mono ?_
      simp only [liftQ, longTh, isHm, ite_false, Bool.false_eq_true, add_zero, zero_add]
      by_cases hl : 2 < List.length (α := Bytes 16) xs
      · simp only [show 2 < List.length (α := Rd.Y) xs from hl, decide_true, ite_true]
        omega
      · simp only [show ¬ 2 < List.length (α := Rd.Y) xs from hl, decide_false,
          Bool.false_eq_true, ite_false]
        omega
    · have hM : M.length ≤ ℓ := by
        simp only [liftQ, longH, decide_eq_true_eq, not_lt, not_or] at ht
        exact ht.1
      refine (cEmb_markR _ _ (hmsgC_bound R pk root M)).mono ?_
      simpa [liftQ, longTh, isHm] using hmsgCost_mono hM
  · have hM : M.length ≤ ℓ := by
      simp only [liftQ, not_lt, not_or] at ht
      exact ht.1
    refine (cEmb_markR _ _ (prfMsgC_bound k r M)).mono ?_
    simpa [liftQ] using prfMsgCost_mono hM

end Chain

/-! ## Long `Thash` evaluations of the SLH-DSA programs -/

section Walk

variable {vp : ValidatedParams} {κ' : Type} {spec : OracleSpec κ'} (p : κ' → Prop) [DecidablePred p]
variable (core : CorePrimitives vp.params)
  {hash : Adrs → core.Y → OracleComp spec core.Y}
  {compress : Adrs → List core.Y → OracleComp spec core.Y}
  {nodeHash : Adrs → core.Y → core.Y → OracleComp spec core.Y}
  (cF cT cH : ℕ)
  (hhash : ∀ a y, IsQueryBoundP (hash a y) p cF)
  (hcompress : ∀ a ys, IsQueryBoundP (compress a ys) p cT)
  (hnode : ∀ a l r, IsQueryBoundP (nodeHash a l r) p cH)

include hhash hcompress hnode in
/-- Hypertree root recovery: `layers` XMSS root recoveries. -/
theorem qb_recover (pk : core.PkSeed) :
    ∀ (layers : ℕ) (pos : LayerPosition vp) (h : pos.layer.val + layers = vp.params.d)
      (msg : core.Y) (sigs : Vector (XmssSig vp.params core) layers),
      IsQueryBoundP (GeneralHypertree.recoverFromPositionWith vp core hash compress nodeHash pk
        pos layers h msg sigs) p (layers * Lazy.xmssPkB vp cF cT cH)
  | 0, pos, h, msg, sigs => by
      rw [GeneralHypertree.recoverFromPositionWith]
      exact isQueryBoundP_pure _ _ _
  | 1, pos, h, msg, sigs => by
      rw [GeneralHypertree.recoverFromPositionWith]
      exact (Lazy.qb_xmssPk p core cF cT cH hhash hcompress hnode _ _ _ _).mono (by omega)
  | layers + 2, pos, h, msg, sigs => by
      rw [GeneralHypertree.recoverFromPositionWith]
      exact (Lazy.qb_bind p (Lazy.qb_xmssPk p core cF cT cH hhash hcompress hnode _ _ _ _)
        fun root => qb_recover pk (layers + 1) _ _ _ _).mono (le_of_eq (by ring))

end Walk

section VerifyLong

variable {vp : ValidatedParams} (core : CorePrimitives vp.params) [DecidableEq core.Y]
variable (ph : PublicHashQuery core.PkSeed core.AdrsKey core.Y → Prop) [DecidablePred ph]

/-- Verification makes at most `1 + d` `ph`-queries, if `ph` holds of no `Thash` query on one or
two values and of no `H_msg` query. -/
theorem verifyM_long (msg : List Byte) (sig : GeneralScheme.SignatureCore vp core)
    (pk : PublicKeyCore core)
    (h1 : ∀ key xs, xs.length ≤ 2 → ¬ ph (.thash pk.pkSeed key xs))
    (hm : ∀ R pkSeed root M, ¬ ph (.hmsg R pkSeed root M)) :
    IsQueryBoundP (GeneralScheme.verifyInternalM vp core msg sig pk :
      OracleComp (publicHashSpec core) Bool) ph
      (vp.params.k * (0 + vp.params.a * 0) + 1 + vp.params.d * Lazy.xmssPkB vp 0 1 0) := by
  have hf : ∀ (a : Adrs) (y : core.Y), IsQueryBoundP (PublicHash.f core pk.pkSeed a y :
      OracleComp (publicHashSpec core) core.Y) ph 0 :=
    fun _ _ => (isQueryBoundP_query_iff _ _ _).2 fun h => absurd h (h1 _ _ (by simp))
  have htl : ∀ (a : Adrs) (ys : List core.Y),
      IsQueryBoundP (PublicHash.tl core pk.pkSeed a ys :
      OracleComp (publicHashSpec core) core.Y) ph 1 :=
    fun _ _ => (isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos
  have hh : ∀ (a : Adrs) (l r : core.Y),
      IsQueryBoundP (PublicHash.h core pk.pkSeed a l r :
      OracleComp (publicHashSpec core) core.Y) ph 0 :=
    fun _ _ _ => (isQueryBoundP_query_iff _ _ _).2 fun h => absurd h (h1 _ _ (by simp))
  have hm' : IsQueryBoundP (PublicHash.hmsg core sig.randomness pk.pkSeed pk.pkRoot msg :
      OracleComp (publicHashSpec core) _) ph 0 :=
    (isQueryBoundP_query_iff _ _ _).2 fun h => absurd h (hm _ _ _ _)
  unfold GeneralScheme.verifyInternalM GeneralHypertree.verifyM GeneralHypertree.pkFromSigM
    GeneralHypertree.recoverFromPositionM forsPkFromSigM
  refine (Lazy.qb_bind ph hm' fun digest =>
    Lazy.qb_bind ph (Lazy.qb_forsPk ph core 0 1 0 hf htl hh _ _ _) fun forsPk =>
      Lazy.qb_bind ph (m := 0) (qb_recover ph core 0 1 0 hf htl hh pk.pkSeed vp.params.d _ _ _ _)
        fun root => isQueryBoundP_pure _ _ _).mono (by omega)

end VerifyLong

/-! ## The open walks of the port programs -/

section OpenWalks

variable {vp : ValidatedParams} {prims : Primitives vp.params}

attribute [local instance] Reduction.Open.openQ

variable (p : ℕ ⊕ ((prims.PkSeed × Adrs) ⊕
    (PublicHashQuery prims.PkSeed prims.AdrsKey prims.Y ⊕ (prims.SkPrf × prims.Y × List Byte))) →
      Prop) [DecidablePred p]

/-- Open key generation: one `T_len` per leaf. -/
theorem openKeygenP_w (pkSeed : prims.PkSeed) (hsec : ∀ a, ¬ p (.inr (.inl (pkSeed, a))))
    (h1 : ∀ key xs, xs.length ≤ 2 → ¬ p (.inr (.inr (.inl (.thash pkSeed key xs))))) :
    IsQueryBoundP (openKeygenP prims pkSeed) p (Lazy.merkleB (Lazy.wotsB vp 0 0 + 1) 0 vp.params.hp) :=
  Lazy.qb_xmssNode p prims.core 0 1 0 0
    (hash := PublicHash.f prims.core pkSeed) (compress := PublicHash.tl prims.core pkSeed)
    (nodeHash := PublicHash.h prims.core pkSeed) (secret := fun a => gameQ prims (pkSeed, a))
    (fun _ _ => (isQueryBoundP_query_iff _ _ _).2 fun h => absurd h (h1 _ _ (by simp)))
    (fun _ _ => (isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos)
    (fun _ _ _ => (isQueryBoundP_query_iff _ _ _).2 fun h => absurd h (h1 _ _ (by simp)))
    (fun _ => (isQueryBoundP_query_iff _ _ _).2 fun h => absurd h (hsec _)) _ _ _

/-- The budget of one open signature for long `Thash` queries. -/
def signLongB (vp : ValidatedParams) : ℕ :=
  0 + vp.params.k * (0 + Lazy.authB (0 + 0) 0 vp.params.a) +
    (vp.params.k * (0 + vp.params.a * 0) + 1) +
    vp.params.d * (Lazy.xmssSignB vp 0 1 0 0 + Lazy.xmssPkB vp 0 1 0)

/-- Open signing: one `T_k` and, per layer, one `T_len` per leaf. -/
theorem openSignCoreP_w (msg : List Byte) (pkSeed : prims.PkSeed) (pkRoot R : prims.Y)
    (hsec : ∀ a, ¬ p (.inr (.inl (pkSeed, a))))
    (h1 : ∀ key xs, xs.length ≤ 2 → ¬ p (.inr (.inr (.inl (.thash pkSeed key xs)))))
    (hm : ∀ R pkSeed root M, ¬ p (.inr (.inr (.inl (.hmsg R pkSeed root M))))) :
    IsQueryBoundP (openSignCoreP prims msg pkSeed pkRoot R) p (signLongB vp) := by
  have hf : ∀ (a : Adrs) (y : prims.core.Y), IsQueryBoundP (PublicHash.f prims.core pkSeed a y :
      OracleComp (PSpec prims (prims.PkSeed × Adrs)) prims.Y) p 0 :=
    fun _ _ => (isQueryBoundP_query_iff _ _ _).2 fun h => absurd h (h1 _ _ (by simp))
  have htl : ∀ (a : Adrs) (ys : List prims.core.Y),
      IsQueryBoundP (PublicHash.tl prims.core pkSeed a ys :
      OracleComp (PSpec prims (prims.PkSeed × Adrs)) prims.Y) p 1 :=
    fun _ _ => (isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos
  have hh : ∀ (a : Adrs) (l r : prims.core.Y),
      IsQueryBoundP (PublicHash.h prims.core pkSeed a l r :
      OracleComp (PSpec prims (prims.PkSeed × Adrs)) prims.Y) p 0 :=
    fun _ _ _ => (isQueryBoundP_query_iff _ _ _).2 fun h => absurd h (h1 _ _ (by simp))
  have hs : ∀ a : Adrs, IsQueryBoundP (gameQ prims (pkSeed, a)) p 0 :=
    fun _ => (isQueryBoundP_query_iff _ _ _).2 fun h => absurd h (hsec _)
  have hm' : IsQueryBoundP (PublicHash.hmsg prims.core R pkSeed pkRoot msg :
      OracleComp (PSpec prims (prims.PkSeed × Adrs)) _) p 0 :=
    (isQueryBoundP_query_iff _ _ _).2 fun h => absurd h (hm _ _ _ _)
  unfold openSignCoreP GeneralScheme.signInternalWithSecretRandomizerM
  exact (Lazy.qb_bind p hm' fun digest =>
    Lazy.qb_bind p (Lazy.qb_forsSign p prims.core 0 0 0 hf hh hs _ _) fun forsSig =>
      Lazy.qb_bind p (Lazy.qb_forsPk p prims.core 0 1 0 hf htl hh forsSig _ _) fun forsPk =>
        Lazy.qb_bind p (m := 0) (Lazy.qb_signFromPos p prims.core 0 1 0 0 hf htl hh hs _ _ _ _ _)
          fun htSig => isQueryBoundP_pure _ _ _).mono (by unfold signLongB; omega)

end OpenWalks

theorem keygenLong_128s :
    Lazy.merkleB (Lazy.wotsB Link.vp 0 0 + 1) 0 Link.vp.params.hp = 512 := by decide

theorem signLongB_128s : signLongB Link.vp = 3585 := by decide

theorem verifyLong_128s :
    Link.vp.params.k * (0 + Link.vp.params.a * 0) + 1 + Link.vp.params.d *
      Lazy.xmssPkB Link.vp 0 1 0 = 8 := by decide

/-! ## Key separation -/

/-- The key of an address of type at most `4` is not the key of a secret-key address. -/
theorem not_skKey (a : Adrs) (ha : a.type ≤ 4) : ¬ skKey (SLHDSA.Concrete.sha2AdrsKey a) :=
  fun ⟨b, hb⟩ => Concrete.keySeparated_sha2Primitives Link.vp.params b.val a b.2.2.1 ha hb.symm

/-! ## The port programs of the `PRF` realisers -/

section Programs

attribute [local instance] Reduction.Open.openQ

variable (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) (pkSeedDist : ProbComp (Bytes 16))

theorem hu_long : ∀ n : ℕ, ¬ (qLong : QIdx Rd (D₀ Rd) → Prop) (.inl n) := by
  intro n; simp [liftQ]

theorem hu_sk : ∀ n : ℕ, ¬ (qSk : QIdx Rd (D₀ Rd) → Prop) (.inl n) := by
  intro n; simp [liftQ]

/-- Long `Thash` queries of open key generation. -/
theorem keygen_long (pkSeed : Rd.PkSeed) :
    IsQueryBoundP (simulateQ embQ (openKeygenP Rd pkSeed)) (qLong : QIdx Rd (D₀ Rd) → Prop) 512 :=
  embQ_bound _ _ _ ((openKeygenP_w (fun t => (qLong : QIdx Rd (D₀ Rd) → Prop) (embIdx t)) pkSeed
    (fun a => by simp [liftQ, embIdx])
    (fun key xs hx => by simp [liftQ, embIdx, longTh]; omega)).mono keygenLong_128s.le)

/-- Long `Thash` queries of one open signature. -/
theorem sign_long (pk : PublicKeyCore Rd.core) (skPrf : Rd.SkPrf) (m : List Byte) :
    IsQueryBoundP (simulateQ embQ (openSignP (optRand₀ oR) pk skPrf m))
      (qLong : QIdx Rd (D₀ Rd) → Prop) 3585 :=
  (embSign_bound (optRand₀ oR) qLong hu_long pk skPrf m 0 3585
    (fun a => (isQueryBoundP_query_iff _ _ _).2 fun h => by simp [liftQ, embIdx] at h)
    (fun R => (openSignCoreP_w (fun t => (qLong : QIdx Rd (D₀ Rd) → Prop) (embIdx t)) m _ _ R
      (fun a => by simp [liftQ, embIdx])
      (fun key xs hx => by simp [liftQ, embIdx, longTh]; omega)
      (fun R pkSeed root M => by simp [liftQ, embIdx, longTh])).mono
        signLongB_128s.le)).mono (by omega)

theorem verify_long (pk : PublicKeyCore Rd.core) (msg : List Byte)
    (sig : GeneralScheme.SignatureCore Link.vp Rd.core) :
    IsQueryBoundP (GeneralScheme.verifyInternalM Link.vp Rd.core msg sig pk :
      OracleComp (publicHashSpec Rd.core) Bool)
      (fun q => (qLong : QIdx Rd (D₀ Rd) → Prop) (.inr (.inr (.inl q)))) 8 :=
  (verifyM_long Rd.core _ msg sig pk (fun key xs hx => by simp [liftQ, longTh]; omega)
    (fun R pkSeed root M => by simp [liftQ, longTh])).mono verifyLong_128s.le

/-- `Thash` queries at secret-key keys of open key generation: none. -/
theorem keygen_sk (pkSeed : Rd.PkSeed) :
    IsQueryBoundP (simulateQ embQ (openKeygenP Rd pkSeed)) (qSk : QIdx Rd (D₀ Rd) → Prop) 0 :=
  embQ_bound _ _ _ (GeneralScheme.keygenInternalWithSecretM_pred
    (fun {α} (oa : OracleComp (PSpec Rd (D₀ Rd)) α) =>
      IsQueryBoundP oa (fun t => (qSk : QIdx Rd (D₀ Rd) → Prop) (embIdx t)) 0)
    (fun x => isQueryBoundP_pure _ _ _) (fun oa ob h h' => isQueryBoundP_bind_zero oa ob h h')
    Rd.core (fun a _ => (isQueryBoundP_query_iff _ _ _).2 fun h => by simp [liftQ, embIdx] at h)
    pkSeed (fun a ha xs => (isQueryBoundP_query_iff _ _ _).2 fun h => (not_skKey a ha h).elim))

/-- `Thash` queries at secret-key keys of one open signature: none. -/
theorem sign_sk (pk : PublicKeyCore Rd.core) (skPrf : Rd.SkPrf) (m : List Byte) :
    IsQueryBoundP (simulateQ embQ (openSignP (optRand₀ oR) pk skPrf m))
      (qSk : QIdx Rd (D₀ Rd) → Prop) 0 :=
  (embSign_bound (optRand₀ oR) qSk hu_sk pk skPrf m 0 0
    (fun a => (isQueryBoundP_query_iff _ _ _).2 fun h => by simp [liftQ, embIdx] at h)
    (fun R => GeneralScheme.signInternalWithSecretRandomizerM_pred
      (fun {α} (oa : OracleComp (PSpec Rd (D₀ Rd)) α) =>
        IsQueryBoundP oa (fun t => (qSk : QIdx Rd (D₀ Rd) → Prop) (embIdx t)) 0)
      (fun x => isQueryBoundP_pure _ _ _) (fun oa ob h h' => isQueryBoundP_bind_zero oa ob h h')
      Rd.core (fun a _ => (isQueryBoundP_query_iff _ _ _).2 fun h => by simp [liftQ, embIdx] at h)
      m _ _ R (fun a ha xs => (isQueryBoundP_query_iff _ _ _).2 fun h => (not_skKey a ha h).elim)
      ((isQueryBoundP_query_iff _ _ _).2 fun h => by simp [liftQ, embIdx, skTh] at h))).mono
        (by omega)

theorem verify_sk (pk : PublicKeyCore Rd.core) (msg : List Byte)
    (sig : GeneralScheme.SignatureCore Link.vp Rd.core) :
    IsQueryBoundP (GeneralScheme.verifyInternalM Link.vp Rd.core msg sig pk :
      OracleComp (publicHashSpec Rd.core) Bool)
      (fun q => (qSk : QIdx Rd (D₀ Rd) → Prop) (.inr (.inr (.inl q)))) 0 :=
  GeneralScheme.verifyInternalM_pred
    (fun {α} (oa : OracleComp (publicHashSpec Rd.core) α) =>
      IsQueryBoundP oa (fun q => (qSk : QIdx Rd (D₀ Rd) → Prop) (.inr (.inr (.inl q)))) 0)
    (fun x => isQueryBoundP_pure _ _ _) (fun oa ob h h' => isQueryBoundP_bind_zero oa ob h h')
    Rd.core msg sig pk (fun a ha xs => (isQueryBoundP_query_iff _ _ _).2 fun h => (not_skKey a ha h).elim)
    ((isQueryBoundP_query_iff _ _ _).2 fun h => by simp [liftQ, skTh] at h)

variable (S : ForgerI) {qf qs ℓ : ℕ}

/-- **Long `Thash` queries of the SUF port program.** -/
theorem PprfS_long (hF : PortBounds (mainC S) qf qs ℓ) :
    IsQueryBoundP (PprfS S oR pkSeedDist) qLong (512 + (qf * 0 + qs * 3585) + 8) := by
  refine restrictP_bound _ False (fun _ => False) (fun _ => False) (fun q => longTh q = true)
    (fun _ => False) (fun _ _ _ h => h.elim) _ _ ?_
  exact bPrfWOpenP_bound (optRand₀ oR) pkSeedDist qLong sufCheckOpen (mainC S) qf qs ℓ 512 3585 0 8
    hF hu_long keygen_long (fun pk skPrf m _ => sign_long oR pk skPrf m)
    (fun q => (portQ_bound _ q).mono (by simp [liftQ]))
    (fun pk f log _ => embHash_bound _ _ 8
      ((isQueryBoundP_bind (m := 0) (verify_long pk f.1 f.2) fun _ _ =>
        isQueryBoundP_pure _ _ _).mono (by omega)))

/-- **Long `Thash` queries of the EUF port program.** -/
theorem PprfE_long (hF : PortBounds (mainC S) qf qs ℓ) :
    IsQueryBoundP (PprfE S oR pkSeedDist) qLong (512 + (qf * 0 + qs * 3585) + 8) := by
  refine restrictP_bound _ False (fun _ => False) (fun _ => False) (fun q => longTh q = true)
    (fun _ => False) (fun _ _ _ h => h.elim) _ _ ?_
  exact bPrfOpenP_bound (optRand₀ oR) pkSeedDist qLong (mainC S) qf qs ℓ 512 3585 0 8
    hF hu_long keygen_long (fun pk skPrf m _ => sign_long oR pk skPrf m)
    (fun q => (portQ_bound _ q).mono (by simp [liftQ]))
    (fun pk msg sig _ => embHash_bound _ _ 8 (verify_long pk msg sig))

/-- **No `Thash` query of the SUF port program is at a secret-key key.** -/
theorem PprfS_sk (hF : PortBounds (mainC S) qf qs ℓ) :
    IsQueryBoundP (PprfS S oR pkSeedDist) qSk 0 := by
  refine restrictP_bound _ False (fun _ => False) (fun _ => False) skTh
    (fun _ => False) (fun _ _ _ h => h.elim) _ _ ?_
  exact (bPrfWOpenP_bound (optRand₀ oR) pkSeedDist qSk sufCheckOpen (mainC S) qf qs ℓ 0 0 0 0
    hF hu_sk keygen_sk (fun pk skPrf m _ => sign_sk oR pk skPrf m)
    (fun q => (portQ_bound _ q).mono (by simp [liftQ]))
    (fun pk f log _ => embHash_bound _ _ 0
      ((isQueryBoundP_bind (m := 0) (verify_sk pk f.1 f.2) fun _ _ =>
        isQueryBoundP_pure _ _ _).mono (by omega)))).mono (by omega)

/-- **No `Thash` query of the EUF port program is at a secret-key key.** -/
theorem PprfE_sk (hF : PortBounds (mainC S) qf qs ℓ) :
    IsQueryBoundP (PprfE S oR pkSeedDist) qSk 0 := by
  refine restrictP_bound _ False (fun _ => False) (fun _ => False) skTh
    (fun _ => False) (fun _ _ _ h => h.elim) _ _ ?_
  exact (bPrfOpenP_bound (optRand₀ oR) pkSeedDist qSk (mainC S) qf qs ℓ 0 0 0 0
    hF hu_sk keygen_sk (fun pk skPrf m _ => sign_sk oR pk skPrf m)
    (fun q => (portQ_bound _ q).mono (by simp [liftQ]))
    (fun pk msg sig _ => embHash_bound _ _ 0 (verify_sk pk msg sig))).mono (by omega)

end Programs

/-! ## The realisers -/

/-- **Key-block-shaped compression queries of the `PRF` realisers.** -/
def qPrfM (qf qs ℓ : ℕ) : ℕ :=
  qf * 1 + (512 + (qf * 0 + qs * 3585) + 8) * 9 + (qs + 1) * hmsgCost ℓ + qs * prfMsgCost ℓ

section Realizers

variable (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
  (pkSeedDist : ProbComp (Bytes 16)) {qf qs ℓ : ℕ}
  (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List Byte) i = true) qf)
  (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List Byte) i = true) qs)
  (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQ (S := List Byte) ℓ i = true) 0)
  (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ)

include hqf hqs hlong hout

/-- The SUF `PRF` realiser `AprfS` makes at most `qPrfM qf qs ℓ` marked compression queries. -/
theorem AprfS_mark : IsQueryBoundP (AprfS S oR pkSeedDist) (Prf.markQ blk128) (qPrfM qf qs ℓ) :=
  have hF := Ideal.Realize.Msg.mainC_bounds S hqf hqs hlong hout
  chainA_mark _ (bPrfWCOpenP_port _ _ hF) (PprfS_long oR pkSeedDist S hF)
    (bPrfWCOpenP_hm _ _ hF) (bPrfWCOpenP_pm _ _ hF) (bPrfWCOpenP_bad _ _ hF thB okLen_le)
    (PprfS_sk oR pkSeedDist S hF)

/-- The EUF `PRF` realiser `AprfE` makes at most `qPrfM qf qs ℓ` marked compression queries. -/
theorem AprfE_mark : IsQueryBoundP (AprfE S oR pkSeedDist) (Prf.markQ blk128) (qPrfM qf qs ℓ) :=
  have hF := Ideal.Realize.Msg.mainC_bounds S hqf hqs hlong hout
  chainA_mark _ (bPrfCOpenP_port _ _ hF) (PprfE_long oR pkSeedDist S hF)
    (bPrfCOpenP_hm _ _ hF) (bPrfCOpenP_pm _ _ hF) (bPrfCOpenP_bad _ _ hF thB okLen_le)
    (PprfE_sk oR pkSeedDist S hF)

theorem realizesPrfSuf_mark :
    IsQueryBoundP (realizesPrfSuf S oR pkSeedDist hqf hqs hlong hout).A (Prf.markQ blk128)
      (qPrfM qf qs ℓ) :=
  AprfS_mark S oR pkSeedDist hqf hqs hlong hout

theorem realizesPrfEuf_mark :
    IsQueryBoundP (realizesPrfEuf S oR pkSeedDist hqf hqs hlong hout).A (Prf.markQ blk128)
      (qPrfM qf qs ℓ) :=
  AprfE_mark S oR pkSeedDist hqf hqs hlong hout

end Realizers

/-- Closed form of `qPrfM`. -/
theorem qPrfM_le (qf qs ℓ : ℕ) : qPrfM qf qs ℓ ≤ qf + (qs + 1) * (32272 + 2 * ((ℓ + 56) / 64)) := by
  unfold qPrfM hmsgCost prfMsgCost
  have h1 : (ℓ + 24) / 64 ≤ (ℓ + 56) / 64 := Nat.div_le_div_right (by omega)
  have h2 := Nat.mul_le_mul_left qs h1
  generalize (ℓ + 56) / 64 = x at *
  generalize (ℓ + 24) / 64 = y at *
  ring_nf
  ring_nf at h2
  omega

end Ideal.Realize.Prf

#print axioms Ideal.Realize.Prf.thashC_mark
#print axioms Ideal.Realize.Prf.chainA_mark
#print axioms Ideal.Realize.Prf.PprfS_long
#print axioms Ideal.Realize.Prf.PprfS_sk
#print axioms Ideal.Realize.Prf.AprfS_mark
#print axioms Ideal.Realize.Prf.AprfE_mark
#print axioms Ideal.Realize.Prf.qPrfM_le
