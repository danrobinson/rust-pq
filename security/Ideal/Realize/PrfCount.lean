import Ideal.Realize.PrfPort
import Ideal.Realize.MsgCount

/-!
# Query counts of the open `PRF` port programs

Indices of `QSpec prims D`: `ℕ ⊕ (((St × Blk) ⊕ D) ⊕ (PublicHashQuery … ⊕ (SkPrf × Y × List Byte)))`.

* `liftQ pp pg ph pm`: a predicate on port (`pp`), game (`pg`), hash (`ph`) and `PRF_msg` (`pm`)
  queries (never on uniform bits); `embQ_bound`, `embHash_bound`: bounds through `embQ`,
  `hashEmb`; `restrictP_bound`: through the domain restriction.
* `np_openKeygenP`, `np_openSignCoreP`, `one_openSignCoreP`: the walks of key generation and
  signing at the PRF-game secrets.
* `bPrfWOpenP_bound`, `bPrfOpenP_bound`: generic counts; instances for the classes
  `qPort`, `qTh`, `qHm`, `qPm`, `qBad`, `qGame` of the SUF and EUF port programs.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security

namespace Ideal.Realize.Prf

open Reduction Reduction.Open
open Ideal.Realize.Msg (harnP_bound isTh isHm longH verifyM_bound PortBounds forged_len)

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! ## Predicates -/

section Preds

variable {D P K Y M : Type}

/-- A predicate on port, game, hash and `PRF_msg` queries. -/
def liftQ (pp : Prop) (pg : D → Prop) (ph : PublicHashQuery P K Y → Prop) (pm : M → Prop) :
    ℕ ⊕ (((St × Blk) ⊕ D) ⊕ (PublicHashQuery P K Y ⊕ M)) → Prop
  | .inl _ => False
  | .inr (.inl (.inl _)) => pp
  | .inr (.inl (.inr d)) => pg d
  | .inr (.inr (.inl q)) => ph q
  | .inr (.inr (.inr m)) => pm m

instance (pp : Prop) [Decidable pp] (pg : D → Prop) (ph : PublicHashQuery P K Y → Prop)
    (pm : M → Prop) [DecidablePred pg] [DecidablePred ph] [DecidablePred pm] :
    DecidablePred (liftQ pp pg ph pm) := fun t => by
  rcases t with n | (q | d) | (q | m) <;> simp only [liftQ] <;> infer_instance

/-- The `QSpec` index of a `PSpec` index. -/
def embIdx : ℕ ⊕ (D ⊕ (PublicHashQuery P K Y ⊕ M)) →
    ℕ ⊕ (((St × Blk) ⊕ D) ⊕ (PublicHashQuery P K Y ⊕ M))
  | .inl n => .inl n
  | .inr (.inl d) => .inr (.inl (.inr d))
  | .inr (.inr q) => .inr (.inr q)

end Preds

section Transfer

variable {p₀ : Params} {prims : Primitives p₀} {D D' α : Type}

abbrev QIdx (prims : Primitives p₀) (D : Type) : Type :=
  ℕ ⊕ (((St × Blk) ⊕ D) ⊕
    (PublicHashQuery prims.PkSeed prims.AdrsKey prims.Y ⊕ (prims.SkPrf × prims.Y × List Byte)))

theorem embQ_bound (p : QIdx prims D → Prop) [DecidablePred p]
    (X : OracleComp (PSpec prims D) α) (n : ℕ) (h : IsQueryBoundP X (fun t => p (embIdx t)) n) :
    IsQueryBoundP (simulateQ embQ X) p n := by
  refine IsQueryBoundP.simulateQ_of_step h (fun t ht => ?_) (fun t ht => ?_)
  · rcases t with m | d | q
    · exact (isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos
    · exact (isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos
    · exact (isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos
  · rcases t with m | d | q
    · exact (isQueryBoundP_query_iff _ _ _).2 fun h' => absurd h' ht
    · exact (isQueryBoundP_query_iff _ _ _).2 fun h' => absurd h' ht
    · exact (isQueryBoundP_query_iff _ _ _).2 fun h' => absurd h' ht

/-- An embedded hash program. -/
theorem embHash_bound (p : QIdx prims D → Prop) [DecidablePred p]
    (Q : OracleComp (publicHashSpec prims.core) α) (n : ℕ)
    (h : IsQueryBoundP Q (fun q => p (.inr (.inr (.inl q)))) n) :
    IsQueryBoundP (simulateQ embQ (simulateQ (hashEmb prims D) Q)) p n := by
  refine embQ_bound p _ n (IsQueryBoundP.simulateQ_of_step h (fun t ht => ?_) (fun t ht => ?_))
  · exact (isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos
  · exact (isQueryBoundP_query_iff _ _ _).2 fun h' => absurd h' ht

/-- Bounds through the domain restriction. -/
theorem restrictP_bound [Inhabited prims.Y] (r : D → Option D') (pp : Prop) [Decidable pp]
    (pg : D → Prop) (pg' : D' → Prop) [DecidablePred pg] [DecidablePred pg']
    (ph : PublicHashQuery prims.PkSeed prims.AdrsKey prims.Y → Prop) [DecidablePred ph]
    (pm : prims.SkPrf × prims.Y × List Byte → Prop) [DecidablePred pm]
    (hg : ∀ d d', r d = some d' → pg' d' → pg d)
    (X : OracleComp (QSpec prims D) α) (n : ℕ)
    (h : IsQueryBoundP X (liftQ pp pg ph pm) n) :
    IsQueryBoundP (simulateQ (restrictP (prims := prims) r) X)
      (liftQ pp pg' ph pm) n := by
  refine IsQueryBoundP.simulateQ_of_step h (fun t ht => ?_) (fun t ht => ?_)
  · rcases t with m | (q | d) | q
    · exact (isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos
    · exact (isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos
    · simp only [restrictP]
      cases r d with
      | none => exact isQueryBoundP_pure _ _ _
      | some d' => exact (isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos
    · exact (isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos
  · rcases t with m | (q | d) | (q | m)
    · exact (isQueryBoundP_query_iff _ _ _).2 fun h' => by simp [liftQ] at h'
    · exact (isQueryBoundP_query_iff _ _ _).2 fun h' => absurd h' ht
    · simp only [restrictP]
      cases hd : r d with
      | none => exact isQueryBoundP_pure _ _ _
      | some d' => exact (isQueryBoundP_query_iff _ _ _).2 fun h' => absurd (hg d d' hd h') ht
    · exact (isQueryBoundP_query_iff _ _ _).2 fun h' => absurd h' ht
    · exact (isQueryBoundP_query_iff _ _ _).2 fun h' => absurd h' ht

end Transfer

/-! ## The structure walks at the PRF-game secrets -/

section Walks

variable {vp : ValidatedParams} {prims : Primitives vp.params} {D : Type}

attribute [local instance] openQ

variable (p : ℕ ⊕ ((prims.PkSeed × Adrs) ⊕
    (PublicHashQuery prims.PkSeed prims.AdrsKey prims.Y ⊕ (prims.SkPrf × prims.Y × List Byte))) →
      Prop) [DecidablePred p]

theorem np_openKeygenP (pkSeed : prims.PkSeed) (hsec : ∀ a, ¬ p (.inr (.inl (pkSeed, a))))
    (hth : ∀ key xs, OkLen vp xs → ¬ p (.inr (.inr (.inl (.thash pkSeed key xs))))) :
    IsQueryBoundP (openKeygenP prims pkSeed) p 0 :=
  np_xmssNode p prims.core
    (hash := PublicHash.f prims.core pkSeed) (compress := PublicHash.tl prims.core pkSeed)
    (nodeHash := PublicHash.h prims.core pkSeed) (secret := fun a => gameQ prims (pkSeed, a))
    (fun _ _ => (isQueryBoundP_query_iff _ _ _).2 fun h => absurd h (hth _ _ (Or.inl rfl)))
    (fun _ ys hys => (isQueryBoundP_query_iff _ _ _).2 fun h =>
      absurd h (hth _ _ (Or.inr (Or.inr hys))))
    (fun _ _ _ => (isQueryBoundP_query_iff _ _ _).2 fun h =>
      absurd h (hth _ _ (Or.inr (Or.inl rfl))))
    (fun _ => (isQueryBoundP_query_iff _ _ _).2 fun h => absurd h (hsec _)) _ _ _

/-- Open signing at a supplied randomizer makes at most `e` `p`-queries, if its `H_msg` query
makes at most `e` and `p` holds of no secret read and no `Thash` query on `1`, `2`, `len`, `k`
values. -/
theorem openSignCoreP_bound (msg : List Byte) (pkSeed : prims.PkSeed) (pkRoot R : prims.Y) (e : ℕ)
    (hsec : ∀ a, ¬ p (.inr (.inl (pkSeed, a))))
    (hth : ∀ key xs, OkLen vp xs → ¬ p (.inr (.inr (.inl (.thash pkSeed key xs)))))
    (hm : IsQueryBoundP (PublicHash.hmsg prims.core R pkSeed pkRoot msg :
      OracleComp (PSpec prims (prims.PkSeed × Adrs)) _) p e) :
    IsQueryBoundP (openSignCoreP prims msg pkSeed pkRoot R) p e := by
  have hf : ∀ (a : Adrs) (y : prims.core.Y), IsQueryBoundP (PublicHash.f prims.core pkSeed a y :
      OracleComp (PSpec prims (prims.PkSeed × Adrs)) prims.Y) p 0 :=
    fun _ _ => (isQueryBoundP_query_iff _ _ _).2 fun h => absurd h (hth _ _ (Or.inl rfl))
  have htl : ∀ (a : Adrs) (ys : List prims.core.Y),
      (ys.length = vp.params.len ∨ ys.length = vp.params.k) →
      IsQueryBoundP (PublicHash.tl prims.core pkSeed a ys :
      OracleComp (PSpec prims (prims.PkSeed × Adrs)) prims.Y) p 0 :=
    fun _ ys hys => (isQueryBoundP_query_iff _ _ _).2 fun h =>
      absurd h (hth _ _ (Or.inr (Or.inr hys)))
  have hh : ∀ (a : Adrs) (l r : prims.core.Y),
      IsQueryBoundP (PublicHash.h prims.core pkSeed a l r :
      OracleComp (PSpec prims (prims.PkSeed × Adrs)) prims.Y) p 0 :=
    fun _ _ _ => (isQueryBoundP_query_iff _ _ _).2 fun h =>
      absurd h (hth _ _ (Or.inr (Or.inl rfl)))
  have hs : ∀ a : Adrs, IsQueryBoundP (gameQ prims (pkSeed, a)) p 0 :=
    fun _ => (isQueryBoundP_query_iff _ _ _).2 fun h => absurd h (hsec _)
  unfold openSignCoreP GeneralScheme.signInternalWithSecretRandomizerM
  exact (isQueryBoundP_bind (m := 0) hm fun digest _ =>
    isQueryBoundP_bind_zero _ _ (np_forsSign p prims.core hf hh hs _ _) fun forsSig =>
      isQueryBoundP_bind_zero _ _ (np_forsPk p prims.core hf htl hh forsSig _ _) fun forsPk =>
        isQueryBoundP_bind_zero _ _ (np_signFromPos p prims.core hf htl hh hs _ _ _ _ _)
          fun htSig => isQueryBoundP_pure _ _ _).mono (by omega)

end Walks

/-! ## Generic counts of the port programs -/

section Programs

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]
variable (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
  (pkSeedDist : ProbComp prims.PkSeed)
variable (p : QIdx prims (D₀ prims) → Prop) [DecidablePred p]

theorem liftM_q {α : Type} (hu : ∀ n, ¬ p (.inl n)) (ob : ProbComp α) :
    IsQueryBoundP (liftM ob : OracleComp (QSpec prims (D₀ prims)) α) p 0 := by
  induction ob using OracleComp.inductionOn with
  | pure a => exact isQueryBoundP_pure _ _ _
  | query_bind n k ih =>
    rw [liftM_bind]
    exact isQueryBoundP_bind_zero _ _
      ((isQueryBoundP_query_iff (spec := QSpec prims (D₀ prims)) _ (.inl n) 0).2 fun h =>
        absurd h (hu n)) ih

theorem forged_lenQ {σ : Type} (mainP : PortForgerProg vp prims) (ℓ : ℕ)
    (hout : ∀ pk, ∀ z ∈ support (mainP pk), z.1.length ≤ ℓ)
    (impl : QueryImpl (FSpecP (GeneralScheme.SignatureCore vp prims.core))
      (StateT σ (OracleComp (QSpec prims (D₀ prims)))))
    (pk : PublicKeyCore prims.core) (s : σ) (z)
    (hz : z ∈ support ((simulateQ impl (mainP pk)).run s)) : z.1.1.length ≤ ℓ := by
  have hz' : z.1 ∈ support ((simulateQ impl (mainP pk)).run' s) := by
    rw [StateT.run'_eq, support_map]
    exact ⟨z, hz, rfl⟩
  exact hout pk z.1 (support_simulateQ_run'_subset _ _ _ hz')

/-- **Generic count of the SUF port program (before the restriction).** -/
theorem bPrfWOpenP_bound (wO : OpenCheck vp prims) (mainP : PortForgerProg vp prims)
    (qf qs ℓ a c w d : ℕ) (hF : PortBounds mainP qf qs ℓ)
    (hu : ∀ n, ¬ p (.inl n))
    (hk : ∀ pkSeed, IsQueryBoundP (simulateQ embQ (openKeygenP prims pkSeed)) p a)
    (hsign : ∀ pk skPrf m, m.length ≤ ℓ →
      IsQueryBoundP (simulateQ embQ (openSignP optRand pk skPrf m)) p c)
    (hport : ∀ q, IsQueryBoundP (portQ (prims := prims) (D := D₀ prims) q) p w)
    (hcheck : ∀ pk f log, f.1.length ≤ ℓ →
      IsQueryBoundP (simulateQ embQ (simulateQ (hashEmb prims (D₀ prims)) (wO pk f log))) p d) :
    IsQueryBoundP (bPrfWOpenP optRand pkSeedDist wO mainP) p (a + (qf * w + qs * c) + d) := by
  unfold bPrfWOpenP bRestWOpenP
  refine (isQueryBoundP_bind (n := 0) (liftM_q p hu pkSeedDist) fun pkSeed _ =>
    isQueryBoundP_bind (n := 0) (liftM_q p hu _) fun skPrf _ =>
      isQueryBoundP_bind (hk pkSeed) fun root _ =>
        isQueryBoundP_bind (harnP_bound p ℓ w c qf qs hu _ hport _ (fun m s hm => ?_)
          _ (hF.qf _) (hF.qs _) (hF.long _) []) fun z hz =>
            hcheck _ _ _ (forged_lenQ mainP ℓ hF.out _ _ _ z hz)).mono (by omega)
  simp only [sigSignOracle, run_appendLog_apply]
  exact isQueryBoundP_bind (m := 0) (hsign _ skPrf m hm) fun u _ => isQueryBoundP_pure _ _ _

/-- **Generic count of the EUF port program (before the restriction).** -/
theorem bPrfOpenP_bound (mainP : PortForgerProg vp prims)
    (qf qs ℓ a c w d : ℕ) (hF : PortBounds mainP qf qs ℓ)
    (hu : ∀ n, ¬ p (.inl n))
    (hk : ∀ pkSeed, IsQueryBoundP (simulateQ embQ (openKeygenP prims pkSeed)) p a)
    (hsign : ∀ pk skPrf m, m.length ≤ ℓ →
      IsQueryBoundP (simulateQ embQ (openSignP optRand pk skPrf m)) p c)
    (hport : ∀ q, IsQueryBoundP (portQ (prims := prims) (D := D₀ prims) q) p w)
    (hcheck : ∀ pk (msg : List Byte) sig, msg.length ≤ ℓ →
      IsQueryBoundP (simulateQ embQ (simulateQ (hashEmb prims (D₀ prims))
        (GeneralScheme.verifyInternalM vp prims.core msg sig pk :
          OracleComp (publicHashSpec prims.core) Bool))) p d) :
    IsQueryBoundP (bPrfOpenP optRand pkSeedDist mainP) p (a + (qf * w + qs * c) + d) := by
  unfold bPrfOpenP bRestOpenP
  refine (isQueryBoundP_bind (n := 0) (liftM_q p hu pkSeedDist) fun pkSeed _ =>
    isQueryBoundP_bind (n := 0) (liftM_q p hu _) fun skPrf _ =>
      isQueryBoundP_bind (hk pkSeed) fun root _ =>
        isQueryBoundP_bind (harnP_bound p ℓ w c qf qs hu _ hport _ (fun m s hm => ?_)
          _ (hF.qf _) (hF.qs _) (hF.long _) []) fun z hz =>
            isQueryBoundP_bind (m := 0) (hcheck _ _ _ (forged_lenQ mainP ℓ hF.out _ _ _ z hz))
              fun v _ => isQueryBoundP_pure _ _ _).mono (by omega)
  simp only [harnessSignOracle, StateT.run_bind, StateT.run_monadLift, bind_assoc]
  exact isQueryBoundP_bind (m := 0) (hsign _ skPrf m hm) fun u _ => by simp

end Programs

/-! ## The query classes and their counts -/

section Classes

variable {D P K Y M : Type}

/-- Port queries. -/
abbrev qPort : ℕ ⊕ (((St × Blk) ⊕ D) ⊕ (PublicHashQuery P K Y ⊕ M)) → Prop :=
  liftQ True (fun _ => False) (fun _ => False) (fun _ => False)
/-- PRF-game queries. -/
abbrev qGame : ℕ ⊕ (((St × Blk) ⊕ D) ⊕ (PublicHashQuery P K Y ⊕ M)) → Prop :=
  liftQ False (fun _ => True) (fun _ => False) (fun _ => False)
/-- Hash queries. -/
abbrev qHash : ℕ ⊕ (((St × Blk) ⊕ D) ⊕ (PublicHashQuery P K Y ⊕ M)) → Prop :=
  liftQ False (fun _ => False) (fun _ => True) (fun _ => False)
/-- `Thash` queries. -/
abbrev qTh : ℕ ⊕ (((St × Blk) ⊕ D) ⊕ (PublicHashQuery P K Y ⊕ M)) → Prop :=
  liftQ False (fun _ => False) (fun q => isTh q = true) (fun _ => False)
/-- `H_msg` queries. -/
abbrev qHm : ℕ ⊕ (((St × Blk) ⊕ D) ⊕ (PublicHashQuery P K Y ⊕ M)) → Prop :=
  liftQ False (fun _ => False) (fun q => isHm q = true) (fun _ => False)
/-- `PRF_msg` queries. -/
abbrev qPm {SK : Type} :
    ℕ ⊕ (((St × Blk) ⊕ D) ⊕ (PublicHashQuery P K Y ⊕ (SK × Y × List Byte))) → Prop :=
  liftQ False (fun _ => False) (fun _ => False) (fun _ => True)
/-- Too long hash / `PRF_msg` queries. -/
abbrev qBad {SK : Type} (B ℓ : ℕ) :
    ℕ ⊕ (((St × Blk) ⊕ D) ⊕ (PublicHashQuery P K Y ⊕ (SK × Y × List Byte))) → Prop :=
  liftQ False (fun _ => False) (fun q => longH B ℓ q = true) (fun t => ℓ < t.2.2.length)

theorem qTh_imp (t : ℕ ⊕ (((St × Blk) ⊕ D) ⊕ (PublicHashQuery P K Y ⊕ M))) :
    qTh t → qHash t := by
  rcases t with n | (q | d) | (q | m) <;> simp [liftQ]

end Classes

section Instances

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]
variable (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
  (pkSeedDist : ProbComp prims.PkSeed)
variable {mainP : PortForgerProg vp prims} {qf qs ℓ : ℕ}

private theorem hu_q {pp : Prop} [Decidable pp] {pg : _ → Prop} {ph : _ → Prop} {pm : _ → Prop}
    [DecidablePred pg] [DecidablePred ph] [DecidablePred pm] :
    ∀ n : ℕ, ¬ (liftQ pp pg ph pm : QIdx prims (D₀ prims) → Prop) (.inl n) := by
  intro n; simp [liftQ]

theorem liftM_zeroG {ι : Type} {X : OracleSpec ι} {α : Type} (ob : ProbComp α)
    (q : ℕ ⊕ ι → Prop) [DecidablePred q] (h0 : ∀ n, ¬ q (.inl n)) :
    IsQueryBoundP (liftM ob : OracleComp (unifSpec + X) α) q 0 := by
  induction ob using OracleComp.inductionOn with
  | pure a => exact isQueryBoundP_pure _ _ _
  | query_bind n k ih =>
    rw [liftM_bind]
    exact isQueryBoundP_bind_zero _ _
      ((isQueryBoundP_query_iff (spec := unifSpec + X) _ (.inl n) 0).2 fun h => absurd h (h0 n)) ih

theorem false_bound {ι α : Type} {spec : OracleSpec ι} (X : OracleComp spec α) (p : ι → Prop)
    [DecidablePred p] (h : ∀ t, ¬ p t) (n : ℕ) : IsQueryBoundP X p n :=
  IsQueryBoundP.of_imp (fun t ht => (h t ht).elim) ((isQueryBoundP_false X 0).mono (Nat.zero_le _))

theorem portQ_bound (p : QIdx prims (D₀ prims) → Prop) [DecidablePred p] (q : St × Blk) :
    IsQueryBoundP (portQ (prims := prims) (D := D₀ prims) q) p
      (if p (.inr (.inl (.inl q))) then 1 else 0) :=
  (isQueryBoundP_query_iff _ _ _).2 fun h => by simp [h]

/-- The signing step through `embQ`: `opt_rand`, one `PRF_msg` query, open signing. -/
theorem embSign_bound (p : QIdx prims (D₀ prims) → Prop) [DecidablePred p]
    (hu : ∀ n, ¬ p (.inl n)) (pk : PublicKeyCore prims.core) (skPrf : prims.SkPrf) (m : List Byte)
    (cg ch : ℕ)
    (hg : ∀ addrnd, IsQueryBoundP (prfMsgQ prims (D₀ prims) skPrf addrnd m)
      (fun t => p (embIdx t)) cg)
    (hs : ∀ R, IsQueryBoundP (openSignCoreP prims m pk.pkSeed pk.pkRoot R)
      (fun t => p (embIdx t)) ch) :
    IsQueryBoundP (simulateQ embQ (openSignP optRand pk skPrf m)) p (cg + ch) := by
  refine embQ_bound p _ (cg + ch) ?_
  unfold openSignP
  exact (isQueryBoundP_bind (n := 0) (m := cg + ch)
    (liftM_zeroG (X := (D₀ prims →ₒ prims.Y) + HSpec prims) _ (fun t => p (embIdx t))
      fun n => hu n) fun addrnd _ =>
    isQueryBoundP_bind (hg addrnd) fun R _ => hs R).mono (by omega)

theorem sufCheckOpen_ph (ph : PublicHashQuery prims.PkSeed prims.AdrsKey prims.Y → Prop)
    [DecidablePred ph] (pk : PublicKeyCore prims.core)
    (f : List Byte × GeneralScheme.SignatureCore vp prims.core) (log : SigLog vp prims) (e : ℕ)
    (hth : ∀ key xs, OkLen vp xs → ¬ ph (.thash pk.pkSeed key xs))
    (hm : IsQueryBoundP (PublicHash.hmsg prims.core f.2.randomness pk.pkSeed pk.pkRoot f.1 :
      OracleComp (publicHashSpec prims.core) _) ph e) :
    IsQueryBoundP (sufCheckOpen pk f log) ph e :=
  (isQueryBoundP_bind (m := 0) (verifyM_bound prims.core ph f.1 f.2 pk e hth hm)
    fun _ _ => isQueryBoundP_pure _ _ _).mono (by omega)

/-- The PSpec index of a hash query is never a port / game / `PRF_msg` query. -/
theorem emb_noPort (t : ℕ ⊕ ((D₀ prims) ⊕ (PublicHashQuery prims.PkSeed prims.AdrsKey prims.Y ⊕
    (prims.SkPrf × prims.Y × List Byte)))) : ¬ (qPort : QIdx prims (D₀ prims) → Prop) (embIdx t) := by
  rcases t with n | d | (q | m) <;> simp [liftQ, embIdx]

section Suf

variable (hF : PortBounds mainP qf qs ℓ)
include hF

/-- **Port queries of the SUF port program**: at most `qf`. -/
theorem bPrfWCOpenP_port :
    IsQueryBoundP (bPrfWCOpenP optRand pkSeedDist sufCheckOpen mainP) qPort qf := by
  refine restrictP_bound _ True (fun _ => False) (fun _ => False) (fun _ => False)
    (fun _ => False) (fun _ _ _ h => h.elim) _ _ ?_
  refine (bPrfWOpenP_bound optRand pkSeedDist qPort sufCheckOpen mainP qf qs ℓ 0 0 1 0 hF hu_q
    (fun pkSeed => embQ_bound _ _ 0 (false_bound _ _ emb_noPort 0))
    (fun pk skPrf m _ => embQ_bound _ _ 0 (false_bound _ _ emb_noPort 0))
    (fun q => (portQ_bound _ q).mono (by simp [liftQ]))
    (fun pk f log _ => embHash_bound _ _ 0 (false_bound _ _ (fun q => by simp [liftQ]) 0))).mono
      (by omega)

/-- **PRF-game queries of the SUF port program**: as `Reduction.Open.bPrfWCOpen_suf_game`. -/
theorem bPrfWCOpenP_game :
    IsQueryBoundP (bPrfWCOpenP optRand pkSeedDist sufCheckOpen mainP) qGame
      (2 ^ vp.params.hp * vp.params.len + qs * signReads vp) := by
  refine restrictP_bound _ False (fun _ => True) (fun _ => True) (fun _ => False)
    (fun _ => False) (fun _ _ _ _ => trivial) _ _ ?_
  refine (bPrfWOpenP_bound optRand pkSeedDist qGame sufCheckOpen mainP qf qs ℓ
    (2 ^ vp.params.hp * vp.params.len) (signReads vp) 0 0 hF hu_q
    (fun pkSeed => embQ_bound _ _ _ ((IsQueryBoundP.of_imp (p' := fun t => hkind t = .game)
      (fun t ht => by rcases t with n | d | (q | m) <;> simp_all [liftQ, embIdx, hkind])
      (openKeygenP_kindBound .game pkSeed)).mono (by
        simpa [hind] using Lazy.keygenB_sec (vp := vp))))
    (fun pk skPrf m _ => embQ_bound _ _ _ ((IsQueryBoundP.of_imp (p' := fun t => hkind t = .game)
      (fun t ht => by rcases t with n | d | (q | m) <;> simp_all [liftQ, embIdx, hkind])
      (openSignP_kindBound (optRand := optRand) .game (by decide) pk skPrf m)).mono (by
        simpa [hind] using Lazy.signB_sec (vp := vp))))
    (fun q => (portQ_bound _ q).mono (by simp [liftQ]))
    (fun pk f log _ => embHash_bound _ _ 0 (false_bound _ _ (fun q => by simp [liftQ]) 0))).mono
      (by omega)

/-- **Hash queries of the SUF port program**: `keygenHashes + qs·signHashes + (1 + verifyHashes)`
(as `Reduction.Open.bPrfWCOpen_suf_hashes`). -/
theorem bPrfWCOpenP_hash :
    IsQueryBoundP (bPrfWCOpenP optRand pkSeedDist sufCheckOpen mainP) qHash
      (Lazy.keygenHashes vp + qs * Lazy.signHashes vp + (1 + Resources2.verifyHashes vp)) := by
  refine restrictP_bound _ False (fun _ => False) (fun _ => False) (fun _ => True)
    (fun _ => False) (fun _ _ _ h => h.elim) _ _ ?_
  refine (bPrfWOpenP_bound optRand pkSeedDist qHash sufCheckOpen mainP qf qs ℓ
    (Lazy.keygenHashes vp) (Lazy.signHashes vp) 0 (1 + Resources2.verifyHashes vp) hF hu_q
    (fun pkSeed => embQ_bound _ _ _ ((IsQueryBoundP.of_imp (p' := fun t => hkind t = .hash)
      (fun t ht => by rcases t with n | d | (q | m) <;> simp_all [liftQ, embIdx, hkind])
      (openKeygenP_kindBound .hash pkSeed)).mono (by
        simpa [hind] using Lazy.keygenB_hash (vp := vp))))
    (fun pk skPrf m _ => embQ_bound _ _ _ ((IsQueryBoundP.of_imp (p' := fun t => hkind t = .hash)
      (fun t ht => by rcases t with n | d | (q | m) <;> simp_all [liftQ, embIdx, hkind])
      (openSignP_kindBound (optRand := optRand) .hash (by decide) pk skPrf m)).mono (by
        simpa [hind] using Lazy.signB_hash (vp := vp))))
    (fun q => (portQ_bound _ q).mono (by simp [liftQ]))
    (fun pk f log _ => embHash_bound _ _ _ (IsQueryBoundP.of_imp (fun _ _ => trivial)
      (sufCheckOpen_bound pk f log)))).mono (by omega)

/-- **`PRF_msg` queries of the SUF port program**: one per signing query. -/
theorem bPrfWCOpenP_pm :
    IsQueryBoundP (bPrfWCOpenP optRand pkSeedDist sufCheckOpen mainP) qPm qs := by
  refine restrictP_bound _ False (fun _ => False) (fun _ => False) (fun _ => False)
    (fun _ => True) (fun _ _ _ h => h.elim) _ _ ?_
  refine (bPrfWOpenP_bound optRand pkSeedDist qPm sufCheckOpen mainP qf qs ℓ 0 1 0 0 hF hu_q
    (fun pkSeed => embQ_bound _ _ 0 (np_openKeygenP _ pkSeed (fun a => by simp [liftQ, embIdx])
      (fun key xs _ => by simp [liftQ, embIdx])))
    (fun pk skPrf m _ => embQ_bound _ _ _ ((IsQueryBoundP.of_imp (p' := fun t => hkind t = .prfmsg)
      (fun t ht => by rcases t with n | d | (q | m) <;> simp_all [liftQ, embIdx, hkind])
      (openSignP_kindBound (optRand := optRand) .prfmsg (by decide) pk skPrf m)).mono (by
        simp [hind, Lazy.signB_game])))
    (fun q => (portQ_bound _ q).mono (by simp [liftQ]))
    (fun pk f log _ => embHash_bound _ _ 0 (false_bound _ _ (fun q => by simp [liftQ]) 0))).mono
      (by omega)

/-- **`H_msg` queries of the SUF port program**: one per signing query, one for verification. -/
theorem bPrfWCOpenP_hm :
    IsQueryBoundP (bPrfWCOpenP optRand pkSeedDist sufCheckOpen mainP) qHm (qs + 1) := by
  refine restrictP_bound _ False (fun _ => False) (fun _ => False) (fun q => isHm q = true)
    (fun _ => False) (fun _ _ _ h => h.elim) _ _ ?_
  refine (bPrfWOpenP_bound optRand pkSeedDist qHm sufCheckOpen mainP qf qs ℓ 0 1 0 1 hF hu_q
    (fun pkSeed => embQ_bound _ _ 0 (np_openKeygenP _ pkSeed (fun a => by simp [liftQ, embIdx])
      (fun key xs _ => by simp [liftQ, embIdx, isHm])))
    (fun pk skPrf m _ => (embSign_bound optRand qHm hu_q pk skPrf m 0 1
      (fun a => (isQueryBoundP_query_iff _ _ _).2 fun h => by simp [liftQ, embIdx] at h)
      (fun R => openSignCoreP_bound _ m _ _ R 1 (fun a => by simp [liftQ, embIdx])
        (fun key xs _ => by simp [liftQ, embIdx, isHm])
        ((isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos))).mono (by omega))
    (fun q => (portQ_bound _ q).mono (by simp [liftQ]))
    (fun pk f log _ => embHash_bound _ _ 1 (sufCheckOpen_ph _ pk f log 1
      (fun key xs _ => by simp [liftQ, isHm])
      ((isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos)))).mono (by omega)

/-- **No too long hash or `PRF_msg` query in the SUF port program.** -/
theorem bPrfWCOpenP_bad (B : ℕ) (hB : ∀ xs : List prims.Y, OkLen vp xs → xs.length ≤ B) :
    IsQueryBoundP (bPrfWCOpenP optRand pkSeedDist sufCheckOpen mainP) (qBad B ℓ) 0 := by
  refine restrictP_bound _ False (fun _ => False) (fun _ => False) (fun q => longH B ℓ q = true)
    (fun t => ℓ < t.2.2.length) (fun _ _ _ h => h.elim) _ _ ?_
  refine (bPrfWOpenP_bound optRand pkSeedDist (qBad B ℓ) sufCheckOpen mainP qf qs ℓ 0 0 0 0 hF hu_q
    (fun pkSeed => embQ_bound _ _ 0 (np_openKeygenP _ pkSeed (fun a => by simp [liftQ, embIdx])
      (fun key xs hx => by simp [liftQ, embIdx, longH]; exact hB xs hx)))
    (fun pk skPrf m hm => (embSign_bound optRand (qBad B ℓ) hu_q pk skPrf m 0 0
      (fun a => (isQueryBoundP_query_iff _ _ _).2 fun h => by
        simp [liftQ, embIdx] at h; omega)
      (fun R => openSignCoreP_bound _ m _ _ R 0 (fun a => by simp [liftQ, embIdx])
        (fun key xs hx => by simp [liftQ, embIdx, longH]; exact hB xs hx)
        ((isQueryBoundP_query_iff _ _ _).2 fun h => by
          simp [liftQ, embIdx, longH] at h; omega))))
    (fun q => (portQ_bound _ q).mono (by simp [liftQ]))
    (fun pk f log hf => embHash_bound _ _ 0 (sufCheckOpen_ph _ pk f log 0
      (fun key xs hx => by simp [liftQ, longH]; exact hB xs hx)
      ((isQueryBoundP_query_iff _ _ _).2 fun h => by simp [liftQ, longH] at h; omega)))).mono
        (by omega)

end Suf

section Euf

variable (hF : PortBounds mainP qf qs ℓ)
include hF

/-- **Port queries of the EUF port program**: at most `qf`. -/
theorem bPrfCOpenP_port :
    IsQueryBoundP (bPrfCOpenP optRand pkSeedDist mainP) qPort qf := by
  refine restrictP_bound _ True (fun _ => False) (fun _ => False) (fun _ => False)
    (fun _ => False) (fun _ _ _ h => h.elim) _ _ ?_
  refine (bPrfOpenP_bound optRand pkSeedDist qPort mainP qf qs ℓ 0 0 1 0 hF hu_q
    (fun pkSeed => embQ_bound _ _ 0 (false_bound _ _ emb_noPort 0))
    (fun pk skPrf m _ => embQ_bound _ _ 0 (false_bound _ _ emb_noPort 0))
    (fun q => (portQ_bound _ q).mono (by simp [liftQ]))
    (fun pk msg sig _ => embHash_bound _ _ 0 (false_bound _ _ (fun q => by simp [liftQ]) 0))).mono
      (by omega)

/-- **PRF-game queries of the EUF port program**: as `Reduction.Open.bPrfCOpen_game`. -/
theorem bPrfCOpenP_game :
    IsQueryBoundP (bPrfCOpenP optRand pkSeedDist mainP) qGame
      (2 ^ vp.params.hp * vp.params.len + qs * signReads vp) := by
  refine restrictP_bound _ False (fun _ => True) (fun _ => True) (fun _ => False)
    (fun _ => False) (fun _ _ _ _ => trivial) _ _ ?_
  refine (bPrfOpenP_bound optRand pkSeedDist qGame mainP qf qs ℓ
    (2 ^ vp.params.hp * vp.params.len) (signReads vp) 0 0 hF hu_q
    (fun pkSeed => embQ_bound _ _ _ ((IsQueryBoundP.of_imp (p' := fun t => hkind t = .game)
      (fun t ht => by rcases t with n | d | (q | m) <;> simp_all [liftQ, embIdx, hkind])
      (openKeygenP_kindBound .game pkSeed)).mono (by
        simpa [hind] using Lazy.keygenB_sec (vp := vp))))
    (fun pk skPrf m _ => embQ_bound _ _ _ ((IsQueryBoundP.of_imp (p' := fun t => hkind t = .game)
      (fun t ht => by rcases t with n | d | (q | m) <;> simp_all [liftQ, embIdx, hkind])
      (openSignP_kindBound (optRand := optRand) .game (by decide) pk skPrf m)).mono (by
        simpa [hind] using Lazy.signB_sec (vp := vp))))
    (fun q => (portQ_bound _ q).mono (by simp [liftQ]))
    (fun pk msg sig _ => embHash_bound _ _ 0 (false_bound _ _ (fun q => by simp [liftQ]) 0))).mono
      (by omega)

/-- **Hash queries of the EUF port program**: `keygenHashes + qs·signHashes + (1 + verifyHashes)`
(as `Reduction.Open.bPrfCOpen_hashes`). -/
theorem bPrfCOpenP_hash :
    IsQueryBoundP (bPrfCOpenP optRand pkSeedDist mainP) qHash
      (Lazy.keygenHashes vp + qs * Lazy.signHashes vp + (1 + Resources2.verifyHashes vp)) := by
  refine restrictP_bound _ False (fun _ => False) (fun _ => False) (fun _ => True)
    (fun _ => False) (fun _ _ _ h => h.elim) _ _ ?_
  refine (bPrfOpenP_bound optRand pkSeedDist qHash mainP qf qs ℓ
    (Lazy.keygenHashes vp) (Lazy.signHashes vp) 0 (1 + Resources2.verifyHashes vp) hF hu_q
    (fun pkSeed => embQ_bound _ _ _ ((IsQueryBoundP.of_imp (p' := fun t => hkind t = .hash)
      (fun t ht => by rcases t with n | d | (q | m) <;> simp_all [liftQ, embIdx, hkind])
      (openKeygenP_kindBound .hash pkSeed)).mono (by
        simpa [hind] using Lazy.keygenB_hash (vp := vp))))
    (fun pk skPrf m _ => embQ_bound _ _ _ ((IsQueryBoundP.of_imp (p' := fun t => hkind t = .hash)
      (fun t ht => by rcases t with n | d | (q | m) <;> simp_all [liftQ, embIdx, hkind])
      (openSignP_kindBound (optRand := optRand) .hash (by decide) pk skPrf m)).mono (by
        simpa [hind] using Lazy.signB_hash (vp := vp))))
    (fun q => (portQ_bound _ q).mono (by simp [liftQ]))
    (fun pk msg sig _ => embHash_bound _ _ _ (IsQueryBoundP.of_imp (fun _ _ => trivial)
      (verifyInternalM_bound msg sig pk)))).mono (by omega)

/-- **`PRF_msg` queries of the EUF port program**: one per signing query. -/
theorem bPrfCOpenP_pm :
    IsQueryBoundP (bPrfCOpenP optRand pkSeedDist mainP) qPm qs := by
  refine restrictP_bound _ False (fun _ => False) (fun _ => False) (fun _ => False)
    (fun _ => True) (fun _ _ _ h => h.elim) _ _ ?_
  refine (bPrfOpenP_bound optRand pkSeedDist qPm mainP qf qs ℓ 0 1 0 0 hF hu_q
    (fun pkSeed => embQ_bound _ _ 0 (np_openKeygenP _ pkSeed (fun a => by simp [liftQ, embIdx])
      (fun key xs _ => by simp [liftQ, embIdx])))
    (fun pk skPrf m _ => embQ_bound _ _ _ ((IsQueryBoundP.of_imp (p' := fun t => hkind t = .prfmsg)
      (fun t ht => by rcases t with n | d | (q | m) <;> simp_all [liftQ, embIdx, hkind])
      (openSignP_kindBound (optRand := optRand) .prfmsg (by decide) pk skPrf m)).mono (by
        simp [hind, Lazy.signB_game])))
    (fun q => (portQ_bound _ q).mono (by simp [liftQ]))
    (fun pk msg sig _ => embHash_bound _ _ 0 (false_bound _ _ (fun q => by simp [liftQ]) 0))).mono
      (by omega)

/-- **`H_msg` queries of the EUF port program**: one per signing query, one for verification. -/
theorem bPrfCOpenP_hm :
    IsQueryBoundP (bPrfCOpenP optRand pkSeedDist mainP) qHm (qs + 1) := by
  refine restrictP_bound _ False (fun _ => False) (fun _ => False) (fun q => isHm q = true)
    (fun _ => False) (fun _ _ _ h => h.elim) _ _ ?_
  refine (bPrfOpenP_bound optRand pkSeedDist qHm mainP qf qs ℓ 0 1 0 1 hF hu_q
    (fun pkSeed => embQ_bound _ _ 0 (np_openKeygenP _ pkSeed (fun a => by simp [liftQ, embIdx])
      (fun key xs _ => by simp [liftQ, embIdx, isHm])))
    (fun pk skPrf m _ => (embSign_bound optRand qHm hu_q pk skPrf m 0 1
      (fun a => (isQueryBoundP_query_iff _ _ _).2 fun h => by simp [liftQ, embIdx] at h)
      (fun R => openSignCoreP_bound _ m _ _ R 1 (fun a => by simp [liftQ, embIdx])
        (fun key xs _ => by simp [liftQ, embIdx, isHm])
        ((isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos))).mono (by omega))
    (fun q => (portQ_bound _ q).mono (by simp [liftQ]))
    (fun pk msg sig _ => embHash_bound _ _ 1 (verifyM_bound prims.core _ msg sig pk 1
      (fun key xs _ => by simp [liftQ, isHm])
      ((isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos)))).mono (by omega)

/-- **No too long hash or `PRF_msg` query in the EUF port program.** -/
theorem bPrfCOpenP_bad (B : ℕ) (hB : ∀ xs : List prims.Y, OkLen vp xs → xs.length ≤ B) :
    IsQueryBoundP (bPrfCOpenP optRand pkSeedDist mainP) (qBad B ℓ) 0 := by
  refine restrictP_bound _ False (fun _ => False) (fun _ => False) (fun q => longH B ℓ q = true)
    (fun t => ℓ < t.2.2.length) (fun _ _ _ h => h.elim) _ _ ?_
  refine (bPrfOpenP_bound optRand pkSeedDist (qBad B ℓ) mainP qf qs ℓ 0 0 0 0 hF hu_q
    (fun pkSeed => embQ_bound _ _ 0 (np_openKeygenP _ pkSeed (fun a => by simp [liftQ, embIdx])
      (fun key xs hx => by simp [liftQ, embIdx, longH]; exact hB xs hx)))
    (fun pk skPrf m hm => (embSign_bound optRand (qBad B ℓ) hu_q pk skPrf m 0 0
      (fun a => (isQueryBoundP_query_iff _ _ _).2 fun h => by
        simp [liftQ, embIdx] at h; omega)
      (fun R => openSignCoreP_bound _ m _ _ R 0 (fun a => by simp [liftQ, embIdx])
        (fun key xs hx => by simp [liftQ, embIdx, longH]; exact hB xs hx)
        ((isQueryBoundP_query_iff _ _ _).2 fun h => by
          simp [liftQ, embIdx, longH] at h; omega))))
    (fun q => (portQ_bound _ q).mono (by simp [liftQ]))
    (fun pk msg sig hf => embHash_bound _ _ 0 (verifyM_bound prims.core _ msg sig pk 0
      (fun key xs hx => by simp [liftQ, longH]; exact hB xs hx)
      ((isQueryBoundP_query_iff _ _ _).2 fun h => by simp [liftQ, longH] at h; omega)))).mono
        (by omega)

end Euf

end Instances

end Ideal.Realize.Prf

#print axioms Ideal.Realize.Prf.restrictP_bound
#print axioms Ideal.Realize.Prf.openSignCoreP_bound
#print axioms Ideal.Realize.Prf.bPrfWOpenP_bound
#print axioms Ideal.Realize.Prf.bPrfOpenP_bound
#print axioms Ideal.Realize.Prf.bPrfWCOpenP_port
#print axioms Ideal.Realize.Prf.bPrfWCOpenP_game
#print axioms Ideal.Realize.Prf.bPrfWCOpenP_hash
#print axioms Ideal.Realize.Prf.bPrfWCOpenP_pm
#print axioms Ideal.Realize.Prf.bPrfWCOpenP_hm
#print axioms Ideal.Realize.Prf.bPrfWCOpenP_bad
#print axioms Ideal.Realize.Prf.bPrfCOpenP_port
#print axioms Ideal.Realize.Prf.bPrfCOpenP_game
#print axioms Ideal.Realize.Prf.bPrfCOpenP_hash
#print axioms Ideal.Realize.Prf.bPrfCOpenP_pm
#print axioms Ideal.Realize.Prf.bPrfCOpenP_hm
#print axioms Ideal.Realize.Prf.bPrfCOpenP_bad
