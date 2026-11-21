import Reduction.Gen.Final
import Reduction.ResourcesFinal

/-!
# Resources of the reduction adversaries around a general-spec forger (package GEN-R)

The resource statements of `Reduction/ResourcesFinal.lean` (classical forgers) for the adversaries
of the general-spec headline (`Reduction/Gen/Final.lean`), around a forger family
`F : GFam ds vp prims` with `hF : ∀ pk, IsQueryBoundP (F pk) (fun i => i.isRight = true) qs`
(at most `qs` signing queries on every path; `ds`-queries and uniform queries of the forger are
the forger's own and are NOT counted).  This file: the generic transfer machinery, item (5), and
the post-seed phases of the two-phase adversaries (item 2).  `ResourcesB.lean`: the single-phase
adversaries (item 3), the pre-seed phases (item 1), the bundle `FinalResourcesG` and
`final_resourcesG` (item 4).

## Method

* `PRes ds a₀ oa t` — `t` is a *partial resolution* of the general program `oa`: an answer is fixed
  at every `ds`-query on the way, and `t` may stop early with the fixed output `a₀`.
  `PRes.queryBound`: bounds survive.  `IsResolution.queryBound` (item 5): the same for the
  resolutions of `Reduction/Gen/Derand.lean`.
* `runGO_bind_queryBound` — **black-box transfer**: if the classical run
  `(simulateQ impl t).run s >>= post` satisfies a query bound for every partial resolution `t` of
  `oa`, then the general run `runGO ds impl oa s >>= embed ds ∘ post` satisfies the same bound
  (predicate `liftP ds p`: `ds`-queries never count).  Corollaries `openShape_queryBound`,
  `openShape2_queryBound`, `openAdv_queryBound`, `runGO_post_queryBound`, `runGO_queryBound`:
  every classical bound "for all forgers with at most `qs` signing queries" of a program of the
  shape "classical prefix; one harness run of the forger; classical suffix" holds verbatim, with
  the SAME numeral, for the general program.  No classical counting proof is repeated.
* `wrapS_runGO`, `runGO_closed`, `wrapS_runGO_closed` — interpretation of the non-`ds` queries of
  an open run, step-wise (the general form of `QueryImpl.simulateQ_mapStateTBase_run`).

## Model (same as classical)

A post-seed program of a two-phase adversary equals the general interpretation
`wrapS ds (Lazy.tblImpl (PublicHash.impl prims) tbl) P` (secret reads from the adversary's table,
hash queries evaluated by `prims`, `ds`-queries and uniform bits forwarded) of an OPEN program
`P : OracleComp ((ds + unifSpec) + (gspec + ((SecIdx →ₒ prims.Y) + publicHashSpec prims.core))) _`
in which every `Thash`/`H_msg` evaluation is a hash query; `kindG` classifies the queries of `P`
(`ds`- and uniform queries: `.unif`), and `IsQueryBoundP P (fun t => kindG t = .hash) bound`
bounds the own hash evaluations.  The open programs are the classical open code with the forger
run by `runGO ds (logHarnessO …) (F pk) []` (the handler of `runForgerLog`):
`memoForgeOpenG` (`bTcrArMG`), `findOpenFullG` (`toDsprG`, `toTcrG`), `wotsPhase2OG` (`rUdG`,
`rPreG`, `rTcrTG`); on classical forgers they are the embedded classical open programs
(`…_embed`).

## "Fresh samples" convention

Sample counts are counts of uniform samples drawn by the reduction's own classical code.  The
forger's own `ds`- and uniform draws are not counted anywhere.  Phase-1 (pre-seed) sample counts
are the classical ones, because the pre-seed programs are the classical programs
(`Phase1Eq`, `phase1_resourcesG` in `ResourcesB.lean`).  For the lazy single-phase adversaries the
fresh draws are the `.sec`-queries of the resource-explicit programs `lazyResG …`
(`FinalResourcesG.msg_draws`, …).  Post-seed sample counts of the two-phase adversaries are NOT
proved (as classically: only argued); likewise everything that is "argued only" in the table of
`ResourcesFinal.lean` (collection queries and wrapper samples of `rUd`/`rPre`/`rTcrT`, the pure
tail `wotsAnswer`, absence of local hashing in phase 1, list work).
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal TweakableHash

namespace Reduction.Gen

set_option linter.unusedSectionVars false

section generic

variable {κ : Type} (ds : OracleSpec κ)
variable {ιx ιg ιh : Type} {X : OracleSpec ιx} {G : OracleSpec ιg} {G2 : OracleSpec ιh}
  {σ α β : Type}

/-- A predicate on the query indices of `unifSpec + X`, as a predicate on the indices of
`(ds + unifSpec) + X`: `ds`-queries never satisfy it. -/
def liftP (_ds : OracleSpec κ) (p : ℕ ⊕ ιx → Prop) : (κ ⊕ ℕ) ⊕ ιx → Prop
  | .inl (.inl _) => False
  | .inl (.inr n) => p (.inl n)
  | .inr x => p (.inr x)

instance liftP.instDecidablePred (p : ℕ ⊕ ιx → Prop) [DecidablePred p] :
    DecidablePred (liftP ds p)
  | .inl (.inl _) => inferInstanceAs (Decidable False)
  | .inl (.inr n) => inferInstanceAs (Decidable (p (.inl n)))
  | .inr x => inferInstanceAs (Decidable (p (.inr x)))

/-- `embed` keeps every query count. -/
theorem embed_queryBoundP (p : ℕ ⊕ ιx → Prop) [DecidablePred p]
    (t : OracleComp (unifSpec + X) α) (n : ℕ) (h : IsQueryBoundP t p n) :
    IsQueryBoundP (embed ds t) (liftP ds p) n := by
  induction t using OracleComp.inductionOn generalizing n with
  | pure a => simp
  | query_bind q k ih =>
    rw [embed_bind]
    rw [isQueryBoundP_query_bind_iff] at h
    rcases q with m | x
    · rw [embed_query_inl, isQueryBoundP_query_bind_iff]
      exact ⟨h.1, fun u ↦ ih u _ (h.2 u)⟩
    · rw [embed_query_inr, isQueryBoundP_query_bind_iff]
      exact ⟨h.1, fun u ↦ ih u _ (h.2 u)⟩

/-- `t` is obtained from `oa` by fixing an answer at every `ds`-query on the way, possibly
stopping early with the fixed output `a₀`. -/
inductive PRes (a₀ : α) : OracleComp ((ds + unifSpec) + X) α → OracleComp (unifSpec + X) α → Prop
  | stub (oa) : PRes a₀ oa (pure a₀)
  | pure (a : α) : PRes a₀ (pure a) (pure a)
  | ds (d : ds.Domain) (k) (u : ds.Range d) (t) : PRes a₀ (k u) t →
      PRes a₀ (liftM (((ds + unifSpec) + X).query (.inl (.inl d))) >>= k) t
  | us (n : ℕ) (k) (k') : (∀ u, PRes a₀ (k u) (k' u)) →
      PRes a₀ (liftM (((ds + unifSpec) + X).query (.inl (.inr n))) >>= k)
        (liftM ((unifSpec + X).query (.inl n)) >>= k')
  | X (q : X.Domain) (k) (k') : (∀ u, PRes a₀ (k u) (k' u)) →
      PRes a₀ (liftM (((ds + unifSpec) + X).query (.inr q)) >>= k)
        (liftM ((unifSpec + X).query (.inr q)) >>= k')

theorem PRes.queryBound (p : ℕ ⊕ ιx → Prop) [DecidablePred p] {a₀ : α}
    {oa : OracleComp ((ds + unifSpec) + X) α} {t : OracleComp (unifSpec + X) α}
    (h : PRes ds a₀ oa t) (n : ℕ) (hb : IsQueryBoundP oa (liftP ds p) n) :
    IsQueryBoundP t p n := by
  induction h generalizing n with
  | stub oa => exact isQueryBoundP_pure _ _ _
  | pure a => exact isQueryBoundP_pure _ _ _
  | ds d k u t _ ih =>
    rw [isQueryBoundP_query_bind_iff] at hb
    exact ih n (hb.2 u)
  | us m k k' _ ih =>
    rw [isQueryBoundP_query_bind_iff] at hb ⊢
    exact ⟨hb.1, fun u ↦ ih u _ (hb.2 u)⟩
  | X q k k' _ ih =>
    rw [isQueryBoundP_query_bind_iff] at hb ⊢
    exact ⟨hb.1, fun u ↦ ih u _ (hb.2 u)⟩

/-- **(5) Resolution.** Query bounds survive fixing the `ds`-coins. -/
theorem IsResolution.queryBoundP (p : ℕ ⊕ ιx → Prop) [DecidablePred p]
    {oa : OracleComp ((ds + unifSpec) + X) α} {t : OracleComp (unifSpec + X) α}
    (h : IsResolution ds oa t) (n : ℕ) (hb : IsQueryBoundP oa (liftP ds p) n) :
    IsQueryBoundP t p n := by
  induction h generalizing n with
  | pure a => exact isQueryBoundP_pure _ _ _
  | ds d k u t _ ih =>
    rw [isQueryBoundP_query_bind_iff] at hb
    exact ih n (hb.2 u)
  | us m k k' _ ih =>
    rw [isQueryBoundP_query_bind_iff] at hb ⊢
    exact ⟨hb.1, fun u ↦ ih u _ (hb.2 u)⟩
  | X q k k' _ ih =>
    rw [isQueryBoundP_query_bind_iff] at hb ⊢
    exact ⟨hb.1, fun u ↦ ih u _ (hb.2 u)⟩

lemma liftP_isRight (i : (κ ⊕ ℕ) ⊕ ιx) :
    liftP ds (fun i : ℕ ⊕ ιx ↦ i.isRight = true) i ↔ i.isRight = true := by
  rcases i with (d | n) | x <;> simp [liftP]

/-- The signing-query bound in the two spellings. -/
lemma isRight_iff_liftP (oa : OracleComp ((ds + unifSpec) + X) α) (n : ℕ) :
    IsQueryBoundP oa (fun i ↦ i.isRight = true) n ↔
      IsQueryBoundP oa (liftP ds (fun i : ℕ ⊕ ιx ↦ i.isRight = true)) n :=
  isQueryBoundP_congr_pred fun i ↦ (liftP_isRight ds i).symm

/-- **(5)** Signing-query bounds survive fixing the `ds`-coins. -/
theorem IsResolution.queryBound {oa : OracleComp ((ds + unifSpec) + X) α}
    {t : OracleComp (unifSpec + X) α} (h : IsResolution ds oa t) (n : ℕ)
    (hb : IsQueryBoundP oa (fun i ↦ i.isRight = true) n) :
    IsQueryBoundP t (fun i ↦ i.isRight = true) n :=
  IsResolution.queryBoundP ds _ h n ((isRight_iff_liftP ds oa n).1 hb)

/-- Transfer of a bound through a classical prefix. -/
theorem bind_transfer (p : ℕ ⊕ ιg → Prop) [DecidablePred p] {γ δ δ' : Type}
    (𝔽 : Set (γ → OracleComp (unifSpec + G) δ)) (hne : 𝔽.Nonempty)
    (g : γ → OracleComp ((ds + unifSpec) + G) δ')
    (h : ∀ a m, (∀ f ∈ 𝔽, IsQueryBoundP (f a) p m) → IsQueryBoundP (g a) (liftP ds p) m)
    (x : OracleComp (unifSpec + G) γ) (m : ℕ)
    (hx : ∀ f ∈ 𝔽, IsQueryBoundP (x >>= f) p m) :
    IsQueryBoundP (embed ds x >>= g) (liftP ds p) m := by
  induction x using OracleComp.inductionOn generalizing m with
  | pure a =>
    rw [embed_pure, pure_bind]
    exact h a m fun f hf ↦ by simpa using hx f hf
  | query_bind q k ih =>
    obtain ⟨f₀, hf₀⟩ := hne
    have hx' : ∀ f ∈ 𝔽, (¬ p q ∨ 0 < m) ∧ ∀ u, IsQueryBoundP (k u >>= f) p
        (if p q then m - 1 else m) := fun f hf ↦ by
      have := hx f hf
      rwa [bind_assoc, isQueryBoundP_query_bind_iff] at this
    rw [embed_bind, bind_assoc]
    rcases q with n | y
    · rw [embed_query_inl, isQueryBoundP_query_bind_iff]
      exact ⟨(hx' f₀ hf₀).1, fun u ↦ ih u _ fun f hf ↦ (hx' f hf).2 u⟩
    · rw [embed_query_inr, isQueryBoundP_query_bind_iff]
      exact ⟨(hx' f₀ hf₀).1, fun u ↦ ih u _ fun f hf ↦ (hx' f hf).2 u⟩

lemma runGO_query_ds (impl : QueryImpl (unifSpec + X) (StateT σ (OracleComp (unifSpec + G))))
    (d : ds.Domain) (s : σ) :
    runGO ds impl (liftM (((ds + unifSpec) + X).query (.inl (.inl d)))) s =
      (fun u ↦ (u, s)) <$> (liftM (((ds + unifSpec) + G).query (.inl (.inl d))) :
        OracleComp ((ds + unifSpec) + G) _) := by
  unfold runGO; rw [simulateQ_spec_query]; rfl

lemma runGO_query_us (impl : QueryImpl (unifSpec + X) (StateT σ (OracleComp (unifSpec + G))))
    (n : ℕ) (s : σ) :
    runGO ds impl (liftM (((ds + unifSpec) + X).query (.inl (.inr n)))) s =
      embed ds ((impl (.inl n)).run s) := by
  unfold runGO; rw [simulateQ_spec_query]; rfl

lemma runGO_query_X (impl : QueryImpl (unifSpec + X) (StateT σ (OracleComp (unifSpec + G))))
    (q : X.Domain) (s : σ) :
    runGO ds impl (liftM (((ds + unifSpec) + X).query (.inr q))) s =
      embed ds ((impl (.inr q)).run s) := by
  unfold runGO; rw [simulateQ_spec_query]; rfl

/-- **Black-box transfer.** A bound for the classical run of every partial resolution gives the
bound for the general run. -/
theorem runGO_bind_queryBound (p : ℕ ⊕ ιg → Prop) [DecidablePred p] (a₀ : α)
    (impl : QueryImpl (unifSpec + X) (StateT σ (OracleComp (unifSpec + G))))
    (post : α × σ → OracleComp (unifSpec + G) β)
    (oa : OracleComp ((ds + unifSpec) + X) α) (s : σ) (m : ℕ)
    (h : ∀ t, PRes ds a₀ oa t → IsQueryBoundP ((simulateQ impl t).run s >>= post) p m) :
    IsQueryBoundP (runGO ds impl oa s >>= fun r ↦ embed ds (post r)) (liftP ds p) m := by
  have key : ∀ (c : (unifSpec + X).Domain) (x : OracleComp (unifSpec + G) ((unifSpec + X).Range c × σ))
      (k : (unifSpec + X).Range c → OracleComp ((ds + unifSpec) + X) α)
      (_ : ∀ u s m, (∀ t, PRes ds a₀ (k u) t →
          IsQueryBoundP ((simulateQ impl t).run s >>= post) p m) →
        IsQueryBoundP (runGO ds impl (k u) s >>= fun r ↦ embed ds (post r)) (liftP ds p) m)
      (m : ℕ)
      (_ : ∀ k₀ : (unifSpec + X).Range c → OracleComp (unifSpec + X) α,
        (∀ u, PRes ds a₀ (k u) (k₀ u)) →
        IsQueryBoundP (x >>= fun r ↦ (simulateQ impl (k₀ r.1)).run r.2 >>= post) p m),
      IsQueryBoundP (embed ds x >>= fun r ↦ runGO ds impl (k r.1) r.2 >>= fun r ↦
        embed ds (post r)) (liftP ds p) m := by
    intro c x k ih m hx
    classical
    refine bind_transfer ds p
      {f | ∃ k₀ : (unifSpec + X).Range c → OracleComp (unifSpec + X) α,
        (∀ u, PRes ds a₀ (k u) (k₀ u)) ∧
        f = fun r ↦ (simulateQ impl (k₀ r.1)).run r.2 >>= post}
      ⟨_, fun _ ↦ pure a₀, fun u ↦ .stub _, rfl⟩ _ ?_ x m ?_
    · rintro ⟨u, s'⟩ m' hf
      refine ih u s' m' fun t ht ↦ ?_
      have := hf _ ⟨Function.update (fun _ ↦ pure a₀) u t, fun u' ↦ ?_, rfl⟩
      · simpa using this
      · by_cases hu : u' = u
        · subst hu; simpa using ht
        · rw [Function.update_of_ne hu]; exact .stub _
    · rintro f ⟨k₀, hk₀, rfl⟩
      exact hx k₀ hk₀
  induction oa using ind3 (ds := ds) generalizing s m with
  | pure a =>
    rw [runGO_pure, pure_bind]
    refine embed_queryBoundP ds p _ m ?_
    simpa using h (pure a) (.pure a)
  | hds d k ih =>
    rw [runGO_bind, runGO_query_ds, bind_assoc, bind_map_left, isQueryBoundP_query_bind_iff]
    refine ⟨Or.inl id, fun u ↦ ?_⟩
    rw [ite_eq_right (show ¬ liftP ds p (.inl (.inl d)) from id)]
    exact ih u s m fun t ht ↦ h t (.ds d k u t ht)
  | hus n k ih =>
    rw [runGO_bind, runGO_query_us, bind_assoc]
    refine key (.inl n) _ k (fun u s m ↦ ih u s m) m fun k₀ hk₀ ↦ ?_
    have := h _ (.us n k k₀ hk₀)
    simpa only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, bind_assoc] using this
  | hX q k ih =>
    rw [runGO_bind, runGO_query_X, bind_assoc]
    refine key (.inr q) _ k (fun u s m ↦ ih u s m) m fun k₀ hk₀ ↦ ?_
    have := h _ (.X q k k₀ hk₀)
    simpa only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, bind_assoc] using this


/-- Black-box transfer, family form with a classical prefix. -/
theorem openShape_queryBound (pX : ℕ ⊕ ιx → Prop) [DecidablePred pX]
    (p : ℕ ⊕ ιg → Prop) [DecidablePred p] (a₀ : α) {P PK : Type}
    (pre : OracleComp (unifSpec + G) P) (pkOf : P → PK)
    (impl : P → QueryImpl (unifSpec + X) (StateT σ (OracleComp (unifSpec + G)))) (s₀ : P → σ)
    (post : P → α × σ → OracleComp (unifSpec + G) β) (qs B : ℕ)
    (hcl : ∀ A₀ : PK → OracleComp (unifSpec + X) α, (∀ pk, IsQueryBoundP (A₀ pk) pX qs) →
      IsQueryBoundP (pre >>= fun x ↦
        (simulateQ (impl x) (A₀ (pkOf x))).run (s₀ x) >>= post x) p B)
    (F : PK → OracleComp ((ds + unifSpec) + X) α)
    (hF : ∀ pk, IsQueryBoundP (F pk) (liftP ds pX) qs) :
    IsQueryBoundP (embed ds pre >>= fun x ↦
      runGO ds (impl x) (F (pkOf x)) (s₀ x) >>= fun r ↦ embed ds (post x r)) (liftP ds p) B := by
  classical
  refine bind_transfer ds p
    {f | ∃ A₀ : PK → OracleComp (unifSpec + X) α, (∀ pk, IsQueryBoundP (A₀ pk) pX qs) ∧
      f = fun x ↦ (simulateQ (impl x) (A₀ (pkOf x))).run (s₀ x) >>= post x}
    ⟨_, fun _ ↦ pure a₀, fun _ ↦ isQueryBoundP_pure _ _ _, rfl⟩ _ ?_ pre B ?_
  · intro x m hf
    refine runGO_bind_queryBound ds p a₀ (impl x) (post x) _ _ m fun t ht ↦ ?_
    have := hf _ ⟨fun pk ↦ if pk = pkOf x then t else pure a₀, fun pk ↦ ?_, rfl⟩
    · simpa using this
    · by_cases hpk : pk = pkOf x
      · subst hpk; simp only [↓reduceIte]; exact ht.queryBound ds pX qs (hF _)
      · simp only [hpk, ↓reduceIte]; exact isQueryBoundP_pure _ _ _
  · rintro f ⟨A₀, hA₀, rfl⟩
    exact hcl A₀ hA₀

/-- Black-box transfer for a run followed by a classical suffix. -/
theorem runGO_post_queryBound (pX : ℕ ⊕ ιx → Prop) [DecidablePred pX]
    (p : ℕ ⊕ ιg → Prop) [DecidablePred p] (a₀ : α)
    (impl : QueryImpl (unifSpec + X) (StateT σ (OracleComp (unifSpec + G)))) (s : σ)
    (post : α × σ → OracleComp (unifSpec + G) β) (qs B : ℕ)
    (hcl : ∀ t : OracleComp (unifSpec + X) α, IsQueryBoundP t pX qs →
      IsQueryBoundP ((simulateQ impl t).run s >>= post) p B)
    (oa : OracleComp ((ds + unifSpec) + X) α) (hF : IsQueryBoundP oa (liftP ds pX) qs) :
    IsQueryBoundP (runGO ds impl oa s >>= fun r ↦ embed ds (post r)) (liftP ds p) B :=
  runGO_bind_queryBound ds p a₀ impl post oa s B fun t ht ↦ hcl t (ht.queryBound ds pX qs hF)

lemma runGO_map (impl : QueryImpl (unifSpec + X) (StateT σ (OracleComp (unifSpec + G))))
    (oa : OracleComp ((ds + unifSpec) + X) α) (f : α → β) (s : σ) :
    runGO ds impl (f <$> oa) s = (fun p ↦ (f p.1, p.2)) <$> runGO ds impl oa s := by
  simp [runGO]

/-- Black-box transfer for a bare run (any output type). -/
theorem runGO_queryBound (pX : ℕ ⊕ ιx → Prop) [DecidablePred pX]
    (p : ℕ ⊕ ιg → Prop) [DecidablePred p]
    (impl : QueryImpl (unifSpec + X) (StateT σ (OracleComp (unifSpec + G)))) (s : σ) (qs B : ℕ)
    (hcl : ∀ {γ : Type} (t : OracleComp (unifSpec + X) γ), IsQueryBoundP t pX qs →
      IsQueryBoundP ((simulateQ impl t).run s) p B)
    (oa : OracleComp ((ds + unifSpec) + X) α) (hF : IsQueryBoundP oa (liftP ds pX) qs) :
    IsQueryBoundP (runGO ds impl oa s) (liftP ds p) B := by
  have := runGO_bind_queryBound ds p (none : Option α) impl (fun r ↦ pure r) (some <$> oa) s B
    fun t ht ↦ by
      simpa using hcl t (ht.queryBound ds pX qs ((isQueryBoundP_map_iff _ _ _).2 hF))
  simpa [runGO_map] using this

/-- Black-box transfer, family form with two classical prefixes and a pure suffix. -/
theorem openShape2_queryBound (pX : ℕ ⊕ ιx → Prop) [DecidablePred pX]
    (p : ℕ ⊕ ιg → Prop) [DecidablePred p] (a₀ : α) {P₁ P₂ PK : Type}
    (pre₁ : OracleComp (unifSpec + G) P₁) (pre₂ : P₁ → OracleComp (unifSpec + G) P₂)
    (pkOf : P₁ → P₂ → PK)
    (impl : P₁ → P₂ → QueryImpl (unifSpec + X) (StateT σ (OracleComp (unifSpec + G)))) (s₀ : σ)
    (post : P₁ → P₂ → α × σ → β) (qs B : ℕ)
    (hcl : ∀ A₀ : PK → OracleComp (unifSpec + X) α, (∀ pk, IsQueryBoundP (A₀ pk) pX qs) →
      IsQueryBoundP (pre₁ >>= fun a ↦ pre₂ a >>= fun b ↦
        (simulateQ (impl a b) (A₀ (pkOf a b))).run s₀ >>= fun r ↦ pure (post a b r)) p B)
    (F : PK → OracleComp ((ds + unifSpec) + X) α)
    (hF : ∀ pk, IsQueryBoundP (F pk) (liftP ds pX) qs) :
    IsQueryBoundP (embed ds pre₁ >>= fun a ↦ embed ds (pre₂ a) >>= fun b ↦
      runGO ds (impl a b) (F (pkOf a b)) s₀ >>= fun r ↦ pure (post a b r)) (liftP ds p) B := by
  have h := openShape_queryBound ds pX p a₀ (pre₁ >>= fun a ↦ pre₂ a >>= fun b ↦ pure (a, b))
    (fun x ↦ pkOf x.1 x.2) (fun x ↦ impl x.1 x.2) (fun _ ↦ s₀)
    (fun x r ↦ pure (post x.1 x.2 r)) qs B
    (fun A₀ hA₀ ↦ by simpa only [bind_assoc, pure_bind] using hcl A₀ hA₀) F hF
  simpa only [embed_bind, embed_pure, bind_assoc, pure_bind] using h

/-- Black-box transfer for `openAdv`. -/
theorem openAdv_queryBound (pX : ℕ ⊕ ιx → Prop) [DecidablePred pX]
    (p : ℕ ⊕ ιg → Prop) [DecidablePred p] (a₀ : α) {P PK : Type}
    (pre : OracleComp (unifSpec + G) P) (pkOf : P → PK)
    (impl : P → QueryImpl (unifSpec + X) (StateT σ (OracleComp (unifSpec + G)))) (s₀ : σ)
    (post : P → α × σ → Bool) (qs B : ℕ)
    (hcl : ∀ A₀ : PK → OracleComp (unifSpec + X) α, (∀ pk, IsQueryBoundP (A₀ pk) pX qs) →
      IsQueryBoundP (pre >>= fun x ↦
        (simulateQ (impl x) (A₀ (pkOf x))).run s₀ >>= fun r ↦ pure (post x r)) p B)
    (F : PK → OracleComp ((ds + unifSpec) + X) α)
    (hF : ∀ pk, IsQueryBoundP (F pk) (liftP ds pX) qs) :
    IsQueryBoundP (openAdv ds pre pkOf impl s₀ post F) (liftP ds p) B := by
  have h := openShape_queryBound ds pX p a₀ pre pkOf impl (fun _ ↦ s₀)
    (fun x r ↦ pure (post x r)) qs B hcl F hF
  simpa only [openAdv, embed_pure] using h

/-- A stateless wrapper that classically keeps the number of game queries keeps it on general
programs. -/
theorem wrapS_queryBound_isRight (w : QueryImpl (unifSpec + G) (OracleComp (unifSpec + G2)))
    (hw : ∀ {γ : Type} (t : OracleComp (unifSpec + G) γ) (n : ℕ),
      IsQueryBoundP t (fun i ↦ i.isRight = true) n →
      IsQueryBoundP (simulateQ w t) (fun i ↦ i.isRight = true) n)
    (P : OracleComp ((ds + unifSpec) + G) α) (n : ℕ)
    (h : IsQueryBoundP P (fun i ↦ i.isRight = true) n) :
    IsQueryBoundP (wrapS ds w P) (fun i ↦ i.isRight = true) n := by
  have hq : ∀ (c : (unifSpec + G).Domain) (m : ℕ),
      IsQueryBoundP (liftM ((unifSpec + G).query c) : OracleComp (unifSpec + G) _)
        (fun i ↦ i.isRight = true) m →
      IsQueryBoundP (embed ds (w c)) (fun i ↦ i.isRight = true) m := fun c m hc ↦ by
    have := hw _ m hc
    rw [simulateQ_spec_query] at this
    exact embed_queryBound ds _ m this
  unfold wrapS
  apply h.simulateQ_of_step
  · rintro ((d | m) | x) ht
    · simp at ht
    · simp at ht
    · exact hq (.inr x) 1 (by simp)
  · rintro ((d | m) | x) ht
    · simp [gImplS]
    · exact hq (.inl m) 0 (by simp)
    · simp at ht

/-! ## Interpretation of open runs -/

/-- Interpreting the answers of an open run by a stateless handler: step-wise. -/
theorem wrapS_runGO (w : QueryImpl (unifSpec + G) (OracleComp (unifSpec + G2)))
    (impl : QueryImpl (unifSpec + X) (StateT σ (OracleComp (unifSpec + G))))
    (impl' : QueryImpl (unifSpec + X) (StateT σ (OracleComp (unifSpec + G2))))
    (hstep : ∀ t s, simulateQ w ((impl t).run s) = (impl' t).run s)
    (oa : OracleComp ((ds + unifSpec) + X) α) (s : σ) :
    wrapS ds w (runGO ds impl oa s) = runGO ds impl' oa s := by
  induction oa using ind3 (ds := ds) generalizing s with
  | pure a => simp
  | hds d k ih =>
    rw [runGO_bind, runGO_bind, runGO_query_ds, runGO_query_ds, wrapS_bind, wrapS_map,
      bind_map_left, bind_map_left]
    have : wrapS ds w (liftM (((ds + unifSpec) + G).query (.inl (.inl d)))) =
        (liftM (((ds + unifSpec) + G2).query (.inl (.inl d))) :
          OracleComp ((ds + unifSpec) + G2) _) := by
      unfold wrapS; rw [simulateQ_spec_query]; rfl
    rw [this]
    exact bind_congr fun u ↦ ih u s
  | hus n k ih =>
    rw [runGO_bind, runGO_bind, runGO_query_us, runGO_query_us, wrapS_bind, wrapS_embed, hstep]
    exact bind_congr fun u ↦ ih _ _
  | hX q k ih =>
    rw [runGO_bind, runGO_bind, runGO_query_X, runGO_query_X, wrapS_bind, wrapS_embed, hstep]
    exact bind_congr fun u ↦ ih _ _

/-- A closed general program as an open one (it makes no game query): the canonical lift. -/
def liftG {α : Type} (oa : OracleComp (gSpec ds) α) : OracleComp ((ds + unifSpec) + G) α :=
  liftM oa

@[simp] lemma liftG_pure (a : α) : liftG ds (G := G) (pure a) = pure a := by simp [liftG]

lemma liftG_bind (oa : OracleComp (gSpec ds) α) (f : α → OracleComp (gSpec ds) β) :
    liftG ds (G := G) (oa >>= f) = liftG ds oa >>= fun a ↦ liftG ds (f a) := by simp [liftG]

lemma liftG_map (oa : OracleComp (gSpec ds) α) (f : α → β) :
    liftG ds (G := G) (f <$> oa) = f <$> liftG ds oa := by simp [liftG]

/-- Classical sampling code, lifted either way. -/
lemma embed_liftM (p : ProbComp α) :
    embed ds (liftM p : OracleComp (unifSpec + G) α) = liftG ds (liftR ds p) := by
  induction p using OracleComp.inductionOn with
  | pure a => simp [liftG]
  | query_bind n k ih =>
    simp only [liftM_bind, embed_bind, liftR_bind, liftG, ih]
    congr 1

/-- An open run whose handler steps are closed is the closed run. -/
theorem runGO_closed (impl' : QueryImpl (unifSpec + X) (StateT σ (OracleComp (unifSpec + G))))
    (H : QueryImpl (unifSpec + X) (StateT σ ProbComp))
    (hstep : ∀ t s, (impl' t).run s = (liftM ((H t).run s) : OracleComp (unifSpec + G) _))
    (oa : OracleComp ((ds + unifSpec) + X) α) (s : σ) :
    runGO ds impl' oa s = liftG ds (runG ds H oa s) := by
  have hus : ∀ n s, runG ds H (liftM (((ds + unifSpec) + X).query (.inl (.inr n)))) s =
      liftR ds ((H (.inl n)).run s) := fun n s ↦ by
    unfold runG; rw [simulateQ_spec_query]; rfl
  have hX : ∀ q s, runG ds H (liftM (((ds + unifSpec) + X).query (.inr q))) s =
      liftR ds ((H (.inr q)).run s) := fun q s ↦ by
    unfold runG; rw [simulateQ_spec_query]; rfl
  induction oa using ind3 (ds := ds) generalizing s with
  | pure a => simp
  | hds d k ih =>
    have hd : runG ds H (liftM (((ds + unifSpec) + X).query (.inl (.inl d)))) s =
        (fun u ↦ (u, s)) <$> (liftM ((gSpec ds).query (.inl d)) : OracleComp (gSpec ds) _) := by
      unfold runG; rw [simulateQ_spec_query]; rfl
    rw [runGO_bind, runG_bind, runGO_query_ds, hd, liftG_bind, liftG_map, bind_map_left,
      bind_map_left]
    refine congrArg₂ _ ?_ (funext fun u ↦ ih u s)
    rfl
  | hus n k ih =>
    rw [runGO_bind, runG_bind, runGO_query_us, hus, hstep, embed_liftM, liftG_bind]
    exact bind_congr fun u ↦ ih _ _
  | hX q k ih =>
    rw [runGO_bind, runG_bind, runGO_query_X, hX, hstep, embed_liftM, liftG_bind]
    exact bind_congr fun u ↦ ih _ _

/-- Interpreting an open run by a stateless handler that closes every step gives the closed
run. -/
theorem wrapS_runGO_closed (w : QueryImpl (unifSpec + G) (OracleComp (unifSpec + G2)))
    (impl : QueryImpl (unifSpec + X) (StateT σ (OracleComp (unifSpec + G))))
    (H : QueryImpl (unifSpec + X) (StateT σ ProbComp))
    (hstep : ∀ t s, simulateQ w ((impl t).run s) =
      (liftM ((H t).run s) : OracleComp (unifSpec + G2) _))
    (oa : OracleComp ((ds + unifSpec) + X) α) (s : σ) :
    wrapS ds w (runGO ds impl oa s) = liftG ds (runG ds H oa s) :=
  (wrapS_runGO ds w impl (fun t ↦ StateT.mk fun s ↦ liftM ((H t).run s)) hstep oa s).trans
    (runGO_closed ds _ H (fun _ _ ↦ rfl) oa s)

end generic

/-! ## SLH-DSA: harness handlers and their interpretation -/

attribute [local irreducible] arityTargets tcrTargets

variable {κ : Type} (ds : OracleSpec κ)
variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]
variable (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
  (pkSeedDist : ProbComp prims.PkSeed)
variable {ι : Type} (gspec : OracleSpec ι)

attribute [local instance] Lazy.openQ Lazy.closedQ

/-- The kind of a query of a general open program; `ds`-queries are private coins. -/
def kindG {κh D : Type} : (κ ⊕ ℕ) ⊕ (ι ⊕ (D ⊕ κh)) → Lazy.Kind
  | .inl _ => .unif
  | .inr x => Lazy.kind (ι := ι) (D := D) (κ := κh) (.inr x)

lemma liftP_kind_iff {κh D : Type} (K : Lazy.Kind) (hK : K ≠ .unif)
    (i : (κ ⊕ ℕ) ⊕ (ι ⊕ (D ⊕ κh))) :
    liftP ds (fun t : ℕ ⊕ (ι ⊕ (D ⊕ κh)) ↦ Lazy.kind t = K) i ↔ kindG i = K := by
  rcases i with (d | n) | x
  · simp only [liftP, kindG, false_iff]; exact fun h ↦ hK h.symm
  · rfl
  · rfl

/-- Kind bounds in the two spellings. -/
lemma kindG_iff_liftP {κh D : Type} {hspec : OracleSpec κh} {V α : Type} (K : Lazy.Kind)
    (hK : K ≠ .unif)
    (oa : OracleComp ((ds + unifSpec) + (gspec + ((D →ₒ V) + hspec))) α) (n : ℕ) :
    IsQueryBoundP oa (fun t ↦ kindG t = K) n ↔
      IsQueryBoundP oa (liftP ds (fun t : ℕ ⊕ (ι ⊕ (D ⊕ κh)) ↦ Lazy.kind t = K)) n :=
  isQueryBoundP_congr_pred fun i ↦ (liftP_kind_iff ds K hK i).symm

/-- The handler of `runForgerLog` with the `G2` randomizer (open programs). -/
noncomputable def logHarnessO (pk : PublicKeyCore prims.core)
    (signO : List Byte → prims.Y →
      OracleComp (Lazy.OSpec prims gspec) (GeneralScheme.SignatureCore vp prims.core)) :
    QueryImpl (unifSpec + (List Byte →ₒ GeneralScheme.SignatureCore vp prims.core))
      (StateT (G2Log prims) (OracleComp (Lazy.OSpec prims gspec))) :=
  (QueryImpl.ofLift unifSpec (OracleComp (Lazy.OSpec prims gspec))).liftTarget
      (StateT (G2Log prims) (OracleComp (Lazy.OSpec prims gspec))) +
    logSignOracle optRand pk lazyRandomizerLift signO

/-- The handler of `g2RunWith`. -/
noncomputable def g2Harness (pk : PublicKeyCore prims.core)
    (signR : List Byte → prims.Y → GeneralScheme.SignatureCore vp prims.core) :
    QueryImpl (unifSpec + (List Byte →ₒ GeneralScheme.SignatureCore vp prims.core))
      (StateT (G2Log prims) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (G2Log prims) ProbComp) +
    g2SignOracle optRand pk signR

/-- One step of the open harness under the table interpretation (any randomizer/signer). -/
theorem logHarness_tbl_step (tbl : SecretTable vp prims) (pk : PublicKeyCore prims.core)
    (randO : G2Log prims → List Byte → prims.Y → OracleComp (Lazy.OSpec prims gspec) prims.Y)
    (signO : List Byte → prims.Y → OracleComp (Lazy.OSpec prims gspec)
      (GeneralScheme.SignatureCore vp prims.core))
    (randC : G2Log prims → List Byte → prims.Y → OracleComp (unifSpec + gspec) prims.Y)
    (signC : List Byte → prims.Y → OracleComp (unifSpec + gspec)
      (GeneralScheme.SignatureCore vp prims.core))
    (hrand : ∀ log m a, simulateQ (Lazy.tblImpl (PublicHash.impl prims) tbl) (randO log m a) =
      randC log m a)
    (hsign : ∀ m R, simulateQ (Lazy.tblImpl (PublicHash.impl prims) tbl) (signO m R) = signC m R)
    (t : (unifSpec + (List Byte →ₒ GeneralScheme.SignatureCore vp prims.core)).Domain)
    (s : G2Log prims) :
    simulateQ (Lazy.tblImpl (gspec := gspec) (PublicHash.impl prims) tbl)
        ((((QueryImpl.ofLift unifSpec (OracleComp (Lazy.OSpec prims gspec))).liftTarget
            (StateT (G2Log prims) (OracleComp (Lazy.OSpec prims gspec))) +
          logSignOracle optRand pk randO signO) t).run s) =
      (((QueryImpl.ofLift unifSpec (OracleComp (unifSpec + gspec))).liftTarget
            (StateT (G2Log prims) (OracleComp (unifSpec + gspec))) +
          logSignOracle optRand pk randC signC) t).run s := by
  cases t with
  | inl n =>
    simp
    exact Lazy.simulateQ_tblImpl_liftM (PublicHash.impl prims) tbl (liftM (unifSpec.query n))
  | inr m =>
    simp [logSignOracle, hrand, hsign, Lazy.simulateQ_tblImpl_liftM]

/-- One step of the open harness with a signer that the table interpretation makes pure: the
step of `g2RunWith`. -/
theorem logHarnessO_tbl_step (tbl : SecretTable vp prims) (pk : PublicKeyCore prims.core)
    (signO : List Byte → prims.Y → OracleComp (Lazy.OSpec prims gspec)
      (GeneralScheme.SignatureCore vp prims.core))
    (signR : List Byte → prims.Y → GeneralScheme.SignatureCore vp prims.core)
    (hsign : ∀ m R, simulateQ (Lazy.tblImpl (PublicHash.impl prims) tbl) (signO m R) =
      pure (signR m R))
    (t : (unifSpec + (List Byte →ₒ GeneralScheme.SignatureCore vp prims.core)).Domain)
    (s : G2Log prims) :
    simulateQ (Lazy.tblImpl (gspec := gspec) (PublicHash.impl prims) tbl)
        ((logHarnessO optRand gspec pk signO t).run s) =
      (liftM ((g2Harness optRand pk signR t).run s) : OracleComp (unifSpec + gspec) _) := by
  have h1 := logHarness_tbl_step optRand gspec tbl pk lazyRandomizerLift signO lazyRandomizerLift
    (fun m R ↦ pure (signR m R))
    (fun log m a ↦ Lazy.simulateQ_tblImpl_liftM (PublicHash.impl prims) tbl _) hsign t s
  have h2 := Resources2.wots_logImpl_run_eq (optRand := optRand) (spec := gspec) pk signR
    (liftM ((unifSpec + (List Byte →ₒ GeneralScheme.SignatureCore vp prims.core)).query t)) s
  rw [simulateQ_spec_query, simulateQ_spec_query] at h2
  exact h1.trans h2


/-! ## (2) Phase 2 of `bTcrArMG` -/

/-- The part of `Resources2.memoForgeOpen` after the forger's run: `H_msg` of the forgery,
verification with the interleaved collision search. -/
noncomputable def memoTailO (L : List (prims.AdrsKey × List prims.Y)) (pkSeed : prims.PkSeed)
    (root : prims.Y) (z : List Byte × GeneralScheme.SignatureCore vp prims.core) :
    OracleComp (Lazy.OSpec prims gspec) (ℕ × List prims.Y) := do
  let dg ← (PublicHash.hmsg prims.core z.2.randomness pkSeed root z.1 :
    OracleComp (Lazy.OSpec prims gspec) (Bytes vp.params.m))
  let c ← (simulateQ (Resources2.collO (gspec := gspec) pkSeed L)
    (Resources2.verifyFree pkSeed (splitDigest vp.params dg) z.2)).run none
  return c.2.getD (0, [])

/-- **`Resources2.memoForgeOpen` around a general-spec forger family**: the classical open code,
the forger run by `runGO` against the handler of `runForgerLog`. -/
noncomputable def memoForgeOpenG (F : GFam ds vp prims)
    (L : List (prims.AdrsKey × List prims.Y)) (pkSeed : prims.PkSeed) :
    OracleComp ((ds + unifSpec) + (gspec + ((SecIdx →ₒ prims.Y) + publicHashSpec prims.core)))
      (ℕ × List prims.Y) :=
  embed ds (Lazy.openKeygen prims gspec pkSeed) >>= fun root ↦
    runGO ds (logHarnessO optRand gspec ⟨pkSeed, root⟩
      (fun m R ↦ Lazy.openSign prims gspec m pkSeed root R)) (F ⟨pkSeed, root⟩) [] >>= fun z ↦
      embed ds (memoTailO gspec L pkSeed root z.1)

variable {optRand pkSeedDist}

/-- The classical open program in the shape of `memoForgeOpenG`. -/
theorem memoForgeOpen_shape (A : Forger vp prims optRand pkSeedDist)
    (L : List (prims.AdrsKey × List prims.Y)) (pkSeed : prims.PkSeed) :
    Resources2.memoForgeOpen (gspec := gspec) A L pkSeed =
      Lazy.openKeygen prims gspec pkSeed >>= fun root ↦
        (simulateQ (logHarnessO optRand gspec ⟨pkSeed, root⟩
          (fun m R ↦ Lazy.openSign prims gspec m pkSeed root R)) (A.main ⟨pkSeed, root⟩)).run []
          >>= fun z ↦ memoTailO gspec L pkSeed root z.1 := rfl

/-- Naturality: on a classical forger, `memoForgeOpenG` is `memoForgeOpen`. -/
theorem memoForgeOpenG_embed (A : Forger vp prims optRand pkSeedDist)
    (L : List (prims.AdrsKey × List prims.Y)) (pkSeed : prims.PkSeed) :
    memoForgeOpenG ds optRand gspec (fun pk ↦ embed ds (A.main pk)) L pkSeed =
      embed ds (Resources2.memoForgeOpen (gspec := gspec) A L pkSeed) := by
  rw [memoForgeOpen_shape]
  simp only [memoForgeOpenG, runGO_embed, embed_bind]

theorem memoTailO_tbl (tbl : SecretTable vp prims) (L : List (prims.AdrsKey × List prims.Y))
    (pkSeed : prims.PkSeed) (z : List Byte × GeneralScheme.SignatureCore vp prims.core) :
    simulateQ (Lazy.tblImpl (gspec := gspec) (PublicHash.impl prims) tbl)
        (memoTailO gspec L pkSeed (idealRoot vp prims tbl pkSeed) z) =
      pure ((findCollisionM pkSeed L
        (verifyCalls (idealPk vp prims tbl pkSeed) z.1 z.2)).getD (0, [])) := by
  have hmsg : ∀ (R : prims.Y) (root : prims.Y) (m : List Byte),
      simulateQ (Lazy.tblImpl (gspec := gspec) (PublicHash.impl prims) tbl)
        (PublicHash.hmsg prims.core R pkSeed root m :
          OracleComp (Lazy.OSpec prims gspec) (Bytes vp.params.m)) =
      pure (prims.Hmsg R pkSeed root m) := by
    intro R root m
    simp [PublicHash.hmsg, Lazy.tblImpl, PublicHash.impl]
  unfold memoTailO
  simp only [simulateQ_bind, simulateQ_pure]
  rw [hmsg, pure_bind]
  have hc := Resources2.collO_tbl (gspec := gspec) tbl pkSeed L
    (Resources2.verifyFree pkSeed (splitDigest vp.params
      (prims.Hmsg z.2.randomness pkSeed (idealRoot vp prims tbl pkSeed) z.1)) z.2) []
  have hnil : findCollisionM pkSeed L [] = none := rfl
  rw [hnil] at hc
  rw [hc, pure_bind, Resources2.verifyCalls_eq_free]
  rfl

/-- **(2a) Phase 2 of `bTcrArMG n F`** is the general interpretation (secret oracle = the table,
hash queries evaluated by `prims`, `ds`-queries forwarded) of the open program
`memoForgeOpenG F L pk`, followed by the hash-free output translation `classOut`. -/
theorem bTcrArMG_forge_open (n : ℕ) (F : GFam ds vp prims) (tbl : SecretTable vp prims)
    (L : List (prims.AdrsKey × List prims.Y)) (pk : prims.PkSeed) :
    liftG ds (G := gspec) ((bTcrArMG ds optRand pkSeedDist n F).forge (tbl, L) pk) =
      wrapS ds (Lazy.tblImpl (gspec := gspec) (PublicHash.impl prims) tbl)
        (memoForgeOpenG ds optRand gspec F L pk) >>= fun jm ↦
          pure (classOut prims n L jm) := by
  show liftG ds (memoForgeG ds optRand n F (tbl, L) pk) = _
  unfold memoForgeOpenG memoForgeG g2RunG g2RunWithG
  rw [wrapS_bind, wrapS_embed, Lazy.openKeygen_tbl, embed_pure, pure_bind, wrapS_bind,
    wrapS_runGO_closed ds _ _ (g2Harness optRand (idealPk vp prims tbl pk)
      (fun m R ↦ idealSign vp prims tbl m (idealPk vp prims tbl pk) R))
      (fun t s ↦ logHarnessO_tbl_step optRand gspec tbl ⟨pk, idealRoot vp prims tbl pk⟩ _ _
        (fun m R ↦ Lazy.openSign_tbl tbl m ⟨pk, idealRoot vp prims tbl pk⟩ R) t s),
    liftG_bind, bind_assoc]
  refine bind_congr fun z ↦ ?_
  rw [wrapS_embed, memoTailO_tbl, embed_pure, pure_bind, liftG_pure]

include pkSeedDist in
/-- **(2b) Own hash evaluations of phase 2 of `bTcrArMG n F`**: the classical bound. -/
theorem memoForgeOpenG_hashes (F : GFam ds vp prims) (qs : ℕ)
    (hF : ∀ pk, IsQueryBoundP (F pk) (fun i ↦ i.isRight = true) qs)
    (L : List (prims.AdrsKey × List prims.Y)) (pkSeed : prims.PkSeed) :
    IsQueryBoundP (memoForgeOpenG ds optRand gspec F L pkSeed) (fun t ↦ kindG t = .hash)
      (Lazy.keygenHashes vp + qs * Lazy.signHashes vp +
        (1 + Resources2.verifyHashes vp * 2)) := by
  rw [kindG_iff_liftP ds gspec .hash (by decide)]
  exact openShape_queryBound ds (fun i ↦ i.isRight = true) _ ([], constSig default) _
    (fun root ↦ (⟨pkSeed, root⟩ : PublicKeyCore prims.core)) _ (fun _ ↦ []) _ qs _
    (fun A₀ hA₀ ↦ Resources2.memoForgeOpen_hashes (gspec := gspec)
      (⟨A₀⟩ : Forger vp prims optRand pkSeedDist) qs hA₀ L pkSeed)
    F fun pk ↦ (isRight_iff_liftP ds _ _).1 (hF pk)

/-! ## (2) Phase 2 of `rUdG`, `rPreG`, `rTcrTG` -/

variable (optRand) in
/-- **`Resources2.wotsPhase2O` around a general-spec forger family.** -/
noncomputable def wotsPhase2OG (F : GFam ds vp prims) (tbl : SecretTable vp prims)
    (hist : List (WotsGame.Entry prims)) (root : prims.Y) (pk : prims.PkSeed) {β : Type}
    (tail : ℕ × prims.Y × WotsSig vp.params prims.core → OracleComp (Lazy.OSpec prims gspec) β) :
    OracleComp ((ds + unifSpec) + (gspec + ((SecIdx →ₒ prims.Y) + publicHashSpec prims.core))) β :=
  runGO ds (logHarnessO optRand gspec ⟨pk, root⟩ (Resources2.wotsSignFromHistO hist ⟨pk, root⟩))
      (F ⟨pk, root⟩) [] >>= fun r ↦
    embed ds (tail (wotsAnswer tbl hist ⟨pk, root⟩ r.1.1 r.1.2))

theorem wotsPhase2O_shape (A : Forger vp prims optRand pkSeedDist) (tbl : SecretTable vp prims)
    (hist : List (WotsGame.Entry prims)) (root : prims.Y) (pk : prims.PkSeed) {β : Type}
    (tail : ℕ × prims.Y × WotsSig vp.params prims.core → OracleComp (Lazy.OSpec prims gspec) β) :
    Resources2.wotsPhase2O (gspec := gspec) A tbl hist root pk tail =
      (simulateQ (logHarnessO optRand gspec ⟨pk, root⟩
        (Resources2.wotsSignFromHistO hist ⟨pk, root⟩)) (A.main ⟨pk, root⟩)).run [] >>= fun r ↦
        tail (wotsAnswer tbl hist ⟨pk, root⟩ r.1.1 r.1.2) := rfl

/-- Naturality: on a classical forger, `wotsPhase2OG` is `wotsPhase2O`. -/
theorem wotsPhase2OG_embed (A : Forger vp prims optRand pkSeedDist) (tbl : SecretTable vp prims)
    (hist : List (WotsGame.Entry prims)) (root : prims.Y) (pk : prims.PkSeed) {β : Type}
    (tail : ℕ × prims.Y × WotsSig vp.params prims.core → OracleComp (Lazy.OSpec prims gspec) β) :
    wotsPhase2OG ds optRand gspec (fun pk ↦ embed ds (A.main pk)) tbl hist root pk tail =
      embed ds (Resources2.wotsPhase2O (gspec := gspec) A tbl hist root pk tail) := by
  rw [wotsPhase2O_shape]
  simp only [wotsPhase2OG, runGO_embed, embed_bind]

/-- Interpretation of `wotsPhase2OG` with a tail that the table interpretation makes pure. -/
theorem wotsPhase2OG_tbl (F : GFam ds vp prims) (tbl : SecretTable vp prims)
    (hist : List (WotsGame.Entry prims)) (root : prims.Y) (pk : prims.PkSeed) {β : Type}
    (tail : ℕ × prims.Y × WotsSig vp.params prims.core → OracleComp (Lazy.OSpec prims gspec) β)
    (tailP : ℕ × prims.Y × WotsSig vp.params prims.core → β)
    (h : ∀ x, simulateQ (Lazy.tblImpl (gspec := gspec) (PublicHash.impl prims) tbl) (tail x) =
      pure (tailP x)) :
    wrapS ds (Lazy.tblImpl (gspec := gspec) (PublicHash.impl prims) tbl)
        (wotsPhase2OG ds optRand gspec F tbl hist root pk tail) =
      liftG ds (bWotsForgeG ds optRand F (tbl, hist, root) pk >>= fun x ↦ pure (tailP x)) := by
  unfold wotsPhase2OG bWotsForgeG g2RunWithG
  rw [wrapS_bind, wrapS_runGO_closed ds _ _ (g2Harness optRand ⟨pk, root⟩
      (signFromHist tbl hist ⟨pk, root⟩))
      (fun t s ↦ logHarnessO_tbl_step optRand gspec tbl ⟨pk, root⟩ _ _
        (fun m R ↦ Resources2.wotsSignFromHistO_tbl tbl hist ⟨pk, root⟩ m R) t s),
    bind_assoc, liftG_bind]
  refine bind_congr fun z ↦ ?_
  rw [wrapS_embed, h, embed_pure, pure_bind, liftG_pure]

/-- **(2a) Phase 2 of `rUdG F`** is the general interpretation of an open program. -/
theorem rUdG_phase2 (F : GFam ds vp prims) (tbl : SecretTable vp prims)
    (hist hist2 : List (WotsGame.Entry prims)) (root : prims.Y) (pk : prims.PkSeed) :
    liftG ds (G := gspec)
        ((rUdG ds optRand pkSeedDist F).distinguish ((tbl, hist, root), hist2) pk) =
      wrapS ds (Lazy.tblImpl (gspec := gspec) (PublicHash.impl prims) tbl)
        (wotsPhase2OG ds optRand gspec F tbl hist root pk
          fun x ↦ Resources2.wotsWinO pk hist2 x.1 x.2.1 x.2.2) :=
  (wotsPhase2OG_tbl ds gspec F tbl hist root pk _ (fun x ↦ WotsGame.win pk hist2 x.1 x.2.1 x.2.2)
    (fun x ↦ Resources2.wotsWinO_tbl tbl pk hist2 x.1 x.2.1 x.2.2)).symm

/-- **(2a) Phase 2 of `rPreG F`** is the general interpretation of an open program. -/
theorem rPreG_phase2 (F : GFam ds vp prims) (tbl : SecretTable vp prims)
    (hist hist2 : List (WotsGame.Entry prims)) (root : prims.Y) (pk : prims.PkSeed) :
    liftG ds (G := gspec)
        ((rPreG ds optRand pkSeedDist F).invert ((tbl, hist, root), hist2) pk) =
      wrapS ds (Lazy.tblImpl (gspec := gspec) (PublicHash.impl prims) tbl)
        (wotsPhase2OG ds optRand gspec F tbl hist root pk
          fun x ↦ Resources2.wotsPreAnswerO pk hist2 x.1 x.2.1 x.2.2) :=
  (wotsPhase2OG_tbl ds gspec F tbl hist root pk _ (fun x ↦ preAnswer pk hist2 x.1 x.2.1 x.2.2)
    (fun x ↦ Resources2.wotsPreAnswerO_tbl tbl pk hist2 x.1 x.2.1 x.2.2)).symm

/-- **(2a) Phase 2 of `rTcrTG F`** is the general interpretation of an open program. -/
theorem rTcrTG_phase2 (F : GFam ds vp prims) (tbl : SecretTable vp prims)
    (hist hist2 : List (WotsGame.Entry prims)) (root : prims.Y) (pk : prims.PkSeed) :
    liftG ds (G := gspec)
        ((rTcrTG ds optRand pkSeedDist F).forge ((tbl, hist, root), hist2) pk) =
      wrapS ds (Lazy.tblImpl (gspec := gspec) (PublicHash.impl prims) tbl)
        (wotsPhase2OG ds optRand gspec F tbl hist root pk
          fun x ↦ Resources2.wotsTcrAnswerO pk hist2 x.1 x.2.1 x.2.2) :=
  (wotsPhase2OG_tbl ds gspec F tbl hist root pk _ (fun x ↦ tcrAnswer pk hist2 x.1 x.2.1 x.2.2)
    (fun x ↦ Resources2.wotsTcrAnswerO_tbl tbl pk hist2 x.1 x.2.1 x.2.2)).symm

include pkSeedDist in
/-- Black-box transfer of a kind bound of `wotsPhase2O` to `wotsPhase2OG`. -/
theorem wotsPhase2OG_kindBound (K : Lazy.Kind) (hK : K ≠ .unif) (F : GFam ds vp prims) (qs B : ℕ)
    (hF : ∀ pk, IsQueryBoundP (F pk) (fun i ↦ i.isRight = true) qs)
    (tbl : SecretTable vp prims) (hist : List (WotsGame.Entry prims)) (root : prims.Y)
    (pk : prims.PkSeed) {β : Type}
    (tail : ℕ × prims.Y × WotsSig vp.params prims.core → OracleComp (Lazy.OSpec prims gspec) β)
    (hcl : ∀ A : Forger vp prims optRand pkSeedDist,
      (∀ pk, IsQueryBoundP (A.main pk) (fun i ↦ i.isRight = true) qs) →
      IsQueryBoundP (Resources2.wotsPhase2O (gspec := gspec) A tbl hist root pk tail)
        (fun t ↦ Lazy.kind t = K) B) :
    IsQueryBoundP (wotsPhase2OG ds optRand gspec F tbl hist root pk tail)
      (fun t ↦ kindG t = K) B := by
  rw [kindG_iff_liftP ds gspec K hK]
  exact runGO_post_queryBound ds (fun i ↦ i.isRight = true) _ ([], constSig default) _ [] _ qs B
    (fun t ht ↦ hcl ⟨fun _ ↦ t⟩ fun _ ↦ ht) _ ((isRight_iff_liftP ds _ _).1 (hF _))

include pkSeedDist in
/-- **(2b) Own hash evaluations of phase 2 of `rUdG F`** (without the pure tail `wotsAnswer`). -/
theorem rUdG_phase2_hashes (F : GFam ds vp prims) (qs : ℕ)
    (hF : ∀ pk, IsQueryBoundP (F pk) (fun i ↦ i.isRight = true) qs)
    (tbl : SecretTable vp prims) (hist hist2 : List (WotsGame.Entry prims)) (root : prims.Y)
    (pk : prims.PkSeed) :
    IsQueryBoundP (wotsPhase2OG ds optRand gspec F tbl hist root pk
        fun x ↦ Resources2.wotsWinO pk hist2 x.1 x.2.1 x.2.2) (fun t ↦ kindG t = .hash)
      (qs * Resources2.wotsSignHistHashes vp + Resources2.wotsWinHashes vp) :=
  wotsPhase2OG_kindBound (pkSeedDist := pkSeedDist) ds gspec .hash (by decide) F qs _ hF tbl hist
    root pk _ fun A hA ↦ Resources2.wots_rUd_phase2_hashes A qs hA tbl hist hist2 root pk

include pkSeedDist in
/-- **(2b) Own hash evaluations of phase 2 of `rPreG F`**. -/
theorem rPreG_phase2_hashes (F : GFam ds vp prims) (qs : ℕ)
    (hF : ∀ pk, IsQueryBoundP (F pk) (fun i ↦ i.isRight = true) qs)
    (tbl : SecretTable vp prims) (hist hist2 : List (WotsGame.Entry prims)) (root : prims.Y)
    (pk : prims.PkSeed) :
    IsQueryBoundP (wotsPhase2OG ds optRand gspec F tbl hist root pk
        fun x ↦ Resources2.wotsPreAnswerO pk hist2 x.1 x.2.1 x.2.2) (fun t ↦ kindG t = .hash)
      (qs * Resources2.wotsSignHistHashes vp + Resources2.wotsPreHashes vp) :=
  wotsPhase2OG_kindBound (pkSeedDist := pkSeedDist) ds gspec .hash (by decide) F qs _ hF tbl hist
    root pk _ fun A hA ↦ Resources2.wots_rPre_phase2_hashes A qs hA tbl hist hist2 root pk

include pkSeedDist in
/-- **(2b) Own hash evaluations of phase 2 of `rTcrTG F`**. -/
theorem rTcrTG_phase2_hashes (F : GFam ds vp prims) (qs : ℕ)
    (hF : ∀ pk, IsQueryBoundP (F pk) (fun i ↦ i.isRight = true) qs)
    (tbl : SecretTable vp prims) (hist hist2 : List (WotsGame.Entry prims)) (root : prims.Y)
    (pk : prims.PkSeed) :
    IsQueryBoundP (wotsPhase2OG ds optRand gspec F tbl hist root pk
        fun x ↦ Resources2.wotsTcrAnswerO pk hist2 x.1 x.2.1 x.2.2) (fun t ↦ kindG t = .hash)
      (qs * Resources2.wotsSignHistHashes vp + Resources2.wotsTcrHashes vp) :=
  wotsPhase2OG_kindBound (pkSeedDist := pkSeedDist) ds gspec .hash (by decide) F qs _ hF tbl hist
    root pk _ fun A hA ↦ Resources2.wots_rTcr_phase2_hashes A qs hA tbl hist hist2 root pk

/-! ## (2) Phase 2 of `toDsprG`, `toTcrG` -/

variable (optRand) in
/-- **`Resources2.findOpenFull` around a general-spec forger family.** -/
noncomputable def findOpenFullG (F : GFam ds vp prims) (pkSeed : prims.PkSeed)
    (ys : List prims.Y) :
    OracleComp ((ds + unifSpec) +
      (Resources2.forsG prims + ((SecIdx →ₒ prims.Y) + publicHashSpec prims.core)))
      (ℕ × prims.Y) :=
  embed ds (Lazy.openKeygen prims (Resources2.forsG prims) pkSeed) >>= fun root ↦
    runGO ds (logHarnessO optRand (Resources2.forsG prims) ⟨pkSeed, root⟩
      (Resources2.forsSignOpen ⟨pkSeed, root⟩ ys)) (F ⟨pkSeed, root⟩) [] >>= fun z ↦
      embed ds (Resources2.findAnswerO ⟨pkSeed, root⟩ ys z.2 z.1.1 z.1.2)

theorem findOpenFull_shape (A : Forger vp prims optRand pkSeedDist) (pkSeed : prims.PkSeed)
    (ys : List prims.Y) :
    Resources2.findOpenFull A pkSeed ys =
      Lazy.openKeygen prims (Resources2.forsG prims) pkSeed >>= fun root ↦
        (simulateQ (logHarnessO optRand (Resources2.forsG prims) ⟨pkSeed, root⟩
          (Resources2.forsSignOpen ⟨pkSeed, root⟩ ys)) (A.main ⟨pkSeed, root⟩)).run [] >>=
          fun z ↦ Resources2.findAnswerO ⟨pkSeed, root⟩ ys z.2 z.1.1 z.1.2 := rfl

/-- Naturality: on a classical forger, `findOpenFullG` is `findOpenFull`. -/
theorem findOpenFullG_embed (A : Forger vp prims optRand pkSeedDist) (pkSeed : prims.PkSeed)
    (ys : List prims.Y) :
    findOpenFullG ds optRand (fun pk ↦ embed ds (A.main pk)) pkSeed ys =
      embed ds (Resources2.findOpenFull A pkSeed ys) := by
  rw [findOpenFull_shape]
  simp only [findOpenFullG, runGO_embed, embed_bind]

/-- **The `find` phase is the general interpretation of `findOpenFullG`.** -/
theorem findOpenFullG_tbl (F : GFam ds vp prims) (tbl : SecretTable vp prims)
    (pkSeed : prims.PkSeed) (ys : List prims.Y) :
    wrapS ds (Lazy.tblImpl (PublicHash.impl prims) tbl) (findOpenFullG ds optRand F pkSeed ys) =
      findOpenPreG ds optRand F tbl pkSeed ys := by
  have hw := wrapS_runGO ds (Lazy.tblImpl (PublicHash.impl prims) tbl)
    (logHarnessO optRand (Resources2.forsG prims) ⟨pkSeed, idealRoot vp prims tbl pkSeed⟩
      (Resources2.forsSignOpen ⟨pkSeed, idealRoot vp prims tbl pkSeed⟩ ys))
    (openPreHarness optRand tbl pkSeed ys)
    (fun t s ↦ logHarness_tbl_step optRand (Resources2.forsG prims) tbl
      ⟨pkSeed, idealRoot vp prims tbl pkSeed⟩ lazyRandomizerLift _ lazyRandomizerLift
      (Reduction.openSign ⟨pkSeed, idealRoot vp prims tbl pkSeed⟩ tbl ys)
      (fun log m a ↦ Lazy.simulateQ_tblImpl_liftM (PublicHash.impl prims) tbl
        (lazyRandomizer log m a))
      (fun m R ↦ Resources2.forsSignOpen_tbl tbl ⟨pkSeed, idealRoot vp prims tbl pkSeed⟩ ys m R)
      t s)
    (F ⟨pkSeed, idealRoot vp prims tbl pkSeed⟩) []
  unfold findOpenFullG findOpenPreG
  rw [wrapS_bind, wrapS_embed, Lazy.openKeygen_tbl, embed_pure, pure_bind, wrapS_bind, hw]
  refine bind_congr fun z ↦ ?_
  rw [wrapS_embed, Resources2.findAnswerO_tbl, embed_pure]
  rfl

/-- **(2a) Forge phase of `toTcrG F`**: one run of the interpreted open program
`findOpenFullG F pk ys` under the opening simulation; the output is forwarded. -/
theorem toTcrG_forge_full (F : GFam ds vp prims) (tbl : SecretTable vp prims)
    (tg : List (prims.AdrsKey × prims.Y)) (ys : List prims.Y) (pk : prims.PkSeed) :
    (toTcrG ds optRand pkSeedDist F).forge (tbl, tg, ys) pk =
      runG ds (SM_DT_OpenPRE_SourceFinalValidity.findOracles tg)
        (wrapS ds (Lazy.tblImpl (PublicHash.impl prims) tbl)
          (findOpenFullG ds optRand F pk ys)) [] >>= fun z ↦ pure z.1 := by
  rw [findOpenFullG_tbl]; rfl

/-- **(2a) Guess phase of `toDsprG F`**: the same single run, then one comparison and one
list-membership test. -/
theorem toDsprG_guess_full (F : GFam ds vp prims) (tbl : SecretTable vp prims)
    (tg : List (prims.AdrsKey × prims.Y)) (ys : List prims.Y) (pk : prims.PkSeed) :
    (toDsprG ds optRand pkSeedDist F).guess (tbl, tg, ys) pk =
      runG ds (SM_DT_OpenPRE_SourceFinalValidity.findOracles tg)
        (wrapS ds (Lazy.tblImpl (PublicHash.impl prims) tbl)
          (findOpenFullG ds optRand F pk ys)) [] >>= fun z ↦ pure (z.1.1,
            decide ((tg[z.1.1]?.map Prod.snd).getD default ≠ z.1.2 ∨ z.1.1 ∈ z.2)) := by
  rw [findOpenFullG_tbl]; rfl

include pkSeedDist in
/-- **(2b) Own hash evaluations of the `find` phase.** -/
theorem findOpenFullG_hashes (F : GFam ds vp prims) (qs : ℕ)
    (hF : ∀ pk, IsQueryBoundP (F pk) (fun i ↦ i.isRight = true) qs)
    (pkSeed : prims.PkSeed) (ys : List prims.Y) :
    IsQueryBoundP (findOpenFullG ds optRand F pkSeed ys) (fun t ↦ kindG t = .hash)
      (Lazy.keygenHashes vp + qs * Resources2.forsSignHashes vp + (1 + qs + vp.params.k)) := by
  rw [kindG_iff_liftP ds (Resources2.forsG prims) .hash (by decide)]
  exact openShape_queryBound ds (fun i ↦ i.isRight = true) _ ([], constSig default) _
    (fun root ↦ (⟨pkSeed, root⟩ : PublicKeyCore prims.core)) _ (fun _ ↦ [])
    (fun root z ↦ Resources2.findAnswerO ⟨pkSeed, root⟩ ys z.2 z.1.1 z.1.2) qs _
    (fun A₀ hA₀ ↦ Resources2.findOpenFull_hashes
      (⟨A₀⟩ : Forger vp prims optRand pkSeedDist) qs hA₀ pkSeed ys)
    F fun pk ↦ (isRight_iff_liftP ds _ _).1 (hF pk)

include pkSeedDist in
/-- **(2b) Opening queries simulated in the `find` phase**: `k` per signing query. -/
theorem findOpenFullG_openings (F : GFam ds vp prims) (qs : ℕ)
    (hF : ∀ pk, IsQueryBoundP (F pk) (fun i ↦ i.isRight = true) qs)
    (pkSeed : prims.PkSeed) (ys : List prims.Y) :
    IsQueryBoundP (findOpenFullG ds optRand F pkSeed ys) (fun t ↦ kindG t = .game)
      (qs * vp.params.k) := by
  rw [kindG_iff_liftP ds (Resources2.forsG prims) .game (by decide)]
  exact openShape_queryBound ds (fun i ↦ i.isRight = true) _ ([], constSig default) _
    (fun root ↦ (⟨pkSeed, root⟩ : PublicKeyCore prims.core)) _ (fun _ ↦ [])
    (fun root z ↦ Resources2.findAnswerO ⟨pkSeed, root⟩ ys z.2 z.1.1 z.1.2) qs _
    (fun A₀ hA₀ ↦ Resources2.findOpenFull_openings
      (⟨A₀⟩ : Forger vp prims optRand pkSeedDist) qs hA₀ pkSeed ys)
    F fun pk ↦ (isRight_iff_liftP ds _ _).1 (hF pk)

end Reduction.Gen

section Axioms
open Reduction.Gen
#print axioms IsResolution.queryBound
#print axioms runGO_bind_queryBound
#print axioms openShape_queryBound
#print axioms wrapS_runGO_closed
#print axioms bTcrArMG_forge_open
#print axioms memoForgeOpenG_hashes
#print axioms rUdG_phase2
#print axioms rUdG_phase2_hashes
#print axioms rPreG_phase2_hashes
#print axioms rTcrTG_phase2_hashes
#print axioms findOpenFullG_tbl
#print axioms toTcrG_forge_full
#print axioms toDsprG_guess_full
#print axioms findOpenFullG_hashes
#print axioms findOpenFullG_openings
end Axioms
