import Reduction.Gen.Derand

/-!
# Running a general-spec forger inside classical code

`gImplT` turns a classical handler for `unifSpec + X` into a handler for `(ds + unifSpec) + X`:
`ds`-queries are forwarded to the ambient monad, everything else is answered by the classical
handler (lifted).  `runG` (closed: target `OracleComp (ds + unifSpec)`), `runGO` (open: target
`OracleComp ((ds + unifSpec) + G)`) and `gImplS` (stateless, open) are its instances.

Syntactic facts: on `embed`ded (i.e. `ds`-free) programs these are the classical simulations
(`runG_embed`, …), and nested simulations fuse (`runG_wrapS`, `runG_runGO`).
-/

open OracleComp OracleSpec ENNReal

namespace Reduction.Gen

variable {κ : Type} (ds : OracleSpec κ)
variable {ιx ιg ι₀ ι₁ : Type} {X : OracleSpec ιx} {G : OracleSpec ιg}
  {T₀ : OracleSpec ι₀} {T₁ : OracleSpec ι₁} {σ τ α β : Type}

/-- A classical stateful handler for `unifSpec + X` with target `OracleComp T₀`, as a handler
for `(ds + unifSpec) + X` with target `OracleComp T₁`: `ds`-queries are answered by `fwd`, all
other queries by the classical handler, lifted by `up`. -/
def gImplT (up : {γ : Type} → OracleComp T₀ γ → OracleComp T₁ γ)
    (fwd : (d : ds.Domain) → OracleComp T₁ (ds.Range d))
    (impl : QueryImpl (unifSpec + X) (StateT σ (OracleComp T₀))) :
    QueryImpl ((ds + unifSpec) + X) (StateT σ (OracleComp T₁))
  | .inl (.inl d) => fun s ↦ (fun u ↦ (u, s)) <$> fwd d
  | .inl (.inr n) => fun s ↦ up ((impl (.inl n)).run s)
  | .inr x => fun s ↦ up ((impl (.inr x)).run s)

/-- Closed instance: the classical handler lives in `ProbComp`. -/
def gImpl (impl : QueryImpl (unifSpec + X) (StateT σ ProbComp)) :
    QueryImpl ((ds + unifSpec) + X) (StateT σ (OracleComp (gSpec ds))) :=
  gImplT ds (liftR ds) (fun d ↦ liftM ((gSpec ds).query (Sum.inl d))) impl

/-- Open instance: the classical handler may query `G`. -/
def gImplO (impl : QueryImpl (unifSpec + X) (StateT σ (OracleComp (unifSpec + G)))) :
    QueryImpl ((ds + unifSpec) + X) (StateT σ (OracleComp ((ds + unifSpec) + G))) :=
  gImplT ds (embed ds) (fun d ↦ liftM (((ds + unifSpec) + G).query (Sum.inl (Sum.inl d)))) impl

/-- Stateless open instance. -/
def gImplS (w : QueryImpl (unifSpec + X) (OracleComp (unifSpec + G))) :
    QueryImpl ((ds + unifSpec) + X) (OracleComp ((ds + unifSpec) + G))
  | .inl (.inl d) => liftM (((ds + unifSpec) + G).query (Sum.inl (Sum.inl d)))
  | .inl (.inr n) => embed ds (w (.inl n))
  | .inr x => embed ds (w (.inr x))

/-- Run a general-spec program against a classical stateful handler (closed). -/
def runG (impl : QueryImpl (unifSpec + X) (StateT σ ProbComp))
    (oa : OracleComp ((ds + unifSpec) + X) α) (s : σ) : OracleComp (gSpec ds) (α × σ) :=
  (simulateQ (gImpl ds impl) oa).run s

/-- Run a general-spec program against a classical stateful handler (open). -/
def runGO (impl : QueryImpl (unifSpec + X) (StateT σ (OracleComp (unifSpec + G))))
    (oa : OracleComp ((ds + unifSpec) + X) α) (s : σ) :
    OracleComp ((ds + unifSpec) + G) (α × σ) :=
  (simulateQ (gImplO ds impl) oa).run s

/-- Interpret the non-`ds` queries of a general-spec program by a classical stateless handler. -/
def wrapS (w : QueryImpl (unifSpec + X) (OracleComp (unifSpec + G)))
    (oa : OracleComp ((ds + unifSpec) + X) α) : OracleComp ((ds + unifSpec) + G) α :=
  simulateQ (gImplS ds w) oa

/-! ## Generic facts about `gImplT` -/

section generic

variable (up : {γ : Type} → OracleComp T₀ γ → OracleComp T₁ γ)
  (fwd : (d : ds.Domain) → OracleComp T₁ (ds.Range d))
  (hp : ∀ {γ : Type} (a : γ), up (pure a : OracleComp T₀ γ) = pure a)
  (hb : ∀ {γ δ : Type} (x : OracleComp T₀ γ) (f : γ → OracleComp T₀ δ),
    up (x >>= f) = up x >>= fun a ↦ up (f a))

include hp hb in
/-- On a `ds`-free program, the lifted handler is the lift of the classical simulation. -/
theorem run_gImplT_embed (impl : QueryImpl (unifSpec + X) (StateT σ (OracleComp T₀)))
    (t : OracleComp (unifSpec + X) α) (s : σ) :
    (simulateQ (gImplT ds up fwd impl) (embed ds t)).run s = up ((simulateQ impl t).run s) := by
  induction t using OracleComp.inductionOn generalizing s with
  | pure a => simp [hp]
  | query_bind q k ih =>
    rw [embed_bind, simulateQ_bind, simulateQ_bind, StateT.run_bind, StateT.run_bind, hb]
    rcases q with n | x
    · rw [embed_query_inl, simulateQ_spec_query, simulateQ_spec_query]
      exact bind_congr fun p ↦ ih _ _
    · rw [embed_query_inr, simulateQ_spec_query, simulateQ_spec_query]
      exact bind_congr fun p ↦ ih _ _

end generic

/-- Composition of a stateful handler with a stateless wrapper. -/
def compS (H : QueryImpl (unifSpec + G) (StateT τ (OracleComp T₀)))
    (w : QueryImpl (unifSpec + X) (OracleComp (unifSpec + G))) :
    QueryImpl (unifSpec + X) (StateT τ (OracleComp T₀)) :=
  fun t ↦ simulateQ H (w t)

/-- Composition of two stateful handlers (state: the pair). -/
def compST (H : QueryImpl (unifSpec + G) (StateT τ (OracleComp T₀)))
    (impl : QueryImpl (unifSpec + X) (StateT σ (OracleComp (unifSpec + G)))) :
    QueryImpl (unifSpec + X) (StateT (σ × τ) (OracleComp T₀)) :=
  fun t st ↦ (fun r ↦ (r.1.1, (r.1.2, r.2))) <$> (simulateQ H ((impl t).run st.1)).run st.2

section fusion

variable (up : {γ : Type} → OracleComp T₀ γ → OracleComp T₁ γ)
  (fwd : (d : ds.Domain) → OracleComp T₁ (ds.Range d))
  (hp : ∀ {γ : Type} (a : γ), up (pure a : OracleComp T₀ γ) = pure a)
  (hb : ∀ {γ δ : Type} (x : OracleComp T₀ γ) (f : γ → OracleComp T₀ δ),
    up (x >>= f) = up x >>= fun a ↦ up (f a))

include hp hb in
/-- **Fusion (stateless inner wrapper).** -/
theorem run_gImplT_wrapS (H : QueryImpl (unifSpec + G) (StateT τ (OracleComp T₀)))
    (w : QueryImpl (unifSpec + X) (OracleComp (unifSpec + G)))
    (oa : OracleComp ((ds + unifSpec) + X) α) (s : τ) :
    (simulateQ (gImplT ds up fwd H) (wrapS ds w oa)).run s =
      (simulateQ (gImplT ds up fwd (compS H w)) oa).run s := by
  unfold wrapS
  induction oa using OracleComp.inductionOn generalizing s with
  | pure a => simp
  | query_bind q k ih =>
    simp only [simulateQ_bind, StateT.run_bind, simulateQ_spec_query]
    rcases q with (d | n) | x
    · have h1 : (simulateQ (gImplT ds up fwd H) (gImplS ds w (Sum.inl (Sum.inl d)))).run s =
          (gImplT ds up fwd (compS H w) (Sum.inl (Sum.inl d))).run s := by
        change (simulateQ (gImplT ds up fwd H)
          (liftM (((ds + unifSpec) + G).query (Sum.inl (Sum.inl d))))).run s = _
        rw [simulateQ_spec_query]; rfl
      rw [h1]
      exact bind_congr fun p ↦ ih _ _
    · have h1 : (simulateQ (gImplT ds up fwd H) (gImplS ds w (Sum.inl (Sum.inr n)))).run s =
          (gImplT ds up fwd (compS H w) (Sum.inl (Sum.inr n))).run s :=
        run_gImplT_embed ds up fwd hp hb H _ s
      rw [h1]
      exact bind_congr fun p ↦ ih _ _
    · have h1 : (simulateQ (gImplT ds up fwd H) (gImplS ds w (Sum.inr x))).run s =
          (gImplT ds up fwd (compS H w) (Sum.inr x)).run s :=
        run_gImplT_embed ds up fwd hp hb H _ s
      rw [h1]
      exact bind_congr fun p ↦ ih _ _

include hp hb in
/-- **Fusion (stateful inner handler).** -/
theorem run_gImplT_runGO (H : QueryImpl (unifSpec + G) (StateT τ (OracleComp T₀)))
    (impl : QueryImpl (unifSpec + X) (StateT σ (OracleComp (unifSpec + G))))
    (oa : OracleComp ((ds + unifSpec) + X) α) (s : σ) (t : τ) :
    (simulateQ (gImplT ds up fwd H) (runGO ds impl oa s)).run t =
      (fun r ↦ ((r.1, r.2.1), r.2.2)) <$>
        (simulateQ (gImplT ds up fwd (compST H impl)) oa).run (s, t) := by
  have hm : ∀ {γ δ : Type} (f : γ → δ) (x : OracleComp T₀ γ), up (f <$> x) = f <$> up x := by
    intro γ δ f x
    rw [map_eq_bind_pure_comp, hb, map_eq_bind_pure_comp]
    exact bind_congr fun a ↦ hp _
  unfold runGO
  induction oa using OracleComp.inductionOn generalizing s t with
  | pure a => simp
  | query_bind q k ih =>
    simp only [simulateQ_bind, StateT.run_bind, simulateQ_spec_query, map_bind]
    rcases q with (d | n) | x
    · have h1 : (gImplO ds impl (Sum.inl (Sum.inl d))).run s =
          (fun u ↦ (u, s)) <$> (liftM (((ds + unifSpec) + G).query (Sum.inl (Sum.inl d))) :
            OracleComp ((ds + unifSpec) + G) _) := rfl
      have h2 : (gImplT ds up fwd (compST H impl) (Sum.inl (Sum.inl d))).run (s, t) =
          (fun u ↦ (u, (s, t))) <$> fwd d := rfl
      have h3 : (gImplT ds up fwd H (Sum.inl (Sum.inl d))).run t = (fun u ↦ (u, t)) <$> fwd d :=
        rfl
      rw [h1, h2]
      simp only [simulateQ_map, StateT.run_map, simulateQ_spec_query, bind_map_left, h3]
      exact bind_congr fun u ↦ ih _ _ _
    · have h1 : (gImplO ds impl (Sum.inl (Sum.inr n))).run s =
          embed ds ((impl (Sum.inl n)).run s) := rfl
      have h2 : (gImplT ds up fwd (compST H impl) (Sum.inl (Sum.inr n))).run (s, t) =
          up ((fun r ↦ (r.1.1, (r.1.2, r.2))) <$>
            (simulateQ H ((impl (Sum.inl n)).run s)).run t) := rfl
      rw [h1, h2, run_gImplT_embed ds up fwd hp hb, hm, bind_map_left]
      exact bind_congr fun u ↦ ih _ _ _
    · have h1 : (gImplO ds impl (Sum.inr x)).run s = embed ds ((impl (Sum.inr x)).run s) := rfl
      have h2 : (gImplT ds up fwd (compST H impl) (Sum.inr x)).run (s, t) =
          up ((fun r ↦ (r.1.1, (r.1.2, r.2))) <$>
            (simulateQ H ((impl (Sum.inr x)).run s)).run t) := rfl
      rw [h1, h2, run_gImplT_embed ds up fwd hp hb, hm, bind_map_left]
      exact bind_congr fun u ↦ ih _ _ _

end fusion

/-! ## The closed and open instances -/

section instances

variable (impl : QueryImpl (unifSpec + X) (StateT σ ProbComp))
  (implO : QueryImpl (unifSpec + X) (StateT σ (OracleComp (unifSpec + G))))

@[simp] lemma runG_pure (a : α) (s : σ) :
    runG ds impl (pure a : OracleComp ((ds + unifSpec) + X) α) s = pure (a, s) := by
  simp [runG]

lemma runG_bind (oa : OracleComp ((ds + unifSpec) + X) α)
    (f : α → OracleComp ((ds + unifSpec) + X) β) (s : σ) :
    runG ds impl (oa >>= f) s = runG ds impl oa s >>= fun p ↦ runG ds impl (f p.1) p.2 := by
  simp [runG]

lemma runG_map (oa : OracleComp ((ds + unifSpec) + X) α) (f : α → β) (s : σ) :
    runG ds impl (f <$> oa) s = (fun p ↦ (f p.1, p.2)) <$> runG ds impl oa s := by
  simp [runG]

@[simp] lemma runGO_pure (a : α) (s : σ) :
    runGO ds implO (pure a : OracleComp ((ds + unifSpec) + X) α) s = pure (a, s) := by
  simp [runGO]

lemma runGO_bind (oa : OracleComp ((ds + unifSpec) + X) α)
    (f : α → OracleComp ((ds + unifSpec) + X) β) (s : σ) :
    runGO ds implO (oa >>= f) s =
      runGO ds implO oa s >>= fun p ↦ runGO ds implO (f p.1) p.2 := by
  simp [runGO]

/-- On a `ds`-free program, `runG` is the classical simulation. -/
theorem runG_embed (t : OracleComp (unifSpec + X) α) (s : σ) :
    runG ds impl (embed ds t) s = liftR ds ((simulateQ impl t).run s) :=
  run_gImplT_embed ds (liftR ds) _ (fun a ↦ liftR_pure ds a) (fun x f ↦ liftR_bind ds x f)
    impl t s

/-- On a `ds`-free program, `runGO` is the classical simulation. -/
theorem runGO_embed (t : OracleComp (unifSpec + X) α) (s : σ) :
    runGO ds implO (embed ds t) s = embed ds ((simulateQ implO t).run s) :=
  run_gImplT_embed ds (embed ds) _ (fun a ↦ embed_pure ds a) (fun x f ↦ embed_bind ds x f)
    implO t s

variable (w : QueryImpl (unifSpec + X) (OracleComp (unifSpec + G)))

@[simp] lemma wrapS_pure (a : α) :
    wrapS ds w (pure a : OracleComp ((ds + unifSpec) + X) α) = pure a := by simp [wrapS]

lemma wrapS_bind (oa : OracleComp ((ds + unifSpec) + X) α)
    (f : α → OracleComp ((ds + unifSpec) + X) β) :
    wrapS ds w (oa >>= f) = wrapS ds w oa >>= fun a ↦ wrapS ds w (f a) := by simp [wrapS]

lemma wrapS_map (oa : OracleComp ((ds + unifSpec) + X) α) (f : α → β) :
    wrapS ds w (f <$> oa) = f <$> wrapS ds w oa := by simp [wrapS]

/-- On a `ds`-free program, `wrapS` is the classical interpretation. -/
theorem wrapS_embed (t : OracleComp (unifSpec + X) α) :
    wrapS ds w (embed ds t) = embed ds (simulateQ w t) := by
  unfold wrapS
  induction t using OracleComp.inductionOn with
  | pure a => simp
  | query_bind q k ih =>
    rw [embed_bind, simulateQ_bind, simulateQ_bind, embed_bind]
    rcases q with n | x
    · rw [embed_query_inl, simulateQ_spec_query, simulateQ_spec_query]
      exact bind_congr fun p ↦ ih _
    · rw [embed_query_inr, simulateQ_spec_query, simulateQ_spec_query]
      exact bind_congr fun p ↦ ih _

/-- **Fusion**: a closed run of a wrapped program is a closed run of the program. -/
theorem runG_wrapS (H : QueryImpl (unifSpec + G) (StateT τ ProbComp))
    (oa : OracleComp ((ds + unifSpec) + X) α) (s : τ) :
    runG ds H (wrapS ds w oa) s = runG ds (compS H w) oa s :=
  run_gImplT_wrapS ds (liftR ds) _ (fun a ↦ liftR_pure ds a) (fun x f ↦ liftR_bind ds x f)
    H w oa s

/-- **Fusion**: a closed run of an open run is a closed run with the pair state. -/
theorem runG_runGO (H : QueryImpl (unifSpec + G) (StateT τ ProbComp))
    (oa : OracleComp ((ds + unifSpec) + X) α) (s : σ) (t : τ) :
    runG ds H (runGO ds implO oa s) t =
      (fun r ↦ ((r.1, r.2.1), r.2.2)) <$> runG ds (compST H implO) oa (s, t) :=
  run_gImplT_runGO ds (liftR ds) _ (fun a ↦ liftR_pure ds a) (fun x f ↦ liftR_bind ds x f)
    H implO oa s t

/-- A closed run of a `ds`-free open program is the classical run. -/
theorem runG_embedO (H : QueryImpl (unifSpec + G) (StateT τ ProbComp))
    (t : OracleComp (unifSpec + G) α) (s : τ) :
    runG ds H (embed ds t) s = liftR ds ((simulateQ H t).run s) := runG_embed ds H t s

/-- **Fusion** (open outer run, stateless inner wrapper). -/
theorem runGO_wrapS {ιh : Type} {Hs : OracleSpec ιh}
    (H : QueryImpl (unifSpec + G) (StateT τ (OracleComp (unifSpec + Hs))))
    (oa : OracleComp ((ds + unifSpec) + X) α) (s : τ) :
    runGO ds H (wrapS ds w oa) s = runGO ds (compS H w) oa s :=
  run_gImplT_wrapS ds (embed ds) _ (fun a ↦ embed_pure ds a) (fun x f ↦ embed_bind ds x f)
    H w oa s

/-- **Fusion** (open outer run, stateful inner run). -/
theorem runGO_runGO {ιh : Type} {Hs : OracleSpec ιh}
    (H : QueryImpl (unifSpec + G) (StateT τ (OracleComp (unifSpec + Hs))))
    (oa : OracleComp ((ds + unifSpec) + X) α) (s : σ) (t : τ) :
    runGO ds H (runGO ds implO oa s) t =
      (fun r ↦ ((r.1, r.2.1), r.2.2)) <$> runGO ds (compST H implO) oa (s, t) :=
  run_gImplT_runGO ds (embed ds) _ (fun a ↦ embed_pure ds a) (fun x f ↦ embed_bind ds x f)
    H implO oa s t

end instances

/-! ## Forger-to-forger wrappers -/

section wrappers

variable {ιx' ιx'' : Type} {X' : OracleSpec ιx'} {X'' : OracleSpec ιx''} {PK PK' PK'' α' α'' : Type}

/-- The identity wrapper handler. -/
def idW (X : OracleSpec ιx) : QueryImpl (unifSpec + X) (OracleComp (unifSpec + X)) :=
  fun t ↦ liftM ((unifSpec + X).query t)

lemma wrapS_idW (oa : OracleComp ((ds + unifSpec) + X) α) : wrapS ds (idW X) oa = oa := by
  unfold wrapS
  induction oa using OracleComp.inductionOn with
  | pure a => simp
  | query_bind q k ih =>
    rw [simulateQ_bind, simulateQ_spec_query]
    have h : gImplS ds (idW X) q = liftM (((ds + unifSpec) + X).query q) := by
      rcases q with (d | n) | x
      · rfl
      · exact embed_query_inl ds n
      · exact embed_query_inr ds x
    rw [h]
    exact bind_congr fun u ↦ ih u

/-- Composition of two stateless wrapper handlers. -/
def compSS (w₂ : QueryImpl (unifSpec + X') (OracleComp (unifSpec + X)))
    (w₁ : QueryImpl (unifSpec + X'') (OracleComp (unifSpec + X'))) :
    QueryImpl (unifSpec + X'') (OracleComp (unifSpec + X)) :=
  fun t ↦ simulateQ w₂ (w₁ t)

/-- **Fusion** of two stateless wrappers. -/
theorem wrapS_wrapS (w₂ : QueryImpl (unifSpec + X') (OracleComp (unifSpec + X)))
    (w₁ : QueryImpl (unifSpec + X'') (OracleComp (unifSpec + X')))
    (oa : OracleComp ((ds + unifSpec) + X'') α) :
    wrapS ds w₂ (wrapS ds w₁ oa) = wrapS ds (compSS w₂ w₁) oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp
  | query_bind q k ih =>
    rw [wrapS_bind, wrapS_bind, wrapS_bind]
    have h : wrapS ds w₂ (wrapS ds w₁ (liftM (((ds + unifSpec) + X'').query q))) =
        wrapS ds (compSS w₂ w₁) (liftM (((ds + unifSpec) + X'').query q)) := by
      unfold wrapS
      rw [simulateQ_spec_query, simulateQ_spec_query]
      rcases q with (d | n) | x
      · change simulateQ (gImplS ds w₂)
          (liftM (((ds + unifSpec) + X').query (Sum.inl (Sum.inl d)))) = _
        rw [simulateQ_spec_query]; rfl
      · exact wrapS_embed ds w₂ (w₁ (Sum.inl n))
      · exact wrapS_embed ds w₂ (w₁ (Sum.inr x))
    rw [h]
    exact bind_congr fun u ↦ ih u

/-- A forger family for one interface from a forger family for another: re-key by `e`, interpret
the non-`ds` queries by the classical stateless handler `w`, translate the output by `g`. -/
def wrapFam (w : QueryImpl (unifSpec + X') (OracleComp (unifSpec + X))) (e : PK → PK')
    (g : α' → α) (F : PK' → OracleComp ((ds + unifSpec) + X') α') :
    PK → OracleComp ((ds + unifSpec) + X) α :=
  fun pk ↦ g <$> wrapS ds w (F (e pk))

lemma wrapFam_id (F : PK → OracleComp ((ds + unifSpec) + X) α) :
    wrapFam ds (idW X) id id F = F := by
  funext pk
  simp [wrapFam, wrapS_idW]

lemma wrapFam_wrapFam (w₂ : QueryImpl (unifSpec + X') (OracleComp (unifSpec + X)))
    (e₂ : PK → PK') (g₂ : α' → α)
    (w₁ : QueryImpl (unifSpec + X'') (OracleComp (unifSpec + X'))) (e₁ : PK' → PK'')
    (g₁ : α'' → α') (F : PK'' → OracleComp ((ds + unifSpec) + X'') α'') :
    wrapFam ds w₂ e₂ g₂ (wrapFam ds w₁ e₁ g₁ F) =
      wrapFam ds (compSS w₂ w₁) (e₁ ∘ e₂) (g₂ ∘ g₁) F := by
  funext pk
  simp only [wrapFam, wrapS_map, wrapS_wrapS, Functor.map_map, Function.comp_apply]
  rfl

/-- On `ds`-free families, `wrapFam` is the classical wrapper. -/
lemma wrapFam_embed (w : QueryImpl (unifSpec + X') (OracleComp (unifSpec + X))) (e : PK → PK')
    (g : α' → α) (F₀ : PK' → OracleComp (unifSpec + X') α') :
    wrapFam ds w e g (fun pk ↦ embed ds (F₀ pk)) =
      fun pk ↦ embed ds (g <$> simulateQ w (F₀ (e pk))) := by
  funext pk
  simp [wrapFam, wrapS_embed]

/-- **Fusion**: a closed run of a wrapped family member. -/
theorem runG_wrapFam (w : QueryImpl (unifSpec + X') (OracleComp (unifSpec + X))) (e : PK → PK')
    (g : α' → α) (F : PK' → OracleComp ((ds + unifSpec) + X') α')
    (H : QueryImpl (unifSpec + X) (StateT τ ProbComp)) (pk : PK) (s : τ) :
    runG ds H (wrapFam ds w e g F pk) s =
      (fun p ↦ (g p.1, p.2)) <$> runG ds (compS H w) (F (e pk)) s := by
  rw [wrapFam, runG_map, runG_wrapS]

/-- **Fusion**: an open run of a wrapped family member. -/
theorem runGO_wrapFam (w : QueryImpl (unifSpec + X') (OracleComp (unifSpec + X))) (e : PK → PK')
    (g : α' → α) (F : PK' → OracleComp ((ds + unifSpec) + X') α')
    (H : QueryImpl (unifSpec + X) (StateT τ (OracleComp (unifSpec + G)))) (pk : PK) (s : τ) :
    runGO ds H (wrapFam ds w e g F pk) s =
      (fun p ↦ (g p.1, p.2)) <$> runGO ds (compS H w) (F (e pk)) s := by
  rw [wrapFam, runGO, simulateQ_map, StateT.run_map]
  exact congrArg _ (runGO_wrapS ds w H (F (e pk)) s)

end wrappers

end Reduction.Gen

section Axioms
open Reduction.Gen
#print axioms runG_embed
#print axioms runG_wrapS
#print axioms runG_runGO
#print axioms wrapS_embed
end Axioms
