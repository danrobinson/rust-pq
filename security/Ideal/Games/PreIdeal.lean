import Ideal.Games.PreBridge
import Ideal.Games.TcrIdeal
import Ideal.Core.HiddenInput

/-!
# SM-PRE in the ideal-compression model: the ideal (hidden-prefix) game

`pre_ideal_le`: when the attacked member has a single message block after the seed block, the
ideal game of `preProg₁ emb A`, `preP₂ emb A` is won with probability at most
`(q₂ + 1)·δ + (q₂ + 1)/|M'| + 1/|St|`, `q₂` the number of compression queries of the
adversary's second phase, `δ` a bound on the probability that the output map hits a fixed value
on a uniform chaining value, `M'` the space the challenge oracle draws its messages from.

Proof.  In the ideal game an accepted challenge at tweak `t` draws `x`, reads the fresh
private-row cell `preCell F emb t x = (F.tch t (emb x)).1` and returns the output of the value
`Y` found there; phase one never reads that cell again, so its view depends on `x` only through
where `Y` is stored.

* *Phase one* (`pre_phase1`).  `preSim` is the modified phase one whose challenge oracle draws
  `Y` directly, records `(t, Y)` and touches no private-row cell.  The randomised state map
  `prePhi` (draw an independent hidden input for every recorded target, `hideDraw`, and lay
  the hidden cells over the cache, `patch`/`hidMap`) commutes in distribution with every step
  (`pre_intertwine_step`; uses the invariant `PreInv`: target tweaks pairwise distinct, cached
  private-row cells carry collection tweaks, collection tweaks are not target tweaks), hence
  with phase one (`evalDistEq_run_of_intertwine`).  So the hidden inputs can be drawn after
  phase one, independently of everything the adversary has seen.
* *Phase two* (`prT_pre_phase2_le`), for a fixed outcome of the modified phase one, a fixed
  seed and `cv ≠ IV`.  The adversary's second phase run from the cache patched with the hidden
  cells is dominated by its run `R'` from the unpatched cache, which does not depend on the
  hidden inputs, until `R'` reads a hidden cell (`prT_run_romImpl_patch_le`).  Averaging over
  the hidden inputs *after* `R'`: `R'` breaks `PreGood` (some cached private-row cell with a
  target tweak has the target's output) with probability `≤ q₂·δ` (`prEvent_routeRO_bad_le`);
  on every run of `R'` the probability over the hidden inputs that a cell cached by `R'` is
  hidden is `≤ q₂/|M'|` (`routeRO_potential_le`, `prEvent_hideDraw_cell_le`), and that the
  answer `m` is the hidden input of its target `≤ 1/|M'|` (`prEvent_hideDraw_getElem_le`);
  otherwise the winning check reads a fresh or good cell and succeeds with probability `≤ δ`
  (`prT_preFin_le`).
* `cv = IV` has probability `1/|St|`.
-/

open OracleComp OracleSpec ENNReal

namespace Ideal

open TweakableHash

variable {St Blk PkSeed Tweak M M' Y ι : Type} {F : THFam St Blk PkSeed Tweak M Y ι}

section Lemmas

variable [DecidableEq St] [DecidableEq Blk] [SampleableType St]

/-! ## Phase one: the game steps through the lazy oracle -/

theorem run_preGameM_inl [DecidableEq Tweak] [SampleableType M'] (emb : M' → M) (n : ℕ)
    (s : SM_DT_PRE_State Tweak M') (c : Cache St Blk) :
    (simulateQ chainRO ((preGameM F emb (.inl n)).run s)).run c =
      (fun u => ((u, s), c)) <$> (unifSpec.query n : ProbComp (Fin (n + 1))) := by
  have h : (simulateQ chainRO ((preGameM F emb (.inl n)).run s)).run c =
      (fun p => ((p.1, s), p.2)) <$> ((chainRO (St := St) (Blk := Blk)) (.inl n)).run c := by
    simp [preGameM]
  rw [h, chainRO_run_inl, Functor.map_map]

theorem run_preGameM_pub [DecidableEq Tweak] [SampleableType M'] (emb : M' → M) (q : St × Blk)
    (s : SM_DT_PRE_State Tweak M') (c : Cache St Blk) :
    (simulateQ chainRO ((preGameM F emb (.inr (.inl q))).run s)).run c =
      (fun p => ((p.1, s), p.2)) <$>
        ((chainRO (St := St) (Blk := Blk)) (.inr (.inl q))).run c := by
  simp [preGameM]

theorem run_preGameM_chal [DecidableEq Tweak] [SampleableType M'] (emb : M' → M)
    (hsingle : ∀ t m, (F.tch t m).2 = []) (t : Tweak) (qs : List (Tweak × M'))
    (tw : List Tweak) (c : Cache St Blk) :
    (simulateQ chainRO ((preGameM F emb (.inr (.inr (.inl t)))).run (qs, tw))).run c =
      if F.numTargets ≤ qs.length ∨ ¬ TweakFresh Prod.fst qs tw t then
        pure ((none, qs, tw), c)
      else ($ᵗ M' : ProbComp M') >>= fun x =>
        (fun p => ((some (F.out p.1), qs ++ [(t, x)], tw), p.2)) <$>
          ((hS St Blk + tS St Blk).randomOracle (.inr (F.tch t (emb x)).1)).run c := by
  rw [preGameM_run_chal]
  by_cases h : F.numTargets ≤ qs.length ∨ ¬ TweakFresh Prod.fst qs tw t
  · simp [h]
  · simp only [h, ite_false, simulateQ_bind, StateT.run_bind, run_chainRO_liftM, bind_map_left]
    refine bind_congr fun x => ?_
    rw [simulateQ_spec_query, chainRO_run_chain, hsingle]
    simp

theorem run_preGameM_coll [DecidableEq Tweak] [SampleableType M'] (emb : M' → M)
    (q : (i : ι) × Tweak × F.Msg i) (qs : List (Tweak × M')) (tw : List Tweak)
    (c : Cache St Blk) :
    (simulateQ chainRO ((preGameM F emb (.inr (.inr (.inr q)))).run (qs, tw))).run c =
      if TweakReserved (Q := Tweak × M') Prod.fst qs q.2.1 then
        pure ((none, qs, tw), c)
      else (fun p => ((some (F.cout q.1 p.1), qs, tw ++ [q.2.1]), p.2)) <$>
        ((chainRO (St := St) (Blk := Blk)) (.inr (.inr (F.cch q.1 q.2.1 q.2.2)))).run c := by
  simp only [preGameM]
  by_cases h : TweakReserved (Q := Tweak × M') Prod.fst qs q.2.1 <;> simp [h]

/-! ## Phase one with deferred hidden inputs -/

/-- The private-row cell read by the challenge oracle at tweak `t` and hidden input `x`. -/
def preCell (F : THFam St Blk PkSeed Tweak M Y ι) (emb : M' → M) (t : Tweak) (x : M') : Blk :=
  (F.tch t (emb x)).1

/-- State of the modified phase one: targets `(tweak, chaining value)`, collection tweaks, and
the joint cache (which contains no target cell). -/
abbrev PreSimState (Tweak St Blk : Type) := (List (Tweak × St) × List Tweak) × Cache St Blk

/-- The modified phase one: the challenge oracle draws the chaining value `Y` of the target
directly, records `(t, Y)` and touches no private-row cell; the other oracles are those of the
game run through the lazy oracle. -/
noncomputable def preSim [DecidableEq Tweak] (F : THFam St Blk PkSeed Tweak M Y ι) :
    QueryImpl F.padvS (StateT (PreSimState Tweak St Blk) ProbComp) := fun
  | .inl n => StateT.mk fun s => (fun u => (u, s)) <$> (unifSpec.query n : ProbComp (Fin (n + 1)))
  | .inr (.inl q) => StateT.mk fun s => (fun z => (z.1, (s.1, z.2))) <$>
      ((chainRO (St := St) (Blk := Blk)) (.inr (.inl q))).run s.2
  | .inr (.inr (.inl t)) => StateT.mk fun s =>
      if F.numTargets ≤ s.1.1.length ∨ ¬ TweakFresh Prod.fst s.1.1 s.1.2 t then pure (none, s)
      else (fun Y => (some (F.out Y), ((s.1.1 ++ [(t, Y)], s.1.2), s.2))) <$>
        ($ᵗ St : ProbComp St)
  | .inr (.inr (.inr q)) => StateT.mk fun s =>
      if TweakReserved (Q := Tweak × St) Prod.fst s.1.1 q.2.1 then pure (none, s)
      else (fun z => (some (F.cout q.1 z.1), ((s.1.1, s.1.2 ++ [q.2.1]), z.2))) <$>
        ((chainRO (St := St) (Blk := Blk)) (.inr (.inr (F.cch q.1 q.2.1 q.2.2)))).run s.2

/-- The game's target list determined by hidden inputs. -/
def preQs (xs : List (Tweak × M' × St)) : List (Tweak × M') := xs.map fun e => (e.1, e.2.1)

/-- From a state of the modified phase one to a state of the game: draw a hidden input for
every target and lay the hidden cells over the cache. -/
noncomputable def prePhi [SampleableType M'] (F : THFam St Blk PkSeed Tweak M Y ι)
    (emb : M' → M) (s : PreSimState Tweak St Blk) :
    ProbComp (SM_DT_PRE_State Tweak M' × Cache St Blk) :=
  (fun xs => ((preQs xs, s.1.2), patch s.2 (hidMap (preCell F emb) xs))) <$> hideDraw s.1.1

/-- Invariant of the modified phase one: target tweaks are pairwise distinct, every cached
private-row cell carries a collection tweak, and no collection tweak is a target tweak. -/
def PreInv (btw : Blk → Tweak) (s : PreSimState Tweak St Blk) : Prop :=
  (s.1.1.map Prod.fst).Nodup ∧
  (∀ B, (s.2 (.inr B)).isSome → btw B ∈ s.1.2) ∧
  (∀ t ∈ s.1.2, t ∉ s.1.1.map Prod.fst)

omit [DecidableEq St] [DecidableEq Blk] [SampleableType St] in
theorem tweakReserved_iff {Q : Type} (l : List (Tweak × Q)) (t : Tweak) :
    TweakReserved Prod.fst l t ↔ t ∈ l.map Prod.fst := by
  simp [TweakReserved]

omit [DecidableEq St] [DecidableEq Blk] [SampleableType St] in
theorem preQs_map_fst [SampleableType M'] {l : List (Tweak × St)} {xs : List (Tweak × M' × St)}
    (h : xs ∈ support (hideDraw l)) : (preQs xs).map Prod.fst = l.map Prod.fst := by
  rw [← map_fst_of_mem_support_hideDraw h, preQs, List.map_map]
  rfl

omit [DecidableEq St] [DecidableEq Blk] [SampleableType St] in
theorem preQs_length [SampleableType M'] {l : List (Tweak × St)} {xs : List (Tweak × M' × St)}
    (h : xs ∈ support (hideDraw l)) : (preQs xs).length = l.length := by
  rw [preQs, List.length_map, length_of_mem_support_hideDraw h]

omit [DecidableEq St] [SampleableType St] in
/-- Under the invariant no hidden cell is cached. -/
theorem not_hiddenRead_of_inv [SampleableType M'] (emb : M' → M) (btw : Blk → Tweak)
    (hbtwT : ∀ t m, btw (F.tch t m).1 = t) {s : PreSimState Tweak St Blk} (hI : PreInv btw s)
    {xs : List (Tweak × M' × St)} (hxs : xs ∈ support (hideDraw s.1.1)) :
    ¬ HiddenRead (hidMap (preCell F emb) xs) s.2 := by
  rintro ⟨B, hB, hB'⟩
  obtain ⟨e, he, rfl⟩ := (hidMap_isSome_iff _ xs B).1 hB
  refine hI.2.2 _ (hI.2.1 _ hB') ?_
  rw [preCell, hbtwT, ← map_fst_of_mem_support_hideDraw hxs]
  exact List.mem_map_of_mem (f := fun e => e.1) he

/-- Every step of the modified phase one preserves the invariant. -/
theorem preInv_step [DecidableEq Tweak] (btw : Blk → Tweak)
    (hbtwC : ∀ i t m, btw (F.cch i t m).1 = t) (t : F.padvS.Domain)
    (s : PreSimState Tweak St Blk) (h : PreInv btw s) :
    ∀ z ∈ support ((preSim F t).run s), PreInv btw z.2 := by
  intro z hz
  obtain ⟨⟨qs, tw⟩, c⟩ := s
  obtain ⟨ha, hb, hc⟩ := h
  rcases t with n | q | t | q
  · simp only [preSim, StateT.run_mk, support_map] at hz
    obtain ⟨u, -, rfl⟩ := hz
    exact ⟨ha, hb, hc⟩
  · simp only [preSim, StateT.run_mk, support_map] at hz
    obtain ⟨p, hp, rfl⟩ := hz
    rw [chainRO_run_pub] at hp
    exact ⟨ha, fun B hB => hb B (by
      rwa [row_eq_of_mem_support_randomOracle_pub q c hp] at hB), hc⟩
  · simp only [preSim, StateT.run_mk] at hz
    split_ifs at hz with hcond
    · rw [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact ⟨ha, hb, hc⟩
    · rw [support_map] at hz
      obtain ⟨Y, -, rfl⟩ := hz
      rw [not_or, not_not] at hcond
      obtain ⟨-, hres, hntw⟩ := hcond
      rw [tweakReserved_iff] at hres
      refine ⟨?_, hb, ?_⟩
      · simp only [List.map_append, List.map_cons, List.map_nil]
        exact List.Nodup.append ha (List.nodup_singleton _) (by simpa using hres)
      · intro t' ht'
        simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append,
          List.mem_singleton, not_or]
        exact ⟨hc t' ht', fun e => hntw (e ▸ ht')⟩
  · simp only [preSim, StateT.run_mk] at hz
    split_ifs at hz with hcond
    · rw [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact ⟨ha, hb, hc⟩
    · rw [support_map] at hz
      obtain ⟨p, hp, rfl⟩ := hz
      obtain ⟨-, hrest⟩ := row_of_mem_support_chainRO_chain _ c hp
      obtain ⟨i, t₀, m₀⟩ := q
      rw [tweakReserved_iff] at hcond
      refine ⟨ha, ?_, ?_⟩
      · intro B hB
        by_cases hBB : B = (F.cch i t₀ m₀).1
        · rw [hBB, hbtwC]; simp
        · rw [hrest B hBB] at hB
          exact List.mem_append_left _ (hb B hB)
      · intro t' ht'
        rcases List.mem_append.mp ht' with ht' | ht'
        · exact hc t' ht'
        · rw [List.mem_singleton.mp ht']
          exact hcond

/-- **Deferred sampling, one step.**  Drawing the hidden inputs and then running a game step
through the lazy oracle has the same distribution as running the step of the modified phase one
and then drawing the hidden inputs. -/
theorem pre_intertwine_step [DecidableEq Tweak] [SampleableType M'] (emb : M' → M)
    (hsingle : ∀ t m, (F.tch t m).2 = [])
    (btw : Blk → Tweak) (hbtwT : ∀ t m, btw (F.tch t m).1 = t)
    (hbtwC : ∀ i t m, btw (F.cch i t m).1 = t) (t : F.padvS.Domain)
    (s : PreSimState Tweak St Blk) (hI : PreInv btw s) :
    (prePhi F emb s >>= fun p => (simulateQ chainRO ((preGameM F emb t).run p.1)).run p.2) =ᵈ
      ((preSim F t).run s >>= fun z => prePhi F emb z.2 >>= fun p => pure ((z.1, p.1), p.2)) := by
  obtain ⟨⟨qs, tw⟩, c⟩ := s
  have eL : (prePhi F emb ((qs, tw), c) >>= fun p =>
        (simulateQ chainRO ((preGameM F emb t).run p.1)).run p.2) =
      hideDraw qs >>= fun xs => (simulateQ chainRO ((preGameM F emb t).run (preQs xs, tw))).run
        (patch c (hidMap (preCell F emb) xs)) := by
    simp only [prePhi, bind_map_left]
  rw [eL]
  rcases t with n | q | t | q
  · have eR : ((preSim F (.inl n)).run ((qs, tw), c) >>= fun z => prePhi F emb z.2 >>= fun p =>
          (pure ((z.1, p.1), p.2) : ProbComp _)) =
        (unifSpec.query n : ProbComp (Fin (n + 1))) >>= fun u => hideDraw qs >>= fun xs =>
          pure ((u, (preQs xs, tw)), patch c (hidMap (preCell F emb) xs)) := by
      simp only [preSim, prePhi, StateT.run_mk, bind_map_left]
      rfl
    rw [eR]
    refine evalDistEq_bind_swap_of_support _ _ _ _ fun xs hxs => ?_
    rw [run_preGameM_inl, map_eq_bind_pure_comp]
    exact .rfl
  · have eR : ((preSim F (.inr (.inl q))).run ((qs, tw), c) >>= fun z =>
          prePhi F emb z.2 >>= fun p => (pure ((z.1, p.1), p.2) : ProbComp _)) =
        ((chainRO (St := St) (Blk := Blk)) (.inr (.inl q))).run c >>= fun z =>
          hideDraw qs >>= fun xs =>
            pure ((z.1, (preQs xs, tw)), patch z.2 (hidMap (preCell F emb) xs)) := by
      simp only [preSim, prePhi, StateT.run_mk, bind_map_left]
    rw [eR]
    refine evalDistEq_bind_swap_of_support _ _ _ _ fun xs hxs => ?_
    rw [run_preGameM_pub, chainRO_run_pub_patch, Functor.map_map, map_eq_bind_pure_comp]
    exact .rfl
  · have hcond_iff : ∀ xs ∈ support (hideDraw (M' := M') qs),
        (F.numTargets ≤ (preQs xs).length ∨ ¬ TweakFresh Prod.fst (preQs xs) tw t) ↔
          (F.numTargets ≤ qs.length ∨ ¬ TweakFresh Prod.fst qs tw t) := by
      intro xs hxs
      rw [preQs_length hxs]
      simp only [TweakFresh, tweakReserved_iff, preQs_map_fst hxs]
    by_cases hcond : F.numTargets ≤ qs.length ∨ ¬ TweakFresh Prod.fst qs tw t
    · have eR : ((preSim F (.inr (.inr (.inl t)))).run ((qs, tw), c) >>= fun z =>
            prePhi F emb z.2 >>= fun p => (pure ((z.1, p.1), p.2) : ProbComp _)) =
          hideDraw qs >>= fun xs =>
            pure ((none, (preQs xs, tw)), patch c (hidMap (preCell F emb) xs)) := by
        simp only [preSim, prePhi, StateT.run_mk, hcond, ite_true, pure_bind, bind_map_left]
      rw [eR]
      refine EvalDistEq.bind_congr_of_support _ fun xs hxs => ?_
      rw [run_preGameM_chal emb hsingle, ite_eq_left_of_eq_true _ _ (eq_true ((hcond_iff xs hxs).2 hcond))]
    · have eR : ((preSim F (.inr (.inr (.inl t)))).run ((qs, tw), c) >>= fun z =>
            prePhi F emb z.2 >>= fun p => (pure ((z.1, p.1), p.2) : ProbComp _)) =
          ($ᵗ St : ProbComp St) >>= fun Y => hideDraw qs >>= fun xs =>
            ($ᵗ M' : ProbComp M') >>= fun x =>
              pure ((some (F.out Y), (preQs (xs ++ [(t, x, Y)]), tw)),
                patch c (hidMap (preCell F emb) (xs ++ [(t, x, Y)]))) := by
        simp only [preSim, prePhi, StateT.run_mk, hcond, ite_false, bind_map_left,
          hideDraw_append_singleton, bind_assoc, pure_bind]
      rw [eR]
      refine evalDistEq_bind_swap_of_support _ _ _ _ fun xs hxs => ?_
      rw [run_preGameM_chal emb hsingle, ite_eq_right_of_eq_false _ _ (eq_false (fun h => hcond ((hcond_iff xs hxs).1 h)))]
      rw [not_or, not_not] at hcond
      obtain ⟨-, hres, hntw⟩ := hcond
      rw [tweakReserved_iff] at hres
      have key : ∀ x : M', (fun p : St × Cache St Blk =>
            ((some (F.out p.1), preQs xs ++ [(t, x)], tw), p.2)) <$>
            ((hS St Blk + tS St Blk).randomOracle (.inr (F.tch t (emb x)).1)).run
              (patch c (hidMap (preCell F emb) xs)) =
          ($ᵗ St : ProbComp St) >>= fun Y =>
            pure ((some (F.out Y), (preQs (xs ++ [(t, x, Y)]), tw)),
              patch c (hidMap (preCell F emb) (xs ++ [(t, x, Y)]))) := by
        intro x
        have hnone : hidMap (preCell F emb) xs (preCell F emb t x) = none := by
          refine (hidMap_eq_none_iff _ xs _).2 fun e he heq => hres ?_
          have hk : e.1 = t := by
            have := congrArg btw heq
            rwa [preCell, preCell, hbtwT, hbtwT] at this
          rw [← hk, ← map_fst_of_mem_support_hideDraw hxs]
          exact List.mem_map_of_mem (f := fun e => e.1) he
        have hc : c (.inr (preCell F emb t x)) = none := by
          by_contra hne
          refine hntw ?_
          have := hI.2.1 _ (Option.isSome_iff_ne_none.mpr hne)
          rwa [preCell, hbtwT] at this
        have hfresh : patch c (hidMap (preCell F emb) xs) (.inr (F.tch t (emb x)).1) = none := by
          rw [← hc]
          exact patch_inr_of_none c hnone
        rw [randomOracle.run_eq]
        simp only [hfresh, map_bind, map_pure]
        refine bind_congr fun (Y : St) => ?_
        rw [patch_hidMap_append _ c xs (t, x, Y) hnone]
        have hq : preQs (xs ++ [(t, x, Y)]) = preQs xs ++ [(t, x)] := by simp [preQs]
        rw [hq]
        rfl
      have e := bind_congr (x := ($ᵗ M' : ProbComp M')) key
      exact (congrArg (fun m => m =ᵈ _) e).mpr (EvalDistEq.bind_bind_swap _ _ _)
  · have hres_iff : ∀ xs ∈ support (hideDraw (M' := M') qs),
        TweakReserved Prod.fst (preQs xs) q.2.1 ↔ TweakReserved Prod.fst qs q.2.1 := by
      intro xs hxs
      rw [tweakReserved_iff, tweakReserved_iff, preQs_map_fst hxs]
    by_cases hres : TweakReserved Prod.fst qs q.2.1
    · have eR : ((preSim F (.inr (.inr (.inr q)))).run ((qs, tw), c) >>= fun z =>
            prePhi F emb z.2 >>= fun p => (pure ((z.1, p.1), p.2) : ProbComp _)) =
          hideDraw qs >>= fun xs =>
            pure ((none, (preQs xs, tw)), patch c (hidMap (preCell F emb) xs)) := by
        simp only [preSim, prePhi, StateT.run_mk, hres, ite_true, pure_bind, bind_map_left]
      rw [eR]
      refine EvalDistEq.bind_congr_of_support _ fun xs hxs => ?_
      rw [run_preGameM_coll, ite_eq_left_of_eq_true _ _ (eq_true ((hres_iff xs hxs).2 hres))]
    · have eR : ((preSim F (.inr (.inr (.inr q)))).run ((qs, tw), c) >>= fun z =>
            prePhi F emb z.2 >>= fun p => (pure ((z.1, p.1), p.2) : ProbComp _)) =
          ((chainRO (St := St) (Blk := Blk)) (.inr (.inr (F.cch q.1 q.2.1 q.2.2)))).run c >>=
            fun z => hideDraw qs >>= fun xs =>
              pure ((some (F.cout q.1 z.1), (preQs xs, tw ++ [q.2.1])),
                patch z.2 (hidMap (preCell F emb) xs)) := by
        simp only [preSim, prePhi, StateT.run_mk, hres, ite_false, bind_map_left]
      rw [eR]
      refine evalDistEq_bind_swap_of_support _ _ _ _ fun xs hxs => ?_
      have hnone : hidMap (preCell F emb) xs (F.cch q.1 q.2.1 q.2.2).1 = none := by
        refine (hidMap_eq_none_iff _ xs _).2 fun e he heq => hres ?_
        have hk : e.1 = q.2.1 := by
          have := congrArg btw heq
          rwa [preCell, hbtwT, hbtwC] at this
        rw [tweakReserved_iff, ← hk, ← map_fst_of_mem_support_hideDraw hxs]
        exact List.mem_map_of_mem (f := fun e => e.1) he
      rw [run_preGameM_coll, ite_eq_right_of_eq_false _ _ (eq_false (fun h => hres ((hres_iff xs hxs).1 h))),
        chainRO_run_chain_patch _ _ hnone, Functor.map_map, map_eq_bind_pure_comp]
      exact .rfl

/-- **Deferred sampling, phase one.**  Phase one of the ideal game has the same distribution
as the modified phase one followed by drawing a hidden input for every target. -/
theorem pre_phase1 [DecidableEq Tweak] [SampleableType M'] (emb : M' → M)
    (hsingle : ∀ t m, (F.tch t m).2 = [])
    (btw : Blk → Tweak) (hbtwT : ∀ t m, btw (F.tch t m).1 = t)
    (hbtwC : ∀ i t m, btw (F.cch i t m).1 = t) (A : PreAdv F M') :
    (simulateQ (hS St Blk + tS St Blk).romImpl (simulateQ chainToT (preProg₁ emb A))).run ∅ =ᵈ
      ((simulateQ (preSim F) A.choose).run (([], []), ∅) >>= fun z =>
        prePhi F emb z.2 >>= fun p => pure ((z.1, p.1), p.2)) := by
  have h := evalDistEq_run_of_intertwine (preGameM F emb) chainRO (preSim F) (prePhi F emb)
    (PreInv btw) (preInv_step btw hbtwC) (pre_intertwine_step emb hsingle btw hbtwT hbtwC)
    A.choose (([], []), ∅) ⟨by simp, fun B hB => by simp at hB, by simp⟩
  have e : prePhi (M' := M') F emb ((([] : List (Tweak × St)), ([] : List Tweak)), ∅) =
      pure (([], []), ∅) := by
    simp [prePhi, hideDraw_nil, hidMap_nil, preQs]
  rw [e, pure_bind] at h
  rw [simulateQ_romImpl_chainToT]
  exact h

/-- The invariant holds after the modified phase one. -/
theorem preInv_phase1 [DecidableEq Tweak] (btw : Blk → Tweak)
    (hbtwC : ∀ i t m, btw (F.cch i t m).1 = t) (A : PreAdv F M') :
    ∀ z ∈ support ((simulateQ (preSim F) A.choose).run (([], []), ∅)), PreInv btw z.2 :=
  simulateQ_run_preservesInv (preSim F) (PreInv btw) (preInv_step btw hbtwC) A.choose
    (([], []), ∅) ⟨by simp, fun B hB => by simp at hB, by simp⟩

/-! ## Phase two -/

/-- The winning check of the SM-PRE game on the adversary's answer `(j, m)`. -/
def preFin [DecidableEq Y] (F : THFam St Blk PkSeed Tweak M Y ι) (emb : M' → M) (pk : PkSeed)
    (qs : List (Tweak × M')) (jm : ℕ × M') : OracleComp (unifSpec + hS St Blk) Bool :=
  match qs[jm.1]? with
  | none => return false
  | some (t, xj) => do
      let y ← evalPub F pk t (emb jm.2)
      let y' ← evalPub F pk t (emb xj)
      return decide (y = y')

omit [DecidableEq St] [DecidableEq Blk] [SampleableType St] in
theorem preP₂_eq [DecidableEq Y] (emb : M' → M) (A : PreAdv F M') (pk : PkSeed)
    (x : A.State × SM_DT_PRE_State Tweak M') :
    preP₂ emb A pk x = A.invert x.1 pk >>= preFin F emb pk x.2.1 := by
  unfold preP₂
  refine bind_congr fun jm => ?_
  obtain ⟨j, m⟩ := jm
  rfl

/-- The good predicate of phase two, for a fixed list of targets `(tweak, chaining value)`: no
cached private-row cell with a target tweak has the target's output. -/
def PreGood (F : THFam St Blk PkSeed Tweak M Y ι) (btw : Blk → Tweak) (qs : List (Tweak × St))
    (c : Cache St Blk) : Prop :=
  ∀ B u, c (.inr B) = some u → ∀ Y', (btw B, Y') ∈ qs → F.out u ≠ F.out Y'

omit [DecidableEq St] [DecidableEq Blk] [SampleableType St] in
theorem preGood_of_inv {btw : Blk → Tweak} {s : PreSimState Tweak St Blk} (hI : PreInv btw s) :
    PreGood F btw s.1.1 s.2 := fun B u hB Y' hY =>
  absurd (List.mem_map_of_mem (f := Prod.fst) hY) (hI.2.2 _ (hI.2.1 B (by rw [hB]; rfl)))

omit [SampleableType St] in
theorem PreGood.cacheQuery_pub {btw : Blk → Tweak} {qs : List (Tweak × St)} {c : Cache St Blk}
    (h : PreGood F btw qs c) (q : St × Blk) (u : St) :
    PreGood F btw qs (c.cacheQuery (.inl q) u) := fun B u' hB =>
  h B u' (by rwa [QueryCache.cacheQuery_of_ne (t := .inl q) c u (by simp)] at hB)

/-- Caching a fresh private-row cell breaks the good predicate with probability at most `δ`. -/
theorem prEvent_not_preGood_cacheQuery_row_le {btw : Blk → Tweak} {qs : List (Tweak × St)}
    (hnd : (qs.map Prod.fst).Nodup) (δ : ℝ≥0∞) (hδ : ∀ y, Pr{let u ← $ᵗ St}[F.out u = y] ≤ δ)
    {c : Cache St Blk} (h : PreGood F btw qs c) (B : Blk) :
    Pr{let u ← ($ᵗ St : ProbComp St)}[¬ PreGood F btw qs (c.cacheQuery (.inr B) u)] ≤ δ := by
  have key : ∀ u : St, (∀ Y', (btw B, Y') ∈ qs → F.out u ≠ F.out Y') →
      PreGood F btw qs (c.cacheQuery (.inr B) u) := by
    intro u hu B' u' hB' Y' hY
    by_cases hBB : B' = B
    · subst hBB
      rw [QueryCache.cacheQuery_self] at hB'
      obtain rfl : u = u' := Option.some.inj hB'
      exact hu Y' hY
    · rw [QueryCache.cacheQuery_of_ne (t := .inr B) c u (by simpa using hBB)] at hB'
      exact h B' u' hB' Y' hY
  by_cases hex : ∃ Y', (btw B, Y') ∈ qs
  · obtain ⟨Y₀, hY₀⟩ := hex
    refine (prEvent_mono _ _ (fun u => F.out u = F.out Y₀) fun u hu => ?_).trans (hδ _)
    by_contra hne
    refine hu (key u fun Y' hY => ?_)
    have := List.inj_on_of_nodup_map hnd hY hY₀ rfl
    obtain rfl : Y' = Y₀ := (Prod.ext_iff.mp this).2
    exact hne
  · rw [prEvent_eq_zero_of_forall_not _ _ fun u => not_not.mpr
      (key u fun Y' hY => absurd ⟨Y', hY⟩ hex)]
    exact zero_le

/-- The winning check, run from a good cache patched with the hidden cells, with `cv ≠ IV` and
an answer that is not the hidden input of its target, succeeds with probability at most `δ`. -/
theorem prT_preFin_le [DecidableEq Y] [SampleableType M'] (emb : M' → M)
    (hemb : Function.Injective emb) (hsingle : ∀ t m, (F.tch t m).2 = [])
    (btw : Blk → Tweak) (hbtwT : ∀ t m, btw (F.tch t m).1 = t)
    (hinj : ∀ t m m', (F.tch t m).1 = (F.tch t m').1 → m = m')
    (δ : ℝ≥0∞) (hδ : ∀ y, Pr{let u ← $ᵗ St}[F.out u = y] ≤ δ)
    (seed : PkSeed) (cv : St) (hcv : cv ≠ F.IV) {qs : List (Tweak × St)}
    (hnd : (qs.map Prod.fst).Nodup) {xs : List (Tweak × M' × St)}
    (hxs : xs ∈ support (hideDraw qs)) {c : Cache St Blk} (hG : PreGood F btw qs c) (j : ℕ)
    (m : M') (hhit : ¬ ∃ e, xs[j]? = some e ∧ e.2.1 = m) :
    HP.prT ((simulateQ (routeRO F.IV (F.sb seed) cv) (preFin F emb seed (preQs xs) (j, m))).run'
      (patch c (hidMap (preCell F emb) xs))) ≤ δ := by
  have hq : (preQs xs)[j]? = (xs[j]?).map fun e => (e.1, e.2.1) := by simp [preQs]
  unfold preFin
  cases hj : xs[j]? with
  | none =>
    simp only [hq, hj, Option.map_none]
    simp [HP.prT_pure]
  | some e =>
    obtain ⟨t, x, Y₀⟩ := e
    simp only [hq, hj, Option.map_some]
    have hmx : x ≠ m := fun h => hhit ⟨_, hj, h⟩
    have he : (t, x, Y₀) ∈ xs := List.mem_of_getElem? hj
    have hnd' : (xs.map fun e => e.1).Nodup := by
      rw [map_fst_of_mem_support_hideDraw hxs]; exact hnd
    have hx : patch c (hidMap (preCell F emb) xs) (.inr (F.tch t (emb x)).1) = some Y₀ :=
      patch_inr_of_some c
        (hidMap_of_mem (preCell F emb) btw (fun k x => hbtwT k (emb x)) hnd' he)
    have hmnone : hidMap (preCell F emb) xs (F.tch t (emb m)).1 = none := by
      refine (hidMap_eq_none_iff _ xs _).2 fun e' he' heq => hmx ?_
      have hk : e'.1 = t := by
        have := congrArg btw heq
        rwa [preCell, hbtwT, hbtwT] at this
      obtain rfl := List.inj_on_of_nodup_map hnd' he' he hk
      exact hemb (hinj t _ _ heq)
    have hYmem : (t, Y₀) ∈ qs := by
      rw [← map_of_mem_support_hideDraw hxs]
      exact List.mem_map_of_mem (f := fun e => (e.1, e.2.2)) he
    have hjY : ∀ c' : Cache St Blk, c' (.inr (F.tch t (emb x)).1) = some Y₀ →
        ((hS St Blk + tS St Blk).randomOracle (.inr (F.tch t (emb x)).1)).run c' =
          pure (Y₀, c') := by
      intro c' hc'
      rcases randomOracle_run_row_cases (F.tch t (emb x)).1 c' with ⟨v', hv', h'⟩ | ⟨hn, -⟩
      · rw [hc'] at hv'
        obtain rfl := Option.some.inj hv'
        exact h'
      · rw [hc'] at hn
        exact absurd hn (by simp)
    unfold HP.prT
    rw [StateT.run'_eq]
    simp only [simulateQ_bind, StateT.run_bind, run_evalPub hsingle seed cv hcv, simulateQ_pure,
      StateT.run_pure]
    rcases randomOracle_run_row_cases (F.tch t (emb m)).1 (patch c (hidMap (preCell F emb) xs))
      with ⟨v, hv, h'⟩ | ⟨hnone, h'⟩
    · rw [h']
      simp only [map_pure, pure_bind, hjY _ hx]
      have hfalse : ¬ (F.out v = F.out Y₀) :=
        hG _ v (by rwa [patch_inr_of_none _ hmnone] at hv) Y₀ (by rw [hbtwT]; exact hYmem)
      simp [hfalse]
    · rw [h']
      have hne : (F.tch t (emb x)).1 ≠ (F.tch t (emb m)).1 := fun e => by
        rw [e, hnone] at hx; exact absurd hx (by simp)
      have hj' : ∀ u : St, ((patch c (hidMap (preCell F emb) xs)).cacheQuery
          (.inr (F.tch t (emb m)).1) u) (.inr (F.tch t (emb x)).1) = some Y₀ := fun u => by
        rw [QueryCache.cacheQuery_of_ne (t := .inr (F.tch t (emb m)).1)
          (patch c (hidMap (preCell F emb) xs)) u (by simpa using hne), hx]
      simp only [map_bind, bind_map_left, Functor.map_map, hjY _ (hj' _), map_pure, pure_bind]
      simp only [bind_pure_comp]
      exact (prEvent_mono ($ᵗ St) _ (fun u => F.out u = F.out Y₀)
        fun u (hu : decide (F.out u = F.out Y₀) = true) => of_decide_eq_true hu).trans (hδ _)

/-- **Phase two.**  From a state of the modified phase one satisfying the invariant, drawing
the hidden inputs and running phase two with `cv ≠ IV` returns `true` with probability at most
`(q₂ + 1)·δ + (q₂ + 1)/|M'|`. -/
theorem prT_pre_phase2_le [DecidableEq Tweak] [DecidableEq Y] [SampleableType M'] [Fintype M']
    (emb : M' → M) (hemb : Function.Injective emb) (hsingle : ∀ t m, (F.tch t m).2 = [])
    (btw : Blk → Tweak) (hbtwT : ∀ t m, btw (F.tch t m).1 = t)
    (hinj : ∀ t m m', (F.tch t m).1 = (F.tch t m').1 → m = m')
    (δ : ℝ≥0∞) (hδ : ∀ y, Pr{let u ← $ᵗ St}[F.out u = y] ≤ δ)
    (A : PreAdv F M') (q₂ : ℕ) (hq₂ : A.InvertBound q₂) (st : A.State)
    (s : PreSimState Tweak St Blk) (hI : PreInv btw s) (seed : PkSeed) (cv : St)
    (hcv : cv ≠ F.IV) :
    HP.prT (prePhi F emb s >>= fun p =>
        (simulateQ (routeRO F.IV (F.sb seed) cv) (preP₂ emb A seed (st, p.1))).run' p.2) ≤
      (q₂ + 1 : ℕ) * δ + (q₂ + 1 : ℕ) * (Fintype.card M' : ℝ≥0∞)⁻¹ := by
  classical
  obtain ⟨⟨qs, tw⟩, c⟩ := s
  have hcellinj : ∀ (k : Tweak) (x x' : M'), preCell F emb k x = preCell F emb k x' → x = x' :=
    fun k x x' h => hemb (hinj k _ _ h)
  have step1 : HP.prT (prePhi F emb ((qs, tw), c) >>= fun p =>
        (simulateQ (routeRO F.IV (F.sb seed) cv) (preP₂ emb A seed (st, p.1))).run' p.2) ≤
      HP.prT (hideDraw qs >>= fun xs =>
        (simulateQ (routeRO F.IV (F.sb seed) cv) (A.invert st seed)).run c >>= fun z =>
          if HiddenRead (hidMap (preCell F emb) xs) z.2 then pure true
          else (simulateQ (routeRO F.IV (F.sb seed) cv) (preFin F emb seed (preQs xs) z.1)).run'
            (patch z.2 (hidMap (preCell F emb) xs))) := by
    simp only [prePhi, bind_map_left]
    refine HP.prT_bind_mono _ _ _ fun xs hxs => ?_
    have hnr := not_hiddenRead_of_inv (F := F) emb btw hbtwT hI hxs
    have e : (simulateQ (routeRO F.IV (F.sb seed) cv)
          (preP₂ emb A seed (st, (preQs xs, tw)))).run' (patch c (hidMap (preCell F emb) xs)) =
        (simulateQ (hS St Blk + tS St Blk).romImpl
          (simulateQ (route F.IV (F.sb seed) cv) (A.invert st seed))).run
            (patch c (hidMap (preCell F emb) xs)) >>= fun z =>
          (simulateQ (routeRO F.IV (F.sb seed) cv) (preFin F emb seed (preQs xs) z.1)).run' z.2 := by
      rw [preP₂_eq, simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind,
        simulateQ_romImpl_route]
      rfl
    rw [e]
    refine (prT_run_romImpl_patch_le _ _ _ c hnr).trans (le_of_eq ?_)
    rw [simulateQ_romImpl_route]
  refine step1.trans ?_
  rw [HP.prT_swap]
  refine (HP.prT_bind_le_prEvent_add _ _ (fun z => ¬ PreGood F btw qs z.2)
    (ε := δ + ((q₂ : ℝ≥0∞) * (Fintype.card M' : ℝ≥0∞)⁻¹ + (Fintype.card M' : ℝ≥0∞)⁻¹))
    fun z hz hgood => ?_).trans ?_
  · rw [not_not] at hgood
    refine (HP.prT_bind_le_prEvent_add (hideDraw qs) _
      (fun xs => HiddenRead (hidMap (preCell F emb) xs) z.2 ∨
        ∃ e, xs[z.1.1]? = some e ∧ e.2.1 = z.1.2) (ε := δ) fun xs hxs hne => ?_).trans ?_
    · rw [not_or] at hne
      simp only [hne.1, ite_false]
      exact prT_preFin_le emb hemb hsingle btw hbtwT hinj δ hδ seed cv hcv hI.1 hxs hgood
        z.1.1 z.1.2 hne.2
    · rw [add_comm]
      refine add_le_add le_rfl ((prEvent_or_le _ _ _).trans
        (add_le_add ?_ (prEvent_hideDraw_getElem_le qs hI.1 _ _)))
      have hpot := routeRO_potential_le F.IV (F.sb seed) cv
        (fun c' : Cache St Blk =>
          Pr{let xs ← hideDraw (M' := M') qs}[HiddenRead (hidMap (preCell F emb) xs) c'])
        (Fintype.card M' : ℝ≥0∞)⁻¹
        (fun c' q u => prEvent_mono _ _ _ fun xs h => hiddenRead_cacheQuery_pub h)
        (fun c' B u => (prEvent_mono _ _ _ fun xs h => hiddenRead_cacheQuery_row h).trans
          ((prEvent_or_le _ _ _).trans (add_le_add le_rfl
            (prEvent_hideDraw_cell_le (preCell F emb) btw (fun k x => hbtwT k (emb x)) hcellinj
              qs hI.1 B))))
        (A.invert st seed) q₂ (hq₂ st seed) c z hz
      refine hpot.trans (le_of_eq ?_)
      rw [prEvent_eq_zero_of_forall_mem_support _ _ fun xs hxs =>
        not_hiddenRead_of_inv (F := F) emb btw hbtwT hI hxs, zero_add]
  · refine (add_le_add_left (prEvent_routeRO_bad_le F.IV (F.sb seed) cv
      (fun c => ¬ PreGood F btw qs c) δ
      (fun c q u hc _ => not_not.mpr ((not_not.mp hc).cacheQuery_pub q u))
      (fun c B hc _ => prEvent_not_preGood_cacheQuery_row_le hI.1 δ hδ (not_not.mp hc) B)
      (A.invert st seed) q₂ (hq₂ st seed) c (not_not.mpr (preGood_of_inv hI))) _).trans
      (le_of_eq ?_)
    push_cast
    ring

end Lemmas

/-- **The ideal SM-PRE game.**  When the attacked member has a single message block after the
seed block, tweaks are recoverable from first blocks (`btw`), the first block is injective in
the message for a fixed tweak, and `emb` is injective, the ideal game of `preProg₁ emb A`,
`preP₂ emb A` is won with probability at most `(q₂ + 1)·δ + (q₂ + 1)/|M'| + 1/|St|`, where
`q₂` bounds the compression queries of `A.invert` and `δ` the probability that the output map
hits a fixed value on a uniform chaining value. -/
theorem pre_ideal_le [Fintype St] [DecidableEq St] [DecidableEq Blk] [SampleableType St]
    [DecidableEq Tweak] [DecidableEq Y] [SampleableType M'] [Fintype M']
    (emb : M' → M) (hemb : Function.Injective emb)
    (hsingle : ∀ t m, (F.tch t m).2 = [])
    (btw : Blk → Tweak) (hbtwT : ∀ t m, btw (F.tch t m).1 = t)
    (hbtwC : ∀ i t m, btw (F.cch i t m).1 = t)
    (hinj : ∀ t m m', (F.tch t m).1 = (F.tch t m').1 → m = m')
    (δ : ℝ≥0∞) (hδ : ∀ y, Pr{let u ← $ᵗ St}[F.out u = y] ≤ δ)
    (A : PreAdv F M') (q₂ : ℕ) (hq₂ : A.InvertBound q₂) :
    𝒟[idealGame F.IV F.sb F.seedGen (preProg₁ emb A) (preP₂ emb A)] {true} ≤
      (q₂ + 1 : ℕ) * δ + (q₂ + 1 : ℕ) * (Fintype.card M' : ℝ≥0∞)⁻¹ +
        (Fintype.card St : ℝ≥0∞)⁻¹ := by
  rw [← HP.prT_eq, idealGame_eq_phases]
  rw [prT_congr_evalDistEq ((pre_phase1 emb hsingle btw hbtwT hbtwC A).bind_left _)]
  simp only [bind_assoc, pure_bind]
  refine HP.prT_bind_le_of_forall_le _ _ fun z hz => ?_
  have hI := preInv_phase1 btw hbtwC A z hz
  rw [HP.prT_swap]
  refine HP.prT_bind_le_of_forall_le _ _ fun seed _ => ?_
  rw [HP.prT_swap]
  refine (HP.prT_bind_le_prEvent_add _ _ (fun cv => cv = F.IV)
    (ε := (q₂ + 1 : ℕ) * δ + (q₂ + 1 : ℕ) * (Fintype.card M' : ℝ≥0∞)⁻¹)
    fun cv _ hcv => ?_).trans ?_
  · exact prT_pre_phase2_le emb hemb hsingle btw hbtwT hinj δ hδ A q₂ hq₂ z.1 z.2 hI seed cv hcv
  · rw [SampleableType.prEvent_uniformSample_eq_singleton, add_comm]

end Ideal

#print axioms Ideal.pre_phase1
#print axioms Ideal.pre_ideal_le
