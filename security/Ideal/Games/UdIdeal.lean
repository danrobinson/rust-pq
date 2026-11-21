import Ideal.Games.UdBridge
import Ideal.Games.PreIdeal
import Ideal.Core.HiddenPrefix

/-!
# SM-UD in the ideal-compression model: the two ideal (hidden-prefix) games

`ud_ideal_le`: when the attacked member has a single message block after the seed block and the
output map sends the uniform distribution on chaining values to the uniform distribution on
`Y`, the ideal game of the real-world programs `udProg₁ .real emb A`, `udP₂ A` returns `true`
at most `q₂/|M'|` more often than the ideal game of the ideal-world programs
`udProg₁ .ideal emb A`, `udP₂ A`; `q₂` is the number of compression queries of the adversary's
second phase.

Proof.  Both phase ones are compared with the modified phase one `preSim` of the SM-PRE
analysis (`Games/PreIdeal.lean`), whose challenge oracle draws a chaining value `Y`, returns
`F.out Y`, records `(t, Y)` and touches no private-row cell.

* *Real world* (`ud_phase1_real`).  A step of the real-world game from the state
  `udPj s` is the corresponding step of the SM-PRE game from `s` with the hidden inputs
  forgotten (`udGameM_real_run_pj`), so the SM-PRE intertwining `pre_intertwine_step` gives:
  real-world phase one `=ᵈ` `preSim`, then independent hidden inputs (`hideDraw`) whose cells
  are laid over the cache (`patch`/`hidMap`).
* *Ideal world* (`ud_phase1_ideal`).  A step of the ideal-world game is a step of `preSim`
  with the chaining values forgotten, because `F.out Y` is uniform (`hout`): ideal-world phase
  one `=ᵈ` `preSim` with the cache left unpatched.
* *Phase two* (`prT_ud_phase2_le`).  `distinguish` run from the patched cache is dominated by
  its run from the unpatched cache until a hidden cell is read (`prT_run_romImpl_patch_le`);
  on every run the probability over the hidden inputs that a cell cached by the run is hidden
  is `≤ q₂/|M'|` (`routeRO_potential_le`, `prEvent_hideDraw_cell_le`).

`hiddenPrefix_ge`: the converse direction of `hiddenPrefix` (ideal ≤ real + error), obtained by
applying `hiddenPrefix` to the negated phase two.
-/

open OracleComp OracleSpec ENNReal

namespace Ideal

open TweakableHash

variable {St Blk PkSeed Tweak M M' Y ι : Type} {F : THFam St Blk PkSeed Tweak M Y ι}

/-! ## Probability helpers -/

section Helpers

variable {α : Type}

theorem prT_bind_le_add_const_all (mx : ProbComp α) (f g : α → ProbComp Bool) (ε : ℝ≥0∞)
    (h : ∀ x, HP.prT (f x) ≤ HP.prT (g x) + ε) :
    HP.prT (mx >>= f) ≤ HP.prT (mx >>= g) + ε := by
  unfold HP.prT at h ⊢
  let : MeasurableSpace α := ⊤
  rw [prEvent_bind_eq_lintegral_of_discrete, prEvent_bind_eq_lintegral_of_discrete]
  calc ∫⁻ a, Pr{let y ← f a}[y = true] ∂𝒟[mx]
      ≤ ∫⁻ a, (Pr{let y ← g a}[y = true] + ε) ∂𝒟[mx] := MeasureTheory.lintegral_mono h
    _ = ∫⁻ a, Pr{let y ← g a}[y = true] ∂𝒟[mx] + ε * 𝒟[mx] Set.univ := by
        rw [MeasureTheory.lintegral_add_right _ measurable_const, MeasureTheory.lintegral_const]
    _ ≤ _ := add_le_add le_rfl (mul_le_of_le_one_right' (evalDist_apply_univ_le_one mx))

/-- A comparison up to an additive constant of the continuations on the possible outputs
survives a common draw. -/
theorem prT_bind_le_add_const (mx : ProbComp α) (f g : α → ProbComp Bool) (ε : ℝ≥0∞)
    (h : ∀ x ∈ support mx, HP.prT (f x) ≤ HP.prT (g x) + ε) :
    HP.prT (mx >>= f) ≤ HP.prT (mx >>= g) + ε := by
  rw [bind_eq_attach_bind mx f, bind_eq_attach_bind mx g]
  exact prT_bind_le_add_const_all _ _ _ ε fun a => h a.1 a.2

/-- Negating a Boolean experiment complements its success probability. -/
theorem prT_not (X : ProbComp Bool) : HP.prT (not <$> X) = 1 - HP.prT X := by
  unfold HP.prT
  rw [prEvent_map, ← prEvent_not_eq_one_sub]
  refine le_antisymm (prEvent_mono _ _ _ fun b hb => ?_) (prEvent_mono _ _ _ fun b hb => ?_)
  · cases b <;> simp_all
  · cases b <;> simp_all

theorem evalDistEq_of_eq {mx my : ProbComp α} (h : mx = my) : mx =ᵈ my := h ▸ .rfl

end Helpers

/-! ## The converse hidden-prefix hop -/

section HiddenPrefixGe

variable {σ : Type}

theorem realGame_not [SampleableType (CF St Blk)] (IV : St) (sb : PkSeed → Blk)
    (seedGen : ProbComp PkSeed) (prog₁ : OracleComp (unifSpec + (hS St Blk + chainS St Blk)) σ)
    (P₂ : PkSeed → σ → OracleComp (unifSpec + hS St Blk) Bool) :
    realGame IV sb seedGen prog₁ (fun pk x => not <$> P₂ pk x) =
      not <$> realGame IV sb seedGen prog₁ P₂ := by
  simp only [realGame, simulateQ_map, map_bind]

theorem idealGame_not [DecidableEq St] [DecidableEq Blk] [SampleableType St] (IV : St)
    (sb : PkSeed → Blk) (seedGen : ProbComp PkSeed)
    (prog₁ : OracleComp (unifSpec + (hS St Blk + chainS St Blk)) σ)
    (P₂ : PkSeed → σ → OracleComp (unifSpec + hS St Blk) Bool) :
    idealGame IV sb seedGen prog₁ (fun pk x => not <$> P₂ pk x) =
      not <$> idealGame IV sb seedGen prog₁ P₂ := by
  simp only [idealGame_eq_phases, simulateQ_map, map_bind, StateT.run'_eq, StateT.run_map,
    Functor.map_map]

/-- **The converse hidden-prefix hop**: the ideal game returns `true` at most as often as the
real game, up to the error of `hiddenPrefix`. -/
theorem hiddenPrefix_ge [Fintype St] [DecidableEq St] [DecidableEq Blk] [SampleableType St]
    [Finite Blk] [SampleableType (CF St Blk)]
    (IV : St) (sb : PkSeed → Blk) (hsb : Function.Injective sb) (seedGen : ProbComp PkSeed)
    (γ : ℝ≥0∞) (hγ : ∀ s, Pr{let s' ← seedGen}[s' = s] ≤ γ)
    (prog₁ : OracleComp (unifSpec + (hS St Blk + chainS St Blk)) σ)
    (P₂ : PkSeed → σ → OracleComp (unifSpec + hS St Blk) Bool) (q₁ C L : ℕ)
    (hq : IsQueryBoundP prog₁ (fun i => isPub i = true) q₁)
    (hC : IsQueryBoundP prog₁ (fun i => isChain i = true) C)
    (hL : AllQueriesSatisfy prog₁ (chainLenLe L)) :
    𝒟[idealGame IV sb seedGen prog₁ P₂] {true} ≤
      𝒟[realGame IV sb seedGen prog₁ P₂] {true} + q₁ * γ +
        (2 * q₁ + C * (1 + 2 * L) + 1 : ℕ) * (Fintype.card St : ℝ≥0∞)⁻¹ := by
  have h := hiddenPrefix IV sb hsb seedGen γ hγ prog₁ (fun pk x => not <$> P₂ pk x) q₁ C L
    hq hC hL
  rw [realGame_not, idealGame_not, ← HP.prT_eq, ← HP.prT_eq, prT_not, prT_not] at h
  rw [← HP.prT_eq, ← HP.prT_eq]
  have hb := HP.prT_le_one (idealGame IV sb seedGen prog₁ P₂)
  rw [← ENNReal.sub_sub_cancel ENNReal.one_ne_top hb, tsub_le_iff_left]
  calc (1 : ℝ≥0∞) ≤ (1 - HP.prT (realGame IV sb seedGen prog₁ P₂)) +
        HP.prT (realGame IV sb seedGen prog₁ P₂) := le_tsub_add
    _ ≤ _ := by
      refine (add_le_add h le_rfl).trans (le_of_eq ?_)
      ring

end HiddenPrefixGe

section Lemmas

variable [DecidableEq St] [DecidableEq Blk] [SampleableType St]

/-! ## Phase one: the game steps through the lazy oracle -/

/-- Forget the payloads of the target list. -/
def udPj {Q : Type} (s : List (Tweak × Q) × List Tweak) : SM_DT_UD_State Tweak :=
  (s.1.map Prod.fst, s.2)

omit [DecidableEq St] [DecidableEq Blk] [SampleableType St] in
theorem tweakReserved_map_fst {Q : Type} (l : List (Tweak × Q)) (t : Tweak) :
    TweakReserved (Q := Tweak) id (l.map Prod.fst) t ↔ TweakReserved Prod.fst l t := by
  simp [TweakReserved]

omit [DecidableEq St] [DecidableEq Blk] [SampleableType St] in
theorem udCond_map_fst {Q : Type} (N : ℕ) (l : List (Tweak × Q)) (tw : List Tweak) (t : Tweak) :
    (N ≤ (l.map Prod.fst).length ∨ ¬ TweakFresh id (l.map Prod.fst) tw t) ↔
      (N ≤ l.length ∨ ¬ TweakFresh Prod.fst l tw t) := by
  simp only [List.length_map, TweakFresh, tweakReserved_map_fst]

omit [DecidableEq St] [DecidableEq Blk] [SampleableType St] in
/-- A step of the real-world SM-UD game is the step of the SM-PRE game with the hidden inputs
forgotten. -/
theorem udGameM_real_run_pj [DecidableEq Tweak] [SampleableType M'] [SampleableType Y]
    (emb : M' → M) (t : F.padvS.Domain) (s : SM_DT_PRE_State Tweak M') :
    (udGameM F .real emb t).run (udPj s) =
      (fun w => (w.1, udPj w.2)) <$> (preGameM F emb t).run s := by
  obtain ⟨qs, tw⟩ := s
  rcases t with n | q | t | q
  · rw [udGameM_run_inl, preGameM_run_inl]; simp
  · rw [udGameM_run_h, preGameM_run_h]; simp
  · rw [udGameM_run_chal_real, preGameM_run_chal]
    by_cases h : F.numTargets ≤ qs.length ∨ ¬ TweakFresh Prod.fst qs tw t
    · have h' : F.numTargets ≤ (udPj (qs, tw)).1.length ∨
          ¬ TweakFresh id (udPj (qs, tw)).1 (udPj (qs, tw)).2 t :=
        (udCond_map_fst F.numTargets qs tw t).2 h
      simp only [h', h, ↓reduceIte]; simp [udPj]
    · have h' : ¬ (F.numTargets ≤ (udPj (qs, tw)).1.length ∨
          ¬ TweakFresh id (udPj (qs, tw)).1 (udPj (qs, tw)).2 t) :=
        fun hh => h ((udCond_map_fst F.numTargets qs tw t).1 hh)
      simp only [h', h, ↓reduceIte]; simp [udPj]
  · rw [udGameM_run_coll, preGameM_run_coll]
    by_cases h : TweakReserved Prod.fst qs q.2.1
    · have h' : TweakReserved (Q := Tweak) id (udPj (qs, tw)).1 q.2.1 :=
        (tweakReserved_map_fst qs q.2.1).2 h
      simp only [h', h, ↓reduceIte]; simp [udPj]
    · have h' : ¬ TweakReserved (Q := Tweak) id (udPj (qs, tw)).1 q.2.1 :=
        fun hh => h ((tweakReserved_map_fst qs q.2.1).1 hh)
      simp only [h', h, ↓reduceIte]; simp [udPj]

theorem run_udGameM_inl [DecidableEq Tweak] [SampleableType M'] [SampleableType Y]
    (world : SM_DT_UD_World) (emb : M' → M) (n : ℕ) (s : SM_DT_UD_State Tweak)
    (c : Cache St Blk) :
    (simulateQ chainRO ((udGameM F world emb (.inl n)).run s)).run c =
      (fun u => ((u, s), c)) <$> (unifSpec.query n : ProbComp (Fin (n + 1))) := by
  have h : (simulateQ chainRO ((udGameM F world emb (.inl n)).run s)).run c =
      (fun p => ((p.1, s), p.2)) <$> ((chainRO (St := St) (Blk := Blk)) (.inl n)).run c := by
    simp [udGameM]
  rw [h, chainRO_run_inl, Functor.map_map]

theorem run_udGameM_pub [DecidableEq Tweak] [SampleableType M'] [SampleableType Y]
    (world : SM_DT_UD_World) (emb : M' → M) (q : St × Blk) (s : SM_DT_UD_State Tweak)
    (c : Cache St Blk) :
    (simulateQ chainRO ((udGameM F world emb (.inr (.inl q))).run s)).run c =
      (fun p => ((p.1, s), p.2)) <$>
        ((chainRO (St := St) (Blk := Blk)) (.inr (.inl q))).run c := by
  simp [udGameM]

theorem run_udGameM_chal_ideal [DecidableEq Tweak] [SampleableType M'] [SampleableType Y]
    (emb : M' → M) (t : Tweak) (s : SM_DT_UD_State Tweak) (c : Cache St Blk) :
    (simulateQ chainRO ((udGameM F .ideal emb (.inr (.inr (.inl t)))).run s)).run c =
      if F.numTargets ≤ s.1.length ∨ ¬ TweakFresh id s.1 s.2 t then pure ((none, s), c)
      else (fun y => ((some y, (s.1 ++ [t], s.2)), c)) <$> ($ᵗ Y : ProbComp Y) := by
  rw [udGameM_run_chal_ideal]
  by_cases h : F.numTargets ≤ s.1.length ∨ ¬ TweakFresh id s.1 s.2 t
  · simp [h]
  · simp only [h, ite_false, simulateQ_bind, StateT.run_bind, run_chainRO_liftM, bind_map_left]
    simp [map_eq_bind_pure_comp]

theorem run_udGameM_coll [DecidableEq Tweak] [SampleableType M'] [SampleableType Y]
    (world : SM_DT_UD_World) (emb : M' → M) (q : (i : ι) × Tweak × F.Msg i)
    (s : SM_DT_UD_State Tweak) (c : Cache St Blk) :
    (simulateQ chainRO ((udGameM F world emb (.inr (.inr (.inr q)))).run s)).run c =
      if TweakReserved (Q := Tweak) id s.1 q.2.1 then pure ((none, s), c)
      else (fun p => ((some (F.cout q.1 p.1), s.1, s.2 ++ [q.2.1]), p.2)) <$>
        ((chainRO (St := St) (Blk := Blk)) (.inr (.inr (F.cch q.1 q.2.1 q.2.2)))).run c := by
  rw [udGameM_run_coll]
  by_cases h : TweakReserved (Q := Tweak) id s.1 q.2.1 <;> simp [h]

/-! ## Phase one of the two worlds against the modified phase one `preSim` -/

/-- From a state of the modified phase one to a state of the real-world game: draw a hidden
input for every target, lay the hidden cells over the cache, forget the hidden inputs. -/
noncomputable def udPhiR [SampleableType M'] (F : THFam St Blk PkSeed Tweak M Y ι)
    (emb : M' → M) (s : PreSimState Tweak St Blk) :
    ProbComp (SM_DT_UD_State Tweak × Cache St Blk) :=
  (fun p => (udPj p.1, p.2)) <$> prePhi F emb s

/-- From a state of the modified phase one to a state of the ideal-world game: forget the
chaining values of the targets. -/
def udPhiI (s : PreSimState Tweak St Blk) : ProbComp (SM_DT_UD_State Tweak × Cache St Blk) :=
  pure (udPj s.1, s.2)

/-- **Deferred sampling, one step, real world.** -/
theorem ud_intertwine_real [DecidableEq Tweak] [SampleableType M'] [SampleableType Y]
    (emb : M' → M) (hsingle : ∀ t m, (F.tch t m).2 = [])
    (btw : Blk → Tweak) (hbtwT : ∀ t m, btw (F.tch t m).1 = t)
    (hbtwC : ∀ i t m, btw (F.cch i t m).1 = t) (t : F.padvS.Domain)
    (s : PreSimState Tweak St Blk) (hI : PreInv btw s) :
    (udPhiR F emb s >>= fun p =>
        (simulateQ chainRO ((udGameM F .real emb t).run p.1)).run p.2) =ᵈ
      ((preSim F t).run s >>= fun z => udPhiR F emb z.2 >>= fun p => pure ((z.1, p.1), p.2)) := by
  have h := EvalDistEq.map_congr
    (fun w : (F.padvS.Range t × SM_DT_PRE_State Tweak M') × Cache St Blk =>
      ((w.1.1, udPj w.1.2), w.2))
    (pre_intertwine_step emb hsingle btw hbtwT hbtwC t s hI)
  have eL : (udPhiR F emb s >>= fun p =>
        (simulateQ chainRO ((udGameM F .real emb t).run p.1)).run p.2) =
      (fun w : (F.padvS.Range t × SM_DT_PRE_State Tweak M') × Cache St Blk =>
        ((w.1.1, udPj w.1.2), w.2)) <$>
        (prePhi F emb s >>= fun p => (simulateQ chainRO ((preGameM F emb t).run p.1)).run p.2) := by
    simp only [udPhiR, bind_map_left, map_bind, udGameM_real_run_pj, simulateQ_map,
      StateT.run_map]
  have eR : ((preSim F t).run s >>= fun z => udPhiR F emb z.2 >>= fun p =>
        (pure ((z.1, p.1), p.2) : ProbComp _)) =
      (fun w : (F.padvS.Range t × SM_DT_PRE_State Tweak M') × Cache St Blk =>
        ((w.1.1, udPj w.1.2), w.2)) <$>
        ((preSim F t).run s >>= fun z => prePhi F emb z.2 >>= fun p =>
          pure ((z.1, p.1), p.2)) := by
    simp only [udPhiR, bind_map_left, map_bind, map_pure]
  rw [eL, eR]
  exact h

/-- **One step, ideal world**: a step of the ideal-world game through the lazy oracle is the
step of the modified phase one with the chaining values of the targets forgotten. -/
theorem ud_intertwine_ideal [DecidableEq Tweak] [SampleableType M'] [SampleableType Y]
    [Finite Y] (emb : M' → M)
    (hout : ∀ p : Y → Prop, Pr{let u ← $ᵗ St}[p (F.out u)] = Pr{let y ← $ᵗ Y}[p y])
    (t : F.padvS.Domain) (s : PreSimState Tweak St Blk) :
    (udPhiI s >>= fun p => (simulateQ chainRO ((udGameM F .ideal emb t).run p.1)).run p.2) =ᵈ
      ((preSim F t).run s >>= fun z => udPhiI z.2 >>= fun p => pure ((z.1, p.1), p.2)) := by
  obtain ⟨⟨qs, tw⟩, c⟩ := s
  simp only [udPhiI, pure_bind]
  rcases t with n | q | t | q
  · refine evalDistEq_of_eq ?_
    rw [run_udGameM_inl]
    simp [preSim, udPj]
  · refine evalDistEq_of_eq ?_
    rw [run_udGameM_pub]
    simp [preSim, udPj]
  · rw [run_udGameM_chal_ideal]
    by_cases h : F.numTargets ≤ qs.length ∨ ¬ TweakFresh Prod.fst qs tw t
    · have h' : F.numTargets ≤ (udPj (qs, tw)).1.length ∨
          ¬ TweakFresh id (udPj (qs, tw)).1 (udPj (qs, tw)).2 t :=
        (udCond_map_fst F.numTargets qs tw t).2 h
      refine evalDistEq_of_eq ?_
      simp only [h', ↓reduceIte]
      simp [preSim, h, udPj]
    · have h' : ¬ (F.numTargets ≤ (udPj (qs, tw)).1.length ∨
          ¬ TweakFresh id (udPj (qs, tw)).1 (udPj (qs, tw)).2 t) :=
        fun hh => h ((udCond_map_fst F.numTargets qs tw t).1 hh)
      have hu : (F.out <$> ($ᵗ St : ProbComp St)) =ᵈ ($ᵗ Y : ProbComp Y) := by
        apply OracleComp.evalDistEq_of_forall_prEvent_eq_output
        intro y
        rw [prEvent_map]
        exact hout (· = y)
      have e : ((preSim F (.inr (.inr (.inl t)))).run ((qs, tw), c) >>= fun z =>
            (pure ((z.1, udPj z.2.1), z.2.2) : ProbComp _)) =
          (fun y => ((some y, ((udPj (qs, tw)).1 ++ [t], (udPj (qs, tw)).2)), c)) <$>
            (F.out <$> ($ᵗ St : ProbComp St)) := by
        simp [preSim, h, udPj, map_eq_bind_pure_comp]
      simp only [h', ↓reduceIte]
      rw [e]
      exact (EvalDistEq.map_congr _ hu).symm
  · rw [run_udGameM_coll]
    by_cases h : TweakReserved Prod.fst qs q.2.1
    · have h' : TweakReserved (Q := Tweak) id (udPj (qs, tw)).1 q.2.1 :=
        (tweakReserved_map_fst qs q.2.1).2 h
      refine evalDistEq_of_eq ?_
      simp only [h', ↓reduceIte]
      simp [preSim, h, udPj]
    · have h' : ¬ TweakReserved (Q := Tweak) id (udPj (qs, tw)).1 q.2.1 :=
        fun hh => h ((tweakReserved_map_fst qs q.2.1).1 hh)
      refine evalDistEq_of_eq ?_
      simp only [h', ↓reduceIte]
      simp [preSim, h, udPj, map_eq_bind_pure_comp]

/-- **Phase one, real world.**  Phase one of the ideal game of the real-world programs has the
same distribution as the modified phase one followed by drawing a hidden input for every
target and laying the hidden cells over the cache. -/
theorem ud_phase1_real [DecidableEq Tweak] [SampleableType M'] [SampleableType Y] (emb : M' → M)
    (hsingle : ∀ t m, (F.tch t m).2 = [])
    (btw : Blk → Tweak) (hbtwT : ∀ t m, btw (F.tch t m).1 = t)
    (hbtwC : ∀ i t m, btw (F.cch i t m).1 = t) (A : UdAdv F) :
    (simulateQ (hS St Blk + tS St Blk).romImpl
        (simulateQ chainToT (udProg₁ .real emb A))).run ∅ =ᵈ
      ((simulateQ (preSim F) A.pick).run (([], []), ∅) >>= fun z =>
        udPhiR F emb z.2 >>= fun p => pure ((z.1, p.1), p.2)) := by
  have h := evalDistEq_run_of_intertwine (udGameM F .real emb) chainRO (preSim F) (udPhiR F emb)
    (PreInv btw) (preInv_step btw hbtwC) (ud_intertwine_real emb hsingle btw hbtwT hbtwC)
    A.pick (([], []), ∅) ⟨by simp, fun B hB => by simp at hB, by simp⟩
  have e : udPhiR (M' := M') F emb ((([] : List (Tweak × St)), ([] : List Tweak)), ∅) =
      pure (([], []), ∅) := by
    simp [udPhiR, udPj, prePhi, hideDraw_nil, hidMap_nil, preQs]
  rw [e, pure_bind] at h
  rw [simulateQ_romImpl_chainToT]
  exact h

/-- **Phase one, ideal world.**  Phase one of the ideal game of the ideal-world programs has
the same distribution as the modified phase one (cache unpatched). -/
theorem ud_phase1_ideal [DecidableEq Tweak] [SampleableType M'] [SampleableType Y] [Finite Y]
    (emb : M' → M)
    (hout : ∀ p : Y → Prop, Pr{let u ← $ᵗ St}[p (F.out u)] = Pr{let y ← $ᵗ Y}[p y])
    (A : UdAdv F) :
    (simulateQ (hS St Blk + tS St Blk).romImpl
        (simulateQ chainToT (udProg₁ .ideal emb A))).run ∅ =ᵈ
      ((simulateQ (preSim F) A.pick).run (([], []), ∅) >>= fun z =>
        udPhiI z.2 >>= fun p => pure ((z.1, p.1), p.2)) := by
  have h := evalDistEq_run_of_intertwine (udGameM F .ideal emb) chainRO (preSim F) udPhiI
    (fun _ => True) (fun _ _ _ _ _ => trivial)
    (fun t s _ => ud_intertwine_ideal emb hout t s) A.pick (([], []), ∅) trivial
  have e : udPhiI ((([] : List (Tweak × St)), ([] : List Tweak)), (∅ : Cache St Blk)) =
      pure (([], []), ∅) := by
    simp [udPhiI, udPj]
  rw [e, pure_bind] at h
  rw [simulateQ_romImpl_chainToT]
  exact h

/-! ## Phase two -/

/-- **Phase two.**  From a state of the modified phase one satisfying the invariant, drawing
the hidden inputs and running `distinguish` from the patched cache returns `true` at most
`q₂/|M'|` more often than running it from the unpatched cache. -/
theorem prT_ud_phase2_le [DecidableEq Tweak] [SampleableType M'] [Fintype M']
    (emb : M' → M) (hemb : Function.Injective emb)
    (btw : Blk → Tweak) (hbtwT : ∀ t m, btw (F.tch t m).1 = t)
    (hinj : ∀ t m m', (F.tch t m).1 = (F.tch t m').1 → m = m')
    (A : UdAdv F) (q₂ : ℕ) (hq₂ : A.DistBound q₂) (st : A.State)
    (s : PreSimState Tweak St Blk) (hI : PreInv btw s) (seed : PkSeed) (cv : St) :
    HP.prT (udPhiR F emb s >>= fun p =>
        (simulateQ (routeRO F.IV (F.sb seed) cv) (udP₂ A seed (st, p.1))).run' p.2) ≤
      HP.prT ((simulateQ (routeRO F.IV (F.sb seed) cv) (udP₂ A seed (st, udPj s.1))).run' s.2) +
        q₂ * (Fintype.card M' : ℝ≥0∞)⁻¹ := by
  classical
  obtain ⟨⟨qs, tw⟩, c⟩ := s
  have hcellinj : ∀ (k : Tweak) (x x' : M'), preCell F emb k x = preCell F emb k x' → x = x' :=
    fun k x x' h => hemb (hinj k _ _ h)
  have step1 : HP.prT (udPhiR F emb ((qs, tw), c) >>= fun p =>
        (simulateQ (routeRO F.IV (F.sb seed) cv) (udP₂ A seed (st, p.1))).run' p.2) ≤
      HP.prT (hideDraw qs >>= fun xs =>
        (simulateQ (routeRO F.IV (F.sb seed) cv) (A.distinguish st seed)).run c >>= fun z =>
          if HiddenRead (hidMap (preCell F emb) xs) z.2 then pure true else pure z.1) := by
    simp only [udPhiR, prePhi, Functor.map_map, bind_map_left, udP₂]
    refine HP.prT_bind_mono _ _ _ fun xs hxs => ?_
    have hnr := not_hiddenRead_of_inv (F := F) emb btw hbtwT hI hxs
    have e : (simulateQ (routeRO F.IV (F.sb seed) cv) (A.distinguish st seed)).run'
          (patch c (hidMap (preCell F emb) xs)) =
        (simulateQ (hS St Blk + tS St Blk).romImpl
          (simulateQ (route F.IV (F.sb seed) cv) (A.distinguish st seed))).run
            (patch c (hidMap (preCell F emb) xs)) >>= fun z => pure z.1 := by
      rw [StateT.run'_eq, simulateQ_romImpl_route, map_eq_bind_pure_comp]
      rfl
    rw [e]
    refine (prT_run_romImpl_patch_le _ _ (fun z => pure z.1) c hnr).trans (le_of_eq ?_)
    rw [simulateQ_romImpl_route]
  refine step1.trans ?_
  rw [HP.prT_swap]
  have e2 : (simulateQ (routeRO F.IV (F.sb seed) cv)
        (udP₂ A seed (st, udPj ((qs, tw), c).1))).run' c =
      (simulateQ (routeRO F.IV (F.sb seed) cv) (A.distinguish st seed)).run c >>= fun z =>
        pure z.1 := by
    rw [StateT.run'_eq, map_eq_bind_pure_comp]
    rfl
  rw [e2]
  refine prT_bind_le_add_const _ _ _ _ fun z hz => ?_
  refine (HP.prT_bind_le_prEvent_add (hideDraw qs) _
    (fun xs => HiddenRead (hidMap (preCell F emb) xs) z.2) (ε := HP.prT (pure z.1))
    fun xs _ hne => ?_).trans ?_
  · simp only [hne, ite_false]
    exact le_rfl
  · rw [add_comm]
    refine add_le_add le_rfl ?_
    have hpot := routeRO_potential_le F.IV (F.sb seed) cv
      (fun c' : Cache St Blk =>
        Pr{let xs ← hideDraw (M' := M') qs}[HiddenRead (hidMap (preCell F emb) xs) c'])
      (Fintype.card M' : ℝ≥0∞)⁻¹
      (fun c' q u => prEvent_mono _ _ _ fun xs h => hiddenRead_cacheQuery_pub h)
      (fun c' B u => (prEvent_mono _ _ _ fun xs h => hiddenRead_cacheQuery_row h).trans
        ((prEvent_or_le _ _ _).trans (add_le_add le_rfl
          (prEvent_hideDraw_cell_le (preCell F emb) btw (fun k x => hbtwT k (emb x)) hcellinj
            qs hI.1 B))))
      (A.distinguish st seed) q₂ (hq₂ st seed) c z hz
    refine hpot.trans (le_of_eq ?_)
    rw [prEvent_eq_zero_of_forall_mem_support _ _ fun xs hxs =>
      not_hiddenRead_of_inv (F := F) emb btw hbtwT hI hxs, zero_add]

end Lemmas

/-- **The two ideal SM-UD games.**  When the attacked member has a single message block after
the seed block, tweaks are recoverable from first blocks (`btw`), the first block is injective
in the message for a fixed tweak, `emb` is injective and the output map sends the uniform
distribution on chaining values to the uniform distribution on `Y` (`hout`), the ideal game of
the real-world programs returns `true` at most `q₂/|M'|` more often than the ideal game of the
ideal-world programs, where `q₂` bounds the compression queries of `A.distinguish`. -/
theorem ud_ideal_le [DecidableEq St] [DecidableEq Blk] [SampleableType St]
    [DecidableEq Tweak] [SampleableType M'] [Fintype M'] [SampleableType Y] [Finite Y]
    (emb : M' → M) (hemb : Function.Injective emb)
    (hsingle : ∀ t m, (F.tch t m).2 = [])
    (btw : Blk → Tweak) (hbtwT : ∀ t m, btw (F.tch t m).1 = t)
    (hbtwC : ∀ i t m, btw (F.cch i t m).1 = t)
    (hinj : ∀ t m m', (F.tch t m).1 = (F.tch t m').1 → m = m')
    (hout : ∀ p : Y → Prop, Pr{let u ← $ᵗ St}[p (F.out u)] = Pr{let y ← $ᵗ Y}[p y])
    (A : UdAdv F) (q₂ : ℕ) (hq₂ : A.DistBound q₂) :
    𝒟[idealGame F.IV F.sb F.seedGen (udProg₁ .real emb A) (udP₂ A)] {true} ≤
      𝒟[idealGame F.IV F.sb F.seedGen (udProg₁ .ideal emb A) (udP₂ A)] {true} +
        q₂ * (Fintype.card M' : ℝ≥0∞)⁻¹ := by
  rw [← HP.prT_eq, ← HP.prT_eq, idealGame_eq_phases, idealGame_eq_phases,
    prT_congr_evalDistEq ((ud_phase1_real emb hsingle btw hbtwT hbtwC A).bind_left _),
    prT_congr_evalDistEq ((ud_phase1_ideal emb hout A).bind_left _)]
  simp only [udPhiI, bind_assoc, pure_bind]
  refine prT_bind_le_add_const _ _ _ _ fun z hz => ?_
  have hI : PreInv btw z.2 :=
    simulateQ_run_preservesInv (preSim F) (PreInv btw) (preInv_step btw hbtwC) A.pick
      (([], []), ∅) ⟨by simp, fun B hB => by simp at hB, by simp⟩ z hz
  rw [HP.prT_swap]
  refine prT_bind_le_add_const _ _ _ _ fun seed _ => ?_
  rw [HP.prT_swap]
  refine prT_bind_le_add_const _ _ _ _ fun cv _ => ?_
  exact prT_ud_phase2_le emb hemb btw hbtwT hinj A q₂ hq₂ z.1 z.2 hI seed cv

end Ideal

#print axioms Ideal.hiddenPrefix_ge
#print axioms Ideal.ud_phase1_real
#print axioms Ideal.ud_phase1_ideal
#print axioms Ideal.prT_ud_phase2_le
#print axioms Ideal.ud_ideal_le
