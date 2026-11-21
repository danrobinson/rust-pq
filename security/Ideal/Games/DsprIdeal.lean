import Ideal.Games.DsprDefs
import Ideal.Games.TcrFVIdeal
import Ideal.Core.HiddenInput

/-!
# Source-final-validity SM-DSPR in the ideal-compression model: the ideal (hidden-prefix) game

`dspr_ideal_le`: when the attacked member has a single message block after the seed block, the
ideal game of `dsprProg₁ A` with the DSPR winning condition (`dsprP₂ winS A`) returns `true` at
most as often as with the `SPprob` winning condition (`dsprP₂ winSP A`), up to `1/|St|`,
provided `ρ ^ (|M| - 1 - q₂) ≤ 1/2`, where `ρ ≤ 1` bounds the probability that the output map
misses a fixed value on a uniform chaining value and `q₂` bounds the compression queries of
the guess phase.

Proof.  The two games differ only when the adversary guesses `b = false` for a recorded target
`(t, m)` of a valid run: then DSPR accepts iff the scan `spPub` returns `false` and `SPprob`
iff it returns `true`.  It suffices that the scan returns `false` with probability `≤ 1/2`
from every cache reachable after the guess phase (`prT_dspr_phase2_le`).

* `FvInv` (the phase-one invariant of the SM-TCR game; phase one is the same program) gives:
  on a valid run the target cell is cached and it is the only cached private-row cell of
  tweak `t` (`cachedN ≤ 1`).
* The guess phase caches at most `q₂` further cells (`cachedN_routeRO_le`, from the pathwise
  potential bound `routeRO_potential_le`), and the target cell stays cached.
* From a cache in which the target cell is cached, the scan over a duplicate-free list returns
  `false` with probability at most `ρ ^ n`, `n` the number of uncached messages of the list
  (`prEvent_spScan_false_le`, induction on the list: a cached cell is a deterministic read; an
  uncached one is a fresh uniform value, which must miss the target image, probability `≤ ρ`,
  independently of the rest).  Here `n ≥ |M| - 1 - q₂`.
* `idealGame_le_idealGame_of_inv`: the comparison of phase two lifts to the ideal games; the
  event `cv = IV` costs `1/|St|`.
-/

open OracleComp OracleSpec ENNReal

namespace Ideal

open TweakableHash Ideal.HP

/-! ## Generic probability lemmas -/

section Generic

variable {α β : Type}

/-- Monotonicity of a bind up to the success probability of a fixed experiment, on the support
of the prefix. -/
theorem prT_bind_le_add_of_support (mx : ProbComp α) (f g : α → ProbComp Bool)
    (K : ProbComp Bool) (h : ∀ x ∈ support mx, prT (f x) ≤ prT (g x) + prT K) :
    prT (mx >>= f) ≤ prT (mx >>= g) + prT K := by
  classical
  have e : prT (mx >>= f) =
      prT (mx >>= fun x => if x ∈ support mx then f x else pure false) :=
    prT_bind_congr _ _ _ fun x hx => by simp only [hx, ↓reduceIte]
  rw [e, ← prT_bind_const mx K]
  refine prT_bind_le_add mx _ g (fun _ => K) fun x => ?_
  by_cases hx : x ∈ support mx
  · simp only [hx, ↓reduceIte]; exact h x hx
  · simp only [hx, ↓reduceIte, prT_pure]; simp

theorem countP_add_countP_not (p : α → Bool) (l : List α) :
    l.countP p + l.countP (fun a => !p a) = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases h : p a <;> simp [h] <;> omega

/-- If `p'` implies `p` away from `a₀`, a duplicate-free list has at most one more element
satisfying `p'` than `p`. -/
theorem countP_le_countP_succ [DecidableEq α] (p p' : α → Bool) (a₀ : α) (l : List α)
    (hnd : l.Nodup) (h : ∀ a, a ≠ a₀ → p' a = true → p a = true) :
    l.countP p' ≤ l.countP p + 1 := by
  have key : l.countP p' ≤ l.countP p + l.count a₀ := by
    clear hnd
    induction l with
    | nil => simp
    | cons a l ih =>
      by_cases ha : a = a₀
      · subst ha
        simp only [List.countP_cons, List.count_cons_self]
        split <;> split <;> omega
      · have := h a ha
        simp only [List.countP_cons]
        cases hp' : p' a <;> cases hp : p a <;> simp_all <;> omega
  exact key.trans (Nat.add_le_add_left (List.nodup_iff_count_le_one.mp hnd a₀) _)

end Generic

/-! ## Comparing two ideal games -/

section Compare

variable {St Blk : Type} [DecidableEq St] [DecidableEq Blk] [SampleableType St]

/-- **Comparison of two ideal games with the same phase one.**  If `Inv` holds of the phase-one
output and the cache after phase one, and for every `cv ≠ IV` phase two `P₂` run from such an
output and cache returns `true` at most as often as `P₂'`, then the ideal game with `P₂` returns
`true` at most as often as the ideal game with `P₂'`, up to `1/|St|`. -/
theorem idealGame_le_idealGame_of_inv [Fintype St] {PkSeed σ : Type}
    (IV : St) (sb : PkSeed → Blk) (seedGen : ProbComp PkSeed)
    (prog₁ : OracleComp (unifSpec + (hS St Blk + chainS St Blk)) σ)
    (P₂ P₂' : PkSeed → σ → OracleComp (unifSpec + hS St Blk) Bool)
    (Inv : σ → Cache St Blk → Prop)
    (h1 : ∀ z ∈ support ((simulateQ (hS St Blk + tS St Blk).romImpl
      (simulateQ chainToT prog₁)).run ∅), Inv z.1 z.2)
    (h2 : ∀ x c seed cv, Inv x c → cv ≠ IV →
      prT ((simulateQ (routeRO IV (sb seed) cv) (P₂ seed x)).run' c) ≤
        prT ((simulateQ (routeRO IV (sb seed) cv) (P₂' seed x)).run' c)) :
    𝒟[idealGame IV sb seedGen prog₁ P₂] {true} ≤
      𝒟[idealGame IV sb seedGen prog₁ P₂'] {true} + (Fintype.card St : ℝ≥0∞)⁻¹ := by
  classical
  let K : ProbComp Bool := ($ᵗ St : ProbComp St) >>= fun cv => pure (decide (cv = IV))
  have hK : prT K = (Fintype.card St : ℝ≥0∞)⁻¹ := by
    rw [prT_bind_pure]
    simp only [decide_eq_true_eq]
    exact SampleableType.prEvent_uniformSample_eq_singleton IV
  rw [← prT_eq, ← prT_eq, idealGame_eq_phases, idealGame_eq_phases, ← hK]
  refine prT_bind_le_add_of_support _ _ _ K fun z hz => ?_
  refine prT_bind_le_add_of_support _ _ _ K fun seed _ => ?_
  refine prT_bind_le_add _ _ _ _ fun cv => ?_
  by_cases hcv : cv = IV
  · rw [prT_pure]
    simp only [hcv, decide_true, ↓reduceIte]
    exact (prT_le_one _).trans le_add_self
  · exact (h2 z.1 z.2 seed cv (h1 z hz) hcv).trans le_self_add

end Compare

/-! ## The scan from a cache -/

section Scan

variable {St Blk PkSeed Tweak M Y : Type} {F : THFam St Blk PkSeed Tweak M Y Empty}
  [DecidableEq St] [DecidableEq Blk] [SampleableType St]

/-- **The scan misses with probability `≤ ρ^(#uncached)`.**  Run from a cache in which the
cell of `m` is cached (and `cv ≠ IV`), the scan of a duplicate-free list `l` returns `false`
(no second preimage with image `y` in `l`) with probability at most `ρ ^ n`, `n` the number of
messages of `l` whose cell is not cached: each of them reads a fresh uniform cell, whose
output differs from `y` with probability at most `ρ`. -/
theorem prEvent_spScan_false_le [DecidableEq M] [DecidableEq Y]
    (hsingle : ∀ t m, (F.tch t m).2 = [])
    (hinj : ∀ t m m', (F.tch t m).1 = (F.tch t m').1 → m = m')
    (ρ : ℝ≥0∞) (hρ : ∀ y, Pr{let u ← $ᵗ St}[F.out u ≠ y] ≤ ρ)
    (seed : PkSeed) (cv : St) (hcv : cv ≠ F.IV) (t : Tweak) (m : M) (y : Y)
    (l : List M) (hnd : l.Nodup) (c : Cache St Blk)
    (hm : (c (.inr (F.tch t m).1)).isSome) :
    Pr{let z ← (simulateQ (routeRO F.IV (F.sb seed) cv) (spScan F seed t m y l)).run c}[
        z.1 = false] ≤
      ρ ^ (l.countP fun a => !(c (.inr (F.tch t a).1)).isSome) := by
  induction l generalizing c with
  | nil => simp [spScan]
  | cons a l ih =>
    obtain ⟨hal, hnd'⟩ := List.nodup_cons.mp hnd
    simp only [spScan, simulateQ_bind, StateT.run_bind, run_evalPub hsingle seed cv hcv,
      simulateQ_pure, StateT.run_pure]
    rcases randomOracle_run_row_cases (F.tch t a).1 c with ⟨v, hv, h⟩ | ⟨hnone, h⟩
    · rw [h]
      simp only [map_pure, pure_bind, bind_pure_comp]
      rw [prEvent_map]
      have hcount : ((a :: l).countP fun a => !(c (.inr (F.tch t a).1)).isSome) =
          l.countP fun a => !(c (.inr (F.tch t a).1)).isSome := by
        rw [List.countP_cons_of_neg]
        simp [hv]
      rw [hcount]
      refine (prEvent_mono _ _ (fun z => z.1 = false) fun z hz => ?_).trans (ih hnd' c hm)
      simp only [Bool.or_eq_false_iff] at hz
      exact hz.2
    · rw [h]
      simp only [Functor.map_map, bind_map_left, bind_pure_comp]
      have hma : m ≠ a := fun e => by
        rw [e, hnone] at hm
        exact absurd hm (by simp)
      have hcount : ((a :: l).countP fun a => !(c (.inr (F.tch t a).1)).isSome) =
          (l.countP fun a => !(c (.inr (F.tch t a).1)).isSome) + 1 := by
        rw [List.countP_cons_of_pos]
        simp [hnone]
      have hcell : ∀ (u : St) (a' : M), a' ≠ a →
          (c.cacheQuery (.inr (F.tch t a).1) u) (.inr (F.tch t a').1) =
            c (.inr (F.tch t a').1) := fun u a' ha' =>
        QueryCache.cacheQuery_of_ne (t := .inr (F.tch t a).1) c u
          (by simpa using fun e => ha' (hinj t a' a e))
      have hcount' : ∀ u : St,
          (l.countP fun a' =>
            !((c.cacheQuery (.inr (F.tch t a).1) u) (.inr (F.tch t a').1)).isSome) =
          l.countP fun a' => !(c (.inr (F.tch t a').1)).isSome := fun u =>
        List.countP_congr fun a' ha' => by
          rw [hcell u a' fun e => hal (e ▸ ha')]
      rw [hcount, pow_succ]
      refine (prEvent_bind_le_prEvent_mul_of_forall_le _ _ (fun u => F.out u ≠ y) _
        (ε := ρ ^ (l.countP fun a' => !(c (.inr (F.tch t a').1)).isSome))
        (fun u _ => ?_) (fun u hu => ?_)).trans ?_
      · rw [prEvent_map]
        refine (prEvent_mono _ _ (fun z => z.1 = false) fun z hz => ?_).trans
          ((ih hnd' _ ?_).trans (le_of_eq (by rw [hcount' u])))
        · simp only [Bool.or_eq_false_iff] at hz
          exact hz.2
        · rw [hcell u m hma]
          exact hm
      · rw [prEvent_map]
        refine prEvent_eq_zero_of_forall_not _ _ fun z => ?_
        rw [not_not] at hu
        simp [hma, hu]
      · rw [mul_comm]
        gcongr
        exact hρ y

end Scan

/-! ## Phase two -/

section Phase2

variable {St Blk PkSeed Tweak M Y : Type} {F : THFam St Blk PkSeed Tweak M Y Empty}
  [DecidableEq St] [DecidableEq Blk] [SampleableType St] [Fintype M]

/-- The number of messages whose private-row cell under the tweak `t` is cached. -/
noncomputable def cachedN (F : THFam St Blk PkSeed Tweak M Y Empty) (t : Tweak)
    (c : Cache St Blk) : ℕ :=
  (Finset.univ : Finset M).toList.countP fun a => (c (.inr (F.tch t a).1)).isSome

/-- A phase-two computation making at most `q₂` compression queries caches at most `q₂` further
cells of tweak `t`, on every run. -/
theorem cachedN_routeRO_le [DecidableEq M]
    (hinj : ∀ t m m', (F.tch t m).1 = (F.tch t m').1 → m = m')
    (seed : PkSeed) (cv : St) (t : Tweak) {α : Type}
    (oa : OracleComp (unifSpec + hS St Blk) α) (q₂ : ℕ)
    (hq : IsQueryBoundP oa (fun i => i.isRight = true) q₂) (c : Cache St Blk) :
    ∀ z ∈ support ((simulateQ (routeRO F.IV (F.sb seed) cv) oa).run c),
      cachedN F t z.2 ≤ cachedN F t c + q₂ := by
  intro z hz
  have h := routeRO_potential_le F.IV (F.sb seed) cv (fun c => (cachedN F t c : ℝ≥0∞)) 1
    ?_ ?_ oa q₂ hq c z hz
  · rw [mul_one] at h
    exact_mod_cast h
  · intro c q u
    refine le_of_eq (congrArg _ ?_)
    exact List.countP_congr fun a _ => by
      rw [QueryCache.cacheQuery_of_ne (t := .inl q) c u (by simp)]
  · intro c B u
    have : cachedN F t (c.cacheQuery (.inr B) u) ≤ cachedN F t c + 1 := by
      by_cases hex : ∃ a₀, (F.tch t a₀).1 = B
      · obtain ⟨a₀, rfl⟩ := hex
        exact countP_le_countP_succ _ _ a₀ _ (Finset.nodup_toList _) fun a ha h' => by
          rwa [QueryCache.cacheQuery_of_ne (t := .inr (F.tch t a₀).1) c u
            (by simpa using fun e => ha (hinj t a a₀ e))] at h'
      · refine le_trans (le_of_eq ?_) (Nat.le_succ _)
        exact List.countP_congr fun a _ => by
          rw [QueryCache.cacheQuery_of_ne (t := .inr B) c u
            (by simpa using fun e => hex ⟨a, e⟩)]
    exact_mod_cast this

/-- **Phase two: predicting "no second preimage" is no better than the baseline.**  From an
output and cache of phase one satisfying the invariant, with `cv ≠ IV`, the DSPR winning
condition holds at most as often as the `SPprob` winning condition, provided
`ρ ^ (|M| - 1 - q₂) ≤ 1/2`. -/
theorem prT_dspr_phase2_le [DecidableEq M] [DecidableEq Y]
    (hsingle : ∀ t m, (F.tch t m).2 = [])
    (btw : Blk → Tweak) (hbtwT : ∀ t m, btw (F.tch t m).1 = t)
    (hinj : ∀ t m m', (F.tch t m).1 = (F.tch t m').1 → m = m')
    (ρ : ℝ≥0∞) (hρ : ∀ y, Pr{let u ← $ᵗ St}[F.out u ≠ y] ≤ ρ) (hρ1 : ρ ≤ 1)
    (A : DsprAdv F) (q₂ : ℕ) (hq₂ : A.GuessBound q₂)
    (hhalf : ρ ^ (Fintype.card M - 1 - q₂) ≤ 2⁻¹)
    (x : A.State × SM_DT_DSPR_SourceFinalValidity.State Tweak M) (c : Cache St Blk)
    (seed : PkSeed) (cv : St) (hInv : FvInv F btw x.2 c) (hcv : cv ≠ F.IV) :
    prT ((simulateQ (routeRO F.IV (F.sb seed) cv) (dsprP₂ winS A seed x)).run' c) ≤
      prT ((simulateQ (routeRO F.IV (F.sb seed) cv) (dsprP₂ winSP A seed x)).run' c) := by
  classical
  unfold dsprP₂
  simp only [simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind]
  refine prT_bind_mono _ _ _ fun z hz => ?_
  obtain ⟨⟨j, b⟩, c₂⟩ := z
  dsimp only
  cases hj : x.2.challenges[j]? with
  | none => exact le_rfl
  | some tm =>
    obtain ⟨t, m⟩ := tm
    dsimp only
    by_cases hv : x.2.valid = true
    swap
    · simp only [hv]
      exact le_rfl
    simp only [hv, ite_true, bind_pure_comp]
    cases b
    swap
    · refine le_of_eq ?_
      simp [winS, winSP]
    have hmem : (t, m) ∈ x.2.challenges := List.mem_of_getElem? hj
    -- the target cell is cached, before and after the guess phase
    have hm₂ : (c₂ (.inr (F.tch t m).1)).isSome := by
      rw [← simulateQ_romImpl_route] at hz
      exact isSome_of_mem_support_run_romImpl _ (.inr (F.tch t m).1) c (hInv.2.1 t m hmem) _ hz
    -- at most `1 + q₂` cells of tweak `t` are cached
    have hc1 : cachedN F t c ≤ 1 := by
      have := countP_le_countP_succ (fun _ : M => false)
        (fun a => (c (.inr (F.tch t a).1)).isSome) m (Finset.univ : Finset M).toList
        (Finset.nodup_toList _) fun a ha h' => by
          obtain ⟨m'', hm'', hB⟩ := hInv.2.2 _ h'
          rw [hbtwT] at hm'' hB
          obtain rfl := hInv.1 hv t m m'' hmem hm''
          exact absurd (hinj t a m hB) ha
      simpa [cachedN] using this
    have hc2 : cachedN F t c₂ ≤ 1 + q₂ :=
      (cachedN_routeRO_le hinj seed cv t _ q₂ (hq₂ x.1 seed) c _ hz).trans
        (Nat.add_le_add_right hc1 _)
    have hlen := countP_add_countP_not (fun a => (c₂ (.inr (F.tch t a).1)).isSome)
      (Finset.univ : Finset M).toList
    rw [Finset.length_toList, Finset.card_univ] at hlen
    have hexp : Fintype.card M - 1 - q₂ ≤
        (Finset.univ : Finset M).toList.countP fun a => !(c₂ (.inr (F.tch t a).1)).isSome := by
      unfold cachedN at hc2
      omega
    -- the scan misses with probability at most 1/2
    have key : Pr{let z ← (simulateQ (routeRO F.IV (F.sb seed) cv) (spPub F seed t m)).run c₂}[
        z.1 = false] ≤ 2⁻¹ := by
      simp only [spPub, simulateQ_bind, StateT.run_bind, run_evalPub hsingle seed cv hcv]
      rcases randomOracle_run_row_cases (F.tch t m).1 c₂ with ⟨v, hv', h⟩ | ⟨hnone, -⟩
      · rw [h]
        simp only [map_pure, pure_bind]
        exact (prEvent_spScan_false_le hsingle hinj ρ hρ seed cv hcv t m _ _
          (Finset.nodup_toList _) c₂ hm₂).trans
          ((pow_le_pow_right_of_le_one' hρ1 hexp).trans hhalf)
      · rw [hnone] at hm₂
        exact absurd hm₂ (by simp)
    unfold prT
    simp only [simulateQ_map, StateT.run_map, Functor.map_map]
    have e1 : Pr{let z ← (simulateQ (routeRO F.IV (F.sb seed) cv) (spPub F seed t m)).run c₂}[
        winS z.1 false = true] =
        Pr{let z ← (simulateQ (routeRO F.IV (F.sb seed) cv) (spPub F seed t m)).run c₂}[
          z.1 = false] := by
      congr 2
      funext z
      obtain ⟨b, c'⟩ := z
      cases b <;> simp [winS]
    have e2 : Pr{let z ← (simulateQ (routeRO F.IV (F.sb seed) cv) (spPub F seed t m)).run c₂}[
        winSP z.1 false = true] =
        1 - Pr{let z ← (simulateQ (routeRO F.IV (F.sb seed) cv) (spPub F seed t m)).run c₂}[
          z.1 = false] := by
      rw [← prEvent_not_eq_one_sub]
      congr 2
      funext z
      obtain ⟨b, c'⟩ := z
      cases b <;> simp [winSP]
    rw [e1, e2]
    refine key.trans ((le_of_eq ?_).trans (tsub_le_tsub_left key 1))
    exact (ENNReal.one_sub_inv_two).symm

end Phase2

/-- **The ideal-game inequality.**  When the attacked member has a single message block after
the seed block (injective in the message and determining the tweak), `ρ ≤ 1` bounds the
probability that the output map misses a fixed value on a uniform chaining value, and
`ρ ^ (|M| - 1 - q₂) ≤ 1/2` (`q₂` the number of compression queries of the guess phase), the
ideal DSPR game is won at most as often as the ideal `SPprob` game, up to `1/|St|`. -/
theorem dspr_ideal_le {St Blk PkSeed Tweak M Y : Type} {F : THFam St Blk PkSeed Tweak M Y Empty}
    [Fintype St] [DecidableEq St] [DecidableEq Blk] [SampleableType St]
    [Fintype M] [DecidableEq Tweak] [DecidableEq M] [DecidableEq Y]
    (hsingle : ∀ t m, (F.tch t m).2 = [])
    (btw : Blk → Tweak) (hbtwT : ∀ t m, btw (F.tch t m).1 = t)
    (hinj : ∀ t m m', (F.tch t m).1 = (F.tch t m').1 → m = m')
    (ρ : ℝ≥0∞) (hρ : ∀ y, Pr{let u ← $ᵗ St}[F.out u ≠ y] ≤ ρ) (hρ1 : ρ ≤ 1)
    (A : DsprAdv F) (q₂ : ℕ) (hq₂ : A.GuessBound q₂)
    (hhalf : ρ ^ (Fintype.card M - 1 - q₂) ≤ 2⁻¹) :
    𝒟[idealGame F.IV F.sb F.seedGen (dsprProg₁ A) (dsprP₂ winS A)] {true} ≤
      𝒟[idealGame F.IV F.sb F.seedGen (dsprProg₁ A) (dsprP₂ winSP A)] {true} +
        (Fintype.card St : ℝ≥0∞)⁻¹ :=
  idealGame_le_idealGame_of_inv F.IV F.sb F.seedGen (dsprProg₁ A) (dsprP₂ winS A)
    (dsprP₂ winSP A) (fun x c => FvInv F btw x.2 c)
    (chainRO_inv_of_step (fvGameM F) (FvInv F btw) (fvInv_step btw hbtwT) A.choose
      .initial ∅ ⟨by simp [SourceFinalValidity.State.initial],
        by simp [SourceFinalValidity.State.initial], fun B hB => by simp at hB⟩)
    fun x c seed cv hInv hcv =>
      prT_dspr_phase2_le hsingle btw hbtwT hinj ρ hρ hρ1 A q₂ hq₂ hhalf x c seed cv hInv hcv

end Ideal

#print axioms Ideal.idealGame_le_idealGame_of_inv
#print axioms Ideal.prEvent_spScan_false_le
#print axioms Ideal.dspr_ideal_le
