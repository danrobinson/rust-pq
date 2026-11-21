import Ideal.Games.TcrFVDefs
import Ideal.Games.TcrIdeal

/-!
# Source-final-validity SM-TCR in the ideal-compression model: the ideal (hidden-prefix) game

`tcrFV_ideal_le`: when the attacked member has a single message block after the seed block, the
ideal game of `fvProg₁ A`, `fvP₂ A` is won with probability at most `(q₂ + 1)·δ + 1/|St|`.

The argument is that of `tcr_ideal_le`, with the invariant adapted to the fact that this game
records every target and checks validity only in the winning condition.  `FvInv` relates the
monitor state and the joint cache after phase one:

* if the sticky bit `valid` is still set, target tweaks are pairwise distinct;
* every target cell of the private row table is cached;
* every cached private-row cell is the cell of a recorded target (stand-alone game: phase one
  reads the private row table only through challenge queries).

The last two clauses hold whether or not the state is valid.  If `valid = false` the winning
condition is `false`.  If `valid = true`, the invariant gives `TcrGood` (no cached private-row
cell other than the target cell of its tweak has the target's output) and phase two is bounded
exactly as in `TcrIdeal.lean` (whose lemmas about `TcrGood` are reused verbatim).
-/

open OracleComp OracleSpec ENNReal

namespace Ideal

open TweakableHash

variable {St Blk PkSeed Tweak M Y : Type} {F : THFam St Blk PkSeed Tweak M Y Empty}

section Lemmas

variable [DecidableEq St] [DecidableEq Blk] [SampleableType St]

/-! ## Phase one: the invariant -/

/-- The phase-one invariant. -/
def FvInv (F : THFam St Blk PkSeed Tweak M Y Empty) (btw : Blk → Tweak)
    (s : SM_DT_TCR_SourceFinalValidity.State Tweak M) (c : Cache St Blk) : Prop :=
  (s.valid = true → ∀ t m m', (t, m) ∈ s.challenges → (t, m') ∈ s.challenges → m = m') ∧
  (∀ t m, (t, m) ∈ s.challenges → (c (.inr (F.tch t m).1)).isSome) ∧
  (∀ B, (c (.inr B)).isSome → ∃ m, (btw B, m) ∈ s.challenges ∧ B = (F.tch (btw B) m).1)

omit [DecidableEq St] [DecidableEq Blk] [SampleableType St] in
theorem FvInv.congr_row {btw : Blk → Tweak} {s : SM_DT_TCR_SourceFinalValidity.State Tweak M}
    {c c' : Cache St Blk} (h : FvInv F btw s c) (hc : ∀ B, c' (.inr B) = c (.inr B)) :
    FvInv F btw s c' := by
  obtain ⟨ha, hb, hc'⟩ := h
  exact ⟨ha, fun t m hm => by rw [hc]; exact hb t m hm, fun B hB => hc' B (by rwa [hc] at hB)⟩

theorem run_fvGameM_inl [DecidableEq Tweak] (n : ℕ)
    (s : SM_DT_TCR_SourceFinalValidity.State Tweak M) (c : Cache St Blk) :
    (simulateQ chainRO ((fvGameM F (.inl n)).run s)).run c =
      (fun p => ((p.1, s), p.2)) <$> ((chainRO (St := St) (Blk := Blk)) (.inl n)).run c := by
  simp [fvGameM]

theorem run_fvGameM_pub [DecidableEq Tweak] (q : St × Blk)
    (s : SM_DT_TCR_SourceFinalValidity.State Tweak M) (c : Cache St Blk) :
    (simulateQ chainRO ((fvGameM F (.inr (.inl q))).run s)).run c =
      (fun p => ((p.1, s), p.2)) <$>
        ((chainRO (St := St) (Blk := Blk)) (.inr (.inl q))).run c := by
  simp [fvGameM]

theorem run_fvGameM_chal [DecidableEq Tweak] (tm : Tweak × M)
    (s : SM_DT_TCR_SourceFinalValidity.State Tweak M) (c : Cache St Blk) :
    (simulateQ chainRO ((fvGameM F (.inr (.inr (.inl tm)))).run s)).run c =
      (fun p => ((F.out p.1, s.recordTarget F.numTargets Prod.fst tm), p.2)) <$>
        ((chainRO (St := St) (Blk := Blk)) (.inr (.inr (F.tch tm.1 tm.2)))).run c := by
  simp [fvGameM]

/-- Every step of the game oracles preserves the invariant. -/
theorem fvInv_step [DecidableEq Tweak] (btw : Blk → Tweak)
    (hbtwT : ∀ t m, btw (F.tch t m).1 = t)
    (t : F.fvAdvS.Domain) (s : SM_DT_TCR_SourceFinalValidity.State Tweak M) (c : Cache St Blk)
    (h : FvInv F btw s c) :
    ∀ z ∈ support ((simulateQ chainRO ((fvGameM F t).run s)).run c),
      FvInv F btw z.1.2 z.2 := by
  intro z hz
  rcases t with n | q | tm | q
  · rw [run_fvGameM_inl, chainRO_run_inl, support_map] at hz
    obtain ⟨p, hp, rfl⟩ := hz
    rw [support_map] at hp
    obtain ⟨u, -, rfl⟩ := hp
    exact h
  · rw [run_fvGameM_pub, chainRO_run_pub, support_map] at hz
    obtain ⟨p, hp, rfl⟩ := hz
    exact h.congr_row (row_eq_of_mem_support_randomOracle_pub q c hp)
  · rw [run_fvGameM_chal, support_map] at hz
    obtain ⟨p, hp, rfl⟩ := hz
    obtain ⟨hsome, hrest⟩ := row_of_mem_support_chainRO_chain _ c hp
    obtain ⟨ha, hb, hc⟩ := h
    obtain ⟨qs, tw, v⟩ := s
    obtain ⟨t₀, m₀⟩ := tm
    refine ⟨?_, ?_, ?_⟩
    · intro hv t m m' hm hm'
      simp only [SourceFinalValidity.State.recordTarget, Bool.and_eq_true,
        decide_eq_true_eq] at hv
      obtain ⟨⟨hv, -⟩, hfresh⟩ := hv
      have hres' : ∀ m, (t₀, m) ∉ qs := fun m hm => hfresh.1 ⟨(t₀, m), hm, rfl⟩
      simp only [SourceFinalValidity.State.recordTarget, List.mem_append, List.mem_singleton,
        Prod.mk.injEq] at hm hm'
      rcases hm with hm | ⟨rfl, rfl⟩ <;> rcases hm' with hm' | ⟨ht, rfl⟩
      · exact ha hv t m m' hm hm'
      · exact absurd (ht ▸ hm) (hres' m)
      · exact absurd hm' (hres' m')
      · rfl
    · intro t m hm
      simp only [SourceFinalValidity.State.recordTarget, List.mem_append, List.mem_singleton,
        Prod.mk.injEq] at hm
      rcases hm with hm | ⟨rfl, rfl⟩
      · by_cases hB : (F.tch t m).1 = (F.tch t₀ m₀).1
        · rw [hB]; exact hsome
        · rw [hrest _ hB]; exact hb t m hm
      · exact hsome
    · intro B hB
      by_cases hBB : B = (F.tch t₀ m₀).1
      · refine ⟨m₀, ?_, ?_⟩
        · rw [hBB, hbtwT]; simp [SourceFinalValidity.State.recordTarget]
        · rw [hBB, hbtwT]
      · rw [hrest B hBB] at hB
        obtain ⟨m, hm, hBm⟩ := hc B hB
        exact ⟨m, List.mem_append_left _ hm, hBm⟩
  · exact q.1.elim

/-- The invariant holds after phase one. -/
theorem fvInv_phase1 [DecidableEq Tweak] (btw : Blk → Tweak)
    (hbtwT : ∀ t m, btw (F.tch t m).1 = t) (A : FvAdv F) :
    ∀ z ∈ support ((simulateQ (hS St Blk + tS St Blk).romImpl
      (simulateQ chainToT (fvProg₁ A))).run ∅), FvInv F btw z.1.2 z.2 :=
  chainRO_inv_of_step (fvGameM F) (FvInv F btw) (fvInv_step btw hbtwT) A.choose
    .initial ∅ ⟨by simp [SourceFinalValidity.State.initial],
      by simp [SourceFinalValidity.State.initial], fun B hB => by simp at hB⟩

/-! ## Phase two -/

omit [DecidableEq St] [DecidableEq Blk] [SampleableType St] in
/-- On a valid state the invariant gives the good predicate of `TcrIdeal.lean`. -/
theorem FvInv.good {btw : Blk → Tweak} {s : SM_DT_TCR_SourceFinalValidity.State Tweak M}
    {c : Cache St Blk} (h : FvInv F btw s c) (hv : s.valid = true) :
    TcrGood F btw s.challenges c := by
  obtain ⟨ha, hb, hc⟩ := h
  intro t m hm
  obtain ⟨v, hv'⟩ := Option.isSome_iff_exists.mp (hb t m hm)
  refine ⟨v, hv', fun B u hB hbt hne => absurd ?_ hne⟩
  obtain ⟨m', hm', hBm⟩ := hc B (by rw [hB]; rfl)
  rw [hbt] at hm' hBm
  rw [hBm, ha hv t m m' hm hm']

/-- Phase two, run from a cache satisfying the phase-one invariant with `cv ≠ IV`, returns
`true` with probability at most `(q₂ + 1) * δ`. -/
theorem prEvent_fv_phase2_le [DecidableEq M] [DecidableEq Y]
    (hsingle : ∀ t m, (F.tch t m).2 = [])
    (btw : Blk → Tweak) (hbtwT : ∀ t m, btw (F.tch t m).1 = t)
    (hinj : ∀ t m m', (F.tch t m).1 = (F.tch t m').1 → m = m')
    (δ : ℝ≥0∞) (hδ : ∀ y, Pr{let u ← $ᵗ St}[F.out u = y] ≤ δ)
    (A : FvAdv F) (q₂ : ℕ) (hq₂ : A.ForgeBound q₂)
    (x : A.State × SM_DT_TCR_SourceFinalValidity.State Tweak M) (c : Cache St Blk)
    (seed : PkSeed) (cv : St) (hInv : FvInv F btw x.2 c) (hcv : cv ≠ F.IV) :
    Pr{let b ← (simulateQ (routeRO F.IV (F.sb seed) cv) (fvP₂ A seed x)).run' c}[b = true] ≤
      (q₂ + 1 : ℕ) * δ := by
  classical
  unfold fvP₂
  rw [simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind]
  by_cases hv : x.2.valid = true
  · have hG := hInv.good hv
    refine (prEvent_bind_le_prEvent_add _ _ (fun z => ¬ TcrGood F btw x.2.challenges z.2) _
      (ε := δ) fun z hz => ?_).trans ?_
    · rw [not_not] at hz
      obtain ⟨⟨j, m⟩, c₂⟩ := z
      rw [← StateT.run'_eq]
      dsimp only
      cases hj : x.2.challenges[j]? with
      | none =>
        simp
      | some tm =>
        obtain ⟨t, mj⟩ := tm
        simp only [hv, ite_true]
        exact prEvent_tcr_final_le hsingle btw hbtwT hinj δ hδ seed cv hcv hz t m mj
          (List.mem_of_getElem? hj)
    · refine (add_le_add_left (prEvent_routeRO_bad_le F.IV (F.sb seed) cv
        (fun c => ¬ TcrGood F btw x.2.challenges c) δ
        (fun c q u hc _ => not_not.mpr ((not_not.mp hc).cacheQuery_pub q u))
        (fun c B hc hB =>
          prEvent_not_tcrGood_cacheQuery_row_le (hInv.1 hv) δ hδ (not_not.mp hc) B hB)
        (A.forge x.1 seed) q₂ (hq₂ x.1 seed) c (not_not.mpr hG)) _).trans (le_of_eq ?_)
      push_cast
      ring
  · refine (prEvent_bind_le_of_forall_le _ _ _ (ε := 0) fun z => ?_).trans zero_le
    obtain ⟨⟨j, m⟩, c₂⟩ := z
    rw [← StateT.run'_eq]
    dsimp only
    cases hj : x.2.challenges[j]? with
    | none => simp
    | some tm =>
      obtain ⟨t, mj⟩ := tm
      simp [hv]

end Lemmas

theorem tcrFV_ideal_le [Fintype St] [DecidableEq St] [DecidableEq Blk] [SampleableType St]
    [DecidableEq Tweak] [DecidableEq M] [DecidableEq Y]
    (hsingle : ∀ t m, (F.tch t m).2 = [])
    (btw : Blk → Tweak) (hbtwT : ∀ t m, btw (F.tch t m).1 = t)
    (hinj : ∀ t m m', (F.tch t m).1 = (F.tch t m').1 → m = m')
    (δ : ℝ≥0∞) (hδ : ∀ y, Pr{let u ← $ᵗ St}[F.out u = y] ≤ δ)
    (A : FvAdv F) (q₂ : ℕ) (hq₂ : A.ForgeBound q₂) :
    𝒟[idealGame F.IV F.sb F.seedGen (fvProg₁ A) (fvP₂ A)] {true} ≤
      (q₂ + 1 : ℕ) * δ + (Fintype.card St : ℝ≥0∞)⁻¹ :=
  idealGame_le_of_inv F.IV F.sb F.seedGen (fvProg₁ A) (fvP₂ A)
    (fun x c => FvInv F btw x.2 c) _ (fvInv_phase1 btw hbtwT A)
    fun x c seed cv hInv hcv =>
      prEvent_fv_phase2_le hsingle btw hbtwT hinj δ hδ A q₂ hq₂ x c seed cv hInv hcv

end Ideal

#print axioms Ideal.tcrFV_ideal_le
