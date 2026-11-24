import Integration.SlhDsaCompressionPosterior
import Integration.SlhDsaCompressionShortAverage

/-! Bound the honest choosing phase for a multi-block target class. The posterior
identity lets the measured quantum continuation access exactly the same completed
tables as the signer after conditioning on the honest transcript. -/
namespace Reduction.Compression.LongPhase
open MLink Ideal Ideal.HP OracleComp OracleSpec ENNReal TweakableHash SLHDSA PQ.Interactive PQ.QROM Quantum
open HiddenWeight
open scoped Classical ComplexOrder
set_option maxRecDepth 12000
set_option maxHeartbeats 700000
local notation "Joint" => hS St Blk + tS St Blk
abbrev Pub := CF St Blk
abbrev Row := Blk → St
abbrev StateCache := Cache St Blk
def pub (c : StateCache) (U : Pub) (x : St × Blk) := (look c (.inl x)).getD (U x)
def row (c : StateCache) (V : Row) (x : Blk) := (look c (.inr x)).getD (V x)

section Generic
variable {State Block : Type} [Fintype State] [Fintype Block] [DecidableEq State] [DecidableEq Block]
  [SampleableType State] [SampleableType (CF State Block)]

private noncomputable local instance jointDraw : SampleableType (Posterior.Answers (hS State Block + tS State Block)) := SampleableType.ofEquiv tblEquiv
private theorem split_equiv {X Y J : Type} [SampleableType X] [SampleableType Y] (e : X × Y ≃ J)
    (w : J → ℝ≥0∞) :
    mean (@SampleableType.selectElem J (SampleableType.ofEquiv e)) w =
      mean ($ᵗ X) (fun x => mean ($ᵗ Y) fun y => w (e (x,y))) := by
  change mean (e <$> ((·,·) <$> ($ᵗ X : ProbComp X) <*> ($ᵗ Y))) w = _
  simp only [seq_eq_bind_map,map_eq_bind_pure_comp,bind_assoc,pure_bind,Function.comp_def,mean_bind,mean_pure]

omit [Fintype State] [DecidableEq State] [DecidableEq Block] in
private theorem split_tables (w : Posterior.Answers (hS State Block + tS State Block) → ℝ≥0∞) :
    mean (@SampleableType.selectElem _ jointDraw) w =
    mean ($ᵗ (CF State Block)) (fun g => mean ($ᵗ (Block → State)) fun T => w (tbl g T)) := by
  kexact split_equiv (X := (CF State Block)) (Y := (Block → State)) tblEquiv w

theorem phaseMeanGeneric {α : Type} (P : OracleComp (unifSpec + (hS State Block + chainS State Block)) α)
    (w : (CF State Block) → (Block → State) → α → ℝ≥0∞) :
    mean ($ᵗ (CF State Block)) (fun g => mean ($ᵗ (Block → State)) fun T => mean (simulateQ (ans₁ g (chainI g T)) P) (w g T)) =
    mean ((simulateQ (hS State Block + tS State Block).romImpl (simulateQ chainToT P)).run ∅)
      (fun z => mean ($ᵗ (CF State Block)) fun U => mean ($ᵗ (Block → State)) fun V => w (fun x => (look z.2 (.inl x)).getD (U x)) (fun y => (look z.2 (.inr y)).getD (V y)) z.1) := by
  let wt := fun f : Posterior.Answers (hS State Block + tS State Block) => w (fun x => f (.inl x)) (fun x => f (.inr x))
  have h := @Posterior.posterior _ (hS State Block + tS State Block) _ _ _ jointDraw _ (simulateQ chainToT P) wt ∅
  simp only [completeTable_empty] at h
  apply Eq.trans _ (h.trans _)
  · apply Eq.trans _ (split_tables (fun f => mean (simulateQ (ansImpl f) (simulateQ chainToT P)) (wt f))).symm
    exact congrArg (mean ($ᵗ (CF State Block))) (funext fun g => congrArg (mean ($ᵗ (Block → State))) (funext fun T => by
      rw [simulateQ_chainToT]
      rfl))
  · apply congrArg (mean _)
    funext z
    exact (split_tables (fun f => wt (completeTable z.2 f) z.1)).trans rfl

end Generic

private theorem mean_cut {α : Type} (p : ProbComp α) (f : α → ℝ≥0∞) (B : α → Prop) [DecidablePred B]
    (e : ℝ≥0∞) (h1 : ∀ x, f x ≤ 1) (h : ∀ x, ¬ B x → f x ≤ e) :
    mean p f ≤ Pr{let x ← p}[B x] + e := by
  have eq := flag p (fun x => decide (B x))
  have le := mean_mono (f := f) (g := fun x => (if B x then (1:ℝ≥0∞) else 0) + e) p (fun x => by
    by_cases hx : B x
    · exact (h1 x).trans (by simp [hx])
    · simpa [hx] using h x hx)
  rw [mean_add] at le
  apply le.trans (add_le_add _ (Wots256.mean_cap _ _ _ (fun _ => le_rfl)))
  simpa only [prT,bind_pure_comp,prEvent_map,Function.comp_def,decide_eq_true_eq] using eq.symm.le


open Wots256 (Node mean_cap)
open ShortBlocks (family tcrScore Msg)
def tails (ar : ℕ) := (22 + 16*ar + 8)/64
def walks (C : ℕ) := (C+C)*(1+9)
def cacheSize (ar C : ℕ) := walks C + C*(tails ar + 1)
noncomputable def firstLoss (ar C : ℕ) : ℝ≥0∞ :=
  ((walks C * (walks C+1) + C*tails ar*(C*tails ar+2*walks C+1) : ℕ) : ℝ≥0∞) / 2^256
noncomputable def avoidLoss (ar C : ℕ) : ℝ≥0∞ := (cacheSize ar C + 1 : ℕ) / (2:ℝ≥0∞)^256
variable {E : Type} [Fintype E] [DecidableEq E]
local notation "W" => WS Input Output E

theorem phase (seeds : ProbComp Node) (ar n C : ℕ) (A : TcrAdv (family seeds ar n))
    (h0 : A.ChooseBound 0) (hch : A.ChalBound C) (hc : A.CollBound C) (hL : A.CollLen 9)
    (seed : Node) (b : CF Chain512 Block512) (M : (Input → Output) → A.State → Node → Closed W (ℕ × Msg ar))
    (ρ : Matrix W W ℂ) (hp : ρ.PosSemidef) (ht : ρ.trace = 1) (bound : ℝ≥0∞)
    (post : ∀ (x : A.State × SM_DT_TCR_State (Bytes 22) (Msg ar)) c cv, cv ≠ IV128 → CFin (look c) (cacheSize ar C) →
      MInv (family seeds ar n) btw128 (tails ar) x.2.1 (look c) →
      MP2.Good (family seeds ar n) btw128 (tails ar) x.2.1 cv (look c) →
      mean ($ᵗ Pub) (fun U => mean ($ᵗ Row) fun V =>
        tcrScore seed (gstar IV128 (sb128 seed) cv (pub c U) (row c V),b) M ρ x) ≤ bound) :
    mean ($ᵗ St) (fun cv => mean ($ᵗ Pub) fun g => mean ($ᵗ Row) fun T =>
      mean (simulateQ (ans₁ g (chainI g T)) (tcrProg₁ A))
        (tcrScore seed (gstar IV128 (sb128 seed) cv g T,b) M ρ)) ≤
      firstLoss ar C + (avoidLoss ar C + bound) := by
  classical
  let F := family seeds ar n
  let P := tcrProg₁ A
  let phase₁ := (simulateQ (hS St Blk + tS St Blk).romImpl (simulateQ chainToT P)).run ∅
  let w := fun cv (z : (A.State × SM_DT_TCR_State (Bytes 22) (Msg ar)) × StateCache) =>
    mean ($ᵗ Pub) (fun U => mean ($ᵗ Row) fun V =>
      tcrScore seed (gstar IV128 (sb128 seed) cv (pub z.2 U) (row z.2 V),b) M ρ z.1)
  have cap (cv z) : w cv z ≤ 1 := mean_cap _ _ _ (fun U => mean_cap _ _ _ (fun V => qWeight_le_one _ _ hp ht))
  have reorder : (mean ($ᵗ St) fun cv => mean ($ᵗ Pub) fun g => mean ($ᵗ Row) fun T =>
      mean (simulateQ (ans₁ g (chainI g T)) P) (tcrScore seed (gstar IV128 (sb128 seed) cv g T,b) M ρ)) =
      mean phase₁ (fun z => mean ($ᵗ St) fun cv => w cv z) := by
    apply Eq.trans _ (mean_switch ($ᵗ St) phase₁ w)
    exact congrArg (mean ($ᵗ St)) (funext fun cv => phaseMeanGeneric P (fun g T => tcrScore seed (gstar IV128 (sb128 seed) cv g T,b) M ρ))
  rw [reorder]
  have hlen (t m) : (F.tch t m).2.length = tails ar := by
    change (tblocks t m.val).2.length = _
    rw [tblocks_snd_length,m.property]; rfl
  have bt (t m) : btw128 (F.tch t m).1 = t := btw128_tblocks t m.val
  have bc (i t m) : btw128 (F.cch i t m).1 = t := btw128_tblocks t m
  have inv := tcr_multi_phase1_le (tails ar) hlen btw128 bt bc (dominated_symE F _ hlen btw128 bt bc) A 0 C C 9 h0 hch hc hL
  let ok := fun z : (A.State × SM_DT_TCR_State (Bytes 22) (Msg ar)) × StateCache =>
    MInv F btw128 (tails ar) z.1.2.1 (look z.2) ∧ CFin (look z.2) (cacheSize ar C)
  apply (mean_cut phase₁ _ (fun z => ¬ok z) _ (fun z => mean_cap _ _ _ (fun cv => cap cv z)) _).trans
  · apply add_le_add _ le_rfl
    simpa only [phase₁,P,ok,firstLoss,cacheSize,walks,Nat.zero_add,div_eq_mul_inv,card_St,Nat.cast_pow,Nat.cast_ofNat] using inv
  · intro z hok
    obtain ⟨hm,hf⟩ := not_not.mp hok
    obtain ⟨l,hl,hmem⟩ := hf
    apply (mean_cut ($ᵗ St) _ (fun cv => cv ∈ IV128 :: l.filterMap (look z.2)) _ (fun cv => cap cv z) _).trans
    · apply add_le_add _ le_rfl
      refine (MP2.prEvent_uniform_mem_le _).trans ?_
      unfold avoidLoss
      rw [card_St,div_eq_mul_inv,Nat.cast_pow,Nat.cast_ofNat]
      gcongr
      simp
      exact (List.length_filterMap_le _ _).trans hl
    · intro cv notin
      simp only [List.mem_cons,List.mem_filterMap,not_or,not_exists,not_and] at notin
      exact post z.1 z.2 cv notin.1 ⟨l,hl,hmem⟩ hm
        (MP2.Good.of_mInv hm fun y hy => notin.2 y (hmem y (by rw [hy]; rfl)) hy)


theorem class_bound (seeds : ProbComp Node) (ar n C : ℕ) (A : TcrAdv (family seeds ar n))
    (h0 : A.ChooseBound 0) (hch : A.ChalBound C) (hc : A.CollBound C) (hL : A.CollLen 9)
    (M : (Input → Output) → A.State → Node → Closed W (ℕ × Msg ar))
    (ρ : Matrix W W ℂ) (hp : ρ.PosSemidef) (ht : ρ.trace = 1) (bound : ℝ≥0∞)
    (post : ∀ seed b (x : A.State × SM_DT_TCR_State (Bytes 22) (Msg ar)) c cv, cv ≠ IV128 → CFin (look c) (cacheSize ar C) →
      MInv (family seeds ar n) btw128 (tails ar) x.2.1 (look c) →
      MP2.Good (family seeds ar n) btw128 (tails ar) x.2.1 cv (look c) →
      mean ($ᵗ Pub) (fun U => mean ($ᵗ Row) fun V =>
        tcrScore seed (gstar IV128 (sb128 seed) cv (pub c U) (row c V),b) M ρ x) ≤ bound) (b : CF Chain512 Block512) :
    mean seeds (fun seed => mean ($ᵗ Pub) fun g => mean
      (simulateQ (ans₁ g (keyedChain IV128 sb128 g seed)) (tcrProg₁ A)) (tcrScore seed (g,b) M ρ)) ≤
      firstLoss ar C + (avoidLoss ar C + bound) + Wots256.phaseLoss (C+C) (max (tails ar) 9) := by
  have hlen (t m) : ((family seeds ar n).tch t m).2.length = tails ar := by
    change (tblocks t m.val).2.length = _
    rw [tblocks_snd_length,m.property]; rfl
  have hop := HiddenWeight.hiddenPrefix IV128 sb128 (tcrProg₁ A) seeds sb128_injective 1
    (fun _ => prEvent_le_one _) 0 (C+C) (max (tails ar) 9) (tcrProg₁_pubBound A h0) (tcrProg₁_chainBound A hch hc)
    (tcrProg₁_chainLen A (fun t m => by rw [hlen]; exact le_max_left _ _) (hL.mono (le_max_right _ _)))
    (fun seed g => tcrScore seed (g,b) M ρ) (fun _ _ _ => qWeight_le_one _ _ hp ht)
  apply hop.trans (add_le_add _ _)
  · exact mean_cap _ _ _ (fun seed => phase seeds ar n C A h0 hch hc hL seed b M ρ hp ht bound (post seed b))
  · simp only [Nat.cast_zero,zero_mul,zero_add,Wots256.phaseLoss,div_eq_mul_inv]
    rw [card_St]
    norm_num

theorem class_average {σ : Type} (seeds : ProbComp Node) (ar n : ℕ)
    (choose : OracleComp (TcrSpec (ShortBlocks.tcrP seeds ar n (fun _ => IV128))) σ)
    (M : (Input → Output) → σ → Node → Closed W (ℕ × Msg ar)) (ρ : Matrix W W ℂ)
    (hp : ρ.PosSemidef) (ht : ρ.trace = 1) (C : ℕ)
    (h0 : (ShortBlocks.classFirst seeds ar n choose).ChooseBound 0)
    (hch : (ShortBlocks.classFirst seeds ar n choose).ChalBound C)
    (hc : (ShortBlocks.classFirst seeds ar n choose).CollBound C)
    (hL : (ShortBlocks.classFirst seeds ar n choose).CollLen 9) (bound : ℝ≥0∞)
    (post : ∀ seed b (x : σ × SM_DT_TCR_State (Bytes 22) (Msg ar)) c cv, cv ≠ IV128 → CFin (look c) (cacheSize ar C) →
      MInv (family seeds ar n) btw128 (tails ar) x.2.1 (look c) →
      MP2.Good (family seeds ar n) btw128 (tails ar) x.2.1 cv (look c) →
      mean ($ᵗ Pub) (fun U => mean ($ᵗ Row) fun V =>
        tcrScore seed (gstar IV128 (sb128 seed) cv (pub c U) (row c V),b) M ρ x) ≤ bound) :
    SetOracle.uniformMean (fun t => mean seeds (ShortBlocks.tcrValue seeds n choose M ρ t)) ≤
      firstLoss ar C + (avoidLoss ar C + bound) + Wots256.phaseLoss (C+C) (max (tails ar) 9) := by
  rw [Wots256.productMean]
  apply mean_cap
  intro b
  have h := class_bound seeds ar n C (ShortBlocks.classFirst seeds ar n choose) h0 hch hc hL M ρ hp ht bound post b
  simpa only [ShortBlocks.tcr_measure] using h

end Reduction.Compression.LongPhase
#print axioms Reduction.Compression.LongPhase.phaseMeanGeneric
#print axioms Reduction.Compression.LongPhase.phase
#print axioms Reduction.Compression.LongPhase.class_average
