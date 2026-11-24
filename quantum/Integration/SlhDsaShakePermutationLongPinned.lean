import Integration.SlhDsaShakePermutationItsrRecorded

/-! Conditional quantum search after revealing a classical transcript of private cells.
The unrevealed table remains uniform. Pins cost no readout amplitude. -/
namespace Reduction.ShakePermutation.Long.Pinned
open Classical Quantum OracleSpec OracleComp PQ.Interactive ENNReal SetOracle ItsrLabel
open Compression.Recording.Database (Growth occupied readout_failure tensor sumWeight)
open scoped ComplexOrder
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 1400000

def overlay {X Y : Type} (pins D : Database X Y) : Database X Y := fun x => (pins x).or (D x)
def response (pins : Bank) (x : Addr) (v : Words) := (pins x).getD v
def complete (pins : Bank) (H : Table) (x : Addr) := response pins x (H x)

theorem overlay_size {X Y : Type} [Fintype X] [DecidableEq X] (pins D : Database X Y) : (overlay pins D).size ≤ pins.size+D.size := by
  apply le_trans _ (Finset.card_union_le (occupied pins) (occupied D))
  apply Finset.card_le_card
  intro i hi
  change i ∈ occupied pins ∪ occupied D
  by_cases h : (pins i).isSome = true
  · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)
  · have n : pins i = none := Option.not_isSome_iff_eq_none.mp h
    have v := (Finset.mem_filter.mp hi).2
    exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simpa [overlay,n] using v⟩)

private theorem insert_free (pins D : Bank) (x : Addr) (h : pins x = none) (y : Words) :
    overlay pins (Function.update D x (some y)) = Function.update (overlay pins D) x (some y) := by
  funext i
  by_cases eq : i = x
  · subst i; simp [overlay,h]
  · simp [overlay,Function.update_of_ne eq]

private theorem insert_known (pins D : Bank) (x : Addr) (h : (pins x).isSome) (y : Words) :
    overlay pins (Function.update D x (some y)) = overlay pins D := by
  funext i
  by_cases eq : i = x
  · subst i; obtain ⟨v,h⟩ := Option.isSome_iff_exists.mp h; simp [overlay,h]
  · simp [overlay,Function.update_of_ne eq]

variable (tag : Bank → Bool) (pins : Bank)
theorem growth (q t : ℕ) (ht : t ≤ q) (δ : ℝ≥0∞) (fin : δ ≠ ⊤)
    (stable : ∀ D x, D x = none → ∀ y, tag D = false → tag (Function.update D x (some y)) = false)
    (step : ∀ D : Bank, D.size ≤ pins.size + (q+1) → ∀ x, D x = none → tag D = true →
      uniformMean (fun v : Words => Classic.hit (tag (Function.update D x (some v)) = false)) ≤ δ) :
    Growth (fun D => tag (overlay pins D) = false) t δ.toReal := by
  apply growth_of_label (fun D => tag (overlay pins D)) q t ht δ fin
  · intro D x emp y bad
    cases h : pins x with
    | none => rw [insert_free pins D x h]; exact stable _ x (by simp [overlay,h,emp]) y bad
    | some u => simpa only [insert_known pins D x (Option.isSome_iff_exists.mpr ⟨u,h⟩)] using bad
  · intro D sz x emp good
    cases h : pins x with
    | none =>
      simp only [insert_free pins D x h]
      exact step _ ((overlay_size pins D).trans (Nat.add_le_add_left sz _)) x (by simp [overlay,h,emp]) good
    | some u =>
      simp only [insert_known pins D x (Option.isSome_iff_exists.mpr ⟨u,h⟩),good,Bool.true_eq_false,Classic.hit,ite_false,
        Classic.avg_const,zero_le]

def evidence (m : ℕ) (l : Log) (H : Table) :=
  (∀ D, Matches D l → tag D = false) ∧ l.length ≤ m ∧ ∀ i y, (i,y) ∈ l → H i = y

theorem log_readout (m : ℕ) (l : Log) {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (v : Bank → V) : sumWeight (fun H => evidence tag m l (complete pins H)) (fun H => tensor v (fun j => some (H j))) ≤
      (Real.sqrt (sumWeight (fun D => tag (overlay pins D) = false) v) +
        (2*(m:ℝ)*Real.sqrt (Fintype.card Words : ℝ)⁻¹)*Real.sqrt (∑ d, ‖v d‖^2))^2 := by
  classical
  by_cases ex : ∃ H, evidence tag m l (complete pins H)
  · obtain ⟨H0,valid,len,agree⟩ := ex
    let free := l.filter (fun p => (pins p.1).isNone)
    let cell : Addr × Words → Addr × Finset Words := fun p => (p.1,{p.2})
    apply readout_failure (free.map cell) m ((List.length_map ..).le.trans ((List.length_filter_le ..).trans len)) _
      (by positivity) _ _ _ _ _ v
    · intro c hc
      obtain ⟨p,_,rfl⟩ := List.mem_map.mp hc
      simp only [cell,Finset.card_singleton,Nat.cast_one,one_div]; exact le_rfl
    · intro H h c hc
      obtain ⟨p,mem,rfl⟩ := List.mem_map.mp hc
      obtain ⟨hp,hn⟩ := List.mem_filter.mp mem
      have n : pins p.1 = none := Option.isNone_iff_eq_none.mp hn
      exact Finset.mem_singleton.mpr (by simpa [complete,response,n] using h.2.2 _ _ hp)
    · intro D h
      apply valid
      intro i y mem
      cases eq : pins i with
      | some z => simpa [overlay,eq] using congrArg some (show z = y by simpa [complete,response,eq] using agree i y mem)
      | none =>
        have inFree : (i,y) ∈ free := List.mem_filter.mpr ⟨mem,by simp [eq]⟩
        obtain ⟨w,hw,read⟩ := h _ (List.mem_map.mpr ⟨_,inFree,rfl⟩)
        simpa [overlay,eq,cell,Finset.mem_singleton.mp hw] using read
  · have no (H : Table) := not_exists.mp ex H
    simp only [sumWeight,no,ite_false,Finset.sum_const_zero]
    exact sq_nonneg _

theorem machine {W : Type} [Fintype W] [DecidableEq W] (M : Table → Closed (WS Addr Words W) Log)
    (q m : ℕ) (hq : PUE (spec := unifSpec) cnt0 M q) (ρ : Matrix (WS Addr Words W) (WS Addr Words W) ℂ)
    (hp : ρ.PosSemidef) (ht : ρ.trace = 1) (δ : ℝ≥0∞) (fin : δ ≠ ⊤) (clean : tag pins = true)
    (stable : ∀ D x, D x = none → ∀ y, tag D = false → tag (Function.update D x (some y)) = false)
    (step : ∀ D : Bank, D.size ≤ pins.size + (q+1) → ∀ x, D x = none → tag D = true →
      uniformMean (fun v : Words => Classic.hit (tag (Function.update D x (some v)) = false)) ≤ δ) :
    uniformMean (fun H => qWeight (fun l => evidence tag m l (complete pins H)) (M (complete pins H)) ρ) ≤
    ENNReal.ofReal ((2*(m:ℝ)*Real.sqrt (Fintype.card Words : ℝ)⁻¹ + q*(4*Real.sqrt δ.toReal))^2) := by
  have start : overlay pins (fun _ => none) = pins := by funext x; cases h : pins x <;> simp [overlay,h]
  apply Compression.Recording.RawFailure.machine_mean (response pins) (fun D => tag (overlay pins D) = false)
    (fun l H => evidence tag m l (complete pins H)) M q hq ρ hp ht δ.toReal _ ENNReal.toReal_nonneg (by positivity)
  · simp [start,clean]
  · exact fun t ht => growth tag pins q t ht δ fin stable step
  · exact fun _ l v => log_readout tag pins m l v

end
end Reduction.ShakePermutation.Long.Pinned
#print axioms Reduction.ShakePermutation.Long.Pinned.machine
