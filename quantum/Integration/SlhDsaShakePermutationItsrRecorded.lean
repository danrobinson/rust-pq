import Integration.SlhDsaShakePermutationItsrGrowth
import Integration.SlhDsaShakePermutationItsrWitness

/-! The compressed-oracle recurrence for a quantum machine that returns a
bounded witness of a collision in two recorded multi-block sponge paths. -/
namespace Reduction.ShakePermutation.ItsrLabel
open Classical Tails MLink SLHDSA Quantum OracleSpec OracleComp PQ.Interactive ENNReal SetOracle
open Compression.Recording.Database (Growth assemble Rest occupied assemble_at assemble_other occupied_assemble_le sumWeight tensor readout_failure)
open scoped ComplexOrder
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 1200000
set_option allowUnsafeReducibility true in
attribute [local irreducible] Graph.support label Good key targets SetOracle.uniformMean Fintype.card

def valid (S π L) (l : Log) := ∀ D, Matches D l → label S π L D = false
def evidence (S π L m) (l : Log) (H : Table) :=
  valid S π L l ∧ l.length ≤ m ∧ ∀ i y, (i,y) ∈ l → H i = y

private theorem fill {X Y : Type} [Fintype X] [Fintype Y] [Nonempty Y] [DecidableEq X] (x : X) (r : Rest x Y) (v : Y) :
    Function.update (assemble x r none) x (some v) = assemble x r (some v) := by
  funext z
  by_cases e : z = x <;> simp [e,Function.update,assemble_at,assemble_other]

private theorem mean_fraction {U : Type} [Fintype U] [DecidableEq U] (p : U → Prop) [DecidablePred p] :
    uniformMean (fun u => Classic.hit (p u)) = ((Finset.univ.filter p).card : ℝ≥0∞)/Fintype.card U := by
  simpa only [Finset.mem_filter,Finset.mem_univ,true_and] using Classic.mean_hit (Finset.univ.filter p)

private theorem convert_fraction {U : Type} [Fintype U] [DecidableEq U] (p : U → Prop) [DecidablePred p]
    (b : ℝ≥0∞) (hb : b ≠ ⊤) (h : uniformMean (fun u => Classic.hit (p u)) ≤ b) :
    ((Finset.univ.filter p).card : ℝ)/Fintype.card U ≤ b.toReal := by
  rw [mean_fraction] at h
  simpa only [ENNReal.toReal_div,ENNReal.toReal_natCast] using ENNReal.toReal_mono hb h

theorem rate_finite (S : Sha2Set) (q : ℕ) : rateBound S q ≠ ⊤ := by
  unfold rateBound
  have h : (Fintype.card Capacity : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  exact ENNReal.add_ne_top.mpr ⟨ENNReal.div_ne_top (ENNReal.natCast_ne_top _) h,
    ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (pow_ne_zero _ (by norm_num))⟩

private theorem growth_of_label {X Y : Type} [Fintype X] [Fintype Y] [Nonempty Y] [DecidableEq X] [DecidableEq Y]
    (tag : Database X Y → Bool) (q t : ℕ) (ht : t ≤ q) (δ : ℝ≥0∞) (fin : δ ≠ ⊤)
    (mono : ∀ D x, D x = none → ∀ v, tag D = false → tag (Function.update D x (some v)) = false)
    (step : ∀ D : Database X Y, D.size ≤ q+1 → ∀ x, D x = none → tag D = true →
      uniformMean (fun v : Y => Classic.hit (tag (Function.update D x (some v)) = false)) ≤ δ) :
    Growth (fun D => tag D = false) t δ.toReal := by
  constructor
  · intro x r u hb
    cases u with
    | none => exact hb
    | some v => rw [← fill]; exact mono _ _ (assemble_at ..) _ hb
  · intro x r cnt clean
    let D : Database X Y := assemble x r none
    have sz : D.size ≤ q+1 := (occupied_assemble_le x r none).trans (Nat.succ_le_succ (cnt.trans ht))
    have ok : tag D = true := Bool.eq_true_of_not_eq_false clean
    have h := step D sz x (assemble_at ..) ok
    simp only [D,fill] at h
    let p := fun v : Y => tag (assemble x r (some v)) = false
    let dp : DecidablePred p := fun v => instDecidableEqBool _ _
    let dc : DecidablePred p := fun v => Classical.propDecidable _
    have eq : dc = dp := Subsingleton.elim _ _
    change ((@Finset.filter _ p dc Finset.univ).card : ℝ)/Fintype.card Y ≤ _
    rw [eq]
    exact @convert_fraction Y _ _ p dp δ fin h

theorem recorded_growth (S π L) (hp : ¬irregular π) (he : ¬Pairs.exceptional π) (q t : ℕ) (ht : t ≤ q) :
    Growth (fun D => label S π L D = false) t (rateBound S (q+1)).toReal :=
  growth_of_label (label S π L) q t ht _ (rate_finite S (q+1)) (stable_bad S π L)
    (fun D => mean_step S π L hp he D (q+1))

private theorem log_readout (S π L m) (l : Log) {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (v : Bank → V) : sumWeight (evidence S π L m l) (fun H => tensor v (fun j => some (H j))) ≤
      (Real.sqrt (sumWeight (fun D => label S π L D = false) v) +
        (2*(m:ℝ)*Real.sqrt (Fintype.card Words : ℝ)⁻¹)*Real.sqrt (∑ d, ‖v d‖^2))^2 := by
  classical
  by_cases admissible : valid S π L l ∧ l.length ≤ m
  · let cell : Addr × Words → Addr × Finset Words := fun p => (p.1,{p.2})
    apply readout_failure (l.map cell) m (by simpa only [List.length_map] using admissible.2) _
      (by positivity) _ _ _ _ _ v
    · intro c hc
      obtain ⟨p,_,rfl⟩ := List.mem_map.mp hc
      simp only [cell,Finset.card_singleton,Nat.cast_one,one_div]; exact le_rfl
    · intro H h c hc
      obtain ⟨p,mem,rfl⟩ := List.mem_map.mp hc
      exact Finset.mem_singleton.mpr (h.2.2 p.1 p.2 mem)
    · intro D h
      apply admissible.1 D
      intro i y hy
      obtain ⟨v,hv,eq⟩ := h (cell (i,y)) (List.mem_map.mpr ⟨_,hy,rfl⟩)
      exact eq.trans (congrArg some (Finset.mem_singleton.mp hv))
  · have no (H : Table) : ¬ evidence S π L m l H := fun e => admissible ⟨e.1,e.2.1⟩
    simp only [sumWeight,no,ite_false,Finset.sum_const_zero]
    exact sq_nonneg _

def price (S : Sha2Set) (q m : ℕ) :=
  (2*(m:ℝ)*Real.sqrt (Fintype.card Words : ℝ)⁻¹ + q*(4*Real.sqrt (rateBound S (q+1)).toReal))^2

theorem recorded_security (S π L) (hp : ¬irregular π) (he : ¬Pairs.exceptional π)
    {W : Type} [Fintype W] [DecidableEq W] (M : Table → Closed (WS Addr Words W) Log) (q m : ℕ)
    (hq : PUE (spec := unifSpec) cnt0 M q) (ρ : Matrix (WS Addr Words W) (WS Addr Words W) ℂ)
    (pos : ρ.PosSemidef) (tr : ρ.trace = 1) :
    uniformMean (fun H => qWeight (fun l => evidence S π L m l H) (M H) ρ) ≤ ENNReal.ofReal (price S q m) := by
  have empty : ¬label S π L (fun _ => none) = false := by
    unfold label; exact fun hb => (of_decide_eq_false hb) (good_empty S π L)
  let δ := (rateBound S (q+1)).toReal
  let K := 2*(m:ℝ)*Real.sqrt (Fintype.card Words : ℝ)⁻¹
  unfold uniformMean price
  exact Compression.Recording.RawFailure.machine_mean (X := Addr) (Y := Words) (Z := Words)
    (fun _ y => y) (fun D => label S π L D = false) (evidence S π L m) M q hq ρ pos tr δ K
    ENNReal.toReal_nonneg (by dsimp [K]; positivity) empty (recorded_growth S π L hp he q)
    (fun _ l w => log_readout S π L m l w)

end
end Reduction.ShakePermutation.ItsrLabel
#print axioms Reduction.ShakePermutation.ItsrLabel.recorded_security
