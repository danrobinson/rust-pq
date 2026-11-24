import MIdeal.SkPrf
import Ideal.Inst.ForsDspr128

namespace MIdeal.Fors
open MLink Ideal SLHDSA SLHDSA.Concrete TweakableHash OracleComp OracleSpec ENNReal
open SkPrf
variable (S : Sha2Set)

/-- FORS leaf hashing has one block after the public seed, including at the 32-byte width. -/
def family (seeds : ProbComp S.Node) : THFam St Blk S.Node (Bytes 22) S.Node S.Node Empty where
  IV := IV128
  sb := seedBlock S
  seedGen := seeds
  tch := fun t x => (singletonBlock S t x, [])
  out := output S
  Msg := fun i => i.elim
  cch := fun i => i.elim
  cout := fun i => i.elim
  numTargets := Reduction.openPreTargets S.vp

private theorem mixed_one (c : CompressFn) (d : Compress512Fn) (p : Params)
    (pk : Bytes p.n) (t : Bytes 22) (x : Bytes p.n) :
    sha2ThashMixed c d p pk t [x] = sha2ThashG c p pk t [x] := by
  simp only [sha2ThashMixed, sha2ThashG, List.length_cons, List.length_nil, ite_true]

theorem eval_eq (seeds : ProbComp S.Node) (g : CompressionTables) :
    (fun (pk : S.Node) (t : Bytes 22) (x : S.Node) => (tablePrimitives g S.vp.params).Thash pk t [x]) =
      (family S seeds).evalT g.1 := by
  funext pk t x
  change sha2ThashMixed (liftC g.1) (lift512 g.2) S.vp.params pk t [x] = _
  rw [mixed_one, singleton_shape S]
  unfold THFam.evalT keyedChain mdFold family
  rfl

theorem tcr_problem (seeds : ProbComp S.Node) (g : CompressionTables) :
    Reduction.forsTcrProblem S.vp (tablePrimitives g S.vp.params) seeds = (family S seeds).fvProb g.1 := by
  change SM_DT_TCR_SourceFinalValidity.Problem.standalone
    { seedGen := seeds, eval := fun pk t x => (tablePrimitives g S.vp.params).Thash pk t [x] }
    (Reduction.openPreTargets S.vp) = _
  erw [eval_eq S seeds g]; rfl

theorem dspr_problem (seeds : ProbComp S.Node) (g : CompressionTables) :
    Reduction.forsDsprProblem S.vp (tablePrimitives g S.vp.params) seeds = (family S seeds).dsprProb g.1 := by
  change SM_DT_DSPR_SourceFinalValidity.Problem.standalone
    { seedGen := seeds, eval := fun pk t x => (tablePrimitives g S.vp.params).Thash pk t [x] }
    (Reduction.openPreTargets S.vp) = _
  erw [eval_eq S seeds g]; rfl

private theorem read_address (a : Bytes 22) (x : S.Node) : btw128 (singletonBlock S a x) = a := by
  ext i hi
  simp [btw128, singletonBlock, List.getElem_append_left, hi]

private theorem inj (a : Bytes 22) (x y : S.Node) (h : singletonBlock S a x = singletonBlock S a y) :
    x = y := by
  have e := congrArg Vector.toList h
  change _ ++ tailL _ = _ ++ tailL _ at e
  exact Vector.toList_inj.mp (List.append_cancel_left (List.append_cancel_right e))

private theorem uniform_out (y : S.Node) :
    Pr{let u ← $ᵗ St}[output S u = y] = (Fintype.card S.Node : ℝ≥0∞)⁻¹ := by
  exact (balanced S (· = y)).trans (SampleableType.prEvent_uniformSample_eq_singleton y)

theorem tcr_bound (seeds : ProbComp S.Node) (γ : ℝ≥0∞)
    (hγ : ∀ s, Pr{let s' ← seeds}[s' = s] ≤ γ)
    (A : FvAdv (family S seeds)) (q₁ qch q₂ : ℕ)
    (h₁ : A.ChooseBound q₁) (hc : A.ChalBound qch) (h₂ : A.ForgeBound q₂) :
    tcrFVAdvantage (family S seeds) A ≤ (q₂+1 : ℕ) * (Fintype.card S.Node : ℝ≥0∞)⁻¹ +
      q₁*γ + (2*q₁+qch+2 : ℕ) * ((2:ℝ≥0∞)^256)⁻¹ := by
  have h := tcrFV_bound (F := family S seeds) (seed_inj S) γ hγ (fun _ _ => rfl) btw128
    (read_address S) (inj S) _ (fun y => (uniform_out S y).le) A q₁ qch q₂ h₁ hc h₂
  simpa only [card_St, Nat.cast_pow, Nat.cast_ofNat] using h

theorem dspr_bound (seeds : ProbComp S.Node) (γ : ℝ≥0∞)
    (hγ : ∀ s, Pr{let s' ← seeds}[s' = s] ≤ γ)
    (A : DsprAdv (family S seeds)) (q₁ qch q₂ : ℕ)
    (h₁ : A.ChooseBound q₁) (hc : A.ChalBound qch) (h₂ : A.GuessBound q₂)
    (hcap : 4*q₂ ≤ Fintype.card S.Node) :
    dsprSuccessI (family S seeds) A ≤ dsprSPI (family S seeds) A + 2*(q₁*γ) +
      (4*q₁+2*qch+3 : ℕ)*((2:ℝ≥0∞)^256)⁻¹ := by
  have hm : 32 ≤ Fintype.card S.Node := by rw [card_bytes]; cases S <;> decide
  have h := dspr_bound_uniform (F := family S seeds) (seed_inj S) γ hγ (fun _ _ => rfl)
    btw128 (read_address S) (inj S) (uniform_out S) hm A q₁ qch q₂ h₁ hc h₂ hcap
  simpa only [card_St, Nat.cast_pow, Nat.cast_ofNat] using h
end MIdeal.Fors

#print axioms MIdeal.Fors.tcr_problem
#print axioms MIdeal.Fors.dspr_problem
#print axioms MIdeal.Fors.tcr_bound
#print axioms MIdeal.Fors.dspr_bound
