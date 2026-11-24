import Integration.SlhDsaCompressionHmac

namespace Reduction.Compression.HmacKey
open MLink Ideal SLHDSA SLHDSA.Concrete OracleComp OracleSpec PQ.Interactive Quantum ENNReal
open scoped Kronecker

private noncomputable def stateEquiv : Chain512 ≃ Bytes 64 := Equiv.ofBijective
  MIdeal.Sha512.serialize MIdeal.Sha512.serialize_bijective

variable (S : Sha2Set)

private theorem trunc_eq (s : Chain512) :
    truncate S s = MIdeal.Sha512.prefixBytes S (stateEquiv s) := by
  change truncate S s = MIdeal.Sha512.prefixBytes S (MIdeal.Sha512.serialize s)
  exact MIdeal.Sha512.prefix_eq S (MIdeal.Sha512.serialize s)

private def replacePrefix (s : Bytes 64) (v : S.Node) : Bytes 64 :=
  Vector.ofFn fun i => if h : i.val < S.vp.params.n then v[i.val]'h else s[i.val]

private theorem read_prefix (s : Bytes 64) (v : S.Node) :
    MIdeal.Sha512.prefixBytes S (replacePrefix S s v) = v := by
  ext i hi; simp [MIdeal.Sha512.prefixBytes, MIdeal.Sha512.takeBytes, replacePrefix]

private theorem undo_prefix (s : Bytes 64) (v : S.Node) :
    replacePrefix S (replacePrefix S s v) (MIdeal.Sha512.prefixBytes S s) = s := by
  ext i hi
  by_cases h : i < S.vp.params.n <;>
    simp [replacePrefix, MIdeal.Sha512.prefixBytes, MIdeal.Sha512.takeBytes, h]

private noncomputable def put {D : Type} (f : D → Chain512) (r : D → S.Node) (x : D) :=
  stateEquiv.symm (replacePrefix S (stateEquiv (f x)) (r x))

private theorem read_put {D : Type} (f : D → Chain512) (r : D → S.Node) :
    (fun x => truncate S (put S f r x)) = r := by
  funext x
  simp only [trunc_eq, put, Equiv.apply_symm_apply, read_prefix]

private theorem swap {D : Type} : Function.Involutive
    (fun z : (D → Chain512) × (D → S.Node) => (put S z.1 z.2, fun x => truncate S (z.1 x))) := by
  rintro ⟨f,r⟩
  refine Prod.ext (funext fun x => ?_) (read_put S f r)
  simp only [put, Equiv.apply_symm_apply, trunc_eq, undo_prefix, Equiv.symm_apply_apply]

/-- Truncating every entry of the private uniform outer function gives a uniform
function with the standardized SLH-DSA node width. Inputs may be repeated. -/
theorem trunc_table {D : Type} [Fintype D] [DecidableEq D] (score : (D → S.Node) → ℝ≥0∞) :
    (Fintype.card (D → Chain512) : ℝ≥0∞)⁻¹ * ∑ f : D → Chain512, score (fun d => truncate S (f d)) =
      (Fintype.card (D → S.Node) : ℝ≥0∞)⁻¹ * ∑ f : D → S.Node, score f := by
  let read := fun (f : D → Chain512) x => truncate S (f x)
  have h := SetOracle.avg_resample (put S) read (swap S) (fun f => score (read f))
  have hr (f : D → Chain512) (r : D → S.Node) : read (put S f r) = r := read_put S f r
  simp only [hr, ← Finset.sum_mul, sum_unifW, one_mul] at h
  simpa only [unifW, ← Finset.mul_sum] using h

/-- The sole remaining HMAC comparison is between a random function indexed by
the inner digest and the ideal message oracle. For distinct inner digests the
former has independent, uniform node values. -/
theorem wide_hmac_digest_game {E : Type} [Fintype E] [DecidableEq E] (hw : S.vp.params.n ≠ 16)
    (A : (Input → Output) → QOC (WS Input Output E) (PRFScheme.PRFOracleSpec (S.Node × List Byte) S.Node) Bool)
    (q : ℕ) (hA : PUE (messageCharge S) A q) (ρ : SubState ((Input × Output) × E)) :
    let M := ρ.matrix ⊗ₖ (SubState.basis ()).matrix
    (∑ g : CompressionTables, unifW _ g * qPrfRealPr (msgPrf S.vp (randPrims (functions S g))) (A (oracle g)) M) ≤
    (∑ g : CompressionTables, unifW _ g *
      ((Fintype.card Chain512 : ℝ≥0∞)⁻¹ * ∑ i : Chain512,
       (Fintype.card (Chain512 → S.Node) : ℝ≥0∞)⁻¹ * ∑ f : Chain512 → S.Node,
         qWeight (· = true) (ansRun (fun d => f (innerDigest S g i d)) (A (oracle g))) M)) +
    ENNReal.ofReal (8*(q:ℝ)^2 / 2^512) + ENNReal.ofReal (8*(q:ℝ)^2 / 2^(8*S.vp.params.n)) := by
  intro M
  have h := wide_hmac_to_inner S hw A q hA ρ
  have eq (g : CompressionTables) (i : Chain512) := trunc_table S
    (fun (f : Chain512 → S.Node) => qWeight (· = true) (ansRun (fun d => f (innerDigest S g i d)) (A (oracle g))) M)
  dsimp only at h eq
  refine h.trans (le_of_eq ?_)
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ rfl) rfl
  apply Finset.sum_congr rfl
  intro g _
  apply congrArg (unifW _ g * ·)
  apply congrArg ((Fintype.card Chain512 : ℝ≥0∞)⁻¹ * ·)
  exact Finset.sum_congr rfl fun i _ => eq g i

end Reduction.Compression.HmacKey
#print axioms Reduction.Compression.HmacKey.trunc_table
#print axioms Reduction.Compression.HmacKey.wide_hmac_digest_game
