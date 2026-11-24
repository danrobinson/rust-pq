import Integration.SlhDsaCompressionHmac256Inner

namespace Reduction.Compression.Hmac256
open MLink Ideal SLHDSA SLHDSA.Concrete OracleComp OracleSpec PQ.Interactive Quantum ENNReal
open scoped Kronecker

private def putPrefix (s : St) (x : Bytes 16) : St :=
  Vector.ofFn fun i => if h : i.val < 16 then x[i.val] else s[i.val]

private theorem trunc_put (s : St) (x : Bytes 16) : truncate (putPrefix s x) = x := by
  ext i hi
  simp [truncate,Ideal.out16,putPrefix]

private theorem undo (s : St) (x : Bytes 16) : putPrefix (putPrefix s x) (truncate s) = s := by
  ext i hi
  by_cases h : i < 16 <;> simp [putPrefix,truncate,Ideal.out16,h]

private def put {D : Type} (f : D → St) (r : D → Bytes 16) (x : D) := putPrefix (f x) (r x)

private theorem read_put {D : Type} (f : D → St) (r : D → Bytes 16) :
    (fun x => truncate (put f r x)) = r := funext fun x => trunc_put (f x) (r x)

private theorem swap {D : Type} : Function.Involutive
    (fun z : (D → St) × (D → Bytes 16) => (put z.1 z.2, fun x => truncate (z.1 x))) :=
  fun ⟨f,r⟩ => Prod.ext (funext (fun x => undo (f x) (r x))) (read_put f r)

/-- Truncating every entry of the private uniform outer function gives a uniform
function with the standardized SLH-DSA node width. Inputs may be repeated. -/
theorem trunc_table {D : Type} [Fintype D] [DecidableEq D] (score : (D → (Bytes 16)) → ℝ≥0∞) :
    (Fintype.card (D → St) : ℝ≥0∞)⁻¹ * ∑ f : D → St, score (fun d => truncate (f d)) =
      (Fintype.card (D → (Bytes 16)) : ℝ≥0∞)⁻¹ * ∑ f : D → (Bytes 16), score f := by
  let read := fun (f : D → St) x => truncate (f x)
  have h := SetOracle.avg_resample (put) read (swap) (fun f => score (read f))
  have hr (f : D → St) (r : D → (Bytes 16)) : read (put f r) = r := read_put f r
  simp only [hr, ← Finset.sum_mul, sum_unifW, one_mul] at h
  simpa only [unifW, ← Finset.mul_sum] using h

/-- The sole remaining HMAC comparison is between a random function indexed by
the inner digest and the ideal message oracle. For distinct inner digests the
former has independent, uniform node values. -/
theorem hmac_digest_game {E : Type} [Fintype E] [DecidableEq E]
    (A : (Input → Output) → QOC (WS Input Output E) (PRFScheme.PRFOracleSpec ((Bytes 16) × List Byte) (Bytes 16)) Bool)
    (q : ℕ) (hA : PUE (messageCharge) A q) (ρ : SubState ((Input × Output) × E)) :
    let M := ρ.matrix ⊗ₖ (SubState.basis ()).matrix
    (∑ g : CompressionTables, unifW _ g * qPrfRealPr (msgPrf Sha2Set.s128s.vp (randPrims (functions Sha2Set.s128s g))) (A (oracle g)) M) ≤
    (∑ g : CompressionTables, unifW _ g *
      ((Fintype.card St : ℝ≥0∞)⁻¹ * ∑ i : St,
       (Fintype.card (St → (Bytes 16)) : ℝ≥0∞)⁻¹ * ∑ f : St → (Bytes 16),
         qWeight (· = true) (ansRun (fun d => f (innerDigest g i d)) (A (oracle g))) M)) +
    ENNReal.ofReal (8*(q:ℝ)^2 / 2^256) + ENNReal.ofReal (8*(q:ℝ)^2 / 2^128) := by
  intro M
  have h := hmac_to_inner A q hA ρ
  have eq (g : CompressionTables) (i : St) := trunc_table
    (fun (f : St → (Bytes 16)) => qWeight (· = true) (ansRun (fun d => f (innerDigest g i d)) (A (oracle g))) M)
  dsimp only at h eq
  refine h.trans (le_of_eq ?_)
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ rfl) rfl
  apply Finset.sum_congr rfl
  intro g _
  apply congrArg (unifW _ g * ·)
  apply congrArg ((Fintype.card St : ℝ≥0∞)⁻¹ * ·)
  exact Finset.sum_congr rfl fun i _ => eq g i

end Reduction.Compression.Hmac256
#print axioms Reduction.Compression.Hmac256.trunc_table
#print axioms Reduction.Compression.Hmac256.hmac_digest_game
