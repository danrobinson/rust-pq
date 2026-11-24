import Integration.SlhDsaCompressionQuantum
import MIdeal.Thash512
import MIdeal.SkPrf

namespace Reduction.Compression
open MLink Ideal SLHDSA SLHDSA.Concrete OracleComp OracleSpec PQ.Interactive PQ.QROM Quantum ENNReal
open VCVio.Algorithms.Sha2

/-- Classical observations of the two SHA-2 compression functions from one quantum port. -/
def tablesOf (H : Input → Output) : CompressionTables :=
  (fun i => (H (.inl i)).1, fun i => (arrayVectorEquivFin UInt64 8).symm (H (.inr i)).2)

theorem tablesOf_oracle (g : CompressionTables) : tablesOf (oracle g) = g := by
  refine Prod.ext rfl (funext fun i => ?_)
  exact (arrayVectorEquivFin UInt64 8).symm_apply_apply _

private theorem fold_cost {C B : Type} (f : (Input → Output) → CF C B)
    (step : ∀ c b, EvalCost (fun H => (pure (f H (c,b)) : ProbComp C)) 1)
    (c : C) (bs : List B) :
    EvalCost (fun H => (pure (mdFold (f H) c bs) : ProbComp C)) bs.length := by
  induction bs generalizing c with
  | nil => exact EvalCost.const (X := Input) (Y := Output) (pure c)
  | cons b bs ih =>
    have h := EvalCost.bind (step c b) (fun c' => ih c')
    simpa only [pure_bind, mdFold, List.foldl_cons, List.length_cons, Nat.add_comm 1] using h

theorem fold256_cost (c : St) (bs : List Blk) :
    EvalCost (fun H => (pure (mdFold (tablesOf H).1 c bs) : ProbComp St)) bs.length :=
  fold_cost (fun H => (tablesOf H).1) (fun c b => EvalCost.eval (X := Input) (Y := Output) (.inl (c,b)) Prod.fst) c bs

theorem fold512_cost (c : Chain512) (bs : List Block512) :
    EvalCost (fun H => (pure (mdFold (tablesOf H).2 c bs) : ProbComp Chain512)) bs.length :=
  fold_cost (fun H => (tablesOf H).2) (fun c b => EvalCost.eval (X := Input) (Y := Output) (.inr (c,b)) (fun y => (arrayVectorEquivFin UInt64 8).symm y.2)) c bs

theorem sha256_cost (m : ByteArray) :
    EvalCost (fun H => (pure (sha256G (liftC (tablesOf H).1) m) : ProbComp ByteArray)) ((m.size+8)/64+1) := by
  have h := (fold256_cost IV128 (padBlocks m)).map digestBytes
  simpa only [sha256G_shape, padBlocks_length, map_pure] using h

theorem sha512_cost (m : ByteArray) :
    EvalCost (fun H => (pure (sha512G (lift512 (tablesOf H).2) m) : ProbComp ByteArray)) ((m.size+16)/128+1) := by
  have h := (fold512_cost MIdeal.Sha512.initial (MIdeal.Sha512.padBlocks m)).map (fun s => stateBytes64 s.toArray)
  simpa only [MIdeal.Sha512.sha512_shape, MIdeal.Sha512.padBlocks_length, map_pure] using h

variable (S : Sha2Set)

/-- Two port queries evaluate the exact truncated secret-address PRF. -/
theorem address_cost (pk key : S.Node) (a : SkAdrs S.vp) :
    EvalCost (fun H => (pure ((tablePrimitives (tablesOf H) S.vp.params).PRF pk key a.val) : ProbComp S.Node)) 2 := by
  have h := (fold256_cost IV128 [MIdeal.SkPrf.seedBlock S pk,
    MIdeal.SkPrf.singletonBlock S (sha2AdrsKey a.val) key]).map (MIdeal.SkPrf.output S)
  simp only [MIdeal.SkPrf.mixed_shape, prfF, MIdeal.SkPrf.keyBlock]
  simpa only [map_pure, mdFold, List.foldl_cons, List.foldl_nil, List.length_cons, List.length_nil] using h

def thashCalls (arity : ℕ) :=
  if arity = 1 ∨ S.vp.params.n = 16 then (30 + S.vp.params.n*arity)/64+2
  else (38 + S.vp.params.n*arity)/128+2

private theorem payload_size (xs : List S.Node) : (concatBytes xs).size = S.vp.params.n * xs.length := by
  have e := congrArg List.length (MIdeal.Sha512.concat_payload S xs)
  simpa only [ByteArray.size, Array.length_toList, MIdeal.Sha512.payload_length] using e

private theorem prefix_size (pk : S.Node) (a : Bytes 22) :
    (sha2Prefix256Key pk a).size = 86 ∧ (sha2Prefix512Key pk a).size = 150 := by
  have width : S.vp.params.n ≤ 32 := by cases S <;> decide
  simp [sha2Prefix256Key, sha2Prefix512Key, bytesToByteArray, zeroByteArray, ByteArray.size_append, ByteArray.size]
  omega

theorem thash_cost (pk : S.Node) (a : Bytes 22) (xs : List S.Node) :
    EvalCost (fun H => (pure ((tablePrimitives (tablesOf H) S.vp.params).Thash pk a xs) : ProbComp S.Node))
      (thashCalls S xs.length) := by
  let m₂ := sha2Prefix256Key pk a ++ concatBytes xs
  let m₅ := sha2Prefix512Key pk a ++ concatBytes xs
  have h₂ := (sha256_cost m₂).map (fun b => byteArrayPrefixOrZero b S.vp.params.n)
  have h₅ := (sha512_cost m₅).map (fun b => byteArrayPrefixOrZero b S.vp.params.n)
  have l₂ : (m₂.size + 8)/64+1 = (30+S.vp.params.n*xs.length)/64+2 := by
    rw [show m₂.size = 86 + S.vp.params.n*xs.length by simp [m₂, (prefix_size S pk a).1, payload_size]]
    omega
  have l₅ : (m₅.size + 16)/128+1 = (38+S.vp.params.n*xs.length)/128+2 := by
    rw [show m₅.size = 150 + S.vp.params.n*xs.length by simp [m₅, (prefix_size S pk a).2, payload_size]]
    omega
  change EvalCost (fun H => (pure (sha2ThashMixed (liftC (tablesOf H).1) (lift512 (tablesOf H).2)
    S.vp.params pk a xs) : ProbComp S.Node)) _
  rw [l₂] at h₂
  rw [l₅] at h₅
  by_cases h₁ : xs.length = 1
  · simpa only [thashCalls, sha2ThashMixed, ite_eq_left h₁, ite_eq_left (Or.inl h₁), map_pure, m₂] using h₂
  · by_cases hn : S.vp.params.n = 16
    · simpa only [thashCalls, sha2ThashMixed, ite_eq_right h₁, ite_eq_left hn, ite_eq_left (Or.inr hn), map_pure, m₂] using h₂
    · simpa only [thashCalls, sha2ThashMixed, ite_eq_right h₁, ite_eq_right hn,
        ite_eq_right (not_or.mpr ⟨h₁,hn⟩), map_pure, m₅] using h₅

end Reduction.Compression

#print axioms Reduction.Compression.address_cost

#print axioms Reduction.Compression.thash_cost
