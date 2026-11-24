import Integration.SlhDsaCompressionCompileNative
import Integration.SlhDsaCompressionClassPort

namespace Reduction.Compression.Recording.Compile
open MLink Ideal SLHDSA OracleComp OracleSpec PQ.Interactive PQ.QROM Quantum ENNReal Classical
open scoped ComplexOrder
variable {E α T : Type} [Fintype E] [DecidableEq E] [DecidableEq T]

/-- A bounded quantum machine with coherent access to the shared pair of SHA-2
compression tables can report a collision in a balanced SHA-512 prefix only
with cubic-in-queries probability. -/
theorem shared_collision (p : Chain512 → T) (N : ℝ) (hN : 0 < N)
    (uniform : ∀ B : Finset T, ((Finset.univ.filter fun y => p y ∈ B).card : ℝ) /
      Fintype.card Chain512 ≤ (B.card:ℝ)/N)
    (M : (Input → Output) → Closed (WS Input Output E) α)
    (pick : α → Option (Right × Right)) (q : ℕ) (hq : PUE (spec := unifSpec) cnt0 M q)
    (ρ₀ : Matrix (WS Input Output E) (WS Input Output E) ℂ)
    (pos : ρ₀.PosSemidef) (tr : ρ₀.trace = 1) :
    (∑ g : CompressionTables, unifW _ g * qWeight (fun z => wins p g (pick z)) (M (oracle g)) ρ₀) ≤
      ENNReal.ofReal (16*((q:ℝ)+1)^3/N) := by
  apply shared_search_le p M pick q hq ρ₀ pos tr _ (by positivity)
  intro a x hx v
  exact pure_mean p N hN uniform LocalSig.Interp.instruments a (fun z => taggedPair (pick z)) x q hx v

end Reduction.Compression.Recording.Compile

#print axioms Reduction.Compression.Recording.Compile.shared_collision
