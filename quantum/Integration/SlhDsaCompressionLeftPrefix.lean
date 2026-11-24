import Integration.SlhDsaCompressionLeftBound

namespace Reduction.Compression.Recording.Compile.LeftPort
open MLink Ideal SLHDSA OracleComp OracleSpec PQ.Interactive PQ.QROM Quantum ENNReal Classical
open scoped ComplexOrder

theorem out16_fraction (B : Finset (Bytes 16)) :
    ((Finset.univ.filter fun y => out16 y ∈ B).card : ℝ) / Fintype.card St = (B.card : ℝ)/2^128 := by
  have h := prEvent_out16 (fun y => y ∈ B)
  simp only [SampleableType.prEvent_uniformSample] at h
  have e := congrArg ENNReal.toReal h
  have hc : (Fintype.card (Bytes 16) : ℝ) = 2^128 := by rw [card_bytes]; norm_num
  rw [← hc]
  simpa only [ENNReal.toReal_div,ENNReal.toReal_natCast,Finset.filter_mem_eq_inter,Finset.univ_inter] using e

variable {E α : Type} [Fintype E] [DecidableEq E]
theorem search {T : Type} [DecidableEq T] (p : St → T) (bits : ℕ)
    (uniform : ∀ B : Finset T, ((Finset.univ.filter fun y => p y ∈ B).card : ℝ) / Fintype.card St ≤ (B.card:ℝ)/2^bits)
    (M : (Input → Output) → Closed (WS Input Output E) α) (pick : α → Option (Left × Left))
    (q : ℕ) (hq : PUE (spec := unifSpec) cnt0 M q) (ρ : Matrix (WS Input Output E) (WS Input Output E) ℂ)
    (hp : ρ.PosSemidef) (ht : ρ.trace = 1) :
    (∑ g : CompressionTables, unifW _ g * qWeight (fun z => wins p g (pick z)) (M (oracle g)) ρ) ≤
      16*((q:ℝ≥0∞)+1)^3/2^bits := by
  have b := shared_collision p (2^bits) (by positivity) uniform M pick q hq ρ hp ht
  apply b.trans_eq
  rw [ENNReal.ofReal_div_of_pos (by positivity),ENNReal.ofReal_mul (by norm_num),
    ENNReal.ofReal_pow (by positivity),ENNReal.ofReal_pow (by norm_num),
    ENNReal.ofReal_add (by positivity) (by norm_num)]
  norm_num

theorem id_fraction (B : Finset St) :
    ((Finset.univ.filter fun y => id y ∈ B).card : ℝ) / Fintype.card St = (B.card : ℝ)/2^256 := by
  simp only [id_eq,Finset.filter_mem_eq_inter,Finset.univ_inter,card_St,Nat.cast_pow,Nat.cast_ofNat]
end Reduction.Compression.Recording.Compile.LeftPort
#print axioms Reduction.Compression.Recording.Compile.LeftPort.search
