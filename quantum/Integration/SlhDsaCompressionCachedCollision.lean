import Integration.SlhDsaCompressionTranscript
import Integration.SlhDsaCompressionCompileResponseNative
import Integration.SlhDsaCompressionClassPort

namespace Reduction.Compression.Recording.Compile
open MLink Ideal Ideal.Prf SLHDSA OracleComp OracleSpec PQ.Interactive PQ.QROM Quantum ENNReal Classical
open scoped Kronecker ComplexOrder

def cachedResponse (a : CF St Blk) (s : List Right) (t : Right → Chain512) : Response.Mapping
  | .inl x, _ => (a x,0)
  | .inr x, y => (0,arrayVectorEquivFin UInt64 8 (if x ∈ s then t x else y))

theorem cached_port (a : CF St Blk) (s : List Right) (t : Right → Chain512) (h : Full) :
    Response.project (cachedResponse a s t) h = oracle (a,mix s t (h ∘ Sum.inr)) := by
  funext x
  cases x with
  | inl x => rfl
  | inr x => by_cases hx : x ∈ s <;> simp [Response.project,cachedResponse,oracle,Ideal.Prf.mix,hx]

variable {E α T : Type} [Fintype E] [DecidableEq E] [DecidableEq T]

/-- After a fixed classical transcript, superposition queries see its recorded answers
and a fresh uniform table elsewhere. Reporting a collision of the fresh table still
obeys the cubic quantum bound. This covers every pair outside the recorded cells. -/
theorem cached_collision (p : Chain512 → T) (N : ℝ) (hN : 0 < N)
    (uniform : ∀ B : Finset T, ((Finset.univ.filter fun y => p y ∈ B).card : ℝ) /
      Fintype.card Chain512 ≤ (B.card:ℝ)/N)
    (a : CF St Blk) (s : List Right) (t : Right → Chain512)
    (M : (Input → Output) → Closed (WS Input Output E) α)
    (pick : α → Option (Right × Right)) (q : ℕ) (hq : PUE (spec := unifSpec) cnt0 M q)
    (ρ₀ : Matrix (WS Input Output E) (WS Input Output E) ℂ)
    (pos : ρ₀.PosSemidef) (tr : ρ₀.trace = 1) :
    (∑ b : Right → Chain512, unifW _ b * qWeight (fun z => wins p (a,b) (pick z))
      (M (oracle (a,mix s t b))) ρ₀) ≤ ENNReal.ofReal (16*((q:ℝ)+1)^3/N) := by
  obtain ⟨x,hx,he⟩ := hq.exists_prog_qprob
  obtain ⟨ρ,hρ⟩ := exists_subState (A := (Input × Output) × E) ρ₀ pos tr
  rw [← right_mean (fun b => qWeight (fun z => wins p (a,b) (pick z)) (M (oracle (a,mix s t b))) ρ₀)]
  let ev := fun h : Full => fun z : α => Database.reports p (taggedPair (pick z)) h
  calc _ = ∑ h : Full, unifW _ h * qprob LocalSig.Interp.instruments
          (Response.project (cachedResponse a s t) h) x ρ (fun v => ev h v.2) := by
            apply Finset.sum_congr rfl
            intro h _
            apply congrArg (unifW _ h * ·)
            rw [he (ev h) _ ρ,cached_port,← hρ]
            exact qWeight_congr_ev (fun z => (reports_tagged p a h (pick z)).symm) _ _
       _ ≤ _ := mixed_mean_over LocalSig.Interp.instruments x ρ q hx
         (Response.project (cachedResponse a s t)) (fun h v => ev h v.2) _ (by positivity)
         (fun u => Response.pure_mean p N hN uniform LocalSig.Interp.instruments
           (cachedResponse a s t) (fun z => taggedPair (pick z)) x q hx u)
end Reduction.Compression.Recording.Compile
#print axioms Reduction.Compression.Recording.Compile.cached_collision
