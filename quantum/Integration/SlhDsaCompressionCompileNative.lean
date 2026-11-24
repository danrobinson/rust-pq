import Integration.SlhDsaCompressionCompileResponseNative

/-! A bounded VCVio program is evaluated against its decoded recording state.
Local instruments may have infinitely many outcomes. The finite-cut Kraus
estimate controls their total via a summable branch series. -/

namespace Reduction.Compression.Recording.Compile
open PQ.QROM Quantum Database MLink Ideal Classical Finset
variable {α T : Type} [DecidableEq T] (p : Chain512 → T) (N : ℝ) (hN : 0 < N)
variable (uniform : ∀ B : Finset T, ((Finset.univ.filter fun y => p y ∈ B).card : ℝ) /
  Fintype.card Chain512 ≤ (B.card:ℝ)/N)
variable {L : LocalSig.{1,0}} (I : L.Interp) (a : CF St Blk) (pick : α → Option (Input × Input))
local notation "Prog" => QuantumComp L (qromSpec Input Output) (fun _ => α)
private theorem project_response (h : Full) :
    Response.project (response a) h = project a h := by
  funext x
  cases x <;> rfl

noncomputable def score {A : QReg} (x : Prog A) (v : State A) :=
  Response.score p I (response a) pick x v

include hN uniform in
theorem native_bound {A : QReg} (x : Prog A) (Q n t : ℕ) (hQ : QueryBounded x n) (ht : t+n ≤ Q)
    (v : State A) (hs : sparse t v) : score p I a pick x v ≤ potential p (price N Q n) v :=
  Response.native_bound p N hN uniform I (response a) pick x Q n t hQ ht v hs

include hN uniform in
theorem pure_mean {A : QReg} (x : Prog A) (q : ℕ) (hx : QueryBounded x q) (u : Vec A) :
    (∑ h : Full, (Fintype.card Full : ℝ)⁻¹ * Purify.pv I (project a h) x
      (fun t => reports p (pick t.2) h) u) ≤ 16*((q:ℝ)+1)^3/N * ‖u‖^2 := by
  simpa only [project_response] using Response.pure_mean p N hN uniform I (response a) pick x q hx u

end Reduction.Compression.Recording.Compile
#print axioms Reduction.Compression.Recording.Compile.native_bound
#print axioms Reduction.Compression.Recording.Compile.pure_mean
