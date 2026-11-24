import Integration.SlhDsaCompressionClassicalForger

namespace Reduction.Compression.ClassicalPort
open MLink Ideal PQ.Interactive PQ.QROM Quantum OracleComp OracleSpec ENNReal Matrix SLHDSA
open MIdeal.PureCompression Classical
open scoped ComplexOrder Kronecker
set_option maxRecDepth 10000
abbrev Msg := List Byte × List Byte
abbrev Sgn := Option (List Byte)
local notation "Work" => WS Input Output Unit
variable {SK : Type} (alg : SignatureAlg ProbComp Msg (List Byte) SK Sgn)
variable (A : MIdeal.PureCompression.Forger) (g : CompressionTables)

theorem classical_game (fresh : QueryLog (Msg →ₒ Sgn) → Msg → Sgn → Bool) :
    qWeight (· = true) (qSigExperiment fresh ((asPort A).at (oracle g) alg)) (asPort A).ρ₀ =
    prob (alg.keygen >>= fun ks =>
      alg.runWithSigningOracle ks.1 ks.2 (simulateQ (instImpl g.1) (simulateQ (instImpl g.2) (A.main ks.1))) >>= fun z =>
      alg.verify ks.1 z.1.1 z.1.2 >>= fun v => pure (fresh z.2 z.1.1 z.1.2 && v)) (· = true) := by
  let Q := (asPort A).at (oracle g) alg
  unfold qSigExperiment
  rw [← one_mul (prob _ _)]
  apply qWeight_liftU_bind
  intro ks
  rw [one_mul]
  let tail := fun z : Return × QueryLog (Msg →ₒ Sgn) =>
    alg.verify ks.1 z.1.1 z.1.2 >>= fun v => pure (fresh z.2 z.1.1 z.1.2 && v)
  let qt := fun z : Return × QueryLog (Msg →ₒ Sgn) =>
    (liftU (W := Work) (alg.verify ks.1 z.1.1 z.1.2) >>= fun v => pure (fresh z.2 z.1.1 z.1.2 && v))
  have h := program_weight (oracle g) (signImpl alg ks.1 ks.2) (simulateQ route (A.main ks.1)) [] initial
    qt tail (· = true) (by
      intro z r
      rw [← one_mul (prob _ _)]
      apply qWeight_liftU_bind
      intro v
      simp [qWeight_pure,prob_pure])
  rw [fixed_route,run_simulateQ_signImpl] at h
  simp only [List.nil_append,Prod.mk.eta,id_map'] at h
  dsimp only [PortForger.at,asPort,SubState.matrix_basis,qt,tail] at h ⊢
  convert h using 2
  ext i j; simp [Matrix.single_apply]

end Reduction.Compression.ClassicalPort
#print axioms Reduction.Compression.ClassicalPort.classical_game
