import Integration.SlhDsaCompressionWotsSmallGame

namespace Reduction.Compression.Wots256
open Ideal Ideal.HP SLHDSA MLink TweakableHash OracleComp OracleSpec PQ.Interactive PQ.QROM Quantum ENNReal
variable {σ : Type}

noncomputable def preFirst (seeds : ProbComp Node) (n : ℕ)
    (choose : OracleComp (PreSpecG (preP seeds n (fun _ => IV128))) σ) : PreAdv (family seeds n) Node where
  State := σ
  choose := simulateQ Realize.embImpl choose
  invert := fun _ _ => pure default

noncomputable def tcrFirst (seeds : ProbComp Node) (n : ℕ)
    (choose : OracleComp (TcrSpec (tcrP seeds n (fun _ => IV128))) σ) : TcrAdv (family seeds n) where
  State := σ
  choose := simulateQ Realize.embImpl choose
  forge := fun _ _ => pure default

noncomputable def udFirst (seeds : ProbComp Node) (n : ℕ)
    (pick : OracleComp (UdSpecG (udP seeds n (fun _ => IV128))) σ) : UdAdv (family seeds n) where
  State := σ
  pick := simulateQ Realize.embImpl pick
  distinguish := fun _ _ => pure false

end Reduction.Compression.Wots256
