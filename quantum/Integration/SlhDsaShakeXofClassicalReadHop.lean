import Integration.SlhDsaShakeXofHiddenRowList
import Ideal.Core.HPBasic
import PQ.Interactive.ApproxLimit

namespace Reduction.ShakeXof
open OracleComp OracleSpec PQ.Interactive Quantum Filter Topology Ideal.HP
open scoped ComplexOrder

/-- Freeze the classical reads of a quantum machine at a second table.
The success probability increases by at most the probability that the
second-table run actually reads a changed location. All quantum operations
(including any coherent port already compiled into the machine) stay fixed
throughout this hop, and the classical reads may be interleaved with them. -/
theorem freeze_classical_reads {ι W : Type} [Fintype W] {sp : OracleSpec ι}
    (a b : (t : ι) → sp.Range t) (bad : ι → Bool)
    (agree : ∀ z, bad z = false → a z = b z)
    (Q : QOC W (unifSpec + sp) Bool) (ρ : Matrix W W ℂ) (psd : ρ.PosSemidef) (unit : ρ.trace = 1) :
    qWeight (fun z => z.1 = true) (close (trImpl a) Q []) ρ ≤
    qWeight (fun z => z.1 = true) (close (trImpl b) Q []) ρ +
      qWeight (fun z => z.2.any bad = true) (close (trImpl b) Q []) ρ := by
  have fw (c : (t : ι) → sp.Range t) : ForwardsUnif (trImpl c) := fun _ _ => rfl
  apply le_of_tendsto_of_tendsto'
    (tendsto_prEvent_close_toProbCompN _ (fw a) (fun z => z.1 = true) Q [] ρ psd unit)
    ((tendsto_prEvent_close_toProbCompN _ (fw b) (fun z => z.1 = true) Q [] ρ psd unit).add
      (tendsto_prEvent_close_toProbCompN _ (fw b) (fun z => z.2.any bad = true) Q [] ρ psd unit))
  intro n
  let P := toProbCompN n Q ρ
  have h := prT_simulateQ_le_add_trace a b bad agree P pure []
  simp only [bind_pure,prT_bind_pure] at h
  have project (c : (t : ι) → sp.Range t) :
      Pr{let z ← (simulateQ (trImpl c) P).run []}[z.1 = true] = prT (simulateQ (ansImpl c) P) := by
    unfold prT
    rw [← fst_map_run_stImpl c (fun i l => l ++ [i]) P ([] : List ι), prEvent_map]
  exact (project a).le.trans (h.trans_eq (congrArg (· + _) (project b).symm))

end Reduction.ShakeXof
#print axioms Reduction.ShakeXof.freeze_classical_reads
