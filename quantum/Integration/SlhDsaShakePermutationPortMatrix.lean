import Integration.SlhDsaShakePermutationPort

/-! Exact action of the compiled reversible circuit on the designated ideal
permutation query register, with arbitrary entangled spectator registers.
The clean auxiliaries are returned in their original state on every query. -/
namespace Reduction.ShakePermutation.RoundPort
open Classical Quantum Matrix

def embed (E : Type) : (Port × Words) × E → Reg Work × E :=
  fun s => (clean s.1.1 s.1.2 0,s.2)

theorem embed_injective (E : Type) : Function.Injective (embed E) := by
  intro s t he
  exact congrArg (fun w : Reg Work × E => ((w.1.2.2.1,w.1.2.2.2.1),w.2)) he

def actual (π : Permutation) (ki ko : Mask) (h : RateMask) (E : Type) :
    Equiv.Perm ((Port × Words) × E) :=
  (oracleEquiv (oracle (salted ki ko h π))).prodCongr (Equiv.refl E)

noncomputable def compiled (π : Permutation) (ki ko : Mask) (h : RateMask) (E : Type) :
    Equiv.Perm (Reg Work × E) :=
  ((publicPort π).run (bank ki ko) h).prodCongr (Equiv.refl E)

theorem port_on_basis (π : Permutation) (ki ko : Mask) (h : RateMask) (E : Type) :
    (compiled π ki ko h E) ∘ embed E = embed E ∘ actual π ki ko h E := by
  funext s
  rcases s with ⟨⟨a,y⟩,z⟩
  exact congrArg (fun w => (w,z)) (publicPort_clean π ki ko h a y)

theorem matrix_intertwines (π : Permutation) (ki ko : Mask) (h : RateMask)
    (E : Type) [Fintype E] [DecidableEq E] :
    basisMatrix (compiled π ki ko h E) * basisMatrix (embed E) =
      basisMatrix (embed E) * basisMatrix (actual π ki ko h E) := by
  rw [← basisMatrix_comp,← basisMatrix_comp,port_on_basis]

private theorem conj_move {A B : Type} [Fintype A] [Fintype B]
    (u : Matrix A A ℂ) (v : Matrix B B ℂ) (e : Matrix B A ℂ) (ρ : Matrix A A ℂ)
    (he : v*e = e*u) :
    MatrixMap.conj v (MatrixMap.conj e ρ) = MatrixMap.conj e (MatrixMap.conj u ρ) := by
  simp only [MatrixMap.conj_apply]
  calc
    _ = (v*e)*ρ*(v*e)ᴴ := by rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = (e*u)*ρ*(e*u)ᴴ := by rw [he]
    _ = _ := by rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]

/-- The same channel as the forger's public port, even with a mixed input
entangled with other registers. The two sides include the clean embedding. -/
theorem port_on_density (π : Permutation) (ki ko : Mask) (h : RateMask)
    (E : Type) [Fintype E] [DecidableEq E] (ρ : Matrix ((Port × Words) × E) ((Port × Words) × E) ℂ) :
    MatrixMap.conj (basisMatrix (compiled π ki ko h E)) (MatrixMap.conj (basisMatrix (embed E)) ρ) =
      MatrixMap.conj (basisMatrix (embed E)) (MatrixMap.conj (basisMatrix (actual π ki ko h E)) ρ) :=
  conj_move _ _ _ ρ (matrix_intertwines π ki ko h E)

end Reduction.ShakePermutation.RoundPort
#print axioms Reduction.ShakePermutation.RoundPort.port_on_density
