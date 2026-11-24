import Integration.SlhDsaShakePermutationPortMatrix

/-! The conventional bitwise-XOR response oracle for both directions of the
ideal 1600-bit permutation. Only the local response copy uses bitwise XOR.
The mask lookups, round evaluation, and coherent uncomputation are shared
with the additive-response port. -/
namespace Reduction.ShakePermutation.RoundPort
open Classical Quantum Matrix

def wordXor (v w : Words) : Words := fun i => v i ^^^ w i

@[simp] theorem wordXor_cancel (v w : Words) : wordXor (wordXor v w) w = v := by
  funext i
  simp [wordXor,UInt64.xor_assoc]

def xorAnswer : Equiv.Perm Work :=
  Function.Involutive.toPerm (fun s => (s.1, wordXor s.2.1 s.2.2, s.2.2)) (by
    intro s
    simp)

noncomputable def xorPort (π : Permutation) : Program Work :=
  .seq (.localOp seed) (.seq (round π) (.seq (.localOp xorAnswer)
    (.seq (round π).reverse (.localOp seed.symm))))

theorem xorPort_cost (π : Permutation) :
    (xorPort π).count true = 8 ∧ (xorPort π).count false = 8 := publicPort_cost π

theorem xorPort_clean (π : Permutation) (ki ko : Mask) (h : RateMask) (a : Port) (y : Words) :
    (xorPort π).run (bank ki ko) h (clean a y 0) =
      clean a (wordXor y (oracle (salted ki ko h π) a)) 0 := by
  rcases a with ⟨d,v⟩
  let f := oracle (salted ki ko h π) (d,v)
  have hp := round_clean π ki ko h d v y v
  have hrev := (Equiv.symm_apply_eq (e := (round π).run (bank ki ko) h)).mpr
    (round_clean π ki ko h d v (wordXor y f) v).symm
  change (.localOp seed.symm : Program Work).run (bank ki ko) h ((round π).reverse.run (bank ki ko) h
    ((.localOp xorAnswer : Program Work).run (bank ki ko) h ((round π).run (bank ki ko) h (clean (d,v) y (0+v))))) = _
  rw [zero_add,hp,Program.reverse_run]
  change (.localOp seed.symm : Program Work).run (bank ki ko) h
    (((round π).run (bank ki ko) h).symm (clean (d,v) (wordXor y f) f)) = _
  rw [hrev]
  simp [Program.run,clean,seed,f]

def xorOracleEquiv (π : Permutation) : Equiv.Perm (Port × Words) :=
  Function.Involutive.toPerm (fun s => (s.1, wordXor s.2 (oracle π s.1))) (by
    intro s
    simp)

noncomputable def xorCompiled (π : Permutation) (ki ko : Mask) (h : RateMask) (E : Type) :
    Equiv.Perm (Reg Work × E) := ((xorPort π).run (bank ki ko) h).prodCongr (Equiv.refl E)

def xorActual (π : Permutation) (E : Type) :=
  (xorOracleEquiv π).prodCongr (Equiv.refl E)

theorem xor_basis (π : Permutation) (ki ko : Mask) (h : RateMask) (E : Type) :
    (xorCompiled π ki ko h E) ∘ embed E = embed E ∘ xorActual (salted ki ko h π) E := by
  funext s
  rcases s with ⟨⟨a,y⟩,z⟩
  exact congrArg (fun w => (w,z)) (xorPort_clean π ki ko h a y)

theorem xor_channel (π : Permutation) (ki ko : Mask) (h : RateMask) (E : Type)
    [Fintype E] [DecidableEq E] (ρ : Matrix ((Port × Words) × E) ((Port × Words) × E) ℂ) :
    MatrixMap.conj (basisMatrix (xorCompiled π ki ko h E)) (MatrixMap.conj (basisMatrix (embed E)) ρ) =
      MatrixMap.conj (basisMatrix (embed E)) (MatrixMap.conj (basisMatrix (xorActual (salted ki ko h π) E)) ρ) := by
  have matrix_eq : basisMatrix (xorCompiled π ki ko h E) * basisMatrix (embed E) =
      basisMatrix (embed E) * basisMatrix (xorActual (salted ki ko h π) E) := by
    rw [← basisMatrix_comp,← basisMatrix_comp,xor_basis]
  simpa only [MatrixMap.conj_mul, LinearMap.comp_apply] using
    congrArg (fun m => MatrixMap.conj m ρ) matrix_eq

end Reduction.ShakePermutation.RoundPort
#print axioms Reduction.ShakePermutation.RoundPort.xor_channel
#print axioms Reduction.ShakePermutation.RoundPort.xorPort_cost
