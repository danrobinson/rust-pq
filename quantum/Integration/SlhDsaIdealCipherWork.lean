import Integration.SlhDsaParallelRowWork
import Integration.SlhDsaSetPrf

/-! Black-box key recovery for the generic block-cipher reference problem.
The hidden key selects one row of a uniformly sampled family of permutations.
The player can use the entire hidden permutation as classical side information
and query encryption or decryption at arbitrary trial keys in entangled batches. -/

namespace Reduction.IdealCipher
open Quantum PQ.QROM ENNReal ParallelRowSearch
universe u v w

variable {K B : Type} [Fintype K] [DecidableEq K]
    [Fintype B] [DecidableEq B] [AddCommGroup B]
    {L : LocalSig.{u,v}} {W : QReg → Type w} {A : QReg} {lanes : ℕ}

/-- The forward and inverse ports access the same permutation at each key. -/
def cipherPort (P : K → Equiv.Perm B) (z : K × Bool × B) : B :=
  if z.2.1 then (P z.1).symm z.2.2 else P z.1 z.2.2

omit [AddCommGroup B] in
theorem replace_row (k : K) (f : (K → Equiv.Perm B) → ℝ≥0∞) :
    avg f = avg (fun P => avg fun J => f (Function.update P k J)) := by
  classical
  apply SetOracle.avg_resample (fun P J => Function.update P k J) (fun P => P k)
  rintro ⟨P,J⟩
  apply Prod.ext
  · funext b
    by_cases h : b = k <;> simp [h,Function.update]
  · simp

/-- The probability of recovering the actual hidden key in the ideal-cipher
model. Local operations are unrestricted. Depth counts oracle batches, and work counts every active query lane. -/
theorem key_recovery (I : L.Interp)
    (x : Equiv.Perm B → QuantumComp L (maskSpec lanes (K × Bool × B) B) W A)
    (ρ : Equiv.Perm B → SubState A) (guess : Equiv.Perm B → (Σ a, W a) → K)
    (d work : ℕ) (rounds : ∀ J, IsTotalBound (x J) d)
    (cost : ∀ J, IsWeightedBound (x J) Finset.card work) :
    avg (fun k : K => avg fun P : K → Equiv.Perm B =>
      leafProb (nRuntime (maskedTable (cipherPort P))) I (x (P k)) (joint (ρ (P k)))
        (fun z => guess (P k) z = k)) ≤
      (1+(4*(d:ℝ≥0∞)*work)^(2⁻¹:ℝ))^2 / Fintype.card K := by
  classical
  let win := fun (k : K) (P : K → Equiv.Perm B) (J : Equiv.Perm B) =>
    leafProb (nRuntime (maskedTable (cipherPort P))) I (x J) (joint (ρ J)) (fun z => guess J z = k)
  change avg (fun k => avg fun P => win k P (P k)) ≤ _
  have replace (k : K) : avg (fun P => win k P (P k)) =
      avg (fun P => avg fun J => win k (Function.update P k J) J) := by
    rw [replace_row k (fun P => win k P (P k))]
    simp
  simp_rw [replace]
  rw [avg_comm]
  apply avg_le
  intro P
  rw [avg_comm]
  apply avg_le
  intro J
  apply recover_row I (cipherPort P) Prod.fst (fun k => cipherPort (Function.update P k J))
    _ (x J) (ρ J) d work (rounds J) (cost J) (guess J)
  intro k z hz
  simp [cipherPort,Function.update_of_ne hz]

/-- For key spaces of size 2^(b+4), success at least one half requires
depth times total active queries at least 2^b. For the AES key widths the
exponents b are 124, 188 and 252. This measures ideal-cipher queries. -/
theorem half_work (I : L.Interp)
    (x : Equiv.Perm B → QuantumComp L (maskSpec lanes (K × Bool × B) B) W A)
    (ρ : Equiv.Perm B → SubState A) (guess : Equiv.Perm B → (Σ a, W a) → K)
    (d work b : ℕ) (keys : Fintype.card K = 2^(b+4))
    (rounds : ∀ J, IsTotalBound (x J) d) (cost : ∀ J, IsWeightedBound (x J) Finset.card work)
    (success : 1/2 ≤ avg (fun k : K => avg fun P : K → Equiv.Perm B =>
      leafProb (nRuntime (maskedTable (cipherPort P))) I (x (P k)) (joint (ρ (P k)))
        (fun z => guess (P k) z = k))) : 2^b ≤ d*work := by
  have h := success.trans (key_recovery I x ρ guess d work rounds cost)
  have cardPos : 0 < Fintype.card K := keys ▸ (by positivity : 0 < 2^(b+4))
  have sqrtFin : (4*(d:ℝ≥0∞)*work)^(2⁻¹:ℝ) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) (by finiteness)
  have realBound := (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mpr h
  simp (disch := finiteness) only [ENNReal.toReal_div,ENNReal.toReal_one,ENNReal.toReal_ofNat,ENNReal.toReal_natCast,
    ENNReal.toReal_pow,ENNReal.toReal_add,← ENNReal.toReal_rpow,
    ENNReal.toReal_mul,← one_div (2:ℝ),← Real.sqrt_eq_rpow] at realBound
  rw [le_div_iff₀ (by positivity)] at realBound
  let z := Real.sqrt (4*(d:ℝ)*work)
  have sq : z^2 = 4*(d:ℝ)*work := Real.sq_sqrt (by positivity)
  have natBound : Fintype.card K ≤ 4+16*(d*work) := by
    exact_mod_cast (show (Fintype.card K:ℝ) ≤ 4+16*((d:ℝ)*work) by
      change 1/2 * _ ≤ (1+z)^2 at realBound
      nlinarith [sq_nonneg (z-1)])
  rw [keys,pow_add] at natBound
  omega

end Reduction.IdealCipher
#print axioms Reduction.IdealCipher.key_recovery
#print axioms Reduction.IdealCipher.half_work
