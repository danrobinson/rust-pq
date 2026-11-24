import Integration.SlhDsaIdealCipherWork
import Ideal.Core.HPBasic
import VCVio.OracleComp.EvalDist.Sum

namespace Reduction.IdealCipher
open PQ.QROM PQ.Interactive ENNReal OracleComp OracleSpec Ideal.HP
variable {K B : Type} [Fintype K] [Nonempty K] [DecidableEq K] [Fintype B] [Nonempty B] [DecidableEq B]

abbrev ClassicalPlayer (K B : Type) := OracleComp (unifSpec + ((K × Bool × B) →ₒ B)) K

noncomputable def classicalWin (P : K → Equiv.Perm B) (k : K) (x : ClassicalPlayer K B) : ℝ≥0∞ :=
  Pr{let guessed ← simulateQ (ansImpl (spec := (K × Bool × B) →ₒ B) (cipherPort P)) x}[guessed = k]

omit [Nonempty K] in
private theorem singleton_average (key : K) :
    avg (fun k : K => if key = k then (1:ℝ≥0∞) else 0) = (Fintype.card K : ℝ≥0∞)⁻¹ := by
  unfold avg
  simp [mul_ite]

omit [Nonempty K] [Fintype B] [Nonempty B] [DecidableEq B] in
/-- In the row-replacement game, an oracle query can change the continuation
only for the one key named in that query. An unqueried key can still be guessed. -/
private theorem find_row (P : K → Equiv.Perm B) (J : Equiv.Perm B) (x : ClassicalPlayer K B)
    (q : ℕ) (cost : CountBound (fun i => i.isRight = true) x q) :
    avg (fun k => classicalWin (Function.update P k J) k x) ≤ (q+1:ℝ≥0∞) / Fintype.card K := by
  induction x using OracleComp.inductionOn generalizing q with
  | pure z =>
    simp only [classicalWin,simulateQ_pure,prEvent_pure,singleton_average]
    rw [div_eq_mul_inv]
    exact le_of_eq_of_le (one_mul _).symm (mul_le_mul' le_add_self le_rfl)
  | query_bind v f ih =>
    rw [countBound_query_bind] at cost
    rcases v with n|z
    · simp only [Sum.isRight_inl,Bool.false_eq_true,ite_false] at cost
      have uniform (k : K) :
          classicalWin (Function.update P k J) k (liftM ((unifSpec + ((K × Bool × B) →ₒ B)).query (.inl n)) >>= f : OracleComp (unifSpec + ((K × Bool × B) →ₒ B)) K) =
            avg (fun r : Fin (n+1) => classicalWin (Function.update P k J) k (f r)) := by
        unfold classicalWin
        rw [simulateQ_ansImpl_inl_bind,prEvent_bind_eq_tsum,tsum_fintype]
        apply Finset.sum_congr rfl
        intro r _
        apply congrArg (· * _)
        change Pr{let i ← ProbComp.uniformFin n}[i = r] = _
        rw [ProbComp.prEvent_uniformFin]
        have singleton : (Finset.univ.filter (fun i : Fin (n+1) => i = r)) = {r} := by ext; simp
        rw [singleton]
        simp
      simp_rw [uniform]
      rw [avg_comm]
      exact avg_le fun r => ih r q (cost r)
    · simp only [Sum.isRight_inr,ite_true] at cost
      obtain ⟨positive,rest⟩ := cost
      cases q with
      | zero => omega
      | succ q =>
        let next := f (cipherPort P z)
        have step (k : K) :
            classicalWin (Function.update P k J) k (liftM ((unifSpec + ((K × Bool × B) →ₒ B)).query (.inr z)) >>= f : OracleComp (unifSpec + ((K × Bool × B) →ₒ B)) K) ≤
            (if z.1 = k then (1:ℝ≥0∞) else 0) + classicalWin (Function.update P k J) k next := by
          by_cases hit : z.1 = k
          · simp only [ite_eq_left hit]
            exact (prEvent_le_one _).trans le_self_add
          · simp only [ite_eq_right hit,zero_add,classicalWin,simulateQ_ansImpl_inr_bind]
            simp only [cipherPort,Function.update_of_ne hit,next]
            exact le_rfl
        apply (avg_mono step).trans
        rw [avg_add,singleton_average]
        apply (add_le_add le_rfl (ih (cipherPort P z) q (rest _))).trans_eq
        push_cast
        rw [div_eq_mul_inv,div_eq_mul_inv]
        ring

omit [Nonempty K] [Nonempty B] in
/-- Classical recovery of the actual uniform key, given its entire permutation.
Each classical encryption or decryption query uses one unit of the path budget.
All local computation and sampling between queries are unrestricted. -/
theorem classical_key_recovery (x : Equiv.Perm B → ClassicalPlayer K B) (q : ℕ)
    (cost : ∀ J, CountBound (fun i => i.isRight = true) (x J) q) :
    avg (fun k : K => avg fun P : K → Equiv.Perm B => classicalWin P k (x (P k))) ≤
      (q+1:ℝ≥0∞)/Fintype.card K := by
  have replace (k : K) : avg (fun P => classicalWin P k (x (P k))) =
      avg (fun P => avg fun J => classicalWin (Function.update P k J) k (x J)) := by
    rw [replace_row k (fun P => classicalWin P k (x (P k)))]
    simp
  simp_rw [replace]
  rw [avg_comm]
  apply avg_le
  intro P
  rw [avg_comm]
  exact avg_le fun J => find_row P J (x J) q (cost J)

omit [Nonempty B] in
/-- A successful classical key recovery with probability at least one half
requires enough trial keys and one final guess to cover half the key space. -/
theorem classical_half_work (x : Equiv.Perm B → ClassicalPlayer K B) (q : ℕ)
    (cost : ∀ J, CountBound (fun i => i.isRight = true) (x J) q)
    (success : 1/2 ≤ avg (fun k : K => avg fun P : K → Equiv.Perm B => classicalWin P k (x (P k)))) :
    Fintype.card K ≤ 2*(q+1) := by
  have h := success.trans (classical_key_recovery x q cost)
  have hr := (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mpr h
  simp (disch := finiteness) only [ENNReal.toReal_div,ENNReal.toReal_one,ENNReal.toReal_ofNat,
    ENNReal.toReal_add,ENNReal.toReal_natCast] at hr
  rw [le_div_iff₀ (by positivity)] at hr
  exact_mod_cast (show (Fintype.card K : ℝ) ≤ 2*((q:ℝ)+1) by linarith)

end Reduction.IdealCipher
#print axioms Reduction.IdealCipher.classical_key_recovery
#print axioms Reduction.IdealCipher.classical_half_work
