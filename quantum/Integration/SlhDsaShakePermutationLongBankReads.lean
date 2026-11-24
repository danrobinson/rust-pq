import Integration.SlhDsaShakePermutationLongBankRecord
import Integration.SlhDsaShakePermutationLongSelectGoals
import Integration.SlhDsaShakePermutationItsrWitness

namespace Reduction.ShakePermutation.Long.BankRun
open Classical ItsrLabel SparsePort MLink SLHDSA OracleSpec OracleComp PQ.Interactive ENNReal SetOracle Tails
noncomputable section
set_option maxRecDepth 8192
variable {A T : Type}

def ask (i : Addr) : OracleComp Spec Words := liftM (Spec.query (.inr i))

def read (π : Permutation) (w : Words) : OracleComp Spec Words := do
  let a ← ask (ItsrLabel.mask false (rateOf w))
  let mid := (layout π).middle (rateOf w) (capOf w) (capOf a)
  let v ← ask (ItsrLabel.mask true mid.1)
  let z := (layout π).finish mid.2 (capOf v)
  let head ← ask (tailHead z)
  pure (join (rateXor mid.1 (rateOf head)) z)

def impl (π : Permutation) : QueryImpl (Phase.Tagged T) (OracleComp Spec)
  | .inl n => liftM (Spec.query (.inl n))
  | .inr (_,w) => read π w

theorem eval_impl (π : Permutation) (H : Table) (p : OracleComp (Phase.Tagged T) A) (f : A → ℝ≥0∞) :
    eval H f (simulateQ (impl π) p) = Phase.run (fun _ => perm π H) f p := by
  induction p using OracleComp.inductionOn with
  | pure z => rfl
  | query_bind i k ih =>
    simp only [simulateQ_bind,simulateQ_spec_query]
    rcases i with n|⟨d,w⟩
    · exact congrArg uniformMean (funext ih)
    · let a := H (ItsrLabel.mask false (rateOf w))
      let mid := (layout π).middle (rateOf w) (capOf w) (capOf a)
      let z := (layout π).finish mid.2 (capOf (H (ItsrLabel.mask true mid.1)))
      let v := join (rateXor mid.1 (rateOf (H (tailHead z)))) z
      have hv : perm π H w=v := by
        conv_lhs => rw [← join_split w]
        simp only [perm,salted,masked,Equiv.trans_apply,maskEquiv,shearEquiv,
          Function.Involutive.toPerm,Equiv.coe_fn_mk,mask_join_eq,shear,rate_mask,cap_mask_eq]
        rfl
      change eval H f (simulateQ (impl π) (k v)) = Phase.run _ f (k (perm π H w))
      rw [hv]; exact ih v

theorem impl_cost (π : Permutation) (p : OracleComp (Phase.Tagged T) A) (Q : ℕ)
    (h : CountBound (fun i => i.isRight = true) (simulateQ Phase.erase p) Q) :
    CountBound (fun i => i.isRight = true) (simulateQ (impl π) p) (3*Q) := by
  induction p using OracleComp.inductionOn generalizing Q with
  | pure => trivial
  | query_bind i k ih =>
    simp only [simulateQ_bind,simulateQ_spec_query] at h ⊢
    rcases i with n|⟨d,w⟩
    · exact fun r => ih r Q (h r)
    · have pos := h.1
      refine ⟨by omega,fun a => ⟨by omega,fun v => ⟨by omega,fun y => ?_⟩⟩⟩
      rw [show 3*Q-1-1-1 = 3*(Q-1) by omega]; exact ih _ _ (h.2 _)

def advance (π : Permutation) (H : Table) (D : Bank) (p : Report) (b : Rate) :=
  let r := rateXor b (rateOf (result p))
  let mid := (layout π).middle r p.cap (capOf (H (ItsrLabel.mask false r)))
  let z := (layout π).finish mid.2 (capOf (H (ItsrLabel.mask true mid.1)))
  write (write (write D H (ItsrLabel.mask false r)) H (ItsrLabel.mask true mid.1)) H (tailHead z)

theorem read_step (π : Permutation) (H : Table) (D : Bank) (p : Report) (b : Rate) (P : Words → Bank → Prop)
    (h : P (result (step π H p b)) (advance π H D p b)) :
    fixedAll H (read π (join (rateXor b (rateOf (result p))) (capOf (result p)))) D P := by
  unfold read; simp only [rate_join,cap_join,result] at *
  simp only [advance,step,push,result,cap_join,rate_join] at h
  kexact h

theorem advance_ext (π H D p b) (pin : Pins D H) : Ext D (advance π H D p b) :=
  ext_trans (write_ext pin _) (ext_trans (write_ext (write_pins pin _) _) (write_ext (write_pins (write_pins pin _) _) _))

theorem advance_pins (π H D p b) (pin : Pins D H) : Pins (advance π H D p b) H :=
  write_pins (write_pins (write_pins pin _) _) _

theorem advance_known (π H D p b) (pin : Pins D H) (old : Matches D p.log) :
    Matches (advance π H D p b) (step π H p b).log := by
  let r := rateXor b (rateOf (result p))
  let mid := (layout π).middle r p.cap (capOf (H (ItsrLabel.mask false r)))
  let z := (layout π).finish mid.2 (capOf (H (ItsrLabel.mask true mid.1)))
  intro i y eq
  simp only [step,push,List.mem_cons,Prod.mk.injEq] at eq
  rcases eq with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|prev
  · apply write_ext (write_pins (write_pins pin _) _) _
    apply write_ext (write_pins pin _) _; exact Function.update_self ..
  · apply write_ext (write_pins (write_pins pin _) _) _; exact Function.update_self ..
  · exact Function.update_self ..
  · exact advance_ext π H D p b pin _ _ (old i y prev)

theorem advance_origin (π H D p b) (z : Capacity) (v : Words) (m : advance π H D p b (tailHead z) = some v) :
    D (tailHead z)=some v ∨ z=(step π H p b).cap := by
  by_cases eq : z=(step π H p b).cap
  · exact Or.inr eq
  · apply Or.inl
    simp only [step,push] at eq
    unfold advance write at m
    rw [Function.update_of_ne (show tailHead z ≠ tailHead _ from fun he => eq (Sum.inr.inj he)),
      Function.update_of_ne (by simp [ItsrLabel.mask,tailHead]),Function.update_of_ne (by simp [ItsrLabel.mask,tailHead])] at m
    exact m
end
end Reduction.ShakePermutation.Long.BankRun
#print axioms Reduction.ShakePermutation.Long.BankRun.advance_known
