import Shakebatch.ForsSign
import Shakebatch.SigBytes
open Aeneas Aeneas.Std Result
namespace slhdsa.ShakeBatch
set_option linter.concreteInstances false
variable [machine : Machine]

/-- FORS signature generation serializes each secret and each authentication sibling in FIPS order. -/
theorem sign_fors_trees {N : Usize} (p : slhdsa.params.Params) (hp : PN p N)
    (sk seed : Array U8 N) (a : address.Adrs) (choices : Slice U32) (permutes : PermutationCorrect)
    (enabled : 0 < machine.width.val) (count : choices.length=p.k.val)
    (index : ∀ t < choices.length, choices.val[t]!.val < 2^p.a.val) :
    shake.fors_batch.sign p choices sk seed a ⦃ out =>
      bytes out.val = (List.range p.k.val).flatMap
        (forsSignTree (Shake.params p) (bytes sk.val) (bytes seed.val) (adrsS a) (nats choices.val)) ∧
      out.length=p.k.val*(1+p.a.val)*N.val ⦄ := by
  apply WP.spec_mono (sign_prefix p hp sk seed a choices permutes enabled count index)
  intro out h
  refine ⟨prefix_bytes p hp sk seed a choices out count h,?_⟩
  rw [h.1,count,Nat.mul_assoc,Nat.add_comm]
end slhdsa.ShakeBatch
