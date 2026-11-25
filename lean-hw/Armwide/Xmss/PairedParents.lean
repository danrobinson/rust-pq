import Armwide.Xmss.Parents
import Paired.Multi
import Slhdsa.Proofs.Util

open Aeneas Aeneas.Std Result
namespace slhdsa.ArmXmss
open H512.Multi

def old {N : Usize} (roots : Nodes N) (i : Nat) := bytes roots.val[i]!.val

/-- Byte-level output of the selected native kernel. A negative feature probe
leaves the whole pass to the scalar implementation. -/
def pairResult {N : Usize} (enabled : Bool) (seed : hash.Seed N) (a : address.Adrs)
    (first : U32) (roots : Nodes N) (count : Usize) :=
  if enabled then parentsBatch N.val (S512.wv seed.state512.val) (adrsS a) first.val count.val (old roots)
  else (0,old roots)

/-- Compose the physical paired-prefix semantics and the extracted scalar suffix.
Input bytes in the gap between processed outputs and unread children can be arbitrary. -/
theorem paired_then_remainder {N} (p : params.Params) (hp : PN p N) (seed : hash.Seed N)
    (hs : SeedOk seed) (wide : N.val=24 ∨ N.val=32) (enabled : Bool) (a : address.Adrs)
    (first : U32) (roots current : Nodes N) (count done : Usize) (size : count.val ≤ 8)
    (room : first.val+count.val ≤ 2^32)
    (returned : done.val=(pairResult enabled seed a first roots count).1)
    (stored : ∀ i < 16, (i < done.val ∨ 2*done.val ≤ i) → bytes current.val[i]!.val=(pairResult enabled seed a first roots count).2 i) :
    xmss.arm.batch_root_512_loop0_loop0 ⟨done,count⟩ seed.pk_seed seed.state seed.state512
      current a first ⦃ out => ∀ j < count.val, bytes out.val[j]!.val=parent p seed a first roots j ⦄ := by
  have width : (paramsS p).n=N.val := congrArg UScalar.val hp.n_eq
  have seedLength : (bytes seed.pk_seed.val).length=(paramsS p).n := by rw [width]; simp
  cases enabled with
  | false =>
    have zero : done.val=0 := returned
    apply remainder p hp seed hs a first roots current done count (by omega) size room
    · intro j hj; omega
    · intro j _ hj
      exact Aeneas.Std.Array.ext _ _ ((bytes_inj _ _).mp (stored j hj (Or.inr (by omega))))
  | true =>
    have stateEq : S512.wv seed.state512.val=pkState512 N.val (bytes seed.pk_seed.val) := by
      rw [hs.2 (by omega)]
      simp [pkState512,slhdsa.toByte_zero]
    have vals := parents_batch_eq_fips (paramsS p) rfl (by rw [width]; exact wide)
      (bytes seed.pk_seed.val) seedLength (adrsS a) first.val count.val (old roots)
      (by intro i _; rw [width]; simp [old])
    simp only [pairResult,ite_true,stateEq] at returned stored
    simp only [width] at vals
    have countEq := returned.trans vals.1
    apply remainder p hp seed hs a first roots current done count (by omega) size room
    · intro j hj
      rw [stored j (by omega) (.inl hj)]
      exact vals.2.1 _ (by omega)
    · intro j hj endPos
      apply Aeneas.Std.Array.ext
      apply (bytes_inj _ _).mp
      rw [stored j endPos (.inr hj)]
      exact vals.2.2 _ (by omega)

end slhdsa.ArmXmss
