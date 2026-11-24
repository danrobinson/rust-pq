import Shakebatch.Sign
open Aeneas Aeneas.Std Result
namespace slhdsa.ShakeBatch

section
variable (hardware : Result Bool)

def shake.batch.available (N : Std.Usize) : Result Bool := do
  let b ←
    match N.val with
    | 16 => ok true
    | 24 => ok true
    | 32 => ok true
    | _ => ok false
  if b
  then hardware
  else ok false

theorem available_for_fips {N : Usize} (p : slhdsa.params.Params) (hp : PN p N) :
    shake.batch.available hardware N = hardware := by
  rcases hp.nok with h|h|h <;> simp [shake.batch.available,h]

end
end slhdsa.ShakeBatch
