import Shakebatch.X86Feature
import Cachepath.NativeVerifierHosts
import Cachepath.NativeVerify.ForsRecovery
import Cachepath.NativeVerify.WotsDispatch

open Aeneas Aeneas.Std Result
namespace slhdsa.NativeVerify
open ShakeBatch
set_option linter.concreteInstances false
noncomputable section

def certified (m : Machine) (kernel : Active m) (on : Bool) (available : Usize → Result Bool)
    (selection : ∀ {N : Usize} (p : params.Params), PN p N → available N=ok on)
    (correct : on=true → ActiveCorrect m kernel) (positive : on=true → 0<m.width.val) :
    CacheopsRust.NativeVerifier.Recovery := by
  letI : Machine := m
  letI : Wots.Dispatch m := ⟨kernel⟩
  letI : Fors.ActiveKernel m := ⟨kernel⟩
  letI : Stream := scalarStream
  letI : StreamCorrect := scalarStreamCorrect
  exact {
    wots := Wots.dispatch available
    fors := Fors.dispatched available
    wots_spec := fun p hp sig msg seed a len domain =>
      Wots.dispatch_spec available p hp sig msg seed a len domain on (selection p hp) correct positive
    fors_spec := fun p hp sig md seed a len hmd domain =>
      Fors.dispatched_fips available p hp sig md seed a domain len hmd on (selection p hp) correct positive
  }

def appleRecovery (sha3 : Bool) := certified (AppleHybrid.machine sha3) (appleActive sha3) true (ShakeBatch.shake.batch.available (ok true))
  (fun p hp=>available_for_fips _ p hp) (fun _=>apple sha3) (fun _=>by change 0<8;decide)

def linuxRecovery := certified Kldisp.machine (fullActive Kldisp.machine KldispRust.shake256.parallel.available)
  true (ShakeBatch.shake.batch.available KldispRust.shake256.parallel.available) (fun p hp=>available_for_fips _ p hp) (fun _=>linux) (fun _=>by decide)

def x86Recovery := certified Kxdispatch.machine (fullActive Kxdispatch.machine KxdispatchRust.shake256.parallel.available)
  GatherRust.avx512Available X86.available (fun p hp=>X86.available_spec p hp) x86 (fun _=>by decide)

end
end slhdsa.NativeVerify
