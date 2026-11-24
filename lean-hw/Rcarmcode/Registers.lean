import Rcarmcode.Code
import Slhdsa.Proofs.Hw.Rounds

namespace slhdsa.RcArmCode

open Spec.SHA256 Aeneas Aeneas.Std

theorem linux_constants : linuxConstants = K := by decide
theorem apple_constants : appleConstants = K := by decide

attribute [local irreducible] Arm.SHA256H Arm.SHA256H2 Arm.SHA256SU0 Arm.SHA256SU1 Arm.ADD

def reference (abcd efgh m0 m1 m2 m3 : Arm.V) : Arm.V × Arm.V :=
  let state := kcompress abcd efgh m0 m1 m2 m3
  (Arm.ADD state.abcd abcd, Arm.ADD state.efgh efgh)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem linux_registers (a e m0 m1 m2 m3 : Arm.V) :
    linux linuxConstants a e m0 m1 m2 m3 = reference a e m0 m1 m2 m3 := by
  rw [linux_constants]
  rfl

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem apple_registers (a e m0 m1 m2 m3 : Arm.V) :
    apple appleConstants a e m0 m1 m2 m3 = reference a e m0 m1 m2 m3 := by
  rw [apple_constants]
  rfl

end slhdsa.RcArmCode
