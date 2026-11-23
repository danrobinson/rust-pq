import Rcarmcode.Registers512
import Armstream.Proof
import Rcarmcode.Loop

namespace slhdsa.RcArmCode.S512

open Spec.SHA512 Aeneas Aeneas.Std slhdsa.H512

attribute [local irreducible] H512.kcompress linux apple Arm.ADD2 Arm.EXT1 Arm.SHA512H
  Arm.SHA512H2 Arm.SHA512SU0 Arm.SHA512SU1

def writeState (p : Arm.V2 × Arm.V2 × Arm.V2 × Arm.V2) : List Word :=
  vwords2 p.1 ++ vwords2 p.2.1 ++ (vwords2 p.2.2.1 ++ vwords2 p.2.2.2)

/-- The four initial state registers and eight reversed input vectors loaded by the routine. -/
def block (onApple : Bool) (st : List Word) (input : Array U8 128#usize) : List Word :=
  let body := if onApple then apple (fun _ => Arm.ADD2) appleConstants
              else linux (fun _ => Arm.ADD2) linuxConstants
  let b := bytes input.val
  writeState (body (vOf2 st 0) (vOf2 st 2) (vOf2 st 4) (vOf2 st 6)
    (beV2 b 0) (beV2 b 16) (beV2 b 32) (beV2 b 48)
    (beV2 b 64) (beV2 b 80) (beV2 b 96) (beV2 b 112))

theorem block_is_fips (onApple : Bool) (st : List Word) (input : Array U8 128#usize) :
    block onApple st input = Spec.SHA512.compress st (bytes input.val) := by
  cases onApple
  · change writeState (linux (fun _ => Arm.ADD2) linuxConstants (vOf2 st 0) (vOf2 st 2)
      (vOf2 st 4) (vOf2 st 6) (beV2 (bytes input.val) 0) (beV2 (bytes input.val) 16) (beV2 (bytes input.val) 32) (beV2 (bytes input.val) 48)
      (beV2 (bytes input.val) 64) (beV2 (bytes input.val) 80) (beV2 (bytes input.val) 96) (beV2 (bytes input.val) 112)) = _
    rw [linux_registers]
    exact H512.kcompress_eq st (bytes input.val)
  · change writeState (apple (fun _ => Arm.ADD2) appleConstants (vOf2 st 0) (vOf2 st 2)
      (vOf2 st 4) (vOf2 st 6) (beV2 (bytes input.val) 0) (beV2 (bytes input.val) 16) (beV2 (bytes input.val) 32) (beV2 (bytes input.val) 48)
      (beV2 (bytes input.val) 64) (beV2 (bytes input.val) 80) (beV2 (bytes input.val) 96) (beV2 (bytes input.val) 112)) = _
    rw [apple_registers]
    exact H512.kcompress_eq st (bytes input.val)

attribute [local irreducible] block

def execute (onApple : Bool) (st : List Word) (blocks : List (Array U8 128#usize)) : List Word :=
  blocks.foldl (block onApple) st

theorem execute_is_fips (onApple : Bool) (blocks : List (Array U8 128#usize)) (st : List Word) :
    execute onApple st blocks = X86.Stream.fold512 st blocks :=
  congrArg (fun f => blocks.foldl f st) (funext fun a => funext fun b => block_is_fips onApple a b)

attribute [local irreducible] execute X86.Stream.fold512

theorem armstream_contract (onApple : Bool) (state : Array U64 8#usize)
    (blocks : Slice (Array U8 128#usize)) :
    ArmStreamRust.sha2.sha512.compress512 state blocks ⦃ out =>
      slhdsa.S512.wv out.val = execute onApple (slhdsa.S512.wv state.val) blocks.val ⦄ := by
  apply WP.spec_mono (slhdsa.PlatformStream.bulk512 state blocks)
  intro _ h
  exact h.trans (execute_is_fips onApple blocks.val (slhdsa.S512.wv state.val)).symm

end slhdsa.RcArmCode.S512
