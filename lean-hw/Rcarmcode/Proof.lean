import Rcarmcode.Registers
import Armstream.Proof

namespace slhdsa.RcArmCode
open Spec.SHA256 Aeneas Aeneas.Std

attribute [local irreducible] kcompress linux apple Arm.ADD Arm.SHA256H Arm.SHA256H2
  Arm.SHA256SU0 Arm.SHA256SU1
set_option maxHeartbeats 80000

def writeState (p : Arm.V × Arm.V) : List Word := vwords p.1 ++ vwords p.2

theorem writeState_size (p : Arm.V × Arm.V) : (writeState p).length = 8 := rfl

/-- The two state-register loads, four reversed message vectors, and final paired store. -/
def block (onApple : Bool) (st : List Word) (input : Array U8 64#usize) : List Word :=
  let body := if onApple then apple appleConstants else linux linuxConstants
  let b := bytes input.val
  writeState (body (vOf st 0) (vOf st 4) (beV b 0) (beV b 16) (beV b 32) (beV b 48))

theorem block_size (onApple : Bool) (st : List Word) (b : Array U8 64#usize) :
    (block onApple st b).length = 8 :=
  writeState_size _

theorem block_is_fips (onApple : Bool) (st : List Word) (size : st.length = 8)
    (input : Array U8 64#usize) :
    block onApple st input = compress st (bytes input.val) := by
  have spec := kcompress_eq st size (bytes input.val) (by simp)
  cases onApple
  · change writeState (linux linuxConstants (vOf st 0) (vOf st 4) (beV (bytes input.val) 0) (beV (bytes input.val) 16) (beV (bytes input.val) 32) (beV (bytes input.val) 48)) = _
    rw [linux_registers]
    exact spec
  · change writeState (apple appleConstants (vOf st 0) (vOf st 4) (beV (bytes input.val) 0) (beV (bytes input.val) 16) (beV (bytes input.val) 32) (beV (bytes input.val) 48)) = _
    rw [apple_registers]
    exact spec

attribute [local irreducible] block

/-- The object-size precondition on a Rust slice ensures that adding 64 bytes
per iteration reaches the end pointer exactly after the last block. -/
def execute (onApple : Bool) (st : List Word) (blocks : List (Array U8 64#usize)) : List Word :=
  blocks.foldl (block onApple) st

private theorem fold_agrees {A B : Type} (f g : A → B → A) (valid : A → Prop)
    (step : ∀ a b, valid a → f a b = g a b) (keep : ∀ a b, valid (f a b)) :
    ∀ (bs : List B) (x : A), valid x → bs.foldl f x = bs.foldl g x := by
  intro bs
  induction bs with
  | nil => intros; rfl
  | cons b bs ih =>
    intro x hx
    exact (ih (f x b) (keep x b)).trans (congrArg (List.foldl g · bs) (step x b hx))

theorem execute_is_fips (onApple : Bool) (blocks : List (Array U8 64#usize))
    (st : List Word) (size : st.length = 8) :
    execute onApple st blocks = X86.Stream.fold256 st blocks :=
  @fold_agrees (List Word) (Array U8 64#usize) (block onApple)
    (fun a b => compress a (bytes b.val)) (fun a => a.length = 8)
    (fun a b ha => block_is_fips onApple a ha b) (block_size onApple) blocks st size

attribute [local irreducible] execute X86.Stream.fold256

/-- The exact compression contract used by the extracted streaming and padding
driver has the same result words as either release hardware implementation. -/
theorem armstream_contract (onApple : Bool) (state : Array U32 8#usize)
    (blocks : Slice (Array U8 64#usize)) :
    ArmStreamRust.sha2.sha256.compress256 state blocks ⦃ out =>
      wv out.val = execute onApple (wv state.val) blocks.val ⦄ := by
  apply WP.spec_mono (slhdsa.PlatformStream.bulk256 state blocks)
  intro _ h
  exact h.trans (execute_is_fips onApple blocks.val (wv state.val) (by simp)).symm

end slhdsa.RcArmCode
