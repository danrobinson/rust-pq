import Platform.Compress512
import Slhdsa.Proofs.Hw.Rounds
import Slhdsa.Proofs.Hw512.Rounds

open Aeneas Aeneas.Std Result

namespace slhdsa.X86
open Spec.SHA256

def stateWords (state : State) : List Word :=
  let (a,b,c,d,e,f,g,h) := state
  [a,b,c,d,e,f,g,h]

private theorem finish (iv : State) (block : Spec.Bytes) :
    stateWords (feedForward iv ((List.range 64).foldl (round (schedule block)) iv)) =
      Spec.SHA256.compress (stateWords iv) block := by
  rcases iv with ⟨a,b,c,d,e,f,g,h⟩
  unfold Spec.SHA256.compress
  simp only [stateWords, List.getElem!_cons_zero, List.getElem!_cons_succ]
  generalize (List.range _).foldl (round (schedule block)) (a,b,c,d,e,f,g,h) = work
  rcases work with ⟨u,v,w,x,y,z,r,s⟩
  rfl

/-- Each lane returns the FIPS 180-4 block compression of its own message and chaining state. -/
theorem compress_block_spec (iv state : Array Reg 8#usize) (w : Array Reg 16#usize)
    (blocks : Fin 16 → Spec.Bytes)
    (hs : Trace state (fun j => schedule (blocks j)) (laneState iv) 4)
    (words : ∀ k, k < 16 → ∀ j, w.val[k]! j = word (blocks j) (4 * k)) :
    PlatformRust.sha256.x86.avx512.compress iv state w ⦃ out => ∀ j,
      stateWords (laneState out j) = Spec.SHA256.compress (stateWords (laneState iv j)) (blocks j) ⦄ := by
  have hr : Ring w (fun j => schedule (blocks j)) 4 := by
    intro k _ hi j
    have hk : k < 16 := by simpa using hi
    rw [Nat.mod_eq_of_lt hk, words k hk, slhdsa.schedule_lt16 _ _ hk]
  apply WP.spec_mono (compress_spec iv state w _ hr hs (fun k lo hi j => slhdsa.schedule_rec _ k lo hi))
  intro out h j
  rw [h j, finish]

#print axioms compress_block_spec
end slhdsa.X86

namespace slhdsa.X86.S512
open Spec.SHA512

def stateWords (state : State) : List Word :=
  let (a,b,c,d,e,f,g,h) := state
  [a,b,c,d,e,f,g,h]

private theorem finish (iv : State) (block : Spec.Bytes) :
    stateWords (feedForward iv ((List.range 80).foldl (round (schedule block)) iv)) =
      Spec.SHA512.compress (stateWords iv) block := by
  rcases iv with ⟨a,b,c,d,e,f,g,h⟩
  unfold Spec.SHA512.compress
  simp only [stateWords, List.getElem!_cons_zero, List.getElem!_cons_succ]
  generalize (List.range _).foldl (round (schedule block)) (a,b,c,d,e,f,g,h) = work
  rcases work with ⟨u,v,w,x,y,z,r,s⟩
  rfl

/-- Each lane returns the FIPS 180-4 block compression of its own message and chaining state. -/
theorem compress_block_spec (iv : Array Reg 8#usize) (w : Array Reg 16#usize)
    (blocks : Fin 8 → Spec.Bytes)
    (words : ∀ k, k < 16 → ∀ j, word64 w.val[k]! j = word (blocks j) (8 * k)) :
    PlatformRust.sha512.x86.compress iv w ⦃ out => ∀ j,
      stateWords (laneState out j) = Spec.SHA512.compress (stateWords (laneState iv j)) (blocks j) ⦄ := by
  have hr : Ring w (fun j => schedule (blocks j)) 0 := by
    intro k _ hi j
    have hk : k < 16 := by simpa using hi
    rw [Nat.mod_eq_of_lt hk, words k hk, slhdsa.H512.schedule_lt16 _ _ hk]
  apply WP.spec_mono (compress_spec iv w _ hr (fun k lo hi j => slhdsa.H512.schedule_rec _ k lo hi))
  intro out h j
  rw [h j, finish]

#print axioms compress_block_spec
end slhdsa.X86.S512
