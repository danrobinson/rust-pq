import Rcavx.Schedule
import Slhdsa.Proofs.Hw512.Rounds
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.RustCrypto512
open RcAvxRust
abbrev Words := List (BitVec 64)
def pair (W : Words) (g : Nat) : Lane := (W[2*g]!,W[2*g+1]!)
def weighted (W : Words) (g : Nat) := zip (· + ·) (pair W g) (pair Spec.SHA512.K g)
def window {α : Type} (p : Nat → α) (g : Nat) : Array α 8#usize :=
  Array.make 8#usize [p g,p (g+1),p (g+2),p (g+3),p (g+4),p (g+5),p (g+6),p (g+7)]
def Both (W V : Words) (g : Nat) : Wide := (pair W g,pair V g)
def Rec (W : Words) := ∀ k, 16≤k → k<80 → W[k]! =
  Spec.SHA512.ssig1 W[k-2]! + W[k-7]! + Spec.SHA512.ssig0 W[k-15]! + W[k-16]!

private theorem shuffle (a b c d : BitVec 64) : a+b+c+d=d+b+c+a := by
  have left (x y z : BitVec 64) : x+(y+z)=y+(x+z) := by
    rw [← BitVec.add_assoc,BitVec.add_comm x y,BitVec.add_assoc]
  simp only [BitVec.add_assoc,BitVec.add_comm,left]

theorem generated_next (W : Words) (g : Nat) (hg : g<32) (rec : Rec W) :
    generated (pair W g) (pair W (g+1)) (pair W (g+4)) (pair W (g+5)) (pair W (g+7)) = pair W (g+8) := by
  rw [generated_fips]
  simp only [pair,Prod.mk.injEq]
  constructor
  · rw [rec (2*(g+8)) (by omega) (by omega)]
    rw [show 2*(g+8)-2 = 2*(g+7) by omega,show 2*(g+8)-7 = 2*(g+4)+1 by omega,show 2*(g+8)-15 = 2*g+1 by omega,show 2*(g+8)-16 = 2*g by omega]
    exact shuffle _ _ _ _
  · rw [rec (2*(g+8)+1) (by omega) (by omega)]
    rw [show 2*(g+8)+1-2 = 2*(g+7)+1 by omega,show 2*(g+8)+1-7 = 2*(g+5) by omega,show 2*(g+8)+1-15 = 2*(g+1) by omega,show 2*(g+8)+1-16 = 2*g+1 by omega]
    exact shuffle _ _ _ _

theorem advance (W : Words) (g : Nat) (hg : g<32) (rec : Rec W) :
    sha512.x86_avx2.sha512_update_x_avx (window (pair W) g) (pair Spec.SHA512.K (g+8)) =
    ok (weighted W (g+8),window (pair W) (g+1)) := by
  unfold window weighted
  rw [update,generated_next W g hg rec]

theorem advance2 (W V : Words) (g : Nat) (hg : g<32) (rW : Rec W) (rV : Rec V) :
    sha512.x86_avx2.sha512_update_x_avx2 (window (Both W V) g) (pair Spec.SHA512.K (g+8),pair Spec.SHA512.K (g+8)) =
    ok ((weighted W (g+8),weighted V (g+8)),window (Both W V) (g+1)) := by
  unfold window weighted Both
  rw [update2]
  dsimp only
  rw [generated_next W g hg rW,generated_next V g hg rV]

theorem k_eq : roundConstants = Spec.SHA512.K := by rfl
end slhdsa.X86.RustCrypto512
