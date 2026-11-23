import Streamround.Proof
import Slhdsa.Proofs.Hw.Rounds
import Slhdsa.Proofs.Hw512.Rounds
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.Stream

/-- Before round t, the sixteen ring slots contain the initial sixteen words
or the sixteen preceding schedule words, according to the round number. -/
def window {n} (slots : Nat → BitVec n) (W : List (BitVec n)) (t : Nat) :=
  ∀ k, t-16 ≤ k → k < max 16 t → slots (k%16) = W[k]!

theorem unchanged_window {n} {slots : Nat → BitVec n} {W t} (old : window slots W t) (early : t < 16) :
    window slots W (t+1) ∧ slots (t%16)=W[t]! := by
  exact ⟨fun k lo hi => old k (by omega) (by omega),old t (by omega) (by omega)⟩

theorem updated_window {n} {slots next : Nat → BitVec n} {W t} (old : window slots W t) (late : 16 ≤ t)
    (write : ∀ k < 16, next k = if t%16=k then W[t]! else slots k) :
    window next W (t+1) ∧ next (t%16)=W[t]! := by
  have current := write (t%16) (by omega)
  simp only [ite_true] at current
  refine ⟨?_,current⟩
  intro k lo hi
  by_cases eq : t=k
  · subst k; exact current
  · rw [write _ (by omega),if_neg (by omega)]
    exact old k (by omega) (by omega)

private theorem expansion {n} {slots : Nat → BitVec n} {W t} (old : window slots W t) (late : 16 ≤ t)
    (s0 s1 : BitVec n → BitVec n)
    (rec : W[t]! = s1 W[t-2]! + W[t-7]! + s0 W[t-15]! + W[t-16]!) :
    slots (t%16) + slots ((t+9)%16) + s0 (slots ((t+1)%16)) + s1 (slots ((t+14)%16)) = W[t]! := by
  have prev (d : Nat) (hd : 0 < d) (lo : d ≤ 16) : slots ((t+(16-d))%16) = W[t-d]! := by
    rw [show (t+(16-d))%16=(t-d)%16 by omega]
    exact old _ (by omega) (by omega)
  have a := prev 16 (by decide) (by decide)
  have b := prev 7 (by decide) (by decide)
  have c := prev 15 (by decide) (by decide)
  have d := prev 2 (by decide) (by decide)
  simp only [Nat.reduceSub,Nat.add_zero] at a b c d
  rw [a,b,c,d,rec]; ac_rfl

theorem expansion256 (slots : Nat → BitVec 32) (block : Spec.Bytes) (t : Nat)
    (old : window slots (Spec.SHA256.schedule block) t) (late : 16 ≤ t) (bound : t < 64) :
    slots (t%16) + slots ((t+9)%16) + Spec.SHA256.ssig0 (slots ((t+1)%16)) +
      Spec.SHA256.ssig1 (slots ((t+14)%16)) = (Spec.SHA256.schedule block)[t]! :=
  expansion old late _ _ (slhdsa.schedule_rec block t late bound)

theorem expansion512 (slots : Nat → BitVec 64) (block : Spec.Bytes) (t : Nat)
    (old : window slots (Spec.SHA512.schedule block) t) (late : 16 ≤ t) (bound : t < 80) :
    slots (t%16) + slots ((t+9)%16) + Spec.SHA512.ssig0 (slots ((t+1)%16)) +
      Spec.SHA512.ssig1 (slots ((t+14)%16)) = (Spec.SHA512.schedule block)[t]! :=
  expansion old late _ _ (slhdsa.H512.schedule_rec block t late bound)

end slhdsa.X86.Stream
