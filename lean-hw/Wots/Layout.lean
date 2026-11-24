import Wots.Chain
import Chainwide.Layout
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.Wots
open Spec.SHA256

/-- Reconstruct the full 64-byte input to F, including the untouched padding. -/
theorem packed_layout (head initial tail : Spec.Bytes) (ws : List Word) (n t k : Nat)
    (hh : head.length=18) (hi : initial.length=n) (hw : ws.length=8)
    (shape : n=16 ∨ n=24 ∨ n=32) (small : t < 16) :
    packedWord (fun i => word (Chain.packet head 0 initial tail) (4*i)) (fun i => ws[i]!) n (BitVec.ofNat 32 t) k =
      word (Chain.packet head (BitVec.ofNat 32 t) ((ser ws).take n) tail) (4*k) := by
  let old := fun i => word (Chain.packet head 0 initial tail) (4*i)
  let ctr := BitVec.ofNat 32 t
  let addressed := Chain.addressWord old (old 4 &&& 0xffff0000) ctr
  have atWord (i : Nat) : addressed i = word (Chain.packet head ctr initial tail) (4*i) :=
    Chain.address_layout head (Spec.toByte 0 4) (initial ++ tail) ctr i hh (by simp [Spec.toByte])
  have orZero (x : Word) : x ||| (0 : Word) = x := by leaf_bits
  have clean : old 4 &&& 0xffff0000 = old 4 := by
    have eq := Chain.address_layout head (Spec.toByte 0 4) (initial ++ tail) 0 4 hh (by simp [Spec.toByte])
    change (old 4 &&& 0xffff0000) ||| ((0 : BitVec 32) >>> 16) = old 4 at eq
    rw [show ((0 : BitVec 32) >>> 16) = (0 : Word) by decide] at eq
    exact (orZero _).symm.trans eq
  have high : ctr >>> 16 = 0 := by
    dsimp [ctr]; interval_cases t <;> decide +kernel
  have pack : packedWord old (fun i => ws[i]!) n ctr k = Leaf.payloadWord addressed ws n k := by
    dsimp only [addressed]
    by_cases a : k=4
    · subst k
      simp (disch := omega) only [packedWord,Chain.valueWord,Leaf.payloadWord,Chain.addressWord,if_neg (by decide : 4 ≠ 5),
        if_neg (show 4 ≠ 5+n/4 by omega),if_neg (show ¬(6 ≤ 4 ∧ 4 < 5+n/4) by omega),if_pos rfl,high,orZero,clean,ite_true]
    by_cases b : k=5
    · subst k
      simp only [packedWord,Leaf.payloadWord,Chain.addressWord,↓reduceIte,show (5=4)=False by decide]
      generalize ws[0]! = x
      generalize old 5 = y
      leaf_bits
    simp (disch := omega) only [packedWord,Leaf.payloadWord,Chain.addressWord,Chain.valueWord,if_neg a,if_neg b]
  change packedWord old _ n ctr k = _
  rw [pack]
  have f : addressed = fun i => word ((head ++ Spec.toByte ctr.toNat 4) ++ (initial ++ tail)) (4*i) := by
    funext i; simpa only [Chain.packet,List.append_assoc] using atWord i
  rw [f,Leaf.payload_word _ _ _ ws n k (by simp [hh,Spec.toByte]) hi hw shape]
  simp only [Chain.packet,List.append_assoc,ctr]

end slhdsa.X86.Wots
