import Chainwide.Retire
import Leaf256.Payload
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.Chain
open Spec.SHA256

def packet (head : Spec.Bytes) (counter : Word) (value tail : Spec.Bytes) :=
  head ++ (Spec.toByte counter.toNat 4 ++ (value ++ tail))

/-- Counter bytes originally present in the 64-byte block can be arbitrary. -/
theorem address_layout (head old tail : Spec.Bytes) (counter : Word) (k : Nat)
    (hh : head.length = 18) (ho : old.length = 4) :
    let w := fun i => word (head ++ (old ++ tail)) (4*i)
    addressWord w (w 4 &&& 0xffff0000) counter k =
      word (head ++ (Spec.toByte counter.toNat 4 ++ tail)) (4*k) := by
  dsimp only
  have idx := Leaf.index_word head tail hh counter k
  rw [← idx]
  have zlen : (Spec.toByte 0 4).length = 4 := by simp [Spec.toByte]
  by_cases small : k < 4
  · simp (disch := omega) only [addressWord,Leaf.prfWords,if_neg,word,List.getElem!_append_left]
  by_cases large : k > 5
  · simp (disch := omega) only [addressWord,Leaf.prfWords,if_neg,word,List.getElem!_append_right,hh,ho,zlen]
  rcases (by omega : k=4 ∨ k=5) with rfl|rfl
  all_goals simp (disch := omega) only [addressWord,Leaf.prfWords,↓reduceIte,word,
    Nat.reduceMul,Nat.reduceAdd,List.getElem!_append_left,List.getElem!_append_right,hh,ho,zlen,Nat.reduceSub]
  all_goals simp only [show Spec.toByte 0 4 = [0#8,0#8,0#8,0#8] by rfl,
    show (5=4) = False by decide,↓reduceIte,List.getElem!_cons_zero,List.getElem!_cons_succ]
  all_goals leaf_bits

private theorem repack (old : Nat → Word) (ws : List Word) (fixed current next : Word) (n k : Nat)
    (shape : n=16 ∨ n=24 ∨ n=32) :
    addressWord (valueWord (addressWord old fixed current) (fun i => ws[i]!) n) fixed next k =
      Leaf.payloadWord (addressWord old fixed next) ws n k := by
  by_cases a : k = 4
  · subst k
    simp [addressWord,Leaf.payloadWord]; omega
  by_cases b : k = 5
  · subst k
    simp only [addressWord,valueWord,Leaf.payloadWord,↓reduceIte]
    simp only [show (5=4) = False by decide,↓reduceIte]
    generalize ws[0]! = x
    generalize old 5 = y
    leaf_bits
  simp (disch := omega) only [addressWord,valueWord,Leaf.payloadWord,if_neg]

theorem next_layout (old : Nat → Word) (ws : List Word) (fixed current next : Word)
    (head value tail : Spec.Bytes) (n k : Nat) (hh : head.length = 18) (hv : value.length = n)
    (hw : ws.length = 8) (shape : n=16 ∨ n=24 ∨ n=32)
    (hk : k < 16) (ready : ∀ t i, i < 16 → addressWord old fixed t i = word (packet head t value tail) (4*i)) :
    addressWord (valueWord (addressWord old fixed current) (fun i => ws[i]!) n) fixed next k =
      word (packet head next ((ser ws).take n) tail) (4*k) := by
  rw [repack _ _ _ _ _ _ _ shape]
  let raw := fun i => word ((head ++ Spec.toByte next.toNat 4) ++ (value ++ tail)) (4*i)
  have eq : Leaf.payloadWord (addressWord old fixed next) ws n k = Leaf.payloadWord raw ws n k := by
    simp only [Leaf.payloadWord,ready next k hk,raw,packet,List.append_assoc]
  rw [eq,Leaf.payload_word _ _ _ _ _ _ (by simp [hh,Spec.toByte]) hv hw shape]
  simp [packet,List.append_assoc]

end slhdsa.X86.Chain
