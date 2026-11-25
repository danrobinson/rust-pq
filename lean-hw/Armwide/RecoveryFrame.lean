import Armwide.SignatureBuffer
import Armwide.KeyPadding
import Spec.Correctness
open Aeneas Aeneas.Std Result
namespace slhdsa.Armwide.Recovery
open WotsRefill Transitions

def frame (n count : Nat) (rows : Nat → Spec.Bytes) := Keygen.filled n (encode n count rows)

theorem encode_size (n count : Nat) (rows : Nat → Spec.Bytes) : (encode n count rows).length=count*n := by
  unfold encode
  change (((List.range count).map rows).flatMap (slot n)).length=_
  rw [List.flatMap_map]
  apply Spec.length_flatMap_const
  intro i; exact slot_length .. 

theorem surround {α : Type} (front body tail data : List α) (i : Nat) (room : i+data.length≤body.length) :
    ((front++body)++tail).setSlice! (front.length+i) data =
      front++body.setSlice! i data++tail := by
  simp only [List.setSlice!,List.length_append]
  rw [Nat.min_eq_left (show data.length≤front.length+body.length+tail.length-(front.length+i) by omega),
    Nat.min_eq_left (show data.length≤body.length-i by omega),List.take_length]
  rw [List.take_append_of_le_length (by simp;omega),List.take_append, List.take_of_length_le (by omega : front.length≤front.length+i),
    List.drop_append_of_le_length (by simp;omega),Nat.add_assoc,List.drop_length_add_append]
  all_goals try omega
  simp [Nat.add_assoc,List.append_assoc]

def writeAt (n : Nat) (buf : Spec.Bytes) (c : Nat) (v : Spec.Bytes) :=
  buf.setSlice! (22+c*n) v

theorem write_frame (n count : Nat) (o : Nat → Spec.Bytes) (c : Nat) (x : Spec.Bytes)
    (live : c<count) (size : x.length=n) :
    writeAt n (frame n count o) c x = frame n count (setOut o c x) := by
  have fits : c*n+n≤count*n := by simpa [Nat.succ_mul] using Nat.mul_le_mul_right n (show c+1≤count by omega)
  change ((List.replicate 22 0#8 ++ encode n count o) ++ _).setSlice! (22+c*n) x=_
  have framed := surround (List.replicate 22 0#8) (encode n count o)
    (List.replicate (Keygen.total n-22-Keygen.payLen n) 0#8) x (c*n) (by rw [size,encode_size];exact fits)
  rw [List.length_replicate] at framed
  rw [framed]
  have middle := write_encode n count o c x
  rw [writeBuffer,slot_full n x size] at middle
  rw [middle]
  rfl

theorem frame_zero (n : Nat) (width : n=16 ∨ n=24 ∨ n=32) :
    frame n (2*n+3) (fun _ => []) = List.replicate (Keygen.total n) 0#8 := by
  unfold frame Keygen.filled
  rw [encode_zero,← List.replicate_add,← List.replicate_add]
  rcases width with rfl|rfl|rfl <;> rfl

end slhdsa.Armwide.Recovery
