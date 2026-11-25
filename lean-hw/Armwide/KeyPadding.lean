import Armwide.PaddingProgram
import Armwide.Endpoints
namespace slhdsa.Armwide.Keygen
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

def total (n : Nat) := if n=16 then 640 else if n=24 then 1280 else 2304
def payLen (n : Nat) := (2*n+3)*n

private def readSpan (a : Spec.Adrs) (buf : Spec.Bytes) (s : Span) : Spec.Bytes :=
  if s.stride=0 then List.replicate s.count (BitVec.ofNat 8 s.source)
  else if s.source<512 then ((Spec.wotsPkAdrs a).compress.drop (s.source-256)).take s.count
  else (buf.drop (s.source-512)).take s.count

def padded (n : Nat) (a : Spec.Adrs) (buf : Spec.Bytes) :=
  (spans[group n]!).flatMap (readSpan a buf)

def filled (n : Nat) (payload : Spec.Bytes) :=
  List.replicate 22 0#8 ++ payload ++ List.replicate (total n-22-payLen n) 0#8

private theorem spans_shape (n : Nat) (width : n=16 ∨ n=24 ∨ n=32) :
    spans[group n]! = [⟨256,22,1⟩,⟨534,payLen n,1⟩,⟨128,1,0⟩,
      ⟨512+22+payLen n+1,total n-22-payLen n-3,1⟩,
      ⟨((if n=16 then 64 else 128)+22+payLen n)*8/256,1,0⟩,
      ⟨((if n=16 then 64 else 128)+22+payLen n)*8%256,1,0⟩] := by
  rcases width with rfl|rfl|rfl <;> decide

private theorem middle (n : Nat) (payload : Spec.Bytes) (size : payload.length=payLen n) :
    ((filled n payload).drop 22).take (payLen n) = payload := by
  simp only [filled,List.append_assoc,List.drop_append,List.length_replicate,List.drop_replicate,Nat.sub_self,
    List.replicate_zero,List.drop_zero,List.nil_append,←size,List.take_left]

private theorem zeros (n : Nat) (payload : Spec.Bytes) (size : payload.length=payLen n) :
    ((filled n payload).drop (22+payLen n+1)).take (total n-22-payLen n-3) =
      List.replicate (total n-22-payLen n-3) 0#8 := by
  have front : (List.replicate 22 0#8 ++ payload).length = 22+payLen n := by rw [List.length_append,List.length_replicate,size]
  rw [filled,List.drop_append,List.drop_eq_nil_of_le (by omega : (List.replicate 22 0#8 ++ payload).length ≤ 22+payLen n+1),List.nil_append]
  simp only [front,List.drop_replicate,List.take_replicate]
  congr 1; omega

theorem padded_eq (n : Nat) (width : n=16 ∨ n=24 ∨ n=32)
    (a : Spec.Adrs) (msg : Spec.Bytes) (size : msg.length=payLen n) :
    padded n a (filled n msg) =
      if n=16 then padFrom 64 ((Spec.wotsPkAdrs a).compress ++ msg)
      else S512.padFrom 128 ((Spec.wotsPkAdrs a).compress ++ msg) := by
  have adrs : (Spec.wotsPkAdrs a).compress.length=22 := rfl
  have x : 512+22+payLen n+1-512=22+payLen n+1 := by omega
  have big : ¬512+22+payLen n+1<512 := by omega
  rw [padded,spans_shape n width]
  simp (config := {decide := true}) only [List.flatMap_cons,List.flatMap_nil,readSpan,Nat.reduceLT,↓reduceIte,
    Nat.reduceSub,List.drop_zero,List.take_of_length_le (Nat.le_of_eq adrs),big,x,middle n msg size,
    zeros n msg size,List.replicate_one,List.append_nil]
  rcases width with rfl|rfl|rfl <;> simp only [payLen,Nat.reduceMul,Nat.reduceAdd] at size <;>
    simp (config := {decide := true}) only [padFrom,S512.padFrom,List.length_append,adrs,size,↓reduceIte,ite_true,
      Nat.reduceMod,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceSub,Nat.reduceMul,total,payLen,
      List.append_assoc,List.cons_append,List.nil_append] <;> rfl

end slhdsa.Armwide.Keygen
