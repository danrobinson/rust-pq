import Kgridbulk.Word
open Aeneas Aeneas.Std Result Spec.Keccak
namespace slhdsa.Kgridbulk

def ratePrefix (a : State) (block : List U8) (words : Nat) : State :=
  _root_.Array.ofFn (n := 25) fun i =>
    if i.val < words then a[i.val]! ^^^ wordAt block (8*i.val) else a[i.val]!

private theorem advance (a : State) (b : List U8) (i : Nat) (bound : i<17) :
    (ratePrefix a b i).setIfInBounds i ((ratePrefix a b i)[i]! ^^^ wordAt b (8*i)) =
    ratePrefix a b (i+1) := by
  apply ext25 _ _ (by simp [ratePrefix]) (by simp [ratePrefix])
  intro j hj
  rw [getElem!_pos _ j (by simpa [ratePrefix] using hj),_root_.Array.getElem_setIfInBounds (by simpa [ratePrefix] using hj)]
  by_cases same : i=j
  · subst j
    simp [ratePrefix,ofFnAt,show i<25 by omega]
  · simp [ratePrefix,ofFnAt,hj,same,Ne.symm same,show (j ≤ i) ↔ j < i by omega]

private def rest (a : State) (block : List U8) (i : Nat) :=
  ((bytes block).drop (8*i)).foldl feed
    (if i=17 then (permute (ratePrefix a block i),0) else (ratePrefix a block i,8*i))

private theorem rest_step (a : State) (b : List U8) (size : b.length=136) (i : Nat) (hi : i<17) :
    rest a b i = rest a b (i+1) := by
  let chunk := (b.drop (8*i)).take 8
  have eight : (bytes chunk).length=8 := by simp [chunk]; omega
  have data : (bytes b).drop (8*i) = bytes chunk ++ (bytes b).drop (8*(i+1)) := by
    simp only [chunk,bytes_take,bytes_drop,show 8*(i+1)=8*i+8 by omega,← List.drop_drop,List.take_append_drop]
  have one := feedWord (ratePrefix a b i) i (bytes chunk) eight (by simp [ratePrefix]; omega) hi
  dsimp only at one
  unfold rest
  rw [if_neg (by omega : i≠17),data,List.foldl_append,one,← wordAt_laneBytes b (8*i) (by omega),advance a b i hi]
  by_cases last : i=16
  · simp [last]
  · simp [last,show i+1≠17 by omega,Nat.mul_succ]

theorem feed_block (a : State) (b : List U8) (shape : a.size=25) (size : b.length=136) :
    (bytes b).foldl feed (a,0) = (permute (ratePrefix a b 17),0) := by
  have base : ratePrefix a b 0 = a := by
    apply ext25 _ _ (by simp [ratePrefix]) shape
    intro i hi
    simp [ratePrefix,ofFnAt,hi]
  have all (i : Nat) (hi : i≤17) : rest a b 0 = rest a b i := by
    induction i with
    | zero => rfl
    | succ i ih => exact (ih (by omega)).trans (rest_step a b size i (by omega))
  simpa [rest,size,base,List.drop_eq_nil_of_le (by simpa using size.le : (bytes b).length ≤ 136)] using all 17 (by decide)
end slhdsa.Kgridbulk
