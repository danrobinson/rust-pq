import Armwide.XmssLeaves
import Armwide.XmssMultiProgram
import Slhdsa.Proofs.Wots
namespace slhdsa.Armwide.XmssLeaves
open Keygen Spec.SHA256

private def coords256 (g k : Nat) := (((reads[if g=2 then 0 else 1]!)[k]!).map
  (List.map (fun i => (i/640,i%640))))

private theorem coords256_eq (g : Nat) (lanes : g=2 ∨ g=4) :
    ∀ k : Fin g, coords256 g k = Keygen.blocks.map (List.map (fun i => (k.val,i))) := by
  rcases lanes with rfl|rfl <;> decide

private def next (input : Nat → Spec.Bytes) (st : List Word) (reads : List (Nat × Nat)) :=
  let words := reads.flatMap (fun (k,i) => ((input k).drop i).take 16)
  let r := Kernel.compressBlockLane true st words
  vwords r.1 ++ vwords r.2

def batched256 (g k : Nat) (state : List Word) (input : Nat → Spec.Bytes) :=
  (ser ((coords256 g k).foldl (next input) state)).take 16

theorem batched256_eq (g k : Nat) (lanes : g=2 ∨ g=4) (key : k<g)
    (st : List Word) (input : Nat → Spec.Bytes) :
    batched256 g k st input = multi256 st (input k) := by
  unfold batched256
  rw [coords256_eq g lanes ⟨k,key⟩]
  simp only [List.foldl_map,multi256]
  apply congrArg (fun f => (ser (List.foldl f st blocks)).take 16)
  funext old reads
  unfold next step
  simp only [List.flatMap_map]
  rfl

def batched512 (g k : Nat) (hard : Bool) (n : Nat) (st : List Spec.SHA512.Word) (input : Nat → Spec.Bytes) :=
  if !hard then scalar512 n st (input k)
  else if g=2 then
    let r:=H512.Multi.compressMulti2 n st (input 0) (input 1) ((input 0).length/128)
    if k=0 then r.1 else r.2
  else
    let r:=H512.Multi.compressMulti4 n st (input 0) (input 1) (input 2) (input 3) ((input 0).length/128)
    if k=0 then r.1 else if k=1 then r.2.1 else if k=2 then r.2.2.1 else r.2.2.2

theorem batched512_eq (n : Nat) (width : n=24 ∨ n=32) (g k : Nat) (lanes : g=2 ∨ g=4) (key : k<g)
    (hard : Bool) (st : List Spec.SHA512.Word) (len : st.length=8) (input : Nat → Spec.Bytes)
    (size : ∀ i<g, (input i).length=total n) :
    batched512 g k hard n st input = scalar512 n st (input k) := by
  cases hard
  · rfl
  rcases lanes with rfl|rfl <;> unfold batched512 <;> simp only [Bool.not_true,Bool.false_eq_true,↓reduceIte]
  · rw [H512.Multi.compress_multi_2_eq_iter n width st len _ _ _ rfl (by rw [size 0 (by decide),size 1 (by decide)])]
    interval_cases k <;> rfl
  · rw [H512.Multi.compress_multi_4_eq_iter n width st len _ _ _ _ _ rfl
        (by rw [size 0 (by decide),size 1 (by decide)]) (by rw [size 0 (by decide),size 2 (by decide)])
        (by rw [size 0 (by decide),size 3 (by decide)])]
    interval_cases k <;> rfl

end slhdsa.Armwide.XmssLeaves
