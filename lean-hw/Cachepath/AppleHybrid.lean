import Cachepath.AppleHybridSchedule
import Shakebatch.Lanes

open Aeneas Aeneas.Std Result
open Spec.Keccak
namespace slhdsa.AppleHybrid
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

private def route (n : Fin 10) (sha3 : Bool) (j : Fin 8) : Route :=
  (schedule n sha3)[j.val]!

/-- Exhaustive over public dispatch inputs; the Keccak states remain arbitrary. -/
private theorem routes_correct : ∀ (n : Fin 10) (sha3 : Bool) (j : Fin 8), j.val < n.val →
    (route n sha3 j).1 = j ∧ ((route n sha3 j).2.map Prod.snd) = rc.toList := by decide

private theorem execute (ops : List (Kind × Lane)) (a : State) :
    ops.foldl (fun s op => liftedRound op.1 s op.2) a = (ops.map Prod.snd).foldl round a := by
  induction ops generalizing a with
  | nil => rfl
  | cons op rest ih =>
    simp only [List.foldl_cons, List.map_cons]
    rw [ih, liftedRound_eq]

def view (s : ShakeBatch.Matrix 8#usize) (j : Fin 8) : State :=
  _root_.Array.ofFn fun i : Fin 25 => s.val[i.val]!.val[j.val]!.bv

private def laneOut (n : Fin 10) (sha3 : Bool) (s : ShakeBatch.Matrix 8#usize) (j : Fin 8) : State :=
  let r := route n sha3 j
  r.2.foldl (fun a op => liftedRound op.1 a op.2) (view s r.1)

/-- The extracted schedule uses the same row-major layout as Rust's [[u64; 8]; 25]. -/
def packed (n : Fin 10) (sha3 : Bool) (s : ShakeBatch.Matrix 8#usize) : ShakeBatch.Matrix 8#usize :=
  Array.from (List.ofFn fun i : Fin 25 =>
    Array.from (List.ofFn fun j : Fin 8 => (⟨(laneOut n sha3 s j)[i.val]!⟩ : U64)) (by simp))
    (by simp)

private theorem packed_cell (n : Fin 10) (sha3 : Bool) (s : ShakeBatch.Matrix 8#usize)
    (i : Fin 25) (j : Fin 8) :
    ((packed n sha3 s).val[i.val]!.val[j.val]!).bv = (laneOut n sha3 s j)[i.val]! := by
  simp only [packed, Array.from_val]
  rw [List.getElem!_ofFn _ i.val i.isLt]
  simp only [Array.from_val]
  rw [List.getElem!_ofFn _ j.val j.isLt]

private theorem fold_size (cs : List Lane) (a : State) (ha : a.size = 25) :
    (cs.foldl round a).size = 25 := by
  induction cs generalizing a with
  | nil => exact ha
  | cons c cs ih =>
    rw [List.foldl_cons]
    exact ih (round a c) (by simp only [round, Id.run, pure, _root_.Array.size_ofFn])

private theorem permute_size (a : State) (ha : a.size = 25) : (permute a).size = 25 :=
  fold_size rc.toList a ha

/-- Covers both CPU capability branches, all nine legal active counts, and the full entry point. -/
theorem active_correct (n : Fin 10) (sha3 : Bool) (s : ShakeBatch.Matrix 8#usize)
    (j : Fin 8) (active : j.val < n.val) :
    view (packed n sha3 s) j = permute (view s j) := by
  obtain ⟨source, constants⟩ := routes_correct n sha3 j active
  have eq : laneOut n sha3 s j = permute (view s j) := by
    unfold laneOut
    rw [execute, source, constants]
    rfl
  apply ext25 _ _ (by simp [view]) (permute_size _ (by simp [view]))
  intro i hi
  rw [view, ofFnAt _ _ hi, packed_cell n sha3 s ⟨i,hi⟩ j, eq]

@[instance_reducible] def machine (sha3 : Bool) : ShakeBatch.Machine := ⟨8#usize, fun s => ok (packed 9 sha3 s)⟩

/-- Complete eight-lane permutation contract for the source lift, on both dispatch branches. -/
theorem permutation_correct (sha3 : Bool) : @ShakeBatch.PermutationCorrect (machine sha3) := by
  intro s
  change (ok (packed 9 sha3 s) : Result _) ⦃ _ => _ ⦄
  simp only [WP.spec_ok]
  intro j hj
  exact active_correct 9 sha3 s ⟨j,hj⟩ (by change j < 9; change j < 8 at hj; omega)

end slhdsa.AppleHybrid
