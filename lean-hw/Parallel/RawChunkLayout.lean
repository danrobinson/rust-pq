import Parallel.AuthTable
open Aeneas Aeneas.Std Result
namespace slhdsa.ParallelRawChunks
open ParallelXmssTicket ParallelSigning

def group (width q : Nat) := (List.range (2^depth width (q%width))).map (q,·)
def slots (width n : Nat) := (List.range n).flatMap (group width)
def offset (width q : Nat) := (slots width q).length

private theorem append_slot (w n : Nat) : slots w (n+1)=slots w n++group w n := by
  simp [slots,List.range_succ]

theorem room {w n q : Nat} (h : q<n) : offset w q+2^depth w (q%w)≤(slots w n).length := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [append_slot,List.length_append]
    by_cases e : q=n
    · simp [e,offset,group]
    · exact (ih (by omega)).trans (Nat.le_add_right ..)

theorem coordinate {w n q c : Nat} (h : q<n) (chunk : c<2^depth w (q%w)) :
    (slots w n)[offset w q+c]! = (q,c) := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [append_slot]
    by_cases e : q=n
    · subst q
      have fit : offset w n+c < (slots w n++group w n).length := by simp [offset,group];omega
      rw [getElem!_pos (slots w n++group w n) (offset w n+c) fit,List.getElem_append_right (by simp [offset])]
      simp [offset,group,chunk]
    · have fit : offset w q+c<(slots w n).length := by have := @room w n q (by omega);omega
      rw [getElem!_pos (slots w n++group w n) (offset w q+c) (by simp;omega),List.getElem_append_left fit,←getElem!_pos]
      exact ih (by omega)

theorem capacity (w n : Nat) (positive : 0<w) (maxW : w≤9) : (slots w n).length≤n*512 := by
  induction n with
  | zero => simp [slots]
  | succ n ih =>
    have split : depth w (n%w)≤9 := by
      unfold depth
      have := Nat.mod_lt n positive;omega
    rw [append_slot,List.length_append]
    simp only [group,List.length_map,List.length_range,Nat.succ_mul]
    have cap := Nat.pow_le_pow_right (by decide : 0<2) split
    omega

theorem shape {w n : Nat} (key : Nat × Nat) (found : key∈slots w n) :
    key.1<n ∧ key.2<2^depth w (key.1%w) := by
  obtain ⟨q,hq,hc⟩ := List.mem_flatMap.mp found
  obtain ⟨c,ac,eq⟩ := List.mem_map.mp hc
  subst key
  exact ⟨List.mem_range.mp hq,List.mem_range.mp ac⟩

def collect {α β : Type} (f : α → Result β) : List α → Result (List β)
  | [] => ok []
  | x::xs => do let y ← f x;let ys ← collect f xs;ok (y::ys)

theorem collect_ok {α β : Type} [Inhabited α] [Inhabited β] (f : α → Result β) (xs : List α)
    (works : ∀ x∈xs, ∃ v, f x=ok v) :
    ∃ out, collect f xs=ok out ∧ out.length=xs.length ∧ ∀ i<xs.length, f xs[i]! = ok out[i]! := by
  induction xs with
  | nil => exact ⟨[],rfl,rfl,by simp⟩
  | cons x xs ih =>
    obtain ⟨y,eq⟩ := works x (by simp)
    obtain ⟨ys,run,len,atIndex⟩ := ih (fun a h => works a (by simp [h]))
    refine ⟨y::ys,by simp [collect,eq,run],by simp [len],?_⟩
    intro i hi
    cases i with
    | zero => simpa using eq
    | succ j => simpa using atIndex j (by simpa using hi)
end slhdsa.ParallelRawChunks
