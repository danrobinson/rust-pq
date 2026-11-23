module
public import Aeneas
@[expose] public section
open Aeneas Aeneas.Std Result
namespace ChainAvx2Rust
/-- The nonzero-width Rust primitive splits a slice into disjoint full arrays
and a remainder. Reborrows preserve the lengths of both slices. -/
def fullChunks {T : Type u} (n : Usize) (b : Slice T) : Slice (Array T n) :=
  let groups := b.length/n.val
  let data := List.ofFn fun j : Fin groups =>
    Array.from ((b.val.drop (n.val*j.val)).take n.val) (by
      simp only [List.length_take,List.length_drop]
      apply Nat.min_eq_left
      by_cases zero : n.val = 0
      · simp [zero]
      · have h := (Nat.le_div_iff_mul_le (by omega : 0 < n.val)).mp (show j.val+1 ≤ b.val.length/n.val from j.isLt)
        rw [Nat.add_mul,Nat.one_mul,Nat.mul_comm j.val] at h
        omega)
  Slice.from data (by change (List.ofFn _).length ≤ _; rw [List.length_ofFn]; exact le_trans (Nat.div_le_self _ _) b.property)

def remainder {T : Type u} (n : Usize) (b : Slice T) : Slice T :=
  Slice.from (b.val.drop (n.val*(b.length/n.val))) (by rw [List.length_drop]; exact le_trans (Nat.sub_le ..) b.property)

def joinChunks {T : Type u} {n : Usize} (b : Slice T) (parts : Slice (Array T n) × Slice T) : Slice T :=
  let data := parts.1.val.flatMap (·.val) ++ parts.2.val
  if h : data.length = b.length then Slice.from data (h ▸ b.property) else b

def core.slice.Slice.as_chunks_mut {T : Type u} (n : Usize) (b : Slice T) :
    Result ((Slice (Array T n) × Slice T) × ((Slice (Array T n) × Slice T) → Slice T)) :=
  if n.val = 0 then fail .panic else ok ((fullChunks n b,remainder n b),joinChunks b)

end ChainAvx2Rust

namespace ChainAvx2Rust
private theorem flatten_prefix {T : Type u} (xs : List T) (n count off : Nat) :
    ((List.ofFn fun i : Fin count => (xs.drop (off+n*i.val)).take n).flatten) =
      (xs.drop off).take (n*count) := by
  induction count generalizing off with
  | zero => simp
  | succ count ih =>
    rw [List.ofFn_succ,List.flatten_cons]
    simp only [Fin.val_zero,Nat.mul_zero,Nat.add_zero,Fin.val_succ]
    simp only [Nat.mul_add,Nat.mul_one,show ∀ i, off+(n*i+n) = (off+n)+n*i by intro; omega]
    rw [ih (off+n),← List.drop_drop,← List.take_add]
    congr 1; omega

theorem fullChunks_flatten {T : Type u} (b : Slice T) (n : Usize) :
    (fullChunks n b).val.flatMap (·.val) = b.val.take (n.val*(b.length/n.val)) := by
  unfold fullChunks
  simp only [Slice.from_val]
  rw [List.flatMap_def,List.map_ofFn]
  simpa only [Function.comp_def,Array.from_val,Nat.zero_add,List.drop_zero] using flatten_prefix b.val n.val (b.length/n.val) 0

theorem chunk_parts {T : Type u} (b : Slice T) (n : Usize) :
    (fullChunks n b).val.flatMap (·.val) ++ (remainder n b).val = b.val := by
  simp only [fullChunks_flatten,remainder,Slice.from_val,List.take_append_drop]

theorem chunks_roundtrip {T : Type u} (b : Slice T) (n : Usize) :
    joinChunks b (fullChunks n b, remainder n b) = b := by
  have rejoin := chunk_parts b n
  apply Slice.ext
  unfold joinChunks
  simp [rejoin,Slice.length]
end ChainAvx2Rust
