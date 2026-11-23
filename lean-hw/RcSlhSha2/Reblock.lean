import RcSlhSha2.Platforms

namespace slhdsa.RcSlhSha2
open Aeneas Aeneas.Std Spec

def raw {w} (bs : List (Array U8 w)) : Bytes := bs.flatMap fun b => bytes b.val

private theorem segments (p : Bytes) (w count : Nat) :
    ((List.range count).map (fun i => (p.drop (w*i)).take w)).flatten = p.take (w*count) := by
  induction count with
  | zero => simp
  | succ k ih =>
    simp only [List.range_succ,List.map_append,List.map_cons,List.map_nil,List.flatten_append,
      List.flatten_cons,List.flatten_nil,List.append_nil,ih,Nat.mul_succ]
    rw [List.take_drop]
    have h := List.take_append_drop (w*k) (p.take (w*k+w))
    simpa [List.take_take,Nat.min_eq_left (Nat.le_add_right (w*k) w)] using h

theorem raw_blocks (w : Usize) (p : Bytes) :
    raw (blocks w p) = p.take (w.val * (p.length / w.val)) := by
  change ((blocks w p).map (fun b => bytes b.val)).flatten = _
  rw [blocks_bytes,segments]

private theorem view_injective {w} {a b : Array U8 w} (eq : bytes a.val = bytes b.val) : a = b := by
  apply (Array.eq_iff a b).mpr
  have e := congrArg (List.map (fun v => (⟨v⟩ : U8))) eq
  simpa [bytes,List.map_map,Function.comp_def] using e

theorem raw_injective {w} (positive : 0 < w.val) {xs ys : List (Array U8 w)}
    (eq : raw xs = raw ys) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons y ys =>
      have h := congrArg List.length eq
      simp [raw,bytes] at h
      omega
  | cons x xs ih =>
    cases ys with
    | nil =>
      have h := congrArg List.length eq
      simp [raw,bytes] at h
      omega
    | cons y ys =>
      change bytes x.val ++ raw xs = bytes y.val ++ raw ys at eq
      have e := congrArg (List.take w.val) eq
      have xlen : (bytes x.val).length = w.val := by simp [bytes]
      have ylen : (bytes y.val).length = w.val := by simp [bytes]
      simp only [List.take_append,xlen,ylen,Nat.sub_self,List.take_zero,List.append_nil,
        List.take_of_length_le xlen.le,List.take_of_length_le ylen.le] at e
      have same := view_injective e
      subst y
      exact congrArg (x :: ·) (ih ((List.append_right_inj _).mp eq))

/-- Supplying exactly the padded bytes in full machine blocks determines
the partition equality used by the hardware hash proofs. -/
theorem blocks_of_raw {w} (positive : 0 < w.val) (groups : List (Slice (Array U8 w))) (p : Bytes)
    (complete : w.val ∣ p.length) (order : raw (groups.flatMap (·.val)) = p) :
    groups.flatMap (·.val) = blocks w p := by
  apply raw_injective positive
  rw [order,raw_blocks,Nat.mul_comm, Nat.div_mul_cancel complete, List.take_length]

end slhdsa.RcSlhSha2
