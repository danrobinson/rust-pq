import Wots.RecoveryRound
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.Wots

/-- The full destination row, including the original header and suffix. -/
def rowComplete (N : Usize) (expected : Nat → Spec.Bytes) (base buf : Buffers) (r : Nat) :=
  bytes buf.val[r]!.val = bytes (base.val[r]!.val.take 22) ++ expected r ++ bytes (base.val[r]!.val.drop (22+N.val))

def rowFrame (N : Usize) (base buf : Buffers) (r : Nat) :=
  buf.val[r]!.val.take 22 = base.val[r]!.val.take 22 ∧
    buf.val[r]!.val.drop (22+N.val) = base.val[r]!.val.drop (22+N.val)

def rowsSafe (N : Usize) (count : Nat) (base buf : Buffers) :=
  buf.length = base.length ∧ ∀ r < base.length, rowFrame N base buf r ∧ (count ≤ r → buf.val[r]! = base.val[r]!)

def accounted (N : Usize) (expected : Nat → Spec.Bytes) (base buf : Buffers) (order : Order)
    (pos : Nat) (owner : Fin 16 → Option Nat) :=
  ∀ q < pos, (∃ j, owner j = some q) ∨ rowComplete N expected base buf order.val[q]!.val

theorem accounted_refill {N expected base buf order p next owner owner'}
    (prior : accounted N expected base buf order p owner)
    (keep : ∀ j q, owner j = some q → owner' j = some q)
    (added : ∀ q, p ≤ q → q < next → ∃! j, owner' j = some q) :
    accounted N expected base buf order next owner' := by
  intro q hq
  by_cases old : q < p
  · rcases prior q old with ⟨j,hj⟩|written
    · exact Or.inl ⟨j,keep j q hj⟩
    · exact Or.inr written
  · exact Or.inl (added q (by omega) hq).exists

theorem splice_frame (row : Array U8 64#usize) (value : List U8) (n : Nat)
    (len : value.length=n) :
    let s := row.val.take 22 ++ value ++ row.val.drop (22+n)
    s.take 22 = row.val.take 22 ∧ s.drop (22+n) = row.val.drop (22+n) := by
  have head : (row.val.take 22).length=22 := by simp
  dsimp only
  rw [List.append_assoc]
  constructor
  · simpa only [head] using (List.take_append_length (l₁ := row.val.take 22) (l₂ := value ++ row.val.drop (22+n)))
  · have eq := List.drop_length_add_append (l₁ := row.val.take 22) (l₂ := value ++ row.val.drop (22+n)) value.length
    rw [List.drop_append_length,head,len] at eq
    exact eq

private theorem lane_key {digits : Slice U32} {order ix active pos owner}
    (owned : owns order ix active pos owner)
    (ordered : ∀ i < digits.length, order.val[rank digits.val i]!.val = i)
    (bound : pos ≤ digits.length) (small : digits.length ≤ 67) (j q) (hj : owner j = some q) :
    enabled active j = true ∧ outputKey ix j = order.val[q]!.val ∧ chainIndex ix j = outputKey ix j := by
  have lane := owned.2 j
  rw [hj] at lane
  obtain ⟨on,lt,idx⟩ := lane
  have cap := (order_at digits order ordered q (by omega)).1
  unfold outputKey chainIndex
  rw [idx,index_roundtrip _ (by omega)]
  refine ⟨on,rfl,?_⟩
  change (UScalar.hcast .I32 order.val[q]!).bv.toNat = _
  rw [UScalar.hcast_bv_eq,BitVec.toNat_setWidth]
  change order.val[q]!.val % (2^32) = _
  exact Nat.mod_eq_of_lt (by omega)

/-- A completed job either still owns a surviving lane or has its exact row in
the buffer. Later retirements preserve that fact, including for earlier writes. -/
theorem account_retirement {N : Usize} {digits : Slice U32} {order ix mask pos owner}
    (base before after : Buffers) (staged : Staged N) (c next : Reg) (survive : U16)
    (expect : Nat → Spec.Bytes) (owned : owns order ix mask pos owner)
    (ordered : ∀ i < digits.length, order.val[rank digits.val i]!.val = i)
    (bound : pos ≤ digits.length) (small : digits.length ≤ 67) (room : digits.length ≤ base.length)
    (safe : rowsSafe N digits.length base before) (prior : accounted N expect base before order pos owner)
    (inc : ∀ j, next j = c j+1)
    (bits : ∀ j, enabled survive j = true ↔ enabled mask j = true ∧ next j ≠ 15)
    (writes : retired ix staged before after (finishes mask c))
    (values : ∀ j, finishes mask c j → bytes staged.val[j.val]!.val = expect (chainIndex ix j)) :
    rowsSafe N digits.length base after ∧
    (∀ r < base.length, rowComplete N expect base before r → rowComplete N expect base after r) ∧
    accounted N expect base after order pos (fun j => if enabled survive j then owner j else none) := by
  have stored (j) (done : finishes mask c j) (hr : outputKey ix j < base.length)
      (index : chainIndex ix j = outputKey ix j) :
      rowFrame N base after (outputKey ix j) ∧ rowComplete N expect base after (outputKey ix j) := by
    have eq := writes.2.1 j done
    have frame := (safe.2 _ hr).1
    have parts := splice_frame before.val[outputKey ix j]! staged.val[j.val]!.val N.val (by simp)
    refine ⟨⟨?_,?_⟩,?_⟩
    · exact (congrArg (List.take 22) eq).trans (parts.1.trans frame.1)
    · exact (congrArg (List.drop (22+N.val)) eq).trans (parts.2.trans frame.2)
    · unfold rowComplete
      rw [eq,frame.1,frame.2]
      simpa only [bytes,List.map_append] using congrArg
        (fun data => bytes (base.val[outputKey ix j]!.val.take 22) ++ data ++ bytes (base.val[outputKey ix j]!.val.drop (22+N.val)))
        ((values j done).trans (congrArg expect index))
  have effect (r) (hr : r < base.length) :
      (rowFrame N base after r ∧ rowComplete N expect base after r ∧ r < digits.length) ∨
        after.val[r]! = before.val[r]! := by
    by_cases hit : ∃ j, finishes mask c j ∧ outputKey ix j = r
    · obtain ⟨j,done,key⟩ := hit
      obtain ⟨q,hq⟩ : ∃ q, owner j = some q := by
        cases e : owner j with
        | some q => exact ⟨q,rfl⟩
        | none => have h := owned.2 j; rw [e] at h; have := done.1; simp_all
      obtain ⟨_,atQ,index⟩ := lane_key owned ordered bound small j q hq
      have valid := (owned_destinations owned ordered bound small).1 j done.1
      subst r
      obtain ⟨frame,complete⟩ := stored j done hr index
      exact Or.inl ⟨frame,complete,valid⟩
    · exact Or.inr (writes.2.2 r (fun j done eq => hit ⟨j,done,eq⟩))
  have preserve (r) (hr : r < base.length) (ready : rowComplete N expect base before r) :
      rowComplete N expect base after r := by
    rcases effect r hr with hit|same
    · exact hit.2.1
    · unfold rowComplete at *; rw [same]; exact ready
  refine ⟨⟨writes.1.trans safe.1,?_⟩,preserve,?_⟩
  · intro r hr
    rcases effect r hr with hit|same
    · exact ⟨hit.1,fun h => (Nat.not_le_of_lt hit.2.2 h).elim⟩
    · obtain ⟨frame,extra⟩ := safe.2 r hr
      exact ⟨by unfold rowFrame at *; rwa [same],fun h => same.trans (extra h)⟩
  · intro q hq
    have roomQ := (order_at digits order ordered q (by omega)).1
    rcases prior q hq with ⟨j,hj⟩|already
    · obtain ⟨on,key,index⟩ := lane_key owned ordered bound small j q hj
      by_cases finished : next j=15
      · right
        have done : finishes mask c j := ⟨on,(inc j).symm.trans finished⟩
        rw [← key]
        exact (stored j done (by omega) index).2
      · exact Or.inl ⟨j,by simp [(bits j).mpr ⟨on,finished⟩,hj]⟩
    · exact Or.inr (preserve _ (by omega) already)

end slhdsa.X86.Wots
