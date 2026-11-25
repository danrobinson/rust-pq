import Armwide.StoreSimulation
import Slhdsa.Proofs.Encoding

namespace slhdsa.Armwide.Transitions
open WotsRefill Spec.SHA256

/-- The initialized signature has one n-byte slot for each chain. Empty slots contain zero. -/
def slot (n : Nat) (row : Spec.Bytes) := row.take n ++ List.replicate (n-row.length) 0#8

theorem slot_length (n : Nat) (row : Spec.Bytes) : (slot n row).length=n := by
  simp only [slot,List.length_append,List.length_take,List.length_replicate]; omega

theorem slot_full (n : Nat) (row : Spec.Bytes) (len : row.length=n) : slot n row=row := by simp [slot,←len]

private def pack (n : Nat) (rows : List Spec.Bytes) := rows.flatMap (slot n)

private theorem pack_length (n : Nat) (rows : List Spec.Bytes) : (pack n rows).length=rows.length*n := by
  induction rows with
  | nil => simp [pack]
  | cons x xs ih => simpa [pack,slot_length,Nat.add_mul,Nat.add_comm] using congrArg (n+·) ih

private theorem pack_set (n : Nat) (rows : List Spec.Bytes) (c : Nat) (v : Spec.Bytes) :
    (pack n rows).setSlice! (c*n) (slot n v) = pack n (rows.set c v) := by
  by_cases bound : c < rows.length
  · have split := List.set_eq_take_append_cons_drop (l:=rows) (i:=c) (a:=rows[c])
    rw [List.set_getElem_self,ite_eq_left bound] at split
    have parts := congrArg (pack n) split
    simp only [pack,List.flatMap_append,List.flatMap_cons] at parts
    rw [List.set_eq_take_append_cons_drop,ite_eq_left bound]
    simp only [pack,List.flatMap_append,List.flatMap_cons]
    rw [parts,←List.append_assoc]
    apply (slhdsa.setSlice_mid' _ _ _ _ _ ?_ (by simp [slot_length])).trans (List.append_assoc ..)
    change c*n=(pack n (rows.take c)).length
    rw [pack_length,List.length_take,Nat.min_eq_left (Nat.le_of_lt bound)]
  · rw [List.set_eq_take_append_cons_drop,ite_eq_right bound]
    have offset : (pack n rows).length ≤ c*n := by rw [pack_length]; exact Nat.mul_le_mul_right _ (by omega)
    simp [List.setSlice!,Nat.sub_eq_zero_of_le offset, List.take_of_length_le offset,
      List.drop_eq_nil_of_le (show (pack n rows).length ≤ c*n+(slot n v).length by omega)]
    exact offset

def encode (n count : Nat) (out : Nat → Spec.Bytes) := pack n ((List.range count).map out)

def writeBuffer (n : Nat) (buf : Spec.Bytes) (c : Nat) (v : Spec.Bytes) :=
  buf.setSlice! (c*n) (slot n v)

def rawStore (n : Nat) (buf : Spec.Bytes) (c : Nat) (v : Spec.Bytes) := buf.setSlice! (c*n) v

theorem write_encode (n count : Nat) (out : Nat → Spec.Bytes) (c : Nat) (v : Spec.Bytes) :
    writeBuffer n (encode n count out) c v = encode n count (setOut out c v) := by
  unfold encode writeBuffer
  rw [pack_set]
  congr 1
  apply List.ext_getElem (by simp)
  intro j h h'
  simp only [List.getElem_set,List.getElem_map,List.getElem_range,setOut]
  split <;> simp_all [eq_comm]

theorem encode_zero (n count : Nat) :
    encode n count (fun _ => []) = List.replicate (count*n) 0#8 := by
  induction count with
  | zero => simp [encode,pack]
  | succ c ih =>
    simp only [encode,pack,List.range_succ,List.map_append,List.flatMap_append,List.map_cons,List.map_nil,
      List.flatMap_cons,List.flatMap_nil,List.append_nil,slot,List.take_nil,List.length_nil,Nat.sub_zero,
      List.nil_append] at *
    rw [ih,←List.replicate_add,Nat.succ_mul]

theorem encode_done (n count : Nat) (rows : Nat → Spec.Bytes) (size : ∀ c < count, (rows c).length=n) :
    encode n count rows = (List.range count).flatMap rows := by
  simp only [encode,pack,List.flatMap_map]
  apply List.flatMap_congr
  intro i hi
  exact slot_full n _ (size _ (List.mem_range.mp hi))

def bufferSign (n : Nat) (st : List Word) (sk : Spec.Bytes) (a : Spec.Adrs) (d : Nat → Nat)
    (order : List Nat) (buffer : Spec.Bytes) : Spec.Bytes :=
  let (ls,q) := initialRows sk d order
  writeRun (rawStore n) n st sk a d ls q buffer (signMeasure ls q+1)

theorem buffer_sign_size (n : Nat) (st : List Word) (sk : Spec.Bytes) (a : Spec.Adrs) (d : Nat → Nat)
    (order : List Nat) (buffer : Spec.Bytes) : (bufferSign n st sk a d order buffer).length = buffer.length := by
  unfold bufferSign
  generalize initialRows sk d order = pair
  obtain ⟨ls,q⟩ := pair
  let fuel := signMeasure ls q+1
  let keep := fun (k : Nat) (_ : Nat) (_ : Spec.Bytes) => k
  have sz := writes_sim (rawStore n) keep List.length (by intro o c v; simp [keep,rawStore])
    n st sk a d ls q buffer fuel
  have constant := writes_sim (fun (_ : Unit) _ _ => ()) keep (fun _ => buffer.length) (by intros; rfl)
    n st sk a d ls q () fuel
  exact sz.symm.trans constant

/-- The actual in-order sequence of signature-offset writes refines the chain table
through the initial fill, every four-lane iteration, and every physical tail move. -/
theorem buffer_sign_table (n count : Nat) (st : List Word) (sk : Spec.Bytes) (a : Spec.Adrs)
    (d : Nat → Nat) (order : List Nat) (width : n=16 ∨ n=24 ∨ n=32) :
    bufferSign n st sk a d order (List.replicate (count*n) 0#8) =
      encode n count (initializedRun sk d order (four n st sk a d) (tail n st a)) := by
  unfold bufferSign initializedRun
  cases initialRows sk d order
  dsimp only
  have writes (o c x) (h : x.length=n) : rawStore n (encode n count o) c x = encode n count (setOut o c x) := by
    simpa only [writeBuffer,rawStore,slot_full n x h] using write_encode n count o c x
  have payload (regs : Arm.V × Arm.V) : (outputDigest n regs).length=n := by
    rw [outputDigest,stored_eq n width]; rcases width with rfl|rfl|rfl <;> rfl
  rw [←encode_zero,writes_sim_on setOut (rawStore n) (encode n count) (fun x => x.length=n) writes
    _ _ _ _ _ _ _ _ _ payload,writes_table]

end slhdsa.Armwide.Transitions
