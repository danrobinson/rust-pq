import PeerEquality.Layers

namespace slhdsa.PeerCall

/-- `Array<Option<XmssSig>, D>` materialization, parametric in the complete
child output type, including signatures of every byte length. -/
private def store {A : Type} : List A → Nat → List (Option A) → List (Option A)
  | [],_,slots => slots
  | x::xs,i,slots => store xs (i+1) (slots.set i (some x))

private theorem fills {A : Type} (pre tail : List A) :
    store tail pre.length (pre.map some ++ List.replicate tail.length none) =
      (pre ++ tail).map some := by
  induction tail generalizing pre with
  | nil => simp [store]
  | cons x xs ih =>
    have head := ih (pre ++ [x])
    simp only [List.length_append,List.length_cons,List.length_nil,Nat.zero_add,List.map_append,
      List.map_cons,List.map_nil,List.append_assoc,List.cons_append,List.nil_append] at head
    simp only [store,List.length_cons,List.replicate_succ]
    rw [List.set_append_right (s := pre.map some) pre.length (some x) (by simp)]
    simp only [List.length_map,Nat.sub_self,List.set_cons_zero]
    simpa [List.append_assoc] using head

theorem all_slots {A : Type} (rows : List A) :
    (store rows 0 (List.replicate rows.length none)).mapM id = some rows := by
  have h := fills ([] : List A) rows
  simp only [List.length_nil,List.map_nil,List.nil_append] at h
  rw [h]
  rw [List.mapM_map]
  exact (List.mapM_pure (m := Option) (f := id) (l := rows)).trans (congrArg some (List.map_id rows))

end slhdsa.PeerCall
