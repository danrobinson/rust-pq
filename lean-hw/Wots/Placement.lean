import Wots.Store
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.Wots

private theorem selected_byte {L} {before after : Rows L} {key start : Nat} {payload : List U8}
    (h : piece before after key start payload) (room : start ≤ L.val)
    (offset : Nat) (ho : offset < payload.length) :
    after.val[key]!.val[start+offset]! = payload[offset]! := by
  rw [h.2.2]
  have hlen : (before.val[key]!.val.take start).length = start := by simp [Nat.min_eq_left room]
  rw [List.append_assoc,List.getElem!_append_right _ _ _ (by omega),hlen,Nat.add_sub_cancel_left,
    List.getElem!_append_left _ _ _ ho]

theorem placed_lane {N L} (hash : Hash) (before after : Rows L) (len atSlot used : Nat)
    (h : batchWrites (N := N) hash before after len atSlot used) (lo : 16 ≤ len)
    (hu : used ≤ 16) (room : 22+len*N.val ≤ L.val)
    (j : Fin 16) (live : j.val < used) (k : Nat) (hk : k < N.val) :
    (after.val[(atSlot+j.val)/len]!.val[22+((atSlot+j.val)%len)*N.val+k]!).bv =
      Store.digestByte hash j k := by
  let width := min used (len-atSlot%len)
  obtain ⟨staged,mid,digest,first,second⟩ := h
  have pos := destination_spec atSlot len used j.val lo hu live
  dsimp only at pos
  simp only [← show width = min used (len-atSlot%len) from rfl] at pos second first
  have cap := Nat.mod_lt atSlot (by omega : 0<len)
  have wle : width ≤ used := Nat.min_le_left ..
  have firstFits : 22+(atSlot%len)*N.val ≤ L.val := by
    have := Nat.mul_le_mul_right N.val (by omega : atSlot%len ≤ len); omega
  have stageLen : staged.val.length = 16 := by simp
  by_cases front : j.val < width
  · rw [if_pos front] at pos
    have key := congrArg Prod.fst pos
    have slot := congrArg Prod.snd pos
    simp only at key slot
    rw [key,slot]
    let src := staged.val.take width
    have sz : src.length = width := by simp [src,Nat.min_eq_left (by omega : width ≤ 16)]
    have inside : N.val*j.val+k < (src.flatMap (·.val)).length := by
      rw [flat_length,sz]
      have := Nat.mul_le_mul_left N.val (by omega : j.val+1 ≤ width)
      rw [Nat.mul_succ] at this; omega
    have selected := selected_byte first firstFits (N.val*j.val+k) inside
    rw [flat_byte src j.val k (by omega) hk] at selected
    have row : src[j.val]! = staged.val[j.val]! := by
      simp only [src,List.getElem!_eq_getElem?_getD,List.getElem?_take_of_lt front]
    change _ = Store.digestByte hash j k
    have addr : 22+(atSlot%len+j.val)*N.val+k = 22+atSlot%len*N.val+(N.val*j.val+k) := by ring
    rw [addr]
    have same : after.val[atSlot/len]! = mid.val[atSlot/len]! := by
      by_cases cross : width < used
      · rw [if_pos cross] at second
        exact second.2.1 _ (by omega)
      · rw [if_neg cross] at second
        rw [second]
    rw [same,selected,row,digest _ live _ hk]
  · rw [if_neg front] at pos
    have key := congrArg Prod.fst pos
    have slot := congrArg Prod.snd pos
    simp only at key slot
    rw [key,slot]
    have cross : width < used := by omega
    rw [if_pos cross] at second
    let src := (staged.val.drop width).take (used-width)
    have sz : src.length = used-width := by
      simp only [src,List.length_take,List.length_drop,stageLen,Nat.min_eq_left (by omega : used-width ≤ 16-width)]
    let i := j.val-width
    have hi : i < used-width := by dsimp [i]; omega
    have inside : N.val*i+k < (src.flatMap (·.val)).length := by
      rw [flat_length,sz]
      have := Nat.mul_le_mul_left N.val (by omega : i+1 ≤ used-width)
      rw [Nat.mul_succ] at this; omega
    have selected := selected_byte second (by omega) (N.val*i+k) inside
    rw [flat_byte src i k (by omega) hk] at selected
    have row : src[i]! = staged.val[j.val]! := by
      simp only [src,List.getElem!_eq_getElem?_getD,List.getElem?_take_of_lt hi,List.getElem?_drop]
      rw [show width+i=j.val by dsimp [i]; omega]
    have addr : 22+(j.val-width)*N.val+k = 22+(N.val*i+k) := by dsimp [i]; ring
    rw [addr,selected,row,digest _ live _ hk]

theorem piece_frame {L} {before after : Rows L} {key start : Nat} {payload : List U8}
    (h : piece before after key start payload) (room : start ≤ L.val)
    (r b : Nat) (unchanged : r ≠ key ∨ b < start ∨ start+payload.length ≤ b) :
    after.val[r]!.val[b]! = before.val[r]!.val[b]! := by
  by_cases same : r = key
  · subst r
    rw [h.2.2,List.append_assoc]
    have hlen : (before.val[key]!.val.take start).length = start := by simp [Nat.min_eq_left room]
    rcases unchanged with bad|prior|later
    · exact (bad rfl).elim
    · rw [List.getElem!_append_left _ _ _ (by omega),List.getElem!_eq_getElem?_getD,
        List.getElem?_take_of_lt prior,← List.getElem!_eq_getElem?_getD]
    · rw [List.getElem!_append_right _ _ _ (by omega),hlen,List.getElem!_append_right _ _ _ (by omega)]
      simp only [List.getElem!_eq_getElem?_getD,List.getElem?_drop]
      rw [show start+payload.length+(b-start-payload.length) = b by omega]
  · rw [h.2.1 r same]

/-- Every byte outside the live endpoints is preserved, including the 22-byte
address header and the unused suffix of each keypair row. -/
theorem batch_frame {N L} (hash : Hash) (before after : Rows L) (len atSlot used : Nat)
    (h : batchWrites (N := N) hash before after len atSlot used) (lo : 16 ≤ len)
    (hu : used ≤ 16) (positive : 0 < N.val) (room : 22+len*N.val ≤ L.val) (r b : Nat)
    (untouched : ∀ j < used, r ≠ (atSlot+j)/len ∨ b < 22+((atSlot+j)%len)*N.val ∨
      22+((atSlot+j)%len)*N.val+N.val ≤ b) :
    after.val[r]!.val[b]! = before.val[r]!.val[b]! := by
  let width := min used (len-atSlot%len)
  obtain ⟨staged,mid,_,first,second⟩ := h
  simp only [← show width = min used (len-atSlot%len) from rfl] at first second
  have wle : width ≤ used := Nat.min_le_left ..
  have stageLen : staged.val.length = 16 := by simp
  have bound : 22+(atSlot%len)*N.val ≤ L.val := by
    have m := Nat.mod_lt atSlot (by omega : 0<len)
    have := Nat.mul_le_mul_right N.val (by omega : atSlot%len ≤ len); omega
  have unchanged : mid.val[r]!.val[b]! = before.val[r]!.val[b]! := by
    apply piece_frame first bound
    rw [flat_length,List.length_take,stageLen,Nat.min_eq_left (by omega : width ≤ 16)]
    by_contra! inside
    obtain ⟨key,lb,ub⟩ := inside
    let off := b-(22+atSlot%len*N.val)
    let j := off/N.val
    have dj : off < width*N.val := by dsimp [off]; rw [Nat.mul_comm N.val width] at ub; omega
    have front : j < width := (Nat.div_lt_iff_lt_mul positive).mpr dj
    have addr := destination_spec atSlot len used j lo hu (by omega)
    dsimp only at addr
    rw [if_pos front] at addr
    obtain ⟨q,s⟩ := Prod.mk.inj addr
    have no := untouched j (by omega)
    rw [q,s,key,Nat.add_mul] at no
    have split := Nat.mod_add_div off N.val
    have rem := Nat.mod_lt off positive
    have eq : off = b-(22+atSlot%len*N.val) := rfl
    change off%N.val + N.val*j = off at split
    rw [Nat.mul_comm N.val j] at split
    omega
  rw [← unchanged]
  by_cases cross : width < used
  · rw [if_pos cross] at second
    apply piece_frame second (by omega)
    rw [flat_length,List.length_take,List.length_drop,stageLen,Nat.min_eq_left (by omega : used-width ≤ 16-width)]
    by_contra! inside
    obtain ⟨key,lb,ub⟩ := inside
    let off := b-22
    let i := off/N.val
    have di : off < (used-width)*N.val := by dsimp [off]; rw [Nat.mul_comm] at ub; omega
    have hi : i < used-width := (Nat.div_lt_iff_lt_mul positive).mpr di
    have live : width+i < used := by omega
    have addr := destination_spec atSlot len used (width+i) lo hu live
    dsimp only at addr
    rw [if_neg (Nat.not_lt.mpr (Nat.le_add_right width i)),Nat.add_sub_cancel_left] at addr
    obtain ⟨q,s⟩ := Prod.mk.inj addr
    have no := untouched (width+i) live
    rw [q,s,key] at no
    have split := Nat.mod_add_div off N.val
    have rem := Nat.mod_lt off positive
    change off%N.val+N.val*i = off at split
    rw [Nat.mul_comm N.val i] at split
    have eq : off = b-22 := rfl
    omega
  · rw [if_neg cross] at second
    rw [second]

end slhdsa.X86.Wots
