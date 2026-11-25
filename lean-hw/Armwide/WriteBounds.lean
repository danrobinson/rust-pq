import Armwide.SignatureBuffer
namespace slhdsa.Armwide.Transitions
open WotsRefill Spec.SHA256
set_option maxHeartbeats 1500000
set_option maxRecDepth 8192

/-- Accumulate success across every address used by a real signature store. -/
def checkStore (n count : Nat) (prev : Bool) (c : Nat) (x : Spec.Bytes) :=
  prev && decide (c*n+x.length ≤ count*n)

private instance : Inhabited SignLane := ⟨⟨[],0,0,0,false⟩⟩
private instance : Inhabited Stepping := ⟨⟨0,⟨[],0,0,0,false⟩,[]⟩⟩

private def Good (count : Nat) (ls : List SignLane) := ∀ l ∈ ls, l.chain < count
private def Ids (count : Nat) (q : List Nat) := ∀ c ∈ q, c<count
private def Ready (n count : Nat) (ls : List Stepping) :=
  ∀ s ∈ ls, s.before.chain<count ∧ s.digest.length=n

private theorem fits {n count c : Nat} (x : Spec.Bytes) (size : x.length=n) (bound : c<count) :
    checkStore n count true c x = true := by
  have room := Nat.mul_le_mul_right n (show c+1 ≤ count by omega)
  simpa [checkStore,size,Nat.add_mul] using room

private theorem transition_safe (n count : Nat) (sk : Spec.Bytes) (d : Nat → Nat) (shared : Bool) (k : Nat)
    (s : Stepping) (q : List Nat) (chain : s.before.chain < count) (size : s.digest.length=n) (ids : Ids count q) :
    let (row,q',safe) := transitionWith (checkStore n count) sk d shared k s q true
    row.chain<count ∧ Ids count q' ∧ safe=true := by
  have write := fits s.digest size chain
  have idx : s.physical.val ≠ 4 := by have := s.physical.isLt; omega
  cases q with
  | nil =>
    cases shared <;> simp only [transitionWith,post_correct,postSpec,List.isEmpty_nil,Bool.not_true,Bool.and_false,
      Bool.false_eq_true,↓reduceIte,idx,List.drop_nil,List.foldl_nil,List.foldl_cons,write,chain,true_and,Ids]
      <;> split_ifs <;> simp [idx,write,chain]
  | cons i q =>
    have head := ids i (by simp)
    have rest : Ids count q := fun c hc => ids c (by simp [hc])
    cases shared <;> simp only [transitionWith,post_correct,postSpec,List.isEmpty_cons,Bool.not_false,Bool.and_true]
      <;> split_ifs <;> simp_all [List.head!,List.head?,Ids]

private theorem before_compact_safe (n count : Nat) (sk : Spec.Bytes) (d : Nat → Nat) (shared : Bool) (k : Nat)
    (ls : List Stepping) (q : List Nat) (ready : Ready n count ls) (ids : Ids count q) :
    let (rows,q',safe) := uncompactedWith (checkStore n count) sk d shared k ls q true
    rows.length=ls.length ∧ Good count rows ∧ Ids count q' ∧ safe=true := by
  induction ls generalizing q with
  | nil => exact ⟨rfl,by simp [Good],ids,rfl⟩
  | cons l ls ih =>
    have h := ready l (by simp)
    have current := transition_safe n count sk d shared k l q h.1 h.2 ids
    cases head : transitionWith (checkStore n count) sk d shared k l q true with
    | mk row tail =>
      obtain ⟨q',b⟩ := tail
      rw [head] at current
      obtain ⟨valid,next,rfl⟩ := current
      have rest := ih q' (fun r hr => ready r (by simp [hr])) next
      cases done : uncompactedWith (checkStore n count) sk d shared k ls q' true with
      | mk rows result =>
        rw [done] at rest
        simp only [uncompactedWith,head,done]
        exact ⟨by simp [rest.1],by simpa [Good] using And.intro valid rest.2.1,rest.2.2⟩

private theorem kept_indices (k : Count) (keep phase : Nat → Bool) :
    (actual k keep phase).kept.length ≤ width k ∧
    (∀ r ∈ (actual k keep phase).kept, r.chain < width k) ∧
    (∀ e ∈ (actual k keep phase).writes, e.chain < width k ∧ e.x < width k) := by
  rw [active_step]
  refine ⟨?_,?_,?_⟩
  · simpa [blueprint] using (List.length_filter_le keep (List.range (width k)))
  · intro r mem
    obtain ⟨i,member,rfl⟩ := List.mem_map.mp mem
    exact List.mem_range.mp (List.mem_filter.mp member).1
  · intro e mem
    simp only [blueprint] at mem
    split at mem
    · obtain ⟨i,member,rfl⟩ := List.mem_map.mp mem
      have hi := List.mem_range.mp (List.mem_filter.mp member).1
      exact ⟨hi,hi⟩
    · contradiction

private theorem compact_safe (n count : Nat) (sk : Spec.Bytes) (d : Nat → Nat) (shared : Bool) (k : Nat)
    (ls : List Stepping) (q : List Nat) (ready : Ready n count ls) (ids : Ids count q) (size : ls.length=4) :
    let (rows,q',safe) := compactWithWriter (checkStore n count) sk d shared k ls q true
    rows.length≤4 ∧ Good count rows ∧ Ids count q' ∧ safe=true := by
  have complete := before_compact_safe n count sk d shared k ls q ready ids
  unfold compactWithWriter
  cases h : uncompactedWith (checkStore n count) sk d shared k ls q true with
  | mk rows pair =>
    rw [h] at complete
    have valid := kept_indices 3 (fun i => rows[i]!.left ≠ 0) (fun i => rows[i]!.isPrf)
    refine ⟨by rw [List.length_map]; exact valid.1,?_,complete.2.2⟩
    intro l hl
    obtain ⟨r,reg,rfl⟩ := List.mem_map.mp hl
    have ri := valid.2.1 r reg
    change r.chain < 4 at ri
    have bound : r.chain < rows.length := by rw [complete.1,size]; exact ri
    change rows[r.chain]!.chain < count
    apply complete.2.1 rows[r.chain]!
    rw [getElem!_pos rows _ bound]; exact List.getElem_mem ..

private theorem rows_ready (n count : Nat) (widthOK : n=16 ∨ n=24 ∨ n=32) (st : List Word)
    (a : Spec.Adrs) (ls : List SignLane) (mode : Mode) (size : lanes mode=ls.length) (valid : Good count ls) :
    Ready n count (steps n st a ls mode) := by
  intro s h
  obtain ⟨j,b,e⟩ := List.mem_iff_getElem.mp h
  rw [←e]
  simp only [steps,List.getElem_ofFn]
  have hi : j<ls.length := by simpa [steps,size] using b
  refine ⟨?_,?_⟩
  · apply valid; rw [getElem!_pos ls j hi]; exact List.getElem_mem ..
  · rw [outputDigest,stored_eq n widthOK]; rcases widthOK with rfl|rfl|rfl <;> rfl

private theorem full_safe (n count : Nat) (widthOK : n=16 ∨ n=24 ∨ n=32) (st : List Word)
    (sk : Spec.Bytes) (a : Spec.Adrs) (d : Nat → Nat) (ls : List SignLane) (q : List Nat)
    (good : Good count ls) (ids : Ids count q) (size : ls.length=4) :
    let (rows,q',safe) := fourWith (checkStore n count) n st sk a d ls q true
    rows.length≤4 ∧ Good count rows ∧ Ids count q' ∧ safe=true := by
  cases phase : ls.any (·.isPrf) <;> simp only [fourWith,phase,Bool.false_eq_true,↓reduceIte]
  · simpa only using compact_safe n count sk d true (signMinLeft ls)
      (steps n st a ls (chooseShared (signMinLeft ls))) q
      (rows_ready n count widthOK st a ls _ size.symm good) ids (by simp [steps,chooseShared,lanes])
  · simpa only using compact_safe n count sk d false 1 (steps n st a ls (.mixed 3)) q
      (rows_ready n count widthOK st a ls _ size.symm good) ids (by simp [steps,lanes])

private theorem fold_safe (n count : Nat) (es : List Event) (rows : List Stepping)
    (ready : Ready n count rows) (idx : ∀ e ∈ es, e.chain < rows.length ∧ e.x < rows.length) :
    es.foldl (fun ok e => checkStore n count ok rows[e.chain]!.before.chain rows[e.x]!.digest) true = true := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    have b := idx e (by simp)
    have one := ready rows[e.chain]! (by rw [getElem!_pos rows _ b.1]; exact List.getElem_mem ..)
    have two := ready rows[e.x]! (by rw [getElem!_pos rows _ b.2]; exact List.getElem_mem ..)
    rw [List.foldl_cons,fits _ two.2 one.1]
    exact ih (fun e h => idx e (by simp [h]))

private theorem tail_safe (n count : Nat) (widthOK : n=16 ∨ n=24 ∨ n=32) (st : List Word)
    (a : Spec.Adrs) (ls : List SignLane) (good : Good count ls) (pos : 0 < ls.length) (short : ls.length < 4) :
    let (rows,safe) := tailWith (checkStore n count) n st a ls true
    rows.length≤4 ∧ Good count rows ∧ safe=true := by
  let k : Count := ⟨(ls.length-1)%4,Nat.mod_lt _ (by decide)⟩
  have size : width k=ls.length := by change (ls.length-1)%4+1=ls.length; rw [Nat.mod_eq_of_lt (by omega)]; omega
  let rows := steps n st a ls (chooseMixed ls.length)
  have ready := rows_ready n count widthOK st a ls (chooseMixed ls.length) size good
  have len : rows.length=width k := by simp [rows,steps,lanes,chooseMixed,k,width]
  let tr := actual k (fun i => 1 < rows[i]!.before.left) (fun i => rows[i]!.before.isPrf)
  have valid := kept_indices k (fun i => 1 < rows[i]!.before.left) (fun i => rows[i]!.before.isPrf)
  change (tr.kept.map (tailRow rows)).length≤4 ∧ Good count (tr.kept.map (tailRow rows)) ∧ _
  refine ⟨by rw [List.length_map]; exact valid.1.trans (by omega),?_,fold_safe n count tr.writes rows ready (by simpa only [len] using valid.2.2)⟩
  intro l mem
  obtain ⟨r,e,rfl⟩ := List.mem_map.mp mem
  have b := valid.2.1 r e
  have hi : r.chain<rows.length := by omega
  exact (ready rows[r.chain]! (by rw [getElem!_pos rows _ hi]; exact List.getElem_mem ..)).1

private theorem run_safe (n count : Nat) (widthOK : n=16 ∨ n=24 ∨ n=32) (st : List Word)
    (sk : Spec.Bytes) (a : Spec.Adrs) (d : Nat → Nat) (ls : List SignLane) (q : List Nat)
    (good : Good count ls) (ids : Ids count q) (size : ls.length≤4) (fuel : Nat) :
    writeRun (checkStore n count) n st sk a d ls q true fuel=true := by
  induction fuel generalizing ls q with
  | zero => rfl
  | succ k ih =>
    simp only [writeRun]
    split
    · rename_i four
      have ok := full_safe n count widthOK st sk a d ls q good ids four
      cases e : fourWith (checkStore n count) n st sk a d ls q true with
      | mk next pair =>
        obtain ⟨queue,b⟩ := pair
        rw [e] at ok
        obtain ⟨len,hls,hq,rfl⟩ := ok
        exact ih next queue hls hq len
    · split
      · rename_i pos
        have ok := tail_safe n count widthOK st a ls good pos (by omega)
        cases e : tailWith (checkStore n count) n st a ls true with
        | mk next b =>
          rw [e] at ok
          obtain ⟨len,hls,rfl⟩ := ok
          exact ih next q hls ids len
      · rfl

/-- Every physical retirement write has room for its entire digest. The audit bit
covers all stores, including writes whose contents could later be overwritten. -/
theorem all_writes_fit (n count : Nat) (widthOK : n=16 ∨ n=24 ∨ n=32) (st : List Word)
    (sk : Spec.Bytes) (a : Spec.Adrs) (d : Nat → Nat) (order : List Nat) (ids : ∀ c ∈ order, c<count) :
    let (ls,q) := initialRows sk d order
    writeRun (checkStore n count) n st sk a d ls q true (signMeasure ls q+1) = true := by
  rw [initial_rows_eq]
  apply run_safe _ _ widthOK
  · intro l hl
    obtain ⟨i,h,rfl⟩ := List.mem_map.mp hl
    exact ids i (List.mem_of_mem_take h)
  · exact fun i h => ids i (List.mem_of_mem_drop h)
  · simp

private def checked (n room : Nat) (o : Spec.Bytes × Bool) (c : Nat) (x : Spec.Bytes) :=
  (rawStore n o.1 c x, o.2 && decide (c*n+x.length ≤ room))

/-- The flag stays true exactly while each selected sub-slice contains a full digest. -/
def checkedSign (n : Nat) (st : List Word) (sk : Spec.Bytes) (a : Spec.Adrs) (d : Nat → Nat)
    (order : List Nat) (buffer : Spec.Bytes) :=
  let (ls,q) := initialRows sk d order
  writeRun (checked n buffer.length) n st sk a d ls q (buffer,true) (signMeasure ls q+1)

theorem checked_value (n : Nat) (st : List Word) (sk : Spec.Bytes) (a : Spec.Adrs) (d : Nat → Nat)
    (order : List Nat) (buffer : Spec.Bytes) :
    (checkedSign n st sk a d order buffer).1 = bufferSign n st sk a d order buffer := by
  unfold checkedSign bufferSign
  cases initialRows sk d order with
  | mk ls q =>
    exact (writes_sim (checked n buffer.length) (rawStore n) Prod.fst (fun _ _ _ => rfl)
      n st sk a d ls q (buffer,true) _).symm

theorem checked_success (n count : Nat) (widthOK : n=16 ∨ n=24 ∨ n=32) (st : List Word)
    (sk : Spec.Bytes) (a : Spec.Adrs) (d : Nat → Nat) (order : List Nat) (buffer : Spec.Bytes)
    (size : buffer.length=count*n) (ids : ∀ c ∈ order, c<count) :
    (checkedSign n st sk a d order buffer).2=true := by
  have target := all_writes_fit n count widthOK st sk a d order ids
  unfold checkedSign
  rw [size]
  cases init : initialRows sk d order with
  | mk ls q =>
    rw [init] at target
    exact (writes_sim (checked n (count*n)) (checkStore n count) Prod.snd (fun _ _ _ => rfl)
      n st sk a d ls q (buffer,true) _).symm.trans target

end slhdsa.Armwide.Transitions
