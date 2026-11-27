import Parallel.CacheAssembly
import Parallel.CacheTickets

namespace ParallelCached.Tickets
open Spec slhdsa.cache.endtoend

def valued (jobs : List (List Nat)) (want : Nat → V) : List (List (Nat × V)) :=
  jobs.map (fun slots => slots.map (fun s => (s,want s)))

private theorem valued_slots (jobs : List (List Nat)) (want : Nat → V) :
    ((valued jobs want).flatten.map Prod.fst) = jobs.flatten := by
  induction jobs with
  | nil => rfl
  | cons first rest ih =>
    simp only [valued,List.map_cons,List.flatten_cons,List.map_append,List.map_map] at ih ⊢
    simpa [Function.comp_def] using congrArg (first++·) ih

private theorem valued_writes (jobs : List (List Nat)) (want : Nat → V) :
    writes (valued jobs want) = planWrites jobs (fun _ => want) := by
  funext i
  simp only [writes,valued,planWrites,List.getElem?_map]
  cases jobs[i]? <;> rfl

/-- Normal completion of the worker loops, including unsuccessful exit tickets,
supplies the joined ledger consumed by the extracted caller. -/
theorem ticket_join {jobs : List (List Nat)} (want : Nat → V) {workers st total}
    (run : Reach (valued jobs want) workers st) (positive : 0<workers)
    (geometry : jobs.flatten.Perm (List.range total))
    (stopped : ¬∃ next, Step (valued jobs want) st next) :
    st.counter=jobs.length+workers ∧ Run jobs.length (planWrites jobs (fun _ => want)) jobs.length [] st.cells := by
  have owns := geometry.nodup_iff.mpr List.nodup_range
  obtain ⟨count,_,joined⟩ := maximal_join run positive (by rw [valued_slots]; exact owns) stopped
  rw [valued_writes] at joined
  simpa [valued] using And.intro count joined

theorem ticket_signature (p : Params) (valid : p.Valid) (msg sk addrnd : Bytes)
    (top : List Bytes) (hit : Option (List Bytes)) (jobs : List (List Nat))
    (geometry : jobs.flatten.Perm (List.range (activeLayers p hit*p.hp+p.k*(1+p.a))))
    (topValid : SpecTreeOk p (block p sk 0) (block p sk 2) (layerAdrs (p.d-1) 0) top)
    (hitValid : ∀ d2, hit=some d2 → SpecTreeOk p (block p sk 0) (block p sk 2)
      (layerAdrs (p.d-2) ((signInputs p msg sk addrnd).tree >>> ((p.d-2)*p.hp))) d2) :
    let input := signInputs p msg sk addrnd
    let want := desired p input.md (block p sk 0) (block p sk 2) input.address input.tree input.leaf hit
    ∀ {workers st}, 0<workers → Reach (valued jobs want) workers st →
      (¬∃ next, Step (valued jobs want) st next) →
      assemble p input.randomizer input.md (block p sk 0) (block p sk 2) input.address
        input.tree input.leaf top hit st.cells = slhSignInternal p msg sk addrnd := by
  intro input want workers st positive run stopped
  have joined := (ticket_join want run positive geometry stopped).2
  exact (complete_signature p valid msg sk addrnd top hit jobs geometry topValid hitValid
    joined (Nat.le_refl _)).2 _ .done

end ParallelCached.Tickets
