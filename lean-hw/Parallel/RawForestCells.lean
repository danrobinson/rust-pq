import Parallel.ForestPack
import Parallel.PhaseTwoObserved
open Aeneas Aeneas.Std Result
namespace slhdsa.ParallelRawForest
open ParallelSignJoin

noncomputable def cells {N : Usize} (plan : PhysicalRows) (p : params.Params) (md : Slice U8)
    (sk seed : Array U8 N) (a : address.Adrs) :=
  let rows := ParallelCached.forsRows (Shake.params p) (bytes md.val) (bytes sk.val) (bytes seed.val) (adrsS a)
  boxed ((expand plan.forest).map (fun j => some (fixed N rows[j]!)))

theorem width (p : Spec.Params) (valid : p.Valid) (md sk pk : Spec.Bytes) (a : Spec.Adrs)
    (row : Spec.Bytes) (read : row∈ParallelCached.forsRows p md sk pk a) : row.length=p.n := by
  obtain ⟨j,_,h⟩ := List.mem_flatMap.mp read
  rcases List.mem_cons.mp h with eq | auth
  · subst row;exact Spec.PRF_length p valid .. 
  · obtain ⟨k,_,eq⟩ := List.mem_map.mp auth
    subst row;exact Spec.forsNode_length p valid ..

theorem pack {N : Usize} (plan : PhysicalRows) (p : params.Params) (hp : PN p N)
    (found : lookup (Shake.params p)=some plan) (md : Slice U8) (sk seed : Array U8 N) (a : address.Adrs) :
    ParallelForestPack.pack_fors p (cells plan p md sk seed a) ⦃ out => bytes out.val=
      (ParallelCached.forsRows (Shake.params p) (bytes md.val) (bytes sk.val) (bytes seed.val) (adrsS a)).flatten ⦄ := by
  let P := Shake.params p
  let rows := ParallelCached.forsRows P (bytes md.val) (bytes sk.val) (bytes seed.val) (adrsS a)
  have order : expand plan.forest=List.range rows.length := by rw [(read_order found).1,ParallelCached.fors_length]
  have bound : rows.length≤35*(1+14) := by rw [ParallelCached.fors_length];exact Nat.mul_le_mul hp.valid.k_le (Nat.add_le_add_left hp.valid.a_le _)
  have get : (cells plan p md sk seed a).val=(List.range rows.length).map (fun j => some (fixed N rows[j]!)) := by
    let l := (List.range rows.length).map (fun j => some (fixed N rows[j]!))
    have small : l.length≤Usize.max := by simp only [l,List.length_map,List.length_range];scalar_tac
    change (boxed ((expand plan.forest).map _)).val=l
    rw [order];change (boxed l).val=l;simp [boxed,List.take_of_length_le small]
  have count : (cells plan p md sk seed a).length=rows.length := by change (cells ..).val.length=_;simp [get]
  rw [ParallelCached.fors_bytes]
  apply ParallelForestPack.pack_fips p hp _ _ _ _ _ (count.trans (ParallelCached.fors_length ..))
  intro i hi
  rw [count] at hi
  have chosen : rows[i]! ∈ rows := by rw [getElem!_pos rows i hi];apply List.getElem_mem
  have len := (width P (Suite.valid .shake hp) _ _ _ _ _ chosen).trans hp.n
  refine ⟨fixed N rows[i]!,?_,?_⟩
  · simp [get,hi]
  · change bytes (fixed N rows[i]!).val=rows[i]!
    rw [fixed,dif_pos len];simp [raw,bytes,Function.comp_def]

end slhdsa.ParallelRawForest
