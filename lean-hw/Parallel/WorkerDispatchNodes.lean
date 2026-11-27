import Parallel.WorkerCrypto
import Parallel.WorkerDispatchWrites

open Aeneas Aeneas.Std Result
namespace ParallelDispatchWrites
open ParallelWorkerHeap ParallelWorkerCounterSafety

def directRow (i : Nat) (v : Array U8 N) : Publication N := ⟨.forsDirect i,v⟩
def splitRow (i : Nat) (v : Array U8 N) : Publication N := ⟨.forsSplit i,v⟩

theorem index_physical (N : Usize) (key : Nat → Key) (T : Type) (ty : ∀ j, Payload N (key j)=T)
    (count i : Usize) (live : i.val<count.val) :
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice _) (physicalTable N key T ty count) i =
      ok ⟨key i.val,ty i.val⟩ := by
  simp [alloc.vec.Vec.index_slice_index,alloc.vec.Vec.index_usize,alloc.vec.Vec.getElem?_Nat_eq,
    physicalTable,alloc.vec.Vec.from_val,List.getElem?_map,List.getElem?_range live]

end ParallelDispatchWrites

namespace slhdsa.WorkerCrypto
set_option linter.concreteInstances false

def scalarHost [cfg : Config] : ParallelScalarFors.Platform :=
  match cfg.host with | .apple f => .apple f | .x86 => .x86 | .linuxArm => .linux

theorem direct_eval [cfg : Config] {N : Usize} (sk seed : Array U8 N) (a : address.Adrs)
    (i z : U32) (s : Usize) :
    (ParallelScalarFors.actions scalarHost cfg.p sk seed a).1 i z s =
      (do let v ← node sk i z seed a; ok (s,v)) := by
  cases cfg with | mk host p => cases host <;> rfl

theorem node_value [cfg : Config] {N : Usize} (hp : PN cfg.p N) (sk seed : Array U8 N)
    (a : address.Adrs) (domain : ForsHorizontal.Domain a) (i z : U32)
    (height : z.val≤14) (room : (i.val+1)*2^z.val≤1048576) :
    ∃ row, node sk i z seed a = ok row ∧ bytes row.val =
      Spec.forsNode (Shake.params cfg.p) (bytes sk.val) i.val z.val (bytes seed.val) (adrsS a) := by
  have law := (ParallelScalarFors.native_laws scalarHost cfg.p hp sk seed a domain).1 i z 0#usize height room
  rw [direct_eval] at law
  generalize equal : node sk i z seed a = action at law ⊢
  cases action <;> simp_all [ParallelScalarFors.Writes]

theorem secret_value [cfg : Config] {N : Usize} (hp : PN cfg.p N) (sk seed : Array U8 N)
    (a : address.Adrs) (i : U32) :
    ∃ row, secret sk seed a i = ok row ∧ bytes row.val =
      Spec.forsSkGen (Shake.params cfg.p) (bytes sk.val) (bytes seed.val) (adrsS a) i.val := by
  cases cfg with
  | mk h p =>
    cases h with
    | apple sha => exact spec_imp_exists (ScalarTicketApple.slhdsa.Shake.fors_sk_gen_spec p hp sk seed a i)
    | x86 => exact spec_imp_exists (ScalarTicketX86.slhdsa.Shake.fors_sk_gen_spec p hp sk seed a i)
    | linuxArm => exact spec_imp_exists (ScalarTicketLinux.slhdsa.Shake.fors_sk_gen_spec p hp sk seed a i)

theorem xmss_value [cfg : Config] {N : Usize} (hp : PN cfg.p N) (sk seed : Array U8 N)
    (a : address.Adrs) (i z : U32) (room : (i.val+1)*2^z.val≤512) :
    ∃ row, xmss sk i z seed a = ok row ∧ bytes row.val =
      Spec.xmssNode (Shake.params cfg.p) (bytes sk.val) i.val z.val (bytes seed.val) (adrsS a) :=
  spec_imp_exists (ParallelLeafTable.node_law rootHost cfg.p hp sk i z seed a room)

end slhdsa.WorkerCrypto
