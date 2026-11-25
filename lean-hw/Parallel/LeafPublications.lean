import Parallel.TicketFromLayers
import Parallel.RootTable
open Aeneas Aeneas.Std Result
namespace slhdsa.ParallelXmssTicket

/-- Publication records only the worker call and the slot receiving its return.
The expected cryptographic value follows from the extracted worker and layers. -/
def LeafReturn {N : Usize} (p : params.Params) (node : Node N) (tree : U64) (leaf : U32)
    (sk seed : Array U8 N) (cells : alloc.vec.Vec (Option (Array U8 N))) (j : Nat) : Prop :=
  ∃ (layer : U16) (dest : Usize) (v : Array U8 N), layer.val<p.d.val ∧
    (do let layers ← build_layers p tree leaf
        leaf_ticket node layers layer sk seed) = ok (dest,v) ∧
    dest.val=j ∧ cells.val[j]! = some v

theorem published_leaf_returns {N : Usize} (p : params.Params) (hp : PN p N) (node : Node N)
    (limit : Nat) (law : NodeLaw p node limit) (capacity : 2^p.hp.val≤limit)
    (tree : U64) (leaf : U32) (sk seed : Array U8 N) (count : Nat)
    (cells : alloc.vec.Vec (Option (Array U8 N))) (size : count≤cells.length)
    (bound : leaf.val<2^p.hp.val)
    (writes : ∀ j<count, LeafReturn p node tree leaf sk seed cells j) :
    ParallelRootWalk.PublishedLeaves (Shake.params p) (bytes sk.val) (bytes seed.val)
      tree.val leaf.val count cells := by
  refine ⟨size,?_⟩
  intro j hj
  obtain ⟨layer,dest,v,inside,ran,slot,stored⟩ := writes j hj
  have result := leaf_from_layers p hp.valid.hp_le node limit law capacity tree leaf layer sk seed inside bound
  rw [ran] at result
  obtain ⟨offset,val⟩ := (WP.spec_ok _).mp result
  exact ⟨v,stored,by simpa only [←slot,offset,show (Shake.params p).hp=p.hp.val from rfl] using val⟩

end slhdsa.ParallelXmssTicket
