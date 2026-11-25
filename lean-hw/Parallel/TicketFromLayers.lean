import Parallel.TicketLayers
import Parallel.XmssTicketHosted
import Parallel.SignTicket

open Aeneas Aeneas.Std Result
namespace slhdsa.ParallelXmssTicket
open ParallelSigning

private theorem leaf_bound (hp tree leaf j : Nat) (bound : leaf<2^hp) : (loc hp tree leaf j).2 < 2^hp := by
  cases j with
  | zero => exact bound
  | succ k => exact Nat.mod_lt _ (Nat.two_pow_pos _)

/-- Produce both the table and the worker value. The ticket reads its actual
layer address from the table allocated and filled by the signing driver. -/
theorem subtree_from_layers {N : Usize} (p : params.Params) (heightOk : p.hp.val≤9)
    (node : Node N) (limit : Nat) (law : NodeLaw p node limit) (tree : U64) (leaf : U32)
    (layer : U16) (idx height : U32) (slot : Usize) (sk seed : Array U8 N)
    (inside : layer.val<p.d.val) (room : (idx.val+1)*2^height.val≤limit) :
    (do let layers ← build_layers p tree leaf
        subtree_ticket node layers layer idx height slot sk seed) ⦃ (dest,r) => dest=slot ∧
      bytes r.val=Spec.xmssNode (Shake.params p) (bytes sk.val) idx.val height.val (bytes seed.val)
        (addr layer.val (loc p.hp.val tree.val leaf.val layer.val).1) ⦄ := by
  step with layer_table p heightOk tree leaf as ⟨rows,table⟩
  obtain ⟨length,cells⟩ := table
  apply WP.spec_mono (subtree_spec p node limit law rows layer idx height slot sk seed (length.symm ▸ inside) room)
  rintro ⟨dest,r⟩ ⟨slotEq,value⟩
  have addrEq := congrArg Prod.fst (cells _ inside)
  dsimp only at addrEq
  exact ⟨slotEq,by rw [value,addrEq]⟩

theorem leaf_from_layers {N : Usize} (p : params.Params) (heightOk : p.hp.val≤9)
    (node : Node N) (limit : Nat) (law : NodeLaw p node limit) (capacity : 2^p.hp.val≤limit)
    (tree : U64) (leaf : U32) (layer : U16) (sk seed : Array U8 N)
    (inside : layer.val<p.d.val) (bounded : leaf.val<2^p.hp.val) :
    (do let layers ← build_layers p tree leaf
        leaf_ticket node layers layer sk seed) ⦃ (dest,r) => dest.val=layer.val ∧
      bytes r.val=Spec.xmssNode (Shake.params p) (bytes sk.val) (loc p.hp.val tree.val leaf.val layer.val).2
        0 (bytes seed.val) (addr layer.val (loc p.hp.val tree.val leaf.val layer.val).1) ⦄ := by
  step with layer_table p heightOk tree leaf as ⟨rows,table⟩
  obtain ⟨length,cells⟩ := table
  have addrEq := congrArg Prod.fst (cells _ inside)
  have idxEq := congrArg Prod.snd (cells _ inside)
  dsimp only at addrEq idxEq
  have room := (leaf_bound p.hp.val tree.val leaf.val layer.val bounded).trans_le capacity
  apply WP.spec_mono (leaf_spec p node limit law rows layer sk seed (length.symm ▸ inside) (by omega))
  rintro ⟨dest,r⟩ ⟨slotEq,value⟩
  exact ⟨slotEq,by rw [value,addrEq,idxEq]⟩

/-- The phase-two Linux WOTS ticket uses the very same address table as the
phase-one XMSS computations. Its only message input is the published root. -/
theorem wots_from_layers {N : Usize} (p : params.Params) (hp : PN p N) (tree : U64) (leaf : U32)
    (roots : alloc.vec.Vec (Array U8 N)) (j : Usize) (sk seed : Array U8 N)
    (inside : j.val<p.d.val) (root : j.val<roots.length) :
    (do let layers ← build_layers p tree leaf
        ParallelSignTicket.ticket layers roots j sk seed) ⦃ r =>
        bytes r.val=Spec.wotsSign (Shake.params p) (bytes roots.val[j.val]!.val) (bytes sk.val)
          (bytes seed.val) { (addr j.val (loc p.hp.val tree.val leaf.val j.val).1).setTypeAndClear Spec.WOTS_HASH with
            keypair := (loc p.hp.val tree.val leaf.val j.val).2 } ⦄ := by
  step with layer_table p hp.valid.hp_le tree leaf as ⟨rows,table⟩
  obtain ⟨length,cells⟩ := table
  have addrEq := congrArg Prod.fst (cells _ inside)
  have idxEq := congrArg Prod.snd (cells _ inside)
  dsimp only at addrEq idxEq
  step with ParallelSignTicket.ticket_spec p hp rows roots j sk seed (length.symm ▸ inside) root as ⟨r,value⟩
  rw [value,addrEq,idxEq]

end slhdsa.ParallelXmssTicket
