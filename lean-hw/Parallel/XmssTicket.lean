import Parallel.XmssTicketProgram
open Aeneas Aeneas.Std Result
namespace slhdsa.ParallelXmssTicket

def NodeLaw {N : Usize} (p : params.Params) (node : Node N) (limit : Nat) :=
  ∀ (sk : Array U8 N) (i z : U32) (seed : Array U8 N) (a : address.Adrs),
    (i.val+1)*2^z.val≤limit → node sk i z seed a ⦃ r =>
      bytes r.val = Spec.xmssNode (Shake.params p) (bytes sk.val) i.val z.val (bytes seed.val) (adrsS a) ⦄

theorem subtree_spec {N : Usize} (p : params.Params) (node : Node N) (limit : Nat) (law : NodeLaw p node limit)
    (layers : alloc.vec.Vec (address.Adrs × U32)) (layer : U16) (idx height : U32) (slot : Usize)
    (sk seed : Array U8 N) (inside : layer.val<layers.length) (room : (idx.val+1)*2^height.val≤limit) :
    subtree_ticket node layers layer idx height slot sk seed ⦃ (dest,r) => dest=slot ∧
      bytes r.val = Spec.xmssNode (Shake.params p) (bytes sk.val) idx.val height.val (bytes seed.val)
        (adrsS layers.val[layer.val]!.1) ⦄ := by
  unfold subtree_ticket
  have cast : (UScalar.cast .Usize layer).val=layer.val := by scalar_tac
  simp only [lift,bind_ok]
  step as ⟨addr,index,read⟩
  all_goals try scalar_tac
  step with law sk idx height seed addr room as ⟨val,correct⟩
  rw [←getElem!_pos,cast] at read
  simp [correct,←read]

theorem leaf_spec {N : Usize} (p : params.Params) (node : Node N) (limit : Nat) (law : NodeLaw p node limit)
    (layers : alloc.vec.Vec (address.Adrs × U32)) (layer : U16)
    (sk seed : Array U8 N) (inside : layer.val<layers.length) (room : layers.val[layer.val]!.2.val+1≤limit) :
    leaf_ticket node layers layer sk seed ⦃ (dest,r) => dest.val=layer.val ∧
      bytes r.val = Spec.xmssNode (Shake.params p) (bytes sk.val) layers.val[layer.val]!.2.val 0 (bytes seed.val)
        (adrsS layers.val[layer.val]!.1) ⦄ := by
  unfold leaf_ticket
  have cast : (UScalar.cast .Usize layer).val=layer.val := by scalar_tac
  simp only [lift,bind_ok]
  step as ⟨addr,index,read⟩
  all_goals try scalar_tac
  rw [←getElem!_pos,cast] at read
  step with law sk index 0#u32 seed addr (by simpa [←read] using room) as ⟨val,correct⟩
  simp [cast,correct,←read]

private theorem linux_law {N : Usize} (p : params.Params) (hp : PN p N) :
    NodeLaw p (WidthThree.linuxNode (N:=N)) (2^32) :=
  fun sk i z seed a h => @WidthThree.linuxNodeSpec N p hp sk i z seed a h

abbrev linux_subtree {N : Usize} (p : params.Params) (hp : PN p N) :=
  @subtree_spec N p _ _ (linux_law p hp)

abbrev linux_leaf {N : Usize} (p : params.Params) (hp : PN p N) :=
  @leaf_spec N p _ _ (linux_law p hp)

end slhdsa.ParallelXmssTicket
