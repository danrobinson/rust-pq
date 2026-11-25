import Parallel.LeafPublications
import Parallel.PhaseTwoWrites
import Parallel.RootTableHosted
open Aeneas Aeneas.Std Result
namespace slhdsa.ParallelLeafTable
open ParallelXmssTicket WidthEight.Ticket ParallelSigning

noncomputable def nodeFor {N : Usize} (host : ParallelRootWalk.Host) (p : params.Params) : Node N :=
  match host with
  | .apple sha3 => hostedNode (.apple sha3) p
  | .x86 => hostedNode .x86 p
  | .linuxArm => WidthThree.linuxNode

theorem node_law {N : Usize} (host : ParallelRootWalk.Host) (p : params.Params) (hp : PN p N) :
    NodeLaw p (nodeFor (N:=N) host p) 512 := by
  cases host with
  | apple sha3 => exact hosted_law (.apple sha3) p hp
  | x86 => exact hosted_law .x86 p hp
  | linuxArm =>
    intro sk i z seed a room
    exact @WidthThree.linuxNodeSpec N p hp sk i z seed a (by omega)

def compute {N : Usize} (node : Node N) (ls : Layers) (sk seed : Array U8 N) (j : Nat) : Result (Array U8 N) := do
  if h : j<2^UScalarTy.U16.numBits then
    let (dest,row) ← leaf_ticket node ls (U16.ofNatCore j h) sk seed
    if dest.val=j then ok row else fail .panic
  else fail .panic

def leaves {N : Usize} (node : Node N) (p : params.Params) (sk seed : Array U8 N) (tree : U64) (leaf : U32)
    (count : Nat) (completed : List Nat) : Result (alloc.vec.Vec (Option (Array U8 N))) := do
  let ls ← build_layers p tree leaf
  let rows ← writeRows count (compute node ls sk seed) completed
  if h : rows.length≤Usize.max then ok (alloc.vec.Vec.from rows h) else fail .panic

theorem leaves_spec {N : Usize} (node : Node N) (p : params.Params) (hp : PN p N) (law : NodeLaw p node 512)
    (sk seed : Array U8 N) (tree : U64) (leaf : U32) (count issued : Nat) (completed : List Nat)
    (size : count≤p.d.val) (bound : leaf.val<2^p.hp.val)
    (trace : Trace count issued [] completed) (drained : count < issued) :
    leaves node p sk seed tree leaf count completed ⦃ slots =>
      ParallelRootWalk.PublishedLeaves (Shake.params p) (bytes sk.val) (bytes seed.val) tree.val leaf.val count slots ⦄ := by
  obtain ⟨ls,built,layout⟩ := spec_imp_exists (layer_table p hp.valid.hp_le tree leaf)
  let value := fun i => Spec.xmssNode (Shake.params p) (bytes sk.val) (loc p.hp.val tree.val leaf.val i).2 0
    (bytes seed.val) (addr i (loc p.hp.val tree.val leaf.val i).1)
  have total (j : Nat) (hj : j<count) : ∃ row, compute node ls sk seed j=ok row ∧ bytes row.val=value j := by
    have d : p.d.val ≤ 22 := hp.valid.d_le
    have small : j<2^UScalarTy.U16.numBits := by change j<65536;omega
    let layer := U16.ofNatCore j small
    have lv : layer.val=j := by simp [layer]
    obtain ⟨⟨dest,v⟩,run,off,data⟩ := spec_imp_exists (leaf_from_layers p hp.valid.hp_le node 512 law
      (Nat.pow_le_pow_right (by decide) hp.valid.hp_le) tree leaf layer sk seed (by omega) bound)
    simp only [built,bind_ok] at run
    refine ⟨v,?_,by simpa only [value,lv] using data⟩
    have eq : dest.val=j := off.trans lv
    simp only [compute,dite_eq_left small]
    change (do let (d,r) ← leaf_ticket node ls layer sk seed; if d.val=j then ok r else fail .panic) = ok v
    rw [run,bind_ok]; exact ite_eq_left eq
  obtain ⟨unique,cover⟩ := (trace.joined drained).exactly_once
  obtain ⟨rows,run,len,fields⟩ := writes count (compute node ls sk seed) (fun j row => bytes row.val=value j) total completed unique (fun j hj => (cover j).mp hj)
  have room : rows.length≤Usize.max := by rw [len];exact size.trans (by scalar_tac)
  simp only [leaves,built,bind_ok,run,dite_eq_left room,WP.spec_ok]
  refine ⟨by change count≤(alloc.vec.Vec.from rows room).val.length;simp [len],?_⟩
  intro j hj
  obtain ⟨row,read,data⟩ := (ite_eq_left ((cover j).mpr hj)) ▸ fields j hj
  exact ⟨row,by simp [alloc.vec.Vec.from_val,List.getElem!_eq_getElem?_getD,read],
    by simpa only [value,show (Shake.params p).hp=p.hp.val from rfl] using data⟩

end slhdsa.ParallelLeafTable
