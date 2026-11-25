import Parallel.RawSlotOrder
import Parallel.AuthTableJobs
import Parallel.PhaseTwoObserved
open Aeneas Aeneas.Std Result
namespace slhdsa.ParallelRawChunks
open ParallelXmssTicket ParallelSigning ParallelAuthTable ParallelSignJoin
set_option maxHeartbeats 2000000

def word (n : Nat) : U32 := ⟨BitVec.ofNat 32 n⟩
def size (n : Nat) : Usize := ⟨BitVec.ofNat _ n⟩
theorem word_val (n : Nat) (h : n<2^32) : (word n).val=n := Nat.mod_eq_of_lt h
theorem size_val (n : Nat) (h : n<2^UScalarTy.Usize.numBits) : (size n).val=n := Nat.mod_eq_of_lt h

def rowInfo (p : params.Params) (layers : Layers) (q : Nat) :=
  let w := p.hp.val
  let layer := size (q/w)
  issuedMetadata p layer layers.val[layer.val]!.2 (word (q%w)) (size (offset w q))

noncomputable def rowChunk {N : Usize} (p : params.Params) (node : Node N) (layers : Layers)
    (sk seed : Array U8 N) (key : Nat × Nat) := do
  let w := p.hp.val
  let (dest,row) ← issuedNode p node layers (size (key.1/w)) (word (key.1%w))
    (size key.2) (size (offset w key.1)) sk seed
  if dest.val=offset w key.1+key.2 then ok (some row) else fail .panic

noncomputable def produce {N : Usize} (p : params.Params) (node : Node N) (layers : Layers) (sk seed : Array U8 N) (schedule : ∀ n, WidthEight.Ticket.Schedule n) := do
  let n := p.d.val*p.hp.val
  let metaRows ← collect (rowInfo p layers) (List.range n)
  let coords := slots p.hp.val n
  let chunks ← fill (rowChunk p node layers sk seed) coords (schedule coords.length)
  ok (boxed metaRows,boxed chunks)

theorem leaf_bounded (w tree leaf j : Nat) (bound : leaf<2^w) : (loc w tree leaf j).2<2^w := by
  cases j with
  | zero => exact bound
  | succ i => exact Nat.mod_lt _ (Nat.two_pow_pos _)

structure Geometry (p : params.Params) (layers : Layers) (q : Nat) : Prop where
  layer : (size (q/p.hp.val)).val=q/p.hp.val
  height : (word (q%p.hp.val)).val=q%p.hp.val
  start : (size (offset p.hp.val q)).val=offset p.hp.val q
  live : q/p.hp.val<layers.length
  narrow : q/p.hp.val<65536
  below : q%p.hp.val<p.hp.val
  index : layers.val[q/p.hp.val]!.2.val<2^p.hp.val
  fits : offset p.hp.val q+2^depth p.hp.val (q%p.hp.val)≤Usize.max

theorem geometry {N : Usize} (p : params.Params) (hp : PN p N) (tree leaf : Nat) (bound : leaf<2^p.hp.val)
    (layers : Layers) (layout : LayerTable p.hp.val tree leaf p.d.val layers) (q : Nat) (row : q<p.d.val*p.hp.val) :
    Geometry p layers q := by
  have hw : 0<p.hp.val := hp.valid.hp_pos
  have hx : p.hp.val≤9 := hp.valid.hp_le
  have dx : p.d.val≤22 := hp.valid.d_le
  have jl : q/p.hp.val<p.d.val := (Nat.div_lt_iff_lt_mul hw).mpr row
  have hl := Nat.mod_lt q hw
  have limit := capacity p.hp.val (p.d.val*p.hp.val) hw hx
  have total : p.d.val*p.hp.val ≤22*9 := Nat.mul_le_mul dx hx
  have inside := @room p.hp.val (p.d.val*p.hp.val) q row
  have fit : offset p.hp.val q+2^depth p.hp.val (q%p.hp.val)≤Usize.max := by scalar_tac
  refine ⟨size_val _ (by scalar_tac),word_val _ (by omega),size_val _ (by exact lt_of_le_of_lt ((Nat.le_add_right ..).trans fit) (by scalar_tac : Usize.max < 2^UScalarTy.Usize.numBits)),
    layout.1 ▸ jl,by omega,hl,?_,fit⟩
  have pos := congrArg Prod.snd (layout.2 (q/p.hp.val) jl)
  dsimp only at pos
  rw [pos];exact leaf_bounded _ _ _ _ bound

theorem info_returns {N : Usize} (p : params.Params) (hp : PN p N) (layers : Layers) (q : Nat)
    (g : Geometry p layers q) : ∃ m, rowInfo p layers q=ok m := by
  obtain ⟨args,call,_⟩ := spec_imp_exists (chunk_spec p (size (q/p.hp.val)) layers.val[(size (q/p.hp.val)).val]!.2
    (word (q%p.hp.val)) 0#usize (size (offset p.hp.val q)) hp.valid.hp_le (by simpa only [g.height] using g.below)
    (by simpa only [g.layer] using g.index) (by simpa only [g.layer] using g.narrow) (Nat.two_pow_pos _) (by simpa only [g.start,g.height] using g.fits))
  rcases args with ⟨_,r,sp,h,first,_,_,_,_⟩
  exact ⟨⟨first,sp,r,h⟩,by simp only [rowInfo,issuedMetadata,call,bind_tc_eq,bind_ok]⟩

theorem chunk_returns {N : Usize} (p : params.Params) (hp : PN p N) (node : Node N) (law : NodeLaw p node 512)
    (layers : Layers) (sk seed : Array U8 N) (q c : Nat) (g : Geometry p layers q)
    (hc : c<2^depth p.hp.val (q%p.hp.val)) :
    ∃ dest row, issuedNode p node layers (size (q/p.hp.val)) (word (q%p.hp.val)) (size c) (size (offset p.hp.val q)) sk seed=ok (dest,row) ∧
      dest.val=offset p.hp.val q+c ∧ rowChunk p node layers sk seed (q,c)=ok (some row) := by
  have cv : (size c).val=c := size_val _ (by have := g.fits;scalar_tac)
  obtain ⟨⟨dest,row⟩,run,whereAt,_⟩ := spec_imp_exists
    (issued_subtree p hp node law layers (size (q/p.hp.val)) layers.val[(size (q/p.hp.val)).val]!.2 (word (q%p.hp.val))
      (size c) (size (offset p.hp.val q)) sk seed (by simpa only [g.layer] using g.live) rfl (by simpa only [g.layer] using g.narrow) (by simpa only [g.height] using g.below)
      (by simpa only [g.layer] using g.index) (by simpa only [cv,g.height] using hc) (by simpa only [g.start,g.height] using g.fits))
  refine ⟨dest,row,run,by simpa only [g.start,cv] using whereAt,?_⟩
  unfold rowChunk
  dsimp only
  change issuedNode p node layers _ _ _ _ sk seed=_ at run
  simp only [run,bind_tc_eq,bind_ok,whereAt,g.start,cv,ite_true]

end slhdsa.ParallelRawChunks
