import Parallel.ForsReducedReceipt
open Aeneas Aeneas.Std Result
namespace slhdsa.ForsMetadata
open ParallelForsMerge (Meta)

private abbrev Window (N : Usize) := Slice (Option (Array U8 N))

private def window {N} (cells : Cells N) (start count : Usize) : Result (Window N) := do
  let stop ← start+count
  alloc.vec.Vec.index (core.slice.index.SliceIndexRangeUsizeSlice _) cells {start:=start,«end»:=stop}

private theorem window_spec {N} (cells : Cells N) (start count : Usize) (fits : start.val+count.val≤cells.length) :
    window cells start count ⦃ s => s.length=count.val ∧ ∀ i<count.val, s.val[i]! = cells.val[start.val+i]! ⦄ := by
  have cap : cells.length≤Usize.max := cells.len_ineq
  unfold window
  step as ⟨stop,stopEq⟩
  step as ⟨s,rows,size⟩
  all_goals try scalar_tac
  refine ⟨by omega,?_⟩
  intro i hi
  rw [rows,List.getElem!_slice]
  change stop.val≤cells.length ∧ start.val+i<stop.val
  omega

private theorem window_bind {N} {α : Type} (cells : Cells N) (start count : Usize) (s : Window N)
    (run : window cells start count=ok s) (f : Window N→Result α) :
    (do let i ← start+count
        let r ← alloc.vec.Vec.index (core.slice.index.SliceIndexRangeUsizeSlice _) cells {start:=start,«end»:=i}
        f r)=f s := by
  simpa only [window,bind_tc_eq,Std.bind_assoc,bind_ok] using congrArg (fun x : Result (Window N) => x >>= f) run

/-- The native merger observes only the reserved consecutive cells, even for
partially initialized tables and for reductions which return an error. -/
theorem merge_rebase {N} (host : ParallelScalarFors.Platform) (m : Meta) (atSlot : Usize)
    (global buf : Cells N) (seed : Array U8 N) (addr : address.Adrs) (stride : Usize)
    (fits : m.slot_start.val+m.chunks.val≤global.length) (room : atSlot.val+m.chunks.val≤buf.length)
    (same : ∀ c<m.chunks.val, global.val[m.slot_start.val+c]! = buf.val[atSlot.val+c]!) :
    merge host m global seed addr stride=merge host {m with slot_start:=atSlot} buf seed addr stride := by
  obtain ⟨gs,gcall,glen,grows⟩ := spec_imp_exists (window_spec global m.slot_start m.chunks fits)
  obtain ⟨ls,lcall,llen,lrows⟩ := spec_imp_exists (window_spec buf atSlot m.chunks room)
  have slices : gs=ls := by
    apply Slice.ext
    apply List.ext_getElem (glen.trans llen.symm)
    intro i hg hl
    have hi : i<m.chunks.val := glen ▸ hg
    rw [←getElem!_pos gs.val i hg,←getElem!_pos ls.val i hl,grows i hi,lrows i hi,same i hi]
  cases host <;>
    simp only [merge,RootTableApple.ForsMerge.slhdsa.ParallelForsMerge.merge_fors,
      RootTableArm.ForsMerge.slhdsa.ParallelForsMerge.merge_fors,
      RootTableX86.ForsMerge.slhdsa.ParallelForsMerge.merge_fors] <;>
    rw [window_bind _ _ _ _ gcall,window_bind _ _ _ _ lcall,slices]
end slhdsa.ForsMetadata
namespace slhdsa.ForsMetadata
open ParallelForsMerge (Meta)

/-- Metadata generated for a lane selects the same cells relative to the
reservation, including lanes after the first in a grouped ticket. -/
theorem emitted_rebase {N} (host : ParallelScalarFors.Platform) (choices : alloc.vec.Vec U32)
    (a j sub : U32) (first active base : Nat) (oldG outG oldL outL : Table)
    (issuedG : Emitted choices a j sub first active base oldG outG)
    (issuedL : Emitted choices a j sub first active 0 oldL outL)
    (global buf : Cells N) (seed : Array U8 N) (addr : address.Adrs) (stride : Usize)
    (lane : Nat) (live : lane<active) (fits : base+active*2^(j.val-sub.val)≤global.length)
    (room : active*2^(j.val-sub.val)≤buf.length)
    (same : ∀ i<active*2^(j.val-sub.val), global.val[base+i]! = buf.val[i]!) :
    merge host outG.val[oldG.length+lane]! global seed addr stride =
    merge host outL.val[oldL.length+lane]! buf seed addr stride := by
  let g := outG.val[oldG.length+lane]!
  let l := outL.val[oldL.length+lane]!
  obtain ⟨gt,gh,gr,gs,gp,gc⟩ := issuedG.2.2 lane live
  obtain ⟨ltree,lh,lr,ls,lp,lc⟩ := issuedL.2.2 lane live
  have recEq : {g with slot_start:=l.slot_start}=l := by
    have t : g.tree=l.tree := UScalar.eq_of_val_eq (gt.trans ltree.symm)
    have r : g.root_idx=l.root_idx := UScalar.eq_of_val_eq (gr.trans lr.symm)
    have c : g.chunks=l.chunks := UScalar.eq_of_val_eq (gc.trans lc.symm)
    have h : g.height=l.height := gh.trans lh.symm
    have s : g.sub_h=l.sub_h := gs.trans ls.symm
    revert t r c h s
    cases g;cases l;simp only [Meta.mk.injEq];tauto
  change merge host g global seed addr stride=merge host l buf seed addr stride
  have top := Nat.mul_le_mul_right (2^(j.val-sub.val)) (show lane+1≤active from live)
  rw [Nat.add_one_mul] at top
  change g.slot_start.val=_ at gp
  change g.chunks.val=_ at gc
  change l.slot_start.val=_ at lp
  rw [Nat.zero_add] at lp
  rw [←recEq]
  apply merge_rebase
  · rw [gp,gc];omega
  · rw [lp,gc];omega
  · intro c hc
    rw [gp,lp,Nat.add_assoc]
    exact same _ (by omega)

end slhdsa.ForsMetadata

namespace slhdsa.RawFors
/-- Both scalar queue producers, with their production native reducer, work at
arbitrary aligned or unaligned reservation offsets. -/
theorem ScalarMerge.action_rebase {N} (m : ScalarMerge N) (host : ParallelScalarFors.Platform)
    (d : Data N) (valid : Valid d) (sat : Bool) (base : Usize) (global : Cells N) (old : ForsMetadata.Table)
    (tree : m.t.val<d.p.k.val) (field : m.j.val<d.p.a.val) (lower : m.sub.val<m.j.val)
    (room : 2^(m.j.val-m.sub.val)≤m.slots.length) (fits : base.val+2^(m.j.val-m.sub.val)≤global.length)
    (cap : old.length<Usize.max) (localCap : m.old.length<Usize.max)
    (same : ∀ i<2^(m.j.val-m.sub.val), global.val[base.val+i]! = m.slots.val[i]!) :
    ({m with start:=base,slots:=global,old:=old}).action host d sat =
    ({m with start:=0#usize}).action host d sat := by
  have tr := valid.count.symm ▸ tree
  have trees : d.choices.length≤35 := valid.count ▸ valid.pn.valid.k_le
  have emit := ForsMetadata.scalar sat d.choices d.p.a m.j m.sub
  obtain ⟨⟨_,g⟩,gcall,_,eg⟩ := spec_imp_exists (emit base m.t old valid.pn.valid.a_le field trees tr
    (valid.digits _ tr) lower (fits.trans global.len_ineq) cap)
  obtain ⟨⟨_,l⟩,lcall,_,el⟩ := spec_imp_exists (emit (0#usize) m.t m.old valid.pn.valid.a_le field trees tr
    (valid.digits _ tr) lower (by simpa using room.trans m.slots.len_ineq) localCap)
  unfold action
  dsimp only
  rw [gcall,lcall,bind_ok,bind_ok]
  exact ForsMetadata.emitted_rebase host _ _ _ _ _ 1 _ old g m.old l eg el global m.slots d.seed d.addr d.stride
    0 (by decide) (by simpa using fits) (by simpa using room) (by simpa using same)

/-- Grouped split jobs lay out one consecutive row per tree. Rebase the whole
region while preserving the selected lane's destination and returned bytes. -/
theorem GroupMerge.action_rebase {N} (m : GroupMerge N) (d : Data N) (valid : Valid d) (lane : Nat)
    (live : lane<m.active.val) (base : Usize) (global : Cells N) (old : ForsMetadata.Table)
    (field : m.j.val<d.p.a.val) (lower : m.sub.val<m.j.val) (range : m.first.val+m.active.val≤d.choices.length)
    (room : m.active.val*2^(m.j.val-m.sub.val)≤m.slots.length)
    (fits : base.val+m.active.val*2^(m.j.val-m.sub.val)≤global.length)
    (cap : old.length+m.active.val≤Usize.max) (localCap : m.old.length+m.active.val≤Usize.max)
    (same : ∀ i<m.active.val*2^(m.j.val-m.sub.val), global.val[base.val+i]! = m.slots.val[i]!) :
    ({m with start:=base,slots:=global,old:=old}).action d lane =
    ({m with start:=0#usize}).action d lane := by
  have trees : d.choices.length≤35 := valid.count ▸ valid.pn.valid.k_le
  let first := UScalar.cast .Usize m.first
  let active := UScalar.cast .Usize m.active
  have fv : first.val=m.first.val := U16.cast_Usize_val_eq _
  have av : active.val=m.active.val := U8.cast_Usize_val_eq _
  have emit := ForsMetadata.group d.choices d.p.a m.j m.sub
  obtain ⟨⟨_,g⟩,gcall,_,eg⟩ := spec_imp_exists (emit base first active old valid.pn.valid.a_le field lower
    trees (by rwa [fv,av]) valid.digits (by rw [av];exact fits.trans global.len_ineq) (by rwa [av]))
  obtain ⟨⟨_,l⟩,lcall,_,el⟩ := spec_imp_exists (emit (0#usize) first active m.old valid.pn.valid.a_le field lower
    trees (by rwa [fv,av]) valid.digits (by simpa [av] using room.trans m.slots.len_ineq) (by rwa [av]))
  unfold action
  dsimp only
  rw [gcall,lcall,bind_ok,bind_ok]
  exact ForsMetadata.emitted_rebase .linux _ _ _ _ _ _ _ old g m.old l eg el global m.slots d.seed d.addr d.stride
    lane (av ▸ live) (by rwa [av]) (by rwa [av]) (by rwa [av])
end slhdsa.RawFors

namespace slhdsa.ForsMetadata
/-- Matching rows are derived from actual child publications at the two
addresses. Equality of the specification bytes determines every array cell. -/
theorem chunkCells_rebase {N} (p : params.Params) (sk : Spec.Bytes) (seed : Array U8 N)
    (addr : address.Adrs) (choices : alloc.vec.Vec U32) (tree : Nat) (j sub : U32)
    (g l : Nat) (global buf : Cells N)
    (issuedG : ChunkCells p sk seed addr choices tree j sub g global)
    (issuedL : ChunkCells p sk seed addr choices tree j sub l buf) :
    ∀ c<2^(j.val-sub.val), global.val[g+c]! = buf.val[l+c]! := by
  intro c hc
  obtain ⟨x,gx,vx⟩ := issuedG c hc
  obtain ⟨y,ly,vy⟩ := issuedL c hc
  rw [gx,ly,Aeneas.Std.Array.ext x y ((bytes_inj _ _).mp (vx.trans vy.symm))]
end slhdsa.ForsMetadata

namespace slhdsa.RawFors
theorem ScalarMerge.cells_rebase {N} (m : ScalarMerge N) (host : ParallelScalarFors.Platform)
    (d : Data N) (v : Valid d) (sat : Bool) (base : Usize) (global : Cells N) (old : ForsMetadata.Table)
    (issuedG : ({m with start:=base,slots:=global,old:=old}).Ready host d sat)
    (issuedL : ({m with start:=0#usize}).Ready host d sat) :
    ∀ c<2^(m.j.val-m.sub.val), global.val[base.val+c]! = m.slots.val[c]! := by
  obtain ⟨tree,field,lower,fitG,_,pubG⟩ := issuedG
  obtain ⟨_,_,_,fitL,_,pubL⟩ := issuedL
  have cells := ForsMetadata.scalar_cells host d.p v.pn d.sk d.seed d.addr v.domain d.choices m.t m.j m.sub
  have toCells := fun start slots fit pub => cells start sat slots tree field lower
      (v.digits _ (v.count ▸ tree)) fit pub
  simpa using ForsMetadata.chunkCells_rebase _ _ _ _ _ _ _ _ _ _ _ _ (toCells base global fitG pubG)
    (toCells (0#usize) m.slots fitL pubL)

theorem GroupMerge.cells_rebase {N} (m : GroupMerge N) (d : Data N) (v : Valid d)
    (base : Usize) (global : Cells N) (old : ForsMetadata.Table)
    (issuedG : ({m with start:=base,slots:=global,old:=old}).Ready d)
    (issuedL : ({m with start:=0#usize}).Ready d) :
    ∀ i<m.active.val*2^(m.j.val-m.sub.val), global.val[base.val+i]! = m.slots.val[i]! := by
  obtain ⟨field,lower,hj,hs,width,range,_,cv,fitG,pubG⟩ := issuedG
  obtain ⟨_,_,_,_,_,_,_,_,fitL,pubL⟩ := issuedL
  intro i inside
  let count := 2^(m.j.val-m.sub.val)
  have positive : 0<count := Nat.two_pow_pos _
  have lane : i/count<m.active.val := (Nat.div_lt_iff_lt_mul positive).2 inside
  have cells := @ForsMetadata.group_cells unreachableHigh N d.p v.pn d.sk d.seed d.addr v.domain
    d.choices m.first m.active m.h m.low m.j m.sub
  have toCells := fun start slots fit pub => cells start m.chunks slots (i/count) lane field lower.le
    ⟨hj,hs⟩ width (v.count ▸ v.pn.valid.k_le) range v.digits cv fit pub
  have agree := ForsMetadata.chunkCells_rebase _ _ _ _ _ _ _ _ _ _ _ _ (toCells base global fitG pubG)
    (toCells (0#usize) m.slots fitL pubL) (i%count) (Nat.mod_lt _ positive)
  change m.chunks.val=count at cv
  simpa only [cv,show (0#usize).val=0 from rfl,Nat.zero_add,Nat.add_assoc,Nat.div_add_mod'] using agree
end slhdsa.RawFors

namespace slhdsa.RawFors
theorem ScalarMerge.published_rebase {N} (m : ScalarMerge N) (host : ParallelScalarFors.Platform)
    (d : Data N) (v : Valid d) (sat : Bool) (base : Usize) (global : Cells N) (old : ForsMetadata.Table)
    (g : ({m with start:=base,slots:=global,old:=old}).Ready host d sat)
    (l : ({m with start:=0#usize}).Ready host d sat) :
    ({m with start:=base,slots:=global,old:=old}).action host d sat = ({m with start:=0#usize}).action host d sat :=
  m.action_rebase host d v sat base global old g.1 g.2.1 g.2.2.1 (by simpa using l.2.2.2.1)
    g.2.2.2.1 g.2.2.2.2.1 l.2.2.2.2.1 (m.cells_rebase host d v sat base global old g l)

theorem GroupMerge.published_rebase {N} (m : GroupMerge N) (d : Data N) (v : Valid d) (lane : Nat)
    (live : lane<m.active.val) (base : Usize) (global : Cells N) (old : ForsMetadata.Table)
    (g : ({m with start:=base,slots:=global,old:=old}).Ready d)
    (l : ({m with start:=0#usize}).Ready d) :
    ({m with start:=base,slots:=global,old:=old}).action d lane = ({m with start:=0#usize}).action d lane := by
  have rows := m.cells_rebase d v base global old g l
  obtain ⟨field,lower,hj,hs,_,range,cap,cv,fitG,_⟩ := g
  obtain ⟨_,_,_,_,_,_,localCap,_,fitL,_⟩ := l
  change m.chunks.val=_ at cv
  apply m.action_rebase d v lane live base global old
  · exact hj ▸ field
  · simpa only [hj,hs] using lower
  · exact range
  · simpa only [show (0#usize).val=0 from rfl,Nat.zero_add,cv] using fitL
  · simpa only [cv] using fitG
  · exact cap
  · exact localCap
  · exact rows
end slhdsa.RawFors
