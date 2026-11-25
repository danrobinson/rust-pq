import Parallel.RawChunkTable
open Aeneas Aeneas.Std Result
namespace slhdsa.ParallelRawChunks
open ParallelXmssTicket ParallelSigning ParallelAuthTable ParallelSignJoin

abbrev Metadata := alloc.vec.Vec XmssAuthMeta

def Fields {N : Usize} (p : params.Params) (sk seed : Array U8 N) (tree leaf : Nat)
    (metas : Metadata) (cells : Slots N) :=
  p.d.val*p.hp.val≤metas.length ∧ ∀ j<p.d.val, ∀ h<p.hp.val,
    let m := metas.val[j*p.hp.val+h]!
    m.root_idx.val=root (loc p.hp.val tree leaf j).2 h ∧ m.height.val=h ∧
    Chunks p (bytes sk.val) seed (addr j (loc p.hp.val tree leaf j).1) m cells

theorem produce_spec {N : Usize} (p : params.Params) (hp : PN p N) (node : Node N) (law : NodeLaw p node 512)
    (layers : Layers) (sk seed : Array U8 N) (tree leaf : Nat) (bound : leaf<2^p.hp.val)
    (layout : LayerTable p.hp.val tree leaf p.d.val layers) (schedule : ∀ n, WidthEight.Ticket.Schedule n) :
    produce p node layers sk seed schedule ⦃ ms cs => Fields p sk seed tree leaf ms cs ⦄ := by
  let n := p.d.val*p.hp.val
  let w := p.hp.val
  have positive : 0<w := hp.valid.hp_pos
  have maxD := hp.valid.d_le
  have maxW : w≤9 := hp.valid.hp_le
  have total : n≤22*9 := Nat.mul_le_mul maxD maxW
  have slotCount := capacity w n positive maxW
  obtain ⟨ms,built,len,record⟩ := collect_ok (rowInfo p layers) (List.range n)
    (fun q present => info_returns p hp layers q (geometry p hp tree leaf bound layers layout q (List.mem_range.mp present)))
  have works (key : Nat × Nat) (present : key∈slots w n) :
      ∃ r, rowChunk p node layers sk seed key=ok (some r) := by
    obtain ⟨q,c⟩ := key
    obtain ⟨live,inside⟩ := shape _ present
    obtain ⟨_,r,_,_,made⟩ := chunk_returns p hp node law layers sk seed q c
      (geometry p hp tree leaf bound layers layout q live) inside
    exact ⟨r,made⟩
  have joined := fill_eq (rowChunk p node layers sk seed) (slots w n) (schedule _) works
  obtain ⟨cs,published,rows,physical⟩ := collect_ok (rowChunk p node layers sk seed) (slots w n)
    (fun k h => let ⟨v,run⟩ := works k h;⟨some v,run⟩)
  simp only [List.length_range] at len record
  have metaEq : (boxed ms).val=ms := by
    have fit : ms.length≤Usize.max := by rw [len];scalar_tac
    simp [boxed,List.take_of_length_le fit]
  have cellsEq : (boxed cs).val=cs := by
    have fit : cs.length≤Usize.max := by rw [rows];scalar_tac
    simp [boxed,List.take_of_length_le fit]
  unfold produce
  change (do let metaRows ← collect _ (List.range n);let chunks ← fill _ (slots w n) (schedule _);ok (boxed metaRows,boxed chunks)) ⦃ _ => _ ⦄
  simp only [built,joined,published,step_simps,uncurry]
  refine ⟨by change n≤(boxed ms).val.length;rw [metaEq,len],?_⟩
  intro j hj h hh
  change h<w at hh
  let q := j*w+h
  have live : q<n := by
    have lim := Nat.mul_le_mul_right w hj
    rw [Nat.succ_mul] at lim
    change j*w+h<p.d.val*w
    omega
  have lj : q/w=j := by simp [q,Nat.add_comm, Nat.add_mul_div_right _ _ positive,Nat.div_eq_of_lt hh]
  have rh : q%w=h := by simp [q,Nat.add_mod,Nat.mod_eq_of_lt hh]
  have g := geometry p hp tree leaf bound layers layout q live
  let layer := size (q/w)
  let level := word (q%w)
  let start := size (offset w q)
  have layerEq : layer.val=j := g.layer.trans lj
  have levelEq : level.val=h := g.height.trans rh
  let m := ms[q]!
  have get : issuedMetadata p layer layers.val[layer.val]!.2 level start=ok m := by
    simpa [rowInfo,live,layer,level,start,w,m] using record q live
  have space : start.val+2^depth p.hp.val level.val≤(boxed cs).length := by
    change _≤(boxed cs).val.length
    rw [cellsEq,rows]
    simpa only [start,w,level,g.start,g.height] using @room w n q live
  have out := chunks_from_jobs p hp node law layers layer level start m sk seed (boxed cs)
    (by simpa only [layer,w,g.layer] using g.live) (by simpa only [layer,w,g.layer] using g.narrow)
    (by simpa only [level,w,g.height] using g.below) (by simpa only [layer,w,g.layer] using g.index) space get (by
      intro c active dest row exec
      have cv : size c.val=c := UScalar.eq_of_val_eq (size_val _ c.bv.isLt)
      have actual : c.val<2^depth w (q%w) := by simpa only [level,w,g.height] using active
      obtain ⟨d,r,run,atSlot,made⟩ := chunk_returns p hp node law layers sk seed q c.val g actual
      rw [cv,exec] at run
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Result.ok_injective run)
      rw [cellsEq,atSlot]
      have index := @room w n q live
      have enough : offset w q+c.val<(slots w n).length := by omega
      have hit := physical (offset w q+c.val) enough
      rw [coordinate live actual,made] at hit
      exact (Result.ok_injective hit).symm)
  have base := congrArg Prod.fst (layout.2 j hj)
  have ix := congrArg Prod.snd (layout.2 j hj)
  dsimp only at base ix
  simpa only [metaEq,layerEq,levelEq,base,ix] using out

end slhdsa.ParallelRawChunks
