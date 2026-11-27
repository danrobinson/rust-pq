import Parallel.ForsReceipts
import Parallel.ForsMetaIssued
open Aeneas Aeneas.Std Result
namespace slhdsa.RawFors

structure ScalarMerge (N : Usize) where
  t : U32
  j : U32
  sub : U32
  start : Usize
  old : ForsMetadata.Table
  slots : Cells N

structure GroupMerge (N : Usize) where
  first : U16
  active : U8
  h : U8
  low : U8
  j : U32
  sub : U32
  start : Usize
  chunks : Usize
  old : ForsMetadata.Table
  slots : Cells N

def ScalarMerge.Ready {N} (m : ScalarMerge N) (host : ParallelScalarFors.Platform) (d : Data N) (sat : Bool) :=
  m.t.val<d.p.k.val ∧ m.j.val<d.p.a.val ∧ m.sub.val<m.j.val ∧
  m.start.val+2^(m.j.val-m.sub.val)≤m.slots.length ∧ m.old.length<Usize.max ∧
    ∀ c : Usize, c.val<2^(m.j.val-m.sub.val) → Agrees m.slots
      (ParallelScalarFors.run (ParallelScalarFors.actions host d.p d.sk d.seed d.addr).2
        ((if sat then ParallelScalarFors.prepare_saturating else ParallelScalarFors.prepare_split)
          m.t d.p.a m.j d.choices.val[m.t.val]! m.sub m.start c))

def GroupMerge.Ready {N} (m : GroupMerge N) (d : Data N) :=
  m.h.val<d.p.a.val ∧ m.low.val<m.h.val ∧ m.j.val=m.h.val ∧ m.sub.val=m.low.val ∧ m.active.val≤3 ∧
  m.first.val+m.active.val≤d.choices.length ∧ m.old.length+m.active.val≤Usize.max ∧ m.chunks.val=2^(m.j.val-m.sub.val) ∧
  m.start.val+m.active.val*m.chunks.val≤m.slots.length ∧
    ∀ c : U32, c.val<m.chunks.val → ∀ rows,
      @ParallelForsTicket.split_ticket unreachableHigh N d.sk d.seed d.addr d.choices d.p.a m.first m.active m.h m.low c m.start m.chunks=ok rows →
      ∀ lane<m.active.val, Writes m.slots rows.val[lane]!

noncomputable def ScalarMerge.action {N} (m : ScalarMerge N) (host : ParallelScalarFors.Platform) (d : Data N) (sat : Bool) : Result (Cell N) :=
  Std.bind ((if sat then ForsMetadata.meta_wide else ForsMetadata.meta_scalar) d.choices d.p.a m.j m.sub m.start m.t m.old)
    (fun r => ForsMetadata.merge host r.2.val[m.old.length]! m.slots d.seed d.addr d.stride)

noncomputable def GroupMerge.action {N} (m : GroupMerge N) (d : Data N) (lane : Nat) : Result (Cell N) :=
  Std.bind (ForsMetadata.meta_group d.choices d.p.a m.j m.sub m.start (UScalar.cast .Usize m.first) (UScalar.cast .Usize m.active) m.old)
    (fun r => ForsMetadata.merge .linux r.2.val[m.old.length+lane]! m.slots d.seed d.addr d.stride)

theorem ScalarMerge.correct {N} (m : ScalarMerge N) (host : ParallelScalarFors.Platform) (d : Data N) (valid : Valid d)
    (sat : Bool) (ready : m.Ready host d sat) : m.action host d sat ⦃ w => Value d m.t.val (m.j.val+1) w ⦄ := by
  obtain ⟨tree,field,lower,space,cap,children⟩ := ready
  obtain ⟨⟨next,records⟩,call,_,_,merged⟩ := spec_imp_exists (ForsMetadata.scalar_issued host d.p valid.pn d.sk d.seed d.addr
    valid.domain d.choices valid.count m.t m.j m.sub m.start d.stride sat m.slots m.old tree field lower
    (valid.digits _ (valid.count.symm ▸ tree)) space cap (by rw [valid.stride,Nat.add_comm]) children)
  unfold action
  rw [call,bind_ok]
  apply WP.spec_mono merged
  rintro ⟨dest,row⟩ result
  simpa [Value,ParallelLowFors.field,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using result

theorem GroupMerge.correct {N} (m : GroupMerge N) (d : Data N) (valid : Valid d) (lane : Nat) (inside : lane<m.active.val)
    (ready : m.Ready d) : m.action d lane ⦃ w => Value d (m.first.val+lane) (m.j.val+1) w ⦄ := by
  obtain ⟨field,lower,jEq,subEq,width,range,cap,count,space,children⟩ := ready
  obtain ⟨⟨next,records⟩,call,_,_,merged⟩ := spec_imp_exists (@ForsMetadata.group_issued unreachableHigh N d.p valid.pn d.sk d.seed d.addr
    valid.domain d.choices m.first m.active m.h m.low m.j m.sub m.start m.chunks d.stride m.slots m.old field lower
    ⟨jEq,subEq⟩ width valid.count range valid.digits cap count space (by rw [valid.stride,Nat.add_comm]) children)
  unfold action
  rw [call,bind_ok]
  apply WP.spec_mono (merged lane inside)
  rintro ⟨dest,row⟩ result
  simpa [Value,ParallelLowFors.field,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using result
end slhdsa.RawFors
