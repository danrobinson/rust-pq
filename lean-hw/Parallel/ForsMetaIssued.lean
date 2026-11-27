import Parallel.ForsMetaMerge
open Aeneas Aeneas.Std Result
namespace slhdsa.ForsMetadata

def Merged {N} (host : ParallelScalarFors.Platform) (p : params.Params) (sk seed : Array U8 N)
    (addr : address.Adrs) (choices : alloc.vec.Vec U32) (j : U32) (t : Nat)
    (stride : Usize) (slots : Cells N) (m : ParallelForsMerge.Meta) :=
  merge host m slots seed addr stride ⦃ (dest,r) => dest.val=t*(1+p.a.val)+1+j.val ∧
    bytes r.val=Spec.forsNode (Shake.params p) (bytes sk.val) (ForsDriver.sibling choices.slice p.a t j.val)
      j.val (bytes seed.val) (adrsS addr) ⦄

/-- Both scalar issuing sites, including the saturating width-eight split. Each
opaque scheduling premise records a physical write of the named native worker. -/
theorem scalar_issued {N} (host : ParallelScalarFors.Platform) (p : params.Params) (hp : PN p N)
    (sk seed : Array U8 N) (addr : address.Adrs) (domain : ForsHorizontal.Domain addr) (choices : alloc.vec.Vec U32)
    (size : choices.length=p.k.val) (t j sub : U32) (start stride : Usize) (sat : Bool) (slots : Cells N) (old : Table)
    (tree : t.val<p.k.val) (field : j.val<p.a.val) (lower : sub.val<j.val)
    (selected : choices.val[t.val]!.val<2^p.a.val) (fits : start.val+2^(j.val-sub.val)≤slots.length)
    (capacity : old.length<Usize.max) (shape : stride.val=1+p.a.val)
    (published : ∀ c : Usize, c.val<2^(j.val-sub.val) → ∀ w,
      ParallelScalarFors.run (ParallelScalarFors.actions host p sk seed addr).2
        ((if sat then ParallelScalarFors.prepare_saturating else ParallelScalarFors.prepare_split)
          t p.a j choices.val[t.val]! sub start c)=ok w → slots.val[w.1.val]! = some w.2) :
    (if sat then meta_wide else meta_scalar) choices p.a j sub start t old ⦃ next out =>
      next.val=start.val+2^(j.val-sub.val) ∧ Emitted choices p.a j sub t.val 1 start.val old out ∧
      Merged host p sk seed addr choices j t.val stride slots out.val[old.length]! ⦄ := by
  have room := slots.len_ineq
  change slots.length≤Usize.max at room
  apply WP.spec_mono (scalar sat choices p.a j sub start t old hp.valid.a_le field (size ▸ hp.valid.k_le)
    (size ▸ tree) selected lower (by omega) capacity)
  rintro ⟨next,out⟩ ⟨nextV,records⟩
  have record : Record choices p.a j sub t.val start.val out.val[old.length]! := by
    simpa only [Nat.add_zero,Nat.zero_mul] using records.2.2 0 (by decide)
  exact ⟨nextV,records,record_merge host p hp _ slots (bytes sk.val) seed addr stride choices t.val start.val j sub
    record tree size selected field lower.le shape fits
    (scalar_cells host p hp sk seed addr domain choices t j sub start sat slots tree field lower selected fits published)⟩

/-- Narrow Arm batches issue one metadata record per live lane. For every
record the consumer reads that lane's contiguous chunk block and returns its FIPS sibling. -/
theorem group_issued [wide : ParallelForsTicket.Wide] {N} (p : params.Params) (hp : PN p N)
    (sk seed : Array U8 N) (addr : address.Adrs) (domain : ForsHorizontal.Domain addr)
    (choices : alloc.vec.Vec U32) (first : U16) (active height low : U8) (j sub : U32)
    (start chunks stride : Usize) (slots : Cells N) (old : Table)
    (field : height.val<p.a.val) (lower : low.val<height.val) (defs : j.val=height.val ∧ sub.val=low.val)
    (width : active.val≤3) (size : choices.length=p.k.val) (range : first.val+active.val≤choices.length)
    (digits : ∀ t<choices.length, choices.val[t]!.val<2^p.a.val) (capacity : old.length+active.val≤Usize.max)
    (cv : chunks.val=2^(j.val-sub.val)) (space : start.val+active.val*chunks.val≤slots.length)
    (shape : stride.val=1+p.a.val)
    (published : ∀ c : U32, c.val<chunks.val → ∀ rows, ParallelForsTicket.split_ticket sk seed addr choices p.a
      first active height low c start chunks=ok rows → ∀ l<active.val, slots.val[rows.val[l]!.1.val]! = some rows.val[l]!.2) :
    meta_group choices p.a j sub start (UScalar.cast .Usize first) (UScalar.cast .Usize active) old ⦃ next out =>
      next.val=start.val+active.val*chunks.val ∧ Emitted choices p.a j sub first.val active.val start.val old out ∧
      ∀ l<active.val, Merged .linux p sk seed addr choices j (first.val+l) stride slots out.val[old.length+l]! ⦄ := by
  have room := slots.len_ineq
  change slots.length≤Usize.max at room
  have fv := U16.cast_Usize_val_eq first
  have av := U8.cast_Usize_val_eq active
  have hj := defs.1
  have hs := defs.2
  have count : choices.length≤35 := size ▸ hp.valid.k_le
  apply WP.spec_mono (group choices p.a j sub start (UScalar.cast .Usize first) (UScalar.cast .Usize active) old
    hp.valid.a_le (by omega) (by omega) count (by rwa [fv,av]) digits (by rw [av,←cv];omega) (by rwa [av]))
  rintro ⟨next,out⟩ ⟨nextV,records⟩
  rw [av,←cv] at nextV
  rw [fv,av] at records
  refine ⟨nextV,records,?_⟩
  intro l hl
  have record := records.2.2 l hl
  rw [←cv] at record
  have bound := Nat.mul_le_mul_right chunks.val (show l+1≤active.val by omega)
  rw [Nat.add_one_mul] at bound
  apply record_merge .linux p hp _ slots (bytes sk.val) seed addr stride choices (first.val+l) _ j sub record
    (by omega) size (digits _ (by omega)) (by omega) (by omega) shape (by rw [←cv];omega)
  exact group_cells p hp sk seed addr domain choices first active height low j sub start chunks slots l hl field lower.le defs
    width count range digits cv space published


/-- The freshly issued metadata intervals partition the reservation exactly.
Each occupied physical position has a unique lane and chunk owner. -/
theorem partition {choices : alloc.vec.Vec U32} {a j sub : U32} {first n start : Nat} {old out : Table}
    (records : Emitted choices a j sub first n start old out)
    (position : Nat) (inside : position<n*2^(j.val-sub.val)) :
    ∃! pair : Fin n × Fin (2^(j.val-sub.val)), out.val[old.length+pair.1.val]!.slot_start.val+pair.2.val=start+position := by
  let width := 2^(j.val-sub.val)
  have pos : 0<width := Nat.two_pow_pos _
  have lane : position/width<n := (Nat.div_lt_iff_lt_mul pos).2 inside
  let pair : Fin n × Fin width := (⟨position/width,lane⟩,⟨position%width,Nat.mod_lt _ pos⟩)
  have slot (i : Fin n) : out.val[old.length+i.val]!.slot_start.val=start+i.val*width :=
    (records.2.2 _ i.isLt).2.2.2.2.1
  refine ⟨pair,?_,?_⟩
  · change out.val[old.length+pair.1.val]!.slot_start.val+pair.2.val=start+position
    rw [slot pair.1]
    change start+(position/width)*width+position%width=start+position
    rw [Nat.add_assoc,Nat.div_add_mod' position width]
  · rintro ⟨i,c⟩ eq
    change out.val[old.length+i.val]!.slot_start.val+c.val=start+position at eq
    rw [slot i,Nat.add_assoc] at eq
    have parts : i.val*width+c.val=position := Nat.add_left_cancel eq
    have chunk : c.val=position%width := by
      rw [←parts,Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt c.isLt]
    have index : i.val=position/width := by
      rw [←parts,Nat.mul_comm i.val width,Nat.mul_add_div pos,Nat.div_eq_of_lt c.isLt,Nat.add_zero]
    exact Prod.ext (Fin.ext index) (Fin.ext chunk)

/-- The narrowed Rust ticket fields can be fed back to the planner without
changing the reserved interval or its decoded FORS height. -/
theorem group_cast_geometry (first active : Usize) (j sub : U32) (range : first.val+active.val≤35)
    (field : j.val≤14) (lower : sub.val≤j.val) :
    UScalar.cast .Usize (UScalar.cast .U16 first)=first ∧ UScalar.cast .Usize (UScalar.cast .U8 active)=active ∧
    (UScalar.cast .U8 j).val=j.val ∧ (UScalar.cast .U8 sub).val=sub.val := by
  have f : (UScalar.cast .U16 first).val=first.val := by
    rw [UScalar.cast_val_eq];apply Nat.mod_eq_of_lt;change _<2^16;omega
  have n : (UScalar.cast .U8 active).val=active.val := by
    rw [UScalar.cast_val_eq];apply Nat.mod_eq_of_lt;change _<2^8;omega
  refine ⟨UScalar.eq_of_val_eq ((U16.cast_Usize_val_eq _).trans f),
    UScalar.eq_of_val_eq ((U8.cast_Usize_val_eq _).trans n),?_,?_⟩ <;>
    rw [UScalar.cast_val_eq] <;> apply Nat.mod_eq_of_lt <;> change _<2^8 <;> omega

end slhdsa.ForsMetadata
