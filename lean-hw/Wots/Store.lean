import Wots.Batch
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.Wots

abbrev Rows (L : Usize) := Slice (Array U8 L)
abbrev Staged (N : Usize) := Array (Array U8 N) 16#usize

/-- Borrow the destination first, as Rust does, then compute the end, select
the staged lanes, flatten and copy them, and restore the two mutable borrows. -/
def putRows {L N} (out : Rows L) (key start : Usize) (endAt : Result Usize)
    (selection : Result (Rows N)) := do
  let (row,restoreRow) ← Slice.index_mut_usize out key
  let stop ← endAt
  let (dst,restoreBytes) ← core.array.Array.index_mut (core.ops.index.IndexMutSlice
    (core.slice.index.SliceIndexRangeUsizeSlice U8)) row
    (⟨start,stop⟩ : core.ops.range.Range Usize)
  let src ← selection
  let flat ← WotsRust.core.slice.SliceArray.as_flattened src
  let written ← core.slice.Slice.copy_from_slice core.marker.CopyU8 dst flat
  ok (restoreRow (restoreBytes written))

def firstRows {N} (staged : Staged N) (width : Usize) :=
  core.array.Array.index (core.ops.index.IndexSlice
    (core.slice.index.SliceIndexRangeToUsizeSlice (Array U8 N))) staged
    (⟨width⟩ : core.ops.range.RangeTo Usize)

def secondRows {N} (staged : Staged N) (width used : Usize) :=
  core.array.Array.index (core.ops.index.IndexSlice
    (core.slice.index.SliceIndexRangeUsizeSlice (Array U8 N))) staged
    (⟨width,used⟩ : core.ops.range.Range Usize)

def stopAt (N start width : Usize) := do
  let byteCount ← width * N
  start + byteCount

def afterBoundary (N width used : Usize) := do
  let remaining ← used - width
  stopAt N 22#usize remaining

def writeBatch {L} (N len atSlot used : Usize) (hash : Hash) (out : Rows L) := do
  let key ← atSlot / len
  let slot ← atSlot % len
  let remaining ← len - slot
  let width := core.cmp.impls.OrdUsize.min used remaining
  let staged ← stage (N := N) hash used
  let offset ← slot * N
  let start ← 22#usize + offset
  let r ← putRows out key start (stopAt N start width) (firstRows staged width)
  if width < used then
    let key' ← key + 1#usize
    putRows r key' 22#usize (afterBoundary N width used) (secondRows staged width used)
  else ok r

private theorem bind_congr_right {A : Type u} {B : Type v} (x : Result A) {f g : A → Result B}
    (same : ∀ a, f a = g a) : Std.bind x f = Std.bind x g := by rw [funext same]

theorem store_batch_eq {L α} (N len atSlot used : Usize) (hash : Hash) (out : Rows L)
    (next : Rows L → Result α) :
    storeBatch N len atSlot used hash out next =
      (do let r ← writeBatch N len atSlot used hash out; next r) := by
  unfold storeBatch writeBatch stage afterBoundary stopAt putRows firstRows secondRows
  simp only [lift,bind_tc_eq,Std.bind_assoc,bind_ok]
  repeat' (apply bind_congr_right; intro x)
  split <;> simp only [bind_tc_eq,Std.bind_assoc,bind_ok]
  rfl

def piece {L} (before after : Rows L) (key start : Nat) (payload : List U8) :=
  after.length = before.length ∧ (∀ j, j ≠ key → after.val[j]! = before.val[j]!) ∧
  after.val[key]!.val = before.val[key]!.val.take start ++ payload ++
    before.val[key]!.val.drop (start+payload.length)

theorem put_spec {L N} (out : Rows L) (key start : Usize) (endAt : Result Usize)
    (selection : Result (Rows N)) (selected : List (Array U8 N)) (hk : key.val < out.length)
    (bound : start.val + N.val*selected.length ≤ L.val)
    (endOK : endAt ⦃ e => e.val = start.val + N.val*selected.length ⦄)
    (selOK : selection ⦃ src => src.val = selected ⦄) :
    putRows out key start endAt selection ⦃ r => piece out r key.val start.val (selected.flatMap (·.val)) ⦄ := by
  obtain ⟨stop,he,hlen⟩ := spec_imp_exists endOK
  obtain ⟨rows,hs,hrows⟩ := spec_imp_exists selOK
  have eq : putRows out key start endAt selection = copyRows out key start stop rows := by
    unfold putRows copyRows
    simp only [he,hs,bind_tc_eq,bind_ok]
  rw [eq]
  apply WP.spec_mono (copy_rows_spec out key start stop rows hk (by simpa [Slice.length,hrows] using hlen) (by omega))
  rintro r ⟨hr,other,bytes⟩
  exact ⟨hr,other,by simpa only [hrows,hlen,flat_length] using bytes⟩

theorem stop_spec (N start width : Usize) (bound : start.val+width.val*N.val ≤ Usize.max) :
    stopAt N start width ⦃ s => s.val = start.val+N.val*width.val ⦄ := by
  unfold stopAt
  step as ⟨n,hn⟩
  step as ⟨s,hs⟩
  simp [hs,hn,Nat.mul_comm]

theorem after_spec (N width used : Usize) (hw : width.val ≤ used.val)
    (bound : 22+(used.val-width.val)*N.val ≤ Usize.max) :
    afterBoundary N width used ⦃ s => s.val = 22+N.val*(used.val-width.val) ⦄ := by
  unfold afterBoundary
  step as ⟨remaining,hr⟩
  step with stop_spec N 22#usize remaining (by change 22 + remaining.val*N.val ≤ Usize.max; simpa only [hr] using bound) as ⟨stop,hs⟩
  simpa only [hr] using hs

theorem first_rows_spec {N} (a : Staged N) (width : Usize) (hw : width.val ≤ 16) :
    firstRows a width ⦃ r => r.val = a.val.take width.val ⦄ := by
  unfold firstRows
  step as ⟨r,hr,hl⟩
  simp [hr,List.slice]

theorem second_rows_spec {N} (a : Staged N) (width used : Usize) (hw : width.val ≤ used.val)
    (hu : used.val ≤ 16) :
    secondRows a width used ⦃ r => r.val = (a.val.drop width.val).take (used.val-width.val) ⦄ := by
  unfold secondRows
  step as ⟨r,hr,hl⟩
  simpa [List.slice,Array.val_to_slice,List.drop_take] using hr


def batchWrites {N L} (hash : Hash) (before after : Rows L) (len atSlot used : Nat) :=
  let key := atSlot/len
  let slot := atSlot%len
  let width := min used (len-slot)
  ∃ (staged : Staged N) (mid : Rows L),
    (∀ j : Fin 16, j.val < used → ∀ k < N.val, (staged.val[j.val]!.val[k]!).bv = Store.digestByte hash j k) ∧
    piece before mid key (22+slot*N.val) ((staged.val.take width).flatMap (·.val)) ∧
    if width < used then piece mid after (key+1) 22 (((staged.val.drop width).take (used-width)).flatMap (·.val))
    else after = mid

/-- Both source branches complete on valid inputs. The postcondition names the
exact staged lane ranges and byte destinations, including preserved data. -/
theorem write_batch_spec {L} (N len atSlot used : Usize) (hash : Hash) (out : Rows L)
    (shape : N.val=16 ∨ N.val=24 ∨ N.val=32) (wide : 16 ≤ len.val) (hu : used.val ≤ 16)
    (live : atSlot.val < len.val*out.length) (ends : atSlot.val+used.val ≤ len.val*out.length)
    (room : 22+len.val*N.val ≤ L.val) :
    writeBatch N len atSlot used hash out ⦃ r => batchWrites (N := N) hash out r len.val atSlot.val used.val ⦄ := by
  unfold writeBatch
  have positive : 0 < len.val := by omega
  have hk : atSlot.val/len.val < out.length := Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using live)
  have hslot := Nat.mod_lt atSlot.val positive
  have Lmax : L.val ≤ Usize.max := by scalar_tac
  step as ⟨key,hkey⟩
  step as ⟨slot,hs⟩
  step as ⟨remaining,hr⟩
  let width := core.cmp.impls.OrdUsize.min used remaining
  have hw : width.val = min used.val (len.val-slot.val) := by simp [width,hr]
  have cap : slot.val + width.val ≤ len.val := by omega
  have bound := Nat.mul_le_mul_right N.val cap
  rw [Nat.add_mul] at bound
  step with stage_spec hash used shape hu as ⟨buf,hbuf⟩
  step as ⟨off,hoff⟩
  step as ⟨start,hstart⟩
  have startOK : start.val = 22+slot.val*N.val := by scalar_tac
  let src := buf.val.take width.val
  have slen : src.length = width.val := by simp [src,Nat.min_eq_left (by omega : width.val ≤ 16)]
  have fit : start.val+width.val*N.val ≤ L.val := by omega
  step with put_spec out key start (stopAt N start width) (firstRows buf width) src (by omega)
    (by rw [slen,Nat.mul_comm N.val]; exact fit)
    (by simpa only [slen] using stop_spec N start width (by omega))
    (first_rows_spec buf width (by omega)) as ⟨mid,hmid⟩
  have midOK : piece out mid (atSlot.val/len.val) (22+(atSlot.val%len.val)*N.val) (src.flatMap (·.val)) := by
    simpa only [hkey,startOK,hs] using hmid
  have widthNat : width.val = min used.val (len.val-atSlot.val%len.val) := by rw [hw,hs]
  change (if width < used then _ else _) ⦃ _ ⦄
  by_cases cross : width < used
  · rw [if_pos cross]
    have crosses : width.val < used.val := cross
    have nextLive : key.val+1 < mid.length := by
      have div := Nat.mod_add_div atSlot.val len.val
      have mlen := hmid.1
      have inc := Nat.mul_succ len.val key.val
      by_contra h
      have back : out.length ≤ key.val+1 := by omega
      have hfull := Nat.mul_le_mul_left len.val back
      rw [inc,hkey] at hfull
      omega
    step as ⟨key',hk'⟩
    let src2 := (buf.val.drop width.val).take (used.val-width.val)
    have slen2 : src2.length = used.val-width.val := by
      simp only [src2,List.length_take,List.length_drop]
      apply Nat.min_eq_left
      rw [show buf.val.length = 16 by simp]
      omega
    have fit2 : 22+(used.val-width.val)*N.val ≤ L.val := by
      have := Nat.mul_le_mul_right N.val (by omega : used.val-width.val ≤ len.val); omega
    step with put_spec mid key' 22#usize (afterBoundary N width used) (secondRows buf width used) src2 (by omega)
      (by rw [slen2,Nat.mul_comm N.val]; exact fit2)
      (by simpa only [slen2,show (22#usize).val = 22 by rfl] using after_spec N width used (by omega) (by omega))
      (second_rows_spec buf width used (by omega) hu) as ⟨r,hr⟩
    refine ⟨buf,mid,hbuf,?_,?_⟩
    · simpa only [← widthNat] using midOK
    · simpa only [← widthNat,if_pos crosses,hk',hkey] using hr
  · rw [if_neg cross]
    simp only [step_simps]
    refine ⟨buf,mid,hbuf,?_,?_⟩
    · simpa only [← widthNat] using midOK
    · simp only [← widthNat,if_neg (show ¬width.val < used.val from cross)]

end slhdsa.X86.Wots
