import Wots.Address
import Wots.Slots
import Wots.Fips
import Wots.Serialize
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.X86.Wots
open WotsRust.core.core_arch.x86.avx512f
open _root_.core.core_arch.x86.avx512f
open WotsRust.sha256.x86.avx512

def patch (base : Words) (key chain : Reg) : Result Words := do
  let old ← Array.index_usize base 2#usize
  let high ← _mm512_srli_epi32 16#u32 key
  let word ← _mm512_or_si512 old high
  let w ← Array.update base 2#usize word
  let low ← _mm512_slli_epi32 16#u32 key
  let w ← Array.update w 3#usize low
  let id ← _mm512_slli_epi32 16#u32 chain
  Array.update w 4#usize id

theorem patch_spec (base : Words) (key chain : Reg) :
    patch base key chain ⦃ w => ∀ k < 16, ∀ j : Fin 16,
      w.val[k]! j = keyWords (chainWords base j) (key j) (chain j) k ⦄ := by
  unfold patch
  step as ⟨old,ho⟩
  simp only [_mm512_srli_epi32,_mm512_or_si512,_mm512_slli_epi32,
    LeafRust.core.core_arch.x86.avx512f._mm512_or_si512,
    LeafRust.core.core_arch.x86.avx512f._mm512_slli_epi32,bind_ok]
  step as ⟨a,ha⟩
  step as ⟨b,hb⟩
  step as ⟨c,hc⟩
  rename_i k hk j
  simp only [hc,hb,ha,Array.set_val_eq,ho,← getElem!_pos]
  have lookup (xs : List Reg) (n : Nat) (v : Reg) (hn : n < xs.length) :
      (xs.set n v)[k]! = if n=k then v else xs[k]! := by
    by_cases h : n=k
    · subst k; simp [Avx2.setSame _ _ _ hn]
    · simp [h]
  simp only [show (4#usize).val = 4 by rfl,show (3#usize).val = 3 by rfl,show (2#usize).val = 2 by rfl,show (16#u32).bv.toNat % 256 = 16 by decide]
  rw [lookup _ 4 _ (by simp),lookup _ 3 _ (by simp),lookup _ 2 _ (by simp)]
  unfold chainWords keyWords
  by_cases x : k=2
  · subst k; rfl
  by_cases y : k=3
  · subst k; rfl
  by_cases z : k=4
  · subst k; rfl
  simp only [if_neg x,if_neg y,if_neg z,if_neg (Ne.symm x),if_neg (Ne.symm y),if_neg (Ne.symm z)]

/-- The remaining two rounds of the shared prefix. The extracted loop also
reuses the two constants and word 2 when switching the address type. -/
def prepare (base : Words) (two : Hash) := do
  let x ← Array.index_usize base 2#usize
  let c ← Array.index_usize WotsRust.sha256.K 2#usize
  let a ← WotsRust.sha256.x86.avx512.round two x c
  let y ← Array.index_usize base 3#usize
  let d ← Array.index_usize WotsRust.sha256.K 3#usize
  let pre ← WotsRust.sha256.x86.avx512.round a y d
  ok (pre,x,c,d)

def storeBatch {L α} (N len «at» used : Usize) (hash : Hash) (out : Slice (Array U8 L))
    (next : Slice (Array U8 L) → Result α) : Result α := do
  let keypair ← «at» / len
  let slot ← «at» % len
  let remaining ← len - slot
  let firstWidth ← lift (core.cmp.impls.OrdUsize.min used remaining)
  let emptyRow := Array.repeat N 0#u8
  let values := Array.repeat 16#usize emptyRow
  let (active, restoreRows) ←
    core.array.Array.index_mut (core.ops.index.IndexMutSlice
      (core.slice.index.SliceIndexRangeToUsizeSlice (Array Std.U8 N))) values
      { «end» := used }
  let written ← WotsRust.sha256.x86.avx512.write_words hash active
  let slotOffset ← slot * N
  let start ← 22#usize + slotOffset
  let (firstRow, restoreFirstRow) ← Slice.index_mut_usize out keypair
  let firstBytes ← firstWidth * N
  let firstEnd ← start + firstBytes
  let (destination, restoreFirstBytes) ←
    core.array.Array.index_mut (core.ops.index.IndexMutSlice
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) firstRow
      { start := start, «end» := firstEnd }
  let staged := restoreRows written
  let firstRows ←
    core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeToUsizeSlice (Array Std.U8 N)))
      staged { «end» := firstWidth }
  let firstPayload ← WotsRust.core.slice.SliceArray.as_flattened firstRows
  let firstCopy ← core.slice.Slice.copy_from_slice core.marker.CopyU8 destination firstPayload
  if firstWidth < used
  then
    let nextKey ← keypair + 1#usize
    let firstUpdated := restoreFirstBytes firstCopy
    let afterFirst := restoreFirstRow firstUpdated
    let (secondRow, restoreSecondRow) ← Slice.index_mut_usize afterFirst nextKey
    let secondWidth ← used - firstWidth
    let secondBytes ← secondWidth * N
    let secondEnd ← 22#usize + secondBytes
    let (secondDestination, restoreSecondBytes) ←
      core.array.Array.index_mut (core.ops.index.IndexMutSlice
        (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) secondRow
        { start := 22#usize, «end» := secondEnd }
    let secondRows ←
      core.array.Array.index (core.ops.index.IndexSlice
        (core.slice.index.SliceIndexRangeUsizeSlice (Array Std.U8 N)))
        staged { start := firstWidth, «end» := used }
    let secondPayload ← WotsRust.core.slice.SliceArray.as_flattened secondRows
    let secondCopy ← core.slice.Slice.copy_from_slice core.marker.CopyU8 secondDestination secondPayload
    let secondUpdated := restoreSecondBytes secondCopy
    let afterSecond := restoreSecondRow secondUpdated
    next afterSecond
  else
    let firstUpdated := restoreFirstBytes firstCopy
    next (restoreFirstRow firstUpdated)

def switchPrefix (base : Words) (two : Hash) (x change : Reg) (c d : U32) := do
  let changed ← _mm512_xor_si512 x change
  let w ← Array.update base 2#usize changed
  let x ← Array.index_usize w 2#usize
  let a ← WotsRust.sha256.x86.avx512.round two x c
  let y ← Array.index_usize w 3#usize
  let pre ← WotsRust.sha256.x86.avx512.round a y d
  ok (w,pre)

def batch (N len atSlot : Usize) (first : U32) (lanes half change : Reg) (iv two : Hash) (base : Words) := do
  let (key,id) ← slotRegs lanes first atSlot len
  let w ← patch base key id
  let (pre,x,c,d) ← prepare w two
  let secret ← PlatformRust.sha256.x86.avx512.compress iv pre w
  let (w,pre) ← switchPrefix w two x change c d
  wots_endpoints_loop1_loop0 N ⟨0#i32,15#i32⟩ iv half w secret pre

private theorem sameBind {A B : Type} (x : Result A) {f g : A → Result B}
    (h : ∀ a, f a = g a) : Std.bind x f = Std.bind x g := by rw [funext h]

private theorem throughBind {A B C : Type} {x : Result A} {f : A → Result B} {g : B → Result C}
    {h : A → Result C} (eq : ∀ v, h v = Std.bind (f v) g) :
    Std.bind x h = Std.bind (Std.bind x f) g := by
  rw [Std.bind_assoc]
  exact sameBind _ eq

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem batch_body_eq {L : Usize} (N len : Usize) (first : U32) (lanes half change : Reg)
    (iv two : Hash) (base : Words) (it : Leaf.Iter) (out : Slice (Array U8 L)) :
    wots_endpoints_loop1.body N first base iv lanes half change len two it out = (do
      let (o,nxt) ← core.iter.adapters.step_by.IteratorStepBy.next
        (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize) it
      match o with
      | none => ok (done out)
      | some atSlot =>
        let total ← len * out.len
        let rem ← total - atSlot
        let used ← lift (core.cmp.impls.OrdUsize.min 16#usize rem)
        let hash ← batch N len atSlot first lanes half change iv two base
        storeBatch N len atSlot used hash out fun v => ok (cont (nxt,v))) := by
  unfold wots_endpoints_loop1.body
  apply sameBind
  rintro ⟨o,nxt⟩
  cases o with
  | none => rfl
  | some pos =>
    iterate 3
      apply sameBind
      intro x
    unfold batch
    simp only [bind_tc_eq,Std.bind_assoc]
    unfold slotRegs patch prepare
    simp only [lift,bind_tc_eq,Std.bind_assoc,bind_ok]
    iterate 26
      apply sameBind
      intro x
    unfold PlatformRust.sha256.x86.avx512.compress
    iterate 60
      apply throughBind
      rintro ⟨a,b⟩
    iterate 24
      apply throughBind
      intro x
    rw [bind_ok]
    unfold switchPrefix storeBatch
    simp only [lift,bind_tc_eq,Std.bind_assoc,bind_ok]

end slhdsa.X86.Wots
