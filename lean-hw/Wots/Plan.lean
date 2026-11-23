import Wots.Bypass
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.Wots
open WotsRust

def prepareRecovery (N : Usize) (sig : Slice U8) (digits : Slice U32) (out : Buffers) := do
  let counts := Array.repeat 16#usize 0#usize
  let iter ←
    SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter
      digits
  let histogram ← sha256.x86.avx512.recover_loop0 iter counts
  let «at» := Array.repeat 16#usize 0#usize
  let offsets ←
    sha256.x86.avx512.recover_loop1 { start := 1#usize, «end» := 16#usize }
      histogram «at»
  let order := Array.repeat 67#usize 0#usize
  let it ← core.slice.Slice.iter digits
  let indexed ←
    core.iter.traits.iterator.Iterator.enumerate.trait_default
      (core.iter.traits.iterator.IteratorSliceIter Std.U32) it
  let order ← sha256.x86.avx512.recover_loop2 indexed offsets order
  let number := Slice.len digits
  let alreadyDone ← Array.index_usize histogram 15#usize
  let workload ← number - alreadyDone
  let endPos := Slice.len digits
  let tail ←
    core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeUsizeSlice Std.Usize)) order
      { start := workload, «end» := endPos }
  let finished ←
    SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter tail
  let copied ← sha256.x86.avx512.recover_loop3 N finished sig out
  ok (order,workload,copied)

def runRecovery (N : Usize) (state : Array U32 8#usize) (adrs : WotsRust.address.Adrs)
    (sig : Slice U8) (digits : Slice U32) (order1 : Order) (workload : Usize) (out1 : Buffers) := do
  let a ← WotsRust.address.Adrs.with_word2 adrs 0#u32
  let a1 ← WotsRust.address.Adrs.with_word3 a 0#u32
  let a2 := Array.repeat N 0#u8
  let s1 ← lift (Array.to_slice a2)
  let template ← WotsRust.hash.short_block a1 s1
  let w ←
    core.array.from_fn 16#usize
      (sha256.x86.avx512.recover.closure.Insts.CoreOpsFunctionFnMutTupleUsize__m512i
      N) template
  let initial ←
    core.array.Array.map
      (sha256.x86.avx512.recover.closure_1.Insts.CoreOpsFunctionFnMutTupleU32__m512i
      N) state ()
  let «prefix» ←
    sha256.x86.avx512.recover_loop4 { start := 0#usize, «end» := 4#usize } w
      initial
  let half ← core.core_arch.x86.avx512f._mm512_set1_epi32 65535#i32
  let mi ←
    core.core_arch.x86.sse2._mm_set_epi32 202182159#i32 134810123#i32
      67438087#i32 66051#i32
  let swap ← core.core_arch.x86.avx512f._mm512_broadcast_i32x4 mi
  let indices := Array.repeat 16#usize 0#i32
  let starts := Array.repeat 16#usize 0#i32
  let idx ← core.core_arch.x86.avx512f._mm512_setzero_si512
  let hash := Array.repeat 8#usize idx
  sha256.x86.avx512.recover_loop5 N idx sig digits out1 order1 workload w
    initial «prefix» half swap indices starts idx idx 0#u16 0#usize hash


theorem recover_eq (N : Usize) (state : Array U32 8#usize) (a : WotsRust.address.Adrs)
    (sig : Slice U8) (digits : Slice U32) (out : Buffers) :
    WotsRust.sha256.x86.avx512.recover N state a sig digits out = (do
      let (order,workload,buf) ← prepareRecovery N sig digits out
      runRecovery N state a sig digits order workload buf) := by
  unfold WotsRust.sha256.x86.avx512.recover prepareRecovery runRecovery
  simp only [bind_tc_eq,Std.bind_assoc,bind_ok]
  rfl

def initialized (N : Usize) (digits : Slice U32) (sig : Slice U8) (out buf : Buffers) :=
  buf.length = out.length ∧ ∀ r < out.length,
    if r < digits.length ∧ digits.val[r]!.val=15 then
      buf.val[r]!.val = out.val[r]!.val.take 22 ++ element N sig r ++ out.val[r]!.val.drop (22+N.val)
    else buf.val[r]! = out.val[r]!

theorem preparation_spec (N : Usize) (sig : Slice U8) (digits : Slice U32) (out : Buffers)
    (width : N.val ≤ 32) (small : digits.length ≤ 67) (valid : ∀ i < digits.length, digits.val[i]!.val < 16)
    (room : digits.length ≤ out.length) (available : N.val*digits.length ≤ sig.length) :
    prepareRecovery N sig digits out ⦃ order workload buf =>
      (∀ i < digits.length, order.val[rank digits.val i]!.val = i) ∧
      workload.val = below digits.val 15 ∧ initialized N digits sig out buf ⦄ := by
  unfold prepareRecovery
  simp only [SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter,core.slice.Slice.iter,
    core.iter.traits.iterator.Iterator.enumerate.trait_default,core.iter.traits.iterator.Iterator.enumerate.default,bind_ok]
  step with histogram_spec digits small valid as ⟨counts,hc⟩
  step with offsets_spec digits counts small hc as ⟨offsets,ho⟩
  step with order_spec digits offsets _ small valid ho as ⟨order,ordered⟩
  step as ⟨num,hn⟩
  have count : num.val = frequency digits.val 15 := by rw [hn,← getElem!_pos]; exact hc 15 (by decide)
  have freq : frequency digits.val 15 ≤ digits.length := frequency_le _ _
  step as ⟨w,hw⟩
  have work : w.val = digits.length-frequency digits.val 15 := by change w.val = digits.len.val-_ ; rw [hw,count]
  step as ⟨tail,ht,hlen⟩
  have lookup (t : Nat) (live : t < tail.length) : tail.val[t]! = order.val[w.val+t]! := by
    rw [ht]; simp only [List.slice,Array.val_to_slice,List.drop_take]
    apply getElem!_take_drop
    omega
  have pos (t : Nat) (live : t < tail.length) : w.val+t < digits.length := by
    change tail.length = digits.len.val-w.val at hlen
    have e : digits.len.val = digits.length := by simp
    omega
  have index (t : Nat) (ht : t < tail.length) : tail.val[t]!.val < digits.length := by
    rw [lookup t ht]; exact (order_at digits order ordered _ (pos _ ht)).1
  have distinct (i : Nat) (hi : i < tail.length) (j : Nat) (hj : j < tail.length)
      (eq : tail.val[i]!.val=tail.val[j]!.val) : i=j := by
    rw [lookup _ hi,lookup _ hj] at eq
    have a := (order_at digits order ordered _ (pos _ hi)).2
    rw [eq,(order_at digits order ordered _ (pos _ hj)).2] at a; omega
  step with bypass_spec N sig out tail width
    (fun t ht => (Nat.mul_le_mul_left N.val (show tail.val[t]!.val+1 ≤ digits.length from index t ht)).trans available)
    (fun t ht => (index t ht).trans_le room) distinct as ⟨buf,hbuf⟩
  refine ⟨ordered,work.trans (workload_eq _ valid),hbuf.1,?_⟩
  intro r hr
  have membership : (∃ t<tail.length,tail.val[t]!.val=r) ↔ r<digits.length ∧ digits.val[r]!.val=15 := by
    constructor
    · rintro ⟨t,ht,eq⟩
      have p := order_partition digits order valid ordered _ (pos t ht)
      rw [lookup _ ht] at eq
      rw [← eq]
      exact ⟨p.1,p.2.2.mp (by omega)⟩
    · rintro ⟨bound,digit⟩
      let p := rank digits.val r
      have smallp : p < digits.length := rank_bound _ _ bound
      have atp : order.val[p]!.val=r := ordered r bound
      have part := (order_partition digits order valid ordered p smallp).2.2
      rw [atp] at part
      have ge := part.mpr digit
      have live : p-w.val < tail.length := by
        change tail.length=digits.len.val-w.val at hlen
        have e : digits.len.val=digits.length := by simp
        omega
      exact ⟨p-w.val,live,by rw [lookup _ live,show w.val+(p-w.val)=p by omega,atp]⟩
  simpa only [membership] using hbuf.2 r hr

end slhdsa.X86.Wots
