import Cachepath.WotsFusedLayout
open Aeneas Aeneas.Std Result ControlFlow Error
namespace slhdsa.NativeVerify

/-- Big-endian bytes of the operand read back as a little-endian 64-bit word. -/
def swap64 (x : U64) : Result U64 := ok ⟨x.bv.extractLsb' 0 8 ++ x.bv.extractLsb' 8 8 ++ x.bv.extractLsb' 16 8 ++ x.bv.extractLsb' 24 8 ++ x.bv.extractLsb' 32 8 ++ x.bv.extractLsb' 40 8 ++ x.bv.extractLsb' 48 8 ++ x.bv.extractLsb' 56 8⟩

/-- [slhdsa::shake::batch::seed_words]: loop body 0:
    Source: 'src/shake/batch.rs', lines 22:4-24:5 -/
@[rust_loop_body]
def seed_words_loop.body
  {N : Std.Usize} (seed : Array Std.U8 N)
  (iter : core.ops.range.Range Std.Usize) (out : Array Std.U64 4#usize) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array Std.U64
    4#usize)) (Array Std.U64 4#usize))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done out)
  | some i =>
    let s ← lift (Array.to_slice seed)
    let i1 ← ShakeBatch.shake.batch.word s i
    let a ← Array.update out i i1
    ok (cont (iter1, a))

/-- [slhdsa::shake::batch::seed_words]: loop 0:
    Source: 'src/shake/batch.rs', lines 22:4-24:5 -/
@[rust_loop]
def seed_words_loop
  {N : Std.Usize} (iter : core.ops.range.Range Std.Usize)
  (seed : Array Std.U8 N) (out : Array Std.U64 4#usize) :
  Result (Array Std.U64 4#usize)
  := do
  loop
    (fun (iter1, out1) => seed_words_loop.body seed iter1 out1)
    (iter, out)

/-- [slhdsa::shake::batch::seed_words]:
    Source: 'src/shake/batch.rs', lines 20:0-26:1 -/
def seed_words
  {N : Std.Usize} (seed : Array Std.U8 N) :
  Result (Array Std.U64 4#usize)
  := do
  let out := Array.repeat 4#usize 0#u64
  let i ← N / 8#usize
  seed_words_loop { start := 0#usize, «end» := i } seed out

/-- [slhdsa::shake::batch::adrs_words]:
    Source: 'src/shake/batch.rs', lines 29:0-36:1 -/
def adrs_words
  (adrs : address.Adrs) : Result (Array Std.U64 4#usize) := do
  let i ← ShakeBatch.core.num.U32.swap_bytes adrs.layer
  let i1 ← lift (core.convert.num.FromU64U32.from i)
  let i2 ← swap64 adrs.tree
  let i3 ← ShakeBatch.core.num.U32.swap_bytes adrs.typ
  let i4 ← lift (core.convert.num.FromU64U32.from i3)
  let i5 ← ShakeBatch.core.num.U32.swap_bytes adrs.keypair
  let i6 ← lift (core.convert.num.FromU64U32.from i5)
  let i7 ← i6 <<< 32#i32
  let i8 ← lift (i4 ||| i7)
  let i9 ← ShakeBatch.core.num.U32.swap_bytes adrs.word2
  let i10 ← lift (core.convert.num.FromU64U32.from i9)
  let i11 ← ShakeBatch.core.num.U32.swap_bytes adrs.word3
  let i12 ← lift (core.convert.num.FromU64U32.from i11)
  let i13 ← i12 <<< 32#i32
  let i14 ← lift (i10 ||| i13)
  ok (Array.make 4#usize [ i1, i2, i8, i14 ])

end slhdsa.NativeVerify
