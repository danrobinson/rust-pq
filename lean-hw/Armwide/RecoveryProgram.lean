import Armwide.RecoverySchedule
import Armwide.RecoveryPreProgram
import Armwide.RecoveryFrame
import Armwide.KeygenProgram
open Aeneas Aeneas.Std Result
namespace slhdsa.Armwide.Recovery
open WotsRefill

def completeRows (n : Nat) (st : List Spec.SHA256.Word) (a : Spec.Adrs) (sig : Nat → Spec.Bytes)
    (d : Nat → Nat) (ord : List Nat) (buf : Spec.Bytes) :=
  let ls := (ord.take 4).map (fresh sig d)
  let queue := ord.drop 4
  run (writeAt n) n st a sig d ls queue buf (recoverMeasure ls queue+1)

def sha256.arm_wide.wots_recover (N : Usize) (st : Array U32 8#usize) (a : slhdsa.address.Adrs)
    (sig : Slice U8) (ds : Slice U32) (buf : Slice U8) : Result (Slice U8) := do
  let (weights,b) ← prepare N ds sig buf
  let selected ← core.array.Array.index
    (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeToUsizeSlice U32)) weights ⟨ds.len⟩
  let result ← ArmwideRust.sha256.arm_wide.sort_descending selected (Array.repeat 67#usize 0#u8)
  if result.1=0#usize then ok b else
    let queue := (result.2.val.take result.1.val).map (·.val)
    let output := completeRows N.val (wv st.val) (slhdsa.adrsS a)
      (fun i => ((slhdsa.bytes sig.val).drop (i*N.val)).take N.val) (fun i => ds.val[i]!.val) queue (slhdsa.bytes b.val)
    if room : output.length≤Usize.max then
      ok (Slice.from (output.map (fun x => (⟨x⟩ : U8))) (by simpa using room))
    else fail .panic

abbrev wots.arm.wots_digits_stack := @ArmwideRust.wots.arm.wots_digits_stack
section
variable [Keygen.Features]
def wots.arm.recover
  {N : Std.Usize} (sig : Slice Std.U8) (m : Array Std.U8 N)
  (seed : hash.Seed N) (adrs : address.Adrs) :
  Result (Array Std.U8 N)
  := do
  let i ← 2#usize * N
  let len ← i + params.LEN2
  let digits ← wots.arm.wots_digits_stack m
  if N = 16#usize
  then
    let buf := Array.repeat 640#usize 0#u8
    let s ←
      core.array.Array.index (core.ops.index.IndexSlice
        (core.slice.index.SliceIndexRangeToUsizeSlice Std.U32)) digits
        { «end» := len }
    let (s1, to_slice_mut_back) ← lift (Array.to_slice_mut buf)
    let s2 ← sha256.arm_wide.wots_recover N seed.state adrs sig s s1
    let buf1 := to_slice_mut_back s2
    let (s3, _) ← lift (Array.to_slice_mut buf1)
    let (a, _) ← Keygen.wots.arm.compress_tlen_1 seed adrs s3 len
    ok a
  else
    if N = 24#usize
    then
      let buf := Array.repeat 1280#usize 0#u8
      let s ←
        core.array.Array.index (core.ops.index.IndexSlice
          (core.slice.index.SliceIndexRangeToUsizeSlice Std.U32)) digits
          { «end» := len }
      let (s1, to_slice_mut_back) ← lift (Array.to_slice_mut buf)
      let s2 ← sha256.arm_wide.wots_recover N seed.state adrs sig s s1
      let buf1 := to_slice_mut_back s2
      let (s3, _) ← lift (Array.to_slice_mut buf1)
      let (a, _) ← Keygen.wots.arm.compress_tlen_1 seed adrs s3 len
      ok a
    else
      let buf := Array.repeat 2304#usize 0#u8
      let s ←
        core.array.Array.index (core.ops.index.IndexSlice
          (core.slice.index.SliceIndexRangeToUsizeSlice Std.U32)) digits
          { «end» := len }
      let (s1, to_slice_mut_back) ← lift (Array.to_slice_mut buf)
      let s2 ← sha256.arm_wide.wots_recover N seed.state adrs sig s s1
      let buf1 := to_slice_mut_back s2
      let (s3, _) ← lift (Array.to_slice_mut buf1)
      let (a, _) ← Keygen.wots.arm.compress_tlen_1 seed adrs s3 len
      ok a

end
end slhdsa.Armwide.Recovery
