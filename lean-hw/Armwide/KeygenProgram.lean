import Armwide.KeyCompression
import Slhdsa.Proofs.Wots

open Aeneas Aeneas.Std Result
namespace slhdsa.Armwide.Keygen

class Features where
  sha512 : Bool

def sha256.arm_wide.wots_endpoints_1 {N : Usize} (st : Array U32 8#usize) (sk : Array U8 N)
    (a : slhdsa.address.Adrs) (buf : Slice U8) : Result (Slice U8) := do
  if 22+payLen N.val > buf.length then fail .panic else
    let result := writeEndpoints N.val (wv st.val) (slhdsa.bytes sk.val) (slhdsa.adrsS a) (slhdsa.bytes buf.val)
    ok (Slice.from (result.map (fun b => (⟨b⟩ : U8))) (by
      rw [List.length_map,write_size,slhdsa.bytes_length]; exact buf.property))

/-- Interpret the Rust padding and kernel routes on a buffer of the public entry's size. -/
def wots.arm.compress_tlen_1 [cpu : Features] {N : Usize} (seed : slhdsa.hash.Seed N)
    (a : slhdsa.address.Adrs) (buf : Slice U8) (len : Usize) : Result (Array U8 N × Slice U8) := do
  if len.val≠2*N.val+3 || buf.length≠total N.val then fail .panic else
    let input := padded N.val (slhdsa.adrsS a) (slhdsa.bytes buf.val)
    let digest := compression N.val cpu.sha512 (wv seed.state.val) (S512.wv seed.state512.val) input
    if fits : digest.length=N.val then
      let r := Array.from (digest.map (fun b => (⟨b⟩ : U8))) (by simpa only [List.length_map] using fits)
      let final := buf.val.setSlice! 0 (input.map (fun b => (⟨b⟩ : U8)))
      ok (r,Slice.from final (by simp [final]))
    else fail .panic

section
variable [Features]

def wots.arm.pk_gen
  {N : Std.Usize} (sk_seed : Array Std.U8 N) (seed : hash.Seed N)
  (adrs : address.Adrs) :
  Result (Array Std.U8 N)
  := do
  let i ← 2#usize * N
  let len ← i + params.LEN2
  if N = 16#usize
  then
    let buf := Array.repeat 640#usize 0#u8
    let (s, to_slice_mut_back) ← lift (Array.to_slice_mut buf)
    let s1 ← sha256.arm_wide.wots_endpoints_1 seed.state sk_seed adrs s
    let buf1 := to_slice_mut_back s1
    let (s2, _) ← lift (Array.to_slice_mut buf1)
    let (a, _) ← wots.arm.compress_tlen_1 seed adrs s2 len
    ok a
  else
    if N = 24#usize
    then
      let buf := Array.repeat 1280#usize 0#u8
      let (s, to_slice_mut_back) ← lift (Array.to_slice_mut buf)
      let s1 ← sha256.arm_wide.wots_endpoints_1 seed.state sk_seed adrs s
      let buf1 := to_slice_mut_back s1
      let (s2, _) ← lift (Array.to_slice_mut buf1)
      let (a, _) ← wots.arm.compress_tlen_1 seed adrs s2 len
      ok a
    else
      let buf := Array.repeat 2304#usize 0#u8
      let (s, to_slice_mut_back) ← lift (Array.to_slice_mut buf)
      let s1 ← sha256.arm_wide.wots_endpoints_1 seed.state sk_seed adrs s
      let buf1 := to_slice_mut_back s1
      let (s2, _) ← lift (Array.to_slice_mut buf1)
      let (a, _) ← wots.arm.compress_tlen_1 seed adrs s2 len
      ok a

end
end slhdsa.Armwide.Keygen
