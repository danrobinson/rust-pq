import Armwide.Keygen
import Armwide.DispatchProgram

open Aeneas Aeneas.Std Result
namespace slhdsa.Armwide.Keygen.Dispatcher

open slhdsa.Armwide.Public.Dispatcher (Cpu)

abbrev sha256.arm_wide.available [Cpu] := Public.Dispatcher.sha256.arm_wide.available

section
variable [Cpu] [Features]

def wots.wots_pk_gen
  {N : Std.Usize} (sk_seed : Array Std.U8 N) (seed : hash.Seed N)
  (adrs : address.Adrs) :
  Result (Array Std.U8 N)
  := do
  let b ←
    match N.val with
    | 16 => ok true
    | 24 => ok true
    | 32 => ok true
    | _ => ok false
  if b
  then
    let b1 ← sha256.arm_wide.available
    if b1
    then wots.arm.pk_gen sk_seed seed adrs
    else
      let i ← 2#usize * N
      let len ← i + params.LEN2
      let blocks ← wots.sk_blocks sk_seed seed adrs
      let (s, index_mut_back) ←
        core.array.Array.index_mut (core.ops.index.IndexMutSlice
          (core.slice.index.SliceIndexRangeUsizeSlice (Array Std.U8 64#usize)))
          blocks { start := 0#usize, «end» := len }
      let a := Array.repeat 67#usize 0#u32
      let s1 ← lift (Array.to_slice a)
      let _ ← params.W - 1#u32
      let i1 ← lift (Std.U32.wrapping_sub params.W 1#u32)
      let a1 := Array.repeat 67#usize i1
      let s2 ← lift (Array.to_slice a1)
      let s3 ← hash.chain_blocks N seed.state s s1 s2
      let a2 ← address.Adrs.with_type adrs address.WOTS_PK
      let pk_adrs ← address.Adrs.with_keypair a2 adrs.keypair
      let blocks1 := index_mut_back s3
      let s4 ←
        core.array.Array.index (core.ops.index.IndexSlice
          (core.slice.index.SliceIndexRangeUsizeSlice (Array Std.U8 64#usize)))
          blocks1 { start := 0#usize, «end» := len }
      hash.thash_values seed pk_adrs s4
  else
    let i ← 2#usize * N
    let len ← i + params.LEN2
    let blocks ← wots.sk_blocks sk_seed seed adrs
    let (s, index_mut_back) ←
      core.array.Array.index_mut (core.ops.index.IndexMutSlice
        (core.slice.index.SliceIndexRangeUsizeSlice (Array Std.U8 64#usize)))
        blocks { start := 0#usize, «end» := len }
    let a := Array.repeat 67#usize 0#u32
    let s1 ← lift (Array.to_slice a)
    let _ ← params.W - 1#u32
    let i1 ← lift (Std.U32.wrapping_sub params.W 1#u32)
    let a1 := Array.repeat 67#usize i1
    let s2 ← lift (Array.to_slice a1)
    let s3 ← hash.chain_blocks N seed.state s s1 s2
    let a2 ← address.Adrs.with_type adrs address.WOTS_PK
    let pk_adrs ← address.Adrs.with_keypair a2 adrs.keypair
    let blocks1 := index_mut_back s3
    let s4 ←
      core.array.Array.index (core.ops.index.IndexSlice
        (core.slice.index.SliceIndexRangeUsizeSlice (Array Std.U8 64#usize)))
        blocks1 { start := 0#usize, «end» := len }
    hash.thash_values seed pk_adrs s4

end

/-- Both branches of the Rust dispatcher compute the same WOTS public key at
the leaf addresses constructed by XMSS, for either SHA-512 feature result. -/
theorem dispatch_eq_scalar [cpu : Cpu] [Features] {N : Usize} (p : params.Params) (hp : PN p N)
    (sk : Array U8 N) (seed : hash.Seed N) (hs : SeedOk seed) (a : address.Adrs)
    (reachable : hashAddr (slhdsa.adrsS a)=slhdsa.adrsS a) :
    wots.wots_pk_gen sk seed a = slhdsa.wots.wots_pk_gen sk seed a := by
  unfold wots.wots_pk_gen
  rcases hp.nok with h|h|h <;> simp only [h,bind_ok,ite_true,sha256.arm_wide.available,Public.Dispatcher.sha256.arm_wide.available] <;> cases cpu.wide
  all_goals first | rfl | exact pk_gen_eq_scalar p hp sk seed hs a reachable

end slhdsa.Armwide.Keygen.Dispatcher
