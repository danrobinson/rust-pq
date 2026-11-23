import Slhdsa.Funs
open Aeneas Aeneas.Std Result
namespace slhdsa.PlatformAdapter

/-- [slhdsa::adapter::sign_into]:
    Source: 'src/adapter.rs', lines 51:0-76:1
    Visibility: public -/
def adapter.sign_into
  (N : Std.Usize) (p : params.Params) (m : Slice Std.U8) (ctx : Slice Std.U8)
  (sk : Slice Std.U8) (has_addrnd : Bool) (addrnd : Slice Std.U8)
  (sig : Slice Std.U8) :
  Result (Bool × (Slice Std.U8))
  := do
  let i := Slice.len ctx
  if i > 255#usize
  then ok (false, sig)
  else
    let rand ← adapter.randomizer N sk has_addrnd addrnd
    let i1 := Slice.len m
    if i1 >= 1024#usize
    then
      let o ← slh.slh_sign p m ctx sk rand
      let s ← core.option.Option.unwrap o
      let s1 := alloc.vec.Vec.deref s
      let sig1 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 sig s1
      ok (true, sig1)
    else
      let mp ← slh.with_context m ctx
      let s := alloc.vec.Vec.deref mp
      let s1 ← slh.slh_sign_internal p s sk rand
      let s2 := alloc.vec.Vec.deref s1
      let sig1 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 sig s2
      ok (true, sig1)

end slhdsa.PlatformAdapter
