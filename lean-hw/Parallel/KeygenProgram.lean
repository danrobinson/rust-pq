import Parallel.KeygenTickets
import Armwide.XmssKeygen
import Slhdsa.Proofs.ShakeSlh
open Aeneas Aeneas.Std Result

namespace slhdsa.ParallelKeygenHost
noncomputable section

class Engine (S : Usize → Type) where
  node {N : Usize} : Array U8 N → U32 → U32 → S N → address.Adrs → Result (Array U8 N)
  seedCtx {N : Usize} : Array U8 N → Result (S N)
  seedBytes {N : Usize} : S N → Spec.Bytes

abbrev ShakeSeed (N : Usize) := Array U8 N

def core.option.Option.unwrap_or_else {T F : Type _} (inst : core.ops.function.FnOnce F Unit T)
    (o : Option T) (f : F) : Result T := match o with
  | some x => ok x
  | none => inst.call_once f ()

def pack {N : Usize} (b : Spec.Bytes) : Result (Array U8 N) :=
  let list := b.map (fun x => (⟨x⟩ : U8))
  if h : list.length=N.val then ok (Array.from list h) else fail .panic

def word (n : Nat) : U32 := ⟨BitVec.ofNat 32 n⟩

def computed {S} (e : Engine S) {N : Usize} (sk : Array U8 N) (s : S N)
    (a : address.Adrs) (h i : Nat) : Spec.Bytes := by
  classical
  exact if answer : ∃ v, e.node sk (word i) (word h) s a=ok v then bytes answer.choose.val else []

/-- Values returned by ensure_workers and the caller's attempt to claim the pool. -/
structure PoolOutcome where
  spawned : Nat
  claimed : Bool

def participants (pool : PoolOutcome) (limit : Nat) :=
  if pool.claimed then 1 + min (limit-1) pool.spawned else 1

def worker {S} (e : Engine S) {N : Usize} (P : Spec.Params) (x86 : Bool) (threads : Nat) (pool : PoolOutcome)
    (sk : Array U8 N) (s : S N) (a : address.Adrs) : Result (Option (Array U8 N)) :=
  if threads<2 ∨ P.hp<3 then ok none else do
    let sub := ParallelKeygen.subHeight x86 P.hp
    let n := ParallelKeygen.count x86 P.hp
    let st := ParallelKeygen.finished n (participants pool (min threads n)) (computed e sk s a sub)
    let root ← pack (ParallelKeygen.result P (e.seedBytes s) (adrsS a) sub st.val)
    ok (some root)

namespace S2
variable [e : Engine hash.Seed]
abbrev hash.seed_ctx {N : Usize} := @e.seedCtx N
abbrev xmss.xmss_node {N : Usize} := @e.node N
def slh.slh_keygen_internal.closure (N : Std.Usize) :=
  Array Std.U8 N × params.Params × hash.Seed N × address.Adrs
def
  slh.slh_keygen_internal.closure.Insts.CoreOpsFunctionFnOnceTupleArrayU8N.call_once
  {N : Std.Usize} (c : slh.slh_keygen_internal.closure N) (_ : Unit) :
  Result (Array Std.U8 N)
  := do
  let (a, p, s, a1) := c
  xmss.xmss_node a 0#u32 p.hp s a1
@[reducible]
def slh.slh_keygen_internal.closure.Insts.CoreOpsFunctionFnOnceTupleArrayU8N (N
  : Std.Usize) : core.ops.function.FnOnce (slh.slh_keygen_internal.closure N)
  Unit (Array Std.U8 N) := {
  call_once :=
    slh.slh_keygen_internal.closure.Insts.CoreOpsFunctionFnOnceTupleArrayU8N.call_once
}

class Host where
  x86 : Bool
  threads : Nat
  pool : PoolOutcome

abbrev slh.parallel.keygen [Host] {N : Usize} (p : params.Params) :=
  @worker _ e N (paramsS p) Host.x86 Host.threads Host.pool

variable [Host]
def slh.slh_keygen_internal
  {N : Std.Usize} (p : params.Params) (sk_seed : Array Std.U8 N)
  (sk_prf : Array Std.U8 N) (pk_seed : Array Std.U8 N) (sk : Slice Std.U8)
  (pk : Slice Std.U8) :
  Result ((Slice Std.U8) × (Slice Std.U8))
  := do
  let a ← address.Adrs.new
  let i ← p.d - 1#u32
  let adrs ← address.Adrs.with_layer a i
  let seed ← hash.seed_ctx pk_seed
  let o ← slh.parallel.keygen p sk_seed seed adrs
  let pk_root ←
    core.option.Option.unwrap_or_else
      (slh.slh_keygen_internal.closure.Insts.CoreOpsFunctionFnOnceTupleArrayU8N
      N) o (sk_seed, p, seed, adrs)
  let (s, index_mut_back) ←
    core.slice.index.Slice.index_mut
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) sk
      { start := 0#usize, «end» := N }
  let s1 ← lift (Array.to_slice sk_seed)
  let s2 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s s1
  let sk1 := index_mut_back s2
  let i1 ← 2#usize * N
  let (s3, index_mut_back1) ←
    core.slice.index.Slice.index_mut
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) sk1
      { start := N, «end» := i1 }
  let s4 ← lift (Array.to_slice sk_prf)
  let s5 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s3 s4
  let sk2 := index_mut_back1 s5
  let i2 ← 3#usize * N
  let (s6, index_mut_back2) ←
    core.slice.index.Slice.index_mut
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) sk2
      { start := i1, «end» := i2 }
  let s7 ← lift (Array.to_slice pk_seed)
  let s8 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s6 s7
  let sk3 := index_mut_back2 s8
  let i3 ← 4#usize * N
  let (s9, index_mut_back3) ←
    core.slice.index.Slice.index_mut
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) sk3
      { start := i2, «end» := i3 }
  let s10 ← lift (Array.to_slice pk_root)
  let s11 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s9 s10
  let (s12, index_mut_back4) ←
    core.slice.index.Slice.index_mut
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) pk
      { start := 0#usize, «end» := N }
  let s13 ← lift (Array.to_slice pk_seed)
  let s14 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s12 s13
  let pk1 := index_mut_back4 s14
  let (s15, index_mut_back5) ←
    core.slice.index.Slice.index_mut
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) pk1
      { start := N, «end» := i1 }
  let s16 ← lift (Array.to_slice pk_root)
  let s17 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s15 s16
  let sk4 := index_mut_back3 s11
  let pk2 := index_mut_back5 s17
  ok (sk4, pk2)
end S2

namespace Sh
variable [e : Engine ShakeSeed]
abbrev shake.hash.seed_ctx {N : Usize} := @e.seedCtx N
abbrev shake.xmss.xmss_node {N : Usize} := @e.node N
def shake.slh.slh_keygen_internal.closure (N : Std.Usize) :=
  Array Std.U8 N × params.Params × Array Std.U8 N × address.Adrs
def
  shake.slh.slh_keygen_internal.closure.Insts.CoreOpsFunctionFnOnceTupleArrayU8N.call_once
  {N : Std.Usize} (c : shake.slh.slh_keygen_internal.closure N) (_ : Unit) :
  Result (Array Std.U8 N)
  := do
  let (a, p, a1, a2) := c
  shake.xmss.xmss_node a 0#u32 p.hp a1 a2
@[reducible]
def
  shake.slh.slh_keygen_internal.closure.Insts.CoreOpsFunctionFnOnceTupleArrayU8N
  (N : Std.Usize) : core.ops.function.FnOnce
  (shake.slh.slh_keygen_internal.closure N) Unit (Array Std.U8 N) := {
  call_once :=
    shake.slh.slh_keygen_internal.closure.Insts.CoreOpsFunctionFnOnceTupleArrayU8N.call_once
}

class Host where
  x86 : Bool
  threads : Nat
  pool : PoolOutcome

abbrev shake.slh.parallel.keygen [Host] {N : Usize} (p : params.Params) :=
  @worker _ e N (Shake.params p) Host.x86 Host.threads Host.pool

variable [Host]
def shake.slh.slh_keygen_internal
  {N : Std.Usize} (p : params.Params) (sk_seed : Array Std.U8 N)
  (sk_prf : Array Std.U8 N) (pk_seed : Array Std.U8 N) (sk : Slice Std.U8)
  (pk : Slice Std.U8) :
  Result ((Slice Std.U8) × (Slice Std.U8))
  := do
  let a ← address.Adrs.new
  let i ← p.d - 1#u32
  let adrs ← address.Adrs.with_layer a i
  let seed ← shake.hash.seed_ctx pk_seed
  let o ← shake.slh.parallel.keygen p sk_seed seed adrs
  let pk_root ←
    core.option.Option.unwrap_or_else
      (shake.slh.slh_keygen_internal.closure.Insts.CoreOpsFunctionFnOnceTupleArrayU8N
      N) o (sk_seed, p, seed, adrs)
  let (s, index_mut_back) ←
    core.slice.index.Slice.index_mut
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) sk
      { start := 0#usize, «end» := N }
  let s1 ← lift (Array.to_slice sk_seed)
  let s2 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s s1
  let sk1 := index_mut_back s2
  let i1 ← 2#usize * N
  let (s3, index_mut_back1) ←
    core.slice.index.Slice.index_mut
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) sk1
      { start := N, «end» := i1 }
  let s4 ← lift (Array.to_slice sk_prf)
  let s5 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s3 s4
  let sk2 := index_mut_back1 s5
  let i2 ← 3#usize * N
  let (s6, index_mut_back2) ←
    core.slice.index.Slice.index_mut
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) sk2
      { start := i1, «end» := i2 }
  let s7 ← lift (Array.to_slice pk_seed)
  let s8 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s6 s7
  let sk3 := index_mut_back2 s8
  let i3 ← 4#usize * N
  let (s9, index_mut_back3) ←
    core.slice.index.Slice.index_mut
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) sk3
      { start := i2, «end» := i3 }
  let s10 ← lift (Array.to_slice pk_root)
  let s11 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s9 s10
  let (s12, index_mut_back4) ←
    core.slice.index.Slice.index_mut
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) pk
      { start := 0#usize, «end» := N }
  let s13 ← lift (Array.to_slice pk_seed)
  let s14 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s12 s13
  let pk1 := index_mut_back4 s14
  let (s15, index_mut_back5) ←
    core.slice.index.Slice.index_mut
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) pk1
      { start := N, «end» := i1 }
  let s16 ← lift (Array.to_slice pk_root)
  let s17 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s15 s16
  let sk4 := index_mut_back3 s11
  let pk2 := index_mut_back5 s17
  ok (sk4, pk2)
end Sh

end
end slhdsa.ParallelKeygenHost
